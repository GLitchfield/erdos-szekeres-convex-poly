module

public import ErdosSzekeres.Fin15AnchoredClauseChunk009
public import ErdosSzekeres.Fin15AnchoredClauseChunk010
public import ErdosSzekeres.Fin15AnchoredClauseChunk011

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 005. -/

theorem fin15Anchored_rejectSemanticSegment005
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0339 chi) ∨
      ((¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0339 chi) ∨
      (¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0339 chi))) ∨
      (((¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0339 chi) ∨
      (Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0339 chi)) ∨
      ((Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0339 chi) ∨
      (Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0339 chi)))) ∨
      ((((Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0339 chi) ∨
      (¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0340 chi)) ∨
      ((¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0340 chi) ∨
      (¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0340 chi))) ∨
      (((¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0340 chi) ∨
      (Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0340 chi)) ∨
      ((Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0340 chi) ∨
      (Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0340 chi))))) ∨
      (((((Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0340 chi) ∨
      (¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0341 chi)) ∨
      ((¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0341 chi) ∨
      (¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0341 chi))) ∨
      (((¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0341 chi) ∨
      (Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0341 chi)) ∨
      ((Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0341 chi) ∨
      (Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0341 chi)))) ∨
      ((((Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0341 chi) ∨
      (¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0342 chi)) ∨
      ((¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0342 chi) ∨
      (¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0342 chi))) ∨
      (((¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0342 chi) ∨
      (Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0342 chi)) ∨
      ((Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0342 chi) ∨
      (Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0342 chi)))))) ∨
      ((((((Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0342 chi) ∨
      (¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0343 chi)) ∨
      ((¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0343 chi) ∨
      (¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0343 chi))) ∨
      (((¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0343 chi) ∨
      (Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0343 chi)) ∨
      ((Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0343 chi) ∨
      (Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0343 chi)))) ∨
      ((((Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0343 chi) ∨
      (¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0344 chi)) ∨
      ((¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0344 chi) ∨
      (¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0344 chi))) ∨
      (((¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0344 chi) ∨
      (Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0344 chi)) ∨
      ((Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0344 chi) ∨
      (Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0344 chi))))) ∨
      (((((Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0344 chi) ∨
      (¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0345 chi)) ∨
      ((¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0345 chi) ∨
      (¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0345 chi))) ∨
      (((¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0345 chi) ∨
      (Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0345 chi)) ∨
      ((Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0345 chi) ∨
      (Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0345 chi)))) ∨
      ((((Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0345 chi) ∨
      (¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0346 chi)) ∨
      ((¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0346 chi) ∨
      (¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0346 chi))) ∨
      (((¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0346 chi) ∨
      (Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0346 chi)) ∨
      ((Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0346 chi) ∨
      (Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0346 chi))))))) ∨
      ((((((Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0346 chi) ∨
      ((¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0347 chi) ∨
      (¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0347 chi))) ∨
      (((Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0347 chi) ∨
      (Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0347 chi)) ∨
      ((Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0347 chi) ∨
      (¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0348 chi)))) ∨
      ((((¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0348 chi) ∨
      (¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0348 chi)) ∨
      ((¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0348 chi) ∨
      (Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0348 chi))) ∨
      (((Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0348 chi) ∨
      (Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0348 chi)) ∨
      ((Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0348 chi) ∨
      (¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0349 chi))))) ∨
      (((((¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0349 chi) ∨
      (¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0349 chi)) ∨
      ((¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0349 chi) ∨
      (Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0349 chi))) ∨
      (((Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0349 chi) ∨
      (Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0349 chi)) ∨
      ((Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0349 chi) ∨
      (¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0350 chi)))) ∨
      ((((¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0350 chi) ∨
      (¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0350 chi)) ∨
      ((¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0350 chi) ∨
      (Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0350 chi))) ∨
      (((Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0350 chi) ∨
      (Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0350 chi)) ∨
      ((Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0350 chi) ∨
      (¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0351 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0351 chi) ∨
      (¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0351 chi)) ∨
      ((¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0351 chi) ∨
      (Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0351 chi))) ∨
      (((Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0351 chi) ∨
      (Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0351 chi)) ∨
      ((Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0351 chi) ∨
      (¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0352 chi)))) ∨
      ((((¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0352 chi) ∨
      (¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0352 chi)) ∨
      ((¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0352 chi) ∨
      (Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0352 chi))) ∨
      (((Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0352 chi) ∨
      (Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0352 chi)) ∨
      ((Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0352 chi) ∨
      (¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0354 chi))))) ∨
      (((((¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0354 chi) ∨
      (¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0354 chi)) ∨
      ((¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0354 chi) ∨
      (Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0354 chi))) ∨
      (((Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0354 chi) ∨
      (Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0354 chi)) ∨
      ((Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0354 chi) ∨
      (¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0355 chi)))) ∨
      ((((¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0355 chi) ∨
      (¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0355 chi)) ∨
      ((¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0355 chi) ∨
      (Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0355 chi))) ∨
      (((Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0355 chi) ∨
      (Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0355 chi)) ∨
      ((Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0355 chi) ∨
      (¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0356 chi)))))))) ∨
      (((((((¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0356 chi) ∨
      ((¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0356 chi) ∨
      (¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0356 chi))) ∨
      (((Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0356 chi) ∨
      (Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0356 chi)) ∨
      ((Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0356 chi) ∨
      (Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0356 chi)))) ∨
      ((((¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0357 chi) ∨
      (¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0357 chi)) ∨
      ((¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0357 chi) ∨
      (¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0357 chi))) ∨
      (((Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0357 chi) ∨
      (Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0357 chi)) ∨
      ((Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0357 chi) ∨
      (Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0357 chi))))) ∨
      (((((¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0358 chi) ∨
      (¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0358 chi)) ∨
      ((¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0358 chi) ∨
      (¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0358 chi))) ∨
      (((Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0358 chi) ∨
      (Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0358 chi)) ∨
      ((Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0358 chi) ∨
      (Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0358 chi)))) ∨
      ((((¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0359 chi) ∨
      (¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0359 chi)) ∨
      ((¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0359 chi) ∨
      (¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0359 chi))) ∨
      (((Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0359 chi) ∨
      (Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0359 chi)) ∨
      ((Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0359 chi) ∨
      (Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0359 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0360 chi) ∨
      (¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0360 chi)) ∨
      ((¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0360 chi) ∨
      (¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0360 chi))) ∨
      (((Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0360 chi) ∨
      (Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0360 chi)) ∨
      ((Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0360 chi) ∨
      (Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0360 chi)))) ∨
      ((((¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0361 chi) ∨
      (¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0361 chi)) ∨
      ((¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0361 chi) ∨
      (¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0361 chi))) ∨
      (((Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0361 chi) ∨
      (Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0361 chi)) ∨
      ((Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0361 chi) ∨
      (Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0361 chi))))) ∨
      (((((¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0362 chi) ∨
      (¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0362 chi)) ∨
      ((¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0362 chi) ∨
      (¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0362 chi))) ∨
      (((Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0362 chi) ∨
      (Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0362 chi)) ∨
      ((Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0362 chi) ∨
      (Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0362 chi)))) ∨
      ((((¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0363 chi) ∨
      (¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0363 chi)) ∨
      ((¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0363 chi) ∨
      (¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0363 chi))) ∨
      (((Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0363 chi) ∨
      (Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0363 chi)) ∨
      ((Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0363 chi) ∨
      (Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0363 chi))))))) ∨
      (((((((¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0364 chi) ∨
      (¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0364 chi)) ∨
      ((¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0364 chi) ∨
      (¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0364 chi))) ∨
      (((Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0364 chi) ∨
      (Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0364 chi)) ∨
      ((Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0364 chi) ∨
      (Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0364 chi)))) ∨
      ((((¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0365 chi) ∨
      (¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0365 chi)) ∨
      ((¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0365 chi) ∨
      (¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0365 chi))) ∨
      (((Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0365 chi) ∨
      (Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0365 chi)) ∨
      ((Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0365 chi) ∨
      (Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0365 chi))))) ∨
      (((((¬Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0366 chi) ∨
      (¬Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0366 chi)) ∨
      ((¬Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0366 chi) ∨
      (¬Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0366 chi))) ∨
      (((Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0366 chi) ∨
      (Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0366 chi)) ∨
      ((Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0366 chi) ∨
      (Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0366 chi)))) ∨
      ((((¬Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0367 chi) ∨
      (¬Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0367 chi)) ∨
      ((¬Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0367 chi) ∨
      (¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0369 chi))) ∨
      (((¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0369 chi) ∨
      (¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0369 chi)) ∨
      ((¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0369 chi) ∨
      (Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0369 chi)))))) ∨
      ((((((Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0369 chi) ∨
      (Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0369 chi)) ∨
      ((Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0369 chi) ∨
      (¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0370 chi))) ∨
      (((¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0370 chi) ∨
      (¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0370 chi)) ∨
      ((¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0370 chi) ∨
      (Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0370 chi)))) ∨
      ((((Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0370 chi) ∨
      (Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0370 chi)) ∨
      ((Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0370 chi) ∨
      (¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0371 chi))) ∨
      (((¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0371 chi) ∨
      (¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0371 chi)) ∨
      ((¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0371 chi) ∨
      (Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0371 chi))))) ∨
      (((((Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0371 chi) ∨
      (Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0371 chi)) ∨
      ((Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0371 chi) ∨
      (¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0372 chi))) ∨
      (((¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0372 chi) ∨
      (¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0372 chi)) ∨
      ((¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0372 chi) ∨
      (Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0372 chi)))) ∨
      ((((Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0372 chi) ∨
      (Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0372 chi)) ∨
      ((Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0372 chi) ∨
      (¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0373 chi))) ∨
      (((¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0373 chi) ∨
      (¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0373 chi)) ∨
      ((¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0373 chi) ∨
      (Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0373 chi)))))))))) := by
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
                exact fin15Anchored_clause01261 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01262 chi hone hbad
                ·
                  exact fin15Anchored_clause01263 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01264 chi hone hbad
                ·
                  exact fin15Anchored_clause01265 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01266 chi hone hbad
                ·
                  exact fin15Anchored_clause01267 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01268 chi hone hbad
                ·
                  exact fin15Anchored_clause01269 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01270 chi hone hbad
                ·
                  exact fin15Anchored_clause01271 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01272 chi hone hbad
                ·
                  exact fin15Anchored_clause01273 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01274 chi hone hbad
                ·
                  exact fin15Anchored_clause01275 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01276 chi hone hbad
                ·
                  exact fin15Anchored_clause01277 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01278 chi hone hbad
                ·
                  exact fin15Anchored_clause01279 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01280 chi hone hbad
                ·
                  exact fin15Anchored_clause01281 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01282 chi hone hbad
                ·
                  exact fin15Anchored_clause01283 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01284 chi hone hbad
                ·
                  exact fin15Anchored_clause01285 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01286 chi hone hbad
                ·
                  exact fin15Anchored_clause01287 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01288 chi hone hbad
                ·
                  exact fin15Anchored_clause01289 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01290 chi hone hbad
                ·
                  exact fin15Anchored_clause01291 chi hone hbad
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
                  exact fin15Anchored_clause01292 chi hone hbad
                ·
                  exact fin15Anchored_clause01293 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01294 chi hone hbad
                ·
                  exact fin15Anchored_clause01295 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01296 chi hone hbad
                ·
                  exact fin15Anchored_clause01297 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01298 chi hone hbad
                ·
                  exact fin15Anchored_clause01299 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01300 chi hone hbad
                ·
                  exact fin15Anchored_clause01301 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01302 chi hone hbad
                ·
                  exact fin15Anchored_clause01303 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01304 chi hone hbad
                ·
                  exact fin15Anchored_clause01305 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01306 chi hone hbad
                ·
                  exact fin15Anchored_clause01307 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01308 chi hone hbad
                ·
                  exact fin15Anchored_clause01309 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01310 chi hone hbad
                ·
                  exact fin15Anchored_clause01311 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01312 chi hone hbad
                ·
                  exact fin15Anchored_clause01313 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01314 chi hone hbad
                ·
                  exact fin15Anchored_clause01315 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01316 chi hone hbad
                ·
                  exact fin15Anchored_clause01317 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01318 chi hone hbad
                ·
                  exact fin15Anchored_clause01319 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01320 chi hone hbad
                ·
                  exact fin15Anchored_clause01321 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01322 chi hone hbad
                ·
                  exact fin15Anchored_clause01323 chi hone hbad
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
                exact fin15Anchored_clause01324 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01325 chi hone hbad
                ·
                  exact fin15Anchored_clause01326 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01327 chi hone hbad
                ·
                  exact fin15Anchored_clause01328 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01329 chi hone hbad
                ·
                  exact fin15Anchored_clause01330 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01331 chi hone hbad
                ·
                  exact fin15Anchored_clause01332 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01333 chi hone hbad
                ·
                  exact fin15Anchored_clause01334 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01335 chi hone hbad
                ·
                  exact fin15Anchored_clause01336 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01337 chi hone hbad
                ·
                  exact fin15Anchored_clause01338 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01339 chi hone hbad
                ·
                  exact fin15Anchored_clause01340 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01341 chi hone hbad
                ·
                  exact fin15Anchored_clause01342 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01343 chi hone hbad
                ·
                  exact fin15Anchored_clause01344 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01345 chi hone hbad
                ·
                  exact fin15Anchored_clause01346 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01347 chi hone hbad
                ·
                  exact fin15Anchored_clause01348 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01349 chi hone hbad
                ·
                  exact fin15Anchored_clause01350 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01351 chi hone hbad
                ·
                  exact fin15Anchored_clause01352 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01353 chi hone hbad
                ·
                  exact fin15Anchored_clause01354 chi hone hbad
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
                  exact fin15Anchored_clause01355 chi hone hbad
                ·
                  exact fin15Anchored_clause01356 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01357 chi hone hbad
                ·
                  exact fin15Anchored_clause01358 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01359 chi hone hbad
                ·
                  exact fin15Anchored_clause01360 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01361 chi hone hbad
                ·
                  exact fin15Anchored_clause01362 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01363 chi hone hbad
                ·
                  exact fin15Anchored_clause01364 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01365 chi hone hbad
                ·
                  exact fin15Anchored_clause01366 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01367 chi hone hbad
                ·
                  exact fin15Anchored_clause01368 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01369 chi hone hbad
                ·
                  exact fin15Anchored_clause01370 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01371 chi hone hbad
                ·
                  exact fin15Anchored_clause01372 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01373 chi hone hbad
                ·
                  exact fin15Anchored_clause01374 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01375 chi hone hbad
                ·
                  exact fin15Anchored_clause01376 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01377 chi hone hbad
                ·
                  exact fin15Anchored_clause01378 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01379 chi hone hbad
                ·
                  exact fin15Anchored_clause01380 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01381 chi hone hbad
                ·
                  exact fin15Anchored_clause01382 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01383 chi hone hbad
                ·
                  exact fin15Anchored_clause01384 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01385 chi hone hbad
                ·
                  exact fin15Anchored_clause01386 chi hone hbad
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
                exact fin15Anchored_clause01387 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01388 chi hone hbad
                ·
                  exact fin15Anchored_clause01389 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01390 chi hone hbad
                ·
                  exact fin15Anchored_clause01391 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01392 chi hone hbad
                ·
                  exact fin15Anchored_clause01393 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01394 chi hone hbad
                ·
                  exact fin15Anchored_clause01395 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01396 chi hone hbad
                ·
                  exact fin15Anchored_clause01397 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01398 chi hone hbad
                ·
                  exact fin15Anchored_clause01399 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01400 chi hone hbad
                ·
                  exact fin15Anchored_clause01401 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01402 chi hone hbad
                ·
                  exact fin15Anchored_clause01403 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01404 chi hone hbad
                ·
                  exact fin15Anchored_clause01405 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01406 chi hone hbad
                ·
                  exact fin15Anchored_clause01407 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01408 chi hone hbad
                ·
                  exact fin15Anchored_clause01409 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01410 chi hone hbad
                ·
                  exact fin15Anchored_clause01411 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01412 chi hone hbad
                ·
                  exact fin15Anchored_clause01413 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01414 chi hone hbad
                ·
                  exact fin15Anchored_clause01415 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01416 chi hone hbad
                ·
                  exact fin15Anchored_clause01417 chi hone hbad
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
                  exact fin15Anchored_clause01418 chi hone hbad
                ·
                  exact fin15Anchored_clause01419 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01420 chi hone hbad
                ·
                  exact fin15Anchored_clause01421 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01422 chi hone hbad
                ·
                  exact fin15Anchored_clause01423 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01424 chi hone hbad
                ·
                  exact fin15Anchored_clause01425 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01426 chi hone hbad
                ·
                  exact fin15Anchored_clause01427 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01428 chi hone hbad
                ·
                  exact fin15Anchored_clause01429 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01430 chi hone hbad
                ·
                  exact fin15Anchored_clause01431 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01432 chi hone hbad
                ·
                  exact fin15Anchored_clause01433 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01434 chi hone hbad
                ·
                  exact fin15Anchored_clause01435 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01436 chi hone hbad
                ·
                  exact fin15Anchored_clause01437 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01438 chi hone hbad
                ·
                  exact fin15Anchored_clause01439 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01440 chi hone hbad
                ·
                  exact fin15Anchored_clause01441 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01442 chi hone hbad
                ·
                  exact fin15Anchored_clause01443 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01444 chi hone hbad
                ·
                  exact fin15Anchored_clause01445 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01446 chi hone hbad
                ·
                  exact fin15Anchored_clause01447 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01448 chi hone hbad
                ·
                  exact fin15Anchored_clause01449 chi hone hbad
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
                  exact fin15Anchored_clause01450 chi hone hbad
                ·
                  exact fin15Anchored_clause01451 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01452 chi hone hbad
                ·
                  exact fin15Anchored_clause01453 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01454 chi hone hbad
                ·
                  exact fin15Anchored_clause01455 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01456 chi hone hbad
                ·
                  exact fin15Anchored_clause01457 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01458 chi hone hbad
                ·
                  exact fin15Anchored_clause01459 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01460 chi hone hbad
                ·
                  exact fin15Anchored_clause01461 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01462 chi hone hbad
                ·
                  exact fin15Anchored_clause01463 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01464 chi hone hbad
                ·
                  exact fin15Anchored_clause01465 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01466 chi hone hbad
                ·
                  exact fin15Anchored_clause01467 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01468 chi hone hbad
                ·
                  exact fin15Anchored_clause01469 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01470 chi hone hbad
                ·
                  exact fin15Anchored_clause01471 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01472 chi hone hbad
                ·
                  exact fin15Anchored_clause01473 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01474 chi hone hbad
                ·
                  exact fin15Anchored_clause01475 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01476 chi hone hbad
                ·
                  exact fin15Anchored_clause01477 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01478 chi hone hbad
                ·
                  exact fin15Anchored_clause01479 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01480 chi hone hbad
                ·
                  exact fin15Anchored_clause01481 chi hone hbad
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
                  exact fin15Anchored_clause01482 chi hone hbad
                ·
                  exact fin15Anchored_clause01483 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01484 chi hone hbad
                ·
                  exact fin15Anchored_clause01485 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01486 chi hone hbad
                ·
                  exact fin15Anchored_clause01487 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01488 chi hone hbad
                ·
                  exact fin15Anchored_clause01489 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01490 chi hone hbad
                ·
                  exact fin15Anchored_clause01491 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01492 chi hone hbad
                ·
                  exact fin15Anchored_clause01493 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01494 chi hone hbad
                ·
                  exact fin15Anchored_clause01495 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01496 chi hone hbad
                ·
                  exact fin15Anchored_clause01497 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01498 chi hone hbad
                ·
                  exact fin15Anchored_clause01499 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01500 chi hone hbad
                ·
                  exact fin15Anchored_clause01501 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01502 chi hone hbad
                ·
                  exact fin15Anchored_clause01503 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01504 chi hone hbad
                ·
                  exact fin15Anchored_clause01505 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01506 chi hone hbad
                ·
                  exact fin15Anchored_clause01507 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01508 chi hone hbad
                ·
                  exact fin15Anchored_clause01509 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01510 chi hone hbad
                ·
                  exact fin15Anchored_clause01511 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01512 chi hone hbad
                ·
                  exact fin15Anchored_clause01513 chi hone hbad

end ErdosSzekeres

end
