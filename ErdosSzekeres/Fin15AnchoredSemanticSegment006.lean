module

public import ErdosSzekeres.Fin15AnchoredClauseChunk011
public import ErdosSzekeres.Fin15AnchoredClauseChunk012
public import ErdosSzekeres.Fin15AnchoredClauseChunk013

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 006. -/

theorem fin15Anchored_rejectSemanticSegment006
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0373 chi) ∨
      ((Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0373 chi) ∨
      (Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0373 chi))) ∨
      (((¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0374 chi) ∨
      (¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0374 chi)) ∨
      ((¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0374 chi) ∨
      (¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0374 chi)))) ∨
      ((((Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0374 chi) ∨
      (Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0374 chi)) ∨
      ((Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0374 chi) ∨
      (Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0374 chi))) ∨
      (((¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0375 chi) ∨
      (¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0375 chi)) ∨
      ((¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0375 chi) ∨
      (¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0375 chi))))) ∨
      (((((Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0375 chi) ∨
      (Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0375 chi)) ∨
      ((Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0375 chi) ∨
      (¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0376 chi))) ∨
      (((¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0376 chi) ∨
      (¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0376 chi)) ∨
      ((¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0376 chi) ∨
      (Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0376 chi)))) ∨
      ((((Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0376 chi) ∨
      (Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0376 chi)) ∨
      ((Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0376 chi) ∨
      (¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0377 chi))) ∨
      (((¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0377 chi) ∨
      (¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0377 chi)) ∨
      ((¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0377 chi) ∨
      (Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0377 chi)))))) ∨
      ((((((Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0377 chi) ∨
      (Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0377 chi)) ∨
      ((Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0377 chi) ∨
      (¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0378 chi))) ∨
      (((¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0378 chi) ∨
      (¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0378 chi)) ∨
      ((¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0378 chi) ∨
      (Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0378 chi)))) ∨
      ((((Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0378 chi) ∨
      (Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0378 chi)) ∨
      ((Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0378 chi) ∨
      (¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0379 chi))) ∨
      (((¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0379 chi) ∨
      (¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0379 chi)) ∨
      ((¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0379 chi) ∨
      (Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0379 chi))))) ∨
      (((((Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0379 chi) ∨
      (Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0379 chi)) ∨
      ((Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0379 chi) ∨
      (¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0380 chi))) ∨
      (((¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0380 chi) ∨
      (¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0380 chi)) ∨
      ((¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0380 chi) ∨
      (Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0380 chi)))) ∨
      ((((Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0380 chi) ∨
      (Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0380 chi)) ∨
      ((Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0380 chi) ∨
      (¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0382 chi))) ∨
      (((¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0382 chi) ∨
      (¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0382 chi)) ∨
      ((¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0382 chi) ∨
      (Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0382 chi))))))) ∨
      ((((((Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0382 chi) ∨
      ((Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0382 chi) ∨
      (Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0382 chi))) ∨
      (((¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0383 chi) ∨
      (¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0383 chi)) ∨
      ((¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0383 chi) ∨
      (¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0383 chi)))) ∨
      ((((Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0383 chi) ∨
      (Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0383 chi)) ∨
      ((Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0383 chi) ∨
      (Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0383 chi))) ∨
      (((¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0384 chi) ∨
      (¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0384 chi)) ∨
      ((¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0384 chi) ∨
      (¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0384 chi))))) ∨
      (((((Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0384 chi) ∨
      (Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0384 chi)) ∨
      ((Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0384 chi) ∨
      (Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0384 chi))) ∨
      (((¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0385 chi) ∨
      (¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0385 chi)) ∨
      ((¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0385 chi) ∨
      (¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0385 chi)))) ∨
      ((((Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0385 chi) ∨
      (Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0385 chi)) ∨
      ((Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0385 chi) ∨
      (Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0385 chi))) ∨
      (((¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0386 chi) ∨
      (¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0386 chi)) ∨
      ((¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0386 chi) ∨
      (¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0386 chi)))))) ∨
      ((((((Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0386 chi) ∨
      (Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0386 chi)) ∨
      ((Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0386 chi) ∨
      (Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0386 chi))) ∨
      (((¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0387 chi) ∨
      (¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0387 chi)) ∨
      ((¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0387 chi) ∨
      (¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0387 chi)))) ∨
      ((((Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0387 chi) ∨
      (Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0387 chi)) ∨
      ((Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0387 chi) ∨
      (Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0387 chi))) ∨
      (((¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0388 chi) ∨
      (¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0388 chi)) ∨
      ((¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0388 chi) ∨
      (¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0388 chi))))) ∨
      (((((Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0388 chi) ∨
      (Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0388 chi)) ∨
      ((Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0388 chi) ∨
      (Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0388 chi))) ∨
      (((¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0389 chi) ∨
      (¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0389 chi)) ∨
      ((¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0389 chi) ∨
      (¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0389 chi)))) ∨
      ((((Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0389 chi) ∨
      (Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0389 chi)) ∨
      ((Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0389 chi) ∨
      (Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0389 chi))) ∨
      (((¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0390 chi) ∨
      (¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0390 chi)) ∨
      ((¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0390 chi) ∨
      (¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0390 chi)))))))) ∨
      (((((((Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0390 chi) ∨
      ((Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0390 chi) ∨
      (Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0390 chi))) ∨
      (((¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0391 chi) ∨
      (¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0391 chi)) ∨
      ((¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0391 chi) ∨
      (¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0391 chi)))) ∨
      ((((Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0391 chi) ∨
      (Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0391 chi)) ∨
      ((Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0391 chi) ∨
      (Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0391 chi))) ∨
      (((¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0392 chi) ∨
      (¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0392 chi)) ∨
      ((¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0392 chi) ∨
      (¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0392 chi))))) ∨
      (((((Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0392 chi) ∨
      (Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0392 chi)) ∨
      ((Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0392 chi) ∨
      (Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0392 chi))) ∨
      (((¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0393 chi) ∨
      (¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0393 chi)) ∨
      ((¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0393 chi) ∨
      (¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0393 chi)))) ∨
      ((((Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0393 chi) ∨
      (Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0393 chi)) ∨
      ((Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0393 chi) ∨
      (Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0393 chi))) ∨
      (((¬Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0394 chi) ∨
      (¬Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0394 chi)) ∨
      ((¬Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0394 chi) ∨
      (¬Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0394 chi)))))) ∨
      ((((((Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0394 chi) ∨
      (Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0394 chi)) ∨
      ((Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0394 chi) ∨
      (Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0394 chi))) ∨
      (((¬Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0396 chi) ∨
      (¬Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0396 chi)) ∨
      ((Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0396 chi) ∨
      (Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0396 chi)))) ∨
      ((((¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0397 chi) ∨
      (¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0397 chi)) ∨
      ((¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0397 chi) ∨
      (¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0397 chi))) ∨
      (((Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0397 chi) ∨
      (Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0397 chi)) ∨
      ((Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0397 chi) ∨
      (Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0397 chi))))) ∨
      (((((¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0398 chi) ∨
      (¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0398 chi)) ∨
      ((¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0398 chi) ∨
      (¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0398 chi))) ∨
      (((Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0398 chi) ∨
      (Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0398 chi)) ∨
      ((Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0398 chi) ∨
      (Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0398 chi)))) ∨
      ((((¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0399 chi) ∨
      (¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0399 chi)) ∨
      ((¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0399 chi) ∨
      (¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0399 chi))) ∨
      (((Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0399 chi) ∨
      (Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0399 chi)) ∨
      ((Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0399 chi) ∨
      (Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0399 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0400 chi) ∨
      ((¬Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0400 chi) ∨
      (¬Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0400 chi))) ∨
      (((¬Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0400 chi) ∨
      (Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0400 chi)) ∨
      ((Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0400 chi) ∨
      (Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0400 chi)))) ∨
      ((((Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0400 chi) ∨
      (¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0401 chi)) ∨
      ((¬Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0401 chi) ∨
      (¬Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0401 chi))) ∨
      (((¬Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0401 chi) ∨
      (Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0401 chi)) ∨
      ((Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0401 chi) ∨
      (Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0401 chi))))) ∨
      (((((Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0401 chi) ∨
      (¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0403 chi)) ∨
      ((¬Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0403 chi) ∨
      (¬Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0403 chi))) ∨
      (((¬Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0403 chi) ∨
      (Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0403 chi)) ∨
      ((Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0403 chi) ∨
      (Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0403 chi)))) ∨
      ((((Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0403 chi) ∨
      (¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0404 chi)) ∨
      ((¬Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0404 chi) ∨
      (¬Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0404 chi))) ∨
      (((¬Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0404 chi) ∨
      (Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0404 chi)) ∨
      ((Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0404 chi) ∨
      (Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0404 chi)))))) ∨
      ((((((Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0404 chi) ∨
      (¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0405 chi)) ∨
      ((¬Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0405 chi) ∨
      (¬Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0405 chi))) ∨
      (((¬Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0405 chi) ∨
      (Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0405 chi)) ∨
      ((Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0405 chi) ∨
      (Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0405 chi)))) ∨
      ((((Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0405 chi) ∨
      (¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0406 chi)) ∨
      ((¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0406 chi) ∨
      (¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0406 chi))) ∨
      (((¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0406 chi) ∨
      (Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0406 chi)) ∨
      ((Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0406 chi) ∨
      (Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0406 chi))))) ∨
      (((((Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0406 chi) ∨
      (¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0407 chi)) ∨
      ((¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0407 chi) ∨
      (¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0407 chi))) ∨
      (((¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0407 chi) ∨
      (Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0407 chi)) ∨
      ((Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0407 chi) ∨
      (Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0407 chi)))) ∨
      ((((¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0408 chi) ∨
      (¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0408 chi)) ∨
      ((¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0408 chi) ∨
      (¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0408 chi))) ∨
      (((Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0408 chi) ∨
      (Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0408 chi)) ∨
      ((Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0408 chi) ∨
      (Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0408 chi)))))))))) := by
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
                exact fin15Anchored_clause01514 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01515 chi hone hbad
                ·
                  exact fin15Anchored_clause01516 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01517 chi hone hbad
                ·
                  exact fin15Anchored_clause01518 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01519 chi hone hbad
                ·
                  exact fin15Anchored_clause01520 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01521 chi hone hbad
                ·
                  exact fin15Anchored_clause01522 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01523 chi hone hbad
                ·
                  exact fin15Anchored_clause01524 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01525 chi hone hbad
                ·
                  exact fin15Anchored_clause01526 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01527 chi hone hbad
                ·
                  exact fin15Anchored_clause01528 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01529 chi hone hbad
                ·
                  exact fin15Anchored_clause01530 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01531 chi hone hbad
                ·
                  exact fin15Anchored_clause01532 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01533 chi hone hbad
                ·
                  exact fin15Anchored_clause01534 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01535 chi hone hbad
                ·
                  exact fin15Anchored_clause01536 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01537 chi hone hbad
                ·
                  exact fin15Anchored_clause01538 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01539 chi hone hbad
                ·
                  exact fin15Anchored_clause01540 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01541 chi hone hbad
                ·
                  exact fin15Anchored_clause01542 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01543 chi hone hbad
                ·
                  exact fin15Anchored_clause01544 chi hone hbad
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
                  exact fin15Anchored_clause01545 chi hone hbad
                ·
                  exact fin15Anchored_clause01546 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01547 chi hone hbad
                ·
                  exact fin15Anchored_clause01548 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01549 chi hone hbad
                ·
                  exact fin15Anchored_clause01550 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01551 chi hone hbad
                ·
                  exact fin15Anchored_clause01552 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01553 chi hone hbad
                ·
                  exact fin15Anchored_clause01554 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01555 chi hone hbad
                ·
                  exact fin15Anchored_clause01556 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01557 chi hone hbad
                ·
                  exact fin15Anchored_clause01558 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01559 chi hone hbad
                ·
                  exact fin15Anchored_clause01560 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01561 chi hone hbad
                ·
                  exact fin15Anchored_clause01562 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01563 chi hone hbad
                ·
                  exact fin15Anchored_clause01564 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01565 chi hone hbad
                ·
                  exact fin15Anchored_clause01566 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01567 chi hone hbad
                ·
                  exact fin15Anchored_clause01568 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01569 chi hone hbad
                ·
                  exact fin15Anchored_clause01570 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01571 chi hone hbad
                ·
                  exact fin15Anchored_clause01572 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01573 chi hone hbad
                ·
                  exact fin15Anchored_clause01574 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01575 chi hone hbad
                ·
                  exact fin15Anchored_clause01576 chi hone hbad
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
                exact fin15Anchored_clause01577 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01578 chi hone hbad
                ·
                  exact fin15Anchored_clause01579 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01580 chi hone hbad
                ·
                  exact fin15Anchored_clause01581 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01582 chi hone hbad
                ·
                  exact fin15Anchored_clause01583 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01584 chi hone hbad
                ·
                  exact fin15Anchored_clause01585 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01586 chi hone hbad
                ·
                  exact fin15Anchored_clause01587 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01588 chi hone hbad
                ·
                  exact fin15Anchored_clause01589 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01590 chi hone hbad
                ·
                  exact fin15Anchored_clause01591 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01592 chi hone hbad
                ·
                  exact fin15Anchored_clause01593 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01594 chi hone hbad
                ·
                  exact fin15Anchored_clause01595 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01596 chi hone hbad
                ·
                  exact fin15Anchored_clause01597 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01598 chi hone hbad
                ·
                  exact fin15Anchored_clause01599 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01600 chi hone hbad
                ·
                  exact fin15Anchored_clause01601 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01602 chi hone hbad
                ·
                  exact fin15Anchored_clause01603 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01604 chi hone hbad
                ·
                  exact fin15Anchored_clause01605 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01606 chi hone hbad
                ·
                  exact fin15Anchored_clause01607 chi hone hbad
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
                  exact fin15Anchored_clause01608 chi hone hbad
                ·
                  exact fin15Anchored_clause01609 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01610 chi hone hbad
                ·
                  exact fin15Anchored_clause01611 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01612 chi hone hbad
                ·
                  exact fin15Anchored_clause01613 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01614 chi hone hbad
                ·
                  exact fin15Anchored_clause01615 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01616 chi hone hbad
                ·
                  exact fin15Anchored_clause01617 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01618 chi hone hbad
                ·
                  exact fin15Anchored_clause01619 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01620 chi hone hbad
                ·
                  exact fin15Anchored_clause01621 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01622 chi hone hbad
                ·
                  exact fin15Anchored_clause01623 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01624 chi hone hbad
                ·
                  exact fin15Anchored_clause01625 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01626 chi hone hbad
                ·
                  exact fin15Anchored_clause01627 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01628 chi hone hbad
                ·
                  exact fin15Anchored_clause01629 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01630 chi hone hbad
                ·
                  exact fin15Anchored_clause01631 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01632 chi hone hbad
                ·
                  exact fin15Anchored_clause01633 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01634 chi hone hbad
                ·
                  exact fin15Anchored_clause01635 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01636 chi hone hbad
                ·
                  exact fin15Anchored_clause01637 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01638 chi hone hbad
                ·
                  exact fin15Anchored_clause01639 chi hone hbad
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
                exact fin15Anchored_clause01640 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01641 chi hone hbad
                ·
                  exact fin15Anchored_clause01642 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01643 chi hone hbad
                ·
                  exact fin15Anchored_clause01644 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01645 chi hone hbad
                ·
                  exact fin15Anchored_clause01646 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01647 chi hone hbad
                ·
                  exact fin15Anchored_clause01648 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01649 chi hone hbad
                ·
                  exact fin15Anchored_clause01650 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01651 chi hone hbad
                ·
                  exact fin15Anchored_clause01652 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01653 chi hone hbad
                ·
                  exact fin15Anchored_clause01654 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01655 chi hone hbad
                ·
                  exact fin15Anchored_clause01656 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01657 chi hone hbad
                ·
                  exact fin15Anchored_clause01658 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01659 chi hone hbad
                ·
                  exact fin15Anchored_clause01660 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01661 chi hone hbad
                ·
                  exact fin15Anchored_clause01662 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01663 chi hone hbad
                ·
                  exact fin15Anchored_clause01664 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01665 chi hone hbad
                ·
                  exact fin15Anchored_clause01666 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01667 chi hone hbad
                ·
                  exact fin15Anchored_clause01668 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01669 chi hone hbad
                ·
                  exact fin15Anchored_clause01670 chi hone hbad
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
                  exact fin15Anchored_clause01671 chi hone hbad
                ·
                  exact fin15Anchored_clause01672 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01673 chi hone hbad
                ·
                  exact fin15Anchored_clause01674 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01675 chi hone hbad
                ·
                  exact fin15Anchored_clause01676 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01677 chi hone hbad
                ·
                  exact fin15Anchored_clause01678 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01679 chi hone hbad
                ·
                  exact fin15Anchored_clause01680 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01681 chi hone hbad
                ·
                  exact fin15Anchored_clause01682 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01683 chi hone hbad
                ·
                  exact fin15Anchored_clause01684 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01685 chi hone hbad
                ·
                  exact fin15Anchored_clause01686 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01687 chi hone hbad
                ·
                  exact fin15Anchored_clause01688 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01689 chi hone hbad
                ·
                  exact fin15Anchored_clause01690 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01691 chi hone hbad
                ·
                  exact fin15Anchored_clause01692 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01693 chi hone hbad
                ·
                  exact fin15Anchored_clause01694 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01695 chi hone hbad
                ·
                  exact fin15Anchored_clause01696 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01697 chi hone hbad
                ·
                  exact fin15Anchored_clause01698 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01699 chi hone hbad
                ·
                  exact fin15Anchored_clause01700 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01701 chi hone hbad
                ·
                  exact fin15Anchored_clause01702 chi hone hbad
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
                exact fin15Anchored_clause01703 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01704 chi hone hbad
                ·
                  exact fin15Anchored_clause01705 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01706 chi hone hbad
                ·
                  exact fin15Anchored_clause01707 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01708 chi hone hbad
                ·
                  exact fin15Anchored_clause01709 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01710 chi hone hbad
                ·
                  exact fin15Anchored_clause01711 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01712 chi hone hbad
                ·
                  exact fin15Anchored_clause01713 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01714 chi hone hbad
                ·
                  exact fin15Anchored_clause01715 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01716 chi hone hbad
                ·
                  exact fin15Anchored_clause01717 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01718 chi hone hbad
                ·
                  exact fin15Anchored_clause01719 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01720 chi hone hbad
                ·
                  exact fin15Anchored_clause01721 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01722 chi hone hbad
                ·
                  exact fin15Anchored_clause01723 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01724 chi hone hbad
                ·
                  exact fin15Anchored_clause01725 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01726 chi hone hbad
                ·
                  exact fin15Anchored_clause01727 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01728 chi hone hbad
                ·
                  exact fin15Anchored_clause01729 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01730 chi hone hbad
                ·
                  exact fin15Anchored_clause01731 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01732 chi hone hbad
                ·
                  exact fin15Anchored_clause01733 chi hone hbad
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
                  exact fin15Anchored_clause01734 chi hone hbad
                ·
                  exact fin15Anchored_clause01735 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01736 chi hone hbad
                ·
                  exact fin15Anchored_clause01737 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01738 chi hone hbad
                ·
                  exact fin15Anchored_clause01739 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01740 chi hone hbad
                ·
                  exact fin15Anchored_clause01741 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01742 chi hone hbad
                ·
                  exact fin15Anchored_clause01743 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01744 chi hone hbad
                ·
                  exact fin15Anchored_clause01745 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01746 chi hone hbad
                ·
                  exact fin15Anchored_clause01747 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01748 chi hone hbad
                ·
                  exact fin15Anchored_clause01749 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01750 chi hone hbad
                ·
                  exact fin15Anchored_clause01751 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01752 chi hone hbad
                ·
                  exact fin15Anchored_clause01753 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01754 chi hone hbad
                ·
                  exact fin15Anchored_clause01755 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01756 chi hone hbad
                ·
                  exact fin15Anchored_clause01757 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01758 chi hone hbad
                ·
                  exact fin15Anchored_clause01759 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01760 chi hone hbad
                ·
                  exact fin15Anchored_clause01761 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01762 chi hone hbad
                ·
                  exact fin15Anchored_clause01763 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01764 chi hone hbad
                ·
                  exact fin15Anchored_clause01765 chi hone hbad

end ErdosSzekeres

end
