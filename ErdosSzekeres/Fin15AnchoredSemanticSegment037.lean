module

public import ErdosSzekeres.Fin15AnchoredClauseChunk072
public import ErdosSzekeres.Fin15AnchoredClauseChunk073
public import ErdosSzekeres.Fin15AnchoredClauseChunk074

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 037. -/

theorem fin15Anchored_rejectSemanticSegment037
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom1019 chi) ∨
      ((¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom1019 chi) ∨
      (¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom1019 chi))) ∨
      (((Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom1019 chi) ∨
      (Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom1019 chi)) ∨
      ((Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom1019 chi) ∨
      (Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom1019 chi)))) ∨
      ((((Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom1019 chi) ∨
      (¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom1020 chi)) ∨
      ((¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom1020 chi) ∨
      (¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom1020 chi))) ∨
      (((¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom1020 chi) ∨
      (Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom1020 chi)) ∨
      ((Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom1020 chi) ∨
      (Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom1020 chi))))) ∨
      (((((Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom1020 chi) ∨
      (Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom1020 chi)) ∨
      ((¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom1021 chi) ∨
      (¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom1021 chi))) ∨
      (((¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom1021 chi) ∨
      (¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom1021 chi)) ∨
      ((¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom1021 chi) ∨
      (Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom1021 chi)))) ∨
      ((((Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom1021 chi) ∨
      (Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom1021 chi)) ∨
      ((Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom1021 chi) ∨
      (Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom1021 chi))) ∨
      (((¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom1022 chi) ∨
      (¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom1022 chi)) ∨
      ((¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom1022 chi) ∨
      (¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom1022 chi)))))) ∨
      ((((((Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom1022 chi) ∨
      (Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom1022 chi)) ∨
      ((Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom1022 chi) ∨
      (¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom1023 chi))) ∨
      (((¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom1023 chi) ∨
      (¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom1023 chi)) ∨
      ((¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom1023 chi) ∨
      (Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom1023 chi)))) ∨
      ((((Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom1023 chi) ∨
      (Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom1023 chi)) ∨
      ((Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom1023 chi) ∨
      (¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom1024 chi))) ∨
      (((¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom1024 chi) ∨
      (¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom1024 chi)) ∨
      ((¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom1024 chi) ∨
      (¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom1024 chi))))) ∨
      (((((¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom1024 chi) ∨
      (Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom1024 chi)) ∨
      ((Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom1024 chi) ∨
      (Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom1024 chi))) ∨
      (((Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom1024 chi) ∨
      (Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom1024 chi)) ∨
      ((¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom1025 chi) ∨
      (¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom1026 chi)))) ∨
      ((((¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom1026 chi) ∨
      (¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom1026 chi)) ∨
      ((¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom1026 chi) ∨
      (Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom1026 chi))) ∨
      (((Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom1026 chi) ∨
      (Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom1026 chi)) ∨
      ((Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom1026 chi) ∨
      (¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom1027 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom1027 chi) ∨
      ((¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom1027 chi) ∨
      (¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom1027 chi))) ∨
      (((¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom1027 chi) ∨
      (Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom1027 chi)) ∨
      ((Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom1027 chi) ∨
      (Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom1027 chi)))) ∨
      ((((Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom1027 chi) ∨
      (Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom1027 chi)) ∨
      ((¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom1028 chi) ∨
      (¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom1028 chi))) ∨
      (((¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom1028 chi) ∨
      (¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom1028 chi)) ∨
      ((¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom1028 chi) ∨
      (Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom1028 chi))))) ∨
      (((((Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom1028 chi) ∨
      (Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom1028 chi)) ∨
      ((Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom1028 chi) ∨
      (Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom1028 chi))) ∨
      (((Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom1028 chi) ∨
      (¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom1029 chi)) ∨
      ((¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom1029 chi) ∨
      (¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom1029 chi)))) ∨
      ((((¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom1029 chi) ∨
      (Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom1029 chi)) ∨
      ((Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom1029 chi) ∨
      (Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom1029 chi))) ∨
      (((Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom1029 chi) ∨
      (Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom1029 chi)) ∨
      ((¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom1030 chi) ∨
      (¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom1030 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom1030 chi) ∨
      (¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom1030 chi)) ∨
      ((¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom1030 chi) ∨
      (Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom1030 chi))) ∨
      (((Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom1030 chi) ∨
      (Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom1030 chi)) ∨
      ((Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom1030 chi) ∨
      (¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom1032 chi)))) ∨
      ((((¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom1032 chi) ∨
      (¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom1032 chi)) ∨
      ((¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom1032 chi) ∨
      (Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom1032 chi))) ∨
      (((Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom1032 chi) ∨
      (Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom1032 chi)) ∨
      ((Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom1032 chi) ∨
      (Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom1032 chi))))) ∨
      (((((¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom1033 chi) ∨
      (¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom1033 chi)) ∨
      ((¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom1033 chi) ∨
      (¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom1033 chi))) ∨
      (((¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom1033 chi) ∨
      (¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom1033 chi)) ∨
      ((Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom1033 chi) ∨
      (Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom1033 chi)))) ∨
      ((((Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom1033 chi) ∨
      (Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom1033 chi)) ∨
      ((¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom1034 chi) ∨
      (¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom1034 chi))) ∨
      (((¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom1034 chi) ∨
      (¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom1034 chi)) ∨
      ((¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom1034 chi) ∨
      (¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom1034 chi)))))))) ∨
      (((((((Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom1034 chi) ∨
      ((Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom1034 chi) ∨
      (Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom1034 chi))) ∨
      (((Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom1034 chi) ∨
      (Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom1034 chi)) ∨
      ((¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom1035 chi) ∨
      (¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom1035 chi)))) ∨
      ((((¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom1035 chi) ∨
      (¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom1035 chi)) ∨
      ((Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom1035 chi) ∨
      (Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom1035 chi))) ∨
      (((Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom1035 chi) ∨
      (Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom1035 chi)) ∨
      ((Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom1035 chi) ∨
      (Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom1035 chi))))) ∨
      (((((¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom1036 chi) ∨
      (¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom1036 chi)) ∨
      ((¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom1036 chi) ∨
      (Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom1036 chi))) ∨
      (((Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom1036 chi) ∨
      (¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom1037 chi)) ∨
      ((¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom1037 chi) ∨
      (¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom1037 chi)))) ∨
      ((((¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom1037 chi) ∨
      (¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom1037 chi)) ∨
      ((¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom1037 chi) ∨
      (Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom1037 chi))) ∨
      (((Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom1037 chi) ∨
      (Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom1037 chi)) ∨
      ((Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom1037 chi) ∨
      (¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom1038 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1038 chi) ∨
      (¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom1038 chi)) ∨
      ((¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1038 chi) ∨
      (¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1038 chi))) ∨
      (((Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1038 chi) ∨
      (Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1038 chi)) ∨
      ((Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom1038 chi) ∨
      (Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1038 chi)))) ∨
      ((((Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom1038 chi) ∨
      (¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom1039 chi)) ∨
      ((¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom1039 chi) ∨
      (¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom1039 chi))) ∨
      (((¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom1039 chi) ∨
      (¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom1039 chi)) ∨
      ((¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom1039 chi) ∨
      (Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom1039 chi))))) ∨
      (((((Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom1039 chi) ∨
      (Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom1039 chi)) ∨
      ((Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom1039 chi) ∨
      (Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom1039 chi))) ∨
      (((¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom1040 chi) ∨
      (¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom1040 chi)) ∨
      ((¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom1040 chi) ∨
      (¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom1040 chi)))) ∨
      ((((Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom1040 chi) ∨
      (¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom1041 chi)) ∨
      ((¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom1041 chi) ∨
      (¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom1041 chi))) ∨
      (((¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom1041 chi) ∨
      (¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom1041 chi)) ∨
      ((Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom1041 chi) ∨
      (Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom1041 chi))))))) ∨
      (((((((Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom1041 chi) ∨
      (Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom1041 chi)) ∨
      ((Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom1041 chi) ∨
      (¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom1042 chi))) ∨
      (((¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom1042 chi) ∨
      (¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom1042 chi)) ∨
      ((¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom1042 chi) ∨
      (Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom1042 chi)))) ∨
      ((((Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom1042 chi) ∨
      (Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom1042 chi)) ∨
      ((Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom1042 chi) ∨
      (¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom1043 chi))) ∨
      (((¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom1043 chi) ∨
      (¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom1043 chi)) ∨
      ((¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom1043 chi) ∨
      (Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom1043 chi))))) ∨
      (((((Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom1043 chi) ∨
      (Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom1043 chi)) ∨
      ((Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom1043 chi) ∨
      (¬Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom1044 chi))) ∨
      (((¬Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom1044 chi) ∨
      (Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom1044 chi)) ∨
      ((Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom1044 chi) ∨
      (Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom1044 chi)))) ∨
      ((((Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom1044 chi) ∨
      (¬Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0396 chi ∧
      Fin15AnchoredAtom1046 chi)) ∨
      ((Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      ¬Fin15AnchoredAtom1046 chi) ∨
      (¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom1047 chi))) ∨
      (((¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1047 chi) ∨
      (¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom1047 chi)) ∨
      ((¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1047 chi) ∨
      (¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1047 chi)))))) ∨
      ((((((Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1047 chi) ∨
      (Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1047 chi)) ∨
      ((Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom1047 chi) ∨
      (Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1047 chi))) ∨
      (((Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1047 chi) ∨
      (Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom1047 chi)) ∨
      ((¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom1048 chi) ∨
      (¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom1048 chi)))) ∨
      ((((¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom1048 chi) ∨
      (¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom1048 chi)) ∨
      ((¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom1048 chi) ∨
      (Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom1048 chi))) ∨
      (((Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom1048 chi) ∨
      (Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom1048 chi)) ∨
      ((Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom1048 chi) ∨
      (Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom1048 chi))))) ∨
      (((((¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom1049 chi) ∨
      (¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom1049 chi)) ∨
      ((¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom1049 chi) ∨
      (¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom1049 chi))) ∨
      (((Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom1049 chi) ∨
      (Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom1049 chi)) ∨
      ((Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom1049 chi) ∨
      (Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom1049 chi)))) ∨
      ((((Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom1049 chi) ∨
      (Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom1049 chi)) ∨
      ((¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom1050 chi) ∨
      (¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom1050 chi))) ∨
      (((¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom1050 chi) ∨
      (¬Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom1050 chi)) ∨
      ((Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom1050 chi) ∨
      (Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom1050 chi)))))))))) := by
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
                exact fin15Anchored_clause09338 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09339 chi hbad
                ·
                  exact fin15Anchored_clause09340 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09341 chi hbad
                ·
                  exact fin15Anchored_clause09342 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09343 chi hbad
                ·
                  exact fin15Anchored_clause09344 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09345 chi hbad
                ·
                  exact fin15Anchored_clause09346 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09347 chi hbad
                ·
                  exact fin15Anchored_clause09348 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09349 chi hbad
                ·
                  exact fin15Anchored_clause09350 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09351 chi hbad
                ·
                  exact fin15Anchored_clause09352 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09353 chi hbad
                ·
                  exact fin15Anchored_clause09354 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09355 chi hbad
                ·
                  exact fin15Anchored_clause09356 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09357 chi hbad
                ·
                  exact fin15Anchored_clause09358 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09359 chi hbad
                ·
                  exact fin15Anchored_clause09360 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09361 chi hbad
                ·
                  exact fin15Anchored_clause09362 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09363 chi hbad
                ·
                  exact fin15Anchored_clause09364 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09365 chi hbad
                ·
                  exact fin15Anchored_clause09366 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09367 chi hbad
                ·
                  exact fin15Anchored_clause09368 chi hbad
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
                  exact fin15Anchored_clause09369 chi hbad
                ·
                  exact fin15Anchored_clause09370 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09371 chi hbad
                ·
                  exact fin15Anchored_clause09372 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09373 chi hbad
                ·
                  exact fin15Anchored_clause09374 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09375 chi hbad
                ·
                  exact fin15Anchored_clause09376 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09377 chi hbad
                ·
                  exact fin15Anchored_clause09378 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09379 chi hbad
                ·
                  exact fin15Anchored_clause09380 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09381 chi hbad
                ·
                  exact fin15Anchored_clause09382 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09383 chi hbad
                ·
                  exact fin15Anchored_clause09384 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09385 chi hbad
                ·
                  exact fin15Anchored_clause09386 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09387 chi hbad
                ·
                  exact fin15Anchored_clause09388 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09389 chi hbad
                ·
                  exact fin15Anchored_clause09390 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09391 chi hbad
                ·
                  exact fin15Anchored_clause09392 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09393 chi hbad
                ·
                  exact fin15Anchored_clause09394 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09395 chi hbad
                ·
                  exact fin15Anchored_clause09396 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09397 chi hbad
                ·
                  exact fin15Anchored_clause09398 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09399 chi hbad
                ·
                  exact fin15Anchored_clause09400 chi hbad
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
                exact fin15Anchored_clause09401 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09402 chi hbad
                ·
                  exact fin15Anchored_clause09403 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09404 chi hbad
                ·
                  exact fin15Anchored_clause09405 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09406 chi hbad
                ·
                  exact fin15Anchored_clause09407 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09408 chi hbad
                ·
                  exact fin15Anchored_clause09409 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09410 chi hbad
                ·
                  exact fin15Anchored_clause09411 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09412 chi hbad
                ·
                  exact fin15Anchored_clause09413 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09414 chi hbad
                ·
                  exact fin15Anchored_clause09415 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09416 chi hbad
                ·
                  exact fin15Anchored_clause09417 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09418 chi hbad
                ·
                  exact fin15Anchored_clause09419 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09420 chi hbad
                ·
                  exact fin15Anchored_clause09421 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09422 chi hbad
                ·
                  exact fin15Anchored_clause09423 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09424 chi hbad
                ·
                  exact fin15Anchored_clause09425 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09426 chi hbad
                ·
                  exact fin15Anchored_clause09427 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09428 chi hbad
                ·
                  exact fin15Anchored_clause09429 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09430 chi hbad
                ·
                  exact fin15Anchored_clause09431 chi hbad
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
                  exact fin15Anchored_clause09432 chi hbad
                ·
                  exact fin15Anchored_clause09433 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09434 chi hbad
                ·
                  exact fin15Anchored_clause09435 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09436 chi hbad
                ·
                  exact fin15Anchored_clause09437 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09438 chi hbad
                ·
                  exact fin15Anchored_clause09439 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09440 chi hbad
                ·
                  exact fin15Anchored_clause09441 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09442 chi hbad
                ·
                  exact fin15Anchored_clause09443 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09444 chi hbad
                ·
                  exact fin15Anchored_clause09445 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09446 chi hbad
                ·
                  exact fin15Anchored_clause09447 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09448 chi hbad
                ·
                  exact fin15Anchored_clause09449 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09450 chi hbad
                ·
                  exact fin15Anchored_clause09451 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09452 chi hbad
                ·
                  exact fin15Anchored_clause09453 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09454 chi hbad
                ·
                  exact fin15Anchored_clause09455 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09456 chi hbad
                ·
                  exact fin15Anchored_clause09457 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09458 chi hbad
                ·
                  exact fin15Anchored_clause09459 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09460 chi hbad
                ·
                  exact fin15Anchored_clause09461 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09462 chi hbad
                ·
                  exact fin15Anchored_clause09463 chi hbad
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
                exact fin15Anchored_clause09464 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09465 chi hbad
                ·
                  exact fin15Anchored_clause09466 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09467 chi hbad
                ·
                  exact fin15Anchored_clause09468 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09469 chi hbad
                ·
                  exact fin15Anchored_clause09470 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09471 chi hbad
                ·
                  exact fin15Anchored_clause09472 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09473 chi hbad
                ·
                  exact fin15Anchored_clause09474 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09475 chi hbad
                ·
                  exact fin15Anchored_clause09476 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09477 chi hbad
                ·
                  exact fin15Anchored_clause09478 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09479 chi hbad
                ·
                  exact fin15Anchored_clause09480 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09481 chi hbad
                ·
                  exact fin15Anchored_clause09482 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09483 chi hbad
                ·
                  exact fin15Anchored_clause09484 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09485 chi hbad
                ·
                  exact fin15Anchored_clause09486 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09487 chi hbad
                ·
                  exact fin15Anchored_clause09488 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09489 chi hbad
                ·
                  exact fin15Anchored_clause09490 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09491 chi hbad
                ·
                  exact fin15Anchored_clause09492 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09493 chi hbad
                ·
                  exact fin15Anchored_clause09494 chi hbad
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
                  exact fin15Anchored_clause09495 chi hbad
                ·
                  exact fin15Anchored_clause09496 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09497 chi hbad
                ·
                  exact fin15Anchored_clause09498 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09499 chi hbad
                ·
                  exact fin15Anchored_clause09500 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09501 chi hbad
                ·
                  exact fin15Anchored_clause09502 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09503 chi hbad
                ·
                  exact fin15Anchored_clause09504 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09505 chi hbad
                ·
                  exact fin15Anchored_clause09506 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09507 chi hbad
                ·
                  exact fin15Anchored_clause09508 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09509 chi hbad
                ·
                  exact fin15Anchored_clause09510 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09511 chi hbad
                ·
                  exact fin15Anchored_clause09512 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09513 chi hbad
                ·
                  exact fin15Anchored_clause09514 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09515 chi hbad
                ·
                  exact fin15Anchored_clause09516 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09517 chi hbad
                ·
                  exact fin15Anchored_clause09518 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09519 chi hbad
                ·
                  exact fin15Anchored_clause09520 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09521 chi hbad
                ·
                  exact fin15Anchored_clause09522 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09523 chi hbad
                ·
                  exact fin15Anchored_clause09524 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09525 chi hbad
                ·
                  exact fin15Anchored_clause09526 chi hbad
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
                  exact fin15Anchored_clause09527 chi hbad
                ·
                  exact fin15Anchored_clause09528 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09529 chi hbad
                ·
                  exact fin15Anchored_clause09530 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09531 chi hbad
                ·
                  exact fin15Anchored_clause09532 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09533 chi hbad
                ·
                  exact fin15Anchored_clause09534 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09535 chi hbad
                ·
                  exact fin15Anchored_clause09536 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09537 chi hbad
                ·
                  exact fin15Anchored_clause09538 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09539 chi hbad
                ·
                  exact fin15Anchored_clause09540 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09541 chi hbad
                ·
                  exact fin15Anchored_clause09542 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09543 chi hbad
                ·
                  exact fin15Anchored_clause09544 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09545 chi hbad
                ·
                  exact fin15Anchored_clause09546 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09547 chi hbad
                ·
                  exact fin15Anchored_clause09548 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09549 chi hbad
                ·
                  exact fin15Anchored_clause09550 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09551 chi hbad
                ·
                  exact fin15Anchored_clause09552 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09553 chi hbad
                ·
                  exact fin15Anchored_clause09554 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09555 chi hbad
                ·
                  exact fin15Anchored_clause09556 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09557 chi hbad
                ·
                  exact fin15Anchored_clause09558 chi hbad
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
                  exact fin15Anchored_clause09559 chi hbad
                ·
                  exact fin15Anchored_clause09560 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09561 chi hbad
                ·
                  exact fin15Anchored_clause09562 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09563 chi hbad
                ·
                  exact fin15Anchored_clause09564 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09565 chi hbad
                ·
                  exact fin15Anchored_clause09566 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09567 chi hbad
                ·
                  exact fin15Anchored_clause09568 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09569 chi hbad
                ·
                  exact fin15Anchored_clause09570 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09571 chi hbad
                ·
                  exact fin15Anchored_clause09572 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09573 chi hbad
                ·
                  exact fin15Anchored_clause09574 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09575 chi hbad
                ·
                  exact fin15Anchored_clause09576 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09577 chi hbad
                ·
                  exact fin15Anchored_clause09578 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09579 chi hbad
                ·
                  exact fin15Anchored_clause09580 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09581 chi hbad
                ·
                  exact fin15Anchored_clause09582 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09583 chi hbad
                ·
                  exact fin15Anchored_clause09584 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09585 chi hbad
                ·
                  exact fin15Anchored_clause09586 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09587 chi hbad
                ·
                  exact fin15Anchored_clause09588 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09589 chi hbad
                ·
                  exact fin15Anchored_clause09590 chi hbad

end ErdosSzekeres

end
