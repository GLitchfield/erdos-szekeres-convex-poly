module

public import ErdosSzekeres.Fin15AnchoredClauseChunk074
public import ErdosSzekeres.Fin15AnchoredClauseChunk075
public import ErdosSzekeres.Fin15AnchoredClauseChunk076

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 038. -/

theorem fin15Anchored_rejectSemanticSegment038
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom1050 chi) ∨
      ((Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom1050 chi) ∨
      (Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom1050 chi))) ∨
      (((¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom1051 chi) ∨
      (¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom1051 chi)) ∨
      ((¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom1051 chi) ∨
      (¬Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom1051 chi)))) ∨
      ((((Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom1051 chi) ∨
      (Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom1051 chi)) ∨
      ((Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom1051 chi) ∨
      (Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom1051 chi))) ∨
      (((Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom1051 chi) ∨
      (¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom1053 chi)) ∨
      ((¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom1053 chi) ∨
      (¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom1053 chi))))) ∨
      (((((¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom1053 chi) ∨
      (¬Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom1053 chi)) ∨
      ((¬Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom1053 chi) ∨
      (Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom1053 chi))) ∨
      (((Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom1053 chi) ∨
      (Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom1053 chi)) ∨
      ((Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom1053 chi) ∨
      (¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom1054 chi)))) ∨
      ((((¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom1054 chi) ∨
      (¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom1054 chi)) ∨
      ((¬Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom1054 chi) ∨
      (Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom1054 chi))) ∨
      (((Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom1054 chi) ∨
      (Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom1054 chi)) ∨
      ((Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom1054 chi) ∨
      (Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom1054 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom1055 chi) ∨
      (¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom1055 chi)) ∨
      ((¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom1055 chi) ∨
      (¬Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom1055 chi))) ∨
      (((Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom1055 chi) ∨
      (Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom1055 chi)) ∨
      ((Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom1055 chi) ∨
      (¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom1056 chi)))) ∨
      ((((¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1056 chi) ∨
      (¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1056 chi)) ∨
      ((¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom1056 chi) ∨
      (¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1056 chi))) ∨
      (((Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1056 chi) ∨
      (Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom1056 chi)) ∨
      ((Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1056 chi) ∨
      (Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1056 chi))))) ∨
      (((((Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom1056 chi) ∨
      (¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom1057 chi)) ∨
      ((¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom1057 chi) ∨
      (¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom1057 chi))) ∨
      (((Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom1057 chi) ∨
      (Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom1057 chi)) ∨
      ((¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom1058 chi) ∨
      (¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1058 chi)))) ∨
      ((((¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom1058 chi) ∨
      (¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1058 chi)) ∨
      ((Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1058 chi) ∨
      (Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1058 chi))) ∨
      (((Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom1058 chi) ∨
      (Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1058 chi)) ∨
      ((Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom1058 chi) ∨
      (¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom1059 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1059 chi) ∨
      ((¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom1059 chi) ∨
      (¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1059 chi))) ∨
      (((¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1059 chi) ∨
      (Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1059 chi)) ∨
      ((Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1059 chi) ∨
      (Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom1059 chi)))) ∨
      ((((Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1059 chi) ∨
      (Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom1059 chi)) ∨
      ((¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom1060 chi) ∨
      (¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1060 chi))) ∨
      (((¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom1060 chi) ∨
      (¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1060 chi)) ∨
      ((Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1060 chi) ∨
      (Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom1060 chi))))) ∨
      (((((Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1060 chi) ∨
      (Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom1060 chi)) ∨
      ((¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom1061 chi) ∨
      (¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom1061 chi))) ∨
      (((Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom1061 chi) ∨
      (Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom1061 chi)) ∨
      ((Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom1061 chi) ∨
      (Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom1061 chi)))) ∨
      ((((Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom1061 chi) ∨
      (Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom1061 chi)) ∨
      ((¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom1062 chi) ∨
      (¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1062 chi))) ∨
      (((¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom1062 chi) ∨
      (¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1062 chi)) ∨
      ((Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1062 chi) ∨
      (Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1062 chi)))))) ∨
      ((((((Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom1062 chi) ∨
      (Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1062 chi)) ∨
      ((Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom1062 chi) ∨
      (¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom1063 chi))) ∨
      (((¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1063 chi) ∨
      (¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom1063 chi)) ∨
      ((¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1063 chi) ∨
      (¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1063 chi)))) ∨
      ((((¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1063 chi) ∨
      (Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1063 chi)) ∨
      ((Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom1063 chi) ∨
      (Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1063 chi))) ∨
      (((Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom1063 chi) ∨
      (¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom1064 chi)) ∨
      ((¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1064 chi) ∨
      (¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom1064 chi))))) ∨
      (((((¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1064 chi) ∨
      (¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1064 chi)) ∨
      ((Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1064 chi) ∨
      (Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom1064 chi))) ∨
      (((Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1064 chi) ∨
      (Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom1064 chi)) ∨
      ((¬Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom1065 chi) ∨
      (¬Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom1065 chi)))) ∨
      ((((¬Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom1065 chi) ∨
      (Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom1065 chi)) ∨
      ((Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom1065 chi) ∨
      (Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom1065 chi))) ∨
      (((Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom1065 chi) ∨
      (¬Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0416 chi ∧
      Fin15AnchoredAtom1066 chi)) ∨
      ((Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0416 chi ∧
      Fin15AnchoredAtom1066 chi) ∨
      (Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0416 chi ∧
      Fin15AnchoredAtom1066 chi)))))))) ∨
      (((((((Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0416 chi ∧
      ¬Fin15AnchoredAtom1066 chi) ∨
      ((¬Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0417 chi ∧
      ¬Fin15AnchoredAtom1067 chi) ∨
      (¬Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0417 chi ∧
      Fin15AnchoredAtom1067 chi))) ∨
      (((Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0417 chi ∧
      ¬Fin15AnchoredAtom1067 chi) ∨
      (Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0417 chi ∧
      Fin15AnchoredAtom1067 chi)) ∨
      ((¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom1068 chi) ∨
      (¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1068 chi)))) ∨
      ((((¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom1068 chi) ∨
      (¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1068 chi)) ∨
      ((¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1068 chi) ∨
      (Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1068 chi))) ∨
      (((Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom1068 chi) ∨
      (Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1068 chi)) ∨
      ((Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1068 chi) ∨
      (Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom1068 chi))))) ∨
      (((((¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom1069 chi) ∨
      (¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom1069 chi)) ∨
      ((¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom1069 chi) ∨
      (¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom1069 chi))) ∨
      (((¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom1069 chi) ∨
      (Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom1069 chi)) ∨
      ((Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom1069 chi) ∨
      (Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom1069 chi)))) ∨
      ((((Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom1069 chi) ∨
      (¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom1070 chi)) ∨
      ((¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1070 chi) ∨
      (¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom1070 chi))) ∨
      (((¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1070 chi) ∨
      (¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1070 chi)) ∨
      ((Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1070 chi) ∨
      (Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1070 chi)))))) ∨
      ((((((Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom1070 chi) ∨
      (Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1070 chi)) ∨
      ((Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1070 chi) ∨
      (Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom1070 chi))) ∨
      (((¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom1071 chi) ∨
      (¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1071 chi)) ∨
      ((¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom1071 chi) ∨
      (¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1071 chi)))) ∨
      ((((Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1071 chi) ∨
      (Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1071 chi)) ∨
      ((Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom1071 chi) ∨
      (Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1071 chi))) ∨
      (((Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1071 chi) ∨
      (Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom1071 chi)) ∨
      ((¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom1073 chi) ∨
      (¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1073 chi))))) ∨
      (((((¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom1073 chi) ∨
      (¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1073 chi)) ∨
      ((Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1073 chi) ∨
      (Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1073 chi))) ∨
      (((Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom1073 chi) ∨
      (Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1073 chi)) ∨
      ((Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom1073 chi) ∨
      (¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom1074 chi)))) ∨
      ((((¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1074 chi) ∨
      (¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1074 chi)) ∨
      ((¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom1074 chi) ∨
      (¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1074 chi))) ∨
      (((¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1074 chi) ∨
      (Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1074 chi)) ∨
      ((Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom1074 chi) ∨
      (Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1074 chi))))))) ∨
      ((((((Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom1074 chi) ∨
      ((¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom1075 chi) ∨
      (¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1075 chi))) ∨
      (((¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1075 chi) ∨
      (Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1075 chi)) ∨
      ((Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1075 chi) ∨
      (Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1075 chi)))) ∨
      ((((Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom1075 chi) ∨
      (¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom1077 chi)) ∨
      ((¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1077 chi) ∨
      (¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom1077 chi))) ∨
      (((¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1077 chi) ∨
      (Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1077 chi)) ∨
      ((Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom1077 chi) ∨
      (Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1077 chi))))) ∨
      (((((Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom1077 chi) ∨
      (¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom1078 chi)) ∨
      ((¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1078 chi) ∨
      (¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom1078 chi))) ∨
      (((¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1078 chi) ∨
      (Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1078 chi)) ∨
      ((Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom1078 chi) ∨
      (Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1078 chi)))) ∨
      ((((Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom1078 chi) ∨
      (¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom1079 chi)) ∨
      ((¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom1079 chi) ∨
      (¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1079 chi))) ∨
      (((¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1079 chi) ∨
      (Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1079 chi)) ∨
      ((Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1079 chi) ∨
      (Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom1079 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom1083 chi) ∨
      (¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1083 chi)) ∨
      ((¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom1083 chi) ∨
      (¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1083 chi))) ∨
      (((¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1083 chi) ∨
      (Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1083 chi)) ∨
      ((Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1083 chi) ∨
      (Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom1083 chi)))) ∨
      ((((Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1083 chi) ∨
      (Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1083 chi)) ∨
      ((Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom1083 chi) ∨
      (¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom1084 chi))) ∨
      (((¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom1084 chi) ∨
      (¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1084 chi)) ∨
      ((¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1084 chi) ∨
      (Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1084 chi))))) ∨
      (((((Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1084 chi) ∨
      (Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1084 chi)) ∨
      ((Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom1084 chi) ∨
      (¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom1085 chi))) ∨
      (((¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom1085 chi) ∨
      (¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1085 chi)) ∨
      ((¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1085 chi) ∨
      (Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1085 chi)))) ∨
      ((((Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom1085 chi) ∨
      (Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1085 chi)) ∨
      ((Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1085 chi) ∨
      (Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom1085 chi))) ∨
      (((¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1086 chi) ∨
      (¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom1086 chi)) ∨
      ((¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1086 chi) ∨
      (¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1086 chi)))))))))) := by
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
                exact fin15Anchored_clause09591 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09592 chi hbad
                ·
                  exact fin15Anchored_clause09593 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09594 chi hbad
                ·
                  exact fin15Anchored_clause09595 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09596 chi hbad
                ·
                  exact fin15Anchored_clause09597 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09598 chi hbad
                ·
                  exact fin15Anchored_clause09599 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09600 chi hbad
                ·
                  exact fin15Anchored_clause09601 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09602 chi hbad
                ·
                  exact fin15Anchored_clause09603 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09604 chi hbad
                ·
                  exact fin15Anchored_clause09605 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09606 chi hbad
                ·
                  exact fin15Anchored_clause09607 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09608 chi hbad
                ·
                  exact fin15Anchored_clause09609 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09610 chi hbad
                ·
                  exact fin15Anchored_clause09611 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09612 chi hbad
                ·
                  exact fin15Anchored_clause09613 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09614 chi hbad
                ·
                  exact fin15Anchored_clause09615 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09616 chi hbad
                ·
                  exact fin15Anchored_clause09617 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09618 chi hbad
                ·
                  exact fin15Anchored_clause09619 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09620 chi hbad
                ·
                  exact fin15Anchored_clause09621 chi hbad
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
                  exact fin15Anchored_clause09622 chi hbad
                ·
                  exact fin15Anchored_clause09623 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09624 chi hbad
                ·
                  exact fin15Anchored_clause09625 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09626 chi hbad
                ·
                  exact fin15Anchored_clause09627 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09628 chi hbad
                ·
                  exact fin15Anchored_clause09629 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09630 chi hbad
                ·
                  exact fin15Anchored_clause09631 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09632 chi hbad
                ·
                  exact fin15Anchored_clause09633 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09634 chi hbad
                ·
                  exact fin15Anchored_clause09635 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09636 chi hbad
                ·
                  exact fin15Anchored_clause09637 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09638 chi hbad
                ·
                  exact fin15Anchored_clause09639 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09640 chi hbad
                ·
                  exact fin15Anchored_clause09641 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09642 chi hbad
                ·
                  exact fin15Anchored_clause09643 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09644 chi hbad
                ·
                  exact fin15Anchored_clause09645 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09646 chi hbad
                ·
                  exact fin15Anchored_clause09647 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09648 chi hbad
                ·
                  exact fin15Anchored_clause09649 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09650 chi hbad
                ·
                  exact fin15Anchored_clause09651 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09652 chi hbad
                ·
                  exact fin15Anchored_clause09653 chi hbad
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
                exact fin15Anchored_clause09654 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09655 chi hbad
                ·
                  exact fin15Anchored_clause09656 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09657 chi hbad
                ·
                  exact fin15Anchored_clause09658 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09659 chi hbad
                ·
                  exact fin15Anchored_clause09660 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09661 chi hbad
                ·
                  exact fin15Anchored_clause09662 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09663 chi hbad
                ·
                  exact fin15Anchored_clause09664 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09665 chi hbad
                ·
                  exact fin15Anchored_clause09666 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09667 chi hbad
                ·
                  exact fin15Anchored_clause09668 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09669 chi hbad
                ·
                  exact fin15Anchored_clause09670 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09671 chi hbad
                ·
                  exact fin15Anchored_clause09672 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09673 chi hbad
                ·
                  exact fin15Anchored_clause09674 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09675 chi hbad
                ·
                  exact fin15Anchored_clause09676 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09677 chi hbad
                ·
                  exact fin15Anchored_clause09678 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09679 chi hbad
                ·
                  exact fin15Anchored_clause09680 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09681 chi hbad
                ·
                  exact fin15Anchored_clause09682 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09683 chi hbad
                ·
                  exact fin15Anchored_clause09684 chi hbad
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
                  exact fin15Anchored_clause09685 chi hbad
                ·
                  exact fin15Anchored_clause09686 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09687 chi hbad
                ·
                  exact fin15Anchored_clause09688 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09689 chi hbad
                ·
                  exact fin15Anchored_clause09690 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09691 chi hbad
                ·
                  exact fin15Anchored_clause09692 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09693 chi hbad
                ·
                  exact fin15Anchored_clause09694 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09695 chi hbad
                ·
                  exact fin15Anchored_clause09696 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09697 chi hbad
                ·
                  exact fin15Anchored_clause09698 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09699 chi hbad
                ·
                  exact fin15Anchored_clause09700 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09701 chi hbad
                ·
                  exact fin15Anchored_clause09702 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09703 chi hbad
                ·
                  exact fin15Anchored_clause09704 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09705 chi hbad
                ·
                  exact fin15Anchored_clause09706 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09707 chi hbad
                ·
                  exact fin15Anchored_clause09708 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09709 chi hbad
                ·
                  exact fin15Anchored_clause09710 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09711 chi hbad
                ·
                  exact fin15Anchored_clause09712 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09713 chi hbad
                ·
                  exact fin15Anchored_clause09714 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09715 chi hbad
                ·
                  exact fin15Anchored_clause09716 chi hbad
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
                exact fin15Anchored_clause09717 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09718 chi hbad
                ·
                  exact fin15Anchored_clause09719 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09720 chi hbad
                ·
                  exact fin15Anchored_clause09721 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09722 chi hbad
                ·
                  exact fin15Anchored_clause09723 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09724 chi hbad
                ·
                  exact fin15Anchored_clause09725 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09726 chi hbad
                ·
                  exact fin15Anchored_clause09727 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09728 chi hbad
                ·
                  exact fin15Anchored_clause09729 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09730 chi hbad
                ·
                  exact fin15Anchored_clause09731 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09732 chi hbad
                ·
                  exact fin15Anchored_clause09733 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09734 chi hbad
                ·
                  exact fin15Anchored_clause09735 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09736 chi hbad
                ·
                  exact fin15Anchored_clause09737 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09738 chi hbad
                ·
                  exact fin15Anchored_clause09739 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09740 chi hbad
                ·
                  exact fin15Anchored_clause09741 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09742 chi hbad
                ·
                  exact fin15Anchored_clause09743 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09744 chi hbad
                ·
                  exact fin15Anchored_clause09745 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09746 chi hbad
                ·
                  exact fin15Anchored_clause09747 chi hbad
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
                  exact fin15Anchored_clause09748 chi hbad
                ·
                  exact fin15Anchored_clause09749 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09750 chi hbad
                ·
                  exact fin15Anchored_clause09751 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09752 chi hbad
                ·
                  exact fin15Anchored_clause09753 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09754 chi hbad
                ·
                  exact fin15Anchored_clause09755 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09756 chi hbad
                ·
                  exact fin15Anchored_clause09757 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09758 chi hbad
                ·
                  exact fin15Anchored_clause09759 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09760 chi hbad
                ·
                  exact fin15Anchored_clause09761 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09762 chi hbad
                ·
                  exact fin15Anchored_clause09763 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09764 chi hbad
                ·
                  exact fin15Anchored_clause09765 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09766 chi hbad
                ·
                  exact fin15Anchored_clause09767 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09768 chi hbad
                ·
                  exact fin15Anchored_clause09769 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09770 chi hbad
                ·
                  exact fin15Anchored_clause09771 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09772 chi hbad
                ·
                  exact fin15Anchored_clause09773 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09774 chi hbad
                ·
                  exact fin15Anchored_clause09775 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09776 chi hbad
                ·
                  exact fin15Anchored_clause09777 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09778 chi hbad
                ·
                  exact fin15Anchored_clause09779 chi hbad
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
                exact fin15Anchored_clause09780 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09781 chi hbad
                ·
                  exact fin15Anchored_clause09782 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09783 chi hbad
                ·
                  exact fin15Anchored_clause09784 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09785 chi hbad
                ·
                  exact fin15Anchored_clause09786 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09787 chi hbad
                ·
                  exact fin15Anchored_clause09788 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09789 chi hbad
                ·
                  exact fin15Anchored_clause09790 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09791 chi hbad
                ·
                  exact fin15Anchored_clause09792 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09793 chi hbad
                ·
                  exact fin15Anchored_clause09794 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09795 chi hbad
                ·
                  exact fin15Anchored_clause09796 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09797 chi hbad
                ·
                  exact fin15Anchored_clause09798 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09799 chi hbad
                ·
                  exact fin15Anchored_clause09800 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09801 chi hbad
                ·
                  exact fin15Anchored_clause09802 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09803 chi hbad
                ·
                  exact fin15Anchored_clause09804 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09805 chi hbad
                ·
                  exact fin15Anchored_clause09806 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09807 chi hbad
                ·
                  exact fin15Anchored_clause09808 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09809 chi hbad
                ·
                  exact fin15Anchored_clause09810 chi hbad
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
                  exact fin15Anchored_clause09811 chi hbad
                ·
                  exact fin15Anchored_clause09812 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09813 chi hbad
                ·
                  exact fin15Anchored_clause09814 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09815 chi hbad
                ·
                  exact fin15Anchored_clause09816 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09817 chi hbad
                ·
                  exact fin15Anchored_clause09818 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09819 chi hbad
                ·
                  exact fin15Anchored_clause09820 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09821 chi hbad
                ·
                  exact fin15Anchored_clause09822 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09823 chi hbad
                ·
                  exact fin15Anchored_clause09824 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09825 chi hbad
                ·
                  exact fin15Anchored_clause09826 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09827 chi hbad
                ·
                  exact fin15Anchored_clause09828 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09829 chi hbad
                ·
                  exact fin15Anchored_clause09830 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09831 chi hbad
                ·
                  exact fin15Anchored_clause09832 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09833 chi hbad
                ·
                  exact fin15Anchored_clause09834 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09835 chi hbad
                ·
                  exact fin15Anchored_clause09836 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09837 chi hbad
                ·
                  exact fin15Anchored_clause09838 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09839 chi hbad
                ·
                  exact fin15Anchored_clause09840 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09841 chi hbad
                ·
                  exact fin15Anchored_clause09842 chi hbad

end ErdosSzekeres

end
