module

public import ErdosSzekeres.Fin15AnchoredClauseChunk076
public import ErdosSzekeres.Fin15AnchoredClauseChunk077
public import ErdosSzekeres.Fin15AnchoredClauseChunk078

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 039. -/

theorem fin15Anchored_rejectSemanticSegment039
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom1087 chi) ∨
      ((¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1087 chi) ∨
      (¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1087 chi))) ∨
      (((¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom1087 chi) ∨
      (¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1087 chi)) ∨
      ((Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1087 chi) ∨
      (Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom1087 chi)))) ∨
      ((((Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1087 chi) ∨
      (Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom1087 chi)) ∨
      ((¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom1088 chi) ∨
      (¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1088 chi))) ∨
      (((¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom1088 chi) ∨
      (¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1088 chi)) ∨
      ((¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1088 chi) ∨
      (Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1088 chi))))) ∨
      (((((Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1088 chi) ∨
      (Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom1088 chi)) ∨
      ((Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1088 chi) ∨
      (Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom1088 chi))) ∨
      (((¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom1089 chi) ∨
      (¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1089 chi)) ∨
      ((¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom1089 chi) ∨
      (¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1089 chi)))) ∨
      ((((¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1089 chi) ∨
      (¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1089 chi)) ∨
      ((Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1089 chi) ∨
      (Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom1089 chi))) ∨
      (((Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1089 chi) ∨
      (Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom1089 chi)) ∨
      ((¬Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom1090 chi) ∨
      (¬Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom1090 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom1090 chi) ∨
      (¬Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom1090 chi)) ∨
      ((Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom1090 chi) ∨
      (Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom1090 chi))) ∨
      (((Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom1090 chi) ∨
      (Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom1090 chi)) ∨
      ((Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom1090 chi) ∨
      (¬Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0441 chi ∧
      ¬Fin15AnchoredAtom1091 chi)))) ∨
      ((((¬Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom1092 chi) ∨
      (¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom1093 chi)) ∨
      ((¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1093 chi) ∨
      (¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom1093 chi))) ∨
      (((¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1093 chi) ∨
      (¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1093 chi)) ∨
      ((Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1093 chi) ∨
      (Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom1093 chi))))) ∨
      (((((Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1093 chi) ∨
      (Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom1093 chi)) ∨
      ((¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom1094 chi) ∨
      (¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1094 chi))) ∨
      (((¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom1094 chi) ∨
      (¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1094 chi)) ∨
      ((Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1094 chi) ∨
      (Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1094 chi)))) ∨
      ((((Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom1094 chi) ∨
      (Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1094 chi)) ∨
      ((Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1094 chi) ∨
      (Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom1094 chi))) ∨
      (((¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom1095 chi) ∨
      (¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1095 chi)) ∨
      ((¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom1095 chi) ∨
      (¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1095 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1095 chi) ∨
      ((Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1095 chi) ∨
      (Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1095 chi))) ∨
      (((Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom1095 chi) ∨
      (Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1095 chi)) ∨
      ((Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom1095 chi) ∨
      (¬Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom1096 chi)))) ∨
      ((((¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1096 chi) ∨
      (Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1096 chi)) ∨
      ((Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom1096 chi) ∨
      (¬Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom1097 chi))) ∨
      (((Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom1097 chi) ∨
      (Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom1097 chi)) ∨
      ((Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom1097 chi) ∨
      (¬Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      ¬Fin15AnchoredAtom1098 chi))))) ∨
      (((((¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0448 chi ∧
      Fin15AnchoredAtom1098 chi) ∨
      (Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      ¬Fin15AnchoredAtom1098 chi)) ∨
      ((Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      Fin15AnchoredAtom1098 chi) ∨
      (¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1099 chi))) ∨
      (((¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1099 chi) ∨
      (¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1099 chi)) ∨
      ((¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1099 chi) ∨
      (Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1099 chi)))) ∨
      ((((Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1099 chi) ∨
      (Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1099 chi)) ∨
      ((Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1099 chi) ∨
      (Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1099 chi))) ∨
      (((¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1100 chi) ∨
      (¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1100 chi)) ∨
      ((¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1100 chi) ∨
      (¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1100 chi)))))) ∨
      ((((((Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1100 chi) ∨
      (Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1100 chi)) ∨
      ((Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1100 chi) ∨
      (Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1100 chi))) ∨
      (((Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1100 chi) ∨
      (Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1100 chi)) ∨
      ((¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1101 chi) ∨
      (¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1101 chi)))) ∨
      ((((¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1101 chi) ∨
      (¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1101 chi)) ∨
      ((Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1101 chi) ∨
      (Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1101 chi))) ∨
      (((Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1101 chi) ∨
      (Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1101 chi)) ∨
      ((Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1101 chi) ∨
      (Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1101 chi))))) ∨
      (((((¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom1102 chi) ∨
      (¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom1102 chi)) ∨
      ((¬Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1102 chi) ∨
      (Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1102 chi))) ∨
      (((Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1102 chi) ∨
      (¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom1103 chi)) ∨
      ((¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1103 chi) ∨
      (¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom1103 chi)))) ∨
      ((((¬Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1103 chi) ∨
      (Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1103 chi)) ∨
      ((Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1103 chi) ∨
      (Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom1103 chi))) ∨
      (((¬Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0454 chi ∧
      Fin15AnchoredAtom1104 chi) ∨
      (Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0454 chi ∧
      ¬Fin15AnchoredAtom1104 chi)) ∨
      ((¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1105 chi) ∨
      (¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1105 chi)))))))) ∨
      (((((((¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1105 chi) ∨
      ((¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1105 chi) ∨
      (¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1105 chi))) ∨
      (((Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1105 chi) ∨
      (Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1105 chi)) ∨
      ((Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1105 chi) ∨
      (Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1105 chi)))) ∨
      ((((Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1105 chi) ∨
      (Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1105 chi)) ∨
      ((¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom1106 chi) ∨
      (¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom1106 chi))) ∨
      (((¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom1106 chi) ∨
      (¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom1106 chi)) ∨
      ((Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom1106 chi) ∨
      (Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom1106 chi))))) ∨
      (((((Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom1106 chi) ∨
      (Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom1106 chi)) ∨
      ((Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom1106 chi) ∨
      (Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom1106 chi))) ∨
      (((¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom1107 chi) ∨
      (¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom1107 chi)) ∨
      ((¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom1107 chi) ∨
      (¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom1107 chi)))) ∨
      ((((Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom1107 chi) ∨
      (Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom1107 chi)) ∨
      ((Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom1107 chi) ∨
      (Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom1107 chi))) ∨
      (((Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom1107 chi) ∨
      (Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom1107 chi)) ∨
      ((¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom1108 chi) ∨
      (¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom1108 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom1108 chi) ∨
      (¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom1108 chi)) ∨
      ((Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom1108 chi) ∨
      (Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom1108 chi))) ∨
      (((Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom1108 chi) ∨
      (Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom1108 chi)) ∨
      ((Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom1108 chi) ∨
      (¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom1109 chi)))) ∨
      ((((¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0174 chi ∧
      Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom1109 chi) ∨
      (¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom1110 chi)) ∨
      ((¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom1110 chi) ∨
      (¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom1110 chi))) ∨
      (((¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom1110 chi) ∨
      (Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom1110 chi)) ∨
      ((Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom1110 chi) ∨
      (Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom1110 chi))))) ∨
      (((((Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom1110 chi) ∨
      (Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom1110 chi)) ∨
      ((¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom1111 chi) ∨
      (¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom1111 chi))) ∨
      (((¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom1111 chi) ∨
      (¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom1111 chi)) ∨
      ((Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom1111 chi) ∨
      (Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom1111 chi)))) ∨
      ((((Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom1111 chi) ∨
      (Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom1111 chi)) ∨
      ((¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom1112 chi) ∨
      (¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom1112 chi))) ∨
      (((¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom1112 chi) ∨
      (Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom1112 chi)) ∨
      ((¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom1113 chi) ∨
      (¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom1113 chi))))))) ∨
      (((((((¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom1113 chi) ∨
      (¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom1113 chi)) ∨
      ((Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom1113 chi) ∨
      (Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom1113 chi))) ∨
      (((Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom1113 chi) ∨
      (Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom1113 chi)) ∨
      ((Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom1113 chi) ∨
      (¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom1114 chi)))) ∨
      ((((¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom1114 chi) ∨
      (¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom1114 chi)) ∨
      ((¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom1114 chi) ∨
      (Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom1114 chi))) ∨
      (((Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom1114 chi) ∨
      (Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom1114 chi)) ∨
      ((Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom1114 chi) ∨
      (¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom1115 chi))))) ∨
      (((((¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom1115 chi) ∨
      (¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom1115 chi)) ∨
      ((¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom1115 chi) ∨
      (Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom1115 chi))) ∨
      (((Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom1115 chi) ∨
      (Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom1115 chi)) ∨
      ((Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom1115 chi) ∨
      (Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom1115 chi)))) ∨
      ((((Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom1115 chi) ∨
      (¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom1116 chi)) ∨
      ((¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom1116 chi) ∨
      (¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom1116 chi))) ∨
      (((¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom1116 chi) ∨
      (Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom1116 chi)) ∨
      ((Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom1116 chi) ∨
      (Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom1116 chi)))))) ∨
      ((((((Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom1116 chi) ∨
      (Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom1116 chi)) ∨
      ((Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom1116 chi) ∨
      (¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom1117 chi))) ∨
      (((¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom1117 chi) ∨
      (¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom1117 chi)) ∨
      ((¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom1117 chi) ∨
      (Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom1117 chi)))) ∨
      ((((Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom1117 chi) ∨
      (Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom1117 chi)) ∨
      ((Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom1117 chi) ∨
      (Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom1117 chi))) ∨
      (((¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom1118 chi) ∨
      (¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0174 chi ∧
      Fin15AnchoredAtom0193 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom1118 chi)) ∨
      ((¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom1119 chi) ∨
      (¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom1119 chi))))) ∨
      (((((¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom1119 chi) ∨
      (¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom1119 chi)) ∨
      ((Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom1119 chi) ∨
      (Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom1119 chi))) ∨
      (((Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom1119 chi) ∨
      (Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom1119 chi)) ∨
      ((Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom1119 chi) ∨
      (¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom1120 chi)))) ∨
      ((((¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom1120 chi) ∨
      (¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom1120 chi)) ∨
      ((¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom1120 chi) ∨
      (¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom1120 chi))) ∨
      (((Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom1120 chi) ∨
      (Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom1120 chi)) ∨
      ((Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom1120 chi) ∨
      (Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom1120 chi)))))))))) := by
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
                exact fin15Anchored_clause09843 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09844 chi hbad
                ·
                  exact fin15Anchored_clause09845 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09846 chi hbad
                ·
                  exact fin15Anchored_clause09847 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09848 chi hbad
                ·
                  exact fin15Anchored_clause09849 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09850 chi hbad
                ·
                  exact fin15Anchored_clause09851 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09852 chi hbad
                ·
                  exact fin15Anchored_clause09853 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09854 chi hbad
                ·
                  exact fin15Anchored_clause09855 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09856 chi hbad
                ·
                  exact fin15Anchored_clause09857 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09858 chi hbad
                ·
                  exact fin15Anchored_clause09859 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09860 chi hbad
                ·
                  exact fin15Anchored_clause09861 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09862 chi hbad
                ·
                  exact fin15Anchored_clause09863 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09864 chi hbad
                ·
                  exact fin15Anchored_clause09865 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09866 chi hbad
                ·
                  exact fin15Anchored_clause09867 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09868 chi hbad
                ·
                  exact fin15Anchored_clause09869 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09870 chi hbad
                ·
                  exact fin15Anchored_clause09871 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09872 chi hbad
                ·
                  exact fin15Anchored_clause09873 chi hbad
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
                  exact fin15Anchored_clause09874 chi hbad
                ·
                  exact fin15Anchored_clause09875 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09876 chi hbad
                ·
                  exact fin15Anchored_clause09877 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09878 chi hbad
                ·
                  exact fin15Anchored_clause09879 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09880 chi hbad
                ·
                  exact fin15Anchored_clause09881 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09882 chi hbad
                ·
                  exact fin15Anchored_clause09883 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09884 chi hbad
                ·
                  exact fin15Anchored_clause09885 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09886 chi hbad
                ·
                  exact fin15Anchored_clause09887 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09888 chi hbad
                ·
                  exact fin15Anchored_clause09889 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09890 chi hbad
                ·
                  exact fin15Anchored_clause09891 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09892 chi hbad
                ·
                  exact fin15Anchored_clause09893 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09894 chi hbad
                ·
                  exact fin15Anchored_clause09895 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09896 chi hbad
                ·
                  exact fin15Anchored_clause09897 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09898 chi hbad
                ·
                  exact fin15Anchored_clause09899 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09900 chi hbad
                ·
                  exact fin15Anchored_clause09901 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09902 chi hbad
                ·
                  exact fin15Anchored_clause09903 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09904 chi hbad
                ·
                  exact fin15Anchored_clause09905 chi hbad
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
                exact fin15Anchored_clause09906 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09907 chi hbad
                ·
                  exact fin15Anchored_clause09908 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09909 chi hbad
                ·
                  exact fin15Anchored_clause09910 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09911 chi hbad
                ·
                  exact fin15Anchored_clause09912 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09913 chi hbad
                ·
                  exact fin15Anchored_clause09914 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09915 chi hbad
                ·
                  exact fin15Anchored_clause09916 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09917 chi hbad
                ·
                  exact fin15Anchored_clause09918 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09919 chi hbad
                ·
                  exact fin15Anchored_clause09920 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09921 chi hbad
                ·
                  exact fin15Anchored_clause09922 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09923 chi hbad
                ·
                  exact fin15Anchored_clause09924 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09925 chi hbad
                ·
                  exact fin15Anchored_clause09926 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09927 chi hbad
                ·
                  exact fin15Anchored_clause09928 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09929 chi hbad
                ·
                  exact fin15Anchored_clause09930 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09931 chi hbad
                ·
                  exact fin15Anchored_clause09932 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09933 chi hbad
                ·
                  exact fin15Anchored_clause09934 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09935 chi hbad
                ·
                  exact fin15Anchored_clause09936 chi hbad
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
                  exact fin15Anchored_clause09937 chi hbad
                ·
                  exact fin15Anchored_clause09938 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09939 chi hbad
                ·
                  exact fin15Anchored_clause09940 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09941 chi hbad
                ·
                  exact fin15Anchored_clause09942 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09943 chi hbad
                ·
                  exact fin15Anchored_clause09944 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09945 chi hbad
                ·
                  exact fin15Anchored_clause09946 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09947 chi hbad
                ·
                  exact fin15Anchored_clause09948 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09949 chi hbad
                ·
                  exact fin15Anchored_clause09950 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09951 chi hbad
                ·
                  exact fin15Anchored_clause09952 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09953 chi hbad
                ·
                  exact fin15Anchored_clause09954 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09955 chi hbad
                ·
                  exact fin15Anchored_clause09956 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09957 chi hbad
                ·
                  exact fin15Anchored_clause09958 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09959 chi hbad
                ·
                  exact fin15Anchored_clause09960 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09961 chi hbad
                ·
                  exact fin15Anchored_clause09962 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09963 chi hbad
                ·
                  exact fin15Anchored_clause09964 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09965 chi hbad
                ·
                  exact fin15Anchored_clause09966 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09967 chi hbad
                ·
                  exact fin15Anchored_clause09968 chi hbad
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
                exact fin15Anchored_clause09969 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09970 chi hbad
                ·
                  exact fin15Anchored_clause09971 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09972 chi hbad
                ·
                  exact fin15Anchored_clause09973 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09974 chi hbad
                ·
                  exact fin15Anchored_clause09975 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09976 chi hbad
                ·
                  exact fin15Anchored_clause09977 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09978 chi hbad
                ·
                  exact fin15Anchored_clause09979 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09980 chi hbad
                ·
                  exact fin15Anchored_clause09981 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09982 chi hbad
                ·
                  exact fin15Anchored_clause09983 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09984 chi hbad
                ·
                  exact fin15Anchored_clause09985 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09986 chi hbad
                ·
                  exact fin15Anchored_clause09987 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09988 chi hbad
                ·
                  exact fin15Anchored_clause09989 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09990 chi hbad
                ·
                  exact fin15Anchored_clause09991 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09992 chi hbad
                ·
                  exact fin15Anchored_clause09993 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09994 chi hbad
                ·
                  exact fin15Anchored_clause09995 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09996 chi hbad
                ·
                  exact fin15Anchored_clause09997 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09998 chi hbad
                ·
                  exact fin15Anchored_clause09999 chi hbad
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
                  exact fin15Anchored_clause10000 chi hbad
                ·
                  exact fin15Anchored_clause10001 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10002 chi hbad
                ·
                  exact fin15Anchored_clause10003 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10004 chi hbad
                ·
                  exact fin15Anchored_clause10005 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10006 chi hbad
                ·
                  exact fin15Anchored_clause10007 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10008 chi hbad
                ·
                  exact fin15Anchored_clause10009 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10010 chi hbad
                ·
                  exact fin15Anchored_clause10011 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10012 chi hbad
                ·
                  exact fin15Anchored_clause10013 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10014 chi hbad
                ·
                  exact fin15Anchored_clause10015 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10016 chi hbad
                ·
                  exact fin15Anchored_clause10017 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10018 chi hbad
                ·
                  exact fin15Anchored_clause10019 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10020 chi hbad
                ·
                  exact fin15Anchored_clause10021 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10022 chi hbad
                ·
                  exact fin15Anchored_clause10023 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10024 chi hbad
                ·
                  exact fin15Anchored_clause10025 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10026 chi hbad
                ·
                  exact fin15Anchored_clause10027 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10028 chi hbad
                ·
                  exact fin15Anchored_clause10029 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10030 chi hbad
                ·
                  exact fin15Anchored_clause10031 chi hbad
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
                  exact fin15Anchored_clause10032 chi hbad
                ·
                  exact fin15Anchored_clause10033 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10034 chi hbad
                ·
                  exact fin15Anchored_clause10035 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10036 chi hbad
                ·
                  exact fin15Anchored_clause10037 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10038 chi hbad
                ·
                  exact fin15Anchored_clause10039 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10040 chi hbad
                ·
                  exact fin15Anchored_clause10041 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10042 chi hbad
                ·
                  exact fin15Anchored_clause10043 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10044 chi hbad
                ·
                  exact fin15Anchored_clause10045 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10046 chi hbad
                ·
                  exact fin15Anchored_clause10047 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10048 chi hbad
                ·
                  exact fin15Anchored_clause10049 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10050 chi hbad
                ·
                  exact fin15Anchored_clause10051 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10052 chi hbad
                ·
                  exact fin15Anchored_clause10053 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10054 chi hbad
                ·
                  exact fin15Anchored_clause10055 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10056 chi hbad
                ·
                  exact fin15Anchored_clause10057 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10058 chi hbad
                ·
                  exact fin15Anchored_clause10059 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10060 chi hbad
                ·
                  exact fin15Anchored_clause10061 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10062 chi hbad
                ·
                  exact fin15Anchored_clause10063 chi hbad
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
                  exact fin15Anchored_clause10064 chi hbad
                ·
                  exact fin15Anchored_clause10065 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10066 chi hbad
                ·
                  exact fin15Anchored_clause10067 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10068 chi hbad
                ·
                  exact fin15Anchored_clause10069 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10070 chi hbad
                ·
                  exact fin15Anchored_clause10071 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10072 chi hbad
                ·
                  exact fin15Anchored_clause10073 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10074 chi hbad
                ·
                  exact fin15Anchored_clause10075 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10076 chi hbad
                ·
                  exact fin15Anchored_clause10077 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10078 chi hbad
                ·
                  exact fin15Anchored_clause10079 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10080 chi hbad
                ·
                  exact fin15Anchored_clause10081 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10082 chi hbad
                ·
                  exact fin15Anchored_clause10083 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10084 chi hbad
                ·
                  exact fin15Anchored_clause10085 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10086 chi hbad
                ·
                  exact fin15Anchored_clause10087 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10088 chi hbad
                ·
                  exact fin15Anchored_clause10089 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10090 chi hbad
                ·
                  exact fin15Anchored_clause10091 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10092 chi hbad
                ·
                  exact fin15Anchored_clause10093 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10094 chi hbad
                ·
                  exact fin15Anchored_clause10095 chi hbad

end ErdosSzekeres

end
