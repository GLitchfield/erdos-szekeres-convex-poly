module

public import ErdosSzekeres.Fin15AnchoredClauseChunk078
public import ErdosSzekeres.Fin15AnchoredClauseChunk079
public import ErdosSzekeres.Fin15AnchoredClauseChunk080

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 040. -/

theorem fin15Anchored_rejectSemanticSegment040
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom1121 chi) ∨
      ((¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom1121 chi) ∨
      (¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom1121 chi))) ∨
      (((¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom1121 chi) ∨
      (Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom1121 chi)) ∨
      ((Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom1121 chi) ∨
      (Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom1121 chi)))) ∨
      ((((Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom1121 chi) ∨
      (Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom1121 chi)) ∨
      ((¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom1122 chi) ∨
      (¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom1122 chi))) ∨
      (((¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom1122 chi) ∨
      (¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom1122 chi)) ∨
      ((Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom1122 chi) ∨
      (Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom1122 chi))))) ∨
      (((((Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom1122 chi) ∨
      (Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom1122 chi)) ∨
      ((¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom1123 chi) ∨
      (¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom1123 chi))) ∨
      (((¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom1123 chi) ∨
      (¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom1123 chi)) ∨
      ((Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom1123 chi) ∨
      (Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom1123 chi)))) ∨
      ((((Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom1123 chi) ∨
      (Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom1123 chi)) ∨
      ((¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom1124 chi) ∨
      (¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom1124 chi))) ∨
      (((¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom1124 chi) ∨
      (¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom1124 chi)) ∨
      ((Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom1124 chi) ∨
      (Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom1124 chi)))))) ∨
      ((((((Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom1124 chi) ∨
      (Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom1124 chi)) ∨
      ((Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom1124 chi) ∨
      (Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom1124 chi))) ∨
      (((¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom1125 chi) ∨
      (¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom1125 chi)) ∨
      ((¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom1125 chi) ∨
      (¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom1125 chi)))) ∨
      ((((Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom1125 chi) ∨
      (Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom1125 chi)) ∨
      ((Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom1125 chi) ∨
      (Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom1125 chi))) ∨
      (((¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom1126 chi) ∨
      (Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom1126 chi)) ∨
      ((Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0174 chi ∧
      Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom1126 chi) ∨
      (¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom1127 chi))))) ∨
      (((((¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom1127 chi) ∨
      (¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom1127 chi)) ∨
      ((¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom1127 chi) ∨
      (¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom1127 chi))) ∨
      (((Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom1127 chi) ∨
      (Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom1127 chi)) ∨
      ((Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom1127 chi) ∨
      (Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom1127 chi)))) ∨
      ((((¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom1128 chi) ∨
      (¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom1128 chi)) ∨
      ((¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom1128 chi) ∨
      (¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom1128 chi))) ∨
      (((Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom1128 chi) ∨
      (Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom1128 chi)) ∨
      ((Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom1128 chi) ∨
      (Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom1128 chi))))))) ∨
      ((((((Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom1128 chi) ∨
      ((¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom1129 chi) ∨
      (¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom1129 chi))) ∨
      (((Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom1129 chi) ∨
      (Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom1129 chi)) ∨
      ((Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom1129 chi) ∨
      (Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom1129 chi)))) ∨
      ((((¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom1130 chi) ∨
      (¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom1130 chi)) ∨
      ((¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom1130 chi) ∨
      (¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom1130 chi))) ∨
      (((Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom1130 chi) ∨
      (Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom1130 chi)) ∨
      ((Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom1130 chi) ∨
      (Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom1130 chi))))) ∨
      (((((¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom1131 chi) ∨
      (¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom1131 chi)) ∨
      ((¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom1131 chi) ∨
      (¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom1131 chi))) ∨
      (((Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom1131 chi) ∨
      (Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom1131 chi)) ∨
      ((Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom1131 chi) ∨
      (Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom1131 chi)))) ∨
      ((((¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom1132 chi) ∨
      (¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom1132 chi)) ∨
      ((¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom1132 chi) ∨
      (¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom1132 chi))) ∨
      (((Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom1132 chi) ∨
      (Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom1132 chi)) ∨
      ((Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom1132 chi) ∨
      (Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom1132 chi)))))) ∨
      ((((((Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom1132 chi) ∨
      (¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom1133 chi)) ∨
      ((Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom1133 chi) ∨
      (Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom1133 chi))) ∨
      (((Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0174 chi ∧
      Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom1133 chi) ∨
      (¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom1134 chi)) ∨
      ((¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom1134 chi) ∨
      (¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom1134 chi)))) ∨
      ((((¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom1134 chi) ∨
      (¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom1134 chi)) ∨
      ((Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom1134 chi) ∨
      (Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom1134 chi))) ∨
      (((Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom1134 chi) ∨
      (Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom1134 chi)) ∨
      ((¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom1135 chi) ∨
      (¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom1135 chi))))) ∨
      (((((¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom1135 chi) ∨
      (¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom1135 chi)) ∨
      ((Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom1135 chi) ∨
      (Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom1135 chi))) ∨
      (((Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom1135 chi) ∨
      (Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom1135 chi)) ∨
      ((¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom1136 chi) ∨
      (¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom1136 chi)))) ∨
      ((((¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom1136 chi) ∨
      (Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom1136 chi)) ∨
      ((Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom1136 chi) ∨
      (Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom1136 chi))) ∨
      (((Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom1136 chi) ∨
      (¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom1137 chi)) ∨
      ((¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom1137 chi) ∨
      (¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom1137 chi)))))))) ∨
      (((((((¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom1137 chi) ∨
      ((Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom1137 chi) ∨
      (Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom1137 chi))) ∨
      (((Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom1137 chi) ∨
      (Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom1137 chi)) ∨
      ((¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom1138 chi) ∨
      (¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom1138 chi)))) ∨
      ((((¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom1138 chi) ∨
      (¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom1138 chi)) ∨
      ((Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom1138 chi) ∨
      (Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom1138 chi))) ∨
      (((Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom1138 chi) ∨
      (Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom1138 chi)) ∨
      ((¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom1139 chi) ∨
      (¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom1139 chi))))) ∨
      (((((¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom1139 chi) ∨
      (¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom1139 chi)) ∨
      ((Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom1139 chi) ∨
      (Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom1139 chi))) ∨
      (((Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom1139 chi) ∨
      (Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom1139 chi)) ∨
      ((¬Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom1140 chi) ∨
      (¬Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom1140 chi)))) ∨
      ((((¬Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom1141 chi) ∨
      (¬Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom1141 chi)) ∨
      ((¬Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom1143 chi) ∨
      (¬Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom1143 chi))) ∨
      (((Fin15AnchoredAtom0174 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0219 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom1144 chi) ∨
      (¬Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom1145 chi)) ∨
      ((¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom1146 chi) ∨
      (¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom1146 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom1146 chi) ∨
      (¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom1146 chi)) ∨
      ((Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom1146 chi) ∨
      (Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom1146 chi))) ∨
      (((Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom1146 chi) ∨
      (Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom1146 chi)) ∨
      ((Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom1146 chi) ∨
      (¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom1147 chi)))) ∨
      ((((Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom1147 chi) ∨
      (Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom1147 chi)) ∨
      ((Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom1147 chi) ∨
      (Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom1147 chi))) ∨
      (((¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom1148 chi) ∨
      (¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom1148 chi)) ∨
      ((¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom1148 chi) ∨
      (¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom1148 chi))))) ∨
      (((((Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom1148 chi) ∨
      (Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom1148 chi)) ∨
      ((Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom1148 chi) ∨
      (Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom1148 chi))) ∨
      (((¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom1149 chi) ∨
      (¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom1149 chi)) ∨
      ((¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom1149 chi) ∨
      (¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom1149 chi)))) ∨
      ((((Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom1149 chi) ∨
      (Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom1149 chi)) ∨
      ((Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom1149 chi) ∨
      (Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom1149 chi))) ∨
      (((¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom1150 chi) ∨
      (¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom1150 chi)) ∨
      ((¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom1150 chi) ∨
      (¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom1150 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom1150 chi) ∨
      ((Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom1150 chi) ∨
      (Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom1150 chi))) ∨
      (((Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom1150 chi) ∨
      (Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom1150 chi)) ∨
      ((¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom1151 chi) ∨
      (¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom1151 chi)))) ∨
      ((((¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom1151 chi) ∨
      (Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom1151 chi)) ∨
      ((Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom1151 chi) ∨
      (Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom1151 chi))) ∨
      (((¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom1152 chi) ∨
      (¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom1152 chi)) ∨
      ((¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom1152 chi) ∨
      (¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom1152 chi))))) ∨
      (((((Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom1152 chi) ∨
      (Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom1152 chi)) ∨
      ((Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom1152 chi) ∨
      (Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom1152 chi))) ∨
      (((¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom1153 chi) ∨
      (¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom1153 chi)) ∨
      ((¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom1153 chi) ∨
      (¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom1153 chi)))) ∨
      ((((Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom1153 chi) ∨
      (Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom1153 chi)) ∨
      ((Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom1153 chi) ∨
      (Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom1153 chi))) ∨
      (((Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom1153 chi) ∨
      (¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom1154 chi)) ∨
      ((¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom1154 chi) ∨
      (¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom1154 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom1154 chi) ∨
      (Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom1154 chi)) ∨
      ((Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom1154 chi) ∨
      (Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom1154 chi))) ∨
      (((Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom1154 chi) ∨
      (Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom1154 chi)) ∨
      ((¬Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom1155 chi) ∨
      (¬Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom1155 chi)))) ∨
      ((((¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom1155 chi) ∨
      (Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom1155 chi)) ∨
      ((Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom1155 chi) ∨
      (¬Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom1156 chi))) ∨
      (((¬Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom1156 chi) ∨
      (Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom1156 chi)) ∨
      ((Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom1156 chi) ∨
      (Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom1156 chi))))) ∨
      (((((Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom1156 chi) ∨
      (¬Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0287 chi ∧
      ¬Fin15AnchoredAtom1157 chi)) ∨
      ((¬Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0232 chi ∧
      Fin15AnchoredAtom0287 chi ∧
      ¬Fin15AnchoredAtom1157 chi) ∨
      (¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0287 chi ∧
      Fin15AnchoredAtom1157 chi))) ∨
      (((Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0287 chi ∧
      Fin15AnchoredAtom1157 chi) ∨
      (¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom1158 chi)) ∨
      ((¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom1158 chi) ∨
      (¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom1158 chi)))) ∨
      ((((¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom1158 chi) ∨
      (Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom1158 chi)) ∨
      ((Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom1158 chi) ∨
      (Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom1158 chi))) ∨
      (((Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom1158 chi) ∨
      (Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom1158 chi)) ∨
      ((¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom1159 chi) ∨
      (¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom1159 chi)))))))))) := by
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
                exact fin15Anchored_clause10096 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10097 chi hbad
                ·
                  exact fin15Anchored_clause10098 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10099 chi hbad
                ·
                  exact fin15Anchored_clause10100 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10101 chi hbad
                ·
                  exact fin15Anchored_clause10102 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10103 chi hbad
                ·
                  exact fin15Anchored_clause10104 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10105 chi hbad
                ·
                  exact fin15Anchored_clause10106 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10107 chi hbad
                ·
                  exact fin15Anchored_clause10108 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10109 chi hbad
                ·
                  exact fin15Anchored_clause10110 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10111 chi hbad
                ·
                  exact fin15Anchored_clause10112 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10113 chi hbad
                ·
                  exact fin15Anchored_clause10114 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10115 chi hbad
                ·
                  exact fin15Anchored_clause10116 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10117 chi hbad
                ·
                  exact fin15Anchored_clause10118 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10119 chi hbad
                ·
                  exact fin15Anchored_clause10120 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10121 chi hbad
                ·
                  exact fin15Anchored_clause10122 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10123 chi hbad
                ·
                  exact fin15Anchored_clause10124 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10125 chi hbad
                ·
                  exact fin15Anchored_clause10126 chi hbad
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
                  exact fin15Anchored_clause10127 chi hbad
                ·
                  exact fin15Anchored_clause10128 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10129 chi hbad
                ·
                  exact fin15Anchored_clause10130 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10131 chi hbad
                ·
                  exact fin15Anchored_clause10132 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10133 chi hbad
                ·
                  exact fin15Anchored_clause10134 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10135 chi hbad
                ·
                  exact fin15Anchored_clause10136 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10137 chi hbad
                ·
                  exact fin15Anchored_clause10138 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10139 chi hbad
                ·
                  exact fin15Anchored_clause10140 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10141 chi hbad
                ·
                  exact fin15Anchored_clause10142 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10143 chi hbad
                ·
                  exact fin15Anchored_clause10144 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10145 chi hbad
                ·
                  exact fin15Anchored_clause10146 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10147 chi hbad
                ·
                  exact fin15Anchored_clause10148 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10149 chi hbad
                ·
                  exact fin15Anchored_clause10150 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10151 chi hbad
                ·
                  exact fin15Anchored_clause10152 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10153 chi hbad
                ·
                  exact fin15Anchored_clause10154 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10155 chi hbad
                ·
                  exact fin15Anchored_clause10156 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10157 chi hbad
                ·
                  exact fin15Anchored_clause10158 chi hbad
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
                exact fin15Anchored_clause10159 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10160 chi hbad
                ·
                  exact fin15Anchored_clause10161 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10162 chi hbad
                ·
                  exact fin15Anchored_clause10163 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10164 chi hbad
                ·
                  exact fin15Anchored_clause10165 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10166 chi hbad
                ·
                  exact fin15Anchored_clause10167 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10168 chi hbad
                ·
                  exact fin15Anchored_clause10169 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10170 chi hbad
                ·
                  exact fin15Anchored_clause10171 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10172 chi hbad
                ·
                  exact fin15Anchored_clause10173 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10174 chi hbad
                ·
                  exact fin15Anchored_clause10175 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10176 chi hbad
                ·
                  exact fin15Anchored_clause10177 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10178 chi hbad
                ·
                  exact fin15Anchored_clause10179 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10180 chi hbad
                ·
                  exact fin15Anchored_clause10181 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10182 chi hbad
                ·
                  exact fin15Anchored_clause10183 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10184 chi hbad
                ·
                  exact fin15Anchored_clause10185 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10186 chi hbad
                ·
                  exact fin15Anchored_clause10187 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10188 chi hbad
                ·
                  exact fin15Anchored_clause10189 chi hbad
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
                  exact fin15Anchored_clause10190 chi hbad
                ·
                  exact fin15Anchored_clause10191 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10192 chi hbad
                ·
                  exact fin15Anchored_clause10193 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10194 chi hbad
                ·
                  exact fin15Anchored_clause10195 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10196 chi hbad
                ·
                  exact fin15Anchored_clause10197 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10198 chi hbad
                ·
                  exact fin15Anchored_clause10199 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10200 chi hbad
                ·
                  exact fin15Anchored_clause10201 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10202 chi hbad
                ·
                  exact fin15Anchored_clause10203 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10204 chi hbad
                ·
                  exact fin15Anchored_clause10205 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10206 chi hbad
                ·
                  exact fin15Anchored_clause10207 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10208 chi hbad
                ·
                  exact fin15Anchored_clause10209 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10210 chi hbad
                ·
                  exact fin15Anchored_clause10211 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10212 chi hbad
                ·
                  exact fin15Anchored_clause10213 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10214 chi hbad
                ·
                  exact fin15Anchored_clause10215 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10216 chi hbad
                ·
                  exact fin15Anchored_clause10217 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10218 chi hbad
                ·
                  exact fin15Anchored_clause10219 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10220 chi hbad
                ·
                  exact fin15Anchored_clause10221 chi hbad
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
                exact fin15Anchored_clause10222 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10223 chi hbad
                ·
                  exact fin15Anchored_clause10224 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10225 chi hbad
                ·
                  exact fin15Anchored_clause10226 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10227 chi hbad
                ·
                  exact fin15Anchored_clause10228 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10229 chi hbad
                ·
                  exact fin15Anchored_clause10230 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10231 chi hbad
                ·
                  exact fin15Anchored_clause10232 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10233 chi hbad
                ·
                  exact fin15Anchored_clause10234 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10235 chi hbad
                ·
                  exact fin15Anchored_clause10236 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10237 chi hbad
                ·
                  exact fin15Anchored_clause10238 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10239 chi hbad
                ·
                  exact fin15Anchored_clause10240 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10241 chi hbad
                ·
                  exact fin15Anchored_clause10242 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10243 chi hbad
                ·
                  exact fin15Anchored_clause10244 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10245 chi hbad
                ·
                  exact fin15Anchored_clause10246 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10247 chi hbad
                ·
                  exact fin15Anchored_clause10248 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10249 chi hbad
                ·
                  exact fin15Anchored_clause10250 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10251 chi hbad
                ·
                  exact fin15Anchored_clause10252 chi hbad
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
                  exact fin15Anchored_clause10253 chi hbad
                ·
                  exact fin15Anchored_clause10254 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10255 chi hbad
                ·
                  exact fin15Anchored_clause10256 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10257 chi hbad
                ·
                  exact fin15Anchored_clause10258 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10259 chi hbad
                ·
                  exact fin15Anchored_clause10260 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10261 chi hbad
                ·
                  exact fin15Anchored_clause10262 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10263 chi hbad
                ·
                  exact fin15Anchored_clause10264 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10265 chi hbad
                ·
                  exact fin15Anchored_clause10266 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10267 chi hbad
                ·
                  exact fin15Anchored_clause10268 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10269 chi hbad
                ·
                  exact fin15Anchored_clause10270 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10271 chi hbad
                ·
                  exact fin15Anchored_clause10272 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10273 chi hbad
                ·
                  exact fin15Anchored_clause10274 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10275 chi hbad
                ·
                  exact fin15Anchored_clause10276 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10277 chi hbad
                ·
                  exact fin15Anchored_clause10278 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10279 chi hbad
                ·
                  exact fin15Anchored_clause10280 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10281 chi hbad
                ·
                  exact fin15Anchored_clause10282 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10283 chi hbad
                ·
                  exact fin15Anchored_clause10284 chi hbad
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
                exact fin15Anchored_clause10285 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10286 chi hbad
                ·
                  exact fin15Anchored_clause10287 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10288 chi hbad
                ·
                  exact fin15Anchored_clause10289 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10290 chi hbad
                ·
                  exact fin15Anchored_clause10291 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10292 chi hbad
                ·
                  exact fin15Anchored_clause10293 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10294 chi hbad
                ·
                  exact fin15Anchored_clause10295 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10296 chi hbad
                ·
                  exact fin15Anchored_clause10297 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10298 chi hbad
                ·
                  exact fin15Anchored_clause10299 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10300 chi hbad
                ·
                  exact fin15Anchored_clause10301 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10302 chi hbad
                ·
                  exact fin15Anchored_clause10303 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10304 chi hbad
                ·
                  exact fin15Anchored_clause10305 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10306 chi hbad
                ·
                  exact fin15Anchored_clause10307 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10308 chi hbad
                ·
                  exact fin15Anchored_clause10309 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10310 chi hbad
                ·
                  exact fin15Anchored_clause10311 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10312 chi hbad
                ·
                  exact fin15Anchored_clause10313 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10314 chi hbad
                ·
                  exact fin15Anchored_clause10315 chi hbad
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
                  exact fin15Anchored_clause10316 chi hbad
                ·
                  exact fin15Anchored_clause10317 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10318 chi hbad
                ·
                  exact fin15Anchored_clause10319 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10320 chi hbad
                ·
                  exact fin15Anchored_clause10321 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10322 chi hbad
                ·
                  exact fin15Anchored_clause10323 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10324 chi hbad
                ·
                  exact fin15Anchored_clause10325 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10326 chi hbad
                ·
                  exact fin15Anchored_clause10327 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10328 chi hbad
                ·
                  exact fin15Anchored_clause10329 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10330 chi hbad
                ·
                  exact fin15Anchored_clause10331 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10332 chi hbad
                ·
                  exact fin15Anchored_clause10333 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10334 chi hbad
                ·
                  exact fin15Anchored_clause10335 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10336 chi hbad
                ·
                  exact fin15Anchored_clause10337 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10338 chi hbad
                ·
                  exact fin15Anchored_clause10339 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10340 chi hbad
                ·
                  exact fin15Anchored_clause10341 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10342 chi hbad
                ·
                  exact fin15Anchored_clause10343 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10344 chi hbad
                ·
                  exact fin15Anchored_clause10345 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10346 chi hbad
                ·
                  exact fin15Anchored_clause10347 chi hbad

end ErdosSzekeres

end
