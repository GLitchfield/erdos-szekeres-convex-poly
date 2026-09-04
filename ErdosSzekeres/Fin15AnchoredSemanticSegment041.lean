module

public import ErdosSzekeres.Fin15AnchoredClauseChunk080
public import ErdosSzekeres.Fin15AnchoredClauseChunk081
public import ErdosSzekeres.Fin15AnchoredClauseChunk082

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 041. -/

theorem fin15Anchored_rejectSemanticSegment041
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom1159 chi) ∨
      ((¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom1159 chi) ∨
      (¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom1159 chi))) ∨
      (((Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom1159 chi) ∨
      (Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom1159 chi)) ∨
      ((Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom1159 chi) ∨
      (Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom1159 chi)))) ∨
      ((((Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom1159 chi) ∨
      (¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom1160 chi)) ∨
      ((¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom1160 chi) ∨
      (¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom1160 chi))) ∨
      (((¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom1160 chi) ∨
      (¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom1160 chi)) ∨
      ((Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom1160 chi) ∨
      (Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom1160 chi))))) ∨
      (((((Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom1160 chi) ∨
      (Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom1160 chi)) ∨
      ((¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom1161 chi) ∨
      (¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom1161 chi))) ∨
      (((¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom1161 chi) ∨
      (¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom1161 chi)) ∨
      ((Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom1161 chi) ∨
      (Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom1161 chi)))) ∨
      ((((Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom1161 chi) ∨
      (Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom1161 chi)) ∨
      ((Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom1161 chi) ∨
      (¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom1162 chi))) ∨
      (((¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom1162 chi) ∨
      (¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom1162 chi)) ∨
      ((¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom1162 chi) ∨
      (Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom1162 chi)))))) ∨
      ((((((Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom1162 chi) ∨
      (Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom1162 chi)) ∨
      ((Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom1162 chi) ∨
      (Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom1162 chi))) ∨
      (((Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom1162 chi) ∨
      (¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0193 chi ∧
      Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom1163 chi)) ∨
      ((¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom1163 chi) ∨
      (¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0193 chi ∧
      Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom1163 chi)))) ∨
      ((((Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom1163 chi) ∨
      (Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0193 chi ∧
      Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom1163 chi)) ∨
      ((¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom1164 chi) ∨
      (¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom1164 chi))) ∨
      (((¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom1164 chi) ∨
      (¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom1164 chi)) ∨
      ((Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom1164 chi) ∨
      (Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom1164 chi))))) ∨
      (((((Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom1164 chi) ∨
      (Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom1164 chi)) ∨
      ((¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom1165 chi) ∨
      (¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom1165 chi))) ∨
      (((¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom1165 chi) ∨
      (¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom1165 chi)) ∨
      ((¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom1165 chi) ∨
      (Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom1165 chi)))) ∨
      ((((Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom1165 chi) ∨
      (Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom1165 chi)) ∨
      ((Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom1165 chi) ∨
      (Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom1165 chi))) ∨
      (((¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom1166 chi) ∨
      (¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom1166 chi)) ∨
      ((¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom1166 chi) ∨
      (Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom1166 chi))))))) ∨
      ((((((Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom1166 chi) ∨
      ((Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom1166 chi) ∨
      (Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom1166 chi))) ∨
      (((¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom1167 chi) ∨
      (¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom1167 chi)) ∨
      ((¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom1167 chi) ∨
      (¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom1167 chi)))) ∨
      ((((¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom1167 chi) ∨
      (Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom1167 chi)) ∨
      ((Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom1167 chi) ∨
      (Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom1167 chi))) ∨
      (((Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom1167 chi) ∨
      (Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom1167 chi)) ∨
      ((¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom1168 chi) ∨
      (¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom1168 chi))))) ∨
      (((((¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom1168 chi) ∨
      (¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom1168 chi)) ∨
      ((¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom1168 chi) ∨
      (Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom1168 chi))) ∨
      (((Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom1168 chi) ∨
      (Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom1168 chi)) ∨
      ((Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom1168 chi) ∨
      (Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom1168 chi)))) ∨
      ((((¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom1169 chi) ∨
      (¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom1169 chi)) ∨
      ((¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom1169 chi) ∨
      (¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom1169 chi))) ∨
      (((Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom1169 chi) ∨
      (Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom1169 chi)) ∨
      ((Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom1169 chi) ∨
      (Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom1169 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom1170 chi) ∨
      (¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom1170 chi)) ∨
      ((¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom1170 chi) ∨
      (¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom1170 chi))) ∨
      (((Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom1170 chi) ∨
      (Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom1170 chi)) ∨
      ((Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom1170 chi) ∨
      (Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom1170 chi)))) ∨
      ((((Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom1170 chi) ∨
      (¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom1171 chi)) ∨
      ((¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom1171 chi) ∨
      (¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom1171 chi))) ∨
      (((Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom1171 chi) ∨
      (¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom1172 chi)) ∨
      ((¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom1172 chi) ∨
      (¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom1172 chi))))) ∨
      (((((¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom1172 chi) ∨
      (¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom1172 chi)) ∨
      ((Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom1172 chi) ∨
      (Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom1172 chi))) ∨
      (((Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom1172 chi) ∨
      (Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom1172 chi)) ∨
      ((¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom1173 chi) ∨
      (¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom1173 chi)))) ∨
      ((((¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom1173 chi) ∨
      (¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom1173 chi)) ∨
      ((¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom1173 chi) ∨
      (Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom1173 chi))) ∨
      (((Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom1173 chi) ∨
      (Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom1173 chi)) ∨
      ((Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom1173 chi) ∨
      (Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom1173 chi)))))))) ∨
      (((((((¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom1174 chi) ∨
      ((Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom1174 chi) ∨
      (Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom1174 chi))) ∨
      (((Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom1174 chi) ∨
      (Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom1174 chi)) ∨
      ((Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom1174 chi) ∨
      (¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom1175 chi)))) ∨
      ((((¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom1175 chi) ∨
      (¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom1175 chi)) ∨
      ((¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom1175 chi) ∨
      (¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom1175 chi))) ∨
      (((Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom1175 chi) ∨
      (Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom1175 chi)) ∨
      ((Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom1175 chi) ∨
      (Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom1175 chi))))) ∨
      (((((Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom1175 chi) ∨
      (¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom1176 chi)) ∨
      ((¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom1176 chi) ∨
      (¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom1176 chi))) ∨
      (((¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom1176 chi) ∨
      (¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom1176 chi)) ∨
      ((Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom1176 chi) ∨
      (Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom1176 chi)))) ∨
      ((((Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom1176 chi) ∨
      (Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom1176 chi)) ∨
      ((Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom1176 chi) ∨
      (¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom1177 chi))) ∨
      (((¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom1177 chi) ∨
      (¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom1177 chi)) ∨
      ((¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom1177 chi) ∨
      (Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom1177 chi)))))) ∨
      ((((((Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom1177 chi) ∨
      (Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom1177 chi)) ∨
      ((Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom1177 chi) ∨
      (¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom1178 chi))) ∨
      (((¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom1178 chi) ∨
      (Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom1178 chi)) ∨
      ((Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom1178 chi) ∨
      (Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom1178 chi)))) ∨
      ((((Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom1178 chi) ∨
      (¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom1179 chi)) ∨
      ((¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom1179 chi) ∨
      (¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom1179 chi))) ∨
      (((¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom1179 chi) ∨
      (Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom1179 chi)) ∨
      ((Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom1179 chi) ∨
      (Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom1179 chi))))) ∨
      (((((Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom1179 chi) ∨
      (Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom1179 chi)) ∨
      ((¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom1180 chi) ∨
      (¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom1180 chi))) ∨
      (((¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom1180 chi) ∨
      (¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom1180 chi)) ∨
      ((Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom1180 chi) ∨
      (Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom1180 chi)))) ∨
      ((((Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom1180 chi) ∨
      (Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom1180 chi)) ∨
      ((Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom1180 chi) ∨
      (Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom1180 chi))) ∨
      (((¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom1181 chi) ∨
      (¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom1181 chi)) ∨
      ((¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom1181 chi) ∨
      (Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom1181 chi))))))) ∨
      ((((((Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom1181 chi) ∨
      ((¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom1182 chi) ∨
      (¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom1182 chi))) ∨
      (((¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom1182 chi) ∨
      (¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom1182 chi)) ∨
      ((Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom1182 chi) ∨
      (Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom1182 chi)))) ∨
      ((((Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom1182 chi) ∨
      (Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom1182 chi)) ∨
      ((Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom1182 chi) ∨
      (¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom1183 chi))) ∨
      (((¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom1183 chi) ∨
      (¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom1183 chi)) ∨
      ((¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom1183 chi) ∨
      (Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom1183 chi))))) ∨
      (((((Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom1183 chi) ∨
      (Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom1183 chi)) ∨
      ((Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom1183 chi) ∨
      (Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom1183 chi))) ∨
      (((¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom1184 chi) ∨
      (¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom1184 chi)) ∨
      ((¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom1184 chi) ∨
      (¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom1184 chi)))) ∨
      ((((¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom1184 chi) ∨
      (Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom1184 chi)) ∨
      ((Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom1184 chi) ∨
      (Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom1184 chi))) ∨
      (((Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom1184 chi) ∨
      (¬Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom1185 chi)) ∨
      ((¬Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom1185 chi) ∨
      (¬Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom1185 chi)))))) ∨
      ((((((Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom1185 chi) ∨
      (Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom1185 chi)) ∨
      ((¬Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom1186 chi) ∨
      (¬Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom1186 chi))) ∨
      (((Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom1186 chi) ∨
      (¬Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom1188 chi)) ∨
      ((¬Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom1188 chi) ∨
      (¬Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom1188 chi)))) ∨
      ((((Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom1188 chi) ∨
      (Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom1188 chi)) ∨
      ((Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom1188 chi) ∨
      (Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0219 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom1189 chi))) ∨
      (((¬Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom1190 chi) ∨
      (¬Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0220 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom1190 chi)) ∨
      ((Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom1190 chi) ∨
      (¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom1191 chi))))) ∨
      (((((¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom1191 chi) ∨
      (¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom1191 chi)) ∨
      ((¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom1191 chi) ∨
      (Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom1191 chi))) ∨
      (((Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom1191 chi) ∨
      (Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom1191 chi)) ∨
      ((Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom1191 chi) ∨
      (Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom1191 chi)))) ∨
      ((((¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom1192 chi) ∨
      (¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom1192 chi)) ∨
      ((Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom1192 chi) ∨
      (Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom1192 chi))) ∨
      (((¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom1193 chi) ∨
      (¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom1193 chi)) ∨
      ((¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom1193 chi) ∨
      (¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom1193 chi)))))))))) := by
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
                exact fin15Anchored_clause10348 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10349 chi hbad
                ·
                  exact fin15Anchored_clause10350 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10351 chi hbad
                ·
                  exact fin15Anchored_clause10352 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10353 chi hbad
                ·
                  exact fin15Anchored_clause10354 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10355 chi hbad
                ·
                  exact fin15Anchored_clause10356 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10357 chi hbad
                ·
                  exact fin15Anchored_clause10358 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10359 chi hbad
                ·
                  exact fin15Anchored_clause10360 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10361 chi hbad
                ·
                  exact fin15Anchored_clause10362 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10363 chi hbad
                ·
                  exact fin15Anchored_clause10364 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10365 chi hbad
                ·
                  exact fin15Anchored_clause10366 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10367 chi hbad
                ·
                  exact fin15Anchored_clause10368 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10369 chi hbad
                ·
                  exact fin15Anchored_clause10370 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10371 chi hbad
                ·
                  exact fin15Anchored_clause10372 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10373 chi hbad
                ·
                  exact fin15Anchored_clause10374 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10375 chi hbad
                ·
                  exact fin15Anchored_clause10376 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10377 chi hbad
                ·
                  exact fin15Anchored_clause10378 chi hbad
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
                  exact fin15Anchored_clause10379 chi hbad
                ·
                  exact fin15Anchored_clause10380 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10381 chi hbad
                ·
                  exact fin15Anchored_clause10382 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10383 chi hbad
                ·
                  exact fin15Anchored_clause10384 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10385 chi hbad
                ·
                  exact fin15Anchored_clause10386 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10387 chi hbad
                ·
                  exact fin15Anchored_clause10388 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10389 chi hbad
                ·
                  exact fin15Anchored_clause10390 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10391 chi hbad
                ·
                  exact fin15Anchored_clause10392 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10393 chi hbad
                ·
                  exact fin15Anchored_clause10394 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10395 chi hbad
                ·
                  exact fin15Anchored_clause10396 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10397 chi hbad
                ·
                  exact fin15Anchored_clause10398 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10399 chi hbad
                ·
                  exact fin15Anchored_clause10400 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10401 chi hbad
                ·
                  exact fin15Anchored_clause10402 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10403 chi hbad
                ·
                  exact fin15Anchored_clause10404 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10405 chi hbad
                ·
                  exact fin15Anchored_clause10406 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10407 chi hbad
                ·
                  exact fin15Anchored_clause10408 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10409 chi hbad
                ·
                  exact fin15Anchored_clause10410 chi hbad
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
                exact fin15Anchored_clause10411 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10412 chi hbad
                ·
                  exact fin15Anchored_clause10413 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10414 chi hbad
                ·
                  exact fin15Anchored_clause10415 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10416 chi hbad
                ·
                  exact fin15Anchored_clause10417 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10418 chi hbad
                ·
                  exact fin15Anchored_clause10419 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10420 chi hbad
                ·
                  exact fin15Anchored_clause10421 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10422 chi hbad
                ·
                  exact fin15Anchored_clause10423 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10424 chi hbad
                ·
                  exact fin15Anchored_clause10425 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10426 chi hbad
                ·
                  exact fin15Anchored_clause10427 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10428 chi hbad
                ·
                  exact fin15Anchored_clause10429 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10430 chi hbad
                ·
                  exact fin15Anchored_clause10431 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10432 chi hbad
                ·
                  exact fin15Anchored_clause10433 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10434 chi hbad
                ·
                  exact fin15Anchored_clause10435 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10436 chi hbad
                ·
                  exact fin15Anchored_clause10437 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10438 chi hbad
                ·
                  exact fin15Anchored_clause10439 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10440 chi hbad
                ·
                  exact fin15Anchored_clause10441 chi hbad
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
                  exact fin15Anchored_clause10442 chi hbad
                ·
                  exact fin15Anchored_clause10443 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10444 chi hbad
                ·
                  exact fin15Anchored_clause10445 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10446 chi hbad
                ·
                  exact fin15Anchored_clause10447 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10448 chi hbad
                ·
                  exact fin15Anchored_clause10449 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10450 chi hbad
                ·
                  exact fin15Anchored_clause10451 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10452 chi hbad
                ·
                  exact fin15Anchored_clause10453 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10454 chi hbad
                ·
                  exact fin15Anchored_clause10455 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10456 chi hbad
                ·
                  exact fin15Anchored_clause10457 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10458 chi hbad
                ·
                  exact fin15Anchored_clause10459 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10460 chi hbad
                ·
                  exact fin15Anchored_clause10461 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10462 chi hbad
                ·
                  exact fin15Anchored_clause10463 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10464 chi hbad
                ·
                  exact fin15Anchored_clause10465 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10466 chi hbad
                ·
                  exact fin15Anchored_clause10467 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10468 chi hbad
                ·
                  exact fin15Anchored_clause10469 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10470 chi hbad
                ·
                  exact fin15Anchored_clause10471 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10472 chi hbad
                ·
                  exact fin15Anchored_clause10473 chi hbad
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
                exact fin15Anchored_clause10474 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10475 chi hbad
                ·
                  exact fin15Anchored_clause10476 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10477 chi hbad
                ·
                  exact fin15Anchored_clause10478 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10479 chi hbad
                ·
                  exact fin15Anchored_clause10480 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10481 chi hbad
                ·
                  exact fin15Anchored_clause10482 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10483 chi hbad
                ·
                  exact fin15Anchored_clause10484 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10485 chi hbad
                ·
                  exact fin15Anchored_clause10486 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10487 chi hbad
                ·
                  exact fin15Anchored_clause10488 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10489 chi hbad
                ·
                  exact fin15Anchored_clause10490 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10491 chi hbad
                ·
                  exact fin15Anchored_clause10492 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10493 chi hbad
                ·
                  exact fin15Anchored_clause10494 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10495 chi hbad
                ·
                  exact fin15Anchored_clause10496 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10497 chi hbad
                ·
                  exact fin15Anchored_clause10498 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10499 chi hbad
                ·
                  exact fin15Anchored_clause10500 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10501 chi hbad
                ·
                  exact fin15Anchored_clause10502 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10503 chi hbad
                ·
                  exact fin15Anchored_clause10504 chi hbad
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
                  exact fin15Anchored_clause10505 chi hbad
                ·
                  exact fin15Anchored_clause10506 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10507 chi hbad
                ·
                  exact fin15Anchored_clause10508 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10509 chi hbad
                ·
                  exact fin15Anchored_clause10510 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10511 chi hbad
                ·
                  exact fin15Anchored_clause10512 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10513 chi hbad
                ·
                  exact fin15Anchored_clause10514 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10515 chi hbad
                ·
                  exact fin15Anchored_clause10516 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10517 chi hbad
                ·
                  exact fin15Anchored_clause10518 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10519 chi hbad
                ·
                  exact fin15Anchored_clause10520 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10521 chi hbad
                ·
                  exact fin15Anchored_clause10522 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10523 chi hbad
                ·
                  exact fin15Anchored_clause10524 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10525 chi hbad
                ·
                  exact fin15Anchored_clause10526 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10527 chi hbad
                ·
                  exact fin15Anchored_clause10528 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10529 chi hbad
                ·
                  exact fin15Anchored_clause10530 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10531 chi hbad
                ·
                  exact fin15Anchored_clause10532 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10533 chi hbad
                ·
                  exact fin15Anchored_clause10534 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10535 chi hbad
                ·
                  exact fin15Anchored_clause10536 chi hbad
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
                exact fin15Anchored_clause10537 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10538 chi hbad
                ·
                  exact fin15Anchored_clause10539 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10540 chi hbad
                ·
                  exact fin15Anchored_clause10541 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10542 chi hbad
                ·
                  exact fin15Anchored_clause10543 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10544 chi hbad
                ·
                  exact fin15Anchored_clause10545 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10546 chi hbad
                ·
                  exact fin15Anchored_clause10547 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10548 chi hbad
                ·
                  exact fin15Anchored_clause10549 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10550 chi hbad
                ·
                  exact fin15Anchored_clause10551 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10552 chi hbad
                ·
                  exact fin15Anchored_clause10553 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10554 chi hbad
                ·
                  exact fin15Anchored_clause10555 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10556 chi hbad
                ·
                  exact fin15Anchored_clause10557 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10558 chi hbad
                ·
                  exact fin15Anchored_clause10559 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10560 chi hbad
                ·
                  exact fin15Anchored_clause10561 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10562 chi hbad
                ·
                  exact fin15Anchored_clause10563 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10564 chi hbad
                ·
                  exact fin15Anchored_clause10565 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10566 chi hbad
                ·
                  exact fin15Anchored_clause10567 chi hbad
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
                  exact fin15Anchored_clause10568 chi hbad
                ·
                  exact fin15Anchored_clause10569 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10570 chi hbad
                ·
                  exact fin15Anchored_clause10571 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10572 chi hbad
                ·
                  exact fin15Anchored_clause10573 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10574 chi hbad
                ·
                  exact fin15Anchored_clause10575 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10576 chi hbad
                ·
                  exact fin15Anchored_clause10577 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10578 chi hbad
                ·
                  exact fin15Anchored_clause10579 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10580 chi hbad
                ·
                  exact fin15Anchored_clause10581 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10582 chi hbad
                ·
                  exact fin15Anchored_clause10583 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10584 chi hbad
                ·
                  exact fin15Anchored_clause10585 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10586 chi hbad
                ·
                  exact fin15Anchored_clause10587 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10588 chi hbad
                ·
                  exact fin15Anchored_clause10589 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10590 chi hbad
                ·
                  exact fin15Anchored_clause10591 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10592 chi hbad
                ·
                  exact fin15Anchored_clause10593 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10594 chi hbad
                ·
                  exact fin15Anchored_clause10595 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10596 chi hbad
                ·
                  exact fin15Anchored_clause10597 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10598 chi hbad
                ·
                  exact fin15Anchored_clause10599 chi hbad

end ErdosSzekeres

end
