module

public import ErdosSzekeres.Fin15AnchoredClauseChunk082
public import ErdosSzekeres.Fin15AnchoredClauseChunk083
public import ErdosSzekeres.Fin15AnchoredClauseChunk084

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 042. -/

theorem fin15Anchored_rejectSemanticSegment042
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom1193 chi) ∨
      ((Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom1193 chi) ∨
      (Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom1193 chi))) ∨
      (((Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom1193 chi) ∨
      (¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom1194 chi)) ∨
      ((¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom1194 chi) ∨
      (¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom1194 chi)))) ∨
      ((((¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom1194 chi) ∨
      (¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom1194 chi)) ∨
      ((Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom1194 chi) ∨
      (Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom1194 chi))) ∨
      (((Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom1194 chi) ∨
      (Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom1194 chi)) ∨
      ((¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom1195 chi) ∨
      (¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom1195 chi))))) ∨
      (((((¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom1195 chi) ∨
      (¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom1195 chi)) ∨
      ((Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom1195 chi) ∨
      (Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom1195 chi))) ∨
      (((Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom1195 chi) ∨
      (Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom1195 chi)) ∨
      ((Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom1195 chi) ∨
      (¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom1196 chi)))) ∨
      ((((Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom1196 chi) ∨
      (Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom1196 chi)) ∨
      ((Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom1196 chi) ∨
      (Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom1196 chi))) ∨
      (((¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom1197 chi) ∨
      (¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom1197 chi)) ∨
      ((¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom1197 chi) ∨
      (¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom1197 chi)))))) ∨
      ((((((Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom1197 chi) ∨
      (Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom1197 chi)) ∨
      ((Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom1197 chi) ∨
      (Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom1197 chi))) ∨
      (((¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom1198 chi) ∨
      (¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom1198 chi)) ∨
      ((¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom1198 chi) ∨
      (¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom1198 chi)))) ∨
      ((((¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom1198 chi) ∨
      (Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom1198 chi)) ∨
      ((Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom1198 chi) ∨
      (Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom1198 chi))) ∨
      (((Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom1198 chi) ∨
      (¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom1199 chi)) ∨
      ((¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom1199 chi) ∨
      (¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom1199 chi))))) ∨
      (((((¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom1199 chi) ∨
      (Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom1199 chi)) ∨
      ((Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom1199 chi) ∨
      (Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom1199 chi))) ∨
      (((Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom1199 chi) ∨
      (Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom1199 chi)) ∨
      ((¬Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom1200 chi) ∨
      (Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom1200 chi)))) ∨
      ((((Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom1200 chi) ∨
      (¬Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom1201 chi)) ∨
      ((Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom1201 chi) ∨
      (Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom1201 chi))) ∨
      (((¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom1203 chi) ∨
      (¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom1203 chi)) ∨
      ((¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom1203 chi) ∨
      (¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom1203 chi))))))) ∨
      ((((((Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom1203 chi) ∨
      ((Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom1203 chi) ∨
      (Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom1203 chi))) ∨
      (((Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom1203 chi) ∨
      (¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom1204 chi)) ∨
      ((¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom1204 chi) ∨
      (¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom1204 chi)))) ∨
      ((((¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom1204 chi) ∨
      (Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom1204 chi)) ∨
      ((Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom1204 chi) ∨
      (Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom1204 chi))) ∨
      (((Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom1204 chi) ∨
      (¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom1205 chi)) ∨
      ((¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom1205 chi) ∨
      (¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom1205 chi))))) ∨
      (((((¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom1205 chi) ∨
      (¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom1205 chi)) ∨
      ((Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom1205 chi) ∨
      (Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom1205 chi))) ∨
      (((Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom1205 chi) ∨
      (Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom1205 chi)) ∨
      ((¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom1206 chi) ∨
      (¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom1206 chi)))) ∨
      ((((¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom1206 chi) ∨
      (¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom1206 chi)) ∨
      ((¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom1206 chi) ∨
      (Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom1206 chi))) ∨
      (((Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom1206 chi) ∨
      (Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom1206 chi)) ∨
      ((Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom1206 chi) ∨
      (¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom1207 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0193 chi ∧
      Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom1207 chi) ∨
      (Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom1207 chi)) ∨
      ((¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom1208 chi) ∨
      (¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom1208 chi))) ∨
      (((¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom1208 chi) ∨
      (¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom1208 chi)) ∨
      ((Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom1208 chi) ∨
      (Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom1208 chi)))) ∨
      ((((Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom1208 chi) ∨
      (Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom1208 chi)) ∨
      ((Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom1208 chi) ∨
      (¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom1209 chi))) ∨
      (((¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom1209 chi) ∨
      (¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom1209 chi)) ∨
      ((¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom1209 chi) ∨
      (Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom1209 chi))))) ∨
      (((((Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom1209 chi) ∨
      (Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom1209 chi)) ∨
      ((Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom1209 chi) ∨
      (¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom1210 chi))) ∨
      (((¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom1210 chi) ∨
      (¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom1210 chi)) ∨
      ((Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom1210 chi) ∨
      (Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom1210 chi)))) ∨
      ((((Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom1210 chi) ∨
      (Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom1210 chi)) ∨
      ((¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom1211 chi) ∨
      (¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom1211 chi))) ∨
      (((¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom1211 chi) ∨
      (¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom1211 chi)) ∨
      ((¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom1211 chi) ∨
      (Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom1211 chi)))))))) ∨
      (((((((Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom1211 chi) ∨
      ((Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom1211 chi) ∨
      (Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom1211 chi))) ∨
      (((Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom1211 chi) ∨
      (¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom1212 chi)) ∨
      ((¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom1212 chi) ∨
      (¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom1212 chi)))) ∨
      ((((¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom1212 chi) ∨
      (Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom1212 chi)) ∨
      ((Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom1212 chi) ∨
      (Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom1212 chi))) ∨
      (((Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom1212 chi) ∨
      (Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom1212 chi)) ∨
      ((¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom1213 chi) ∨
      (¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom1213 chi))))) ∨
      (((((¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom1213 chi) ∨
      (¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom1213 chi)) ∨
      ((¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom1213 chi) ∨
      (Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom1213 chi))) ∨
      (((Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom1213 chi) ∨
      (Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom1213 chi)) ∨
      ((Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom1213 chi) ∨
      (Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom1213 chi)))) ∨
      ((((¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom1214 chi) ∨
      (¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom1214 chi)) ∨
      ((¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0193 chi ∧
      Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom1214 chi) ∨
      (¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom1215 chi))) ∨
      (((¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom1215 chi) ∨
      (¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom1215 chi)) ∨
      ((¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom1215 chi) ∨
      (Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom1215 chi)))))) ∨
      ((((((Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom1215 chi) ∨
      (Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom1215 chi)) ∨
      ((Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom1215 chi) ∨
      (¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom1216 chi))) ∨
      (((¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom1216 chi) ∨
      (¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom1216 chi)) ∨
      ((¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom1216 chi) ∨
      (¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom1216 chi)))) ∨
      ((((Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom1216 chi) ∨
      (Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom1216 chi)) ∨
      ((Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom1216 chi) ∨
      (Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom1216 chi))) ∨
      (((Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom1216 chi) ∨
      (¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom1217 chi)) ∨
      ((¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom1217 chi) ∨
      (Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom1217 chi))))) ∨
      (((((Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom1217 chi) ∨
      (Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom1217 chi)) ∨
      ((¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom1218 chi) ∨
      (¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom1218 chi))) ∨
      (((¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom1218 chi) ∨
      (¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom1218 chi)) ∨
      ((Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom1218 chi) ∨
      (Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom1218 chi)))) ∨
      ((((Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom1218 chi) ∨
      (Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom1218 chi)) ∨
      ((Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom1218 chi) ∨
      (¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom1219 chi))) ∨
      (((¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom1219 chi) ∨
      (¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom1219 chi)) ∨
      ((¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom1219 chi) ∨
      (¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom1219 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom1219 chi) ∨
      ((Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom1219 chi) ∨
      (Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom1219 chi))) ∨
      (((Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom1219 chi) ∨
      (Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom1219 chi)) ∨
      ((Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom1219 chi) ∨
      (¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom1220 chi)))) ∨
      ((((¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom1220 chi) ∨
      (¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom1220 chi)) ∨
      ((¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom1220 chi) ∨
      (¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom1220 chi))) ∨
      (((Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom1220 chi) ∨
      (Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom1220 chi)) ∨
      ((Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom1220 chi) ∨
      (Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom1220 chi))))) ∨
      (((((Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom1220 chi) ∨
      (¬Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom1221 chi)) ∨
      ((Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom1221 chi) ∨
      (¬Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom1222 chi))) ∨
      (((¬Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom1222 chi) ∨
      (¬Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom1222 chi)) ∨
      ((¬Fin15AnchoredAtom0193 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom1222 chi) ∨
      (Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom1222 chi)))) ∨
      ((((Fin15AnchoredAtom0193 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom1222 chi) ∨
      (Fin15AnchoredAtom0193 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom1222 chi)) ∨
      ((¬Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom1226 chi) ∨
      (¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom1227 chi))) ∨
      (((¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom1227 chi) ∨
      (¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom1227 chi)) ∨
      ((¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom1227 chi) ∨
      (Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom1227 chi)))))) ∨
      ((((((Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom1227 chi) ∨
      (Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom1227 chi)) ∨
      ((Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom1227 chi) ∨
      (Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom1227 chi))) ∨
      (((¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom1228 chi) ∨
      (Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom1228 chi)) ∨
      ((Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom1228 chi) ∨
      (Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom1228 chi)))) ∨
      ((((Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom1228 chi) ∨
      (¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom1229 chi)) ∨
      ((¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom1229 chi) ∨
      (¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom1229 chi))) ∨
      (((¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom1229 chi) ∨
      (Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom1229 chi)) ∨
      ((Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom1229 chi) ∨
      (Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom1229 chi))))) ∨
      (((((Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom1229 chi) ∨
      (Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom1229 chi)) ∨
      ((¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom1230 chi) ∨
      (¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom1230 chi))) ∨
      (((¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom1230 chi) ∨
      (¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom1230 chi)) ∨
      ((Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom1230 chi) ∨
      (Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom1230 chi)))) ∨
      ((((Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom1230 chi) ∨
      (Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom1230 chi)) ∨
      ((Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom1230 chi) ∨
      (¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom1231 chi))) ∨
      (((¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom1231 chi) ∨
      (¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom1231 chi)) ∨
      ((¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom1231 chi) ∨
      (Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom1231 chi)))))))))) := by
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
                exact fin15Anchored_clause10600 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10601 chi hbad
                ·
                  exact fin15Anchored_clause10602 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10603 chi hbad
                ·
                  exact fin15Anchored_clause10604 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10605 chi hbad
                ·
                  exact fin15Anchored_clause10606 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10607 chi hbad
                ·
                  exact fin15Anchored_clause10608 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10609 chi hbad
                ·
                  exact fin15Anchored_clause10610 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10611 chi hbad
                ·
                  exact fin15Anchored_clause10612 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10613 chi hbad
                ·
                  exact fin15Anchored_clause10614 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10615 chi hbad
                ·
                  exact fin15Anchored_clause10616 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10617 chi hbad
                ·
                  exact fin15Anchored_clause10618 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10619 chi hbad
                ·
                  exact fin15Anchored_clause10620 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10621 chi hbad
                ·
                  exact fin15Anchored_clause10622 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10623 chi hbad
                ·
                  exact fin15Anchored_clause10624 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10625 chi hbad
                ·
                  exact fin15Anchored_clause10626 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10627 chi hbad
                ·
                  exact fin15Anchored_clause10628 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10629 chi hbad
                ·
                  exact fin15Anchored_clause10630 chi hbad
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
                  exact fin15Anchored_clause10631 chi hbad
                ·
                  exact fin15Anchored_clause10632 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10633 chi hbad
                ·
                  exact fin15Anchored_clause10634 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10635 chi hbad
                ·
                  exact fin15Anchored_clause10636 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10637 chi hbad
                ·
                  exact fin15Anchored_clause10638 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10639 chi hbad
                ·
                  exact fin15Anchored_clause10640 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10641 chi hbad
                ·
                  exact fin15Anchored_clause10642 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10643 chi hbad
                ·
                  exact fin15Anchored_clause10644 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10645 chi hbad
                ·
                  exact fin15Anchored_clause10646 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10647 chi hbad
                ·
                  exact fin15Anchored_clause10648 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10649 chi hbad
                ·
                  exact fin15Anchored_clause10650 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10651 chi hbad
                ·
                  exact fin15Anchored_clause10652 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10653 chi hbad
                ·
                  exact fin15Anchored_clause10654 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10655 chi hbad
                ·
                  exact fin15Anchored_clause10656 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10657 chi hbad
                ·
                  exact fin15Anchored_clause10658 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10659 chi hbad
                ·
                  exact fin15Anchored_clause10660 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10661 chi hbad
                ·
                  exact fin15Anchored_clause10662 chi hbad
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
                exact fin15Anchored_clause10663 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10664 chi hbad
                ·
                  exact fin15Anchored_clause10665 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10666 chi hbad
                ·
                  exact fin15Anchored_clause10667 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10668 chi hbad
                ·
                  exact fin15Anchored_clause10669 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10670 chi hbad
                ·
                  exact fin15Anchored_clause10671 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10672 chi hbad
                ·
                  exact fin15Anchored_clause10673 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10674 chi hbad
                ·
                  exact fin15Anchored_clause10675 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10676 chi hbad
                ·
                  exact fin15Anchored_clause10677 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10678 chi hbad
                ·
                  exact fin15Anchored_clause10679 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10680 chi hbad
                ·
                  exact fin15Anchored_clause10681 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10682 chi hbad
                ·
                  exact fin15Anchored_clause10683 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10684 chi hbad
                ·
                  exact fin15Anchored_clause10685 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10686 chi hbad
                ·
                  exact fin15Anchored_clause10687 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10688 chi hbad
                ·
                  exact fin15Anchored_clause10689 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10690 chi hbad
                ·
                  exact fin15Anchored_clause10691 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10692 chi hbad
                ·
                  exact fin15Anchored_clause10693 chi hbad
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
                  exact fin15Anchored_clause10694 chi hbad
                ·
                  exact fin15Anchored_clause10695 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10696 chi hbad
                ·
                  exact fin15Anchored_clause10697 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10698 chi hbad
                ·
                  exact fin15Anchored_clause10699 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10700 chi hbad
                ·
                  exact fin15Anchored_clause10701 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10702 chi hbad
                ·
                  exact fin15Anchored_clause10703 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10704 chi hbad
                ·
                  exact fin15Anchored_clause10705 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10706 chi hbad
                ·
                  exact fin15Anchored_clause10707 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10708 chi hbad
                ·
                  exact fin15Anchored_clause10709 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10710 chi hbad
                ·
                  exact fin15Anchored_clause10711 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10712 chi hbad
                ·
                  exact fin15Anchored_clause10713 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10714 chi hbad
                ·
                  exact fin15Anchored_clause10715 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10716 chi hbad
                ·
                  exact fin15Anchored_clause10717 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10718 chi hbad
                ·
                  exact fin15Anchored_clause10719 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10720 chi hbad
                ·
                  exact fin15Anchored_clause10721 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10722 chi hbad
                ·
                  exact fin15Anchored_clause10723 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10724 chi hbad
                ·
                  exact fin15Anchored_clause10725 chi hbad
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
                exact fin15Anchored_clause10726 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10727 chi hbad
                ·
                  exact fin15Anchored_clause10728 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10729 chi hbad
                ·
                  exact fin15Anchored_clause10730 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10731 chi hbad
                ·
                  exact fin15Anchored_clause10732 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10733 chi hbad
                ·
                  exact fin15Anchored_clause10734 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10735 chi hbad
                ·
                  exact fin15Anchored_clause10736 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10737 chi hbad
                ·
                  exact fin15Anchored_clause10738 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10739 chi hbad
                ·
                  exact fin15Anchored_clause10740 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10741 chi hbad
                ·
                  exact fin15Anchored_clause10742 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10743 chi hbad
                ·
                  exact fin15Anchored_clause10744 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10745 chi hbad
                ·
                  exact fin15Anchored_clause10746 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10747 chi hbad
                ·
                  exact fin15Anchored_clause10748 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10749 chi hbad
                ·
                  exact fin15Anchored_clause10750 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10751 chi hbad
                ·
                  exact fin15Anchored_clause10752 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10753 chi hbad
                ·
                  exact fin15Anchored_clause10754 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10755 chi hbad
                ·
                  exact fin15Anchored_clause10756 chi hbad
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
                  exact fin15Anchored_clause10757 chi hbad
                ·
                  exact fin15Anchored_clause10758 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10759 chi hbad
                ·
                  exact fin15Anchored_clause10760 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10761 chi hbad
                ·
                  exact fin15Anchored_clause10762 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10763 chi hbad
                ·
                  exact fin15Anchored_clause10764 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10765 chi hbad
                ·
                  exact fin15Anchored_clause10766 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10767 chi hbad
                ·
                  exact fin15Anchored_clause10768 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10769 chi hbad
                ·
                  exact fin15Anchored_clause10770 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10771 chi hbad
                ·
                  exact fin15Anchored_clause10772 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10773 chi hbad
                ·
                  exact fin15Anchored_clause10774 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10775 chi hbad
                ·
                  exact fin15Anchored_clause10776 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10777 chi hbad
                ·
                  exact fin15Anchored_clause10778 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10779 chi hbad
                ·
                  exact fin15Anchored_clause10780 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10781 chi hbad
                ·
                  exact fin15Anchored_clause10782 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10783 chi hbad
                ·
                  exact fin15Anchored_clause10784 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10785 chi hbad
                ·
                  exact fin15Anchored_clause10786 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10787 chi hbad
                ·
                  exact fin15Anchored_clause10788 chi hbad
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
                exact fin15Anchored_clause10789 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10790 chi hbad
                ·
                  exact fin15Anchored_clause10791 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10792 chi hbad
                ·
                  exact fin15Anchored_clause10793 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10794 chi hbad
                ·
                  exact fin15Anchored_clause10795 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10796 chi hbad
                ·
                  exact fin15Anchored_clause10797 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10798 chi hbad
                ·
                  exact fin15Anchored_clause10799 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10800 chi hbad
                ·
                  exact fin15Anchored_clause10801 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10802 chi hbad
                ·
                  exact fin15Anchored_clause10803 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10804 chi hbad
                ·
                  exact fin15Anchored_clause10805 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10806 chi hbad
                ·
                  exact fin15Anchored_clause10807 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10808 chi hbad
                ·
                  exact fin15Anchored_clause10809 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10810 chi hbad
                ·
                  exact fin15Anchored_clause10811 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10812 chi hbad
                ·
                  exact fin15Anchored_clause10813 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10814 chi hbad
                ·
                  exact fin15Anchored_clause10815 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10816 chi hbad
                ·
                  exact fin15Anchored_clause10817 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10818 chi hbad
                ·
                  exact fin15Anchored_clause10819 chi hbad
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
                  exact fin15Anchored_clause10820 chi hbad
                ·
                  exact fin15Anchored_clause10821 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10822 chi hbad
                ·
                  exact fin15Anchored_clause10823 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10824 chi hbad
                ·
                  exact fin15Anchored_clause10825 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10826 chi hbad
                ·
                  exact fin15Anchored_clause10827 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10828 chi hbad
                ·
                  exact fin15Anchored_clause10829 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10830 chi hbad
                ·
                  exact fin15Anchored_clause10831 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10832 chi hbad
                ·
                  exact fin15Anchored_clause10833 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10834 chi hbad
                ·
                  exact fin15Anchored_clause10835 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10836 chi hbad
                ·
                  exact fin15Anchored_clause10837 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10838 chi hbad
                ·
                  exact fin15Anchored_clause10839 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10840 chi hbad
                ·
                  exact fin15Anchored_clause10841 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10842 chi hbad
                ·
                  exact fin15Anchored_clause10843 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10844 chi hbad
                ·
                  exact fin15Anchored_clause10845 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10846 chi hbad
                ·
                  exact fin15Anchored_clause10847 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10848 chi hbad
                ·
                  exact fin15Anchored_clause10849 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10850 chi hbad
                ·
                  exact fin15Anchored_clause10851 chi hbad

end ErdosSzekeres

end
