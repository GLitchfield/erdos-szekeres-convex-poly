module

public import ErdosSzekeres.Fin15AnchoredClauseChunk088
public import ErdosSzekeres.Fin15AnchoredClauseChunk089
public import ErdosSzekeres.Fin15AnchoredClauseChunk090

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 045. -/

theorem fin15Anchored_rejectSemanticSegment045
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom1315 chi) ∨
      ((Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1315 chi) ∨
      (Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom1315 chi))) ∨
      (((¬Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom1316 chi) ∨
      (¬Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1316 chi)) ∨
      ((¬Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1316 chi) ∨
      (Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1316 chi)))) ∨
      ((((Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom1316 chi) ∨
      (Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1316 chi)) ∨
      ((Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom1316 chi) ∨
      (¬Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom1317 chi))) ∨
      (((¬Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom1317 chi) ∨
      (Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom1317 chi)) ∨
      ((Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom1317 chi) ∨
      (Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom1317 chi))))) ∨
      (((((Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      Fin15AnchoredAtom1318 chi) ∨
      (¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1319 chi)) ∨
      ((¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1319 chi) ∨
      (¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1319 chi))) ∨
      (((¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1319 chi) ∨
      (¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1319 chi)) ∨
      ((Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1319 chi) ∨
      (Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1319 chi)))) ∨
      ((((Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1319 chi) ∨
      (Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1319 chi)) ∨
      ((Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1319 chi) ∨
      (¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1320 chi))) ∨
      (((¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1320 chi) ∨
      (¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1320 chi)) ∨
      ((¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1320 chi) ∨
      (Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1320 chi)))))) ∨
      ((((((Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1320 chi) ∨
      (Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1320 chi)) ∨
      ((Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1320 chi) ∨
      (Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1320 chi))) ∨
      (((Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1320 chi) ∨
      (¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1321 chi)) ∨
      ((¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1321 chi) ∨
      (¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1321 chi)))) ∨
      ((((¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1321 chi) ∨
      (Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1321 chi)) ∨
      ((Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1321 chi) ∨
      (Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1321 chi))) ∨
      (((Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1321 chi) ∨
      (Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1321 chi)) ∨
      ((Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1321 chi) ∨
      (¬Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1322 chi))))) ∨
      (((((¬Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom1322 chi) ∨
      (¬Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1322 chi)) ∨
      ((Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1322 chi) ∨
      (Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom1322 chi))) ∨
      (((Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1322 chi) ∨
      (Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom1322 chi)) ∨
      ((¬Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom1323 chi) ∨
      (¬Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1323 chi)))) ∨
      ((((¬Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom1323 chi) ∨
      (¬Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0232 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1323 chi)) ∨
      ((Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1323 chi) ∨
      (Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom1323 chi))) ∨
      (((Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0232 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1323 chi) ∨
      (¬Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0454 chi ∧
      Fin15AnchoredAtom1324 chi)) ∨
      ((¬Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0454 chi ∧
      ¬Fin15AnchoredAtom1324 chi) ∨
      (Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0232 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0454 chi ∧
      ¬Fin15AnchoredAtom1324 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1325 chi) ∨
      ((¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1325 chi) ∨
      (¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1325 chi))) ∨
      (((¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1325 chi) ∨
      (¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1325 chi)) ∨
      ((Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1325 chi) ∨
      (Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1325 chi)))) ∨
      ((((Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1325 chi) ∨
      (Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1325 chi)) ∨
      ((Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1325 chi) ∨
      (Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1325 chi))) ∨
      (((¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom1326 chi) ∨
      (¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom1326 chi)) ∨
      ((¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom1326 chi) ∨
      (¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom1326 chi))))) ∨
      (((((Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom1326 chi) ∨
      (Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom1326 chi)) ∨
      ((Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom1326 chi) ∨
      (Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom1326 chi))) ∨
      (((Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom1326 chi) ∨
      (¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom1327 chi)) ∨
      ((¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom1327 chi) ∨
      (¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom1327 chi)))) ∨
      ((((¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom1327 chi) ∨
      (Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom1327 chi)) ∨
      ((Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom1327 chi) ∨
      (Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom1327 chi))) ∨
      (((Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom1327 chi) ∨
      (Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom1327 chi)) ∨
      ((¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom1328 chi) ∨
      (¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom1328 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom1328 chi) ∨
      (¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom1328 chi)) ∨
      ((¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom1328 chi) ∨
      (Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom1328 chi))) ∨
      (((Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom1328 chi) ∨
      (Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom1328 chi)) ∨
      ((Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom1328 chi) ∨
      (¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom1329 chi)))) ∨
      ((((¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom1329 chi) ∨
      (¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom1329 chi)) ∨
      ((¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom1329 chi) ∨
      (¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom1329 chi))) ∨
      (((Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom1329 chi) ∨
      (Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom1329 chi)) ∨
      ((Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom1329 chi) ∨
      (Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom1329 chi))))) ∨
      (((((¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom1330 chi) ∨
      (¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom1330 chi)) ∨
      ((¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom1330 chi) ∨
      (¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom1330 chi))) ∨
      (((¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom1330 chi) ∨
      (Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom1330 chi)) ∨
      ((Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom1330 chi) ∨
      (Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom1330 chi)))) ∨
      ((((Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom1330 chi) ∨
      (Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom1330 chi)) ∨
      ((¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom1331 chi) ∨
      (¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom1331 chi))) ∨
      (((Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom1331 chi) ∨
      (Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom1331 chi)) ∨
      ((¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom1332 chi) ∨
      (¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom1332 chi)))))))) ∨
      (((((((¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom1332 chi) ∨
      ((¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom1332 chi) ∨
      (¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom1332 chi))) ∨
      (((Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom1332 chi) ∨
      (Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom1332 chi)) ∨
      ((Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom1332 chi) ∨
      (Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom1332 chi)))) ∨
      ((((Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom1332 chi) ∨
      (¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom1333 chi)) ∨
      ((¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom1333 chi) ∨
      (¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom1333 chi))) ∨
      (((¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom1333 chi) ∨
      (Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom1333 chi)) ∨
      ((Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom1333 chi) ∨
      (Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom1333 chi))))) ∨
      (((((Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom1333 chi) ∨
      (Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom1333 chi)) ∨
      ((Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom1333 chi) ∨
      (¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom1334 chi))) ∨
      (((¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom1334 chi) ∨
      (¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom1334 chi)) ∨
      ((¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom1334 chi) ∨
      (Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom1334 chi)))) ∨
      ((((Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom1334 chi) ∨
      (Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom1334 chi)) ∨
      ((Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom1334 chi) ∨
      (¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom1335 chi))) ∨
      (((¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom1335 chi) ∨
      (¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom1335 chi)) ∨
      ((¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom1335 chi) ∨
      (Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom1335 chi)))))) ∨
      ((((((Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom1335 chi) ∨
      (Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom1335 chi)) ∨
      ((Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom1335 chi) ∨
      (Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom1335 chi))) ∨
      (((¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom1336 chi) ∨
      (¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom1336 chi)) ∨
      ((¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom1336 chi) ∨
      (¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom1336 chi)))) ∨
      ((((Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom1336 chi) ∨
      (Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom1336 chi)) ∨
      ((Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom1336 chi) ∨
      (Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom1336 chi))) ∨
      (((Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom1336 chi) ∨
      (Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom1336 chi)) ∨
      ((¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom1337 chi) ∨
      (¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom1337 chi))))) ∨
      (((((¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom1337 chi) ∨
      (¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom1337 chi)) ∨
      ((Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom1337 chi) ∨
      (Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom1337 chi))) ∨
      (((Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom1337 chi) ∨
      (Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom1337 chi)) ∨
      ((¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom1338 chi) ∨
      (¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom1338 chi)))) ∨
      ((((¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom1338 chi) ∨
      (¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom1338 chi)) ∨
      ((¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom1338 chi) ∨
      (¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom1338 chi))) ∨
      (((Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom1338 chi) ∨
      (Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom1338 chi)) ∨
      ((Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom1338 chi) ∨
      (Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom1338 chi))))))) ∨
      (((((((Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom1338 chi) ∨
      (¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom1339 chi)) ∨
      ((Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom1339 chi) ∨
      (¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom1340 chi))) ∨
      (((¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom1340 chi) ∨
      (¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom1340 chi)) ∨
      ((¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom1340 chi) ∨
      (Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom1340 chi)))) ∨
      ((((Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom1340 chi) ∨
      (Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom1340 chi)) ∨
      ((Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom1340 chi) ∨
      (¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom1341 chi))) ∨
      (((¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom1341 chi) ∨
      (¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom1341 chi)) ∨
      ((¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom1341 chi) ∨
      (¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom1341 chi))))) ∨
      (((((Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom1341 chi) ∨
      (Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom1341 chi)) ∨
      ((Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom1341 chi) ∨
      (Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom1341 chi))) ∨
      (((¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom1342 chi) ∨
      (¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom1342 chi)) ∨
      ((¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom1342 chi) ∨
      (¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom1342 chi)))) ∨
      ((((Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom1342 chi) ∨
      (Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom1342 chi)) ∨
      ((Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom1342 chi) ∨
      (Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom1342 chi))) ∨
      (((¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom1343 chi) ∨
      (¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom1343 chi)) ∨
      ((¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom1343 chi) ∨
      (¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom1343 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom1343 chi) ∨
      (¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom1343 chi)) ∨
      ((Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom1343 chi) ∨
      (Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom1343 chi))) ∨
      (((Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom1343 chi) ∨
      (Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom1343 chi)) ∨
      ((Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom1343 chi) ∨
      (¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom1344 chi)))) ∨
      ((((¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom1344 chi) ∨
      (¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom1344 chi)) ∨
      ((¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom1344 chi) ∨
      (¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom1344 chi))) ∨
      (((Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom1344 chi) ∨
      (Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom1344 chi)) ∨
      ((Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom1344 chi) ∨
      (Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom1344 chi))))) ∨
      (((((¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom1345 chi) ∨
      (¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom1345 chi)) ∨
      ((¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom1345 chi) ∨
      (¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom1345 chi))) ∨
      (((¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom1345 chi) ∨
      (¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom1345 chi)) ∨
      ((¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom1345 chi) ∨
      (Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom1345 chi)))) ∨
      ((((Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom1345 chi) ∨
      (Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom1345 chi)) ∨
      ((Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom1345 chi) ∨
      (¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom1346 chi))) ∨
      (((¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom1346 chi) ∨
      (Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom1346 chi)) ∨
      ((¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom1347 chi) ∨
      (¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom1347 chi)))))))))) := by
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
                exact fin15Anchored_clause11357 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11358 chi hbad
                ·
                  exact fin15Anchored_clause11359 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11360 chi hbad
                ·
                  exact fin15Anchored_clause11361 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11362 chi hbad
                ·
                  exact fin15Anchored_clause11363 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11364 chi hbad
                ·
                  exact fin15Anchored_clause11365 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11366 chi hbad
                ·
                  exact fin15Anchored_clause11367 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11368 chi hbad
                ·
                  exact fin15Anchored_clause11369 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11370 chi hbad
                ·
                  exact fin15Anchored_clause11371 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11372 chi hbad
                ·
                  exact fin15Anchored_clause11373 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11374 chi hbad
                ·
                  exact fin15Anchored_clause11375 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11376 chi hbad
                ·
                  exact fin15Anchored_clause11377 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11378 chi hbad
                ·
                  exact fin15Anchored_clause11379 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11380 chi hbad
                ·
                  exact fin15Anchored_clause11381 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11382 chi hbad
                ·
                  exact fin15Anchored_clause11383 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11384 chi hbad
                ·
                  exact fin15Anchored_clause11385 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11386 chi hbad
                ·
                  exact fin15Anchored_clause11387 chi hbad
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
                  exact fin15Anchored_clause11388 chi hbad
                ·
                  exact fin15Anchored_clause11389 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11390 chi hbad
                ·
                  exact fin15Anchored_clause11391 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11392 chi hbad
                ·
                  exact fin15Anchored_clause11393 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11394 chi hbad
                ·
                  exact fin15Anchored_clause11395 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11396 chi hbad
                ·
                  exact fin15Anchored_clause11397 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11398 chi hbad
                ·
                  exact fin15Anchored_clause11399 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11400 chi hbad
                ·
                  exact fin15Anchored_clause11401 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11402 chi hbad
                ·
                  exact fin15Anchored_clause11403 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11404 chi hbad
                ·
                  exact fin15Anchored_clause11405 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11406 chi hbad
                ·
                  exact fin15Anchored_clause11407 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11408 chi hbad
                ·
                  exact fin15Anchored_clause11409 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11410 chi hbad
                ·
                  exact fin15Anchored_clause11411 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11412 chi hbad
                ·
                  exact fin15Anchored_clause11413 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11414 chi hbad
                ·
                  exact fin15Anchored_clause11415 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11416 chi hbad
                ·
                  exact fin15Anchored_clause11417 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11418 chi hbad
                ·
                  exact fin15Anchored_clause11419 chi hbad
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
                exact fin15Anchored_clause11420 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11421 chi hbad
                ·
                  exact fin15Anchored_clause11422 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11423 chi hbad
                ·
                  exact fin15Anchored_clause11424 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11425 chi hbad
                ·
                  exact fin15Anchored_clause11426 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11427 chi hbad
                ·
                  exact fin15Anchored_clause11428 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11429 chi hbad
                ·
                  exact fin15Anchored_clause11430 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11431 chi hbad
                ·
                  exact fin15Anchored_clause11432 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11433 chi hbad
                ·
                  exact fin15Anchored_clause11434 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11435 chi hbad
                ·
                  exact fin15Anchored_clause11436 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11437 chi hbad
                ·
                  exact fin15Anchored_clause11438 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11439 chi hbad
                ·
                  exact fin15Anchored_clause11440 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11441 chi hbad
                ·
                  exact fin15Anchored_clause11442 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11443 chi hbad
                ·
                  exact fin15Anchored_clause11444 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11445 chi hbad
                ·
                  exact fin15Anchored_clause11446 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11447 chi hbad
                ·
                  exact fin15Anchored_clause11448 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11449 chi hbad
                ·
                  exact fin15Anchored_clause11450 chi hbad
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
                  exact fin15Anchored_clause11451 chi hbad
                ·
                  exact fin15Anchored_clause11452 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11453 chi hbad
                ·
                  exact fin15Anchored_clause11454 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11455 chi hbad
                ·
                  exact fin15Anchored_clause11456 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11457 chi hbad
                ·
                  exact fin15Anchored_clause11458 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11459 chi hbad
                ·
                  exact fin15Anchored_clause11460 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11461 chi hbad
                ·
                  exact fin15Anchored_clause11462 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11463 chi hbad
                ·
                  exact fin15Anchored_clause11464 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11465 chi hbad
                ·
                  exact fin15Anchored_clause11466 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11467 chi hbad
                ·
                  exact fin15Anchored_clause11468 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11469 chi hbad
                ·
                  exact fin15Anchored_clause11470 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11471 chi hbad
                ·
                  exact fin15Anchored_clause11472 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11473 chi hbad
                ·
                  exact fin15Anchored_clause11474 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11475 chi hbad
                ·
                  exact fin15Anchored_clause11476 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11477 chi hbad
                ·
                  exact fin15Anchored_clause11478 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11479 chi hbad
                ·
                  exact fin15Anchored_clause11480 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11481 chi hbad
                ·
                  exact fin15Anchored_clause11482 chi hbad
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
                exact fin15Anchored_clause11483 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11484 chi hbad
                ·
                  exact fin15Anchored_clause11485 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11486 chi hbad
                ·
                  exact fin15Anchored_clause11487 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11488 chi hbad
                ·
                  exact fin15Anchored_clause11489 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11490 chi hbad
                ·
                  exact fin15Anchored_clause11491 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11492 chi hbad
                ·
                  exact fin15Anchored_clause11493 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11494 chi hbad
                ·
                  exact fin15Anchored_clause11495 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11496 chi hbad
                ·
                  exact fin15Anchored_clause11497 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11498 chi hbad
                ·
                  exact fin15Anchored_clause11499 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11500 chi hbad
                ·
                  exact fin15Anchored_clause11501 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11502 chi hbad
                ·
                  exact fin15Anchored_clause11503 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11504 chi hbad
                ·
                  exact fin15Anchored_clause11505 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11506 chi hbad
                ·
                  exact fin15Anchored_clause11507 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11508 chi hbad
                ·
                  exact fin15Anchored_clause11509 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11510 chi hbad
                ·
                  exact fin15Anchored_clause11511 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11512 chi hbad
                ·
                  exact fin15Anchored_clause11513 chi hbad
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
                  exact fin15Anchored_clause11514 chi hbad
                ·
                  exact fin15Anchored_clause11515 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11516 chi hbad
                ·
                  exact fin15Anchored_clause11517 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11518 chi hbad
                ·
                  exact fin15Anchored_clause11519 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11520 chi hbad
                ·
                  exact fin15Anchored_clause11521 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11522 chi hbad
                ·
                  exact fin15Anchored_clause11523 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11524 chi hbad
                ·
                  exact fin15Anchored_clause11525 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11526 chi hbad
                ·
                  exact fin15Anchored_clause11527 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11528 chi hbad
                ·
                  exact fin15Anchored_clause11529 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11530 chi hbad
                ·
                  exact fin15Anchored_clause11531 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11532 chi hbad
                ·
                  exact fin15Anchored_clause11533 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11534 chi hbad
                ·
                  exact fin15Anchored_clause11535 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11536 chi hbad
                ·
                  exact fin15Anchored_clause11537 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11538 chi hbad
                ·
                  exact fin15Anchored_clause11539 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11540 chi hbad
                ·
                  exact fin15Anchored_clause11541 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11542 chi hbad
                ·
                  exact fin15Anchored_clause11543 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11544 chi hbad
                ·
                  exact fin15Anchored_clause11545 chi hbad
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
                  exact fin15Anchored_clause11546 chi hbad
                ·
                  exact fin15Anchored_clause11547 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11548 chi hbad
                ·
                  exact fin15Anchored_clause11549 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11550 chi hbad
                ·
                  exact fin15Anchored_clause11551 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11552 chi hbad
                ·
                  exact fin15Anchored_clause11553 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11554 chi hbad
                ·
                  exact fin15Anchored_clause11555 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11556 chi hbad
                ·
                  exact fin15Anchored_clause11557 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11558 chi hbad
                ·
                  exact fin15Anchored_clause11559 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11560 chi hbad
                ·
                  exact fin15Anchored_clause11561 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11562 chi hbad
                ·
                  exact fin15Anchored_clause11563 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11564 chi hbad
                ·
                  exact fin15Anchored_clause11565 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11566 chi hbad
                ·
                  exact fin15Anchored_clause11567 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11568 chi hbad
                ·
                  exact fin15Anchored_clause11569 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11570 chi hbad
                ·
                  exact fin15Anchored_clause11571 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11572 chi hbad
                ·
                  exact fin15Anchored_clause11573 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11574 chi hbad
                ·
                  exact fin15Anchored_clause11575 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11576 chi hbad
                ·
                  exact fin15Anchored_clause11577 chi hbad
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
                  exact fin15Anchored_clause11578 chi hbad
                ·
                  exact fin15Anchored_clause11579 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11580 chi hbad
                ·
                  exact fin15Anchored_clause11581 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11582 chi hbad
                ·
                  exact fin15Anchored_clause11583 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11584 chi hbad
                ·
                  exact fin15Anchored_clause11585 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11586 chi hbad
                ·
                  exact fin15Anchored_clause11587 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11588 chi hbad
                ·
                  exact fin15Anchored_clause11589 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11590 chi hbad
                ·
                  exact fin15Anchored_clause11591 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11592 chi hbad
                ·
                  exact fin15Anchored_clause11593 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11594 chi hbad
                ·
                  exact fin15Anchored_clause11595 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11596 chi hbad
                ·
                  exact fin15Anchored_clause11597 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11598 chi hbad
                ·
                  exact fin15Anchored_clause11599 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11600 chi hbad
                ·
                  exact fin15Anchored_clause11601 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11602 chi hbad
                ·
                  exact fin15Anchored_clause11603 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11604 chi hbad
                ·
                  exact fin15Anchored_clause11605 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11606 chi hbad
                ·
                  exact fin15Anchored_clause11607 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11608 chi hbad
                ·
                  exact fin15Anchored_clause11609 chi hbad

end ErdosSzekeres

end
