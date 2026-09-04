module

public import ErdosSzekeres.Fin15AnchoredClauseChunk090
public import ErdosSzekeres.Fin15AnchoredClauseChunk091
public import ErdosSzekeres.Fin15AnchoredClauseChunk092

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 046. -/

theorem fin15Anchored_rejectSemanticSegment046
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom1347 chi) ∨
      ((¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom1347 chi) ∨
      (¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom1347 chi))) ∨
      (((Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom1347 chi) ∨
      (Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom1347 chi)) ∨
      ((Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom1347 chi) ∨
      (Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom1347 chi)))) ∨
      ((((Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom1347 chi) ∨
      (¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom1348 chi)) ∨
      ((¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom1348 chi) ∨
      (¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom1348 chi))) ∨
      (((¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom1348 chi) ∨
      (Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom1348 chi)) ∨
      ((Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom1348 chi) ∨
      (Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom1348 chi))))) ∨
      (((((Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom1348 chi) ∨
      (Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom1348 chi)) ∨
      ((¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom1349 chi) ∨
      (¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom1349 chi))) ∨
      (((¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom1349 chi) ∨
      (¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom1349 chi)) ∨
      ((Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom1349 chi) ∨
      (Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom1349 chi)))) ∨
      ((((Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom1349 chi) ∨
      (Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom1349 chi)) ∨
      ((¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom1350 chi) ∨
      (¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom1350 chi))) ∨
      (((¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom1350 chi) ∨
      (¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom1350 chi)) ∨
      ((Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom1350 chi) ∨
      (Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom1350 chi)))))) ∨
      ((((((Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom1350 chi) ∨
      (Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom1350 chi)) ∨
      ((Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom1350 chi) ∨
      (¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom1351 chi))) ∨
      (((¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom1351 chi) ∨
      (¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom1351 chi)) ∨
      ((¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom1351 chi) ∨
      (¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom1351 chi)))) ∨
      ((((¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom1351 chi) ∨
      (Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom1351 chi)) ∨
      ((Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom1351 chi) ∨
      (Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom1351 chi))) ∨
      (((Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom1351 chi) ∨
      (Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom1351 chi)) ∨
      ((¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom1353 chi) ∨
      (¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom1353 chi))))) ∨
      (((((¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom1353 chi) ∨
      (¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom1353 chi)) ∨
      ((Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom1353 chi) ∨
      (Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom1353 chi))) ∨
      (((Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom1353 chi) ∨
      (Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom1353 chi)) ∨
      ((Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom1353 chi) ∨
      (¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom1354 chi)))) ∨
      ((((¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom1354 chi) ∨
      (¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom1354 chi)) ∨
      ((¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom1354 chi) ∨
      (Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom1354 chi))) ∨
      (((Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom1354 chi) ∨
      (Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom1354 chi)) ∨
      ((Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom1354 chi) ∨
      (¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom1355 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom1355 chi) ∨
      ((¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom1355 chi) ∨
      (¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom1355 chi))) ∨
      (((Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom1355 chi) ∨
      (Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom1355 chi)) ∨
      ((Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom1355 chi) ∨
      (Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom1355 chi)))) ∨
      ((((¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom1356 chi) ∨
      (¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom1356 chi)) ∨
      ((¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom1356 chi) ∨
      (¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom1356 chi))) ∨
      (((Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom1356 chi) ∨
      (Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom1356 chi)) ∨
      ((Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom1356 chi) ∨
      (Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom1356 chi))))) ∨
      (((((Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom1356 chi) ∨
      (¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom1357 chi)) ∨
      ((¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom1357 chi) ∨
      (¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom1357 chi))) ∨
      (((¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom1357 chi) ∨
      (¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom1357 chi)) ∨
      ((¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom1357 chi) ∨
      (Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom1357 chi)))) ∨
      ((((Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom1357 chi) ∨
      (¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom1358 chi)) ∨
      ((¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom1358 chi) ∨
      (¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom1358 chi))) ∨
      (((¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom1358 chi) ∨
      (Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom1358 chi)) ∨
      ((Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom1358 chi) ∨
      (Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom1358 chi)))))) ∨
      ((((((Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom1358 chi) ∨
      (¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom1359 chi)) ∨
      ((¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom1359 chi) ∨
      (¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom1359 chi))) ∨
      (((¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom1359 chi) ∨
      (Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom1359 chi)) ∨
      ((Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom1359 chi) ∨
      (Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom1359 chi)))) ∨
      ((((Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom1359 chi) ∨
      (¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom1360 chi)) ∨
      ((¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom1360 chi) ∨
      (¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom1360 chi))) ∨
      (((¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom1360 chi) ∨
      (Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom1360 chi)) ∨
      ((Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom1360 chi) ∨
      (Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom1360 chi))))) ∨
      (((((Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom1360 chi) ∨
      (Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom1360 chi)) ∨
      ((¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom1361 chi) ∨
      (Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom1361 chi))) ∨
      (((Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom1361 chi) ∨
      (Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom1361 chi)) ∨
      ((¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom1362 chi) ∨
      (¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom1362 chi)))) ∨
      ((((¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom1362 chi) ∨
      (¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom1362 chi)) ∨
      ((¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom1362 chi) ∨
      (Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom1362 chi))) ∨
      (((Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom1362 chi) ∨
      (Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom1362 chi)) ∨
      ((Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom1362 chi) ∨
      (Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom1362 chi)))))))) ∨
      (((((((¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom1363 chi) ∨
      ((¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom1363 chi) ∨
      (¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom1363 chi))) ∨
      (((¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom1363 chi) ∨
      (¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom1363 chi)) ∨
      ((Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom1363 chi) ∨
      (Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom1363 chi)))) ∨
      ((((Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom1363 chi) ∨
      (Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom1363 chi)) ∨
      ((Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom1363 chi) ∨
      (¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom1364 chi))) ∨
      (((¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom1364 chi) ∨
      (¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom1364 chi)) ∨
      ((¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom1364 chi) ∨
      (¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom1364 chi))))) ∨
      (((((Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom1364 chi) ∨
      (Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom1364 chi)) ∨
      ((Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom1364 chi) ∨
      (Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom1364 chi))) ∨
      (((Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom1364 chi) ∨
      (¬Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom1365 chi)) ∨
      ((¬Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom1365 chi) ∨
      (Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom1365 chi)))) ∨
      ((((Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom1365 chi) ∨
      (Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom1365 chi)) ∨
      ((¬Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom1366 chi) ∨
      (Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom1366 chi))) ∨
      (((Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0287 chi ∧
      ¬Fin15AnchoredAtom0332 chi ∧
      Fin15AnchoredAtom1367 chi) ∨
      (¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom1368 chi)) ∨
      ((¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom1368 chi) ∨
      (¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom1368 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom1368 chi) ∨
      (Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom1368 chi)) ∨
      ((Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom1368 chi) ∨
      (Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom1368 chi))) ∨
      (((Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom1368 chi) ∨
      (Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom1368 chi)) ∨
      ((¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom1369 chi) ∨
      (¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom1369 chi)))) ∨
      ((((¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom1369 chi) ∨
      (¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom1369 chi)) ∨
      ((¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom1369 chi) ∨
      (Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom1369 chi))) ∨
      (((Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom1369 chi) ∨
      (Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom1369 chi)) ∨
      ((Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom1369 chi) ∨
      (¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom1370 chi))))) ∨
      (((((¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom1370 chi) ∨
      (¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom1370 chi)) ∨
      ((¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom1370 chi) ∨
      (¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom1370 chi))) ∨
      (((Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom1370 chi) ∨
      (Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom1370 chi)) ∨
      ((Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom1370 chi) ∨
      (Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom1370 chi)))) ∨
      ((((¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom1371 chi) ∨
      (¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom1371 chi)) ∨
      ((¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom1371 chi) ∨
      (¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom1371 chi))) ∨
      (((Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom1371 chi) ∨
      (Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom1371 chi)) ∨
      ((Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom1371 chi) ∨
      (Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom1371 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom1372 chi) ∨
      ((¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom1372 chi) ∨
      (¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom1372 chi))) ∨
      (((¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom1372 chi) ∨
      (¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom1372 chi)) ∨
      ((Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom1372 chi) ∨
      (Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom1372 chi)))) ∨
      ((((Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom1372 chi) ∨
      (Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom1372 chi)) ∨
      ((Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom1372 chi) ∨
      (¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom1373 chi))) ∨
      (((¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom1373 chi) ∨
      (¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom1373 chi)) ∨
      ((¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom1373 chi) ∨
      (¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom1373 chi))))) ∨
      (((((¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom1373 chi) ∨
      (Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom1373 chi)) ∨
      ((Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom1373 chi) ∨
      (Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom1373 chi))) ∨
      (((Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom1373 chi) ∨
      (Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom1373 chi)) ∨
      ((¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom1374 chi) ∨
      (¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom1374 chi)))) ∨
      ((((¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom1374 chi) ∨
      (¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom1374 chi)) ∨
      ((Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom1374 chi) ∨
      (Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom1374 chi))) ∨
      (((Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom1374 chi) ∨
      (Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom1374 chi)) ∨
      ((Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom1374 chi) ∨
      (¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom1375 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom1375 chi) ∨
      (¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom1375 chi)) ∨
      ((¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom1375 chi) ∨
      (Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom1375 chi))) ∨
      (((Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom1375 chi) ∨
      (Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom1375 chi)) ∨
      ((¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom1376 chi) ∨
      (¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom1376 chi)))) ∨
      ((((¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom1376 chi) ∨
      (¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom1376 chi)) ∨
      ((¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom1376 chi) ∨
      (¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom1376 chi))) ∨
      (((Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom1376 chi) ∨
      (Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom1376 chi)) ∨
      ((Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom1376 chi) ∨
      (Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom1376 chi))))) ∨
      (((((¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom1377 chi) ∨
      (¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom1377 chi)) ∨
      ((¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom1377 chi) ∨
      (¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom1377 chi))) ∨
      (((Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom1377 chi) ∨
      (Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom1377 chi)) ∨
      ((Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom1377 chi) ∨
      (Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom1377 chi)))) ∨
      ((((Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom1377 chi) ∨
      (¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom1378 chi)) ∨
      ((¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom1378 chi) ∨
      (¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom1378 chi))) ∨
      (((¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom1378 chi) ∨
      (¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom1378 chi)) ∨
      ((¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom1378 chi) ∨
      (Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom1378 chi)))))))))) := by
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
                exact fin15Anchored_clause11610 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11611 chi hbad
                ·
                  exact fin15Anchored_clause11612 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11613 chi hbad
                ·
                  exact fin15Anchored_clause11614 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11615 chi hbad
                ·
                  exact fin15Anchored_clause11616 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11617 chi hbad
                ·
                  exact fin15Anchored_clause11618 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11619 chi hbad
                ·
                  exact fin15Anchored_clause11620 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11621 chi hbad
                ·
                  exact fin15Anchored_clause11622 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11623 chi hbad
                ·
                  exact fin15Anchored_clause11624 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11625 chi hbad
                ·
                  exact fin15Anchored_clause11626 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11627 chi hbad
                ·
                  exact fin15Anchored_clause11628 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11629 chi hbad
                ·
                  exact fin15Anchored_clause11630 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11631 chi hbad
                ·
                  exact fin15Anchored_clause11632 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11633 chi hbad
                ·
                  exact fin15Anchored_clause11634 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11635 chi hbad
                ·
                  exact fin15Anchored_clause11636 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11637 chi hbad
                ·
                  exact fin15Anchored_clause11638 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11639 chi hbad
                ·
                  exact fin15Anchored_clause11640 chi hbad
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
                  exact fin15Anchored_clause11641 chi hbad
                ·
                  exact fin15Anchored_clause11642 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11643 chi hbad
                ·
                  exact fin15Anchored_clause11644 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11645 chi hbad
                ·
                  exact fin15Anchored_clause11646 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11647 chi hbad
                ·
                  exact fin15Anchored_clause11648 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11649 chi hbad
                ·
                  exact fin15Anchored_clause11650 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11651 chi hbad
                ·
                  exact fin15Anchored_clause11652 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11653 chi hbad
                ·
                  exact fin15Anchored_clause11654 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11655 chi hbad
                ·
                  exact fin15Anchored_clause11656 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11657 chi hbad
                ·
                  exact fin15Anchored_clause11658 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11659 chi hbad
                ·
                  exact fin15Anchored_clause11660 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11661 chi hbad
                ·
                  exact fin15Anchored_clause11662 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11663 chi hbad
                ·
                  exact fin15Anchored_clause11664 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11665 chi hbad
                ·
                  exact fin15Anchored_clause11666 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11667 chi hbad
                ·
                  exact fin15Anchored_clause11668 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11669 chi hbad
                ·
                  exact fin15Anchored_clause11670 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11671 chi hbad
                ·
                  exact fin15Anchored_clause11672 chi hbad
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
                exact fin15Anchored_clause11673 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11674 chi hbad
                ·
                  exact fin15Anchored_clause11675 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11676 chi hbad
                ·
                  exact fin15Anchored_clause11677 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11678 chi hbad
                ·
                  exact fin15Anchored_clause11679 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11680 chi hbad
                ·
                  exact fin15Anchored_clause11681 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11682 chi hbad
                ·
                  exact fin15Anchored_clause11683 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11684 chi hbad
                ·
                  exact fin15Anchored_clause11685 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11686 chi hbad
                ·
                  exact fin15Anchored_clause11687 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11688 chi hbad
                ·
                  exact fin15Anchored_clause11689 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11690 chi hbad
                ·
                  exact fin15Anchored_clause11691 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11692 chi hbad
                ·
                  exact fin15Anchored_clause11693 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11694 chi hbad
                ·
                  exact fin15Anchored_clause11695 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11696 chi hbad
                ·
                  exact fin15Anchored_clause11697 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11698 chi hbad
                ·
                  exact fin15Anchored_clause11699 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11700 chi hbad
                ·
                  exact fin15Anchored_clause11701 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11702 chi hbad
                ·
                  exact fin15Anchored_clause11703 chi hbad
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
                  exact fin15Anchored_clause11704 chi hbad
                ·
                  exact fin15Anchored_clause11705 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11706 chi hbad
                ·
                  exact fin15Anchored_clause11707 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11708 chi hbad
                ·
                  exact fin15Anchored_clause11709 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11710 chi hbad
                ·
                  exact fin15Anchored_clause11711 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11712 chi hbad
                ·
                  exact fin15Anchored_clause11713 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11714 chi hbad
                ·
                  exact fin15Anchored_clause11715 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11716 chi hbad
                ·
                  exact fin15Anchored_clause11717 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11718 chi hbad
                ·
                  exact fin15Anchored_clause11719 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11720 chi hbad
                ·
                  exact fin15Anchored_clause11721 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11722 chi hbad
                ·
                  exact fin15Anchored_clause11723 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11724 chi hbad
                ·
                  exact fin15Anchored_clause11725 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11726 chi hbad
                ·
                  exact fin15Anchored_clause11727 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11728 chi hbad
                ·
                  exact fin15Anchored_clause11729 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11730 chi hbad
                ·
                  exact fin15Anchored_clause11731 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11732 chi hbad
                ·
                  exact fin15Anchored_clause11733 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11734 chi hbad
                ·
                  exact fin15Anchored_clause11735 chi hbad
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
                exact fin15Anchored_clause11736 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11737 chi hbad
                ·
                  exact fin15Anchored_clause11738 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11739 chi hbad
                ·
                  exact fin15Anchored_clause11740 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11741 chi hbad
                ·
                  exact fin15Anchored_clause11742 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11743 chi hbad
                ·
                  exact fin15Anchored_clause11744 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11745 chi hbad
                ·
                  exact fin15Anchored_clause11746 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11747 chi hbad
                ·
                  exact fin15Anchored_clause11748 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11749 chi hbad
                ·
                  exact fin15Anchored_clause11750 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11751 chi hbad
                ·
                  exact fin15Anchored_clause11752 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11753 chi hbad
                ·
                  exact fin15Anchored_clause11754 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11755 chi hbad
                ·
                  exact fin15Anchored_clause11756 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11757 chi hbad
                ·
                  exact fin15Anchored_clause11758 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11759 chi hbad
                ·
                  exact fin15Anchored_clause11760 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11761 chi hbad
                ·
                  exact fin15Anchored_clause11762 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11763 chi hbad
                ·
                  exact fin15Anchored_clause11764 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11765 chi hbad
                ·
                  exact fin15Anchored_clause11766 chi hbad
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
                  exact fin15Anchored_clause11767 chi hbad
                ·
                  exact fin15Anchored_clause11768 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11769 chi hbad
                ·
                  exact fin15Anchored_clause11770 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11771 chi hbad
                ·
                  exact fin15Anchored_clause11772 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11773 chi hbad
                ·
                  exact fin15Anchored_clause11774 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11775 chi hbad
                ·
                  exact fin15Anchored_clause11776 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11777 chi hbad
                ·
                  exact fin15Anchored_clause11778 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11779 chi hbad
                ·
                  exact fin15Anchored_clause11780 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11781 chi hbad
                ·
                  exact fin15Anchored_clause11782 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11783 chi hbad
                ·
                  exact fin15Anchored_clause11784 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11785 chi hbad
                ·
                  exact fin15Anchored_clause11786 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11787 chi hbad
                ·
                  exact fin15Anchored_clause11788 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11789 chi hbad
                ·
                  exact fin15Anchored_clause11790 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11791 chi hbad
                ·
                  exact fin15Anchored_clause11792 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11793 chi hbad
                ·
                  exact fin15Anchored_clause11794 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11795 chi hbad
                ·
                  exact fin15Anchored_clause11796 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11797 chi hbad
                ·
                  exact fin15Anchored_clause11798 chi hbad
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
                exact fin15Anchored_clause11799 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11800 chi hbad
                ·
                  exact fin15Anchored_clause11801 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11802 chi hbad
                ·
                  exact fin15Anchored_clause11803 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11804 chi hbad
                ·
                  exact fin15Anchored_clause11805 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11806 chi hbad
                ·
                  exact fin15Anchored_clause11807 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11808 chi hbad
                ·
                  exact fin15Anchored_clause11809 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11810 chi hbad
                ·
                  exact fin15Anchored_clause11811 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11812 chi hbad
                ·
                  exact fin15Anchored_clause11813 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11814 chi hbad
                ·
                  exact fin15Anchored_clause11815 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11816 chi hbad
                ·
                  exact fin15Anchored_clause11817 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11818 chi hbad
                ·
                  exact fin15Anchored_clause11819 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11820 chi hbad
                ·
                  exact fin15Anchored_clause11821 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11822 chi hbad
                ·
                  exact fin15Anchored_clause11823 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11824 chi hbad
                ·
                  exact fin15Anchored_clause11825 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11826 chi hbad
                ·
                  exact fin15Anchored_clause11827 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11828 chi hbad
                ·
                  exact fin15Anchored_clause11829 chi hbad
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
                  exact fin15Anchored_clause11830 chi hbad
                ·
                  exact fin15Anchored_clause11831 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11832 chi hbad
                ·
                  exact fin15Anchored_clause11833 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11834 chi hbad
                ·
                  exact fin15Anchored_clause11835 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11836 chi hbad
                ·
                  exact fin15Anchored_clause11837 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11838 chi hbad
                ·
                  exact fin15Anchored_clause11839 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11840 chi hbad
                ·
                  exact fin15Anchored_clause11841 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11842 chi hbad
                ·
                  exact fin15Anchored_clause11843 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11844 chi hbad
                ·
                  exact fin15Anchored_clause11845 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11846 chi hbad
                ·
                  exact fin15Anchored_clause11847 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11848 chi hbad
                ·
                  exact fin15Anchored_clause11849 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11850 chi hbad
                ·
                  exact fin15Anchored_clause11851 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11852 chi hbad
                ·
                  exact fin15Anchored_clause11853 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11854 chi hbad
                ·
                  exact fin15Anchored_clause11855 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11856 chi hbad
                ·
                  exact fin15Anchored_clause11857 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11858 chi hbad
                ·
                  exact fin15Anchored_clause11859 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11860 chi hbad
                ·
                  exact fin15Anchored_clause11861 chi hbad

end ErdosSzekeres

end
