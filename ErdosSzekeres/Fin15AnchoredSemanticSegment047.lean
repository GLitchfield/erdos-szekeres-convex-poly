module

public import ErdosSzekeres.Fin15AnchoredClauseChunk092
public import ErdosSzekeres.Fin15AnchoredClauseChunk093
public import ErdosSzekeres.Fin15AnchoredClauseChunk094

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 047. -/

theorem fin15Anchored_rejectSemanticSegment047
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom1378 chi) ∨
      ((Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom1378 chi) ∨
      (Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom1378 chi))) ∨
      (((Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom1378 chi) ∨
      (¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom1379 chi)) ∨
      ((¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom1379 chi) ∨
      (¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom1379 chi)))) ∨
      ((((¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom1379 chi) ∨
      (¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom1379 chi)) ∨
      ((Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom1379 chi) ∨
      (Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom1379 chi))) ∨
      (((Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom1379 chi) ∨
      (Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom1379 chi)) ∨
      ((Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom1379 chi) ∨
      (¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom1380 chi))))) ∨
      (((((¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom1380 chi) ∨
      (¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom1380 chi)) ∨
      ((¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom1380 chi) ∨
      (¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom1380 chi))) ∨
      (((¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom1380 chi) ∨
      (Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom1380 chi)) ∨
      ((Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom1380 chi) ∨
      (Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom1380 chi)))) ∨
      ((((Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom1380 chi) ∨
      (Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom1380 chi)) ∨
      ((¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom1381 chi) ∨
      (¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom1381 chi))) ∨
      (((¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom1381 chi) ∨
      (¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom1381 chi)) ∨
      ((Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom1381 chi) ∨
      (Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom1381 chi)))))) ∨
      ((((((Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom1381 chi) ∨
      (Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom1381 chi)) ∨
      ((Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom1381 chi) ∨
      (Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom1382 chi))) ∨
      (((Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom1382 chi) ∨
      (Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom1382 chi)) ∨
      ((¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom1383 chi) ∨
      (¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom1383 chi)))) ∨
      ((((¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom1383 chi) ∨
      (¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom1383 chi)) ∨
      ((¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom1383 chi) ∨
      (Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom1383 chi))) ∨
      (((Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom1383 chi) ∨
      (Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom1383 chi)) ∨
      ((Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom1383 chi) ∨
      (Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom1383 chi))))) ∨
      (((((¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom1384 chi) ∨
      (¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom1384 chi)) ∨
      ((¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom1384 chi) ∨
      (¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom1384 chi))) ∨
      (((¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom1384 chi) ∨
      (Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom1384 chi)) ∨
      ((Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom1384 chi) ∨
      (Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom1384 chi)))) ∨
      ((((Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom1384 chi) ∨
      (Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom1384 chi)) ∨
      ((¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom1385 chi) ∨
      (¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom1385 chi))) ∨
      (((¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom1385 chi) ∨
      (¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom1385 chi)) ∨
      ((Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom1385 chi) ∨
      (Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom1385 chi))))))) ∨
      ((((((Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom1385 chi) ∨
      ((Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom1385 chi) ∨
      (Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom1385 chi))) ∨
      (((¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom1386 chi) ∨
      (¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom1386 chi)) ∨
      ((¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom1386 chi) ∨
      (¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom1386 chi)))) ∨
      ((((¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom1386 chi) ∨
      (¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom1386 chi)) ∨
      ((Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom1386 chi) ∨
      (Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom1386 chi))) ∨
      (((Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom1386 chi) ∨
      (Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom1386 chi)) ∨
      ((¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom1387 chi) ∨
      (¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom1387 chi))))) ∨
      (((((¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom1387 chi) ∨
      (¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom1387 chi)) ∨
      ((¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom1387 chi) ∨
      (Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom1387 chi))) ∨
      (((Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom1387 chi) ∨
      (Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom1387 chi)) ∨
      ((Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom1387 chi) ∨
      (¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom1389 chi)))) ∨
      ((((¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom1389 chi) ∨
      (¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom1389 chi)) ∨
      ((¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom1389 chi) ∨
      (Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom1389 chi))) ∨
      (((Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom1389 chi) ∨
      (Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom1389 chi)) ∨
      ((Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom1389 chi) ∨
      (Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom1389 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom1390 chi) ∨
      (¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom1390 chi)) ∨
      ((¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom1390 chi) ∨
      (¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom1390 chi))) ∨
      (((¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom1390 chi) ∨
      (¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom1390 chi)) ∨
      ((Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom1390 chi) ∨
      (Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom1390 chi)))) ∨
      ((((Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom1390 chi) ∨
      (Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom1390 chi)) ∨
      ((Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom1390 chi) ∨
      (¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom1391 chi))) ∨
      (((¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom1391 chi) ∨
      (¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom1391 chi)) ∨
      ((¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom1391 chi) ∨
      (Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom1391 chi))))) ∨
      (((((Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom1391 chi) ∨
      (Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom1391 chi)) ∨
      ((Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom1391 chi) ∨
      (¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom1392 chi))) ∨
      (((¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom1392 chi) ∨
      (¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom1392 chi)) ∨
      ((¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom1392 chi) ∨
      (Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom1392 chi)))) ∨
      ((((Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom1392 chi) ∨
      (Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom1392 chi)) ∨
      ((Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom1392 chi) ∨
      (Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom1392 chi))) ∨
      (((Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom1392 chi) ∨
      (Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom1392 chi)) ∨
      ((¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom1393 chi) ∨
      (¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom1393 chi)))))))) ∨
      (((((((¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom1393 chi) ∨
      ((¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom1393 chi) ∨
      (Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom1393 chi))) ∨
      (((Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom1393 chi) ∨
      (Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom1393 chi)) ∨
      ((Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom1393 chi) ∨
      (¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom1394 chi)))) ∨
      ((((¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom1394 chi) ∨
      (¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom1394 chi)) ∨
      ((¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom1394 chi) ∨
      (Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom1394 chi))) ∨
      (((Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom1394 chi) ∨
      (Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom1394 chi)) ∨
      ((Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom1394 chi) ∨
      (¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom1395 chi))))) ∨
      (((((¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom1395 chi) ∨
      (¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom1395 chi)) ∨
      ((¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom1395 chi) ∨
      (Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom1395 chi))) ∨
      (((Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom1395 chi) ∨
      (Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom1395 chi)) ∨
      ((Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom1395 chi) ∨
      (Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom1395 chi)))) ∨
      ((((¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom1396 chi) ∨
      (¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom1396 chi)) ∨
      ((¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom1396 chi) ∨
      (¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom1396 chi))) ∨
      (((¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom1396 chi) ∨
      (Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom1396 chi)) ∨
      ((Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom1396 chi) ∨
      (Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom1396 chi)))))) ∨
      ((((((Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom1396 chi) ∨
      (Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom1396 chi)) ∨
      ((Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom1396 chi) ∨
      (¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom1397 chi))) ∨
      (((¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom1397 chi) ∨
      (¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom1397 chi)) ∨
      ((¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom1397 chi) ∨
      (¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom1397 chi)))) ∨
      ((((Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom1397 chi) ∨
      (Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom1397 chi)) ∨
      ((Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom1397 chi) ∨
      (¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom1398 chi))) ∨
      (((¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom1398 chi) ∨
      (¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom1398 chi)) ∨
      ((¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom1398 chi) ∨
      (Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom1398 chi))))) ∨
      (((((Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom1398 chi) ∨
      (Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom1398 chi)) ∨
      ((Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom1398 chi) ∨
      (¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom1399 chi))) ∨
      (((¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom1399 chi) ∨
      (¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom1399 chi)) ∨
      ((¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom1399 chi) ∨
      (Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom1399 chi)))) ∨
      ((((Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom1399 chi) ∨
      (Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom1399 chi)) ∨
      ((Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom1399 chi) ∨
      (Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom1399 chi))) ∨
      (((¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom1400 chi) ∨
      (¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom1400 chi)) ∨
      ((¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom1400 chi) ∨
      (¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom1400 chi))))))) ∨
      (((((((Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom1400 chi) ∨
      (Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom1400 chi)) ∨
      ((Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom1400 chi) ∨
      (Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom1400 chi))) ∨
      (((Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom1400 chi) ∨
      (¬Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom1401 chi)) ∨
      ((¬Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom1401 chi) ∨
      (¬Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom1401 chi)))) ∨
      ((((¬Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom1401 chi) ∨
      (¬Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom1401 chi)) ∨
      ((Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom1401 chi) ∨
      (Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom1401 chi))) ∨
      (((¬Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom1402 chi) ∨
      (¬Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom1402 chi)) ∨
      ((¬Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0287 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      ¬Fin15AnchoredAtom1403 chi) ∨
      (¬Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0287 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom1403 chi))))) ∨
      (((((¬Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0287 chi ∧
      Fin15AnchoredAtom0368 chi ∧
      ¬Fin15AnchoredAtom1403 chi) ∨
      (¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom1404 chi)) ∨
      ((¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom1404 chi) ∨
      (¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom1404 chi))) ∨
      (((¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom1404 chi) ∨
      (Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom1404 chi)) ∨
      ((Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom1404 chi) ∨
      (Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom1404 chi)))) ∨
      ((((Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom1404 chi) ∨
      (¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom1405 chi)) ∨
      ((¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom1405 chi) ∨
      (¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom1405 chi))) ∨
      (((¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom1405 chi) ∨
      (Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom1405 chi)) ∨
      ((Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom1405 chi) ∨
      (Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom1405 chi)))))) ∨
      ((((((Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom1405 chi) ∨
      (Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom1405 chi)) ∨
      ((Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom1405 chi) ∨
      (¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom1406 chi))) ∨
      (((¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom1406 chi) ∨
      (¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom1406 chi)) ∨
      ((¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom1406 chi) ∨
      (Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom1406 chi)))) ∨
      ((((Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom1406 chi) ∨
      (Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom1406 chi)) ∨
      ((Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom1406 chi) ∨
      (Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom1406 chi))) ∨
      (((¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom1407 chi) ∨
      (¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom1407 chi)) ∨
      ((¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom1407 chi) ∨
      (¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom1407 chi))))) ∨
      (((((Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom1407 chi) ∨
      (Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom1407 chi)) ∨
      ((Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom1407 chi) ∨
      (¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom1408 chi))) ∨
      (((¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom1408 chi) ∨
      (¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom1408 chi)) ∨
      ((¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom1408 chi) ∨
      (Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom1408 chi)))) ∨
      ((((Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom1408 chi) ∨
      (Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom1408 chi)) ∨
      ((Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom1408 chi) ∨
      (Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom1408 chi))) ∨
      (((Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom1408 chi) ∨
      (¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom1409 chi)) ∨
      ((¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom1409 chi) ∨
      (¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom1409 chi)))))))))) := by
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
                exact fin15Anchored_clause11862 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11863 chi hbad
                ·
                  exact fin15Anchored_clause11864 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11865 chi hbad
                ·
                  exact fin15Anchored_clause11866 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11867 chi hbad
                ·
                  exact fin15Anchored_clause11868 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11869 chi hbad
                ·
                  exact fin15Anchored_clause11870 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11871 chi hbad
                ·
                  exact fin15Anchored_clause11872 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11873 chi hbad
                ·
                  exact fin15Anchored_clause11874 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11875 chi hbad
                ·
                  exact fin15Anchored_clause11876 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11877 chi hbad
                ·
                  exact fin15Anchored_clause11878 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11879 chi hbad
                ·
                  exact fin15Anchored_clause11880 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11881 chi hbad
                ·
                  exact fin15Anchored_clause11882 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11883 chi hbad
                ·
                  exact fin15Anchored_clause11884 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11885 chi hbad
                ·
                  exact fin15Anchored_clause11886 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11887 chi hbad
                ·
                  exact fin15Anchored_clause11888 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11889 chi hbad
                ·
                  exact fin15Anchored_clause11890 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11891 chi hbad
                ·
                  exact fin15Anchored_clause11892 chi hbad
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
                  exact fin15Anchored_clause11893 chi hbad
                ·
                  exact fin15Anchored_clause11894 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11895 chi hbad
                ·
                  exact fin15Anchored_clause11896 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11897 chi hbad
                ·
                  exact fin15Anchored_clause11898 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11899 chi hbad
                ·
                  exact fin15Anchored_clause11900 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11901 chi hbad
                ·
                  exact fin15Anchored_clause11902 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11903 chi hbad
                ·
                  exact fin15Anchored_clause11904 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11905 chi hbad
                ·
                  exact fin15Anchored_clause11906 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11907 chi hbad
                ·
                  exact fin15Anchored_clause11908 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11909 chi hbad
                ·
                  exact fin15Anchored_clause11910 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11911 chi hbad
                ·
                  exact fin15Anchored_clause11912 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11913 chi hbad
                ·
                  exact fin15Anchored_clause11914 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11915 chi hbad
                ·
                  exact fin15Anchored_clause11916 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11917 chi hbad
                ·
                  exact fin15Anchored_clause11918 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11919 chi hbad
                ·
                  exact fin15Anchored_clause11920 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11921 chi hbad
                ·
                  exact fin15Anchored_clause11922 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11923 chi hbad
                ·
                  exact fin15Anchored_clause11924 chi hbad
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
                exact fin15Anchored_clause11925 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11926 chi hbad
                ·
                  exact fin15Anchored_clause11927 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11928 chi hbad
                ·
                  exact fin15Anchored_clause11929 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11930 chi hbad
                ·
                  exact fin15Anchored_clause11931 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11932 chi hbad
                ·
                  exact fin15Anchored_clause11933 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11934 chi hbad
                ·
                  exact fin15Anchored_clause11935 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11936 chi hbad
                ·
                  exact fin15Anchored_clause11937 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11938 chi hbad
                ·
                  exact fin15Anchored_clause11939 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11940 chi hbad
                ·
                  exact fin15Anchored_clause11941 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11942 chi hbad
                ·
                  exact fin15Anchored_clause11943 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11944 chi hbad
                ·
                  exact fin15Anchored_clause11945 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11946 chi hbad
                ·
                  exact fin15Anchored_clause11947 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11948 chi hbad
                ·
                  exact fin15Anchored_clause11949 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11950 chi hbad
                ·
                  exact fin15Anchored_clause11951 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11952 chi hbad
                ·
                  exact fin15Anchored_clause11953 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11954 chi hbad
                ·
                  exact fin15Anchored_clause11955 chi hbad
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
                  exact fin15Anchored_clause11956 chi hbad
                ·
                  exact fin15Anchored_clause11957 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11958 chi hbad
                ·
                  exact fin15Anchored_clause11959 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11960 chi hbad
                ·
                  exact fin15Anchored_clause11961 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11962 chi hbad
                ·
                  exact fin15Anchored_clause11963 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11964 chi hbad
                ·
                  exact fin15Anchored_clause11965 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11966 chi hbad
                ·
                  exact fin15Anchored_clause11967 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11968 chi hbad
                ·
                  exact fin15Anchored_clause11969 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11970 chi hbad
                ·
                  exact fin15Anchored_clause11971 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11972 chi hbad
                ·
                  exact fin15Anchored_clause11973 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11974 chi hbad
                ·
                  exact fin15Anchored_clause11975 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11976 chi hbad
                ·
                  exact fin15Anchored_clause11977 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11978 chi hbad
                ·
                  exact fin15Anchored_clause11979 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11980 chi hbad
                ·
                  exact fin15Anchored_clause11981 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11982 chi hbad
                ·
                  exact fin15Anchored_clause11983 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11984 chi hbad
                ·
                  exact fin15Anchored_clause11985 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11986 chi hbad
                ·
                  exact fin15Anchored_clause11987 chi hbad
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
                exact fin15Anchored_clause11988 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11989 chi hbad
                ·
                  exact fin15Anchored_clause11990 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11991 chi hbad
                ·
                  exact fin15Anchored_clause11992 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11993 chi hbad
                ·
                  exact fin15Anchored_clause11994 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11995 chi hbad
                ·
                  exact fin15Anchored_clause11996 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11997 chi hbad
                ·
                  exact fin15Anchored_clause11998 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11999 chi hbad
                ·
                  exact fin15Anchored_clause12000 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12001 chi hbad
                ·
                  exact fin15Anchored_clause12002 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12003 chi hbad
                ·
                  exact fin15Anchored_clause12004 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12005 chi hbad
                ·
                  exact fin15Anchored_clause12006 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12007 chi hbad
                ·
                  exact fin15Anchored_clause12008 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12009 chi hbad
                ·
                  exact fin15Anchored_clause12010 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12011 chi hbad
                ·
                  exact fin15Anchored_clause12012 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12013 chi hbad
                ·
                  exact fin15Anchored_clause12014 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12015 chi hbad
                ·
                  exact fin15Anchored_clause12016 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12017 chi hbad
                ·
                  exact fin15Anchored_clause12018 chi hbad
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
                  exact fin15Anchored_clause12019 chi hbad
                ·
                  exact fin15Anchored_clause12020 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12021 chi hbad
                ·
                  exact fin15Anchored_clause12022 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12023 chi hbad
                ·
                  exact fin15Anchored_clause12024 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12025 chi hbad
                ·
                  exact fin15Anchored_clause12026 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12027 chi hbad
                ·
                  exact fin15Anchored_clause12028 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12029 chi hbad
                ·
                  exact fin15Anchored_clause12030 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12031 chi hbad
                ·
                  exact fin15Anchored_clause12032 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12033 chi hbad
                ·
                  exact fin15Anchored_clause12034 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12035 chi hbad
                ·
                  exact fin15Anchored_clause12036 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12037 chi hbad
                ·
                  exact fin15Anchored_clause12038 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12039 chi hbad
                ·
                  exact fin15Anchored_clause12040 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12041 chi hbad
                ·
                  exact fin15Anchored_clause12042 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12043 chi hbad
                ·
                  exact fin15Anchored_clause12044 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12045 chi hbad
                ·
                  exact fin15Anchored_clause12046 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12047 chi hbad
                ·
                  exact fin15Anchored_clause12048 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12049 chi hbad
                ·
                  exact fin15Anchored_clause12050 chi hbad
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
                  exact fin15Anchored_clause12051 chi hbad
                ·
                  exact fin15Anchored_clause12052 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12053 chi hbad
                ·
                  exact fin15Anchored_clause12054 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12055 chi hbad
                ·
                  exact fin15Anchored_clause12056 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12057 chi hbad
                ·
                  exact fin15Anchored_clause12058 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12059 chi hbad
                ·
                  exact fin15Anchored_clause12060 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12061 chi hbad
                ·
                  exact fin15Anchored_clause12062 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12063 chi hbad
                ·
                  exact fin15Anchored_clause12064 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12065 chi hbad
                ·
                  exact fin15Anchored_clause12066 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12067 chi hbad
                ·
                  exact fin15Anchored_clause12068 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12069 chi hbad
                ·
                  exact fin15Anchored_clause12070 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12071 chi hbad
                ·
                  exact fin15Anchored_clause12072 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12073 chi hbad
                ·
                  exact fin15Anchored_clause12074 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12075 chi hbad
                ·
                  exact fin15Anchored_clause12076 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12077 chi hbad
                ·
                  exact fin15Anchored_clause12078 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12079 chi hbad
                ·
                  exact fin15Anchored_clause12080 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12081 chi hbad
                ·
                  exact fin15Anchored_clause12082 chi hbad
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
                  exact fin15Anchored_clause12083 chi hbad
                ·
                  exact fin15Anchored_clause12084 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12085 chi hbad
                ·
                  exact fin15Anchored_clause12086 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12087 chi hbad
                ·
                  exact fin15Anchored_clause12088 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12089 chi hbad
                ·
                  exact fin15Anchored_clause12090 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12091 chi hbad
                ·
                  exact fin15Anchored_clause12092 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12093 chi hbad
                ·
                  exact fin15Anchored_clause12094 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12095 chi hbad
                ·
                  exact fin15Anchored_clause12096 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12097 chi hbad
                ·
                  exact fin15Anchored_clause12098 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12099 chi hbad
                ·
                  exact fin15Anchored_clause12100 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12101 chi hbad
                ·
                  exact fin15Anchored_clause12102 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12103 chi hbad
                ·
                  exact fin15Anchored_clause12104 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12105 chi hbad
                ·
                  exact fin15Anchored_clause12106 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12107 chi hbad
                ·
                  exact fin15Anchored_clause12108 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12109 chi hbad
                ·
                  exact fin15Anchored_clause12110 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12111 chi hbad
                ·
                  exact fin15Anchored_clause12112 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12113 chi hbad
                ·
                  exact fin15Anchored_clause12114 chi hbad

end ErdosSzekeres

end
