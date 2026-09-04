module

public import ErdosSzekeres.Fin15AnchoredClauseChunk094
public import ErdosSzekeres.Fin15AnchoredClauseChunk095
public import ErdosSzekeres.Fin15AnchoredClauseChunk096

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 048. -/

theorem fin15Anchored_rejectSemanticSegment048
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom1409 chi) ∨
      ((Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom1409 chi) ∨
      (Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom1409 chi))) ∨
      (((Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom1409 chi) ∨
      (Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom1409 chi)) ∨
      ((¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom1410 chi) ∨
      (Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom1410 chi)))) ∨
      ((((¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom1411 chi) ∨
      (¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom1411 chi)) ∨
      ((¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom1411 chi) ∨
      (¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom1411 chi))) ∨
      (((¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom1411 chi) ∨
      (Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom1411 chi)) ∨
      ((Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom1411 chi) ∨
      (Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom1411 chi))))) ∨
      (((((Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom1411 chi) ∨
      (Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom1411 chi)) ∨
      ((¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom1412 chi) ∨
      (¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom1412 chi))) ∨
      (((¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom1412 chi) ∨
      (¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom1412 chi)) ∨
      ((Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom1412 chi) ∨
      (Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom1412 chi)))) ∨
      ((((Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom1412 chi) ∨
      (Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom1412 chi)) ∨
      ((Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom1412 chi) ∨
      (¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom1413 chi))) ∨
      (((¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom1413 chi) ∨
      (¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom1413 chi)) ∨
      ((¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom1413 chi) ∨
      (Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom1413 chi)))))) ∨
      ((((((Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom1413 chi) ∨
      (Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom1413 chi)) ∨
      ((Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom1413 chi) ∨
      (Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom1413 chi))) ∨
      (((¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom1414 chi) ∨
      (¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom1414 chi)) ∨
      ((¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom1414 chi) ∨
      (¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom1414 chi)))) ∨
      ((((¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom1414 chi) ∨
      (Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom1414 chi)) ∨
      ((Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom1414 chi) ∨
      (Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom1414 chi))) ∨
      (((Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom1414 chi) ∨
      (Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom1414 chi)) ∨
      ((Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom1414 chi) ∨
      (¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom1415 chi))))) ∨
      (((((¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom1415 chi) ∨
      (¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom1415 chi)) ∨
      ((¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom1415 chi) ∨
      (Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom1415 chi))) ∨
      (((Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom1415 chi) ∨
      (Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom1415 chi)) ∨
      ((Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom1415 chi) ∨
      (¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom1417 chi)))) ∨
      ((((¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom1417 chi) ∨
      (¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom1417 chi)) ∨
      ((¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom1417 chi) ∨
      (Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom1417 chi))) ∨
      (((Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom1417 chi) ∨
      (Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom1417 chi)) ∨
      ((Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom1417 chi) ∨
      (¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom1418 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom1418 chi) ∨
      ((¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom1418 chi) ∨
      (¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom1418 chi))) ∨
      (((Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom1418 chi) ∨
      (Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom1418 chi)) ∨
      ((Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom1418 chi) ∨
      (Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom1418 chi)))) ∨
      ((((¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom1419 chi) ∨
      (¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom1419 chi)) ∨
      ((¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom1419 chi) ∨
      (¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom1419 chi))) ∨
      (((¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom1419 chi) ∨
      (Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom1419 chi)) ∨
      ((Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom1419 chi) ∨
      (Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom1419 chi))))) ∨
      (((((Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom1419 chi) ∨
      (¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom1420 chi)) ∨
      ((¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom1420 chi) ∨
      (¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom1420 chi))) ∨
      (((¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom1420 chi) ∨
      (¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom1420 chi)) ∨
      ((Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom1420 chi) ∨
      (Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom1420 chi)))) ∨
      ((((Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom1420 chi) ∨
      (Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom1420 chi)) ∨
      ((¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom1421 chi) ∨
      (¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom1421 chi))) ∨
      (((Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom1421 chi) ∨
      (Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom1421 chi)) ∨
      ((¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom1422 chi) ∨
      (¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom1422 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom1422 chi) ∨
      (¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom1422 chi)) ∨
      ((Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom1422 chi) ∨
      (Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom1422 chi))) ∨
      (((Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom1422 chi) ∨
      (Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom1422 chi)) ∨
      ((¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom1423 chi) ∨
      (¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1423 chi)))) ∨
      ((((¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1423 chi) ∨
      (¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom1423 chi)) ∨
      ((¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1423 chi) ∨
      (Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1423 chi))) ∨
      (((Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1423 chi) ∨
      (Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom1423 chi)) ∨
      ((Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1423 chi) ∨
      (Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom1423 chi))))) ∨
      (((((¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom1424 chi) ∨
      (¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom1424 chi)) ∨
      ((¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom1424 chi) ∨
      (¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom1424 chi))) ∨
      (((¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom1424 chi) ∨
      (Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom1424 chi)) ∨
      ((Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom1424 chi) ∨
      (Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom1424 chi)))) ∨
      ((((Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom1424 chi) ∨
      (Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom1424 chi)) ∨
      ((¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom1425 chi) ∨
      (¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom1425 chi))) ∨
      (((¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom1425 chi) ∨
      (¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom1425 chi)) ∨
      ((Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom1425 chi) ∨
      (Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom1425 chi)))))))) ∨
      (((((((¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom1426 chi) ∨
      ((¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom1426 chi) ∨
      (¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom1426 chi))) ∨
      (((¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom1426 chi) ∨
      (Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom1426 chi)) ∨
      ((Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom1426 chi) ∨
      (Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom1426 chi)))) ∨
      ((((Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom1426 chi) ∨
      (Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom1426 chi)) ∨
      ((Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom1426 chi) ∨
      (¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom1427 chi))) ∨
      (((¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom1427 chi) ∨
      (¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom1427 chi)) ∨
      ((¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom1427 chi) ∨
      (¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom1427 chi))))) ∨
      (((((Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom1427 chi) ∨
      (Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom1427 chi)) ∨
      ((Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom1427 chi) ∨
      (Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom1427 chi))) ∨
      (((Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom1427 chi) ∨
      (¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom1428 chi)) ∨
      ((¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom1428 chi) ∨
      (¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom1428 chi)))) ∨
      ((((¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom1428 chi) ∨
      (¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom1428 chi)) ∨
      ((Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom1428 chi) ∨
      (Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom1428 chi))) ∨
      (((Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom1428 chi) ∨
      (Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom1428 chi)) ∨
      ((Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom1428 chi) ∨
      (Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom1428 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom1429 chi) ∨
      (¬Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom1429 chi)) ∨
      ((Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom1429 chi) ∨
      (Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom1429 chi))) ∨
      (((¬Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom1430 chi) ∨
      (¬Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0395 chi ∧
      Fin15AnchoredAtom1430 chi)) ∨
      ((¬Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom1430 chi) ∨
      (¬Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0395 chi ∧
      Fin15AnchoredAtom1430 chi)))) ∨
      ((((¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom1432 chi) ∨
      (¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1432 chi)) ∨
      ((¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom1432 chi) ∨
      (¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1432 chi))) ∨
      (((¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1432 chi) ∨
      (Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1432 chi)) ∨
      ((Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1432 chi) ∨
      (Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom1432 chi))))) ∨
      (((((Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1432 chi) ∨
      (Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom1432 chi)) ∨
      ((¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom1433 chi) ∨
      (¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom1433 chi))) ∨
      (((¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom1433 chi) ∨
      (¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom1433 chi)) ∨
      ((¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom1433 chi) ∨
      (Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom1433 chi)))) ∨
      ((((Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom1433 chi) ∨
      (Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom1433 chi)) ∨
      ((Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom1433 chi) ∨
      (Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom1433 chi))) ∨
      (((Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom1433 chi) ∨
      (¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom1434 chi)) ∨
      ((¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom1434 chi) ∨
      (¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom1434 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom1434 chi) ∨
      ((¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom1434 chi) ∨
      (Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom1434 chi))) ∨
      (((Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom1434 chi) ∨
      (Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom1434 chi)) ∨
      ((Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom1434 chi) ∨
      (Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom1434 chi)))) ∨
      ((((Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom1434 chi) ∨
      (¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom1435 chi)) ∨
      ((¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom1435 chi) ∨
      (¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom1435 chi))) ∨
      (((¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom1435 chi) ∨
      (Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom1435 chi)) ∨
      ((Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom1435 chi) ∨
      (Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom1435 chi))))) ∨
      (((((Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom1435 chi) ∨
      (Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom1435 chi)) ∨
      ((Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom1435 chi) ∨
      (¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom1436 chi))) ∨
      (((¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom1436 chi) ∨
      (¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom1436 chi)) ∨
      ((¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom1436 chi) ∨
      (Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom1436 chi)))) ∨
      ((((Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom1436 chi) ∨
      (Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom1436 chi)) ∨
      ((Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom1436 chi) ∨
      (Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom1436 chi))) ∨
      (((¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom1438 chi) ∨
      (¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom1438 chi)) ∨
      ((¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom1438 chi) ∨
      (¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom1438 chi)))))) ∨
      ((((((Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom1438 chi) ∨
      (Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom1438 chi)) ∨
      ((Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom1438 chi) ∨
      (Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom1438 chi))) ∨
      (((Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom1438 chi) ∨
      (¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom1439 chi)) ∨
      ((¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom1439 chi) ∨
      (¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom1439 chi)))) ∨
      ((((¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom1439 chi) ∨
      (Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom1439 chi)) ∨
      ((Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom1439 chi) ∨
      (Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom1439 chi))) ∨
      (((Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom1439 chi) ∨
      (¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom1440 chi)) ∨
      ((¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom1440 chi) ∨
      (¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom1440 chi))))) ∨
      (((((¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom1440 chi) ∨
      (¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom1440 chi)) ∨
      ((¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom1440 chi) ∨
      (Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom1440 chi))) ∨
      (((Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom1440 chi) ∨
      (Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom1440 chi)) ∨
      ((Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom1440 chi) ∨
      (Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom1440 chi)))) ∨
      ((((¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom1441 chi) ∨
      (¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1441 chi)) ∨
      ((¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom1441 chi) ∨
      (¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1441 chi))) ∨
      (((¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1441 chi) ∨
      (Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1441 chi)) ∨
      ((Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1441 chi) ∨
      (Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom1441 chi)))))))))) := by
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
                exact fin15Anchored_clause12115 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12116 chi hbad
                ·
                  exact fin15Anchored_clause12117 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12118 chi hbad
                ·
                  exact fin15Anchored_clause12119 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12120 chi hbad
                ·
                  exact fin15Anchored_clause12121 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12122 chi hbad
                ·
                  exact fin15Anchored_clause12123 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12124 chi hbad
                ·
                  exact fin15Anchored_clause12125 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12126 chi hbad
                ·
                  exact fin15Anchored_clause12127 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12128 chi hbad
                ·
                  exact fin15Anchored_clause12129 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12130 chi hbad
                ·
                  exact fin15Anchored_clause12131 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12132 chi hbad
                ·
                  exact fin15Anchored_clause12133 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12134 chi hbad
                ·
                  exact fin15Anchored_clause12135 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12136 chi hbad
                ·
                  exact fin15Anchored_clause12137 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12138 chi hbad
                ·
                  exact fin15Anchored_clause12139 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12140 chi hbad
                ·
                  exact fin15Anchored_clause12141 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12142 chi hbad
                ·
                  exact fin15Anchored_clause12143 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12144 chi hbad
                ·
                  exact fin15Anchored_clause12145 chi hbad
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
                  exact fin15Anchored_clause12146 chi hbad
                ·
                  exact fin15Anchored_clause12147 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12148 chi hbad
                ·
                  exact fin15Anchored_clause12149 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12150 chi hbad
                ·
                  exact fin15Anchored_clause12151 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12152 chi hbad
                ·
                  exact fin15Anchored_clause12153 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12154 chi hbad
                ·
                  exact fin15Anchored_clause12155 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12156 chi hbad
                ·
                  exact fin15Anchored_clause12157 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12158 chi hbad
                ·
                  exact fin15Anchored_clause12159 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12160 chi hbad
                ·
                  exact fin15Anchored_clause12161 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12162 chi hbad
                ·
                  exact fin15Anchored_clause12163 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12164 chi hbad
                ·
                  exact fin15Anchored_clause12165 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12166 chi hbad
                ·
                  exact fin15Anchored_clause12167 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12168 chi hbad
                ·
                  exact fin15Anchored_clause12169 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12170 chi hbad
                ·
                  exact fin15Anchored_clause12171 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12172 chi hbad
                ·
                  exact fin15Anchored_clause12173 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12174 chi hbad
                ·
                  exact fin15Anchored_clause12175 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12176 chi hbad
                ·
                  exact fin15Anchored_clause12177 chi hbad
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
                exact fin15Anchored_clause12178 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12179 chi hbad
                ·
                  exact fin15Anchored_clause12180 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12181 chi hbad
                ·
                  exact fin15Anchored_clause12182 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12183 chi hbad
                ·
                  exact fin15Anchored_clause12184 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12185 chi hbad
                ·
                  exact fin15Anchored_clause12186 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12187 chi hbad
                ·
                  exact fin15Anchored_clause12188 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12189 chi hbad
                ·
                  exact fin15Anchored_clause12190 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12191 chi hbad
                ·
                  exact fin15Anchored_clause12192 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12193 chi hbad
                ·
                  exact fin15Anchored_clause12194 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12195 chi hbad
                ·
                  exact fin15Anchored_clause12196 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12197 chi hbad
                ·
                  exact fin15Anchored_clause12198 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12199 chi hbad
                ·
                  exact fin15Anchored_clause12200 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12201 chi hbad
                ·
                  exact fin15Anchored_clause12202 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12203 chi hbad
                ·
                  exact fin15Anchored_clause12204 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12205 chi hbad
                ·
                  exact fin15Anchored_clause12206 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12207 chi hbad
                ·
                  exact fin15Anchored_clause12208 chi hbad
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
                  exact fin15Anchored_clause12209 chi hbad
                ·
                  exact fin15Anchored_clause12210 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12211 chi hbad
                ·
                  exact fin15Anchored_clause12212 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12213 chi hbad
                ·
                  exact fin15Anchored_clause12214 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12215 chi hbad
                ·
                  exact fin15Anchored_clause12216 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12217 chi hbad
                ·
                  exact fin15Anchored_clause12218 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12219 chi hbad
                ·
                  exact fin15Anchored_clause12220 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12221 chi hbad
                ·
                  exact fin15Anchored_clause12222 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12223 chi hbad
                ·
                  exact fin15Anchored_clause12224 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12225 chi hbad
                ·
                  exact fin15Anchored_clause12226 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12227 chi hbad
                ·
                  exact fin15Anchored_clause12228 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12229 chi hbad
                ·
                  exact fin15Anchored_clause12230 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12231 chi hbad
                ·
                  exact fin15Anchored_clause12232 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12233 chi hbad
                ·
                  exact fin15Anchored_clause12234 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12235 chi hbad
                ·
                  exact fin15Anchored_clause12236 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12237 chi hbad
                ·
                  exact fin15Anchored_clause12238 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12239 chi hbad
                ·
                  exact fin15Anchored_clause12240 chi hbad
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
                exact fin15Anchored_clause12241 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12242 chi hbad
                ·
                  exact fin15Anchored_clause12243 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12244 chi hbad
                ·
                  exact fin15Anchored_clause12245 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12246 chi hbad
                ·
                  exact fin15Anchored_clause12247 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12248 chi hbad
                ·
                  exact fin15Anchored_clause12249 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12250 chi hbad
                ·
                  exact fin15Anchored_clause12251 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12252 chi hbad
                ·
                  exact fin15Anchored_clause12253 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12254 chi hbad
                ·
                  exact fin15Anchored_clause12255 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12256 chi hbad
                ·
                  exact fin15Anchored_clause12257 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12258 chi hbad
                ·
                  exact fin15Anchored_clause12259 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12260 chi hbad
                ·
                  exact fin15Anchored_clause12261 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12262 chi hbad
                ·
                  exact fin15Anchored_clause12263 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12264 chi hbad
                ·
                  exact fin15Anchored_clause12265 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12266 chi hbad
                ·
                  exact fin15Anchored_clause12267 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12268 chi hbad
                ·
                  exact fin15Anchored_clause12269 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12270 chi hbad
                ·
                  exact fin15Anchored_clause12271 chi hbad
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
                  exact fin15Anchored_clause12272 chi hbad
                ·
                  exact fin15Anchored_clause12273 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12274 chi hbad
                ·
                  exact fin15Anchored_clause12275 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12276 chi hbad
                ·
                  exact fin15Anchored_clause12277 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12278 chi hbad
                ·
                  exact fin15Anchored_clause12279 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12280 chi hbad
                ·
                  exact fin15Anchored_clause12281 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12282 chi hbad
                ·
                  exact fin15Anchored_clause12283 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12284 chi hbad
                ·
                  exact fin15Anchored_clause12285 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12286 chi hbad
                ·
                  exact fin15Anchored_clause12287 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12288 chi hbad
                ·
                  exact fin15Anchored_clause12289 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12290 chi hbad
                ·
                  exact fin15Anchored_clause12291 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12292 chi hbad
                ·
                  exact fin15Anchored_clause12293 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12294 chi hbad
                ·
                  exact fin15Anchored_clause12295 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12296 chi hbad
                ·
                  exact fin15Anchored_clause12297 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12298 chi hbad
                ·
                  exact fin15Anchored_clause12299 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12300 chi hbad
                ·
                  exact fin15Anchored_clause12301 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12302 chi hbad
                ·
                  exact fin15Anchored_clause12303 chi hbad
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
                exact fin15Anchored_clause12304 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12305 chi hbad
                ·
                  exact fin15Anchored_clause12306 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12307 chi hbad
                ·
                  exact fin15Anchored_clause12308 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12309 chi hbad
                ·
                  exact fin15Anchored_clause12310 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12311 chi hbad
                ·
                  exact fin15Anchored_clause12312 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12313 chi hbad
                ·
                  exact fin15Anchored_clause12314 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12315 chi hbad
                ·
                  exact fin15Anchored_clause12316 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12317 chi hbad
                ·
                  exact fin15Anchored_clause12318 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12319 chi hbad
                ·
                  exact fin15Anchored_clause12320 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12321 chi hbad
                ·
                  exact fin15Anchored_clause12322 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12323 chi hbad
                ·
                  exact fin15Anchored_clause12324 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12325 chi hbad
                ·
                  exact fin15Anchored_clause12326 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12327 chi hbad
                ·
                  exact fin15Anchored_clause12328 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12329 chi hbad
                ·
                  exact fin15Anchored_clause12330 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12331 chi hbad
                ·
                  exact fin15Anchored_clause12332 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12333 chi hbad
                ·
                  exact fin15Anchored_clause12334 chi hbad
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
                  exact fin15Anchored_clause12335 chi hbad
                ·
                  exact fin15Anchored_clause12336 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12337 chi hbad
                ·
                  exact fin15Anchored_clause12338 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12339 chi hbad
                ·
                  exact fin15Anchored_clause12340 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12341 chi hbad
                ·
                  exact fin15Anchored_clause12342 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12343 chi hbad
                ·
                  exact fin15Anchored_clause12344 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12345 chi hbad
                ·
                  exact fin15Anchored_clause12346 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12347 chi hbad
                ·
                  exact fin15Anchored_clause12348 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12349 chi hbad
                ·
                  exact fin15Anchored_clause12350 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12351 chi hbad
                ·
                  exact fin15Anchored_clause12352 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12353 chi hbad
                ·
                  exact fin15Anchored_clause12354 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12355 chi hbad
                ·
                  exact fin15Anchored_clause12356 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12357 chi hbad
                ·
                  exact fin15Anchored_clause12358 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12359 chi hbad
                ·
                  exact fin15Anchored_clause12360 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12361 chi hbad
                ·
                  exact fin15Anchored_clause12362 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12363 chi hbad
                ·
                  exact fin15Anchored_clause12364 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12365 chi hbad
                ·
                  exact fin15Anchored_clause12366 chi hbad

end ErdosSzekeres

end
