module

public import ErdosSzekeres.Fin15AnchoredClauseChunk096
public import ErdosSzekeres.Fin15AnchoredClauseChunk097
public import ErdosSzekeres.Fin15AnchoredClauseChunk098

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 049. -/

theorem fin15Anchored_rejectSemanticSegment049
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1441 chi) ∨
      ((Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom1441 chi) ∨
      (¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom1442 chi))) ∨
      (((¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom1442 chi) ∨
      (¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom1442 chi)) ∨
      ((Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom1442 chi) ∨
      (Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom1442 chi)))) ∨
      ((((¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom1443 chi) ∨
      (¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1443 chi)) ∨
      ((¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom1443 chi) ∨
      (¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1443 chi))) ∨
      (((¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1443 chi) ∨
      (Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1443 chi)) ∨
      ((Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1443 chi) ∨
      (Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom1443 chi))))) ∨
      (((((Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1443 chi) ∨
      (Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom1443 chi)) ∨
      ((¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom1444 chi) ∨
      (¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1444 chi))) ∨
      (((¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom1444 chi) ∨
      (¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1444 chi)) ∨
      ((¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1444 chi) ∨
      (Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1444 chi)))) ∨
      ((((Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1444 chi) ∨
      (Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom1444 chi)) ∨
      ((Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1444 chi) ∨
      (Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1444 chi))) ∨
      (((Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom1444 chi) ∨
      (¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom1445 chi)) ∨
      ((¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1445 chi) ∨
      (¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom1445 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1445 chi) ∨
      (¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1445 chi)) ∨
      ((Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1445 chi) ∨
      (Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom1445 chi))) ∨
      (((Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1445 chi) ∨
      (Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom1445 chi)) ∨
      ((¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom1446 chi) ∨
      (¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom1446 chi)))) ∨
      ((((¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom1446 chi) ∨
      (¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom1446 chi)) ∨
      ((¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom1446 chi) ∨
      (Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom1446 chi))) ∨
      (((Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom1446 chi) ∨
      (Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom1446 chi)) ∨
      ((Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom1446 chi) ∨
      (¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom1447 chi))))) ∨
      (((((¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1447 chi) ∨
      (¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom1447 chi)) ∨
      ((¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1447 chi) ∨
      (¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1447 chi))) ∨
      (((Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1447 chi) ∨
      (Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1447 chi)) ∨
      ((Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom1447 chi) ∨
      (Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1447 chi)))) ∨
      ((((Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1447 chi) ∨
      (Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom1447 chi)) ∨
      ((¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom1448 chi) ∨
      (¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1448 chi))) ∨
      (((¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1448 chi) ∨
      (¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom1448 chi)) ∨
      ((¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1448 chi) ∨
      (Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1448 chi))))))) ∨
      ((((((Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1448 chi) ∨
      ((Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom1448 chi) ∨
      (Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1448 chi))) ∨
      (((Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom1448 chi) ∨
      (¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom1449 chi)) ∨
      ((¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1449 chi) ∨
      (¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1449 chi)))) ∨
      ((((¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom1449 chi) ∨
      (¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1449 chi)) ∨
      ((¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1449 chi) ∨
      (Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1449 chi))) ∨
      (((Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1449 chi) ∨
      (Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom1449 chi)) ∨
      ((Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1449 chi) ∨
      (Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom1449 chi))))) ∨
      (((((¬Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom1450 chi) ∨
      (Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom1450 chi)) ∨
      ((Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom1450 chi) ∨
      (Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom1450 chi))) ∨
      (((¬Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0287 chi ∧
      ¬Fin15AnchoredAtom0417 chi ∧
      ¬Fin15AnchoredAtom1452 chi) ∨
      (¬Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0287 chi ∧
      Fin15AnchoredAtom0417 chi ∧
      ¬Fin15AnchoredAtom1452 chi)) ∨
      ((¬Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0287 chi ∧
      ¬Fin15AnchoredAtom0417 chi ∧
      Fin15AnchoredAtom1452 chi) ∨
      (¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom1453 chi)))) ∨
      ((((¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1453 chi) ∨
      (¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom1453 chi)) ∨
      ((¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1453 chi) ∨
      (¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1453 chi))) ∨
      (((Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1453 chi) ∨
      (Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1453 chi)) ∨
      ((Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom1453 chi) ∨
      (Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1453 chi)))))) ∨
      ((((((Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom1453 chi) ∨
      (¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom1454 chi)) ∨
      ((¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom1454 chi) ∨
      (¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom1454 chi))) ∨
      (((¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom1454 chi) ∨
      (¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom1454 chi)) ∨
      ((Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom1454 chi) ∨
      (Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom1454 chi)))) ∨
      ((((Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom1454 chi) ∨
      (Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom1454 chi)) ∨
      ((Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom1454 chi) ∨
      (¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom1455 chi))) ∨
      (((¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1455 chi) ∨
      (¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom1455 chi)) ∨
      ((¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1455 chi) ∨
      (¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1455 chi))))) ∨
      (((((Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1455 chi) ∨
      (Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1455 chi)) ∨
      ((Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom1455 chi) ∨
      (Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1455 chi))) ∨
      (((Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1455 chi) ∨
      (Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom1455 chi)) ∨
      ((¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom1456 chi) ∨
      (¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1456 chi)))) ∨
      ((((¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1456 chi) ∨
      (¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom1456 chi)) ∨
      ((¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1456 chi) ∨
      (Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1456 chi))) ∨
      (((Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1456 chi) ∨
      (Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom1456 chi)) ∨
      ((Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1456 chi) ∨
      (Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom1456 chi)))))))) ∨
      (((((((¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom1458 chi) ∨
      ((¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1458 chi) ∨
      (¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom1458 chi))) ∨
      (((¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1458 chi) ∨
      (¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1458 chi)) ∨
      ((Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1458 chi) ∨
      (Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1458 chi)))) ∨
      ((((Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom1458 chi) ∨
      (Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1458 chi)) ∨
      ((Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom1458 chi) ∨
      (¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom1459 chi))) ∨
      (((¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1459 chi) ∨
      (¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom1459 chi)) ∨
      ((¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1459 chi) ∨
      (Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1459 chi))))) ∨
      (((((Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1459 chi) ∨
      (Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom1459 chi)) ∨
      ((Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1459 chi) ∨
      (Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom1459 chi))) ∨
      (((¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom1460 chi) ∨
      (¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1460 chi)) ∨
      ((¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom1460 chi) ∨
      (¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1460 chi)))) ∨
      ((((Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1460 chi) ∨
      (Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1460 chi)) ∨
      ((Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom1460 chi) ∨
      (Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1460 chi))) ∨
      (((Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom1460 chi) ∨
      (¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom1462 chi)) ∨
      ((¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1462 chi) ∨
      (¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom1462 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1462 chi) ∨
      (Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1462 chi)) ∨
      ((Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom1462 chi) ∨
      (Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1462 chi))) ∨
      (((Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom1462 chi) ∨
      (¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom1463 chi)) ∨
      ((¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1463 chi) ∨
      (¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom1463 chi)))) ∨
      ((((¬Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1463 chi) ∨
      (¬Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1463 chi)) ∨
      ((Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1463 chi) ∨
      (Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1463 chi))) ∨
      (((Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom1463 chi) ∨
      (Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1463 chi)) ∨
      ((Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1463 chi) ∨
      (Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom1463 chi))))) ∨
      (((((¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom1464 chi) ∨
      (¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1464 chi)) ∨
      ((¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom1464 chi) ∨
      (¬Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1464 chi))) ∨
      (((Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1464 chi) ∨
      (Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1464 chi)) ∨
      ((Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom1464 chi) ∨
      (Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1464 chi)))) ∨
      ((((Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom1464 chi) ∨
      (¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom1468 chi)) ∨
      ((¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1468 chi) ∨
      (¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom1468 chi))) ∨
      (((¬Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1468 chi) ∨
      (Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1468 chi)) ∨
      ((Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1468 chi) ∨
      (Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom1468 chi))))))) ∨
      ((((((Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1468 chi) ∨
      ((Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom1468 chi) ∨
      (¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom1469 chi))) ∨
      (((¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1469 chi) ∨
      (¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom1469 chi)) ∨
      ((¬Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1469 chi) ∨
      (¬Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1469 chi)))) ∨
      ((((Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1469 chi) ∨
      (Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1469 chi)) ∨
      ((Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1469 chi) ∨
      (Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom1469 chi))) ∨
      (((¬Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom1470 chi) ∨
      (¬Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1470 chi)) ∨
      ((¬Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom1470 chi) ∨
      (¬Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1470 chi))))) ∨
      (((((Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1470 chi) ∨
      (Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1470 chi)) ∨
      ((Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom1470 chi) ∨
      (Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1470 chi))) ∨
      (((Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1470 chi) ∨
      (Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom1470 chi)) ∨
      ((¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1471 chi) ∨
      (¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1471 chi)))) ∨
      ((((¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom1471 chi) ∨
      (¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1471 chi)) ∨
      ((Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1471 chi) ∨
      (Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1471 chi))) ∨
      (((Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1471 chi) ∨
      (Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1471 chi)) ∨
      ((Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom1471 chi) ∨
      (¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom1472 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1472 chi) ∨
      (¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom1472 chi)) ∨
      ((¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1472 chi) ∨
      (Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1472 chi))) ∨
      (((Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1472 chi) ∨
      (Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom1472 chi)) ∨
      ((Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1472 chi) ∨
      (Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom1472 chi)))) ∨
      ((((¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom1473 chi) ∨
      (¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1473 chi)) ∨
      ((¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1473 chi) ∨
      (¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom1473 chi))) ∨
      (((¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1473 chi) ∨
      (Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1473 chi)) ∨
      ((Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1473 chi) ∨
      (Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom1473 chi))))) ∨
      (((((Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1473 chi) ∨
      (Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom1473 chi)) ∨
      ((¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom1474 chi) ∨
      (¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1474 chi))) ∨
      (((¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1474 chi) ∨
      (¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom1474 chi)) ∨
      ((¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1474 chi) ∨
      (Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1474 chi)))) ∨
      ((((Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1474 chi) ∨
      (Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1474 chi)) ∨
      ((Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom1474 chi) ∨
      (Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1474 chi))) ∨
      (((Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom1474 chi) ∨
      (¬Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom1475 chi)) ∨
      ((¬Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom1475 chi) ∨
      (¬Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom1475 chi)))))))))) := by
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
                exact fin15Anchored_clause12367 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12368 chi hbad
                ·
                  exact fin15Anchored_clause12369 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12370 chi hbad
                ·
                  exact fin15Anchored_clause12371 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12372 chi hbad
                ·
                  exact fin15Anchored_clause12373 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12374 chi hbad
                ·
                  exact fin15Anchored_clause12375 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12376 chi hbad
                ·
                  exact fin15Anchored_clause12377 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12378 chi hbad
                ·
                  exact fin15Anchored_clause12379 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12380 chi hbad
                ·
                  exact fin15Anchored_clause12381 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12382 chi hbad
                ·
                  exact fin15Anchored_clause12383 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12384 chi hbad
                ·
                  exact fin15Anchored_clause12385 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12386 chi hbad
                ·
                  exact fin15Anchored_clause12387 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12388 chi hbad
                ·
                  exact fin15Anchored_clause12389 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12390 chi hbad
                ·
                  exact fin15Anchored_clause12391 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12392 chi hbad
                ·
                  exact fin15Anchored_clause12393 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12394 chi hbad
                ·
                  exact fin15Anchored_clause12395 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12396 chi hbad
                ·
                  exact fin15Anchored_clause12397 chi hbad
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
                  exact fin15Anchored_clause12398 chi hbad
                ·
                  exact fin15Anchored_clause12399 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12400 chi hbad
                ·
                  exact fin15Anchored_clause12401 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12402 chi hbad
                ·
                  exact fin15Anchored_clause12403 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12404 chi hbad
                ·
                  exact fin15Anchored_clause12405 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12406 chi hbad
                ·
                  exact fin15Anchored_clause12407 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12408 chi hbad
                ·
                  exact fin15Anchored_clause12409 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12410 chi hbad
                ·
                  exact fin15Anchored_clause12411 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12412 chi hbad
                ·
                  exact fin15Anchored_clause12413 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12414 chi hbad
                ·
                  exact fin15Anchored_clause12415 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12416 chi hbad
                ·
                  exact fin15Anchored_clause12417 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12418 chi hbad
                ·
                  exact fin15Anchored_clause12419 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12420 chi hbad
                ·
                  exact fin15Anchored_clause12421 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12422 chi hbad
                ·
                  exact fin15Anchored_clause12423 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12424 chi hbad
                ·
                  exact fin15Anchored_clause12425 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12426 chi hbad
                ·
                  exact fin15Anchored_clause12427 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12428 chi hbad
                ·
                  exact fin15Anchored_clause12429 chi hbad
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
                exact fin15Anchored_clause12430 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12431 chi hbad
                ·
                  exact fin15Anchored_clause12432 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12433 chi hbad
                ·
                  exact fin15Anchored_clause12434 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12435 chi hbad
                ·
                  exact fin15Anchored_clause12436 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12437 chi hbad
                ·
                  exact fin15Anchored_clause12438 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12439 chi hbad
                ·
                  exact fin15Anchored_clause12440 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12441 chi hbad
                ·
                  exact fin15Anchored_clause12442 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12443 chi hbad
                ·
                  exact fin15Anchored_clause12444 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12445 chi hbad
                ·
                  exact fin15Anchored_clause12446 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12447 chi hbad
                ·
                  exact fin15Anchored_clause12448 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12449 chi hbad
                ·
                  exact fin15Anchored_clause12450 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12451 chi hbad
                ·
                  exact fin15Anchored_clause12452 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12453 chi hbad
                ·
                  exact fin15Anchored_clause12454 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12455 chi hbad
                ·
                  exact fin15Anchored_clause12456 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12457 chi hbad
                ·
                  exact fin15Anchored_clause12458 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12459 chi hbad
                ·
                  exact fin15Anchored_clause12460 chi hbad
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
                  exact fin15Anchored_clause12461 chi hbad
                ·
                  exact fin15Anchored_clause12462 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12463 chi hbad
                ·
                  exact fin15Anchored_clause12464 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12465 chi hbad
                ·
                  exact fin15Anchored_clause12466 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12467 chi hbad
                ·
                  exact fin15Anchored_clause12468 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12469 chi hbad
                ·
                  exact fin15Anchored_clause12470 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12471 chi hbad
                ·
                  exact fin15Anchored_clause12472 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12473 chi hbad
                ·
                  exact fin15Anchored_clause12474 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12475 chi hbad
                ·
                  exact fin15Anchored_clause12476 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12477 chi hbad
                ·
                  exact fin15Anchored_clause12478 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12479 chi hbad
                ·
                  exact fin15Anchored_clause12480 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12481 chi hbad
                ·
                  exact fin15Anchored_clause12482 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12483 chi hbad
                ·
                  exact fin15Anchored_clause12484 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12485 chi hbad
                ·
                  exact fin15Anchored_clause12486 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12487 chi hbad
                ·
                  exact fin15Anchored_clause12488 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12489 chi hbad
                ·
                  exact fin15Anchored_clause12490 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12491 chi hbad
                ·
                  exact fin15Anchored_clause12492 chi hbad
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
                exact fin15Anchored_clause12493 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12494 chi hbad
                ·
                  exact fin15Anchored_clause12495 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12496 chi hbad
                ·
                  exact fin15Anchored_clause12497 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12498 chi hbad
                ·
                  exact fin15Anchored_clause12499 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12500 chi hbad
                ·
                  exact fin15Anchored_clause12501 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12502 chi hbad
                ·
                  exact fin15Anchored_clause12503 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12504 chi hbad
                ·
                  exact fin15Anchored_clause12505 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12506 chi hbad
                ·
                  exact fin15Anchored_clause12507 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12508 chi hbad
                ·
                  exact fin15Anchored_clause12509 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12510 chi hbad
                ·
                  exact fin15Anchored_clause12511 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12512 chi hbad
                ·
                  exact fin15Anchored_clause12513 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12514 chi hbad
                ·
                  exact fin15Anchored_clause12515 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12516 chi hbad
                ·
                  exact fin15Anchored_clause12517 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12518 chi hbad
                ·
                  exact fin15Anchored_clause12519 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12520 chi hbad
                ·
                  exact fin15Anchored_clause12521 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12522 chi hbad
                ·
                  exact fin15Anchored_clause12523 chi hbad
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
                  exact fin15Anchored_clause12524 chi hbad
                ·
                  exact fin15Anchored_clause12525 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12526 chi hbad
                ·
                  exact fin15Anchored_clause12527 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12528 chi hbad
                ·
                  exact fin15Anchored_clause12529 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12530 chi hbad
                ·
                  exact fin15Anchored_clause12531 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12532 chi hbad
                ·
                  exact fin15Anchored_clause12533 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12534 chi hbad
                ·
                  exact fin15Anchored_clause12535 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12536 chi hbad
                ·
                  exact fin15Anchored_clause12537 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12538 chi hbad
                ·
                  exact fin15Anchored_clause12539 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12540 chi hbad
                ·
                  exact fin15Anchored_clause12541 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12542 chi hbad
                ·
                  exact fin15Anchored_clause12543 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12544 chi hbad
                ·
                  exact fin15Anchored_clause12545 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12546 chi hbad
                ·
                  exact fin15Anchored_clause12547 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12548 chi hbad
                ·
                  exact fin15Anchored_clause12549 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12550 chi hbad
                ·
                  exact fin15Anchored_clause12551 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12552 chi hbad
                ·
                  exact fin15Anchored_clause12553 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12554 chi hbad
                ·
                  exact fin15Anchored_clause12555 chi hbad
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
                exact fin15Anchored_clause12556 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12557 chi hbad
                ·
                  exact fin15Anchored_clause12558 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12559 chi hbad
                ·
                  exact fin15Anchored_clause12560 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12561 chi hbad
                ·
                  exact fin15Anchored_clause12562 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12563 chi hbad
                ·
                  exact fin15Anchored_clause12564 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12565 chi hbad
                ·
                  exact fin15Anchored_clause12566 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12567 chi hbad
                ·
                  exact fin15Anchored_clause12568 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12569 chi hbad
                ·
                  exact fin15Anchored_clause12570 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12571 chi hbad
                ·
                  exact fin15Anchored_clause12572 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12573 chi hbad
                ·
                  exact fin15Anchored_clause12574 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12575 chi hbad
                ·
                  exact fin15Anchored_clause12576 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12577 chi hbad
                ·
                  exact fin15Anchored_clause12578 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12579 chi hbad
                ·
                  exact fin15Anchored_clause12580 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12581 chi hbad
                ·
                  exact fin15Anchored_clause12582 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12583 chi hbad
                ·
                  exact fin15Anchored_clause12584 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12585 chi hbad
                ·
                  exact fin15Anchored_clause12586 chi hbad
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
                  exact fin15Anchored_clause12587 chi hbad
                ·
                  exact fin15Anchored_clause12588 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12589 chi hbad
                ·
                  exact fin15Anchored_clause12590 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12591 chi hbad
                ·
                  exact fin15Anchored_clause12592 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12593 chi hbad
                ·
                  exact fin15Anchored_clause12594 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12595 chi hbad
                ·
                  exact fin15Anchored_clause12596 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12597 chi hbad
                ·
                  exact fin15Anchored_clause12598 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12599 chi hbad
                ·
                  exact fin15Anchored_clause12600 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12601 chi hbad
                ·
                  exact fin15Anchored_clause12602 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12603 chi hbad
                ·
                  exact fin15Anchored_clause12604 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12605 chi hbad
                ·
                  exact fin15Anchored_clause12606 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12607 chi hbad
                ·
                  exact fin15Anchored_clause12608 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12609 chi hbad
                ·
                  exact fin15Anchored_clause12610 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12611 chi hbad
                ·
                  exact fin15Anchored_clause12612 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12613 chi hbad
                ·
                  exact fin15Anchored_clause12614 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12615 chi hbad
                ·
                  exact fin15Anchored_clause12616 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12617 chi hbad
                ·
                  exact fin15Anchored_clause12618 chi hbad

end ErdosSzekeres

end
