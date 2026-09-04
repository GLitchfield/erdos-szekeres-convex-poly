module

public import ErdosSzekeres.Fin15AnchoredClauseChunk102
public import ErdosSzekeres.Fin15AnchoredClauseChunk103
public import ErdosSzekeres.Fin15AnchoredClauseChunk104

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 052. -/

theorem fin15Anchored_rejectSemanticSegment052
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom1533 chi) ∨
      ((¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom1533 chi) ∨
      (¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom1533 chi))) ∨
      (((Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom1533 chi) ∨
      (Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom1533 chi)) ∨
      ((Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom1533 chi) ∨
      (Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom1533 chi)))) ∨
      ((((Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom1533 chi) ∨
      (Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom1533 chi)) ∨
      ((¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom1534 chi) ∨
      (¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom1534 chi))) ∨
      (((¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom1534 chi) ∨
      (¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom1534 chi)) ∨
      ((Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom1534 chi) ∨
      (Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom1534 chi))))) ∨
      (((((Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom1534 chi) ∨
      (Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom1534 chi)) ∨
      ((¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom1535 chi) ∨
      (¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom1535 chi))) ∨
      (((¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom1535 chi) ∨
      (¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom1535 chi)) ∨
      ((¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom1535 chi) ∨
      (Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom1535 chi)))) ∨
      ((((Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom1535 chi) ∨
      (Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom1535 chi)) ∨
      ((Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom1535 chi) ∨
      (¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom1537 chi))) ∨
      (((¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom1537 chi) ∨
      (¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom1537 chi)) ∨
      ((¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom1537 chi) ∨
      (Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom1537 chi)))))) ∨
      ((((((Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom1537 chi) ∨
      (Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom1537 chi)) ∨
      ((Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom1537 chi) ∨
      (Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom1537 chi))) ∨
      (((¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom1538 chi) ∨
      (¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom1538 chi)) ∨
      ((¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom1538 chi) ∨
      (¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom1538 chi)))) ∨
      ((((Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom1538 chi) ∨
      (Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom1538 chi)) ∨
      ((Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom1538 chi) ∨
      (Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom1538 chi))) ∨
      (((Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom1538 chi) ∨
      (¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom1539 chi)) ∨
      ((¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom1539 chi) ∨
      (¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom1539 chi))))) ∨
      (((((¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom1539 chi) ∨
      (¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom1539 chi)) ∨
      ((Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom1539 chi) ∨
      (Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom1539 chi))) ∨
      (((Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom1539 chi) ∨
      (Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom1539 chi)) ∨
      ((Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom1539 chi) ∨
      (¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom1540 chi)))) ∨
      ((((¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom1540 chi) ∨
      (¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom1540 chi)) ∨
      ((¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom1540 chi) ∨
      (Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom1540 chi))) ∨
      (((Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom1540 chi) ∨
      (Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom1540 chi)) ∨
      ((Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom1540 chi) ∨
      (¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom1541 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom1541 chi) ∨
      ((¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom1541 chi) ∨
      (Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom1541 chi))) ∨
      (((Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom1541 chi) ∨
      (Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom1541 chi)) ∨
      ((Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom1541 chi) ∨
      (¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom1542 chi)))) ∨
      ((((¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom1542 chi) ∨
      (¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom1542 chi)) ∨
      ((¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom1542 chi) ∨
      (¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom1542 chi))) ∨
      (((Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom1542 chi) ∨
      (Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom1542 chi)) ∨
      ((Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom1542 chi) ∨
      (Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom1542 chi))))) ∨
      (((((Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom1542 chi) ∨
      (¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom1543 chi)) ∨
      ((¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1543 chi) ∨
      (¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom1543 chi))) ∨
      (((¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1543 chi) ∨
      (¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1543 chi)) ∨
      ((¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1543 chi) ∨
      (Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1543 chi)))) ∨
      ((((Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1543 chi) ∨
      (Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1543 chi)) ∨
      ((Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom1543 chi) ∨
      (Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1543 chi))) ∨
      (((Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1543 chi) ∨
      (Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom1543 chi)) ∨
      ((¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom1544 chi) ∨
      (¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom1544 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom1544 chi) ∨
      (¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom1544 chi)) ∨
      ((¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom1544 chi) ∨
      (Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom1544 chi))) ∨
      (((Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom1544 chi) ∨
      (Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom1544 chi)) ∨
      ((Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom1544 chi) ∨
      (Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom1544 chi)))) ∨
      ((((Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom1544 chi) ∨
      (¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom1545 chi)) ∨
      ((¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom1545 chi) ∨
      (¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom1545 chi))) ∨
      (((¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom1545 chi) ∨
      (¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom1545 chi)) ∨
      ((Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom1545 chi) ∨
      (Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom1545 chi))))) ∨
      (((((Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom1545 chi) ∨
      (Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom1545 chi)) ∨
      ((Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom1545 chi) ∨
      (¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom1546 chi))) ∨
      (((¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom1546 chi) ∨
      (¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom1546 chi)) ∨
      ((¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom1546 chi) ∨
      (Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom1546 chi)))) ∨
      ((((Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom1546 chi) ∨
      (Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom1546 chi)) ∨
      ((Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom1546 chi) ∨
      (Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom1546 chi))) ∨
      (((Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom1546 chi) ∨
      (¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom1547 chi)) ∨
      ((¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom1547 chi) ∨
      (¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom1547 chi)))))))) ∨
      (((((((¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom1547 chi) ∨
      ((Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom1547 chi) ∨
      (Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom1547 chi))) ∨
      (((Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom1547 chi) ∨
      (Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom1547 chi)) ∨
      ((Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom1547 chi) ∨
      (¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom1548 chi)))) ∨
      ((((¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom1548 chi) ∨
      (¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom1548 chi)) ∨
      ((¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom1548 chi) ∨
      (¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom1548 chi))) ∨
      (((¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom1548 chi) ∨
      (Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom1548 chi)) ∨
      ((Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom1548 chi) ∨
      (Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom1548 chi))))) ∨
      (((((Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom1548 chi) ∨
      (Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom1548 chi)) ∨
      ((Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom1548 chi) ∨
      (¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom1549 chi))) ∨
      (((¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom1549 chi) ∨
      (¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom1549 chi)) ∨
      ((¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom1549 chi) ∨
      (¬Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom1549 chi)))) ∨
      ((((Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom1549 chi) ∨
      (Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom1549 chi)) ∨
      ((Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom1549 chi) ∨
      (Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom1549 chi))) ∨
      (((¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom1550 chi) ∨
      (¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0395 chi ∧
      Fin15AnchoredAtom1550 chi)) ∨
      ((¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom1550 chi) ∨
      (¬Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0395 chi ∧
      Fin15AnchoredAtom1550 chi)))))) ∨
      ((((((Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0395 chi ∧
      Fin15AnchoredAtom1550 chi) ∨
      (Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0395 chi ∧
      Fin15AnchoredAtom1550 chi)) ∨
      ((Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0395 chi ∧
      Fin15AnchoredAtom1550 chi) ∨
      (¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      Fin15AnchoredAtom1551 chi))) ∨
      (((¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      Fin15AnchoredAtom0396 chi ∧
      ¬Fin15AnchoredAtom1551 chi) ∨
      (Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      Fin15AnchoredAtom1551 chi)) ∨
      ((Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      Fin15AnchoredAtom1551 chi) ∨
      (¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom1552 chi)))) ∨
      ((((¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1552 chi) ∨
      (¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom1552 chi)) ∨
      ((¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1552 chi) ∨
      (¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1552 chi))) ∨
      (((¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1552 chi) ∨
      (Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1552 chi)) ∨
      ((Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom1552 chi) ∨
      (Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1552 chi))))) ∨
      (((((Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom1552 chi) ∨
      (¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom1553 chi)) ∨
      ((¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom1553 chi) ∨
      (¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom1553 chi))) ∨
      (((¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom1553 chi) ∨
      (¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom1553 chi)) ∨
      ((Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom1553 chi) ∨
      (Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom1553 chi)))) ∨
      ((((Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom1553 chi) ∨
      (Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom1553 chi)) ∨
      ((Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom1553 chi) ∨
      (¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom1554 chi))) ∨
      (((¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom1554 chi) ∨
      (¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom1554 chi)) ∨
      ((¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom1554 chi) ∨
      (¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom1554 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom1554 chi) ∨
      ((Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom1554 chi) ∨
      (Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom1554 chi))) ∨
      (((Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom1554 chi) ∨
      (Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom1554 chi)) ∨
      ((Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom1554 chi) ∨
      (¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom1555 chi)))) ∨
      ((((¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom1555 chi) ∨
      (¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom1555 chi)) ∨
      ((¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom1555 chi) ∨
      (Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom1555 chi))) ∨
      (((Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom1555 chi) ∨
      (Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom1555 chi)) ∨
      ((Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom1555 chi) ∨
      (Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom1555 chi))))) ∨
      (((((¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom1556 chi) ∨
      (¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom1556 chi)) ∨
      ((¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom1556 chi) ∨
      (¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom1556 chi))) ∨
      (((¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom1556 chi) ∨
      (Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom1556 chi)) ∨
      ((Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom1556 chi) ∨
      (Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom1556 chi)))) ∨
      ((((Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom1556 chi) ∨
      (Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom1556 chi)) ∨
      ((¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom1558 chi) ∨
      (¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom1558 chi))) ∨
      (((¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom1558 chi) ∨
      (¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom1558 chi)) ∨
      ((Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom1558 chi) ∨
      (Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom1558 chi)))))) ∨
      ((((((Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom1558 chi) ∨
      (Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom1558 chi)) ∨
      ((¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom1559 chi) ∨
      (¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom1559 chi))) ∨
      (((¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom1559 chi) ∨
      (¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom1559 chi)) ∨
      ((Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom1559 chi) ∨
      (Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom1559 chi)))) ∨
      ((((Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom1559 chi) ∨
      (Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom1559 chi)) ∨
      ((¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom1560 chi) ∨
      (¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom1560 chi))) ∨
      (((¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom1560 chi) ∨
      (¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom1560 chi)) ∨
      ((¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom1560 chi) ∨
      (Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom1560 chi))))) ∨
      (((((Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom1560 chi) ∨
      (Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom1560 chi)) ∨
      ((Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom1560 chi) ∨
      (¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom1561 chi))) ∨
      (((¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1561 chi) ∨
      (¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom1561 chi)) ∨
      ((¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1561 chi) ∨
      (¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1561 chi)))) ∨
      ((((Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1561 chi) ∨
      (Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1561 chi)) ∨
      ((Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom1561 chi) ∨
      (Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1561 chi))) ∨
      (((Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom1561 chi) ∨
      (¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom1562 chi)) ∨
      ((¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom1562 chi) ∨
      (¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom1562 chi)))))))))) := by
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
                exact fin15Anchored_clause13124 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13125 chi hbad
                ·
                  exact fin15Anchored_clause13126 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13127 chi hbad
                ·
                  exact fin15Anchored_clause13128 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13129 chi hbad
                ·
                  exact fin15Anchored_clause13130 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13131 chi hbad
                ·
                  exact fin15Anchored_clause13132 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13133 chi hbad
                ·
                  exact fin15Anchored_clause13134 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13135 chi hbad
                ·
                  exact fin15Anchored_clause13136 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13137 chi hbad
                ·
                  exact fin15Anchored_clause13138 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13139 chi hbad
                ·
                  exact fin15Anchored_clause13140 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13141 chi hbad
                ·
                  exact fin15Anchored_clause13142 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13143 chi hbad
                ·
                  exact fin15Anchored_clause13144 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13145 chi hbad
                ·
                  exact fin15Anchored_clause13146 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13147 chi hbad
                ·
                  exact fin15Anchored_clause13148 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13149 chi hbad
                ·
                  exact fin15Anchored_clause13150 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13151 chi hbad
                ·
                  exact fin15Anchored_clause13152 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13153 chi hbad
                ·
                  exact fin15Anchored_clause13154 chi hbad
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
                  exact fin15Anchored_clause13155 chi hbad
                ·
                  exact fin15Anchored_clause13156 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13157 chi hbad
                ·
                  exact fin15Anchored_clause13158 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13159 chi hbad
                ·
                  exact fin15Anchored_clause13160 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13161 chi hbad
                ·
                  exact fin15Anchored_clause13162 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13163 chi hbad
                ·
                  exact fin15Anchored_clause13164 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13165 chi hbad
                ·
                  exact fin15Anchored_clause13166 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13167 chi hbad
                ·
                  exact fin15Anchored_clause13168 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13169 chi hbad
                ·
                  exact fin15Anchored_clause13170 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13171 chi hbad
                ·
                  exact fin15Anchored_clause13172 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13173 chi hbad
                ·
                  exact fin15Anchored_clause13174 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13175 chi hbad
                ·
                  exact fin15Anchored_clause13176 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13177 chi hbad
                ·
                  exact fin15Anchored_clause13178 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13179 chi hbad
                ·
                  exact fin15Anchored_clause13180 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13181 chi hbad
                ·
                  exact fin15Anchored_clause13182 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13183 chi hbad
                ·
                  exact fin15Anchored_clause13184 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13185 chi hbad
                ·
                  exact fin15Anchored_clause13186 chi hbad
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
                exact fin15Anchored_clause13187 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13188 chi hbad
                ·
                  exact fin15Anchored_clause13189 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13190 chi hbad
                ·
                  exact fin15Anchored_clause13191 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13192 chi hbad
                ·
                  exact fin15Anchored_clause13193 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13194 chi hbad
                ·
                  exact fin15Anchored_clause13195 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13196 chi hbad
                ·
                  exact fin15Anchored_clause13197 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13198 chi hbad
                ·
                  exact fin15Anchored_clause13199 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13200 chi hbad
                ·
                  exact fin15Anchored_clause13201 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13202 chi hbad
                ·
                  exact fin15Anchored_clause13203 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13204 chi hbad
                ·
                  exact fin15Anchored_clause13205 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13206 chi hbad
                ·
                  exact fin15Anchored_clause13207 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13208 chi hbad
                ·
                  exact fin15Anchored_clause13209 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13210 chi hbad
                ·
                  exact fin15Anchored_clause13211 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13212 chi hbad
                ·
                  exact fin15Anchored_clause13213 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13214 chi hbad
                ·
                  exact fin15Anchored_clause13215 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13216 chi hbad
                ·
                  exact fin15Anchored_clause13217 chi hbad
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
                  exact fin15Anchored_clause13218 chi hbad
                ·
                  exact fin15Anchored_clause13219 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13220 chi hbad
                ·
                  exact fin15Anchored_clause13221 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13222 chi hbad
                ·
                  exact fin15Anchored_clause13223 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13224 chi hbad
                ·
                  exact fin15Anchored_clause13225 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13226 chi hbad
                ·
                  exact fin15Anchored_clause13227 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13228 chi hbad
                ·
                  exact fin15Anchored_clause13229 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13230 chi hbad
                ·
                  exact fin15Anchored_clause13231 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13232 chi hbad
                ·
                  exact fin15Anchored_clause13233 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13234 chi hbad
                ·
                  exact fin15Anchored_clause13235 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13236 chi hbad
                ·
                  exact fin15Anchored_clause13237 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13238 chi hbad
                ·
                  exact fin15Anchored_clause13239 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13240 chi hbad
                ·
                  exact fin15Anchored_clause13241 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13242 chi hbad
                ·
                  exact fin15Anchored_clause13243 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13244 chi hbad
                ·
                  exact fin15Anchored_clause13245 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13246 chi hbad
                ·
                  exact fin15Anchored_clause13247 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13248 chi hbad
                ·
                  exact fin15Anchored_clause13249 chi hbad
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
                exact fin15Anchored_clause13250 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13251 chi hbad
                ·
                  exact fin15Anchored_clause13252 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13253 chi hbad
                ·
                  exact fin15Anchored_clause13254 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13255 chi hbad
                ·
                  exact fin15Anchored_clause13256 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13257 chi hbad
                ·
                  exact fin15Anchored_clause13258 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13259 chi hbad
                ·
                  exact fin15Anchored_clause13260 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13261 chi hbad
                ·
                  exact fin15Anchored_clause13262 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13263 chi hbad
                ·
                  exact fin15Anchored_clause13264 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13265 chi hbad
                ·
                  exact fin15Anchored_clause13266 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13267 chi hbad
                ·
                  exact fin15Anchored_clause13268 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13269 chi hbad
                ·
                  exact fin15Anchored_clause13270 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13271 chi hbad
                ·
                  exact fin15Anchored_clause13272 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13273 chi hbad
                ·
                  exact fin15Anchored_clause13274 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13275 chi hbad
                ·
                  exact fin15Anchored_clause13276 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13277 chi hbad
                ·
                  exact fin15Anchored_clause13278 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13279 chi hbad
                ·
                  exact fin15Anchored_clause13280 chi hbad
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
                  exact fin15Anchored_clause13281 chi hbad
                ·
                  exact fin15Anchored_clause13282 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13283 chi hbad
                ·
                  exact fin15Anchored_clause13284 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13285 chi hbad
                ·
                  exact fin15Anchored_clause13286 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13287 chi hbad
                ·
                  exact fin15Anchored_clause13288 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13289 chi hbad
                ·
                  exact fin15Anchored_clause13290 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13291 chi hbad
                ·
                  exact fin15Anchored_clause13292 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13293 chi hbad
                ·
                  exact fin15Anchored_clause13294 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13295 chi hbad
                ·
                  exact fin15Anchored_clause13296 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13297 chi hbad
                ·
                  exact fin15Anchored_clause13298 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13299 chi hbad
                ·
                  exact fin15Anchored_clause13300 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13301 chi hbad
                ·
                  exact fin15Anchored_clause13302 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13303 chi hbad
                ·
                  exact fin15Anchored_clause13304 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13305 chi hbad
                ·
                  exact fin15Anchored_clause13306 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13307 chi hbad
                ·
                  exact fin15Anchored_clause13308 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13309 chi hbad
                ·
                  exact fin15Anchored_clause13310 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13311 chi hbad
                ·
                  exact fin15Anchored_clause13312 chi hbad
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
                exact fin15Anchored_clause13313 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13314 chi hbad
                ·
                  exact fin15Anchored_clause13315 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13316 chi hbad
                ·
                  exact fin15Anchored_clause13317 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13318 chi hbad
                ·
                  exact fin15Anchored_clause13319 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13320 chi hbad
                ·
                  exact fin15Anchored_clause13321 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13322 chi hbad
                ·
                  exact fin15Anchored_clause13323 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13324 chi hbad
                ·
                  exact fin15Anchored_clause13325 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13326 chi hbad
                ·
                  exact fin15Anchored_clause13327 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13328 chi hbad
                ·
                  exact fin15Anchored_clause13329 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13330 chi hbad
                ·
                  exact fin15Anchored_clause13331 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13332 chi hbad
                ·
                  exact fin15Anchored_clause13333 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13334 chi hbad
                ·
                  exact fin15Anchored_clause13335 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13336 chi hbad
                ·
                  exact fin15Anchored_clause13337 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13338 chi hbad
                ·
                  exact fin15Anchored_clause13339 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13340 chi hbad
                ·
                  exact fin15Anchored_clause13341 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13342 chi hbad
                ·
                  exact fin15Anchored_clause13343 chi hbad
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
                  exact fin15Anchored_clause13344 chi hbad
                ·
                  exact fin15Anchored_clause13345 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13346 chi hbad
                ·
                  exact fin15Anchored_clause13347 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13348 chi hbad
                ·
                  exact fin15Anchored_clause13349 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13350 chi hbad
                ·
                  exact fin15Anchored_clause13351 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13352 chi hbad
                ·
                  exact fin15Anchored_clause13353 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13354 chi hbad
                ·
                  exact fin15Anchored_clause13355 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13356 chi hbad
                ·
                  exact fin15Anchored_clause13357 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13358 chi hbad
                ·
                  exact fin15Anchored_clause13359 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13360 chi hbad
                ·
                  exact fin15Anchored_clause13361 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13362 chi hbad
                ·
                  exact fin15Anchored_clause13363 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13364 chi hbad
                ·
                  exact fin15Anchored_clause13365 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13366 chi hbad
                ·
                  exact fin15Anchored_clause13367 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13368 chi hbad
                ·
                  exact fin15Anchored_clause13369 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13370 chi hbad
                ·
                  exact fin15Anchored_clause13371 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13372 chi hbad
                ·
                  exact fin15Anchored_clause13373 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13374 chi hbad
                ·
                  exact fin15Anchored_clause13375 chi hbad

end ErdosSzekeres

end
