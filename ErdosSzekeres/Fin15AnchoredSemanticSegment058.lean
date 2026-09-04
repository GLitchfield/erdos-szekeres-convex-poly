module

public import ErdosSzekeres.Fin15AnchoredClauseChunk114
public import ErdosSzekeres.Fin15AnchoredClauseChunk115
public import ErdosSzekeres.Fin15AnchoredClauseChunk116

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 058. -/

theorem fin15Anchored_rejectSemanticSegment058
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1715 chi) ∨
      ((¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1715 chi) ∨
      (¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom1715 chi))) ∨
      (((¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1715 chi) ∨
      (Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1715 chi)) ∨
      ((Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom1715 chi) ∨
      (Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1715 chi)))) ∨
      ((((Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1715 chi) ∨
      (Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom1715 chi)) ∨
      ((¬Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom1716 chi) ∨
      (¬Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1716 chi))) ∨
      (((¬Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom1716 chi) ∨
      (¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1716 chi)) ∨
      ((Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1716 chi) ∨
      (Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom1716 chi))))) ∨
      (((((Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1716 chi) ∨
      (Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom1716 chi)) ∨
      ((¬Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom1718 chi) ∨
      (¬Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1718 chi))) ∨
      (((¬Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1718 chi) ∨
      (¬Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom1718 chi)) ∨
      ((¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1718 chi) ∨
      (Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1718 chi)))) ∨
      ((((Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1718 chi) ∨
      (Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom1718 chi)) ∨
      ((Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1718 chi) ∨
      (Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom1718 chi))) ∨
      (((¬Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom1719 chi) ∨
      (¬Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1719 chi)) ∨
      ((¬Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1719 chi) ∨
      (¬Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom1719 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1719 chi) ∨
      (¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1719 chi)) ∨
      ((Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1719 chi) ∨
      (Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom1719 chi))) ∨
      (((Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1719 chi) ∨
      (Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom1719 chi)) ∨
      ((¬Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom1720 chi) ∨
      (¬Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1720 chi)))) ∨
      ((((¬Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom1720 chi) ∨
      (¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1720 chi)) ∨
      ((¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1720 chi) ∨
      (Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1720 chi))) ∨
      (((Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1720 chi) ∨
      (Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom1720 chi)) ∨
      ((Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1720 chi) ∨
      (Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom1720 chi))))) ∨
      (((((¬Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom1722 chi) ∨
      (¬Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1722 chi)) ∨
      ((¬Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom1722 chi) ∨
      (¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1722 chi))) ∨
      (((¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1722 chi) ∨
      (¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1722 chi)) ∨
      ((Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1722 chi) ∨
      (Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom1722 chi)))) ∨
      ((((Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1722 chi) ∨
      (Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom1722 chi)) ∨
      ((¬Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom1723 chi) ∨
      (¬Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1723 chi))) ∨
      (((¬Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom1723 chi) ∨
      (¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1723 chi)) ∨
      ((Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1723 chi) ∨
      (Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom1723 chi))))))) ∨
      ((((((Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1723 chi) ∨
      ((Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom1723 chi) ∨
      (¬Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom1724 chi))) ∨
      (((¬Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1724 chi) ∨
      (¬Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom1724 chi)) ∨
      ((¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1724 chi) ∨
      (¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1724 chi)))) ∨
      ((((Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1724 chi) ∨
      (Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom1724 chi)) ∨
      ((Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1724 chi) ∨
      (Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1724 chi))) ∨
      (((Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom1724 chi) ∨
      (¬Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom1728 chi)) ∨
      ((¬Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1728 chi) ∨
      (¬Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom1728 chi))))) ∨
      (((((¬Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1728 chi) ∨
      (¬Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1728 chi)) ∨
      ((Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1728 chi) ∨
      (Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1728 chi))) ∨
      (((Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom1728 chi) ∨
      (Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1728 chi)) ∨
      ((Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1728 chi) ∨
      (Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom1728 chi)))) ∨
      ((((¬Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom1729 chi) ∨
      (¬Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1729 chi)) ∨
      ((¬Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1729 chi) ∨
      (¬Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom1729 chi))) ∨
      (((¬Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1729 chi) ∨
      (Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1729 chi)) ∨
      ((Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1729 chi) ∨
      (Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom1729 chi)))))) ∨
      ((((((Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1729 chi) ∨
      (Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom1729 chi)) ∨
      ((¬Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom1730 chi) ∨
      (¬Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1730 chi))) ∨
      (((¬Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom1730 chi) ∨
      (¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1730 chi)) ∨
      ((¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1730 chi) ∨
      (¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1730 chi)))) ∨
      ((((Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1730 chi) ∨
      (Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1730 chi)) ∨
      ((Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1730 chi) ∨
      (Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom1730 chi))) ∨
      (((Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1730 chi) ∨
      (Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom1730 chi)) ∨
      ((¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom1731 chi) ∨
      (¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1731 chi))))) ∨
      (((((¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom1731 chi) ∨
      (¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1731 chi)) ∨
      ((¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1731 chi) ∨
      (Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1731 chi))) ∨
      (((Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom1731 chi) ∨
      (Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom1731 chi)) ∨
      ((¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom1732 chi) ∨
      (¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1732 chi)))) ∨
      ((((¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom1732 chi) ∨
      (¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1732 chi)) ∨
      ((¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1732 chi) ∨
      (Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1732 chi))) ∨
      (((Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1732 chi) ∨
      (Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1732 chi)) ∨
      ((Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom1732 chi) ∨
      (Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1732 chi)))))))) ∨
      (((((((Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom1732 chi) ∨
      ((¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom1733 chi) ∨
      (¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1733 chi))) ∨
      (((¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1733 chi) ∨
      (¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom1733 chi)) ∨
      ((¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1733 chi) ∨
      (¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1733 chi)))) ∨
      ((((¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1733 chi) ∨
      (Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1733 chi)) ∨
      ((Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom1733 chi) ∨
      (Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1733 chi))) ∨
      (((Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1733 chi) ∨
      (Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom1733 chi)) ∨
      ((¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom1734 chi) ∨
      (¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1734 chi))))) ∨
      (((((¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1734 chi) ∨
      (¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom1734 chi)) ∨
      ((¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1734 chi) ∨
      (Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1734 chi))) ∨
      (((Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1734 chi) ∨
      (Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom1734 chi)) ∨
      ((Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1734 chi) ∨
      (Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom1734 chi)))) ∨
      ((((¬Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom1735 chi) ∨
      (¬Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom1735 chi)) ∨
      ((¬Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom1735 chi) ∨
      (Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom1735 chi))) ∨
      (((Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom1735 chi) ∨
      (Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom1735 chi)) ∨
      ((Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom1735 chi) ∨
      (¬Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0395 chi ∧
      Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom1736 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0395 chi ∧
      Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom1736 chi) ∨
      (Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom1736 chi)) ∨
      ((Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom1736 chi) ∨
      (Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0395 chi ∧
      Fin15AnchoredAtom0441 chi ∧
      ¬Fin15AnchoredAtom1736 chi))) ∨
      (((¬Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      ¬Fin15AnchoredAtom0442 chi ∧
      ¬Fin15AnchoredAtom1737 chi) ∨
      (Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      ¬Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom1737 chi)) ∨
      ((Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom1737 chi) ∨
      (¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom1738 chi)))) ∨
      ((((¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1738 chi) ∨
      (¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom1738 chi)) ∨
      ((¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1738 chi) ∨
      (Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1738 chi))) ∨
      (((Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1738 chi) ∨
      (Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1738 chi)) ∨
      ((Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom1738 chi) ∨
      (Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1738 chi))))) ∨
      (((((Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom1738 chi) ∨
      (¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom1739 chi)) ∨
      ((¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1739 chi) ∨
      (¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom1739 chi))) ∨
      (((¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1739 chi) ∨
      (¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1739 chi)) ∨
      ((¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1739 chi) ∨
      (Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1739 chi)))) ∨
      ((((Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1739 chi) ∨
      (Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom1739 chi)) ∨
      ((Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1739 chi) ∨
      (Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom1739 chi))) ∨
      (((¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom1740 chi) ∨
      (¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1740 chi)) ∨
      ((¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom1740 chi) ∨
      (¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1740 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1740 chi) ∨
      ((Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1740 chi) ∨
      (Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1740 chi))) ∨
      (((Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom1740 chi) ∨
      (Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1740 chi)) ∨
      ((Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom1740 chi) ∨
      (¬Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom1741 chi)))) ∨
      ((((¬Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom1741 chi) ∨
      (¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1741 chi)) ∨
      ((¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1741 chi) ∨
      (¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1741 chi))) ∨
      (((Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1741 chi) ∨
      (Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1741 chi)) ∨
      ((Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom1741 chi) ∨
      (Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1741 chi))))) ∨
      (((((Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom1741 chi) ∨
      (¬Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom1742 chi)) ∨
      ((¬Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom1742 chi) ∨
      (¬Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0395 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom1742 chi))) ∨
      (((Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom1742 chi) ∨
      (Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0395 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom1742 chi)) ∨
      ((¬Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      ¬Fin15AnchoredAtom1743 chi) ∨
      (¬Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      Fin15AnchoredAtom0448 chi ∧
      Fin15AnchoredAtom1743 chi)))) ∨
      ((((¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0396 chi ∧
      Fin15AnchoredAtom0448 chi ∧
      Fin15AnchoredAtom1743 chi) ∨
      (¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1744 chi)) ∨
      ((¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1744 chi) ∨
      (¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1744 chi))) ∨
      (((¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1744 chi) ∨
      (¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1744 chi)) ∨
      ((¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1744 chi) ∨
      (¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1744 chi)))))) ∨
      ((((((Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1744 chi) ∨
      (Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1744 chi)) ∨
      ((Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1744 chi) ∨
      (Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1744 chi))) ∨
      (((Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1744 chi) ∨
      (¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1745 chi)) ∨
      ((¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1745 chi) ∨
      (¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1745 chi)))) ∨
      ((((¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1745 chi) ∨
      (Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1745 chi)) ∨
      ((Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1745 chi) ∨
      (Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1745 chi))) ∨
      (((Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1745 chi) ∨
      (Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1745 chi)) ∨
      ((¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1746 chi) ∨
      (¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1746 chi))))) ∨
      (((((¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1746 chi) ∨
      (¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1746 chi)) ∨
      ((¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1746 chi) ∨
      (Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1746 chi))) ∨
      (((Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1746 chi) ∨
      (Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1746 chi)) ∨
      ((Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1746 chi) ∨
      (¬Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom1747 chi)))) ∨
      ((((Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1747 chi) ∨
      (Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom1747 chi)) ∨
      ((Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0395 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1747 chi) ∨
      (Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0395 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom1747 chi))) ∨
      (((¬Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom1748 chi) ∨
      (¬Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1748 chi)) ∨
      ((Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1748 chi) ∨
      (Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1748 chi)))))))))) := by
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
                exact fin15Anchored_clause14639 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14640 chi hbad
                ·
                  exact fin15Anchored_clause14641 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14642 chi hbad
                ·
                  exact fin15Anchored_clause14643 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14644 chi hbad
                ·
                  exact fin15Anchored_clause14645 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14646 chi hbad
                ·
                  exact fin15Anchored_clause14647 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14648 chi hbad
                ·
                  exact fin15Anchored_clause14649 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14650 chi hbad
                ·
                  exact fin15Anchored_clause14651 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14652 chi hbad
                ·
                  exact fin15Anchored_clause14653 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14654 chi hbad
                ·
                  exact fin15Anchored_clause14655 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14656 chi hbad
                ·
                  exact fin15Anchored_clause14657 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14658 chi hbad
                ·
                  exact fin15Anchored_clause14659 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14660 chi hbad
                ·
                  exact fin15Anchored_clause14661 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14662 chi hbad
                ·
                  exact fin15Anchored_clause14663 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14664 chi hbad
                ·
                  exact fin15Anchored_clause14665 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14666 chi hbad
                ·
                  exact fin15Anchored_clause14667 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14668 chi hbad
                ·
                  exact fin15Anchored_clause14669 chi hbad
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
                  exact fin15Anchored_clause14670 chi hbad
                ·
                  exact fin15Anchored_clause14671 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14672 chi hbad
                ·
                  exact fin15Anchored_clause14673 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14674 chi hbad
                ·
                  exact fin15Anchored_clause14675 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14676 chi hbad
                ·
                  exact fin15Anchored_clause14677 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14678 chi hbad
                ·
                  exact fin15Anchored_clause14679 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14680 chi hbad
                ·
                  exact fin15Anchored_clause14681 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14682 chi hbad
                ·
                  exact fin15Anchored_clause14683 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14684 chi hbad
                ·
                  exact fin15Anchored_clause14685 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14686 chi hbad
                ·
                  exact fin15Anchored_clause14687 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14688 chi hbad
                ·
                  exact fin15Anchored_clause14689 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14690 chi hbad
                ·
                  exact fin15Anchored_clause14691 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14692 chi hbad
                ·
                  exact fin15Anchored_clause14693 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14694 chi hbad
                ·
                  exact fin15Anchored_clause14695 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14696 chi hbad
                ·
                  exact fin15Anchored_clause14697 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14698 chi hbad
                ·
                  exact fin15Anchored_clause14699 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14700 chi hbad
                ·
                  exact fin15Anchored_clause14701 chi hbad
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
                exact fin15Anchored_clause14702 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14703 chi hbad
                ·
                  exact fin15Anchored_clause14704 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14705 chi hbad
                ·
                  exact fin15Anchored_clause14706 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14707 chi hbad
                ·
                  exact fin15Anchored_clause14708 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14709 chi hbad
                ·
                  exact fin15Anchored_clause14710 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14711 chi hbad
                ·
                  exact fin15Anchored_clause14712 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14713 chi hbad
                ·
                  exact fin15Anchored_clause14714 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14715 chi hbad
                ·
                  exact fin15Anchored_clause14716 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14717 chi hbad
                ·
                  exact fin15Anchored_clause14718 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14719 chi hbad
                ·
                  exact fin15Anchored_clause14720 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14721 chi hbad
                ·
                  exact fin15Anchored_clause14722 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14723 chi hbad
                ·
                  exact fin15Anchored_clause14724 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14725 chi hbad
                ·
                  exact fin15Anchored_clause14726 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14727 chi hbad
                ·
                  exact fin15Anchored_clause14728 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14729 chi hbad
                ·
                  exact fin15Anchored_clause14730 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14731 chi hbad
                ·
                  exact fin15Anchored_clause14732 chi hbad
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
                  exact fin15Anchored_clause14733 chi hbad
                ·
                  exact fin15Anchored_clause14734 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14735 chi hbad
                ·
                  exact fin15Anchored_clause14736 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14737 chi hbad
                ·
                  exact fin15Anchored_clause14738 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14739 chi hbad
                ·
                  exact fin15Anchored_clause14740 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14741 chi hbad
                ·
                  exact fin15Anchored_clause14742 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14743 chi hbad
                ·
                  exact fin15Anchored_clause14744 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14745 chi hbad
                ·
                  exact fin15Anchored_clause14746 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14747 chi hbad
                ·
                  exact fin15Anchored_clause14748 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14749 chi hbad
                ·
                  exact fin15Anchored_clause14750 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14751 chi hbad
                ·
                  exact fin15Anchored_clause14752 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14753 chi hbad
                ·
                  exact fin15Anchored_clause14754 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14755 chi hbad
                ·
                  exact fin15Anchored_clause14756 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14757 chi hbad
                ·
                  exact fin15Anchored_clause14758 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14759 chi hbad
                ·
                  exact fin15Anchored_clause14760 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14761 chi hbad
                ·
                  exact fin15Anchored_clause14762 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14763 chi hbad
                ·
                  exact fin15Anchored_clause14764 chi hbad
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
                exact fin15Anchored_clause14765 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14766 chi hbad
                ·
                  exact fin15Anchored_clause14767 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14768 chi hbad
                ·
                  exact fin15Anchored_clause14769 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14770 chi hbad
                ·
                  exact fin15Anchored_clause14771 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14772 chi hbad
                ·
                  exact fin15Anchored_clause14773 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14774 chi hbad
                ·
                  exact fin15Anchored_clause14775 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14776 chi hbad
                ·
                  exact fin15Anchored_clause14777 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14778 chi hbad
                ·
                  exact fin15Anchored_clause14779 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14780 chi hbad
                ·
                  exact fin15Anchored_clause14781 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14782 chi hbad
                ·
                  exact fin15Anchored_clause14783 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14784 chi hbad
                ·
                  exact fin15Anchored_clause14785 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14786 chi hbad
                ·
                  exact fin15Anchored_clause14787 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14788 chi hbad
                ·
                  exact fin15Anchored_clause14789 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14790 chi hbad
                ·
                  exact fin15Anchored_clause14791 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14792 chi hbad
                ·
                  exact fin15Anchored_clause14793 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14794 chi hbad
                ·
                  exact fin15Anchored_clause14795 chi hbad
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
                  exact fin15Anchored_clause14796 chi hbad
                ·
                  exact fin15Anchored_clause14797 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14798 chi hbad
                ·
                  exact fin15Anchored_clause14799 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14800 chi hbad
                ·
                  exact fin15Anchored_clause14801 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14802 chi hbad
                ·
                  exact fin15Anchored_clause14803 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14804 chi hbad
                ·
                  exact fin15Anchored_clause14805 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14806 chi hbad
                ·
                  exact fin15Anchored_clause14807 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14808 chi hbad
                ·
                  exact fin15Anchored_clause14809 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14810 chi hbad
                ·
                  exact fin15Anchored_clause14811 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14812 chi hbad
                ·
                  exact fin15Anchored_clause14813 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14814 chi hbad
                ·
                  exact fin15Anchored_clause14815 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14816 chi hbad
                ·
                  exact fin15Anchored_clause14817 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14818 chi hbad
                ·
                  exact fin15Anchored_clause14819 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14820 chi hbad
                ·
                  exact fin15Anchored_clause14821 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14822 chi hbad
                ·
                  exact fin15Anchored_clause14823 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14824 chi hbad
                ·
                  exact fin15Anchored_clause14825 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14826 chi hbad
                ·
                  exact fin15Anchored_clause14827 chi hbad
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
                exact fin15Anchored_clause14828 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14829 chi hbad
                ·
                  exact fin15Anchored_clause14830 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14831 chi hbad
                ·
                  exact fin15Anchored_clause14832 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14833 chi hbad
                ·
                  exact fin15Anchored_clause14834 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14835 chi hbad
                ·
                  exact fin15Anchored_clause14836 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14837 chi hbad
                ·
                  exact fin15Anchored_clause14838 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14839 chi hbad
                ·
                  exact fin15Anchored_clause14840 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14841 chi hbad
                ·
                  exact fin15Anchored_clause14842 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14843 chi hbad
                ·
                  exact fin15Anchored_clause14844 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14845 chi hbad
                ·
                  exact fin15Anchored_clause14846 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14847 chi hbad
                ·
                  exact fin15Anchored_clause14848 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14849 chi hbad
                ·
                  exact fin15Anchored_clause14850 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14851 chi hbad
                ·
                  exact fin15Anchored_clause14852 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14853 chi hbad
                ·
                  exact fin15Anchored_clause14854 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14855 chi hbad
                ·
                  exact fin15Anchored_clause14856 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14857 chi hbad
                ·
                  exact fin15Anchored_clause14858 chi hbad
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
                  exact fin15Anchored_clause14859 chi hbad
                ·
                  exact fin15Anchored_clause14860 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14861 chi hbad
                ·
                  exact fin15Anchored_clause14862 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14863 chi hbad
                ·
                  exact fin15Anchored_clause14864 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14865 chi hbad
                ·
                  exact fin15Anchored_clause14866 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14867 chi hbad
                ·
                  exact fin15Anchored_clause14868 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14869 chi hbad
                ·
                  exact fin15Anchored_clause14870 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14871 chi hbad
                ·
                  exact fin15Anchored_clause14872 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14873 chi hbad
                ·
                  exact fin15Anchored_clause14874 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14875 chi hbad
                ·
                  exact fin15Anchored_clause14876 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14877 chi hbad
                ·
                  exact fin15Anchored_clause14878 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14879 chi hbad
                ·
                  exact fin15Anchored_clause14880 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14881 chi hbad
                ·
                  exact fin15Anchored_clause14882 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14883 chi hbad
                ·
                  exact fin15Anchored_clause14884 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14885 chi hbad
                ·
                  exact fin15Anchored_clause14886 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14887 chi hbad
                ·
                  exact fin15Anchored_clause14888 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14889 chi hbad
                ·
                  exact fin15Anchored_clause14890 chi hbad

end ErdosSzekeres

end
