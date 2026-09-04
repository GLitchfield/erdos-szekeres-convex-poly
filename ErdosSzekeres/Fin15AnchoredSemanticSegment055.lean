module

public import ErdosSzekeres.Fin15AnchoredClauseChunk108
public import ErdosSzekeres.Fin15AnchoredClauseChunk109
public import ErdosSzekeres.Fin15AnchoredClauseChunk110

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 055. -/

theorem fin15Anchored_rejectSemanticSegment055
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom1624 chi) ∨
      ((Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom1624 chi) ∨
      (Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom1624 chi))) ∨
      (((Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom1624 chi) ∨
      (Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom1624 chi)) ∨
      ((Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom1624 chi) ∨
      (¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom1625 chi)))) ∨
      ((((¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom1625 chi) ∨
      (¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom1625 chi)) ∨
      ((¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom1625 chi) ∨
      (Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom1625 chi))) ∨
      (((Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom1625 chi) ∨
      (Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom1625 chi)) ∨
      ((¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom1626 chi) ∨
      (¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom1626 chi))))) ∨
      (((((¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom1626 chi) ∨
      (¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom1626 chi)) ∨
      ((¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom1626 chi) ∨
      (¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom1626 chi))) ∨
      (((Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom1626 chi) ∨
      (Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom1626 chi)) ∨
      ((Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom1626 chi) ∨
      (Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom1626 chi)))) ∨
      ((((¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom1627 chi) ∨
      (¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1627 chi)) ∨
      ((¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom1627 chi) ∨
      (¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1627 chi))) ∨
      (((¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1627 chi) ∨
      (Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1627 chi)) ∨
      ((Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1627 chi) ∨
      (Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1627 chi)))))) ∨
      ((((((Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom1627 chi) ∨
      (Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1627 chi)) ∨
      ((Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom1627 chi) ∨
      (¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom1628 chi))) ∨
      (((¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom1628 chi) ∨
      (¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom1628 chi)) ∨
      ((¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom1628 chi) ∨
      (¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom1628 chi)))) ∨
      ((((Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom1628 chi) ∨
      (Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom1628 chi)) ∨
      ((Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom1628 chi) ∨
      (Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom1628 chi))) ∨
      (((Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom1628 chi) ∨
      (¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom1629 chi)) ∨
      ((¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom1629 chi) ∨
      (¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom1629 chi))))) ∨
      (((((¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom1629 chi) ∨
      (Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom1629 chi)) ∨
      ((Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom1629 chi) ∨
      (Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom1629 chi))) ∨
      (((Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom1629 chi) ∨
      (Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom1629 chi)) ∨
      ((¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom1630 chi) ∨
      (¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom1630 chi)))) ∨
      ((((¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom1630 chi) ∨
      (¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom1630 chi)) ∨
      ((¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom1630 chi) ∨
      (¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom1630 chi))) ∨
      (((Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom1630 chi) ∨
      (Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom1630 chi)) ∨
      ((Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom1630 chi) ∨
      (Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom1630 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom1631 chi) ∨
      ((¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom1631 chi) ∨
      (¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom1631 chi))) ∨
      (((¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom1631 chi) ∨
      (Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom1631 chi)) ∨
      ((Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom1631 chi) ∨
      (Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom1631 chi)))) ∨
      ((((Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom1631 chi) ∨
      (Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom1631 chi)) ∨
      ((¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom1632 chi) ∨
      (¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom1632 chi))) ∨
      (((¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom1632 chi) ∨
      (¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom1632 chi)) ∨
      ((¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom1632 chi) ∨
      (¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom1632 chi))))) ∨
      (((((Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom1632 chi) ∨
      (Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom1632 chi)) ∨
      ((Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom1632 chi) ∨
      (Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom1632 chi))) ∨
      (((¬Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom1633 chi) ∨
      (¬Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom1633 chi)) ∨
      ((¬Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom1633 chi) ∨
      (Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom1633 chi)))) ∨
      ((((Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom1633 chi) ∨
      (Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom1633 chi)) ∨
      ((¬Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom1634 chi) ∨
      (Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom1634 chi))) ∨
      (((¬Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      ¬Fin15AnchoredAtom1635 chi) ∨
      (¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom1636 chi)) ∨
      ((¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1636 chi) ∨
      (¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1636 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom1636 chi) ∨
      (¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1636 chi)) ∨
      ((¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1636 chi) ∨
      (¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1636 chi))) ∨
      (((¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1636 chi) ∨
      (Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1636 chi)) ∨
      ((Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1636 chi) ∨
      (Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom1636 chi)))) ∨
      ((((Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1636 chi) ∨
      (Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom1636 chi)) ∨
      ((¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom1637 chi) ∨
      (¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom1637 chi))) ∨
      (((¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom1637 chi) ∨
      (¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom1637 chi)) ∨
      ((Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom1637 chi) ∨
      (Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom1637 chi))))) ∨
      (((((Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom1637 chi) ∨
      (Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom1637 chi)) ∨
      ((Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom1637 chi) ∨
      (¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom1638 chi))) ∨
      (((¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom1638 chi) ∨
      (¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom1638 chi)) ∨
      ((¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom1638 chi) ∨
      (Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom1638 chi)))) ∨
      ((((Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom1638 chi) ∨
      (Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom1638 chi)) ∨
      ((Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom1638 chi) ∨
      (¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom1639 chi))) ∨
      (((¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom1639 chi) ∨
      (¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom1639 chi)) ∨
      ((¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom1639 chi) ∨
      (¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom1639 chi)))))))) ∨
      (((((((Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom1639 chi) ∨
      ((Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom1639 chi) ∨
      (Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom1639 chi))) ∨
      (((Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom1639 chi) ∨
      (Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom1639 chi)) ∨
      ((Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom1639 chi) ∨
      (¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom1640 chi)))) ∨
      ((((¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom1640 chi) ∨
      (¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom1640 chi)) ∨
      ((¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom1640 chi) ∨
      (Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom1640 chi))) ∨
      (((Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom1640 chi) ∨
      (Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom1640 chi)) ∨
      ((Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom1640 chi) ∨
      (Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom1640 chi))))) ∨
      (((((¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom1642 chi) ∨
      (¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom1642 chi)) ∨
      ((¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom1642 chi) ∨
      (¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom1642 chi))) ∨
      (((¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom1642 chi) ∨
      (Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom1642 chi)) ∨
      ((Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom1642 chi) ∨
      (Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom1642 chi)))) ∨
      ((((Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom1642 chi) ∨
      (Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom1642 chi)) ∨
      ((Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom1642 chi) ∨
      (¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom1643 chi))) ∨
      (((¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom1643 chi) ∨
      (¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom1643 chi)) ∨
      ((¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom1643 chi) ∨
      (¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom1643 chi)))))) ∨
      ((((((Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom1643 chi) ∨
      (Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom1643 chi)) ∨
      ((Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom1643 chi) ∨
      (Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom1643 chi))) ∨
      (((Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom1643 chi) ∨
      (¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom1644 chi)) ∨
      ((¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom1644 chi) ∨
      (¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom1644 chi)))) ∨
      ((((¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom1644 chi) ∨
      (¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom1644 chi)) ∨
      ((Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom1644 chi) ∨
      (Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom1644 chi))) ∨
      (((Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom1644 chi) ∨
      (Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom1644 chi)) ∨
      ((¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom1645 chi) ∨
      (¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1645 chi))))) ∨
      (((((¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom1645 chi) ∨
      (¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1645 chi)) ∨
      ((¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1645 chi) ∨
      (Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1645 chi))) ∨
      (((Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom1645 chi) ∨
      (Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1645 chi)) ∨
      ((Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom1645 chi) ∨
      (¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom1646 chi)))) ∨
      ((((¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom1646 chi) ∨
      (¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom1646 chi)) ∨
      ((¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom1646 chi) ∨
      (Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom1646 chi))) ∨
      (((Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom1646 chi) ∨
      (Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom1646 chi)) ∨
      ((Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom1646 chi) ∨
      (Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom1646 chi))))))) ∨
      (((((((¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom1647 chi) ∨
      (¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1647 chi)) ∨
      ((¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom1647 chi) ∨
      (¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1647 chi))) ∨
      (((¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1647 chi) ∨
      (¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1647 chi)) ∨
      ((Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1647 chi) ∨
      (Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1647 chi)))) ∨
      ((((Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom1647 chi) ∨
      (Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1647 chi)) ∨
      ((Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom1647 chi) ∨
      (¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom1648 chi))) ∨
      (((¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1648 chi) ∨
      (¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom1648 chi)) ∨
      ((¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1648 chi) ∨
      (¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1648 chi))))) ∨
      (((((Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1648 chi) ∨
      (Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom1648 chi)) ∨
      ((Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1648 chi) ∨
      (Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom1648 chi))) ∨
      (((¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom1649 chi) ∨
      (¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1649 chi)) ∨
      ((¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom1649 chi) ∨
      (¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1649 chi)))) ∨
      ((((Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1649 chi) ∨
      (Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1649 chi)) ∨
      ((Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom1649 chi) ∨
      (Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1649 chi))) ∨
      (((Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom1649 chi) ∨
      (¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom1650 chi)) ∨
      ((¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom1650 chi) ∨
      (¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom1650 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom1650 chi) ∨
      (¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom1650 chi)) ∨
      ((¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom1650 chi) ∨
      (Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom1650 chi))) ∨
      (((Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom1650 chi) ∨
      (¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom1651 chi)) ∨
      ((¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1651 chi) ∨
      (¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom1651 chi)))) ∨
      ((((¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1651 chi) ∨
      (¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1651 chi)) ∨
      ((Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1651 chi) ∨
      (Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1651 chi))) ∨
      (((Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom1651 chi) ∨
      (Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1651 chi)) ∨
      ((Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1651 chi) ∨
      (Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom1651 chi))))) ∨
      (((((¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom1652 chi) ∨
      (¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1652 chi)) ∨
      ((¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom1652 chi) ∨
      (¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1652 chi))) ∨
      (((Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1652 chi) ∨
      (Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1652 chi)) ∨
      ((Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom1652 chi) ∨
      (Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1652 chi)))) ∨
      ((((Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom1652 chi) ∨
      (¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom1653 chi)) ∨
      ((¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1653 chi) ∨
      (¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom1653 chi))) ∨
      (((¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1653 chi) ∨
      (¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1653 chi)) ∨
      ((¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1653 chi) ∨
      (Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1653 chi)))))))))) := by
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
                exact fin15Anchored_clause13881 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13882 chi hbad
                ·
                  exact fin15Anchored_clause13883 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13884 chi hbad
                ·
                  exact fin15Anchored_clause13885 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13886 chi hbad
                ·
                  exact fin15Anchored_clause13887 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13888 chi hbad
                ·
                  exact fin15Anchored_clause13889 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13890 chi hbad
                ·
                  exact fin15Anchored_clause13891 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13892 chi hbad
                ·
                  exact fin15Anchored_clause13893 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13894 chi hbad
                ·
                  exact fin15Anchored_clause13895 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13896 chi hbad
                ·
                  exact fin15Anchored_clause13897 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13898 chi hbad
                ·
                  exact fin15Anchored_clause13899 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13900 chi hbad
                ·
                  exact fin15Anchored_clause13901 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13902 chi hbad
                ·
                  exact fin15Anchored_clause13903 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13904 chi hbad
                ·
                  exact fin15Anchored_clause13905 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13906 chi hbad
                ·
                  exact fin15Anchored_clause13907 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13908 chi hbad
                ·
                  exact fin15Anchored_clause13909 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13910 chi hbad
                ·
                  exact fin15Anchored_clause13911 chi hbad
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
                  exact fin15Anchored_clause13912 chi hbad
                ·
                  exact fin15Anchored_clause13913 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13914 chi hbad
                ·
                  exact fin15Anchored_clause13915 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13916 chi hbad
                ·
                  exact fin15Anchored_clause13917 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13918 chi hbad
                ·
                  exact fin15Anchored_clause13919 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13920 chi hbad
                ·
                  exact fin15Anchored_clause13921 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13922 chi hbad
                ·
                  exact fin15Anchored_clause13923 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13924 chi hbad
                ·
                  exact fin15Anchored_clause13925 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13926 chi hbad
                ·
                  exact fin15Anchored_clause13927 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13928 chi hbad
                ·
                  exact fin15Anchored_clause13929 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13930 chi hbad
                ·
                  exact fin15Anchored_clause13931 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13932 chi hbad
                ·
                  exact fin15Anchored_clause13933 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13934 chi hbad
                ·
                  exact fin15Anchored_clause13935 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13936 chi hbad
                ·
                  exact fin15Anchored_clause13937 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13938 chi hbad
                ·
                  exact fin15Anchored_clause13939 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13940 chi hbad
                ·
                  exact fin15Anchored_clause13941 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13942 chi hbad
                ·
                  exact fin15Anchored_clause13943 chi hbad
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
                exact fin15Anchored_clause13944 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13945 chi hbad
                ·
                  exact fin15Anchored_clause13946 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13947 chi hbad
                ·
                  exact fin15Anchored_clause13948 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13949 chi hbad
                ·
                  exact fin15Anchored_clause13950 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13951 chi hbad
                ·
                  exact fin15Anchored_clause13952 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13953 chi hbad
                ·
                  exact fin15Anchored_clause13954 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13955 chi hbad
                ·
                  exact fin15Anchored_clause13956 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13957 chi hbad
                ·
                  exact fin15Anchored_clause13958 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13959 chi hbad
                ·
                  exact fin15Anchored_clause13960 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13961 chi hbad
                ·
                  exact fin15Anchored_clause13962 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13963 chi hbad
                ·
                  exact fin15Anchored_clause13964 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13965 chi hbad
                ·
                  exact fin15Anchored_clause13966 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13967 chi hbad
                ·
                  exact fin15Anchored_clause13968 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13969 chi hbad
                ·
                  exact fin15Anchored_clause13970 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13971 chi hbad
                ·
                  exact fin15Anchored_clause13972 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13973 chi hbad
                ·
                  exact fin15Anchored_clause13974 chi hbad
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
                  exact fin15Anchored_clause13975 chi hbad
                ·
                  exact fin15Anchored_clause13976 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13977 chi hbad
                ·
                  exact fin15Anchored_clause13978 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13979 chi hbad
                ·
                  exact fin15Anchored_clause13980 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13981 chi hbad
                ·
                  exact fin15Anchored_clause13982 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13983 chi hbad
                ·
                  exact fin15Anchored_clause13984 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13985 chi hbad
                ·
                  exact fin15Anchored_clause13986 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13987 chi hbad
                ·
                  exact fin15Anchored_clause13988 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13989 chi hbad
                ·
                  exact fin15Anchored_clause13990 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13991 chi hbad
                ·
                  exact fin15Anchored_clause13992 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13993 chi hbad
                ·
                  exact fin15Anchored_clause13994 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13995 chi hbad
                ·
                  exact fin15Anchored_clause13996 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13997 chi hbad
                ·
                  exact fin15Anchored_clause13998 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13999 chi hbad
                ·
                  exact fin15Anchored_clause14000 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14001 chi hbad
                ·
                  exact fin15Anchored_clause14002 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14003 chi hbad
                ·
                  exact fin15Anchored_clause14004 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14005 chi hbad
                ·
                  exact fin15Anchored_clause14006 chi hbad
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
                exact fin15Anchored_clause14007 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14008 chi hbad
                ·
                  exact fin15Anchored_clause14009 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14010 chi hbad
                ·
                  exact fin15Anchored_clause14011 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14012 chi hbad
                ·
                  exact fin15Anchored_clause14013 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14014 chi hbad
                ·
                  exact fin15Anchored_clause14015 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14016 chi hbad
                ·
                  exact fin15Anchored_clause14017 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14018 chi hbad
                ·
                  exact fin15Anchored_clause14019 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14020 chi hbad
                ·
                  exact fin15Anchored_clause14021 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14022 chi hbad
                ·
                  exact fin15Anchored_clause14023 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14024 chi hbad
                ·
                  exact fin15Anchored_clause14025 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14026 chi hbad
                ·
                  exact fin15Anchored_clause14027 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14028 chi hbad
                ·
                  exact fin15Anchored_clause14029 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14030 chi hbad
                ·
                  exact fin15Anchored_clause14031 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14032 chi hbad
                ·
                  exact fin15Anchored_clause14033 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14034 chi hbad
                ·
                  exact fin15Anchored_clause14035 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14036 chi hbad
                ·
                  exact fin15Anchored_clause14037 chi hbad
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
                  exact fin15Anchored_clause14038 chi hbad
                ·
                  exact fin15Anchored_clause14039 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14040 chi hbad
                ·
                  exact fin15Anchored_clause14041 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14042 chi hbad
                ·
                  exact fin15Anchored_clause14043 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14044 chi hbad
                ·
                  exact fin15Anchored_clause14045 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14046 chi hbad
                ·
                  exact fin15Anchored_clause14047 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14048 chi hbad
                ·
                  exact fin15Anchored_clause14049 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14050 chi hbad
                ·
                  exact fin15Anchored_clause14051 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14052 chi hbad
                ·
                  exact fin15Anchored_clause14053 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14054 chi hbad
                ·
                  exact fin15Anchored_clause14055 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14056 chi hbad
                ·
                  exact fin15Anchored_clause14057 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14058 chi hbad
                ·
                  exact fin15Anchored_clause14059 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14060 chi hbad
                ·
                  exact fin15Anchored_clause14061 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14062 chi hbad
                ·
                  exact fin15Anchored_clause14063 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14064 chi hbad
                ·
                  exact fin15Anchored_clause14065 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14066 chi hbad
                ·
                  exact fin15Anchored_clause14067 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14068 chi hbad
                ·
                  exact fin15Anchored_clause14069 chi hbad
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
                  exact fin15Anchored_clause14070 chi hbad
                ·
                  exact fin15Anchored_clause14071 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14072 chi hbad
                ·
                  exact fin15Anchored_clause14073 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14074 chi hbad
                ·
                  exact fin15Anchored_clause14075 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14076 chi hbad
                ·
                  exact fin15Anchored_clause14077 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14078 chi hbad
                ·
                  exact fin15Anchored_clause14079 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14080 chi hbad
                ·
                  exact fin15Anchored_clause14081 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14082 chi hbad
                ·
                  exact fin15Anchored_clause14083 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14084 chi hbad
                ·
                  exact fin15Anchored_clause14085 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14086 chi hbad
                ·
                  exact fin15Anchored_clause14087 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14088 chi hbad
                ·
                  exact fin15Anchored_clause14089 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14090 chi hbad
                ·
                  exact fin15Anchored_clause14091 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14092 chi hbad
                ·
                  exact fin15Anchored_clause14093 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14094 chi hbad
                ·
                  exact fin15Anchored_clause14095 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14096 chi hbad
                ·
                  exact fin15Anchored_clause14097 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14098 chi hbad
                ·
                  exact fin15Anchored_clause14099 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14100 chi hbad
                ·
                  exact fin15Anchored_clause14101 chi hbad
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
                  exact fin15Anchored_clause14102 chi hbad
                ·
                  exact fin15Anchored_clause14103 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14104 chi hbad
                ·
                  exact fin15Anchored_clause14105 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14106 chi hbad
                ·
                  exact fin15Anchored_clause14107 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14108 chi hbad
                ·
                  exact fin15Anchored_clause14109 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14110 chi hbad
                ·
                  exact fin15Anchored_clause14111 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14112 chi hbad
                ·
                  exact fin15Anchored_clause14113 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14114 chi hbad
                ·
                  exact fin15Anchored_clause14115 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14116 chi hbad
                ·
                  exact fin15Anchored_clause14117 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14118 chi hbad
                ·
                  exact fin15Anchored_clause14119 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14120 chi hbad
                ·
                  exact fin15Anchored_clause14121 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14122 chi hbad
                ·
                  exact fin15Anchored_clause14123 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14124 chi hbad
                ·
                  exact fin15Anchored_clause14125 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14126 chi hbad
                ·
                  exact fin15Anchored_clause14127 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14128 chi hbad
                ·
                  exact fin15Anchored_clause14129 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14130 chi hbad
                ·
                  exact fin15Anchored_clause14131 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14132 chi hbad
                ·
                  exact fin15Anchored_clause14133 chi hbad

end ErdosSzekeres

end
