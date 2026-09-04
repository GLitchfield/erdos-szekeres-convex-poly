module

public import ErdosSzekeres.Fin15AnchoredClauseChunk141
public import ErdosSzekeres.Fin15AnchoredClauseChunk142
public import ErdosSzekeres.Fin15AnchoredClauseChunk143

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 072. -/

theorem fin15Anchored_rejectSemanticSegment072
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom2386 chi ∧
      ¬Fin15AnchoredAtom0611 chi) ∨
      ((Fin15AnchoredAtom2386 chi ∧
      ¬Fin15AnchoredAtom0618 chi) ∨
      (Fin15AnchoredAtom2386 chi ∧
      ¬Fin15AnchoredAtom0633 chi))) ∨
      (((Fin15AnchoredAtom2386 chi ∧
      ¬Fin15AnchoredAtom0714 chi) ∨
      (Fin15AnchoredAtom2386 chi ∧
      ¬Fin15AnchoredAtom1385 chi)) ∨
      ((¬Fin15AnchoredAtom2386 chi ∧
      Fin15AnchoredAtom0611 chi ∧
      Fin15AnchoredAtom0618 chi ∧
      Fin15AnchoredAtom0633 chi ∧
      Fin15AnchoredAtom0714 chi ∧
      Fin15AnchoredAtom1385 chi) ∨
      (Fin15AnchoredAtom2387 chi ∧
      ¬Fin15AnchoredAtom0612 chi)))) ∨
      ((((Fin15AnchoredAtom2387 chi ∧
      ¬Fin15AnchoredAtom0613 chi) ∨
      (Fin15AnchoredAtom2387 chi ∧
      ¬Fin15AnchoredAtom0634 chi)) ∨
      ((Fin15AnchoredAtom2387 chi ∧
      ¬Fin15AnchoredAtom0715 chi) ∨
      (Fin15AnchoredAtom2387 chi ∧
      ¬Fin15AnchoredAtom1386 chi))) ∨
      (((¬Fin15AnchoredAtom2387 chi ∧
      Fin15AnchoredAtom0612 chi ∧
      Fin15AnchoredAtom0613 chi ∧
      Fin15AnchoredAtom0634 chi ∧
      Fin15AnchoredAtom0715 chi ∧
      Fin15AnchoredAtom1386 chi) ∨
      (Fin15AnchoredAtom2388 chi ∧
      ¬Fin15AnchoredAtom0612 chi)) ∨
      ((Fin15AnchoredAtom2388 chi ∧
      ¬Fin15AnchoredAtom0614 chi) ∨
      (Fin15AnchoredAtom2388 chi ∧
      ¬Fin15AnchoredAtom0635 chi))))) ∨
      (((((Fin15AnchoredAtom2388 chi ∧
      ¬Fin15AnchoredAtom0716 chi) ∨
      (Fin15AnchoredAtom2388 chi ∧
      ¬Fin15AnchoredAtom1387 chi)) ∨
      ((¬Fin15AnchoredAtom2388 chi ∧
      Fin15AnchoredAtom0612 chi ∧
      Fin15AnchoredAtom0614 chi ∧
      Fin15AnchoredAtom0635 chi ∧
      Fin15AnchoredAtom0716 chi ∧
      Fin15AnchoredAtom1387 chi) ∨
      (Fin15AnchoredAtom2390 chi ∧
      ¬Fin15AnchoredAtom0612 chi))) ∨
      (((Fin15AnchoredAtom2390 chi ∧
      ¬Fin15AnchoredAtom0616 chi) ∨
      (Fin15AnchoredAtom2390 chi ∧
      ¬Fin15AnchoredAtom0637 chi)) ∨
      ((Fin15AnchoredAtom2390 chi ∧
      ¬Fin15AnchoredAtom0718 chi) ∨
      (Fin15AnchoredAtom2390 chi ∧
      ¬Fin15AnchoredAtom1389 chi)))) ∨
      ((((¬Fin15AnchoredAtom2390 chi ∧
      Fin15AnchoredAtom0612 chi ∧
      Fin15AnchoredAtom0616 chi ∧
      Fin15AnchoredAtom0637 chi ∧
      Fin15AnchoredAtom0718 chi ∧
      Fin15AnchoredAtom1389 chi) ∨
      (Fin15AnchoredAtom2391 chi ∧
      ¬Fin15AnchoredAtom0612 chi)) ∨
      ((Fin15AnchoredAtom2391 chi ∧
      ¬Fin15AnchoredAtom0617 chi) ∨
      (Fin15AnchoredAtom2391 chi ∧
      ¬Fin15AnchoredAtom0638 chi))) ∨
      (((Fin15AnchoredAtom2391 chi ∧
      ¬Fin15AnchoredAtom0719 chi) ∨
      (Fin15AnchoredAtom2391 chi ∧
      ¬Fin15AnchoredAtom1390 chi)) ∨
      ((¬Fin15AnchoredAtom2391 chi ∧
      Fin15AnchoredAtom0612 chi ∧
      Fin15AnchoredAtom0617 chi ∧
      Fin15AnchoredAtom0638 chi ∧
      Fin15AnchoredAtom0719 chi ∧
      Fin15AnchoredAtom1390 chi) ∨
      (Fin15AnchoredAtom2392 chi ∧
      ¬Fin15AnchoredAtom0612 chi)))))) ∨
      ((((((Fin15AnchoredAtom2392 chi ∧
      ¬Fin15AnchoredAtom0618 chi) ∨
      (Fin15AnchoredAtom2392 chi ∧
      ¬Fin15AnchoredAtom0639 chi)) ∨
      ((Fin15AnchoredAtom2392 chi ∧
      ¬Fin15AnchoredAtom0720 chi) ∨
      (Fin15AnchoredAtom2392 chi ∧
      ¬Fin15AnchoredAtom1391 chi))) ∨
      (((¬Fin15AnchoredAtom2392 chi ∧
      Fin15AnchoredAtom0612 chi ∧
      Fin15AnchoredAtom0618 chi ∧
      Fin15AnchoredAtom0639 chi ∧
      Fin15AnchoredAtom0720 chi ∧
      Fin15AnchoredAtom1391 chi) ∨
      (Fin15AnchoredAtom2393 chi ∧
      ¬Fin15AnchoredAtom0613 chi)) ∨
      ((Fin15AnchoredAtom2393 chi ∧
      ¬Fin15AnchoredAtom0614 chi) ∨
      (Fin15AnchoredAtom2393 chi ∧
      ¬Fin15AnchoredAtom0640 chi)))) ∨
      ((((Fin15AnchoredAtom2393 chi ∧
      ¬Fin15AnchoredAtom0721 chi) ∨
      (Fin15AnchoredAtom2393 chi ∧
      ¬Fin15AnchoredAtom1392 chi)) ∨
      ((¬Fin15AnchoredAtom2393 chi ∧
      Fin15AnchoredAtom0613 chi ∧
      Fin15AnchoredAtom0614 chi ∧
      Fin15AnchoredAtom0640 chi ∧
      Fin15AnchoredAtom0721 chi ∧
      Fin15AnchoredAtom1392 chi) ∨
      (Fin15AnchoredAtom2394 chi ∧
      ¬Fin15AnchoredAtom0613 chi))) ∨
      (((Fin15AnchoredAtom2394 chi ∧
      ¬Fin15AnchoredAtom0722 chi) ∨
      (Fin15AnchoredAtom2394 chi ∧
      ¬Fin15AnchoredAtom1393 chi)) ∨
      ((¬Fin15AnchoredAtom2394 chi ∧
      Fin15AnchoredAtom0613 chi ∧
      Fin15AnchoredAtom0615 chi ∧
      Fin15AnchoredAtom0641 chi ∧
      Fin15AnchoredAtom0722 chi ∧
      Fin15AnchoredAtom1393 chi) ∨
      (Fin15AnchoredAtom2395 chi ∧
      ¬Fin15AnchoredAtom0613 chi))))) ∨
      (((((Fin15AnchoredAtom2395 chi ∧
      ¬Fin15AnchoredAtom0616 chi) ∨
      (Fin15AnchoredAtom2395 chi ∧
      ¬Fin15AnchoredAtom0642 chi)) ∨
      ((Fin15AnchoredAtom2395 chi ∧
      ¬Fin15AnchoredAtom0723 chi) ∨
      (Fin15AnchoredAtom2395 chi ∧
      ¬Fin15AnchoredAtom1394 chi))) ∨
      (((¬Fin15AnchoredAtom2395 chi ∧
      Fin15AnchoredAtom0613 chi ∧
      Fin15AnchoredAtom0616 chi ∧
      Fin15AnchoredAtom0642 chi ∧
      Fin15AnchoredAtom0723 chi ∧
      Fin15AnchoredAtom1394 chi) ∨
      (Fin15AnchoredAtom2396 chi ∧
      ¬Fin15AnchoredAtom0613 chi)) ∨
      ((Fin15AnchoredAtom2396 chi ∧
      ¬Fin15AnchoredAtom0617 chi) ∨
      (Fin15AnchoredAtom2396 chi ∧
      ¬Fin15AnchoredAtom0643 chi)))) ∨
      ((((Fin15AnchoredAtom2396 chi ∧
      ¬Fin15AnchoredAtom0724 chi) ∨
      (Fin15AnchoredAtom2396 chi ∧
      ¬Fin15AnchoredAtom1395 chi)) ∨
      ((¬Fin15AnchoredAtom2396 chi ∧
      Fin15AnchoredAtom0613 chi ∧
      Fin15AnchoredAtom0617 chi ∧
      Fin15AnchoredAtom0643 chi ∧
      Fin15AnchoredAtom0724 chi ∧
      Fin15AnchoredAtom1395 chi) ∨
      (Fin15AnchoredAtom2397 chi ∧
      ¬Fin15AnchoredAtom0613 chi))) ∨
      (((Fin15AnchoredAtom2397 chi ∧
      ¬Fin15AnchoredAtom0618 chi) ∨
      (Fin15AnchoredAtom2397 chi ∧
      ¬Fin15AnchoredAtom0644 chi)) ∨
      ((Fin15AnchoredAtom2397 chi ∧
      ¬Fin15AnchoredAtom0725 chi) ∨
      (Fin15AnchoredAtom2397 chi ∧
      ¬Fin15AnchoredAtom1396 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom2397 chi ∧
      Fin15AnchoredAtom0613 chi ∧
      Fin15AnchoredAtom0618 chi ∧
      Fin15AnchoredAtom0644 chi ∧
      Fin15AnchoredAtom0725 chi ∧
      Fin15AnchoredAtom1396 chi) ∨
      ((Fin15AnchoredAtom2398 chi ∧
      ¬Fin15AnchoredAtom0614 chi) ∨
      (Fin15AnchoredAtom2398 chi ∧
      ¬Fin15AnchoredAtom0615 chi))) ∨
      (((Fin15AnchoredAtom2398 chi ∧
      ¬Fin15AnchoredAtom0645 chi) ∨
      (Fin15AnchoredAtom2398 chi ∧
      ¬Fin15AnchoredAtom0726 chi)) ∨
      ((Fin15AnchoredAtom2398 chi ∧
      ¬Fin15AnchoredAtom1397 chi) ∨
      (¬Fin15AnchoredAtom2398 chi ∧
      Fin15AnchoredAtom0614 chi ∧
      Fin15AnchoredAtom0615 chi ∧
      Fin15AnchoredAtom0645 chi ∧
      Fin15AnchoredAtom0726 chi ∧
      Fin15AnchoredAtom1397 chi)))) ∨
      ((((Fin15AnchoredAtom2399 chi ∧
      ¬Fin15AnchoredAtom0614 chi) ∨
      (Fin15AnchoredAtom2399 chi ∧
      ¬Fin15AnchoredAtom0616 chi)) ∨
      ((Fin15AnchoredAtom2399 chi ∧
      ¬Fin15AnchoredAtom0646 chi) ∨
      (Fin15AnchoredAtom2399 chi ∧
      ¬Fin15AnchoredAtom0727 chi))) ∨
      (((Fin15AnchoredAtom2399 chi ∧
      ¬Fin15AnchoredAtom1398 chi) ∨
      (¬Fin15AnchoredAtom2399 chi ∧
      Fin15AnchoredAtom0614 chi ∧
      Fin15AnchoredAtom0616 chi ∧
      Fin15AnchoredAtom0646 chi ∧
      Fin15AnchoredAtom0727 chi ∧
      Fin15AnchoredAtom1398 chi)) ∨
      ((Fin15AnchoredAtom2400 chi ∧
      ¬Fin15AnchoredAtom0614 chi) ∨
      (Fin15AnchoredAtom2400 chi ∧
      ¬Fin15AnchoredAtom0617 chi))))) ∨
      (((((Fin15AnchoredAtom2400 chi ∧
      ¬Fin15AnchoredAtom0647 chi) ∨
      (Fin15AnchoredAtom2400 chi ∧
      ¬Fin15AnchoredAtom0728 chi)) ∨
      ((Fin15AnchoredAtom2400 chi ∧
      ¬Fin15AnchoredAtom1399 chi) ∨
      (¬Fin15AnchoredAtom2400 chi ∧
      Fin15AnchoredAtom0614 chi ∧
      Fin15AnchoredAtom0617 chi ∧
      Fin15AnchoredAtom0647 chi ∧
      Fin15AnchoredAtom0728 chi ∧
      Fin15AnchoredAtom1399 chi))) ∨
      (((Fin15AnchoredAtom2401 chi ∧
      ¬Fin15AnchoredAtom0614 chi) ∨
      (Fin15AnchoredAtom2401 chi ∧
      ¬Fin15AnchoredAtom0618 chi)) ∨
      ((Fin15AnchoredAtom2401 chi ∧
      ¬Fin15AnchoredAtom0648 chi) ∨
      (Fin15AnchoredAtom2401 chi ∧
      ¬Fin15AnchoredAtom0729 chi)))) ∨
      ((((Fin15AnchoredAtom2401 chi ∧
      ¬Fin15AnchoredAtom1400 chi) ∨
      (¬Fin15AnchoredAtom2401 chi ∧
      Fin15AnchoredAtom0614 chi ∧
      Fin15AnchoredAtom0618 chi ∧
      Fin15AnchoredAtom0648 chi ∧
      Fin15AnchoredAtom0729 chi ∧
      Fin15AnchoredAtom1400 chi)) ∨
      ((Fin15AnchoredAtom2402 chi ∧
      ¬Fin15AnchoredAtom0616 chi) ∨
      (Fin15AnchoredAtom2402 chi ∧
      ¬Fin15AnchoredAtom0649 chi))) ∨
      (((Fin15AnchoredAtom2402 chi ∧
      ¬Fin15AnchoredAtom0730 chi) ∨
      (¬Fin15AnchoredAtom2402 chi ∧
      Fin15AnchoredAtom0615 chi ∧
      Fin15AnchoredAtom0616 chi ∧
      Fin15AnchoredAtom0649 chi ∧
      Fin15AnchoredAtom0730 chi ∧
      Fin15AnchoredAtom1401 chi)) ∨
      ((Fin15AnchoredAtom2403 chi ∧
      ¬Fin15AnchoredAtom0615 chi) ∨
      (Fin15AnchoredAtom2403 chi ∧
      ¬Fin15AnchoredAtom0617 chi)))))) ∨
      ((((((Fin15AnchoredAtom2403 chi ∧
      ¬Fin15AnchoredAtom0650 chi) ∨
      (Fin15AnchoredAtom2403 chi ∧
      ¬Fin15AnchoredAtom0731 chi)) ∨
      ((Fin15AnchoredAtom2403 chi ∧
      ¬Fin15AnchoredAtom1402 chi) ∨
      (¬Fin15AnchoredAtom2403 chi ∧
      Fin15AnchoredAtom0615 chi ∧
      Fin15AnchoredAtom0617 chi ∧
      Fin15AnchoredAtom0650 chi ∧
      Fin15AnchoredAtom0731 chi ∧
      Fin15AnchoredAtom1402 chi))) ∨
      (((Fin15AnchoredAtom2404 chi ∧
      ¬Fin15AnchoredAtom0618 chi) ∨
      (Fin15AnchoredAtom2404 chi ∧
      ¬Fin15AnchoredAtom1403 chi)) ∨
      ((¬Fin15AnchoredAtom2404 chi ∧
      Fin15AnchoredAtom0615 chi ∧
      Fin15AnchoredAtom0618 chi ∧
      Fin15AnchoredAtom0651 chi ∧
      Fin15AnchoredAtom0732 chi ∧
      Fin15AnchoredAtom1403 chi) ∨
      (Fin15AnchoredAtom2405 chi ∧
      ¬Fin15AnchoredAtom0616 chi)))) ∨
      ((((Fin15AnchoredAtom2405 chi ∧
      ¬Fin15AnchoredAtom0617 chi) ∨
      (Fin15AnchoredAtom2405 chi ∧
      ¬Fin15AnchoredAtom0652 chi)) ∨
      ((Fin15AnchoredAtom2405 chi ∧
      ¬Fin15AnchoredAtom0733 chi) ∨
      (Fin15AnchoredAtom2405 chi ∧
      ¬Fin15AnchoredAtom1404 chi))) ∨
      (((¬Fin15AnchoredAtom2405 chi ∧
      Fin15AnchoredAtom0616 chi ∧
      Fin15AnchoredAtom0617 chi ∧
      Fin15AnchoredAtom0652 chi ∧
      Fin15AnchoredAtom0733 chi ∧
      Fin15AnchoredAtom1404 chi) ∨
      (Fin15AnchoredAtom2406 chi ∧
      ¬Fin15AnchoredAtom0616 chi)) ∨
      ((Fin15AnchoredAtom2406 chi ∧
      ¬Fin15AnchoredAtom0618 chi) ∨
      (Fin15AnchoredAtom2406 chi ∧
      ¬Fin15AnchoredAtom0653 chi))))) ∨
      (((((Fin15AnchoredAtom2406 chi ∧
      ¬Fin15AnchoredAtom0734 chi) ∨
      (Fin15AnchoredAtom2406 chi ∧
      ¬Fin15AnchoredAtom1405 chi)) ∨
      ((¬Fin15AnchoredAtom2406 chi ∧
      Fin15AnchoredAtom0616 chi ∧
      Fin15AnchoredAtom0618 chi ∧
      Fin15AnchoredAtom0653 chi ∧
      Fin15AnchoredAtom0734 chi ∧
      Fin15AnchoredAtom1405 chi) ∨
      (Fin15AnchoredAtom2407 chi ∧
      ¬Fin15AnchoredAtom0617 chi))) ∨
      (((Fin15AnchoredAtom2407 chi ∧
      ¬Fin15AnchoredAtom0618 chi) ∨
      (Fin15AnchoredAtom2407 chi ∧
      ¬Fin15AnchoredAtom0654 chi)) ∨
      ((Fin15AnchoredAtom2407 chi ∧
      ¬Fin15AnchoredAtom0735 chi) ∨
      (Fin15AnchoredAtom2407 chi ∧
      ¬Fin15AnchoredAtom1406 chi)))) ∨
      ((((¬Fin15AnchoredAtom2407 chi ∧
      Fin15AnchoredAtom0617 chi ∧
      Fin15AnchoredAtom0618 chi ∧
      Fin15AnchoredAtom0654 chi ∧
      Fin15AnchoredAtom0735 chi ∧
      Fin15AnchoredAtom1406 chi) ∨
      (Fin15AnchoredAtom2408 chi ∧
      ¬Fin15AnchoredAtom0619 chi)) ∨
      ((Fin15AnchoredAtom2408 chi ∧
      ¬Fin15AnchoredAtom0620 chi) ∨
      (Fin15AnchoredAtom2408 chi ∧
      ¬Fin15AnchoredAtom0627 chi))) ∨
      (((Fin15AnchoredAtom2408 chi ∧
      ¬Fin15AnchoredAtom0736 chi) ∨
      (Fin15AnchoredAtom2408 chi ∧
      ¬Fin15AnchoredAtom1407 chi)) ∨
      ((¬Fin15AnchoredAtom2408 chi ∧
      Fin15AnchoredAtom0619 chi ∧
      Fin15AnchoredAtom0620 chi ∧
      Fin15AnchoredAtom0627 chi ∧
      Fin15AnchoredAtom0736 chi ∧
      Fin15AnchoredAtom1407 chi) ∨
      (Fin15AnchoredAtom2409 chi ∧
      ¬Fin15AnchoredAtom0619 chi)))))))) ∨
      (((((((Fin15AnchoredAtom2409 chi ∧
      ¬Fin15AnchoredAtom0621 chi) ∨
      ((Fin15AnchoredAtom2409 chi ∧
      ¬Fin15AnchoredAtom0628 chi) ∨
      (Fin15AnchoredAtom2409 chi ∧
      ¬Fin15AnchoredAtom0737 chi))) ∨
      (((Fin15AnchoredAtom2409 chi ∧
      ¬Fin15AnchoredAtom1408 chi) ∨
      (¬Fin15AnchoredAtom2409 chi ∧
      Fin15AnchoredAtom0619 chi ∧
      Fin15AnchoredAtom0621 chi ∧
      Fin15AnchoredAtom0628 chi ∧
      Fin15AnchoredAtom0737 chi ∧
      Fin15AnchoredAtom1408 chi)) ∨
      ((Fin15AnchoredAtom2410 chi ∧
      ¬Fin15AnchoredAtom0619 chi) ∨
      (Fin15AnchoredAtom2410 chi ∧
      ¬Fin15AnchoredAtom0622 chi)))) ∨
      ((((Fin15AnchoredAtom2410 chi ∧
      ¬Fin15AnchoredAtom0629 chi) ∨
      (Fin15AnchoredAtom2410 chi ∧
      ¬Fin15AnchoredAtom0738 chi)) ∨
      ((Fin15AnchoredAtom2410 chi ∧
      ¬Fin15AnchoredAtom1409 chi) ∨
      (¬Fin15AnchoredAtom2410 chi ∧
      Fin15AnchoredAtom0619 chi ∧
      Fin15AnchoredAtom0622 chi ∧
      Fin15AnchoredAtom0629 chi ∧
      Fin15AnchoredAtom0738 chi ∧
      Fin15AnchoredAtom1409 chi))) ∨
      (((Fin15AnchoredAtom2411 chi ∧
      ¬Fin15AnchoredAtom0619 chi) ∨
      (Fin15AnchoredAtom2411 chi ∧
      ¬Fin15AnchoredAtom0623 chi)) ∨
      ((Fin15AnchoredAtom2411 chi ∧
      ¬Fin15AnchoredAtom0630 chi) ∨
      (Fin15AnchoredAtom2411 chi ∧
      ¬Fin15AnchoredAtom0739 chi))))) ∨
      (((((Fin15AnchoredAtom2411 chi ∧
      ¬Fin15AnchoredAtom1410 chi) ∨
      (¬Fin15AnchoredAtom2411 chi ∧
      Fin15AnchoredAtom0619 chi ∧
      Fin15AnchoredAtom0623 chi ∧
      Fin15AnchoredAtom0630 chi ∧
      Fin15AnchoredAtom0739 chi ∧
      Fin15AnchoredAtom1410 chi)) ∨
      ((Fin15AnchoredAtom2412 chi ∧
      ¬Fin15AnchoredAtom0619 chi) ∨
      (Fin15AnchoredAtom2412 chi ∧
      ¬Fin15AnchoredAtom0624 chi))) ∨
      (((Fin15AnchoredAtom2412 chi ∧
      ¬Fin15AnchoredAtom0631 chi) ∨
      (Fin15AnchoredAtom2412 chi ∧
      ¬Fin15AnchoredAtom0740 chi)) ∨
      ((Fin15AnchoredAtom2412 chi ∧
      ¬Fin15AnchoredAtom1411 chi) ∨
      (¬Fin15AnchoredAtom2412 chi ∧
      Fin15AnchoredAtom0619 chi ∧
      Fin15AnchoredAtom0624 chi ∧
      Fin15AnchoredAtom0631 chi ∧
      Fin15AnchoredAtom0740 chi ∧
      Fin15AnchoredAtom1411 chi)))) ∨
      ((((Fin15AnchoredAtom2413 chi ∧
      ¬Fin15AnchoredAtom0619 chi) ∨
      (Fin15AnchoredAtom2413 chi ∧
      ¬Fin15AnchoredAtom0625 chi)) ∨
      ((Fin15AnchoredAtom2413 chi ∧
      ¬Fin15AnchoredAtom0632 chi) ∨
      (Fin15AnchoredAtom2413 chi ∧
      ¬Fin15AnchoredAtom0741 chi))) ∨
      (((Fin15AnchoredAtom2413 chi ∧
      ¬Fin15AnchoredAtom1412 chi) ∨
      (¬Fin15AnchoredAtom2413 chi ∧
      Fin15AnchoredAtom0619 chi ∧
      Fin15AnchoredAtom0625 chi ∧
      Fin15AnchoredAtom0632 chi ∧
      Fin15AnchoredAtom0741 chi ∧
      Fin15AnchoredAtom1412 chi)) ∨
      ((Fin15AnchoredAtom2414 chi ∧
      ¬Fin15AnchoredAtom0619 chi) ∨
      (Fin15AnchoredAtom2414 chi ∧
      ¬Fin15AnchoredAtom0626 chi)))))) ∨
      ((((((Fin15AnchoredAtom2414 chi ∧
      ¬Fin15AnchoredAtom0633 chi) ∨
      (Fin15AnchoredAtom2414 chi ∧
      ¬Fin15AnchoredAtom0742 chi)) ∨
      ((Fin15AnchoredAtom2414 chi ∧
      ¬Fin15AnchoredAtom1413 chi) ∨
      (¬Fin15AnchoredAtom2414 chi ∧
      Fin15AnchoredAtom0619 chi ∧
      Fin15AnchoredAtom0626 chi ∧
      Fin15AnchoredAtom0633 chi ∧
      Fin15AnchoredAtom0742 chi ∧
      Fin15AnchoredAtom1413 chi))) ∨
      (((Fin15AnchoredAtom2415 chi ∧
      ¬Fin15AnchoredAtom0620 chi) ∨
      (Fin15AnchoredAtom2415 chi ∧
      ¬Fin15AnchoredAtom0621 chi)) ∨
      ((Fin15AnchoredAtom2415 chi ∧
      ¬Fin15AnchoredAtom0634 chi) ∨
      (Fin15AnchoredAtom2415 chi ∧
      ¬Fin15AnchoredAtom0743 chi)))) ∨
      ((((Fin15AnchoredAtom2415 chi ∧
      ¬Fin15AnchoredAtom1414 chi) ∨
      (¬Fin15AnchoredAtom2415 chi ∧
      Fin15AnchoredAtom0620 chi ∧
      Fin15AnchoredAtom0621 chi ∧
      Fin15AnchoredAtom0634 chi ∧
      Fin15AnchoredAtom0743 chi ∧
      Fin15AnchoredAtom1414 chi)) ∨
      ((Fin15AnchoredAtom2416 chi ∧
      ¬Fin15AnchoredAtom0620 chi) ∨
      (Fin15AnchoredAtom2416 chi ∧
      ¬Fin15AnchoredAtom0622 chi))) ∨
      (((Fin15AnchoredAtom2416 chi ∧
      ¬Fin15AnchoredAtom0635 chi) ∨
      (Fin15AnchoredAtom2416 chi ∧
      ¬Fin15AnchoredAtom0744 chi)) ∨
      ((Fin15AnchoredAtom2416 chi ∧
      ¬Fin15AnchoredAtom1415 chi) ∨
      (¬Fin15AnchoredAtom2416 chi ∧
      Fin15AnchoredAtom0620 chi ∧
      Fin15AnchoredAtom0622 chi ∧
      Fin15AnchoredAtom0635 chi ∧
      Fin15AnchoredAtom0744 chi ∧
      Fin15AnchoredAtom1415 chi))))) ∨
      (((((Fin15AnchoredAtom2418 chi ∧
      ¬Fin15AnchoredAtom0620 chi) ∨
      (Fin15AnchoredAtom2418 chi ∧
      ¬Fin15AnchoredAtom0624 chi)) ∨
      ((Fin15AnchoredAtom2418 chi ∧
      ¬Fin15AnchoredAtom0637 chi) ∨
      (Fin15AnchoredAtom2418 chi ∧
      ¬Fin15AnchoredAtom0746 chi))) ∨
      (((Fin15AnchoredAtom2418 chi ∧
      ¬Fin15AnchoredAtom1417 chi) ∨
      (¬Fin15AnchoredAtom2418 chi ∧
      Fin15AnchoredAtom0620 chi ∧
      Fin15AnchoredAtom0624 chi ∧
      Fin15AnchoredAtom0637 chi ∧
      Fin15AnchoredAtom0746 chi ∧
      Fin15AnchoredAtom1417 chi)) ∨
      ((Fin15AnchoredAtom2419 chi ∧
      ¬Fin15AnchoredAtom0620 chi) ∨
      (Fin15AnchoredAtom2419 chi ∧
      ¬Fin15AnchoredAtom0625 chi)))) ∨
      ((((Fin15AnchoredAtom2419 chi ∧
      ¬Fin15AnchoredAtom0638 chi) ∨
      (Fin15AnchoredAtom2419 chi ∧
      ¬Fin15AnchoredAtom0747 chi)) ∨
      ((Fin15AnchoredAtom2419 chi ∧
      ¬Fin15AnchoredAtom1418 chi) ∨
      (¬Fin15AnchoredAtom2419 chi ∧
      Fin15AnchoredAtom0620 chi ∧
      Fin15AnchoredAtom0625 chi ∧
      Fin15AnchoredAtom0638 chi ∧
      Fin15AnchoredAtom0747 chi ∧
      Fin15AnchoredAtom1418 chi))) ∨
      (((Fin15AnchoredAtom2420 chi ∧
      ¬Fin15AnchoredAtom0620 chi) ∨
      (Fin15AnchoredAtom2420 chi ∧
      ¬Fin15AnchoredAtom0626 chi)) ∨
      ((Fin15AnchoredAtom2420 chi ∧
      ¬Fin15AnchoredAtom0639 chi) ∨
      (Fin15AnchoredAtom2420 chi ∧
      ¬Fin15AnchoredAtom0748 chi))))))) ∨
      ((((((Fin15AnchoredAtom2420 chi ∧
      ¬Fin15AnchoredAtom1419 chi) ∨
      ((¬Fin15AnchoredAtom2420 chi ∧
      Fin15AnchoredAtom0620 chi ∧
      Fin15AnchoredAtom0626 chi ∧
      Fin15AnchoredAtom0639 chi ∧
      Fin15AnchoredAtom0748 chi ∧
      Fin15AnchoredAtom1419 chi) ∨
      (Fin15AnchoredAtom2421 chi ∧
      ¬Fin15AnchoredAtom0621 chi))) ∨
      (((Fin15AnchoredAtom2421 chi ∧
      ¬Fin15AnchoredAtom0622 chi) ∨
      (Fin15AnchoredAtom2421 chi ∧
      ¬Fin15AnchoredAtom0640 chi)) ∨
      ((Fin15AnchoredAtom2421 chi ∧
      ¬Fin15AnchoredAtom0749 chi) ∨
      (Fin15AnchoredAtom2421 chi ∧
      ¬Fin15AnchoredAtom1420 chi)))) ∨
      ((((¬Fin15AnchoredAtom2421 chi ∧
      Fin15AnchoredAtom0621 chi ∧
      Fin15AnchoredAtom0622 chi ∧
      Fin15AnchoredAtom0640 chi ∧
      Fin15AnchoredAtom0749 chi ∧
      Fin15AnchoredAtom1420 chi) ∨
      (Fin15AnchoredAtom2422 chi ∧
      ¬Fin15AnchoredAtom0621 chi)) ∨
      ((Fin15AnchoredAtom2422 chi ∧
      ¬Fin15AnchoredAtom0623 chi) ∨
      (Fin15AnchoredAtom2422 chi ∧
      ¬Fin15AnchoredAtom0750 chi))) ∨
      (((Fin15AnchoredAtom2422 chi ∧
      ¬Fin15AnchoredAtom1421 chi) ∨
      (¬Fin15AnchoredAtom2422 chi ∧
      Fin15AnchoredAtom0621 chi ∧
      Fin15AnchoredAtom0623 chi ∧
      Fin15AnchoredAtom0641 chi ∧
      Fin15AnchoredAtom0750 chi ∧
      Fin15AnchoredAtom1421 chi)) ∨
      ((Fin15AnchoredAtom2423 chi ∧
      ¬Fin15AnchoredAtom0621 chi) ∨
      (Fin15AnchoredAtom2423 chi ∧
      ¬Fin15AnchoredAtom0624 chi))))) ∨
      (((((Fin15AnchoredAtom2423 chi ∧
      ¬Fin15AnchoredAtom0642 chi) ∨
      (Fin15AnchoredAtom2423 chi ∧
      ¬Fin15AnchoredAtom0751 chi)) ∨
      ((Fin15AnchoredAtom2423 chi ∧
      ¬Fin15AnchoredAtom1422 chi) ∨
      (¬Fin15AnchoredAtom2423 chi ∧
      Fin15AnchoredAtom0621 chi ∧
      Fin15AnchoredAtom0624 chi ∧
      Fin15AnchoredAtom0642 chi ∧
      Fin15AnchoredAtom0751 chi ∧
      Fin15AnchoredAtom1422 chi))) ∨
      (((Fin15AnchoredAtom2424 chi ∧
      ¬Fin15AnchoredAtom0621 chi) ∨
      (Fin15AnchoredAtom2424 chi ∧
      ¬Fin15AnchoredAtom0625 chi)) ∨
      ((Fin15AnchoredAtom2424 chi ∧
      ¬Fin15AnchoredAtom0643 chi) ∨
      (Fin15AnchoredAtom2424 chi ∧
      ¬Fin15AnchoredAtom0752 chi)))) ∨
      ((((Fin15AnchoredAtom2424 chi ∧
      ¬Fin15AnchoredAtom1423 chi) ∨
      (¬Fin15AnchoredAtom2424 chi ∧
      Fin15AnchoredAtom0621 chi ∧
      Fin15AnchoredAtom0625 chi ∧
      Fin15AnchoredAtom0643 chi ∧
      Fin15AnchoredAtom0752 chi ∧
      Fin15AnchoredAtom1423 chi)) ∨
      ((Fin15AnchoredAtom2425 chi ∧
      ¬Fin15AnchoredAtom0621 chi) ∨
      (Fin15AnchoredAtom2425 chi ∧
      ¬Fin15AnchoredAtom0626 chi))) ∨
      (((Fin15AnchoredAtom2425 chi ∧
      ¬Fin15AnchoredAtom0644 chi) ∨
      (Fin15AnchoredAtom2425 chi ∧
      ¬Fin15AnchoredAtom0753 chi)) ∨
      ((Fin15AnchoredAtom2425 chi ∧
      ¬Fin15AnchoredAtom1424 chi) ∨
      (¬Fin15AnchoredAtom2425 chi ∧
      Fin15AnchoredAtom0621 chi ∧
      Fin15AnchoredAtom0626 chi ∧
      Fin15AnchoredAtom0644 chi ∧
      Fin15AnchoredAtom0753 chi ∧
      Fin15AnchoredAtom1424 chi)))))) ∨
      ((((((Fin15AnchoredAtom2426 chi ∧
      ¬Fin15AnchoredAtom0622 chi) ∨
      (Fin15AnchoredAtom2426 chi ∧
      ¬Fin15AnchoredAtom0623 chi)) ∨
      ((Fin15AnchoredAtom2426 chi ∧
      ¬Fin15AnchoredAtom0645 chi) ∨
      (Fin15AnchoredAtom2426 chi ∧
      ¬Fin15AnchoredAtom0754 chi))) ∨
      (((Fin15AnchoredAtom2426 chi ∧
      ¬Fin15AnchoredAtom1425 chi) ∨
      (¬Fin15AnchoredAtom2426 chi ∧
      Fin15AnchoredAtom0622 chi ∧
      Fin15AnchoredAtom0623 chi ∧
      Fin15AnchoredAtom0645 chi ∧
      Fin15AnchoredAtom0754 chi ∧
      Fin15AnchoredAtom1425 chi)) ∨
      ((Fin15AnchoredAtom2427 chi ∧
      ¬Fin15AnchoredAtom0622 chi) ∨
      (Fin15AnchoredAtom2427 chi ∧
      ¬Fin15AnchoredAtom0624 chi)))) ∨
      ((((Fin15AnchoredAtom2427 chi ∧
      ¬Fin15AnchoredAtom0646 chi) ∨
      (Fin15AnchoredAtom2427 chi ∧
      ¬Fin15AnchoredAtom0755 chi)) ∨
      ((Fin15AnchoredAtom2427 chi ∧
      ¬Fin15AnchoredAtom1426 chi) ∨
      (¬Fin15AnchoredAtom2427 chi ∧
      Fin15AnchoredAtom0622 chi ∧
      Fin15AnchoredAtom0624 chi ∧
      Fin15AnchoredAtom0646 chi ∧
      Fin15AnchoredAtom0755 chi ∧
      Fin15AnchoredAtom1426 chi))) ∨
      (((Fin15AnchoredAtom2428 chi ∧
      ¬Fin15AnchoredAtom0622 chi) ∨
      (Fin15AnchoredAtom2428 chi ∧
      ¬Fin15AnchoredAtom0625 chi)) ∨
      ((Fin15AnchoredAtom2428 chi ∧
      ¬Fin15AnchoredAtom0647 chi) ∨
      (Fin15AnchoredAtom2428 chi ∧
      ¬Fin15AnchoredAtom0756 chi))))) ∨
      (((((Fin15AnchoredAtom2428 chi ∧
      ¬Fin15AnchoredAtom1427 chi) ∨
      (¬Fin15AnchoredAtom2428 chi ∧
      Fin15AnchoredAtom0622 chi ∧
      Fin15AnchoredAtom0625 chi ∧
      Fin15AnchoredAtom0647 chi ∧
      Fin15AnchoredAtom0756 chi ∧
      Fin15AnchoredAtom1427 chi)) ∨
      ((Fin15AnchoredAtom2429 chi ∧
      ¬Fin15AnchoredAtom0622 chi) ∨
      (Fin15AnchoredAtom2429 chi ∧
      ¬Fin15AnchoredAtom0626 chi))) ∨
      (((Fin15AnchoredAtom2429 chi ∧
      ¬Fin15AnchoredAtom0648 chi) ∨
      (Fin15AnchoredAtom2429 chi ∧
      ¬Fin15AnchoredAtom0757 chi)) ∨
      ((Fin15AnchoredAtom2429 chi ∧
      ¬Fin15AnchoredAtom1428 chi) ∨
      (¬Fin15AnchoredAtom2429 chi ∧
      Fin15AnchoredAtom0622 chi ∧
      Fin15AnchoredAtom0626 chi ∧
      Fin15AnchoredAtom0648 chi ∧
      Fin15AnchoredAtom0757 chi ∧
      Fin15AnchoredAtom1428 chi)))) ∨
      ((((Fin15AnchoredAtom2430 chi ∧
      ¬Fin15AnchoredAtom0624 chi) ∨
      (¬Fin15AnchoredAtom2430 chi ∧
      Fin15AnchoredAtom0623 chi ∧
      Fin15AnchoredAtom0624 chi ∧
      Fin15AnchoredAtom0649 chi ∧
      Fin15AnchoredAtom0758 chi ∧
      Fin15AnchoredAtom1429 chi)) ∨
      ((Fin15AnchoredAtom2431 chi ∧
      ¬Fin15AnchoredAtom0623 chi) ∨
      (Fin15AnchoredAtom2431 chi ∧
      ¬Fin15AnchoredAtom0625 chi))) ∨
      (((Fin15AnchoredAtom2431 chi ∧
      ¬Fin15AnchoredAtom0650 chi) ∨
      (Fin15AnchoredAtom2431 chi ∧
      ¬Fin15AnchoredAtom0759 chi)) ∨
      ((Fin15AnchoredAtom2431 chi ∧
      ¬Fin15AnchoredAtom1430 chi) ∨
      (¬Fin15AnchoredAtom2431 chi ∧
      Fin15AnchoredAtom0623 chi ∧
      Fin15AnchoredAtom0625 chi ∧
      Fin15AnchoredAtom0650 chi ∧
      Fin15AnchoredAtom0759 chi ∧
      Fin15AnchoredAtom1430 chi)))))))))) := by
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
                exact fin15Anchored_clause18173 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18174 chi hbad
                ·
                  exact fin15Anchored_clause18175 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18176 chi hbad
                ·
                  exact fin15Anchored_clause18177 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18178 chi hbad
                ·
                  exact fin15Anchored_clause18179 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18180 chi hbad
                ·
                  exact fin15Anchored_clause18181 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18182 chi hbad
                ·
                  exact fin15Anchored_clause18183 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18184 chi hbad
                ·
                  exact fin15Anchored_clause18185 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18186 chi hbad
                ·
                  exact fin15Anchored_clause18187 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18188 chi hbad
                ·
                  exact fin15Anchored_clause18189 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18190 chi hbad
                ·
                  exact fin15Anchored_clause18191 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18192 chi hbad
                ·
                  exact fin15Anchored_clause18193 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18194 chi hbad
                ·
                  exact fin15Anchored_clause18195 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18196 chi hbad
                ·
                  exact fin15Anchored_clause18197 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18198 chi hbad
                ·
                  exact fin15Anchored_clause18199 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18200 chi hbad
                ·
                  exact fin15Anchored_clause18201 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18202 chi hbad
                ·
                  exact fin15Anchored_clause18203 chi hbad
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
                  exact fin15Anchored_clause18204 chi hbad
                ·
                  exact fin15Anchored_clause18205 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18206 chi hbad
                ·
                  exact fin15Anchored_clause18207 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18208 chi hbad
                ·
                  exact fin15Anchored_clause18209 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18210 chi hbad
                ·
                  exact fin15Anchored_clause18211 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18212 chi hbad
                ·
                  exact fin15Anchored_clause18213 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18214 chi hbad
                ·
                  exact fin15Anchored_clause18215 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18216 chi hbad
                ·
                  exact fin15Anchored_clause18217 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18218 chi hbad
                ·
                  exact fin15Anchored_clause18219 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18220 chi hbad
                ·
                  exact fin15Anchored_clause18221 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18222 chi hbad
                ·
                  exact fin15Anchored_clause18223 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18224 chi hbad
                ·
                  exact fin15Anchored_clause18225 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18226 chi hbad
                ·
                  exact fin15Anchored_clause18227 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18228 chi hbad
                ·
                  exact fin15Anchored_clause18229 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18230 chi hbad
                ·
                  exact fin15Anchored_clause18231 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18232 chi hbad
                ·
                  exact fin15Anchored_clause18233 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18234 chi hbad
                ·
                  exact fin15Anchored_clause18235 chi hbad
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
                exact fin15Anchored_clause18236 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18237 chi hbad
                ·
                  exact fin15Anchored_clause18238 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18239 chi hbad
                ·
                  exact fin15Anchored_clause18240 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18241 chi hbad
                ·
                  exact fin15Anchored_clause18242 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18243 chi hbad
                ·
                  exact fin15Anchored_clause18244 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18245 chi hbad
                ·
                  exact fin15Anchored_clause18246 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18247 chi hbad
                ·
                  exact fin15Anchored_clause18248 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18249 chi hbad
                ·
                  exact fin15Anchored_clause18250 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18251 chi hbad
                ·
                  exact fin15Anchored_clause18252 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18253 chi hbad
                ·
                  exact fin15Anchored_clause18254 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18255 chi hbad
                ·
                  exact fin15Anchored_clause18256 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18257 chi hbad
                ·
                  exact fin15Anchored_clause18258 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18259 chi hbad
                ·
                  exact fin15Anchored_clause18260 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18261 chi hbad
                ·
                  exact fin15Anchored_clause18262 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18263 chi hbad
                ·
                  exact fin15Anchored_clause18264 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18265 chi hbad
                ·
                  exact fin15Anchored_clause18266 chi hbad
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
                  exact fin15Anchored_clause18267 chi hbad
                ·
                  exact fin15Anchored_clause18268 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18269 chi hbad
                ·
                  exact fin15Anchored_clause18270 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18271 chi hbad
                ·
                  exact fin15Anchored_clause18272 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18273 chi hbad
                ·
                  exact fin15Anchored_clause18274 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18275 chi hbad
                ·
                  exact fin15Anchored_clause18276 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18277 chi hbad
                ·
                  exact fin15Anchored_clause18278 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18279 chi hbad
                ·
                  exact fin15Anchored_clause18280 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18281 chi hbad
                ·
                  exact fin15Anchored_clause18282 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18283 chi hbad
                ·
                  exact fin15Anchored_clause18284 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18285 chi hbad
                ·
                  exact fin15Anchored_clause18286 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18287 chi hbad
                ·
                  exact fin15Anchored_clause18288 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18289 chi hbad
                ·
                  exact fin15Anchored_clause18290 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18291 chi hbad
                ·
                  exact fin15Anchored_clause18292 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18293 chi hbad
                ·
                  exact fin15Anchored_clause18294 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18295 chi hbad
                ·
                  exact fin15Anchored_clause18296 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18297 chi hbad
                ·
                  exact fin15Anchored_clause18298 chi hbad
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
                exact fin15Anchored_clause18299 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18300 chi hbad
                ·
                  exact fin15Anchored_clause18301 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18302 chi hbad
                ·
                  exact fin15Anchored_clause18303 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18304 chi hbad
                ·
                  exact fin15Anchored_clause18305 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18306 chi hbad
                ·
                  exact fin15Anchored_clause18307 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18308 chi hbad
                ·
                  exact fin15Anchored_clause18309 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18310 chi hbad
                ·
                  exact fin15Anchored_clause18311 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18312 chi hbad
                ·
                  exact fin15Anchored_clause18313 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18314 chi hbad
                ·
                  exact fin15Anchored_clause18315 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18316 chi hbad
                ·
                  exact fin15Anchored_clause18317 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18318 chi hbad
                ·
                  exact fin15Anchored_clause18319 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18320 chi hbad
                ·
                  exact fin15Anchored_clause18321 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18322 chi hbad
                ·
                  exact fin15Anchored_clause18323 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18324 chi hbad
                ·
                  exact fin15Anchored_clause18325 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18326 chi hbad
                ·
                  exact fin15Anchored_clause18327 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18328 chi hbad
                ·
                  exact fin15Anchored_clause18329 chi hbad
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
                  exact fin15Anchored_clause18330 chi hbad
                ·
                  exact fin15Anchored_clause18331 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18332 chi hbad
                ·
                  exact fin15Anchored_clause18333 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18334 chi hbad
                ·
                  exact fin15Anchored_clause18335 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18336 chi hbad
                ·
                  exact fin15Anchored_clause18337 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18338 chi hbad
                ·
                  exact fin15Anchored_clause18339 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18340 chi hbad
                ·
                  exact fin15Anchored_clause18341 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18342 chi hbad
                ·
                  exact fin15Anchored_clause18343 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18344 chi hbad
                ·
                  exact fin15Anchored_clause18345 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18346 chi hbad
                ·
                  exact fin15Anchored_clause18347 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18348 chi hbad
                ·
                  exact fin15Anchored_clause18349 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18350 chi hbad
                ·
                  exact fin15Anchored_clause18351 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18352 chi hbad
                ·
                  exact fin15Anchored_clause18353 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18354 chi hbad
                ·
                  exact fin15Anchored_clause18355 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18356 chi hbad
                ·
                  exact fin15Anchored_clause18357 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18358 chi hbad
                ·
                  exact fin15Anchored_clause18359 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18360 chi hbad
                ·
                  exact fin15Anchored_clause18361 chi hbad
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
                exact fin15Anchored_clause18362 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18363 chi hbad
                ·
                  exact fin15Anchored_clause18364 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18365 chi hbad
                ·
                  exact fin15Anchored_clause18366 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18367 chi hbad
                ·
                  exact fin15Anchored_clause18368 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18369 chi hbad
                ·
                  exact fin15Anchored_clause18370 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18371 chi hbad
                ·
                  exact fin15Anchored_clause18372 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18373 chi hbad
                ·
                  exact fin15Anchored_clause18374 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18375 chi hbad
                ·
                  exact fin15Anchored_clause18376 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18377 chi hbad
                ·
                  exact fin15Anchored_clause18378 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18379 chi hbad
                ·
                  exact fin15Anchored_clause18380 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18381 chi hbad
                ·
                  exact fin15Anchored_clause18382 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18383 chi hbad
                ·
                  exact fin15Anchored_clause18384 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18385 chi hbad
                ·
                  exact fin15Anchored_clause18386 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18387 chi hbad
                ·
                  exact fin15Anchored_clause18388 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18389 chi hbad
                ·
                  exact fin15Anchored_clause18390 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18391 chi hbad
                ·
                  exact fin15Anchored_clause18392 chi hbad
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
                  exact fin15Anchored_clause18393 chi hbad
                ·
                  exact fin15Anchored_clause18394 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18395 chi hbad
                ·
                  exact fin15Anchored_clause18396 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18397 chi hbad
                ·
                  exact fin15Anchored_clause18398 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18399 chi hbad
                ·
                  exact fin15Anchored_clause18400 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18401 chi hbad
                ·
                  exact fin15Anchored_clause18402 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18403 chi hbad
                ·
                  exact fin15Anchored_clause18404 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18405 chi hbad
                ·
                  exact fin15Anchored_clause18406 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18407 chi hbad
                ·
                  exact fin15Anchored_clause18408 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18409 chi hbad
                ·
                  exact fin15Anchored_clause18410 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18411 chi hbad
                ·
                  exact fin15Anchored_clause18412 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18413 chi hbad
                ·
                  exact fin15Anchored_clause18414 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18415 chi hbad
                ·
                  exact fin15Anchored_clause18416 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18417 chi hbad
                ·
                  exact fin15Anchored_clause18418 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18419 chi hbad
                ·
                  exact fin15Anchored_clause18420 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18421 chi hbad
                ·
                  exact fin15Anchored_clause18422 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18423 chi hbad
                ·
                  exact fin15Anchored_clause18424 chi hbad

end ErdosSzekeres

end
