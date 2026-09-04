module

public import ErdosSzekeres.Fin15AnchoredClauseChunk140
public import ErdosSzekeres.Fin15AnchoredClauseChunk141

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 071. -/

theorem fin15Anchored_rejectSemanticSegment071
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((¬Fin15AnchoredAtom2338 chi ∧
      Fin15AnchoredAtom0601 chi ∧
      Fin15AnchoredAtom0604 chi ∧
      Fin15AnchoredAtom0621 chi ∧
      Fin15AnchoredAtom0666 chi ∧
      Fin15AnchoredAtom1337 chi) ∨
      ((Fin15AnchoredAtom2339 chi ∧
      ¬Fin15AnchoredAtom0601 chi) ∨
      (Fin15AnchoredAtom2339 chi ∧
      ¬Fin15AnchoredAtom0605 chi))) ∨
      (((Fin15AnchoredAtom2339 chi ∧
      ¬Fin15AnchoredAtom0622 chi) ∨
      (Fin15AnchoredAtom2339 chi ∧
      ¬Fin15AnchoredAtom0667 chi)) ∨
      ((Fin15AnchoredAtom2339 chi ∧
      ¬Fin15AnchoredAtom1338 chi) ∨
      (¬Fin15AnchoredAtom2339 chi ∧
      Fin15AnchoredAtom0601 chi ∧
      Fin15AnchoredAtom0605 chi ∧
      Fin15AnchoredAtom0622 chi ∧
      Fin15AnchoredAtom0667 chi ∧
      Fin15AnchoredAtom1338 chi)))) ∨
      ((((Fin15AnchoredAtom2340 chi ∧
      ¬Fin15AnchoredAtom0601 chi) ∨
      (Fin15AnchoredAtom2340 chi ∧
      ¬Fin15AnchoredAtom0668 chi)) ∨
      ((¬Fin15AnchoredAtom2340 chi ∧
      Fin15AnchoredAtom0601 chi ∧
      Fin15AnchoredAtom0606 chi ∧
      Fin15AnchoredAtom0623 chi ∧
      Fin15AnchoredAtom0668 chi ∧
      Fin15AnchoredAtom1339 chi) ∨
      (Fin15AnchoredAtom2341 chi ∧
      ¬Fin15AnchoredAtom0601 chi))) ∨
      (((Fin15AnchoredAtom2341 chi ∧
      ¬Fin15AnchoredAtom0607 chi) ∨
      (Fin15AnchoredAtom2341 chi ∧
      ¬Fin15AnchoredAtom0624 chi)) ∨
      ((Fin15AnchoredAtom2341 chi ∧
      ¬Fin15AnchoredAtom0669 chi) ∨
      (Fin15AnchoredAtom2341 chi ∧
      ¬Fin15AnchoredAtom1340 chi))))) ∨
      (((((¬Fin15AnchoredAtom2341 chi ∧
      Fin15AnchoredAtom0601 chi ∧
      Fin15AnchoredAtom0607 chi ∧
      Fin15AnchoredAtom0624 chi ∧
      Fin15AnchoredAtom0669 chi ∧
      Fin15AnchoredAtom1340 chi) ∨
      (Fin15AnchoredAtom2342 chi ∧
      ¬Fin15AnchoredAtom0601 chi)) ∨
      ((Fin15AnchoredAtom2342 chi ∧
      ¬Fin15AnchoredAtom0608 chi) ∨
      (Fin15AnchoredAtom2342 chi ∧
      ¬Fin15AnchoredAtom0625 chi))) ∨
      (((Fin15AnchoredAtom2342 chi ∧
      ¬Fin15AnchoredAtom0670 chi) ∨
      (Fin15AnchoredAtom2342 chi ∧
      ¬Fin15AnchoredAtom1341 chi)) ∨
      ((¬Fin15AnchoredAtom2342 chi ∧
      Fin15AnchoredAtom0601 chi ∧
      Fin15AnchoredAtom0608 chi ∧
      Fin15AnchoredAtom0625 chi ∧
      Fin15AnchoredAtom0670 chi ∧
      Fin15AnchoredAtom1341 chi) ∨
      (Fin15AnchoredAtom2343 chi ∧
      ¬Fin15AnchoredAtom0601 chi)))) ∨
      ((((Fin15AnchoredAtom2343 chi ∧
      ¬Fin15AnchoredAtom0609 chi) ∨
      (Fin15AnchoredAtom2343 chi ∧
      ¬Fin15AnchoredAtom0626 chi)) ∨
      ((Fin15AnchoredAtom2343 chi ∧
      ¬Fin15AnchoredAtom0671 chi) ∨
      (Fin15AnchoredAtom2343 chi ∧
      ¬Fin15AnchoredAtom1342 chi))) ∨
      (((¬Fin15AnchoredAtom2343 chi ∧
      Fin15AnchoredAtom0601 chi ∧
      Fin15AnchoredAtom0609 chi ∧
      Fin15AnchoredAtom0626 chi ∧
      Fin15AnchoredAtom0671 chi ∧
      Fin15AnchoredAtom1342 chi) ∨
      (Fin15AnchoredAtom2344 chi ∧
      ¬Fin15AnchoredAtom0602 chi)) ∨
      ((Fin15AnchoredAtom2344 chi ∧
      ¬Fin15AnchoredAtom0603 chi) ∨
      (Fin15AnchoredAtom2344 chi ∧
      ¬Fin15AnchoredAtom0627 chi)))))) ∨
      ((((((Fin15AnchoredAtom2344 chi ∧
      ¬Fin15AnchoredAtom0672 chi) ∨
      (Fin15AnchoredAtom2344 chi ∧
      ¬Fin15AnchoredAtom1343 chi)) ∨
      ((¬Fin15AnchoredAtom2344 chi ∧
      Fin15AnchoredAtom0602 chi ∧
      Fin15AnchoredAtom0603 chi ∧
      Fin15AnchoredAtom0627 chi ∧
      Fin15AnchoredAtom0672 chi ∧
      Fin15AnchoredAtom1343 chi) ∨
      (Fin15AnchoredAtom2345 chi ∧
      ¬Fin15AnchoredAtom0602 chi))) ∨
      (((Fin15AnchoredAtom2345 chi ∧
      ¬Fin15AnchoredAtom0604 chi) ∨
      (Fin15AnchoredAtom2345 chi ∧
      ¬Fin15AnchoredAtom0628 chi)) ∨
      ((Fin15AnchoredAtom2345 chi ∧
      ¬Fin15AnchoredAtom0673 chi) ∨
      (Fin15AnchoredAtom2345 chi ∧
      ¬Fin15AnchoredAtom1344 chi)))) ∨
      ((((¬Fin15AnchoredAtom2345 chi ∧
      Fin15AnchoredAtom0602 chi ∧
      Fin15AnchoredAtom0604 chi ∧
      Fin15AnchoredAtom0628 chi ∧
      Fin15AnchoredAtom0673 chi ∧
      Fin15AnchoredAtom1344 chi) ∨
      (Fin15AnchoredAtom2346 chi ∧
      ¬Fin15AnchoredAtom0602 chi)) ∨
      ((Fin15AnchoredAtom2346 chi ∧
      ¬Fin15AnchoredAtom0605 chi) ∨
      (Fin15AnchoredAtom2346 chi ∧
      ¬Fin15AnchoredAtom0629 chi))) ∨
      (((Fin15AnchoredAtom2346 chi ∧
      ¬Fin15AnchoredAtom0674 chi) ∨
      (Fin15AnchoredAtom2346 chi ∧
      ¬Fin15AnchoredAtom1345 chi)) ∨
      ((¬Fin15AnchoredAtom2346 chi ∧
      Fin15AnchoredAtom0602 chi ∧
      Fin15AnchoredAtom0605 chi ∧
      Fin15AnchoredAtom0629 chi ∧
      Fin15AnchoredAtom0674 chi ∧
      Fin15AnchoredAtom1345 chi) ∨
      (Fin15AnchoredAtom2347 chi ∧
      ¬Fin15AnchoredAtom0602 chi))))) ∨
      (((((Fin15AnchoredAtom2347 chi ∧
      ¬Fin15AnchoredAtom0606 chi) ∨
      (Fin15AnchoredAtom2347 chi ∧
      ¬Fin15AnchoredAtom0630 chi)) ∨
      ((Fin15AnchoredAtom2347 chi ∧
      ¬Fin15AnchoredAtom0675 chi) ∨
      (Fin15AnchoredAtom2347 chi ∧
      ¬Fin15AnchoredAtom1346 chi))) ∨
      (((¬Fin15AnchoredAtom2347 chi ∧
      Fin15AnchoredAtom0602 chi ∧
      Fin15AnchoredAtom0606 chi ∧
      Fin15AnchoredAtom0630 chi ∧
      Fin15AnchoredAtom0675 chi ∧
      Fin15AnchoredAtom1346 chi) ∨
      (Fin15AnchoredAtom2348 chi ∧
      ¬Fin15AnchoredAtom0602 chi)) ∨
      ((Fin15AnchoredAtom2348 chi ∧
      ¬Fin15AnchoredAtom0607 chi) ∨
      (Fin15AnchoredAtom2348 chi ∧
      ¬Fin15AnchoredAtom0631 chi)))) ∨
      ((((Fin15AnchoredAtom2348 chi ∧
      ¬Fin15AnchoredAtom0676 chi) ∨
      (Fin15AnchoredAtom2348 chi ∧
      ¬Fin15AnchoredAtom1347 chi)) ∨
      ((¬Fin15AnchoredAtom2348 chi ∧
      Fin15AnchoredAtom0602 chi ∧
      Fin15AnchoredAtom0607 chi ∧
      Fin15AnchoredAtom0631 chi ∧
      Fin15AnchoredAtom0676 chi ∧
      Fin15AnchoredAtom1347 chi) ∨
      (Fin15AnchoredAtom2349 chi ∧
      ¬Fin15AnchoredAtom0602 chi))) ∨
      (((Fin15AnchoredAtom2349 chi ∧
      ¬Fin15AnchoredAtom0608 chi) ∨
      (Fin15AnchoredAtom2349 chi ∧
      ¬Fin15AnchoredAtom0632 chi)) ∨
      ((Fin15AnchoredAtom2349 chi ∧
      ¬Fin15AnchoredAtom0677 chi) ∨
      (Fin15AnchoredAtom2349 chi ∧
      ¬Fin15AnchoredAtom1348 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom2349 chi ∧
      Fin15AnchoredAtom0602 chi ∧
      Fin15AnchoredAtom0608 chi ∧
      Fin15AnchoredAtom0632 chi ∧
      Fin15AnchoredAtom0677 chi ∧
      Fin15AnchoredAtom1348 chi) ∨
      ((Fin15AnchoredAtom2350 chi ∧
      ¬Fin15AnchoredAtom0602 chi) ∨
      (Fin15AnchoredAtom2350 chi ∧
      ¬Fin15AnchoredAtom0609 chi))) ∨
      (((Fin15AnchoredAtom2350 chi ∧
      ¬Fin15AnchoredAtom0633 chi) ∨
      (Fin15AnchoredAtom2350 chi ∧
      ¬Fin15AnchoredAtom0678 chi)) ∨
      ((Fin15AnchoredAtom2350 chi ∧
      ¬Fin15AnchoredAtom1349 chi) ∨
      (¬Fin15AnchoredAtom2350 chi ∧
      Fin15AnchoredAtom0602 chi ∧
      Fin15AnchoredAtom0609 chi ∧
      Fin15AnchoredAtom0633 chi ∧
      Fin15AnchoredAtom0678 chi ∧
      Fin15AnchoredAtom1349 chi)))) ∨
      ((((Fin15AnchoredAtom2351 chi ∧
      ¬Fin15AnchoredAtom0603 chi) ∨
      (Fin15AnchoredAtom2351 chi ∧
      ¬Fin15AnchoredAtom0604 chi)) ∨
      ((Fin15AnchoredAtom2351 chi ∧
      ¬Fin15AnchoredAtom0634 chi) ∨
      (Fin15AnchoredAtom2351 chi ∧
      ¬Fin15AnchoredAtom0679 chi))) ∨
      (((Fin15AnchoredAtom2351 chi ∧
      ¬Fin15AnchoredAtom1350 chi) ∨
      (¬Fin15AnchoredAtom2351 chi ∧
      Fin15AnchoredAtom0603 chi ∧
      Fin15AnchoredAtom0604 chi ∧
      Fin15AnchoredAtom0634 chi ∧
      Fin15AnchoredAtom0679 chi ∧
      Fin15AnchoredAtom1350 chi)) ∨
      ((Fin15AnchoredAtom2352 chi ∧
      ¬Fin15AnchoredAtom0603 chi) ∨
      (Fin15AnchoredAtom2352 chi ∧
      ¬Fin15AnchoredAtom0605 chi))))) ∨
      (((((Fin15AnchoredAtom2352 chi ∧
      ¬Fin15AnchoredAtom0635 chi) ∨
      (Fin15AnchoredAtom2352 chi ∧
      ¬Fin15AnchoredAtom0680 chi)) ∨
      ((Fin15AnchoredAtom2352 chi ∧
      ¬Fin15AnchoredAtom1351 chi) ∨
      (¬Fin15AnchoredAtom2352 chi ∧
      Fin15AnchoredAtom0603 chi ∧
      Fin15AnchoredAtom0605 chi ∧
      Fin15AnchoredAtom0635 chi ∧
      Fin15AnchoredAtom0680 chi ∧
      Fin15AnchoredAtom1351 chi))) ∨
      (((Fin15AnchoredAtom2354 chi ∧
      ¬Fin15AnchoredAtom0603 chi) ∨
      (Fin15AnchoredAtom2354 chi ∧
      ¬Fin15AnchoredAtom0607 chi)) ∨
      ((Fin15AnchoredAtom2354 chi ∧
      ¬Fin15AnchoredAtom0637 chi) ∨
      (Fin15AnchoredAtom2354 chi ∧
      ¬Fin15AnchoredAtom0682 chi)))) ∨
      ((((Fin15AnchoredAtom2354 chi ∧
      ¬Fin15AnchoredAtom1353 chi) ∨
      (¬Fin15AnchoredAtom2354 chi ∧
      Fin15AnchoredAtom0603 chi ∧
      Fin15AnchoredAtom0607 chi ∧
      Fin15AnchoredAtom0637 chi ∧
      Fin15AnchoredAtom0682 chi ∧
      Fin15AnchoredAtom1353 chi)) ∨
      ((Fin15AnchoredAtom2355 chi ∧
      ¬Fin15AnchoredAtom0603 chi) ∨
      (Fin15AnchoredAtom2355 chi ∧
      ¬Fin15AnchoredAtom0608 chi))) ∨
      (((Fin15AnchoredAtom2355 chi ∧
      ¬Fin15AnchoredAtom0638 chi) ∨
      (Fin15AnchoredAtom2355 chi ∧
      ¬Fin15AnchoredAtom0683 chi)) ∨
      ((Fin15AnchoredAtom2355 chi ∧
      ¬Fin15AnchoredAtom1354 chi) ∨
      (¬Fin15AnchoredAtom2355 chi ∧
      Fin15AnchoredAtom0603 chi ∧
      Fin15AnchoredAtom0608 chi ∧
      Fin15AnchoredAtom0638 chi ∧
      Fin15AnchoredAtom0683 chi ∧
      Fin15AnchoredAtom1354 chi)))))) ∨
      ((((((Fin15AnchoredAtom2356 chi ∧
      ¬Fin15AnchoredAtom0603 chi) ∨
      (Fin15AnchoredAtom2356 chi ∧
      ¬Fin15AnchoredAtom0609 chi)) ∨
      ((Fin15AnchoredAtom2356 chi ∧
      ¬Fin15AnchoredAtom0639 chi) ∨
      (Fin15AnchoredAtom2356 chi ∧
      ¬Fin15AnchoredAtom0684 chi))) ∨
      (((Fin15AnchoredAtom2356 chi ∧
      ¬Fin15AnchoredAtom1355 chi) ∨
      (¬Fin15AnchoredAtom2356 chi ∧
      Fin15AnchoredAtom0603 chi ∧
      Fin15AnchoredAtom0609 chi ∧
      Fin15AnchoredAtom0639 chi ∧
      Fin15AnchoredAtom0684 chi ∧
      Fin15AnchoredAtom1355 chi)) ∨
      ((Fin15AnchoredAtom2357 chi ∧
      ¬Fin15AnchoredAtom0604 chi) ∨
      (Fin15AnchoredAtom2357 chi ∧
      ¬Fin15AnchoredAtom0605 chi)))) ∨
      ((((Fin15AnchoredAtom2357 chi ∧
      ¬Fin15AnchoredAtom0640 chi) ∨
      (Fin15AnchoredAtom2357 chi ∧
      ¬Fin15AnchoredAtom0685 chi)) ∨
      ((Fin15AnchoredAtom2357 chi ∧
      ¬Fin15AnchoredAtom1356 chi) ∨
      (¬Fin15AnchoredAtom2357 chi ∧
      Fin15AnchoredAtom0604 chi ∧
      Fin15AnchoredAtom0605 chi ∧
      Fin15AnchoredAtom0640 chi ∧
      Fin15AnchoredAtom0685 chi ∧
      Fin15AnchoredAtom1356 chi))) ∨
      (((Fin15AnchoredAtom2358 chi ∧
      ¬Fin15AnchoredAtom0604 chi) ∨
      (Fin15AnchoredAtom2358 chi ∧
      ¬Fin15AnchoredAtom0686 chi)) ∨
      ((Fin15AnchoredAtom2358 chi ∧
      ¬Fin15AnchoredAtom1357 chi) ∨
      (¬Fin15AnchoredAtom2358 chi ∧
      Fin15AnchoredAtom0604 chi ∧
      Fin15AnchoredAtom0606 chi ∧
      Fin15AnchoredAtom0641 chi ∧
      Fin15AnchoredAtom0686 chi ∧
      Fin15AnchoredAtom1357 chi))))) ∨
      (((((Fin15AnchoredAtom2359 chi ∧
      ¬Fin15AnchoredAtom0604 chi) ∨
      (Fin15AnchoredAtom2359 chi ∧
      ¬Fin15AnchoredAtom0607 chi)) ∨
      ((Fin15AnchoredAtom2359 chi ∧
      ¬Fin15AnchoredAtom0642 chi) ∨
      (Fin15AnchoredAtom2359 chi ∧
      ¬Fin15AnchoredAtom0687 chi))) ∨
      (((Fin15AnchoredAtom2359 chi ∧
      ¬Fin15AnchoredAtom1358 chi) ∨
      (¬Fin15AnchoredAtom2359 chi ∧
      Fin15AnchoredAtom0604 chi ∧
      Fin15AnchoredAtom0607 chi ∧
      Fin15AnchoredAtom0642 chi ∧
      Fin15AnchoredAtom0687 chi ∧
      Fin15AnchoredAtom1358 chi)) ∨
      ((Fin15AnchoredAtom2360 chi ∧
      ¬Fin15AnchoredAtom0604 chi) ∨
      (Fin15AnchoredAtom2360 chi ∧
      ¬Fin15AnchoredAtom0608 chi)))) ∨
      ((((Fin15AnchoredAtom2360 chi ∧
      ¬Fin15AnchoredAtom0643 chi) ∨
      (Fin15AnchoredAtom2360 chi ∧
      ¬Fin15AnchoredAtom0688 chi)) ∨
      ((Fin15AnchoredAtom2360 chi ∧
      ¬Fin15AnchoredAtom1359 chi) ∨
      (¬Fin15AnchoredAtom2360 chi ∧
      Fin15AnchoredAtom0604 chi ∧
      Fin15AnchoredAtom0608 chi ∧
      Fin15AnchoredAtom0643 chi ∧
      Fin15AnchoredAtom0688 chi ∧
      Fin15AnchoredAtom1359 chi))) ∨
      (((Fin15AnchoredAtom2361 chi ∧
      ¬Fin15AnchoredAtom0604 chi) ∨
      (Fin15AnchoredAtom2361 chi ∧
      ¬Fin15AnchoredAtom0609 chi)) ∨
      ((Fin15AnchoredAtom2361 chi ∧
      ¬Fin15AnchoredAtom0644 chi) ∨
      (Fin15AnchoredAtom2361 chi ∧
      ¬Fin15AnchoredAtom0689 chi)))))))) ∨
      (((((((Fin15AnchoredAtom2361 chi ∧
      ¬Fin15AnchoredAtom1360 chi) ∨
      ((¬Fin15AnchoredAtom2361 chi ∧
      Fin15AnchoredAtom0604 chi ∧
      Fin15AnchoredAtom0609 chi ∧
      Fin15AnchoredAtom0644 chi ∧
      Fin15AnchoredAtom0689 chi ∧
      Fin15AnchoredAtom1360 chi) ∨
      (Fin15AnchoredAtom2362 chi ∧
      ¬Fin15AnchoredAtom0605 chi))) ∨
      (((Fin15AnchoredAtom2362 chi ∧
      ¬Fin15AnchoredAtom0690 chi) ∨
      (Fin15AnchoredAtom2363 chi ∧
      ¬Fin15AnchoredAtom0605 chi)) ∨
      ((Fin15AnchoredAtom2363 chi ∧
      ¬Fin15AnchoredAtom0607 chi) ∨
      (Fin15AnchoredAtom2363 chi ∧
      ¬Fin15AnchoredAtom0646 chi)))) ∨
      ((((Fin15AnchoredAtom2363 chi ∧
      ¬Fin15AnchoredAtom0691 chi) ∨
      (Fin15AnchoredAtom2363 chi ∧
      ¬Fin15AnchoredAtom1362 chi)) ∨
      ((¬Fin15AnchoredAtom2363 chi ∧
      Fin15AnchoredAtom0605 chi ∧
      Fin15AnchoredAtom0607 chi ∧
      Fin15AnchoredAtom0646 chi ∧
      Fin15AnchoredAtom0691 chi ∧
      Fin15AnchoredAtom1362 chi) ∨
      (Fin15AnchoredAtom2364 chi ∧
      ¬Fin15AnchoredAtom0605 chi))) ∨
      (((Fin15AnchoredAtom2364 chi ∧
      ¬Fin15AnchoredAtom0608 chi) ∨
      (Fin15AnchoredAtom2364 chi ∧
      ¬Fin15AnchoredAtom0647 chi)) ∨
      ((Fin15AnchoredAtom2364 chi ∧
      ¬Fin15AnchoredAtom0692 chi) ∨
      (Fin15AnchoredAtom2364 chi ∧
      ¬Fin15AnchoredAtom1363 chi))))) ∨
      (((((¬Fin15AnchoredAtom2364 chi ∧
      Fin15AnchoredAtom0605 chi ∧
      Fin15AnchoredAtom0608 chi ∧
      Fin15AnchoredAtom0647 chi ∧
      Fin15AnchoredAtom0692 chi ∧
      Fin15AnchoredAtom1363 chi) ∨
      (Fin15AnchoredAtom2365 chi ∧
      ¬Fin15AnchoredAtom0605 chi)) ∨
      ((Fin15AnchoredAtom2365 chi ∧
      ¬Fin15AnchoredAtom0609 chi) ∨
      (Fin15AnchoredAtom2365 chi ∧
      ¬Fin15AnchoredAtom0648 chi))) ∨
      (((Fin15AnchoredAtom2365 chi ∧
      ¬Fin15AnchoredAtom0693 chi) ∨
      (Fin15AnchoredAtom2365 chi ∧
      ¬Fin15AnchoredAtom1364 chi)) ∨
      ((¬Fin15AnchoredAtom2365 chi ∧
      Fin15AnchoredAtom0605 chi ∧
      Fin15AnchoredAtom0609 chi ∧
      Fin15AnchoredAtom0648 chi ∧
      Fin15AnchoredAtom0693 chi ∧
      Fin15AnchoredAtom1364 chi) ∨
      (Fin15AnchoredAtom2366 chi ∧
      ¬Fin15AnchoredAtom0606 chi)))) ∨
      ((((Fin15AnchoredAtom2366 chi ∧
      ¬Fin15AnchoredAtom0607 chi) ∨
      (Fin15AnchoredAtom2366 chi ∧
      ¬Fin15AnchoredAtom0694 chi)) ∨
      ((Fin15AnchoredAtom2366 chi ∧
      ¬Fin15AnchoredAtom1365 chi) ∨
      (¬Fin15AnchoredAtom2366 chi ∧
      Fin15AnchoredAtom0606 chi ∧
      Fin15AnchoredAtom0607 chi ∧
      Fin15AnchoredAtom0649 chi ∧
      Fin15AnchoredAtom0694 chi ∧
      Fin15AnchoredAtom1365 chi))) ∨
      (((Fin15AnchoredAtom2367 chi ∧
      ¬Fin15AnchoredAtom0608 chi) ∨
      (Fin15AnchoredAtom2368 chi ∧
      ¬Fin15AnchoredAtom0609 chi)) ∨
      ((Fin15AnchoredAtom2369 chi ∧
      ¬Fin15AnchoredAtom0607 chi) ∨
      (Fin15AnchoredAtom2369 chi ∧
      ¬Fin15AnchoredAtom0608 chi)))))) ∨
      ((((((Fin15AnchoredAtom2369 chi ∧
      ¬Fin15AnchoredAtom0652 chi) ∨
      (Fin15AnchoredAtom2369 chi ∧
      ¬Fin15AnchoredAtom0697 chi)) ∨
      ((Fin15AnchoredAtom2369 chi ∧
      ¬Fin15AnchoredAtom1368 chi) ∨
      (¬Fin15AnchoredAtom2369 chi ∧
      Fin15AnchoredAtom0607 chi ∧
      Fin15AnchoredAtom0608 chi ∧
      Fin15AnchoredAtom0652 chi ∧
      Fin15AnchoredAtom0697 chi ∧
      Fin15AnchoredAtom1368 chi))) ∨
      (((Fin15AnchoredAtom2370 chi ∧
      ¬Fin15AnchoredAtom0607 chi) ∨
      (Fin15AnchoredAtom2370 chi ∧
      ¬Fin15AnchoredAtom0609 chi)) ∨
      ((Fin15AnchoredAtom2370 chi ∧
      ¬Fin15AnchoredAtom0653 chi) ∨
      (Fin15AnchoredAtom2370 chi ∧
      ¬Fin15AnchoredAtom0698 chi)))) ∨
      ((((Fin15AnchoredAtom2370 chi ∧
      ¬Fin15AnchoredAtom1369 chi) ∨
      (¬Fin15AnchoredAtom2370 chi ∧
      Fin15AnchoredAtom0607 chi ∧
      Fin15AnchoredAtom0609 chi ∧
      Fin15AnchoredAtom0653 chi ∧
      Fin15AnchoredAtom0698 chi ∧
      Fin15AnchoredAtom1369 chi)) ∨
      ((Fin15AnchoredAtom2371 chi ∧
      ¬Fin15AnchoredAtom0608 chi) ∨
      (Fin15AnchoredAtom2371 chi ∧
      ¬Fin15AnchoredAtom0609 chi))) ∨
      (((Fin15AnchoredAtom2371 chi ∧
      ¬Fin15AnchoredAtom0654 chi) ∨
      (Fin15AnchoredAtom2371 chi ∧
      ¬Fin15AnchoredAtom0699 chi)) ∨
      ((Fin15AnchoredAtom2371 chi ∧
      ¬Fin15AnchoredAtom1370 chi) ∨
      (¬Fin15AnchoredAtom2371 chi ∧
      Fin15AnchoredAtom0608 chi ∧
      Fin15AnchoredAtom0609 chi ∧
      Fin15AnchoredAtom0654 chi ∧
      Fin15AnchoredAtom0699 chi ∧
      Fin15AnchoredAtom1370 chi))))) ∨
      (((((Fin15AnchoredAtom2372 chi ∧
      ¬Fin15AnchoredAtom0610 chi) ∨
      (Fin15AnchoredAtom2372 chi ∧
      ¬Fin15AnchoredAtom0611 chi)) ∨
      ((Fin15AnchoredAtom2372 chi ∧
      ¬Fin15AnchoredAtom0619 chi) ∨
      (Fin15AnchoredAtom2372 chi ∧
      ¬Fin15AnchoredAtom0700 chi))) ∨
      (((Fin15AnchoredAtom2372 chi ∧
      ¬Fin15AnchoredAtom1371 chi) ∨
      (¬Fin15AnchoredAtom2372 chi ∧
      Fin15AnchoredAtom0610 chi ∧
      Fin15AnchoredAtom0611 chi ∧
      Fin15AnchoredAtom0619 chi ∧
      Fin15AnchoredAtom0700 chi ∧
      Fin15AnchoredAtom1371 chi)) ∨
      ((Fin15AnchoredAtom2373 chi ∧
      ¬Fin15AnchoredAtom0610 chi) ∨
      (Fin15AnchoredAtom2373 chi ∧
      ¬Fin15AnchoredAtom0612 chi)))) ∨
      ((((Fin15AnchoredAtom2373 chi ∧
      ¬Fin15AnchoredAtom0620 chi) ∨
      (Fin15AnchoredAtom2373 chi ∧
      ¬Fin15AnchoredAtom0701 chi)) ∨
      ((Fin15AnchoredAtom2373 chi ∧
      ¬Fin15AnchoredAtom1372 chi) ∨
      (¬Fin15AnchoredAtom2373 chi ∧
      Fin15AnchoredAtom0610 chi ∧
      Fin15AnchoredAtom0612 chi ∧
      Fin15AnchoredAtom0620 chi ∧
      Fin15AnchoredAtom0701 chi ∧
      Fin15AnchoredAtom1372 chi))) ∨
      (((Fin15AnchoredAtom2374 chi ∧
      ¬Fin15AnchoredAtom0610 chi) ∨
      (Fin15AnchoredAtom2374 chi ∧
      ¬Fin15AnchoredAtom0613 chi)) ∨
      ((Fin15AnchoredAtom2374 chi ∧
      ¬Fin15AnchoredAtom0621 chi) ∨
      (Fin15AnchoredAtom2374 chi ∧
      ¬Fin15AnchoredAtom0702 chi))))))) ∨
      (((((((Fin15AnchoredAtom2374 chi ∧
      ¬Fin15AnchoredAtom1373 chi) ∨
      (¬Fin15AnchoredAtom2374 chi ∧
      Fin15AnchoredAtom0610 chi ∧
      Fin15AnchoredAtom0613 chi ∧
      Fin15AnchoredAtom0621 chi ∧
      Fin15AnchoredAtom0702 chi ∧
      Fin15AnchoredAtom1373 chi)) ∨
      ((Fin15AnchoredAtom2375 chi ∧
      ¬Fin15AnchoredAtom0610 chi) ∨
      (Fin15AnchoredAtom2375 chi ∧
      ¬Fin15AnchoredAtom0614 chi))) ∨
      (((Fin15AnchoredAtom2375 chi ∧
      ¬Fin15AnchoredAtom0622 chi) ∨
      (Fin15AnchoredAtom2375 chi ∧
      ¬Fin15AnchoredAtom0703 chi)) ∨
      ((Fin15AnchoredAtom2375 chi ∧
      ¬Fin15AnchoredAtom1374 chi) ∨
      (¬Fin15AnchoredAtom2375 chi ∧
      Fin15AnchoredAtom0610 chi ∧
      Fin15AnchoredAtom0614 chi ∧
      Fin15AnchoredAtom0622 chi ∧
      Fin15AnchoredAtom0703 chi ∧
      Fin15AnchoredAtom1374 chi)))) ∨
      ((((Fin15AnchoredAtom2376 chi ∧
      ¬Fin15AnchoredAtom0704 chi) ∨
      (Fin15AnchoredAtom2376 chi ∧
      ¬Fin15AnchoredAtom1375 chi)) ∨
      ((¬Fin15AnchoredAtom2376 chi ∧
      Fin15AnchoredAtom0610 chi ∧
      Fin15AnchoredAtom0615 chi ∧
      Fin15AnchoredAtom0623 chi ∧
      Fin15AnchoredAtom0704 chi ∧
      Fin15AnchoredAtom1375 chi) ∨
      (Fin15AnchoredAtom2377 chi ∧
      ¬Fin15AnchoredAtom0610 chi))) ∨
      (((Fin15AnchoredAtom2377 chi ∧
      ¬Fin15AnchoredAtom0616 chi) ∨
      (Fin15AnchoredAtom2377 chi ∧
      ¬Fin15AnchoredAtom0624 chi)) ∨
      ((Fin15AnchoredAtom2377 chi ∧
      ¬Fin15AnchoredAtom0705 chi) ∨
      (Fin15AnchoredAtom2377 chi ∧
      ¬Fin15AnchoredAtom1376 chi))))) ∨
      (((((¬Fin15AnchoredAtom2377 chi ∧
      Fin15AnchoredAtom0610 chi ∧
      Fin15AnchoredAtom0616 chi ∧
      Fin15AnchoredAtom0624 chi ∧
      Fin15AnchoredAtom0705 chi ∧
      Fin15AnchoredAtom1376 chi) ∨
      (Fin15AnchoredAtom2378 chi ∧
      ¬Fin15AnchoredAtom0610 chi)) ∨
      ((Fin15AnchoredAtom2378 chi ∧
      ¬Fin15AnchoredAtom0617 chi) ∨
      (Fin15AnchoredAtom2378 chi ∧
      ¬Fin15AnchoredAtom0625 chi))) ∨
      (((Fin15AnchoredAtom2378 chi ∧
      ¬Fin15AnchoredAtom0706 chi) ∨
      (Fin15AnchoredAtom2378 chi ∧
      ¬Fin15AnchoredAtom1377 chi)) ∨
      ((¬Fin15AnchoredAtom2378 chi ∧
      Fin15AnchoredAtom0610 chi ∧
      Fin15AnchoredAtom0617 chi ∧
      Fin15AnchoredAtom0625 chi ∧
      Fin15AnchoredAtom0706 chi ∧
      Fin15AnchoredAtom1377 chi) ∨
      (Fin15AnchoredAtom2379 chi ∧
      ¬Fin15AnchoredAtom0610 chi)))) ∨
      ((((Fin15AnchoredAtom2379 chi ∧
      ¬Fin15AnchoredAtom0618 chi) ∨
      (Fin15AnchoredAtom2379 chi ∧
      ¬Fin15AnchoredAtom0626 chi)) ∨
      ((Fin15AnchoredAtom2379 chi ∧
      ¬Fin15AnchoredAtom0707 chi) ∨
      (Fin15AnchoredAtom2379 chi ∧
      ¬Fin15AnchoredAtom1378 chi))) ∨
      (((¬Fin15AnchoredAtom2379 chi ∧
      Fin15AnchoredAtom0610 chi ∧
      Fin15AnchoredAtom0618 chi ∧
      Fin15AnchoredAtom0626 chi ∧
      Fin15AnchoredAtom0707 chi ∧
      Fin15AnchoredAtom1378 chi) ∨
      (Fin15AnchoredAtom2380 chi ∧
      ¬Fin15AnchoredAtom0611 chi)) ∨
      ((Fin15AnchoredAtom2380 chi ∧
      ¬Fin15AnchoredAtom0612 chi) ∨
      (Fin15AnchoredAtom2380 chi ∧
      ¬Fin15AnchoredAtom0627 chi)))))) ∨
      ((((((Fin15AnchoredAtom2380 chi ∧
      ¬Fin15AnchoredAtom0708 chi) ∨
      (Fin15AnchoredAtom2380 chi ∧
      ¬Fin15AnchoredAtom1379 chi)) ∨
      ((¬Fin15AnchoredAtom2380 chi ∧
      Fin15AnchoredAtom0611 chi ∧
      Fin15AnchoredAtom0612 chi ∧
      Fin15AnchoredAtom0627 chi ∧
      Fin15AnchoredAtom0708 chi ∧
      Fin15AnchoredAtom1379 chi) ∨
      (Fin15AnchoredAtom2381 chi ∧
      ¬Fin15AnchoredAtom0611 chi))) ∨
      (((Fin15AnchoredAtom2381 chi ∧
      ¬Fin15AnchoredAtom0613 chi) ∨
      (Fin15AnchoredAtom2381 chi ∧
      ¬Fin15AnchoredAtom0628 chi)) ∨
      ((Fin15AnchoredAtom2381 chi ∧
      ¬Fin15AnchoredAtom0709 chi) ∨
      (Fin15AnchoredAtom2381 chi ∧
      ¬Fin15AnchoredAtom1380 chi)))) ∨
      ((((¬Fin15AnchoredAtom2381 chi ∧
      Fin15AnchoredAtom0611 chi ∧
      Fin15AnchoredAtom0613 chi ∧
      Fin15AnchoredAtom0628 chi ∧
      Fin15AnchoredAtom0709 chi ∧
      Fin15AnchoredAtom1380 chi) ∨
      (Fin15AnchoredAtom2382 chi ∧
      ¬Fin15AnchoredAtom0611 chi)) ∨
      ((Fin15AnchoredAtom2382 chi ∧
      ¬Fin15AnchoredAtom0614 chi) ∨
      (Fin15AnchoredAtom2382 chi ∧
      ¬Fin15AnchoredAtom0629 chi))) ∨
      (((Fin15AnchoredAtom2382 chi ∧
      ¬Fin15AnchoredAtom0710 chi) ∨
      (Fin15AnchoredAtom2382 chi ∧
      ¬Fin15AnchoredAtom1381 chi)) ∨
      ((¬Fin15AnchoredAtom2382 chi ∧
      Fin15AnchoredAtom0611 chi ∧
      Fin15AnchoredAtom0614 chi ∧
      Fin15AnchoredAtom0629 chi ∧
      Fin15AnchoredAtom0710 chi ∧
      Fin15AnchoredAtom1381 chi) ∨
      (Fin15AnchoredAtom2383 chi ∧
      ¬Fin15AnchoredAtom0611 chi))))) ∨
      (((((Fin15AnchoredAtom2383 chi ∧
      ¬Fin15AnchoredAtom0615 chi) ∨
      (Fin15AnchoredAtom2383 chi ∧
      ¬Fin15AnchoredAtom0630 chi)) ∨
      ((Fin15AnchoredAtom2383 chi ∧
      ¬Fin15AnchoredAtom0711 chi) ∨
      (Fin15AnchoredAtom2383 chi ∧
      ¬Fin15AnchoredAtom1382 chi))) ∨
      (((Fin15AnchoredAtom2384 chi ∧
      ¬Fin15AnchoredAtom0611 chi) ∨
      (Fin15AnchoredAtom2384 chi ∧
      ¬Fin15AnchoredAtom0616 chi)) ∨
      ((Fin15AnchoredAtom2384 chi ∧
      ¬Fin15AnchoredAtom0631 chi) ∨
      (Fin15AnchoredAtom2384 chi ∧
      ¬Fin15AnchoredAtom0712 chi)))) ∨
      ((((Fin15AnchoredAtom2384 chi ∧
      ¬Fin15AnchoredAtom1383 chi) ∨
      (¬Fin15AnchoredAtom2384 chi ∧
      Fin15AnchoredAtom0611 chi ∧
      Fin15AnchoredAtom0616 chi ∧
      Fin15AnchoredAtom0631 chi ∧
      Fin15AnchoredAtom0712 chi ∧
      Fin15AnchoredAtom1383 chi)) ∨
      ((Fin15AnchoredAtom2385 chi ∧
      ¬Fin15AnchoredAtom0611 chi) ∨
      (Fin15AnchoredAtom2385 chi ∧
      ¬Fin15AnchoredAtom0617 chi))) ∨
      (((Fin15AnchoredAtom2385 chi ∧
      ¬Fin15AnchoredAtom0632 chi) ∨
      (Fin15AnchoredAtom2385 chi ∧
      ¬Fin15AnchoredAtom0713 chi)) ∨
      ((Fin15AnchoredAtom2385 chi ∧
      ¬Fin15AnchoredAtom1384 chi) ∨
      (¬Fin15AnchoredAtom2385 chi ∧
      Fin15AnchoredAtom0611 chi ∧
      Fin15AnchoredAtom0617 chi ∧
      Fin15AnchoredAtom0632 chi ∧
      Fin15AnchoredAtom0713 chi ∧
      Fin15AnchoredAtom1384 chi)))))))))) := by
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
                exact fin15Anchored_clause17920 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17921 chi hbad
                ·
                  exact fin15Anchored_clause17922 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17923 chi hbad
                ·
                  exact fin15Anchored_clause17924 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17925 chi hbad
                ·
                  exact fin15Anchored_clause17926 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17927 chi hbad
                ·
                  exact fin15Anchored_clause17928 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17929 chi hbad
                ·
                  exact fin15Anchored_clause17930 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17931 chi hbad
                ·
                  exact fin15Anchored_clause17932 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17933 chi hbad
                ·
                  exact fin15Anchored_clause17934 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17935 chi hbad
                ·
                  exact fin15Anchored_clause17936 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17937 chi hbad
                ·
                  exact fin15Anchored_clause17938 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17939 chi hbad
                ·
                  exact fin15Anchored_clause17940 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17941 chi hbad
                ·
                  exact fin15Anchored_clause17942 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17943 chi hbad
                ·
                  exact fin15Anchored_clause17944 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17945 chi hbad
                ·
                  exact fin15Anchored_clause17946 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17947 chi hbad
                ·
                  exact fin15Anchored_clause17948 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17949 chi hbad
                ·
                  exact fin15Anchored_clause17950 chi hbad
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
                  exact fin15Anchored_clause17951 chi hbad
                ·
                  exact fin15Anchored_clause17952 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17953 chi hbad
                ·
                  exact fin15Anchored_clause17954 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17955 chi hbad
                ·
                  exact fin15Anchored_clause17956 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17957 chi hbad
                ·
                  exact fin15Anchored_clause17958 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17959 chi hbad
                ·
                  exact fin15Anchored_clause17960 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17961 chi hbad
                ·
                  exact fin15Anchored_clause17962 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17963 chi hbad
                ·
                  exact fin15Anchored_clause17964 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17965 chi hbad
                ·
                  exact fin15Anchored_clause17966 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17967 chi hbad
                ·
                  exact fin15Anchored_clause17968 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17969 chi hbad
                ·
                  exact fin15Anchored_clause17970 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17971 chi hbad
                ·
                  exact fin15Anchored_clause17972 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17973 chi hbad
                ·
                  exact fin15Anchored_clause17974 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17975 chi hbad
                ·
                  exact fin15Anchored_clause17976 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17977 chi hbad
                ·
                  exact fin15Anchored_clause17978 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17979 chi hbad
                ·
                  exact fin15Anchored_clause17980 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17981 chi hbad
                ·
                  exact fin15Anchored_clause17982 chi hbad
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
                exact fin15Anchored_clause17983 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17984 chi hbad
                ·
                  exact fin15Anchored_clause17985 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17986 chi hbad
                ·
                  exact fin15Anchored_clause17987 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17988 chi hbad
                ·
                  exact fin15Anchored_clause17989 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17990 chi hbad
                ·
                  exact fin15Anchored_clause17991 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17992 chi hbad
                ·
                  exact fin15Anchored_clause17993 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17994 chi hbad
                ·
                  exact fin15Anchored_clause17995 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17996 chi hbad
                ·
                  exact fin15Anchored_clause17997 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17998 chi hbad
                ·
                  exact fin15Anchored_clause17999 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18000 chi hbad
                ·
                  exact fin15Anchored_clause18001 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18002 chi hbad
                ·
                  exact fin15Anchored_clause18003 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18004 chi hbad
                ·
                  exact fin15Anchored_clause18005 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18006 chi hbad
                ·
                  exact fin15Anchored_clause18007 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18008 chi hbad
                ·
                  exact fin15Anchored_clause18009 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18010 chi hbad
                ·
                  exact fin15Anchored_clause18011 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18012 chi hbad
                ·
                  exact fin15Anchored_clause18013 chi hbad
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
                  exact fin15Anchored_clause18014 chi hbad
                ·
                  exact fin15Anchored_clause18015 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18016 chi hbad
                ·
                  exact fin15Anchored_clause18017 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18018 chi hbad
                ·
                  exact fin15Anchored_clause18019 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18020 chi hbad
                ·
                  exact fin15Anchored_clause18021 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18022 chi hbad
                ·
                  exact fin15Anchored_clause18023 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18024 chi hbad
                ·
                  exact fin15Anchored_clause18025 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18026 chi hbad
                ·
                  exact fin15Anchored_clause18027 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18028 chi hbad
                ·
                  exact fin15Anchored_clause18029 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18030 chi hbad
                ·
                  exact fin15Anchored_clause18031 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18032 chi hbad
                ·
                  exact fin15Anchored_clause18033 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18034 chi hbad
                ·
                  exact fin15Anchored_clause18035 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18036 chi hbad
                ·
                  exact fin15Anchored_clause18037 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18038 chi hbad
                ·
                  exact fin15Anchored_clause18039 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18040 chi hbad
                ·
                  exact fin15Anchored_clause18041 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18042 chi hbad
                ·
                  exact fin15Anchored_clause18043 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18044 chi hbad
                ·
                  exact fin15Anchored_clause18045 chi hbad
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
                exact fin15Anchored_clause18046 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18047 chi hbad
                ·
                  exact fin15Anchored_clause18048 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18049 chi hbad
                ·
                  exact fin15Anchored_clause18050 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18051 chi hbad
                ·
                  exact fin15Anchored_clause18052 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18053 chi hbad
                ·
                  exact fin15Anchored_clause18054 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18055 chi hbad
                ·
                  exact fin15Anchored_clause18056 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18057 chi hbad
                ·
                  exact fin15Anchored_clause18058 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18059 chi hbad
                ·
                  exact fin15Anchored_clause18060 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18061 chi hbad
                ·
                  exact fin15Anchored_clause18062 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18063 chi hbad
                ·
                  exact fin15Anchored_clause18064 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18065 chi hbad
                ·
                  exact fin15Anchored_clause18066 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18067 chi hbad
                ·
                  exact fin15Anchored_clause18068 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18069 chi hbad
                ·
                  exact fin15Anchored_clause18070 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18071 chi hbad
                ·
                  exact fin15Anchored_clause18072 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18073 chi hbad
                ·
                  exact fin15Anchored_clause18074 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18075 chi hbad
                ·
                  exact fin15Anchored_clause18076 chi hbad
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
                  exact fin15Anchored_clause18077 chi hbad
                ·
                  exact fin15Anchored_clause18078 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18079 chi hbad
                ·
                  exact fin15Anchored_clause18080 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18081 chi hbad
                ·
                  exact fin15Anchored_clause18082 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18083 chi hbad
                ·
                  exact fin15Anchored_clause18084 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18085 chi hbad
                ·
                  exact fin15Anchored_clause18086 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18087 chi hbad
                ·
                  exact fin15Anchored_clause18088 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18089 chi hbad
                ·
                  exact fin15Anchored_clause18090 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18091 chi hbad
                ·
                  exact fin15Anchored_clause18092 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18093 chi hbad
                ·
                  exact fin15Anchored_clause18094 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18095 chi hbad
                ·
                  exact fin15Anchored_clause18096 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18097 chi hbad
                ·
                  exact fin15Anchored_clause18098 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18099 chi hbad
                ·
                  exact fin15Anchored_clause18100 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18101 chi hbad
                ·
                  exact fin15Anchored_clause18102 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18103 chi hbad
                ·
                  exact fin15Anchored_clause18104 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18105 chi hbad
                ·
                  exact fin15Anchored_clause18106 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18107 chi hbad
                ·
                  exact fin15Anchored_clause18108 chi hbad
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
                  exact fin15Anchored_clause18109 chi hbad
                ·
                  exact fin15Anchored_clause18110 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18111 chi hbad
                ·
                  exact fin15Anchored_clause18112 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18113 chi hbad
                ·
                  exact fin15Anchored_clause18114 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18115 chi hbad
                ·
                  exact fin15Anchored_clause18116 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18117 chi hbad
                ·
                  exact fin15Anchored_clause18118 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18119 chi hbad
                ·
                  exact fin15Anchored_clause18120 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18121 chi hbad
                ·
                  exact fin15Anchored_clause18122 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18123 chi hbad
                ·
                  exact fin15Anchored_clause18124 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18125 chi hbad
                ·
                  exact fin15Anchored_clause18126 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18127 chi hbad
                ·
                  exact fin15Anchored_clause18128 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18129 chi hbad
                ·
                  exact fin15Anchored_clause18130 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18131 chi hbad
                ·
                  exact fin15Anchored_clause18132 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18133 chi hbad
                ·
                  exact fin15Anchored_clause18134 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18135 chi hbad
                ·
                  exact fin15Anchored_clause18136 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18137 chi hbad
                ·
                  exact fin15Anchored_clause18138 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18139 chi hbad
                ·
                  exact fin15Anchored_clause18140 chi hbad
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
                  exact fin15Anchored_clause18141 chi hbad
                ·
                  exact fin15Anchored_clause18142 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18143 chi hbad
                ·
                  exact fin15Anchored_clause18144 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18145 chi hbad
                ·
                  exact fin15Anchored_clause18146 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18147 chi hbad
                ·
                  exact fin15Anchored_clause18148 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18149 chi hbad
                ·
                  exact fin15Anchored_clause18150 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18151 chi hbad
                ·
                  exact fin15Anchored_clause18152 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18153 chi hbad
                ·
                  exact fin15Anchored_clause18154 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18155 chi hbad
                ·
                  exact fin15Anchored_clause18156 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18157 chi hbad
                ·
                  exact fin15Anchored_clause18158 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18159 chi hbad
                ·
                  exact fin15Anchored_clause18160 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18161 chi hbad
                ·
                  exact fin15Anchored_clause18162 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18163 chi hbad
                ·
                  exact fin15Anchored_clause18164 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18165 chi hbad
                ·
                  exact fin15Anchored_clause18166 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18167 chi hbad
                ·
                  exact fin15Anchored_clause18168 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18169 chi hbad
                ·
                  exact fin15Anchored_clause18170 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18171 chi hbad
                ·
                  exact fin15Anchored_clause18172 chi hbad

end ErdosSzekeres

end
