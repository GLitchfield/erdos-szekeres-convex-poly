module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk090
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk091

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 118. -/

theorem predecessorHalfFin13_rejectSemanticSegment118
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((PredecessorHalfFin13Atom0344 chi ∧
      PredecessorHalfFin13Atom0347 chi ∧
      PredecessorHalfFin13Atom0350 chi ∧
      PredecessorHalfFin13Atom0368 chi ∧
      PredecessorHalfFin13Atom0371 chi ∧
      PredecessorHalfFin13Atom0383 chi ∧
      PredecessorHalfFin13Atom0404 chi ∧
      PredecessorHalfFin13Atom0407 chi ∧
      PredecessorHalfFin13Atom0419 chi ∧
      PredecessorHalfFin13Atom0483 chi ∧
      PredecessorHalfFin13Atom0689 chi ∧
      PredecessorHalfFin13Atom0692 chi ∧
      PredecessorHalfFin13Atom0704 chi ∧
      PredecessorHalfFin13Atom0768 chi ∧
      PredecessorHalfFin13Atom0852 chi) ∨
      ((PredecessorHalfFin13Atom0344 chi ∧
      PredecessorHalfFin13Atom0348 chi ∧
      PredecessorHalfFin13Atom0350 chi ∧
      PredecessorHalfFin13Atom0369 chi ∧
      PredecessorHalfFin13Atom0371 chi ∧
      PredecessorHalfFin13Atom0385 chi ∧
      PredecessorHalfFin13Atom0405 chi ∧
      PredecessorHalfFin13Atom0407 chi ∧
      PredecessorHalfFin13Atom0421 chi ∧
      PredecessorHalfFin13Atom0485 chi ∧
      PredecessorHalfFin13Atom0690 chi ∧
      PredecessorHalfFin13Atom0692 chi ∧
      PredecessorHalfFin13Atom0706 chi ∧
      PredecessorHalfFin13Atom0770 chi ∧
      PredecessorHalfFin13Atom0854 chi) ∨
      (PredecessorHalfFin13Atom0345 chi ∧
      PredecessorHalfFin13Atom0346 chi ∧
      PredecessorHalfFin13Atom0347 chi ∧
      PredecessorHalfFin13Atom0372 chi ∧
      PredecessorHalfFin13Atom0373 chi ∧
      PredecessorHalfFin13Atom0377 chi ∧
      PredecessorHalfFin13Atom0408 chi ∧
      PredecessorHalfFin13Atom0409 chi ∧
      PredecessorHalfFin13Atom0413 chi ∧
      PredecessorHalfFin13Atom0487 chi ∧
      PredecessorHalfFin13Atom0693 chi ∧
      PredecessorHalfFin13Atom0694 chi ∧
      PredecessorHalfFin13Atom0698 chi ∧
      PredecessorHalfFin13Atom0772 chi ∧
      PredecessorHalfFin13Atom0856 chi))) ∨
      ((PredecessorHalfFin13Atom0345 chi ∧
      PredecessorHalfFin13Atom0346 chi ∧
      PredecessorHalfFin13Atom0348 chi ∧
      PredecessorHalfFin13Atom0372 chi ∧
      PredecessorHalfFin13Atom0374 chi ∧
      PredecessorHalfFin13Atom0378 chi ∧
      PredecessorHalfFin13Atom0408 chi ∧
      PredecessorHalfFin13Atom0410 chi ∧
      PredecessorHalfFin13Atom0414 chi ∧
      PredecessorHalfFin13Atom0488 chi ∧
      PredecessorHalfFin13Atom0693 chi ∧
      PredecessorHalfFin13Atom0695 chi ∧
      PredecessorHalfFin13Atom0699 chi ∧
      PredecessorHalfFin13Atom0773 chi ∧
      PredecessorHalfFin13Atom0857 chi) ∨
      ((PredecessorHalfFin13Atom0345 chi ∧
      PredecessorHalfFin13Atom0346 chi ∧
      PredecessorHalfFin13Atom0350 chi ∧
      PredecessorHalfFin13Atom0372 chi ∧
      PredecessorHalfFin13Atom0376 chi ∧
      PredecessorHalfFin13Atom0380 chi ∧
      PredecessorHalfFin13Atom0408 chi ∧
      PredecessorHalfFin13Atom0412 chi ∧
      PredecessorHalfFin13Atom0416 chi ∧
      PredecessorHalfFin13Atom0490 chi ∧
      PredecessorHalfFin13Atom0693 chi ∧
      PredecessorHalfFin13Atom0697 chi ∧
      PredecessorHalfFin13Atom0701 chi ∧
      PredecessorHalfFin13Atom0775 chi ∧
      PredecessorHalfFin13Atom0859 chi) ∨
      (PredecessorHalfFin13Atom0345 chi ∧
      PredecessorHalfFin13Atom0347 chi ∧
      PredecessorHalfFin13Atom0348 chi ∧
      PredecessorHalfFin13Atom0373 chi ∧
      PredecessorHalfFin13Atom0374 chi ∧
      PredecessorHalfFin13Atom0381 chi ∧
      PredecessorHalfFin13Atom0409 chi ∧
      PredecessorHalfFin13Atom0410 chi ∧
      PredecessorHalfFin13Atom0417 chi ∧
      PredecessorHalfFin13Atom0491 chi ∧
      PredecessorHalfFin13Atom0694 chi ∧
      PredecessorHalfFin13Atom0695 chi ∧
      PredecessorHalfFin13Atom0702 chi ∧
      PredecessorHalfFin13Atom0776 chi ∧
      PredecessorHalfFin13Atom0860 chi)))) ∨
      (((PredecessorHalfFin13Atom0345 chi ∧
      PredecessorHalfFin13Atom0347 chi ∧
      PredecessorHalfFin13Atom0350 chi ∧
      PredecessorHalfFin13Atom0373 chi ∧
      PredecessorHalfFin13Atom0376 chi ∧
      PredecessorHalfFin13Atom0383 chi ∧
      PredecessorHalfFin13Atom0409 chi ∧
      PredecessorHalfFin13Atom0412 chi ∧
      PredecessorHalfFin13Atom0419 chi ∧
      PredecessorHalfFin13Atom0493 chi ∧
      PredecessorHalfFin13Atom0694 chi ∧
      PredecessorHalfFin13Atom0697 chi ∧
      PredecessorHalfFin13Atom0704 chi ∧
      PredecessorHalfFin13Atom0778 chi ∧
      PredecessorHalfFin13Atom0862 chi) ∨
      ((PredecessorHalfFin13Atom0345 chi ∧
      PredecessorHalfFin13Atom0348 chi ∧
      PredecessorHalfFin13Atom0350 chi ∧
      PredecessorHalfFin13Atom0374 chi ∧
      PredecessorHalfFin13Atom0376 chi ∧
      PredecessorHalfFin13Atom0385 chi ∧
      PredecessorHalfFin13Atom0410 chi ∧
      PredecessorHalfFin13Atom0412 chi ∧
      PredecessorHalfFin13Atom0421 chi ∧
      PredecessorHalfFin13Atom0495 chi ∧
      PredecessorHalfFin13Atom0695 chi ∧
      PredecessorHalfFin13Atom0697 chi ∧
      PredecessorHalfFin13Atom0706 chi ∧
      PredecessorHalfFin13Atom0780 chi ∧
      PredecessorHalfFin13Atom0864 chi) ∨
      (PredecessorHalfFin13Atom0346 chi ∧
      PredecessorHalfFin13Atom0347 chi ∧
      PredecessorHalfFin13Atom0348 chi ∧
      PredecessorHalfFin13Atom0377 chi ∧
      PredecessorHalfFin13Atom0378 chi ∧
      PredecessorHalfFin13Atom0381 chi ∧
      PredecessorHalfFin13Atom0413 chi ∧
      PredecessorHalfFin13Atom0414 chi ∧
      PredecessorHalfFin13Atom0417 chi ∧
      PredecessorHalfFin13Atom0497 chi ∧
      PredecessorHalfFin13Atom0698 chi ∧
      PredecessorHalfFin13Atom0699 chi ∧
      PredecessorHalfFin13Atom0702 chi ∧
      PredecessorHalfFin13Atom0782 chi ∧
      PredecessorHalfFin13Atom0866 chi))) ∨
      ((PredecessorHalfFin13Atom0346 chi ∧
      PredecessorHalfFin13Atom0347 chi ∧
      PredecessorHalfFin13Atom0350 chi ∧
      PredecessorHalfFin13Atom0377 chi ∧
      PredecessorHalfFin13Atom0380 chi ∧
      PredecessorHalfFin13Atom0383 chi ∧
      PredecessorHalfFin13Atom0413 chi ∧
      PredecessorHalfFin13Atom0416 chi ∧
      PredecessorHalfFin13Atom0419 chi ∧
      PredecessorHalfFin13Atom0499 chi ∧
      PredecessorHalfFin13Atom0698 chi ∧
      PredecessorHalfFin13Atom0701 chi ∧
      PredecessorHalfFin13Atom0704 chi ∧
      PredecessorHalfFin13Atom0784 chi ∧
      PredecessorHalfFin13Atom0868 chi) ∨
      ((PredecessorHalfFin13Atom0346 chi ∧
      PredecessorHalfFin13Atom0348 chi ∧
      PredecessorHalfFin13Atom0350 chi ∧
      PredecessorHalfFin13Atom0378 chi ∧
      PredecessorHalfFin13Atom0380 chi ∧
      PredecessorHalfFin13Atom0385 chi ∧
      PredecessorHalfFin13Atom0414 chi ∧
      PredecessorHalfFin13Atom0416 chi ∧
      PredecessorHalfFin13Atom0421 chi ∧
      PredecessorHalfFin13Atom0501 chi ∧
      PredecessorHalfFin13Atom0699 chi ∧
      PredecessorHalfFin13Atom0701 chi ∧
      PredecessorHalfFin13Atom0706 chi ∧
      PredecessorHalfFin13Atom0786 chi ∧
      PredecessorHalfFin13Atom0870 chi) ∨
      (PredecessorHalfFin13Atom0347 chi ∧
      PredecessorHalfFin13Atom0348 chi ∧
      PredecessorHalfFin13Atom0350 chi ∧
      PredecessorHalfFin13Atom0381 chi ∧
      PredecessorHalfFin13Atom0383 chi ∧
      PredecessorHalfFin13Atom0385 chi ∧
      PredecessorHalfFin13Atom0417 chi ∧
      PredecessorHalfFin13Atom0419 chi ∧
      PredecessorHalfFin13Atom0421 chi ∧
      PredecessorHalfFin13Atom0504 chi ∧
      PredecessorHalfFin13Atom0702 chi ∧
      PredecessorHalfFin13Atom0704 chi ∧
      PredecessorHalfFin13Atom0706 chi ∧
      PredecessorHalfFin13Atom0789 chi ∧
      PredecessorHalfFin13Atom0873 chi))))) ∨
      ((((PredecessorHalfFin13Atom0351 chi ∧
      PredecessorHalfFin13Atom0352 chi ∧
      PredecessorHalfFin13Atom0353 chi ∧
      PredecessorHalfFin13Atom0359 chi ∧
      PredecessorHalfFin13Atom0360 chi ∧
      PredecessorHalfFin13Atom0366 chi ∧
      PredecessorHalfFin13Atom0423 chi ∧
      PredecessorHalfFin13Atom0424 chi ∧
      PredecessorHalfFin13Atom0430 chi ∧
      PredecessorHalfFin13Atom0451 chi ∧
      PredecessorHalfFin13Atom0708 chi ∧
      PredecessorHalfFin13Atom0709 chi ∧
      PredecessorHalfFin13Atom0715 chi ∧
      PredecessorHalfFin13Atom0736 chi ∧
      PredecessorHalfFin13Atom0876 chi) ∨
      ((PredecessorHalfFin13Atom0351 chi ∧
      PredecessorHalfFin13Atom0352 chi ∧
      PredecessorHalfFin13Atom0354 chi ∧
      PredecessorHalfFin13Atom0359 chi ∧
      PredecessorHalfFin13Atom0361 chi ∧
      PredecessorHalfFin13Atom0367 chi ∧
      PredecessorHalfFin13Atom0423 chi ∧
      PredecessorHalfFin13Atom0425 chi ∧
      PredecessorHalfFin13Atom0431 chi ∧
      PredecessorHalfFin13Atom0452 chi ∧
      PredecessorHalfFin13Atom0708 chi ∧
      PredecessorHalfFin13Atom0710 chi ∧
      PredecessorHalfFin13Atom0716 chi ∧
      PredecessorHalfFin13Atom0737 chi ∧
      PredecessorHalfFin13Atom0877 chi) ∨
      (PredecessorHalfFin13Atom0351 chi ∧
      PredecessorHalfFin13Atom0352 chi ∧
      PredecessorHalfFin13Atom0355 chi ∧
      PredecessorHalfFin13Atom0359 chi ∧
      PredecessorHalfFin13Atom0362 chi ∧
      PredecessorHalfFin13Atom0368 chi ∧
      PredecessorHalfFin13Atom0423 chi ∧
      PredecessorHalfFin13Atom0426 chi ∧
      PredecessorHalfFin13Atom0432 chi ∧
      PredecessorHalfFin13Atom0453 chi ∧
      PredecessorHalfFin13Atom0708 chi ∧
      PredecessorHalfFin13Atom0711 chi ∧
      PredecessorHalfFin13Atom0717 chi ∧
      PredecessorHalfFin13Atom0738 chi ∧
      PredecessorHalfFin13Atom0878 chi))) ∨
      ((PredecessorHalfFin13Atom0351 chi ∧
      PredecessorHalfFin13Atom0352 chi ∧
      PredecessorHalfFin13Atom0356 chi ∧
      PredecessorHalfFin13Atom0359 chi ∧
      PredecessorHalfFin13Atom0363 chi ∧
      PredecessorHalfFin13Atom0369 chi ∧
      PredecessorHalfFin13Atom0423 chi ∧
      PredecessorHalfFin13Atom0427 chi ∧
      PredecessorHalfFin13Atom0433 chi ∧
      PredecessorHalfFin13Atom0454 chi ∧
      PredecessorHalfFin13Atom0708 chi ∧
      PredecessorHalfFin13Atom0712 chi ∧
      PredecessorHalfFin13Atom0718 chi ∧
      PredecessorHalfFin13Atom0739 chi ∧
      PredecessorHalfFin13Atom0879 chi) ∨
      ((PredecessorHalfFin13Atom0351 chi ∧
      PredecessorHalfFin13Atom0352 chi ∧
      PredecessorHalfFin13Atom0358 chi ∧
      PredecessorHalfFin13Atom0359 chi ∧
      PredecessorHalfFin13Atom0365 chi ∧
      PredecessorHalfFin13Atom0371 chi ∧
      PredecessorHalfFin13Atom0423 chi ∧
      PredecessorHalfFin13Atom0429 chi ∧
      PredecessorHalfFin13Atom0435 chi ∧
      PredecessorHalfFin13Atom0456 chi ∧
      PredecessorHalfFin13Atom0708 chi ∧
      PredecessorHalfFin13Atom0714 chi ∧
      PredecessorHalfFin13Atom0720 chi ∧
      PredecessorHalfFin13Atom0741 chi ∧
      PredecessorHalfFin13Atom0881 chi) ∨
      (PredecessorHalfFin13Atom0351 chi ∧
      PredecessorHalfFin13Atom0353 chi ∧
      PredecessorHalfFin13Atom0354 chi ∧
      PredecessorHalfFin13Atom0360 chi ∧
      PredecessorHalfFin13Atom0361 chi ∧
      PredecessorHalfFin13Atom0372 chi ∧
      PredecessorHalfFin13Atom0424 chi ∧
      PredecessorHalfFin13Atom0425 chi ∧
      PredecessorHalfFin13Atom0436 chi ∧
      PredecessorHalfFin13Atom0457 chi ∧
      PredecessorHalfFin13Atom0709 chi ∧
      PredecessorHalfFin13Atom0710 chi ∧
      PredecessorHalfFin13Atom0721 chi ∧
      PredecessorHalfFin13Atom0742 chi ∧
      PredecessorHalfFin13Atom0882 chi)))) ∨
      (((PredecessorHalfFin13Atom0351 chi ∧
      PredecessorHalfFin13Atom0353 chi ∧
      PredecessorHalfFin13Atom0355 chi ∧
      PredecessorHalfFin13Atom0360 chi ∧
      PredecessorHalfFin13Atom0362 chi ∧
      PredecessorHalfFin13Atom0373 chi ∧
      PredecessorHalfFin13Atom0424 chi ∧
      PredecessorHalfFin13Atom0426 chi ∧
      PredecessorHalfFin13Atom0437 chi ∧
      PredecessorHalfFin13Atom0458 chi ∧
      PredecessorHalfFin13Atom0709 chi ∧
      PredecessorHalfFin13Atom0711 chi ∧
      PredecessorHalfFin13Atom0722 chi ∧
      PredecessorHalfFin13Atom0743 chi ∧
      PredecessorHalfFin13Atom0883 chi) ∨
      ((PredecessorHalfFin13Atom0351 chi ∧
      PredecessorHalfFin13Atom0353 chi ∧
      PredecessorHalfFin13Atom0356 chi ∧
      PredecessorHalfFin13Atom0360 chi ∧
      PredecessorHalfFin13Atom0363 chi ∧
      PredecessorHalfFin13Atom0374 chi ∧
      PredecessorHalfFin13Atom0424 chi ∧
      PredecessorHalfFin13Atom0427 chi ∧
      PredecessorHalfFin13Atom0438 chi ∧
      PredecessorHalfFin13Atom0459 chi ∧
      PredecessorHalfFin13Atom0709 chi ∧
      PredecessorHalfFin13Atom0712 chi ∧
      PredecessorHalfFin13Atom0723 chi ∧
      PredecessorHalfFin13Atom0744 chi ∧
      PredecessorHalfFin13Atom0884 chi) ∨
      (PredecessorHalfFin13Atom0351 chi ∧
      PredecessorHalfFin13Atom0353 chi ∧
      PredecessorHalfFin13Atom0358 chi ∧
      PredecessorHalfFin13Atom0360 chi ∧
      PredecessorHalfFin13Atom0365 chi ∧
      PredecessorHalfFin13Atom0376 chi ∧
      PredecessorHalfFin13Atom0424 chi ∧
      PredecessorHalfFin13Atom0429 chi ∧
      PredecessorHalfFin13Atom0440 chi ∧
      PredecessorHalfFin13Atom0461 chi ∧
      PredecessorHalfFin13Atom0709 chi ∧
      PredecessorHalfFin13Atom0714 chi ∧
      PredecessorHalfFin13Atom0725 chi ∧
      PredecessorHalfFin13Atom0746 chi ∧
      PredecessorHalfFin13Atom0886 chi))) ∨
      ((PredecessorHalfFin13Atom0351 chi ∧
      PredecessorHalfFin13Atom0354 chi ∧
      PredecessorHalfFin13Atom0355 chi ∧
      PredecessorHalfFin13Atom0361 chi ∧
      PredecessorHalfFin13Atom0362 chi ∧
      PredecessorHalfFin13Atom0377 chi ∧
      PredecessorHalfFin13Atom0425 chi ∧
      PredecessorHalfFin13Atom0426 chi ∧
      PredecessorHalfFin13Atom0441 chi ∧
      PredecessorHalfFin13Atom0462 chi ∧
      PredecessorHalfFin13Atom0710 chi ∧
      PredecessorHalfFin13Atom0711 chi ∧
      PredecessorHalfFin13Atom0726 chi ∧
      PredecessorHalfFin13Atom0747 chi ∧
      PredecessorHalfFin13Atom0887 chi) ∨
      ((PredecessorHalfFin13Atom0351 chi ∧
      PredecessorHalfFin13Atom0354 chi ∧
      PredecessorHalfFin13Atom0356 chi ∧
      PredecessorHalfFin13Atom0361 chi ∧
      PredecessorHalfFin13Atom0363 chi ∧
      PredecessorHalfFin13Atom0378 chi ∧
      PredecessorHalfFin13Atom0425 chi ∧
      PredecessorHalfFin13Atom0427 chi ∧
      PredecessorHalfFin13Atom0442 chi ∧
      PredecessorHalfFin13Atom0463 chi ∧
      PredecessorHalfFin13Atom0710 chi ∧
      PredecessorHalfFin13Atom0712 chi ∧
      PredecessorHalfFin13Atom0727 chi ∧
      PredecessorHalfFin13Atom0748 chi ∧
      PredecessorHalfFin13Atom0888 chi) ∨
      (PredecessorHalfFin13Atom0351 chi ∧
      PredecessorHalfFin13Atom0354 chi ∧
      PredecessorHalfFin13Atom0358 chi ∧
      PredecessorHalfFin13Atom0361 chi ∧
      PredecessorHalfFin13Atom0365 chi ∧
      PredecessorHalfFin13Atom0380 chi ∧
      PredecessorHalfFin13Atom0425 chi ∧
      PredecessorHalfFin13Atom0429 chi ∧
      PredecessorHalfFin13Atom0444 chi ∧
      PredecessorHalfFin13Atom0465 chi ∧
      PredecessorHalfFin13Atom0710 chi ∧
      PredecessorHalfFin13Atom0714 chi ∧
      PredecessorHalfFin13Atom0729 chi ∧
      PredecessorHalfFin13Atom0750 chi ∧
      PredecessorHalfFin13Atom0890 chi)))))) ∨
      (((((PredecessorHalfFin13Atom0351 chi ∧
      PredecessorHalfFin13Atom0355 chi ∧
      PredecessorHalfFin13Atom0356 chi ∧
      PredecessorHalfFin13Atom0362 chi ∧
      PredecessorHalfFin13Atom0363 chi ∧
      PredecessorHalfFin13Atom0381 chi ∧
      PredecessorHalfFin13Atom0426 chi ∧
      PredecessorHalfFin13Atom0427 chi ∧
      PredecessorHalfFin13Atom0445 chi ∧
      PredecessorHalfFin13Atom0466 chi ∧
      PredecessorHalfFin13Atom0711 chi ∧
      PredecessorHalfFin13Atom0712 chi ∧
      PredecessorHalfFin13Atom0730 chi ∧
      PredecessorHalfFin13Atom0751 chi ∧
      PredecessorHalfFin13Atom0891 chi) ∨
      ((PredecessorHalfFin13Atom0351 chi ∧
      PredecessorHalfFin13Atom0355 chi ∧
      PredecessorHalfFin13Atom0358 chi ∧
      PredecessorHalfFin13Atom0362 chi ∧
      PredecessorHalfFin13Atom0365 chi ∧
      PredecessorHalfFin13Atom0383 chi ∧
      PredecessorHalfFin13Atom0426 chi ∧
      PredecessorHalfFin13Atom0429 chi ∧
      PredecessorHalfFin13Atom0447 chi ∧
      PredecessorHalfFin13Atom0468 chi ∧
      PredecessorHalfFin13Atom0711 chi ∧
      PredecessorHalfFin13Atom0714 chi ∧
      PredecessorHalfFin13Atom0732 chi ∧
      PredecessorHalfFin13Atom0753 chi ∧
      PredecessorHalfFin13Atom0893 chi) ∨
      (PredecessorHalfFin13Atom0351 chi ∧
      PredecessorHalfFin13Atom0356 chi ∧
      PredecessorHalfFin13Atom0358 chi ∧
      PredecessorHalfFin13Atom0363 chi ∧
      PredecessorHalfFin13Atom0365 chi ∧
      PredecessorHalfFin13Atom0385 chi ∧
      PredecessorHalfFin13Atom0427 chi ∧
      PredecessorHalfFin13Atom0429 chi ∧
      PredecessorHalfFin13Atom0449 chi ∧
      PredecessorHalfFin13Atom0470 chi ∧
      PredecessorHalfFin13Atom0712 chi ∧
      PredecessorHalfFin13Atom0714 chi ∧
      PredecessorHalfFin13Atom0734 chi ∧
      PredecessorHalfFin13Atom0755 chi ∧
      PredecessorHalfFin13Atom0895 chi))) ∨
      ((PredecessorHalfFin13Atom0352 chi ∧
      PredecessorHalfFin13Atom0353 chi ∧
      PredecessorHalfFin13Atom0354 chi ∧
      PredecessorHalfFin13Atom0366 chi ∧
      PredecessorHalfFin13Atom0367 chi ∧
      PredecessorHalfFin13Atom0372 chi ∧
      PredecessorHalfFin13Atom0430 chi ∧
      PredecessorHalfFin13Atom0431 chi ∧
      PredecessorHalfFin13Atom0436 chi ∧
      PredecessorHalfFin13Atom0472 chi ∧
      PredecessorHalfFin13Atom0715 chi ∧
      PredecessorHalfFin13Atom0716 chi ∧
      PredecessorHalfFin13Atom0721 chi ∧
      PredecessorHalfFin13Atom0757 chi ∧
      PredecessorHalfFin13Atom0897 chi) ∨
      ((PredecessorHalfFin13Atom0352 chi ∧
      PredecessorHalfFin13Atom0353 chi ∧
      PredecessorHalfFin13Atom0355 chi ∧
      PredecessorHalfFin13Atom0366 chi ∧
      PredecessorHalfFin13Atom0368 chi ∧
      PredecessorHalfFin13Atom0373 chi ∧
      PredecessorHalfFin13Atom0430 chi ∧
      PredecessorHalfFin13Atom0432 chi ∧
      PredecessorHalfFin13Atom0437 chi ∧
      PredecessorHalfFin13Atom0473 chi ∧
      PredecessorHalfFin13Atom0715 chi ∧
      PredecessorHalfFin13Atom0717 chi ∧
      PredecessorHalfFin13Atom0722 chi ∧
      PredecessorHalfFin13Atom0758 chi ∧
      PredecessorHalfFin13Atom0898 chi) ∨
      (PredecessorHalfFin13Atom0352 chi ∧
      PredecessorHalfFin13Atom0353 chi ∧
      PredecessorHalfFin13Atom0356 chi ∧
      PredecessorHalfFin13Atom0366 chi ∧
      PredecessorHalfFin13Atom0369 chi ∧
      PredecessorHalfFin13Atom0374 chi ∧
      PredecessorHalfFin13Atom0430 chi ∧
      PredecessorHalfFin13Atom0433 chi ∧
      PredecessorHalfFin13Atom0438 chi ∧
      PredecessorHalfFin13Atom0474 chi ∧
      PredecessorHalfFin13Atom0715 chi ∧
      PredecessorHalfFin13Atom0718 chi ∧
      PredecessorHalfFin13Atom0723 chi ∧
      PredecessorHalfFin13Atom0759 chi ∧
      PredecessorHalfFin13Atom0899 chi)))) ∨
      (((PredecessorHalfFin13Atom0352 chi ∧
      PredecessorHalfFin13Atom0354 chi ∧
      PredecessorHalfFin13Atom0355 chi ∧
      PredecessorHalfFin13Atom0367 chi ∧
      PredecessorHalfFin13Atom0368 chi ∧
      PredecessorHalfFin13Atom0377 chi ∧
      PredecessorHalfFin13Atom0431 chi ∧
      PredecessorHalfFin13Atom0432 chi ∧
      PredecessorHalfFin13Atom0441 chi ∧
      PredecessorHalfFin13Atom0477 chi ∧
      PredecessorHalfFin13Atom0716 chi ∧
      PredecessorHalfFin13Atom0717 chi ∧
      PredecessorHalfFin13Atom0726 chi ∧
      PredecessorHalfFin13Atom0762 chi ∧
      PredecessorHalfFin13Atom0902 chi) ∨
      ((PredecessorHalfFin13Atom0352 chi ∧
      PredecessorHalfFin13Atom0354 chi ∧
      PredecessorHalfFin13Atom0356 chi ∧
      PredecessorHalfFin13Atom0367 chi ∧
      PredecessorHalfFin13Atom0369 chi ∧
      PredecessorHalfFin13Atom0378 chi ∧
      PredecessorHalfFin13Atom0431 chi ∧
      PredecessorHalfFin13Atom0433 chi ∧
      PredecessorHalfFin13Atom0442 chi ∧
      PredecessorHalfFin13Atom0478 chi ∧
      PredecessorHalfFin13Atom0716 chi ∧
      PredecessorHalfFin13Atom0718 chi ∧
      PredecessorHalfFin13Atom0727 chi ∧
      PredecessorHalfFin13Atom0763 chi ∧
      PredecessorHalfFin13Atom0903 chi) ∨
      (PredecessorHalfFin13Atom0352 chi ∧
      PredecessorHalfFin13Atom0354 chi ∧
      PredecessorHalfFin13Atom0358 chi ∧
      PredecessorHalfFin13Atom0367 chi ∧
      PredecessorHalfFin13Atom0371 chi ∧
      PredecessorHalfFin13Atom0380 chi ∧
      PredecessorHalfFin13Atom0431 chi ∧
      PredecessorHalfFin13Atom0435 chi ∧
      PredecessorHalfFin13Atom0444 chi ∧
      PredecessorHalfFin13Atom0480 chi ∧
      PredecessorHalfFin13Atom0716 chi ∧
      PredecessorHalfFin13Atom0720 chi ∧
      PredecessorHalfFin13Atom0729 chi ∧
      PredecessorHalfFin13Atom0765 chi ∧
      PredecessorHalfFin13Atom0905 chi))) ∨
      ((PredecessorHalfFin13Atom0352 chi ∧
      PredecessorHalfFin13Atom0355 chi ∧
      PredecessorHalfFin13Atom0356 chi ∧
      PredecessorHalfFin13Atom0368 chi ∧
      PredecessorHalfFin13Atom0369 chi ∧
      PredecessorHalfFin13Atom0381 chi ∧
      PredecessorHalfFin13Atom0432 chi ∧
      PredecessorHalfFin13Atom0433 chi ∧
      PredecessorHalfFin13Atom0445 chi ∧
      PredecessorHalfFin13Atom0481 chi ∧
      PredecessorHalfFin13Atom0717 chi ∧
      PredecessorHalfFin13Atom0718 chi ∧
      PredecessorHalfFin13Atom0730 chi ∧
      PredecessorHalfFin13Atom0766 chi ∧
      PredecessorHalfFin13Atom0906 chi) ∨
      ((PredecessorHalfFin13Atom0352 chi ∧
      PredecessorHalfFin13Atom0355 chi ∧
      PredecessorHalfFin13Atom0358 chi ∧
      PredecessorHalfFin13Atom0368 chi ∧
      PredecessorHalfFin13Atom0371 chi ∧
      PredecessorHalfFin13Atom0383 chi ∧
      PredecessorHalfFin13Atom0432 chi ∧
      PredecessorHalfFin13Atom0435 chi ∧
      PredecessorHalfFin13Atom0447 chi ∧
      PredecessorHalfFin13Atom0483 chi ∧
      PredecessorHalfFin13Atom0717 chi ∧
      PredecessorHalfFin13Atom0720 chi ∧
      PredecessorHalfFin13Atom0732 chi ∧
      PredecessorHalfFin13Atom0768 chi ∧
      PredecessorHalfFin13Atom0908 chi) ∨
      (PredecessorHalfFin13Atom0352 chi ∧
      PredecessorHalfFin13Atom0356 chi ∧
      PredecessorHalfFin13Atom0358 chi ∧
      PredecessorHalfFin13Atom0369 chi ∧
      PredecessorHalfFin13Atom0371 chi ∧
      PredecessorHalfFin13Atom0385 chi ∧
      PredecessorHalfFin13Atom0433 chi ∧
      PredecessorHalfFin13Atom0435 chi ∧
      PredecessorHalfFin13Atom0449 chi ∧
      PredecessorHalfFin13Atom0485 chi ∧
      PredecessorHalfFin13Atom0718 chi ∧
      PredecessorHalfFin13Atom0720 chi ∧
      PredecessorHalfFin13Atom0734 chi ∧
      PredecessorHalfFin13Atom0770 chi ∧
      PredecessorHalfFin13Atom0910 chi))))) ∨
      ((((PredecessorHalfFin13Atom0353 chi ∧
      PredecessorHalfFin13Atom0354 chi ∧
      PredecessorHalfFin13Atom0355 chi ∧
      PredecessorHalfFin13Atom0372 chi ∧
      PredecessorHalfFin13Atom0373 chi ∧
      PredecessorHalfFin13Atom0377 chi ∧
      PredecessorHalfFin13Atom0436 chi ∧
      PredecessorHalfFin13Atom0437 chi ∧
      PredecessorHalfFin13Atom0441 chi ∧
      PredecessorHalfFin13Atom0487 chi ∧
      PredecessorHalfFin13Atom0721 chi ∧
      PredecessorHalfFin13Atom0722 chi ∧
      PredecessorHalfFin13Atom0726 chi ∧
      PredecessorHalfFin13Atom0772 chi ∧
      PredecessorHalfFin13Atom0912 chi) ∨
      ((PredecessorHalfFin13Atom0353 chi ∧
      PredecessorHalfFin13Atom0354 chi ∧
      PredecessorHalfFin13Atom0356 chi ∧
      PredecessorHalfFin13Atom0372 chi ∧
      PredecessorHalfFin13Atom0374 chi ∧
      PredecessorHalfFin13Atom0378 chi ∧
      PredecessorHalfFin13Atom0436 chi ∧
      PredecessorHalfFin13Atom0438 chi ∧
      PredecessorHalfFin13Atom0442 chi ∧
      PredecessorHalfFin13Atom0488 chi ∧
      PredecessorHalfFin13Atom0721 chi ∧
      PredecessorHalfFin13Atom0723 chi ∧
      PredecessorHalfFin13Atom0727 chi ∧
      PredecessorHalfFin13Atom0773 chi ∧
      PredecessorHalfFin13Atom0913 chi) ∨
      (PredecessorHalfFin13Atom0353 chi ∧
      PredecessorHalfFin13Atom0354 chi ∧
      PredecessorHalfFin13Atom0358 chi ∧
      PredecessorHalfFin13Atom0372 chi ∧
      PredecessorHalfFin13Atom0376 chi ∧
      PredecessorHalfFin13Atom0380 chi ∧
      PredecessorHalfFin13Atom0436 chi ∧
      PredecessorHalfFin13Atom0440 chi ∧
      PredecessorHalfFin13Atom0444 chi ∧
      PredecessorHalfFin13Atom0490 chi ∧
      PredecessorHalfFin13Atom0721 chi ∧
      PredecessorHalfFin13Atom0725 chi ∧
      PredecessorHalfFin13Atom0729 chi ∧
      PredecessorHalfFin13Atom0775 chi ∧
      PredecessorHalfFin13Atom0915 chi))) ∨
      ((PredecessorHalfFin13Atom0353 chi ∧
      PredecessorHalfFin13Atom0355 chi ∧
      PredecessorHalfFin13Atom0356 chi ∧
      PredecessorHalfFin13Atom0373 chi ∧
      PredecessorHalfFin13Atom0374 chi ∧
      PredecessorHalfFin13Atom0381 chi ∧
      PredecessorHalfFin13Atom0437 chi ∧
      PredecessorHalfFin13Atom0438 chi ∧
      PredecessorHalfFin13Atom0445 chi ∧
      PredecessorHalfFin13Atom0491 chi ∧
      PredecessorHalfFin13Atom0722 chi ∧
      PredecessorHalfFin13Atom0723 chi ∧
      PredecessorHalfFin13Atom0730 chi ∧
      PredecessorHalfFin13Atom0776 chi ∧
      PredecessorHalfFin13Atom0916 chi) ∨
      ((PredecessorHalfFin13Atom0353 chi ∧
      PredecessorHalfFin13Atom0355 chi ∧
      PredecessorHalfFin13Atom0358 chi ∧
      PredecessorHalfFin13Atom0373 chi ∧
      PredecessorHalfFin13Atom0376 chi ∧
      PredecessorHalfFin13Atom0383 chi ∧
      PredecessorHalfFin13Atom0437 chi ∧
      PredecessorHalfFin13Atom0440 chi ∧
      PredecessorHalfFin13Atom0447 chi ∧
      PredecessorHalfFin13Atom0493 chi ∧
      PredecessorHalfFin13Atom0722 chi ∧
      PredecessorHalfFin13Atom0725 chi ∧
      PredecessorHalfFin13Atom0732 chi ∧
      PredecessorHalfFin13Atom0778 chi ∧
      PredecessorHalfFin13Atom0918 chi) ∨
      (PredecessorHalfFin13Atom0353 chi ∧
      PredecessorHalfFin13Atom0356 chi ∧
      PredecessorHalfFin13Atom0358 chi ∧
      PredecessorHalfFin13Atom0374 chi ∧
      PredecessorHalfFin13Atom0376 chi ∧
      PredecessorHalfFin13Atom0385 chi ∧
      PredecessorHalfFin13Atom0438 chi ∧
      PredecessorHalfFin13Atom0440 chi ∧
      PredecessorHalfFin13Atom0449 chi ∧
      PredecessorHalfFin13Atom0495 chi ∧
      PredecessorHalfFin13Atom0723 chi ∧
      PredecessorHalfFin13Atom0725 chi ∧
      PredecessorHalfFin13Atom0734 chi ∧
      PredecessorHalfFin13Atom0780 chi ∧
      PredecessorHalfFin13Atom0920 chi)))) ∨
      (((PredecessorHalfFin13Atom0354 chi ∧
      PredecessorHalfFin13Atom0355 chi ∧
      PredecessorHalfFin13Atom0356 chi ∧
      PredecessorHalfFin13Atom0377 chi ∧
      PredecessorHalfFin13Atom0378 chi ∧
      PredecessorHalfFin13Atom0381 chi ∧
      PredecessorHalfFin13Atom0441 chi ∧
      PredecessorHalfFin13Atom0442 chi ∧
      PredecessorHalfFin13Atom0445 chi ∧
      PredecessorHalfFin13Atom0497 chi ∧
      PredecessorHalfFin13Atom0726 chi ∧
      PredecessorHalfFin13Atom0727 chi ∧
      PredecessorHalfFin13Atom0730 chi ∧
      PredecessorHalfFin13Atom0782 chi ∧
      PredecessorHalfFin13Atom0922 chi) ∨
      ((PredecessorHalfFin13Atom0354 chi ∧
      PredecessorHalfFin13Atom0355 chi ∧
      PredecessorHalfFin13Atom0358 chi ∧
      PredecessorHalfFin13Atom0377 chi ∧
      PredecessorHalfFin13Atom0380 chi ∧
      PredecessorHalfFin13Atom0383 chi ∧
      PredecessorHalfFin13Atom0441 chi ∧
      PredecessorHalfFin13Atom0444 chi ∧
      PredecessorHalfFin13Atom0447 chi ∧
      PredecessorHalfFin13Atom0499 chi ∧
      PredecessorHalfFin13Atom0726 chi ∧
      PredecessorHalfFin13Atom0729 chi ∧
      PredecessorHalfFin13Atom0732 chi ∧
      PredecessorHalfFin13Atom0784 chi ∧
      PredecessorHalfFin13Atom0924 chi) ∨
      (PredecessorHalfFin13Atom0354 chi ∧
      PredecessorHalfFin13Atom0356 chi ∧
      PredecessorHalfFin13Atom0358 chi ∧
      PredecessorHalfFin13Atom0378 chi ∧
      PredecessorHalfFin13Atom0380 chi ∧
      PredecessorHalfFin13Atom0385 chi ∧
      PredecessorHalfFin13Atom0442 chi ∧
      PredecessorHalfFin13Atom0444 chi ∧
      PredecessorHalfFin13Atom0449 chi ∧
      PredecessorHalfFin13Atom0501 chi ∧
      PredecessorHalfFin13Atom0727 chi ∧
      PredecessorHalfFin13Atom0729 chi ∧
      PredecessorHalfFin13Atom0734 chi ∧
      PredecessorHalfFin13Atom0786 chi ∧
      PredecessorHalfFin13Atom0926 chi))) ∨
      (((PredecessorHalfFin13Atom0355 chi ∧
      PredecessorHalfFin13Atom0356 chi ∧
      PredecessorHalfFin13Atom0358 chi ∧
      PredecessorHalfFin13Atom0381 chi ∧
      PredecessorHalfFin13Atom0383 chi ∧
      PredecessorHalfFin13Atom0385 chi ∧
      PredecessorHalfFin13Atom0445 chi ∧
      PredecessorHalfFin13Atom0447 chi ∧
      PredecessorHalfFin13Atom0449 chi ∧
      PredecessorHalfFin13Atom0504 chi ∧
      PredecessorHalfFin13Atom0730 chi ∧
      PredecessorHalfFin13Atom0732 chi ∧
      PredecessorHalfFin13Atom0734 chi ∧
      PredecessorHalfFin13Atom0789 chi ∧
      PredecessorHalfFin13Atom0929 chi) ∨
      (PredecessorHalfFin13Atom0359 chi ∧
      PredecessorHalfFin13Atom0360 chi ∧
      PredecessorHalfFin13Atom0361 chi ∧
      PredecessorHalfFin13Atom0366 chi ∧
      PredecessorHalfFin13Atom0367 chi ∧
      PredecessorHalfFin13Atom0372 chi ∧
      PredecessorHalfFin13Atom0451 chi ∧
      PredecessorHalfFin13Atom0452 chi ∧
      PredecessorHalfFin13Atom0457 chi ∧
      PredecessorHalfFin13Atom0472 chi ∧
      PredecessorHalfFin13Atom0736 chi ∧
      PredecessorHalfFin13Atom0737 chi ∧
      PredecessorHalfFin13Atom0742 chi ∧
      PredecessorHalfFin13Atom0757 chi ∧
      PredecessorHalfFin13Atom0932 chi)) ∨
      ((PredecessorHalfFin13Atom0359 chi ∧
      PredecessorHalfFin13Atom0360 chi ∧
      PredecessorHalfFin13Atom0362 chi ∧
      PredecessorHalfFin13Atom0366 chi ∧
      PredecessorHalfFin13Atom0368 chi ∧
      PredecessorHalfFin13Atom0373 chi ∧
      PredecessorHalfFin13Atom0451 chi ∧
      PredecessorHalfFin13Atom0453 chi ∧
      PredecessorHalfFin13Atom0458 chi ∧
      PredecessorHalfFin13Atom0473 chi ∧
      PredecessorHalfFin13Atom0736 chi ∧
      PredecessorHalfFin13Atom0738 chi ∧
      PredecessorHalfFin13Atom0743 chi ∧
      PredecessorHalfFin13Atom0758 chi ∧
      PredecessorHalfFin13Atom0933 chi) ∨
      (PredecessorHalfFin13Atom0359 chi ∧
      PredecessorHalfFin13Atom0360 chi ∧
      PredecessorHalfFin13Atom0363 chi ∧
      PredecessorHalfFin13Atom0366 chi ∧
      PredecessorHalfFin13Atom0369 chi ∧
      PredecessorHalfFin13Atom0374 chi ∧
      PredecessorHalfFin13Atom0451 chi ∧
      PredecessorHalfFin13Atom0454 chi ∧
      PredecessorHalfFin13Atom0459 chi ∧
      PredecessorHalfFin13Atom0474 chi ∧
      PredecessorHalfFin13Atom0736 chi ∧
      PredecessorHalfFin13Atom0739 chi ∧
      PredecessorHalfFin13Atom0744 chi ∧
      PredecessorHalfFin13Atom0759 chi ∧
      PredecessorHalfFin13Atom0934 chi))))))) ∨
      ((((((PredecessorHalfFin13Atom0359 chi ∧
      PredecessorHalfFin13Atom0361 chi ∧
      PredecessorHalfFin13Atom0362 chi ∧
      PredecessorHalfFin13Atom0367 chi ∧
      PredecessorHalfFin13Atom0368 chi ∧
      PredecessorHalfFin13Atom0377 chi ∧
      PredecessorHalfFin13Atom0452 chi ∧
      PredecessorHalfFin13Atom0453 chi ∧
      PredecessorHalfFin13Atom0462 chi ∧
      PredecessorHalfFin13Atom0477 chi ∧
      PredecessorHalfFin13Atom0737 chi ∧
      PredecessorHalfFin13Atom0738 chi ∧
      PredecessorHalfFin13Atom0747 chi ∧
      PredecessorHalfFin13Atom0762 chi ∧
      PredecessorHalfFin13Atom0937 chi) ∨
      ((PredecessorHalfFin13Atom0359 chi ∧
      PredecessorHalfFin13Atom0361 chi ∧
      PredecessorHalfFin13Atom0363 chi ∧
      PredecessorHalfFin13Atom0367 chi ∧
      PredecessorHalfFin13Atom0369 chi ∧
      PredecessorHalfFin13Atom0378 chi ∧
      PredecessorHalfFin13Atom0452 chi ∧
      PredecessorHalfFin13Atom0454 chi ∧
      PredecessorHalfFin13Atom0463 chi ∧
      PredecessorHalfFin13Atom0478 chi ∧
      PredecessorHalfFin13Atom0737 chi ∧
      PredecessorHalfFin13Atom0739 chi ∧
      PredecessorHalfFin13Atom0748 chi ∧
      PredecessorHalfFin13Atom0763 chi ∧
      PredecessorHalfFin13Atom0938 chi) ∨
      (PredecessorHalfFin13Atom0359 chi ∧
      PredecessorHalfFin13Atom0361 chi ∧
      PredecessorHalfFin13Atom0365 chi ∧
      PredecessorHalfFin13Atom0367 chi ∧
      PredecessorHalfFin13Atom0371 chi ∧
      PredecessorHalfFin13Atom0380 chi ∧
      PredecessorHalfFin13Atom0452 chi ∧
      PredecessorHalfFin13Atom0456 chi ∧
      PredecessorHalfFin13Atom0465 chi ∧
      PredecessorHalfFin13Atom0480 chi ∧
      PredecessorHalfFin13Atom0737 chi ∧
      PredecessorHalfFin13Atom0741 chi ∧
      PredecessorHalfFin13Atom0750 chi ∧
      PredecessorHalfFin13Atom0765 chi ∧
      PredecessorHalfFin13Atom0940 chi))) ∨
      ((PredecessorHalfFin13Atom0359 chi ∧
      PredecessorHalfFin13Atom0362 chi ∧
      PredecessorHalfFin13Atom0363 chi ∧
      PredecessorHalfFin13Atom0368 chi ∧
      PredecessorHalfFin13Atom0369 chi ∧
      PredecessorHalfFin13Atom0381 chi ∧
      PredecessorHalfFin13Atom0453 chi ∧
      PredecessorHalfFin13Atom0454 chi ∧
      PredecessorHalfFin13Atom0466 chi ∧
      PredecessorHalfFin13Atom0481 chi ∧
      PredecessorHalfFin13Atom0738 chi ∧
      PredecessorHalfFin13Atom0739 chi ∧
      PredecessorHalfFin13Atom0751 chi ∧
      PredecessorHalfFin13Atom0766 chi ∧
      PredecessorHalfFin13Atom0941 chi) ∨
      ((PredecessorHalfFin13Atom0359 chi ∧
      PredecessorHalfFin13Atom0362 chi ∧
      PredecessorHalfFin13Atom0365 chi ∧
      PredecessorHalfFin13Atom0368 chi ∧
      PredecessorHalfFin13Atom0371 chi ∧
      PredecessorHalfFin13Atom0383 chi ∧
      PredecessorHalfFin13Atom0453 chi ∧
      PredecessorHalfFin13Atom0456 chi ∧
      PredecessorHalfFin13Atom0468 chi ∧
      PredecessorHalfFin13Atom0483 chi ∧
      PredecessorHalfFin13Atom0738 chi ∧
      PredecessorHalfFin13Atom0741 chi ∧
      PredecessorHalfFin13Atom0753 chi ∧
      PredecessorHalfFin13Atom0768 chi ∧
      PredecessorHalfFin13Atom0943 chi) ∨
      (PredecessorHalfFin13Atom0359 chi ∧
      PredecessorHalfFin13Atom0363 chi ∧
      PredecessorHalfFin13Atom0365 chi ∧
      PredecessorHalfFin13Atom0369 chi ∧
      PredecessorHalfFin13Atom0371 chi ∧
      PredecessorHalfFin13Atom0385 chi ∧
      PredecessorHalfFin13Atom0454 chi ∧
      PredecessorHalfFin13Atom0456 chi ∧
      PredecessorHalfFin13Atom0470 chi ∧
      PredecessorHalfFin13Atom0485 chi ∧
      PredecessorHalfFin13Atom0739 chi ∧
      PredecessorHalfFin13Atom0741 chi ∧
      PredecessorHalfFin13Atom0755 chi ∧
      PredecessorHalfFin13Atom0770 chi ∧
      PredecessorHalfFin13Atom0945 chi)))) ∨
      (((PredecessorHalfFin13Atom0360 chi ∧
      PredecessorHalfFin13Atom0361 chi ∧
      PredecessorHalfFin13Atom0362 chi ∧
      PredecessorHalfFin13Atom0372 chi ∧
      PredecessorHalfFin13Atom0373 chi ∧
      PredecessorHalfFin13Atom0377 chi ∧
      PredecessorHalfFin13Atom0457 chi ∧
      PredecessorHalfFin13Atom0458 chi ∧
      PredecessorHalfFin13Atom0462 chi ∧
      PredecessorHalfFin13Atom0487 chi ∧
      PredecessorHalfFin13Atom0742 chi ∧
      PredecessorHalfFin13Atom0743 chi ∧
      PredecessorHalfFin13Atom0747 chi ∧
      PredecessorHalfFin13Atom0772 chi ∧
      PredecessorHalfFin13Atom0947 chi) ∨
      ((PredecessorHalfFin13Atom0360 chi ∧
      PredecessorHalfFin13Atom0361 chi ∧
      PredecessorHalfFin13Atom0363 chi ∧
      PredecessorHalfFin13Atom0372 chi ∧
      PredecessorHalfFin13Atom0374 chi ∧
      PredecessorHalfFin13Atom0378 chi ∧
      PredecessorHalfFin13Atom0457 chi ∧
      PredecessorHalfFin13Atom0459 chi ∧
      PredecessorHalfFin13Atom0463 chi ∧
      PredecessorHalfFin13Atom0488 chi ∧
      PredecessorHalfFin13Atom0742 chi ∧
      PredecessorHalfFin13Atom0744 chi ∧
      PredecessorHalfFin13Atom0748 chi ∧
      PredecessorHalfFin13Atom0773 chi ∧
      PredecessorHalfFin13Atom0948 chi) ∨
      (PredecessorHalfFin13Atom0360 chi ∧
      PredecessorHalfFin13Atom0361 chi ∧
      PredecessorHalfFin13Atom0365 chi ∧
      PredecessorHalfFin13Atom0372 chi ∧
      PredecessorHalfFin13Atom0376 chi ∧
      PredecessorHalfFin13Atom0380 chi ∧
      PredecessorHalfFin13Atom0457 chi ∧
      PredecessorHalfFin13Atom0461 chi ∧
      PredecessorHalfFin13Atom0465 chi ∧
      PredecessorHalfFin13Atom0490 chi ∧
      PredecessorHalfFin13Atom0742 chi ∧
      PredecessorHalfFin13Atom0746 chi ∧
      PredecessorHalfFin13Atom0750 chi ∧
      PredecessorHalfFin13Atom0775 chi ∧
      PredecessorHalfFin13Atom0950 chi))) ∨
      ((PredecessorHalfFin13Atom0360 chi ∧
      PredecessorHalfFin13Atom0362 chi ∧
      PredecessorHalfFin13Atom0363 chi ∧
      PredecessorHalfFin13Atom0373 chi ∧
      PredecessorHalfFin13Atom0374 chi ∧
      PredecessorHalfFin13Atom0381 chi ∧
      PredecessorHalfFin13Atom0458 chi ∧
      PredecessorHalfFin13Atom0459 chi ∧
      PredecessorHalfFin13Atom0466 chi ∧
      PredecessorHalfFin13Atom0491 chi ∧
      PredecessorHalfFin13Atom0743 chi ∧
      PredecessorHalfFin13Atom0744 chi ∧
      PredecessorHalfFin13Atom0751 chi ∧
      PredecessorHalfFin13Atom0776 chi ∧
      PredecessorHalfFin13Atom0951 chi) ∨
      ((PredecessorHalfFin13Atom0360 chi ∧
      PredecessorHalfFin13Atom0362 chi ∧
      PredecessorHalfFin13Atom0365 chi ∧
      PredecessorHalfFin13Atom0373 chi ∧
      PredecessorHalfFin13Atom0376 chi ∧
      PredecessorHalfFin13Atom0383 chi ∧
      PredecessorHalfFin13Atom0458 chi ∧
      PredecessorHalfFin13Atom0461 chi ∧
      PredecessorHalfFin13Atom0468 chi ∧
      PredecessorHalfFin13Atom0493 chi ∧
      PredecessorHalfFin13Atom0743 chi ∧
      PredecessorHalfFin13Atom0746 chi ∧
      PredecessorHalfFin13Atom0753 chi ∧
      PredecessorHalfFin13Atom0778 chi ∧
      PredecessorHalfFin13Atom0953 chi) ∨
      (PredecessorHalfFin13Atom0360 chi ∧
      PredecessorHalfFin13Atom0363 chi ∧
      PredecessorHalfFin13Atom0365 chi ∧
      PredecessorHalfFin13Atom0374 chi ∧
      PredecessorHalfFin13Atom0376 chi ∧
      PredecessorHalfFin13Atom0385 chi ∧
      PredecessorHalfFin13Atom0459 chi ∧
      PredecessorHalfFin13Atom0461 chi ∧
      PredecessorHalfFin13Atom0470 chi ∧
      PredecessorHalfFin13Atom0495 chi ∧
      PredecessorHalfFin13Atom0744 chi ∧
      PredecessorHalfFin13Atom0746 chi ∧
      PredecessorHalfFin13Atom0755 chi ∧
      PredecessorHalfFin13Atom0780 chi ∧
      PredecessorHalfFin13Atom0955 chi))))) ∨
      ((((PredecessorHalfFin13Atom0361 chi ∧
      PredecessorHalfFin13Atom0362 chi ∧
      PredecessorHalfFin13Atom0363 chi ∧
      PredecessorHalfFin13Atom0377 chi ∧
      PredecessorHalfFin13Atom0378 chi ∧
      PredecessorHalfFin13Atom0381 chi ∧
      PredecessorHalfFin13Atom0462 chi ∧
      PredecessorHalfFin13Atom0463 chi ∧
      PredecessorHalfFin13Atom0466 chi ∧
      PredecessorHalfFin13Atom0497 chi ∧
      PredecessorHalfFin13Atom0747 chi ∧
      PredecessorHalfFin13Atom0748 chi ∧
      PredecessorHalfFin13Atom0751 chi ∧
      PredecessorHalfFin13Atom0782 chi ∧
      PredecessorHalfFin13Atom0957 chi) ∨
      ((PredecessorHalfFin13Atom0361 chi ∧
      PredecessorHalfFin13Atom0362 chi ∧
      PredecessorHalfFin13Atom0365 chi ∧
      PredecessorHalfFin13Atom0377 chi ∧
      PredecessorHalfFin13Atom0380 chi ∧
      PredecessorHalfFin13Atom0383 chi ∧
      PredecessorHalfFin13Atom0462 chi ∧
      PredecessorHalfFin13Atom0465 chi ∧
      PredecessorHalfFin13Atom0468 chi ∧
      PredecessorHalfFin13Atom0499 chi ∧
      PredecessorHalfFin13Atom0747 chi ∧
      PredecessorHalfFin13Atom0750 chi ∧
      PredecessorHalfFin13Atom0753 chi ∧
      PredecessorHalfFin13Atom0784 chi ∧
      PredecessorHalfFin13Atom0959 chi) ∨
      (PredecessorHalfFin13Atom0361 chi ∧
      PredecessorHalfFin13Atom0363 chi ∧
      PredecessorHalfFin13Atom0365 chi ∧
      PredecessorHalfFin13Atom0378 chi ∧
      PredecessorHalfFin13Atom0380 chi ∧
      PredecessorHalfFin13Atom0385 chi ∧
      PredecessorHalfFin13Atom0463 chi ∧
      PredecessorHalfFin13Atom0465 chi ∧
      PredecessorHalfFin13Atom0470 chi ∧
      PredecessorHalfFin13Atom0501 chi ∧
      PredecessorHalfFin13Atom0748 chi ∧
      PredecessorHalfFin13Atom0750 chi ∧
      PredecessorHalfFin13Atom0755 chi ∧
      PredecessorHalfFin13Atom0786 chi ∧
      PredecessorHalfFin13Atom0961 chi))) ∨
      ((PredecessorHalfFin13Atom0362 chi ∧
      PredecessorHalfFin13Atom0363 chi ∧
      PredecessorHalfFin13Atom0365 chi ∧
      PredecessorHalfFin13Atom0381 chi ∧
      PredecessorHalfFin13Atom0383 chi ∧
      PredecessorHalfFin13Atom0385 chi ∧
      PredecessorHalfFin13Atom0466 chi ∧
      PredecessorHalfFin13Atom0468 chi ∧
      PredecessorHalfFin13Atom0470 chi ∧
      PredecessorHalfFin13Atom0504 chi ∧
      PredecessorHalfFin13Atom0751 chi ∧
      PredecessorHalfFin13Atom0753 chi ∧
      PredecessorHalfFin13Atom0755 chi ∧
      PredecessorHalfFin13Atom0789 chi ∧
      PredecessorHalfFin13Atom0964 chi) ∨
      ((PredecessorHalfFin13Atom0366 chi ∧
      PredecessorHalfFin13Atom0367 chi ∧
      PredecessorHalfFin13Atom0368 chi ∧
      PredecessorHalfFin13Atom0372 chi ∧
      PredecessorHalfFin13Atom0373 chi ∧
      PredecessorHalfFin13Atom0377 chi ∧
      PredecessorHalfFin13Atom0472 chi ∧
      PredecessorHalfFin13Atom0473 chi ∧
      PredecessorHalfFin13Atom0477 chi ∧
      PredecessorHalfFin13Atom0487 chi ∧
      PredecessorHalfFin13Atom0757 chi ∧
      PredecessorHalfFin13Atom0758 chi ∧
      PredecessorHalfFin13Atom0762 chi ∧
      PredecessorHalfFin13Atom0772 chi ∧
      PredecessorHalfFin13Atom0967 chi) ∨
      (PredecessorHalfFin13Atom0366 chi ∧
      PredecessorHalfFin13Atom0367 chi ∧
      PredecessorHalfFin13Atom0369 chi ∧
      PredecessorHalfFin13Atom0372 chi ∧
      PredecessorHalfFin13Atom0374 chi ∧
      PredecessorHalfFin13Atom0378 chi ∧
      PredecessorHalfFin13Atom0472 chi ∧
      PredecessorHalfFin13Atom0474 chi ∧
      PredecessorHalfFin13Atom0478 chi ∧
      PredecessorHalfFin13Atom0488 chi ∧
      PredecessorHalfFin13Atom0757 chi ∧
      PredecessorHalfFin13Atom0759 chi ∧
      PredecessorHalfFin13Atom0763 chi ∧
      PredecessorHalfFin13Atom0773 chi ∧
      PredecessorHalfFin13Atom0968 chi)))) ∨
      (((PredecessorHalfFin13Atom0366 chi ∧
      PredecessorHalfFin13Atom0367 chi ∧
      PredecessorHalfFin13Atom0371 chi ∧
      PredecessorHalfFin13Atom0372 chi ∧
      PredecessorHalfFin13Atom0376 chi ∧
      PredecessorHalfFin13Atom0380 chi ∧
      PredecessorHalfFin13Atom0472 chi ∧
      PredecessorHalfFin13Atom0476 chi ∧
      PredecessorHalfFin13Atom0480 chi ∧
      PredecessorHalfFin13Atom0490 chi ∧
      PredecessorHalfFin13Atom0757 chi ∧
      PredecessorHalfFin13Atom0761 chi ∧
      PredecessorHalfFin13Atom0765 chi ∧
      PredecessorHalfFin13Atom0775 chi ∧
      PredecessorHalfFin13Atom0970 chi) ∨
      ((PredecessorHalfFin13Atom0366 chi ∧
      PredecessorHalfFin13Atom0368 chi ∧
      PredecessorHalfFin13Atom0369 chi ∧
      PredecessorHalfFin13Atom0373 chi ∧
      PredecessorHalfFin13Atom0374 chi ∧
      PredecessorHalfFin13Atom0381 chi ∧
      PredecessorHalfFin13Atom0473 chi ∧
      PredecessorHalfFin13Atom0474 chi ∧
      PredecessorHalfFin13Atom0481 chi ∧
      PredecessorHalfFin13Atom0491 chi ∧
      PredecessorHalfFin13Atom0758 chi ∧
      PredecessorHalfFin13Atom0759 chi ∧
      PredecessorHalfFin13Atom0766 chi ∧
      PredecessorHalfFin13Atom0776 chi ∧
      PredecessorHalfFin13Atom0971 chi) ∨
      (PredecessorHalfFin13Atom0366 chi ∧
      PredecessorHalfFin13Atom0368 chi ∧
      PredecessorHalfFin13Atom0371 chi ∧
      PredecessorHalfFin13Atom0373 chi ∧
      PredecessorHalfFin13Atom0376 chi ∧
      PredecessorHalfFin13Atom0383 chi ∧
      PredecessorHalfFin13Atom0473 chi ∧
      PredecessorHalfFin13Atom0476 chi ∧
      PredecessorHalfFin13Atom0483 chi ∧
      PredecessorHalfFin13Atom0493 chi ∧
      PredecessorHalfFin13Atom0758 chi ∧
      PredecessorHalfFin13Atom0761 chi ∧
      PredecessorHalfFin13Atom0768 chi ∧
      PredecessorHalfFin13Atom0778 chi ∧
      PredecessorHalfFin13Atom0973 chi))) ∨
      ((PredecessorHalfFin13Atom0366 chi ∧
      PredecessorHalfFin13Atom0369 chi ∧
      PredecessorHalfFin13Atom0371 chi ∧
      PredecessorHalfFin13Atom0374 chi ∧
      PredecessorHalfFin13Atom0376 chi ∧
      PredecessorHalfFin13Atom0385 chi ∧
      PredecessorHalfFin13Atom0474 chi ∧
      PredecessorHalfFin13Atom0476 chi ∧
      PredecessorHalfFin13Atom0485 chi ∧
      PredecessorHalfFin13Atom0495 chi ∧
      PredecessorHalfFin13Atom0759 chi ∧
      PredecessorHalfFin13Atom0761 chi ∧
      PredecessorHalfFin13Atom0770 chi ∧
      PredecessorHalfFin13Atom0780 chi ∧
      PredecessorHalfFin13Atom0975 chi) ∨
      ((PredecessorHalfFin13Atom0367 chi ∧
      PredecessorHalfFin13Atom0368 chi ∧
      PredecessorHalfFin13Atom0369 chi ∧
      PredecessorHalfFin13Atom0377 chi ∧
      PredecessorHalfFin13Atom0378 chi ∧
      PredecessorHalfFin13Atom0381 chi ∧
      PredecessorHalfFin13Atom0477 chi ∧
      PredecessorHalfFin13Atom0478 chi ∧
      PredecessorHalfFin13Atom0481 chi ∧
      PredecessorHalfFin13Atom0497 chi ∧
      PredecessorHalfFin13Atom0762 chi ∧
      PredecessorHalfFin13Atom0763 chi ∧
      PredecessorHalfFin13Atom0766 chi ∧
      PredecessorHalfFin13Atom0782 chi ∧
      PredecessorHalfFin13Atom0977 chi) ∨
      (PredecessorHalfFin13Atom0367 chi ∧
      PredecessorHalfFin13Atom0368 chi ∧
      PredecessorHalfFin13Atom0371 chi ∧
      PredecessorHalfFin13Atom0377 chi ∧
      PredecessorHalfFin13Atom0380 chi ∧
      PredecessorHalfFin13Atom0383 chi ∧
      PredecessorHalfFin13Atom0477 chi ∧
      PredecessorHalfFin13Atom0480 chi ∧
      PredecessorHalfFin13Atom0483 chi ∧
      PredecessorHalfFin13Atom0499 chi ∧
      PredecessorHalfFin13Atom0762 chi ∧
      PredecessorHalfFin13Atom0765 chi ∧
      PredecessorHalfFin13Atom0768 chi ∧
      PredecessorHalfFin13Atom0784 chi ∧
      PredecessorHalfFin13Atom0979 chi)))))) ∨
      (((((PredecessorHalfFin13Atom0367 chi ∧
      PredecessorHalfFin13Atom0369 chi ∧
      PredecessorHalfFin13Atom0371 chi ∧
      PredecessorHalfFin13Atom0378 chi ∧
      PredecessorHalfFin13Atom0380 chi ∧
      PredecessorHalfFin13Atom0385 chi ∧
      PredecessorHalfFin13Atom0478 chi ∧
      PredecessorHalfFin13Atom0480 chi ∧
      PredecessorHalfFin13Atom0485 chi ∧
      PredecessorHalfFin13Atom0501 chi ∧
      PredecessorHalfFin13Atom0763 chi ∧
      PredecessorHalfFin13Atom0765 chi ∧
      PredecessorHalfFin13Atom0770 chi ∧
      PredecessorHalfFin13Atom0786 chi ∧
      PredecessorHalfFin13Atom0981 chi) ∨
      ((PredecessorHalfFin13Atom0368 chi ∧
      PredecessorHalfFin13Atom0369 chi ∧
      PredecessorHalfFin13Atom0371 chi ∧
      PredecessorHalfFin13Atom0381 chi ∧
      PredecessorHalfFin13Atom0383 chi ∧
      PredecessorHalfFin13Atom0385 chi ∧
      PredecessorHalfFin13Atom0481 chi ∧
      PredecessorHalfFin13Atom0483 chi ∧
      PredecessorHalfFin13Atom0485 chi ∧
      PredecessorHalfFin13Atom0504 chi ∧
      PredecessorHalfFin13Atom0766 chi ∧
      PredecessorHalfFin13Atom0768 chi ∧
      PredecessorHalfFin13Atom0770 chi ∧
      PredecessorHalfFin13Atom0789 chi ∧
      PredecessorHalfFin13Atom0984 chi) ∨
      (PredecessorHalfFin13Atom0372 chi ∧
      PredecessorHalfFin13Atom0373 chi ∧
      PredecessorHalfFin13Atom0374 chi ∧
      PredecessorHalfFin13Atom0377 chi ∧
      PredecessorHalfFin13Atom0378 chi ∧
      PredecessorHalfFin13Atom0381 chi ∧
      PredecessorHalfFin13Atom0487 chi ∧
      PredecessorHalfFin13Atom0488 chi ∧
      PredecessorHalfFin13Atom0491 chi ∧
      PredecessorHalfFin13Atom0497 chi ∧
      PredecessorHalfFin13Atom0772 chi ∧
      PredecessorHalfFin13Atom0773 chi ∧
      PredecessorHalfFin13Atom0776 chi ∧
      PredecessorHalfFin13Atom0782 chi ∧
      PredecessorHalfFin13Atom0987 chi))) ∨
      ((PredecessorHalfFin13Atom0372 chi ∧
      PredecessorHalfFin13Atom0374 chi ∧
      PredecessorHalfFin13Atom0376 chi ∧
      PredecessorHalfFin13Atom0378 chi ∧
      PredecessorHalfFin13Atom0380 chi ∧
      PredecessorHalfFin13Atom0385 chi ∧
      PredecessorHalfFin13Atom0488 chi ∧
      PredecessorHalfFin13Atom0490 chi ∧
      PredecessorHalfFin13Atom0495 chi ∧
      PredecessorHalfFin13Atom0501 chi ∧
      PredecessorHalfFin13Atom0773 chi ∧
      PredecessorHalfFin13Atom0775 chi ∧
      PredecessorHalfFin13Atom0780 chi ∧
      PredecessorHalfFin13Atom0786 chi ∧
      PredecessorHalfFin13Atom0991 chi) ∨
      ((PredecessorHalfFin13Atom0373 chi ∧
      PredecessorHalfFin13Atom0374 chi ∧
      PredecessorHalfFin13Atom0376 chi ∧
      PredecessorHalfFin13Atom0381 chi ∧
      PredecessorHalfFin13Atom0383 chi ∧
      PredecessorHalfFin13Atom0385 chi ∧
      PredecessorHalfFin13Atom0491 chi ∧
      PredecessorHalfFin13Atom0493 chi ∧
      PredecessorHalfFin13Atom0495 chi ∧
      PredecessorHalfFin13Atom0504 chi ∧
      PredecessorHalfFin13Atom0776 chi ∧
      PredecessorHalfFin13Atom0778 chi ∧
      PredecessorHalfFin13Atom0780 chi ∧
      PredecessorHalfFin13Atom0789 chi ∧
      PredecessorHalfFin13Atom0994 chi) ∨
      (PredecessorHalfFin13Atom0387 chi ∧
      PredecessorHalfFin13Atom0388 chi ∧
      PredecessorHalfFin13Atom0389 chi ∧
      PredecessorHalfFin13Atom0395 chi ∧
      PredecessorHalfFin13Atom0396 chi ∧
      PredecessorHalfFin13Atom0402 chi ∧
      PredecessorHalfFin13Atom0423 chi ∧
      PredecessorHalfFin13Atom0424 chi ∧
      PredecessorHalfFin13Atom0430 chi ∧
      PredecessorHalfFin13Atom0451 chi ∧
      PredecessorHalfFin13Atom0792 chi ∧
      PredecessorHalfFin13Atom0793 chi ∧
      PredecessorHalfFin13Atom0799 chi ∧
      PredecessorHalfFin13Atom0820 chi ∧
      PredecessorHalfFin13Atom0876 chi)))) ∨
      (((PredecessorHalfFin13Atom0387 chi ∧
      PredecessorHalfFin13Atom0388 chi ∧
      PredecessorHalfFin13Atom0390 chi ∧
      PredecessorHalfFin13Atom0395 chi ∧
      PredecessorHalfFin13Atom0397 chi ∧
      PredecessorHalfFin13Atom0403 chi ∧
      PredecessorHalfFin13Atom0423 chi ∧
      PredecessorHalfFin13Atom0425 chi ∧
      PredecessorHalfFin13Atom0431 chi ∧
      PredecessorHalfFin13Atom0452 chi ∧
      PredecessorHalfFin13Atom0792 chi ∧
      PredecessorHalfFin13Atom0794 chi ∧
      PredecessorHalfFin13Atom0800 chi ∧
      PredecessorHalfFin13Atom0821 chi ∧
      PredecessorHalfFin13Atom0877 chi) ∨
      ((PredecessorHalfFin13Atom0387 chi ∧
      PredecessorHalfFin13Atom0388 chi ∧
      PredecessorHalfFin13Atom0391 chi ∧
      PredecessorHalfFin13Atom0395 chi ∧
      PredecessorHalfFin13Atom0398 chi ∧
      PredecessorHalfFin13Atom0404 chi ∧
      PredecessorHalfFin13Atom0423 chi ∧
      PredecessorHalfFin13Atom0426 chi ∧
      PredecessorHalfFin13Atom0432 chi ∧
      PredecessorHalfFin13Atom0453 chi ∧
      PredecessorHalfFin13Atom0792 chi ∧
      PredecessorHalfFin13Atom0795 chi ∧
      PredecessorHalfFin13Atom0801 chi ∧
      PredecessorHalfFin13Atom0822 chi ∧
      PredecessorHalfFin13Atom0878 chi) ∨
      (PredecessorHalfFin13Atom0387 chi ∧
      PredecessorHalfFin13Atom0388 chi ∧
      PredecessorHalfFin13Atom0392 chi ∧
      PredecessorHalfFin13Atom0395 chi ∧
      PredecessorHalfFin13Atom0399 chi ∧
      PredecessorHalfFin13Atom0405 chi ∧
      PredecessorHalfFin13Atom0423 chi ∧
      PredecessorHalfFin13Atom0427 chi ∧
      PredecessorHalfFin13Atom0433 chi ∧
      PredecessorHalfFin13Atom0454 chi ∧
      PredecessorHalfFin13Atom0792 chi ∧
      PredecessorHalfFin13Atom0796 chi ∧
      PredecessorHalfFin13Atom0802 chi ∧
      PredecessorHalfFin13Atom0823 chi ∧
      PredecessorHalfFin13Atom0879 chi))) ∨
      ((PredecessorHalfFin13Atom0387 chi ∧
      PredecessorHalfFin13Atom0388 chi ∧
      PredecessorHalfFin13Atom0394 chi ∧
      PredecessorHalfFin13Atom0395 chi ∧
      PredecessorHalfFin13Atom0401 chi ∧
      PredecessorHalfFin13Atom0407 chi ∧
      PredecessorHalfFin13Atom0423 chi ∧
      PredecessorHalfFin13Atom0429 chi ∧
      PredecessorHalfFin13Atom0435 chi ∧
      PredecessorHalfFin13Atom0456 chi ∧
      PredecessorHalfFin13Atom0792 chi ∧
      PredecessorHalfFin13Atom0798 chi ∧
      PredecessorHalfFin13Atom0804 chi ∧
      PredecessorHalfFin13Atom0825 chi ∧
      PredecessorHalfFin13Atom0881 chi) ∨
      ((PredecessorHalfFin13Atom0387 chi ∧
      PredecessorHalfFin13Atom0389 chi ∧
      PredecessorHalfFin13Atom0390 chi ∧
      PredecessorHalfFin13Atom0396 chi ∧
      PredecessorHalfFin13Atom0397 chi ∧
      PredecessorHalfFin13Atom0408 chi ∧
      PredecessorHalfFin13Atom0424 chi ∧
      PredecessorHalfFin13Atom0425 chi ∧
      PredecessorHalfFin13Atom0436 chi ∧
      PredecessorHalfFin13Atom0457 chi ∧
      PredecessorHalfFin13Atom0793 chi ∧
      PredecessorHalfFin13Atom0794 chi ∧
      PredecessorHalfFin13Atom0805 chi ∧
      PredecessorHalfFin13Atom0826 chi ∧
      PredecessorHalfFin13Atom0882 chi) ∨
      (PredecessorHalfFin13Atom0387 chi ∧
      PredecessorHalfFin13Atom0389 chi ∧
      PredecessorHalfFin13Atom0391 chi ∧
      PredecessorHalfFin13Atom0396 chi ∧
      PredecessorHalfFin13Atom0398 chi ∧
      PredecessorHalfFin13Atom0409 chi ∧
      PredecessorHalfFin13Atom0424 chi ∧
      PredecessorHalfFin13Atom0426 chi ∧
      PredecessorHalfFin13Atom0437 chi ∧
      PredecessorHalfFin13Atom0458 chi ∧
      PredecessorHalfFin13Atom0793 chi ∧
      PredecessorHalfFin13Atom0795 chi ∧
      PredecessorHalfFin13Atom0806 chi ∧
      PredecessorHalfFin13Atom0827 chi ∧
      PredecessorHalfFin13Atom0883 chi))))) ∨
      ((((PredecessorHalfFin13Atom0387 chi ∧
      PredecessorHalfFin13Atom0389 chi ∧
      PredecessorHalfFin13Atom0392 chi ∧
      PredecessorHalfFin13Atom0396 chi ∧
      PredecessorHalfFin13Atom0399 chi ∧
      PredecessorHalfFin13Atom0410 chi ∧
      PredecessorHalfFin13Atom0424 chi ∧
      PredecessorHalfFin13Atom0427 chi ∧
      PredecessorHalfFin13Atom0438 chi ∧
      PredecessorHalfFin13Atom0459 chi ∧
      PredecessorHalfFin13Atom0793 chi ∧
      PredecessorHalfFin13Atom0796 chi ∧
      PredecessorHalfFin13Atom0807 chi ∧
      PredecessorHalfFin13Atom0828 chi ∧
      PredecessorHalfFin13Atom0884 chi) ∨
      ((PredecessorHalfFin13Atom0387 chi ∧
      PredecessorHalfFin13Atom0389 chi ∧
      PredecessorHalfFin13Atom0394 chi ∧
      PredecessorHalfFin13Atom0396 chi ∧
      PredecessorHalfFin13Atom0401 chi ∧
      PredecessorHalfFin13Atom0412 chi ∧
      PredecessorHalfFin13Atom0424 chi ∧
      PredecessorHalfFin13Atom0429 chi ∧
      PredecessorHalfFin13Atom0440 chi ∧
      PredecessorHalfFin13Atom0461 chi ∧
      PredecessorHalfFin13Atom0793 chi ∧
      PredecessorHalfFin13Atom0798 chi ∧
      PredecessorHalfFin13Atom0809 chi ∧
      PredecessorHalfFin13Atom0830 chi ∧
      PredecessorHalfFin13Atom0886 chi) ∨
      (PredecessorHalfFin13Atom0387 chi ∧
      PredecessorHalfFin13Atom0390 chi ∧
      PredecessorHalfFin13Atom0391 chi ∧
      PredecessorHalfFin13Atom0397 chi ∧
      PredecessorHalfFin13Atom0398 chi ∧
      PredecessorHalfFin13Atom0413 chi ∧
      PredecessorHalfFin13Atom0425 chi ∧
      PredecessorHalfFin13Atom0426 chi ∧
      PredecessorHalfFin13Atom0441 chi ∧
      PredecessorHalfFin13Atom0462 chi ∧
      PredecessorHalfFin13Atom0794 chi ∧
      PredecessorHalfFin13Atom0795 chi ∧
      PredecessorHalfFin13Atom0810 chi ∧
      PredecessorHalfFin13Atom0831 chi ∧
      PredecessorHalfFin13Atom0887 chi))) ∨
      ((PredecessorHalfFin13Atom0387 chi ∧
      PredecessorHalfFin13Atom0390 chi ∧
      PredecessorHalfFin13Atom0392 chi ∧
      PredecessorHalfFin13Atom0397 chi ∧
      PredecessorHalfFin13Atom0399 chi ∧
      PredecessorHalfFin13Atom0414 chi ∧
      PredecessorHalfFin13Atom0425 chi ∧
      PredecessorHalfFin13Atom0427 chi ∧
      PredecessorHalfFin13Atom0442 chi ∧
      PredecessorHalfFin13Atom0463 chi ∧
      PredecessorHalfFin13Atom0794 chi ∧
      PredecessorHalfFin13Atom0796 chi ∧
      PredecessorHalfFin13Atom0811 chi ∧
      PredecessorHalfFin13Atom0832 chi ∧
      PredecessorHalfFin13Atom0888 chi) ∨
      ((PredecessorHalfFin13Atom0387 chi ∧
      PredecessorHalfFin13Atom0390 chi ∧
      PredecessorHalfFin13Atom0394 chi ∧
      PredecessorHalfFin13Atom0397 chi ∧
      PredecessorHalfFin13Atom0401 chi ∧
      PredecessorHalfFin13Atom0416 chi ∧
      PredecessorHalfFin13Atom0425 chi ∧
      PredecessorHalfFin13Atom0429 chi ∧
      PredecessorHalfFin13Atom0444 chi ∧
      PredecessorHalfFin13Atom0465 chi ∧
      PredecessorHalfFin13Atom0794 chi ∧
      PredecessorHalfFin13Atom0798 chi ∧
      PredecessorHalfFin13Atom0813 chi ∧
      PredecessorHalfFin13Atom0834 chi ∧
      PredecessorHalfFin13Atom0890 chi) ∨
      (PredecessorHalfFin13Atom0387 chi ∧
      PredecessorHalfFin13Atom0391 chi ∧
      PredecessorHalfFin13Atom0392 chi ∧
      PredecessorHalfFin13Atom0398 chi ∧
      PredecessorHalfFin13Atom0399 chi ∧
      PredecessorHalfFin13Atom0417 chi ∧
      PredecessorHalfFin13Atom0426 chi ∧
      PredecessorHalfFin13Atom0427 chi ∧
      PredecessorHalfFin13Atom0445 chi ∧
      PredecessorHalfFin13Atom0466 chi ∧
      PredecessorHalfFin13Atom0795 chi ∧
      PredecessorHalfFin13Atom0796 chi ∧
      PredecessorHalfFin13Atom0814 chi ∧
      PredecessorHalfFin13Atom0835 chi ∧
      PredecessorHalfFin13Atom0891 chi)))) ∨
      (((PredecessorHalfFin13Atom0387 chi ∧
      PredecessorHalfFin13Atom0391 chi ∧
      PredecessorHalfFin13Atom0394 chi ∧
      PredecessorHalfFin13Atom0398 chi ∧
      PredecessorHalfFin13Atom0401 chi ∧
      PredecessorHalfFin13Atom0419 chi ∧
      PredecessorHalfFin13Atom0426 chi ∧
      PredecessorHalfFin13Atom0429 chi ∧
      PredecessorHalfFin13Atom0447 chi ∧
      PredecessorHalfFin13Atom0468 chi ∧
      PredecessorHalfFin13Atom0795 chi ∧
      PredecessorHalfFin13Atom0798 chi ∧
      PredecessorHalfFin13Atom0816 chi ∧
      PredecessorHalfFin13Atom0837 chi ∧
      PredecessorHalfFin13Atom0893 chi) ∨
      ((PredecessorHalfFin13Atom0387 chi ∧
      PredecessorHalfFin13Atom0392 chi ∧
      PredecessorHalfFin13Atom0394 chi ∧
      PredecessorHalfFin13Atom0399 chi ∧
      PredecessorHalfFin13Atom0401 chi ∧
      PredecessorHalfFin13Atom0421 chi ∧
      PredecessorHalfFin13Atom0427 chi ∧
      PredecessorHalfFin13Atom0429 chi ∧
      PredecessorHalfFin13Atom0449 chi ∧
      PredecessorHalfFin13Atom0470 chi ∧
      PredecessorHalfFin13Atom0796 chi ∧
      PredecessorHalfFin13Atom0798 chi ∧
      PredecessorHalfFin13Atom0818 chi ∧
      PredecessorHalfFin13Atom0839 chi ∧
      PredecessorHalfFin13Atom0895 chi) ∨
      (PredecessorHalfFin13Atom0388 chi ∧
      PredecessorHalfFin13Atom0389 chi ∧
      PredecessorHalfFin13Atom0390 chi ∧
      PredecessorHalfFin13Atom0402 chi ∧
      PredecessorHalfFin13Atom0403 chi ∧
      PredecessorHalfFin13Atom0408 chi ∧
      PredecessorHalfFin13Atom0430 chi ∧
      PredecessorHalfFin13Atom0431 chi ∧
      PredecessorHalfFin13Atom0436 chi ∧
      PredecessorHalfFin13Atom0472 chi ∧
      PredecessorHalfFin13Atom0799 chi ∧
      PredecessorHalfFin13Atom0800 chi ∧
      PredecessorHalfFin13Atom0805 chi ∧
      PredecessorHalfFin13Atom0841 chi ∧
      PredecessorHalfFin13Atom0897 chi))) ∨
      (((PredecessorHalfFin13Atom0388 chi ∧
      PredecessorHalfFin13Atom0389 chi ∧
      PredecessorHalfFin13Atom0392 chi ∧
      PredecessorHalfFin13Atom0402 chi ∧
      PredecessorHalfFin13Atom0405 chi ∧
      PredecessorHalfFin13Atom0410 chi ∧
      PredecessorHalfFin13Atom0430 chi ∧
      PredecessorHalfFin13Atom0433 chi ∧
      PredecessorHalfFin13Atom0438 chi ∧
      PredecessorHalfFin13Atom0474 chi ∧
      PredecessorHalfFin13Atom0799 chi ∧
      PredecessorHalfFin13Atom0802 chi ∧
      PredecessorHalfFin13Atom0807 chi ∧
      PredecessorHalfFin13Atom0843 chi ∧
      PredecessorHalfFin13Atom0899 chi) ∨
      (PredecessorHalfFin13Atom0388 chi ∧
      PredecessorHalfFin13Atom0389 chi ∧
      PredecessorHalfFin13Atom0394 chi ∧
      PredecessorHalfFin13Atom0402 chi ∧
      PredecessorHalfFin13Atom0407 chi ∧
      PredecessorHalfFin13Atom0412 chi ∧
      PredecessorHalfFin13Atom0430 chi ∧
      PredecessorHalfFin13Atom0435 chi ∧
      PredecessorHalfFin13Atom0440 chi ∧
      PredecessorHalfFin13Atom0476 chi ∧
      PredecessorHalfFin13Atom0799 chi ∧
      PredecessorHalfFin13Atom0804 chi ∧
      PredecessorHalfFin13Atom0809 chi ∧
      PredecessorHalfFin13Atom0845 chi ∧
      PredecessorHalfFin13Atom0901 chi)) ∨
      ((PredecessorHalfFin13Atom0388 chi ∧
      PredecessorHalfFin13Atom0390 chi ∧
      PredecessorHalfFin13Atom0391 chi ∧
      PredecessorHalfFin13Atom0403 chi ∧
      PredecessorHalfFin13Atom0404 chi ∧
      PredecessorHalfFin13Atom0413 chi ∧
      PredecessorHalfFin13Atom0431 chi ∧
      PredecessorHalfFin13Atom0432 chi ∧
      PredecessorHalfFin13Atom0441 chi ∧
      PredecessorHalfFin13Atom0477 chi ∧
      PredecessorHalfFin13Atom0800 chi ∧
      PredecessorHalfFin13Atom0801 chi ∧
      PredecessorHalfFin13Atom0810 chi ∧
      PredecessorHalfFin13Atom0846 chi ∧
      PredecessorHalfFin13Atom0902 chi) ∨
      (PredecessorHalfFin13Atom0388 chi ∧
      PredecessorHalfFin13Atom0390 chi ∧
      PredecessorHalfFin13Atom0392 chi ∧
      PredecessorHalfFin13Atom0403 chi ∧
      PredecessorHalfFin13Atom0405 chi ∧
      PredecessorHalfFin13Atom0414 chi ∧
      PredecessorHalfFin13Atom0431 chi ∧
      PredecessorHalfFin13Atom0433 chi ∧
      PredecessorHalfFin13Atom0442 chi ∧
      PredecessorHalfFin13Atom0478 chi ∧
      PredecessorHalfFin13Atom0800 chi ∧
      PredecessorHalfFin13Atom0802 chi ∧
      PredecessorHalfFin13Atom0811 chi ∧
      PredecessorHalfFin13Atom0847 chi ∧
      PredecessorHalfFin13Atom0903 chi))))))))) := by
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
              exact predecessorHalfFin13_clause25273 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause25275 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause25277 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause25278 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause25280 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause25281 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause25283 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause25285 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause25287 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause25289 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause25291 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause25294 chi hnoStrong hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause25297 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause25298 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause25299 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause25300 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause25302 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause25303 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause25304 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause25305 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause25307 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause25308 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause25309 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause25311 chi hnoStrong hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause25312 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause25314 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause25316 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause25318 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause25319 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause25320 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause25323 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause25324 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause25326 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause25327 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause25329 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause25331 chi hnoStrong hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause25333 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause25334 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause25336 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause25337 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause25339 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause25341 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause25343 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause25345 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause25347 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause25350 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause25353 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause25354 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause25355 chi hnoStrong hbad
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
              exact predecessorHalfFin13_clause25358 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause25359 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause25361 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause25362 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause25364 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause25366 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause25368 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause25369 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause25371 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause25372 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause25374 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause25376 chi hnoStrong hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause25378 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause25380 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause25382 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause25385 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause25388 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause25389 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause25391 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause25392 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause25394 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause25396 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause25398 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause25400 chi hnoStrong hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause25402 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause25405 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause25408 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause25412 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause25415 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause25423 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause25424 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause25425 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause25426 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause25428 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause25429 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause25430 chi hnoStrong hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause25431 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause25433 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause25434 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause25435 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause25437 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause25438 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause25440 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause25442 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause25444 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause25446 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause25448 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause25449 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause25450 chi hnoStrong hbad

end ErdosSzekeres

end
