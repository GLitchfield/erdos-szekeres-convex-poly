module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk091
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk092

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 119. -/

theorem predecessorHalfFin13_rejectSemanticSegment119
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((PredecessorHalfFin13Atom0388 chi ∧
      PredecessorHalfFin13Atom0390 chi ∧
      PredecessorHalfFin13Atom0394 chi ∧
      PredecessorHalfFin13Atom0403 chi ∧
      PredecessorHalfFin13Atom0407 chi ∧
      PredecessorHalfFin13Atom0416 chi ∧
      PredecessorHalfFin13Atom0431 chi ∧
      PredecessorHalfFin13Atom0435 chi ∧
      PredecessorHalfFin13Atom0444 chi ∧
      PredecessorHalfFin13Atom0480 chi ∧
      PredecessorHalfFin13Atom0800 chi ∧
      PredecessorHalfFin13Atom0804 chi ∧
      PredecessorHalfFin13Atom0813 chi ∧
      PredecessorHalfFin13Atom0849 chi ∧
      PredecessorHalfFin13Atom0905 chi) ∨
      ((PredecessorHalfFin13Atom0388 chi ∧
      PredecessorHalfFin13Atom0391 chi ∧
      PredecessorHalfFin13Atom0392 chi ∧
      PredecessorHalfFin13Atom0404 chi ∧
      PredecessorHalfFin13Atom0405 chi ∧
      PredecessorHalfFin13Atom0417 chi ∧
      PredecessorHalfFin13Atom0432 chi ∧
      PredecessorHalfFin13Atom0433 chi ∧
      PredecessorHalfFin13Atom0445 chi ∧
      PredecessorHalfFin13Atom0481 chi ∧
      PredecessorHalfFin13Atom0801 chi ∧
      PredecessorHalfFin13Atom0802 chi ∧
      PredecessorHalfFin13Atom0814 chi ∧
      PredecessorHalfFin13Atom0850 chi ∧
      PredecessorHalfFin13Atom0906 chi) ∨
      (PredecessorHalfFin13Atom0388 chi ∧
      PredecessorHalfFin13Atom0391 chi ∧
      PredecessorHalfFin13Atom0394 chi ∧
      PredecessorHalfFin13Atom0404 chi ∧
      PredecessorHalfFin13Atom0407 chi ∧
      PredecessorHalfFin13Atom0419 chi ∧
      PredecessorHalfFin13Atom0432 chi ∧
      PredecessorHalfFin13Atom0435 chi ∧
      PredecessorHalfFin13Atom0447 chi ∧
      PredecessorHalfFin13Atom0483 chi ∧
      PredecessorHalfFin13Atom0801 chi ∧
      PredecessorHalfFin13Atom0804 chi ∧
      PredecessorHalfFin13Atom0816 chi ∧
      PredecessorHalfFin13Atom0852 chi ∧
      PredecessorHalfFin13Atom0908 chi))) ∨
      ((PredecessorHalfFin13Atom0388 chi ∧
      PredecessorHalfFin13Atom0392 chi ∧
      PredecessorHalfFin13Atom0394 chi ∧
      PredecessorHalfFin13Atom0405 chi ∧
      PredecessorHalfFin13Atom0407 chi ∧
      PredecessorHalfFin13Atom0421 chi ∧
      PredecessorHalfFin13Atom0433 chi ∧
      PredecessorHalfFin13Atom0435 chi ∧
      PredecessorHalfFin13Atom0449 chi ∧
      PredecessorHalfFin13Atom0485 chi ∧
      PredecessorHalfFin13Atom0802 chi ∧
      PredecessorHalfFin13Atom0804 chi ∧
      PredecessorHalfFin13Atom0818 chi ∧
      PredecessorHalfFin13Atom0854 chi ∧
      PredecessorHalfFin13Atom0910 chi) ∨
      ((PredecessorHalfFin13Atom0389 chi ∧
      PredecessorHalfFin13Atom0390 chi ∧
      PredecessorHalfFin13Atom0391 chi ∧
      PredecessorHalfFin13Atom0408 chi ∧
      PredecessorHalfFin13Atom0409 chi ∧
      PredecessorHalfFin13Atom0413 chi ∧
      PredecessorHalfFin13Atom0436 chi ∧
      PredecessorHalfFin13Atom0437 chi ∧
      PredecessorHalfFin13Atom0441 chi ∧
      PredecessorHalfFin13Atom0487 chi ∧
      PredecessorHalfFin13Atom0805 chi ∧
      PredecessorHalfFin13Atom0806 chi ∧
      PredecessorHalfFin13Atom0810 chi ∧
      PredecessorHalfFin13Atom0856 chi ∧
      PredecessorHalfFin13Atom0912 chi) ∨
      (PredecessorHalfFin13Atom0389 chi ∧
      PredecessorHalfFin13Atom0390 chi ∧
      PredecessorHalfFin13Atom0392 chi ∧
      PredecessorHalfFin13Atom0408 chi ∧
      PredecessorHalfFin13Atom0410 chi ∧
      PredecessorHalfFin13Atom0414 chi ∧
      PredecessorHalfFin13Atom0436 chi ∧
      PredecessorHalfFin13Atom0438 chi ∧
      PredecessorHalfFin13Atom0442 chi ∧
      PredecessorHalfFin13Atom0488 chi ∧
      PredecessorHalfFin13Atom0805 chi ∧
      PredecessorHalfFin13Atom0807 chi ∧
      PredecessorHalfFin13Atom0811 chi ∧
      PredecessorHalfFin13Atom0857 chi ∧
      PredecessorHalfFin13Atom0913 chi)))) ∨
      (((PredecessorHalfFin13Atom0389 chi ∧
      PredecessorHalfFin13Atom0390 chi ∧
      PredecessorHalfFin13Atom0394 chi ∧
      PredecessorHalfFin13Atom0408 chi ∧
      PredecessorHalfFin13Atom0412 chi ∧
      PredecessorHalfFin13Atom0416 chi ∧
      PredecessorHalfFin13Atom0436 chi ∧
      PredecessorHalfFin13Atom0440 chi ∧
      PredecessorHalfFin13Atom0444 chi ∧
      PredecessorHalfFin13Atom0490 chi ∧
      PredecessorHalfFin13Atom0805 chi ∧
      PredecessorHalfFin13Atom0809 chi ∧
      PredecessorHalfFin13Atom0813 chi ∧
      PredecessorHalfFin13Atom0859 chi ∧
      PredecessorHalfFin13Atom0915 chi) ∨
      ((PredecessorHalfFin13Atom0389 chi ∧
      PredecessorHalfFin13Atom0391 chi ∧
      PredecessorHalfFin13Atom0392 chi ∧
      PredecessorHalfFin13Atom0409 chi ∧
      PredecessorHalfFin13Atom0410 chi ∧
      PredecessorHalfFin13Atom0417 chi ∧
      PredecessorHalfFin13Atom0437 chi ∧
      PredecessorHalfFin13Atom0438 chi ∧
      PredecessorHalfFin13Atom0445 chi ∧
      PredecessorHalfFin13Atom0491 chi ∧
      PredecessorHalfFin13Atom0806 chi ∧
      PredecessorHalfFin13Atom0807 chi ∧
      PredecessorHalfFin13Atom0814 chi ∧
      PredecessorHalfFin13Atom0860 chi ∧
      PredecessorHalfFin13Atom0916 chi) ∨
      (PredecessorHalfFin13Atom0389 chi ∧
      PredecessorHalfFin13Atom0391 chi ∧
      PredecessorHalfFin13Atom0394 chi ∧
      PredecessorHalfFin13Atom0409 chi ∧
      PredecessorHalfFin13Atom0412 chi ∧
      PredecessorHalfFin13Atom0419 chi ∧
      PredecessorHalfFin13Atom0437 chi ∧
      PredecessorHalfFin13Atom0440 chi ∧
      PredecessorHalfFin13Atom0447 chi ∧
      PredecessorHalfFin13Atom0493 chi ∧
      PredecessorHalfFin13Atom0806 chi ∧
      PredecessorHalfFin13Atom0809 chi ∧
      PredecessorHalfFin13Atom0816 chi ∧
      PredecessorHalfFin13Atom0862 chi ∧
      PredecessorHalfFin13Atom0918 chi))) ∨
      ((PredecessorHalfFin13Atom0389 chi ∧
      PredecessorHalfFin13Atom0392 chi ∧
      PredecessorHalfFin13Atom0394 chi ∧
      PredecessorHalfFin13Atom0410 chi ∧
      PredecessorHalfFin13Atom0412 chi ∧
      PredecessorHalfFin13Atom0421 chi ∧
      PredecessorHalfFin13Atom0438 chi ∧
      PredecessorHalfFin13Atom0440 chi ∧
      PredecessorHalfFin13Atom0449 chi ∧
      PredecessorHalfFin13Atom0495 chi ∧
      PredecessorHalfFin13Atom0807 chi ∧
      PredecessorHalfFin13Atom0809 chi ∧
      PredecessorHalfFin13Atom0818 chi ∧
      PredecessorHalfFin13Atom0864 chi ∧
      PredecessorHalfFin13Atom0920 chi) ∨
      ((PredecessorHalfFin13Atom0390 chi ∧
      PredecessorHalfFin13Atom0391 chi ∧
      PredecessorHalfFin13Atom0392 chi ∧
      PredecessorHalfFin13Atom0413 chi ∧
      PredecessorHalfFin13Atom0414 chi ∧
      PredecessorHalfFin13Atom0417 chi ∧
      PredecessorHalfFin13Atom0441 chi ∧
      PredecessorHalfFin13Atom0442 chi ∧
      PredecessorHalfFin13Atom0445 chi ∧
      PredecessorHalfFin13Atom0497 chi ∧
      PredecessorHalfFin13Atom0810 chi ∧
      PredecessorHalfFin13Atom0811 chi ∧
      PredecessorHalfFin13Atom0814 chi ∧
      PredecessorHalfFin13Atom0866 chi ∧
      PredecessorHalfFin13Atom0922 chi) ∨
      (PredecessorHalfFin13Atom0390 chi ∧
      PredecessorHalfFin13Atom0391 chi ∧
      PredecessorHalfFin13Atom0394 chi ∧
      PredecessorHalfFin13Atom0413 chi ∧
      PredecessorHalfFin13Atom0416 chi ∧
      PredecessorHalfFin13Atom0419 chi ∧
      PredecessorHalfFin13Atom0441 chi ∧
      PredecessorHalfFin13Atom0444 chi ∧
      PredecessorHalfFin13Atom0447 chi ∧
      PredecessorHalfFin13Atom0499 chi ∧
      PredecessorHalfFin13Atom0810 chi ∧
      PredecessorHalfFin13Atom0813 chi ∧
      PredecessorHalfFin13Atom0816 chi ∧
      PredecessorHalfFin13Atom0868 chi ∧
      PredecessorHalfFin13Atom0924 chi))))) ∨
      ((((PredecessorHalfFin13Atom0390 chi ∧
      PredecessorHalfFin13Atom0392 chi ∧
      PredecessorHalfFin13Atom0394 chi ∧
      PredecessorHalfFin13Atom0414 chi ∧
      PredecessorHalfFin13Atom0416 chi ∧
      PredecessorHalfFin13Atom0421 chi ∧
      PredecessorHalfFin13Atom0442 chi ∧
      PredecessorHalfFin13Atom0444 chi ∧
      PredecessorHalfFin13Atom0449 chi ∧
      PredecessorHalfFin13Atom0501 chi ∧
      PredecessorHalfFin13Atom0811 chi ∧
      PredecessorHalfFin13Atom0813 chi ∧
      PredecessorHalfFin13Atom0818 chi ∧
      PredecessorHalfFin13Atom0870 chi ∧
      PredecessorHalfFin13Atom0926 chi) ∨
      ((PredecessorHalfFin13Atom0391 chi ∧
      PredecessorHalfFin13Atom0392 chi ∧
      PredecessorHalfFin13Atom0394 chi ∧
      PredecessorHalfFin13Atom0417 chi ∧
      PredecessorHalfFin13Atom0419 chi ∧
      PredecessorHalfFin13Atom0421 chi ∧
      PredecessorHalfFin13Atom0445 chi ∧
      PredecessorHalfFin13Atom0447 chi ∧
      PredecessorHalfFin13Atom0449 chi ∧
      PredecessorHalfFin13Atom0504 chi ∧
      PredecessorHalfFin13Atom0814 chi ∧
      PredecessorHalfFin13Atom0816 chi ∧
      PredecessorHalfFin13Atom0818 chi ∧
      PredecessorHalfFin13Atom0873 chi ∧
      PredecessorHalfFin13Atom0929 chi) ∨
      (PredecessorHalfFin13Atom0395 chi ∧
      PredecessorHalfFin13Atom0396 chi ∧
      PredecessorHalfFin13Atom0397 chi ∧
      PredecessorHalfFin13Atom0402 chi ∧
      PredecessorHalfFin13Atom0403 chi ∧
      PredecessorHalfFin13Atom0408 chi ∧
      PredecessorHalfFin13Atom0451 chi ∧
      PredecessorHalfFin13Atom0452 chi ∧
      PredecessorHalfFin13Atom0457 chi ∧
      PredecessorHalfFin13Atom0472 chi ∧
      PredecessorHalfFin13Atom0820 chi ∧
      PredecessorHalfFin13Atom0821 chi ∧
      PredecessorHalfFin13Atom0826 chi ∧
      PredecessorHalfFin13Atom0841 chi ∧
      PredecessorHalfFin13Atom0932 chi))) ∨
      ((PredecessorHalfFin13Atom0395 chi ∧
      PredecessorHalfFin13Atom0396 chi ∧
      PredecessorHalfFin13Atom0398 chi ∧
      PredecessorHalfFin13Atom0402 chi ∧
      PredecessorHalfFin13Atom0404 chi ∧
      PredecessorHalfFin13Atom0409 chi ∧
      PredecessorHalfFin13Atom0451 chi ∧
      PredecessorHalfFin13Atom0453 chi ∧
      PredecessorHalfFin13Atom0458 chi ∧
      PredecessorHalfFin13Atom0473 chi ∧
      PredecessorHalfFin13Atom0820 chi ∧
      PredecessorHalfFin13Atom0822 chi ∧
      PredecessorHalfFin13Atom0827 chi ∧
      PredecessorHalfFin13Atom0842 chi ∧
      PredecessorHalfFin13Atom0933 chi) ∨
      ((PredecessorHalfFin13Atom0395 chi ∧
      PredecessorHalfFin13Atom0396 chi ∧
      PredecessorHalfFin13Atom0399 chi ∧
      PredecessorHalfFin13Atom0402 chi ∧
      PredecessorHalfFin13Atom0405 chi ∧
      PredecessorHalfFin13Atom0410 chi ∧
      PredecessorHalfFin13Atom0451 chi ∧
      PredecessorHalfFin13Atom0454 chi ∧
      PredecessorHalfFin13Atom0459 chi ∧
      PredecessorHalfFin13Atom0474 chi ∧
      PredecessorHalfFin13Atom0820 chi ∧
      PredecessorHalfFin13Atom0823 chi ∧
      PredecessorHalfFin13Atom0828 chi ∧
      PredecessorHalfFin13Atom0843 chi ∧
      PredecessorHalfFin13Atom0934 chi) ∨
      (PredecessorHalfFin13Atom0395 chi ∧
      PredecessorHalfFin13Atom0396 chi ∧
      PredecessorHalfFin13Atom0401 chi ∧
      PredecessorHalfFin13Atom0402 chi ∧
      PredecessorHalfFin13Atom0407 chi ∧
      PredecessorHalfFin13Atom0412 chi ∧
      PredecessorHalfFin13Atom0451 chi ∧
      PredecessorHalfFin13Atom0456 chi ∧
      PredecessorHalfFin13Atom0461 chi ∧
      PredecessorHalfFin13Atom0476 chi ∧
      PredecessorHalfFin13Atom0820 chi ∧
      PredecessorHalfFin13Atom0825 chi ∧
      PredecessorHalfFin13Atom0830 chi ∧
      PredecessorHalfFin13Atom0845 chi ∧
      PredecessorHalfFin13Atom0936 chi)))) ∨
      (((PredecessorHalfFin13Atom0395 chi ∧
      PredecessorHalfFin13Atom0397 chi ∧
      PredecessorHalfFin13Atom0398 chi ∧
      PredecessorHalfFin13Atom0403 chi ∧
      PredecessorHalfFin13Atom0404 chi ∧
      PredecessorHalfFin13Atom0413 chi ∧
      PredecessorHalfFin13Atom0452 chi ∧
      PredecessorHalfFin13Atom0453 chi ∧
      PredecessorHalfFin13Atom0462 chi ∧
      PredecessorHalfFin13Atom0477 chi ∧
      PredecessorHalfFin13Atom0821 chi ∧
      PredecessorHalfFin13Atom0822 chi ∧
      PredecessorHalfFin13Atom0831 chi ∧
      PredecessorHalfFin13Atom0846 chi ∧
      PredecessorHalfFin13Atom0937 chi) ∨
      ((PredecessorHalfFin13Atom0395 chi ∧
      PredecessorHalfFin13Atom0397 chi ∧
      PredecessorHalfFin13Atom0399 chi ∧
      PredecessorHalfFin13Atom0403 chi ∧
      PredecessorHalfFin13Atom0405 chi ∧
      PredecessorHalfFin13Atom0414 chi ∧
      PredecessorHalfFin13Atom0452 chi ∧
      PredecessorHalfFin13Atom0454 chi ∧
      PredecessorHalfFin13Atom0463 chi ∧
      PredecessorHalfFin13Atom0478 chi ∧
      PredecessorHalfFin13Atom0821 chi ∧
      PredecessorHalfFin13Atom0823 chi ∧
      PredecessorHalfFin13Atom0832 chi ∧
      PredecessorHalfFin13Atom0847 chi ∧
      PredecessorHalfFin13Atom0938 chi) ∨
      (PredecessorHalfFin13Atom0395 chi ∧
      PredecessorHalfFin13Atom0397 chi ∧
      PredecessorHalfFin13Atom0401 chi ∧
      PredecessorHalfFin13Atom0403 chi ∧
      PredecessorHalfFin13Atom0407 chi ∧
      PredecessorHalfFin13Atom0416 chi ∧
      PredecessorHalfFin13Atom0452 chi ∧
      PredecessorHalfFin13Atom0456 chi ∧
      PredecessorHalfFin13Atom0465 chi ∧
      PredecessorHalfFin13Atom0480 chi ∧
      PredecessorHalfFin13Atom0821 chi ∧
      PredecessorHalfFin13Atom0825 chi ∧
      PredecessorHalfFin13Atom0834 chi ∧
      PredecessorHalfFin13Atom0849 chi ∧
      PredecessorHalfFin13Atom0940 chi))) ∨
      ((PredecessorHalfFin13Atom0395 chi ∧
      PredecessorHalfFin13Atom0398 chi ∧
      PredecessorHalfFin13Atom0399 chi ∧
      PredecessorHalfFin13Atom0404 chi ∧
      PredecessorHalfFin13Atom0405 chi ∧
      PredecessorHalfFin13Atom0417 chi ∧
      PredecessorHalfFin13Atom0453 chi ∧
      PredecessorHalfFin13Atom0454 chi ∧
      PredecessorHalfFin13Atom0466 chi ∧
      PredecessorHalfFin13Atom0481 chi ∧
      PredecessorHalfFin13Atom0822 chi ∧
      PredecessorHalfFin13Atom0823 chi ∧
      PredecessorHalfFin13Atom0835 chi ∧
      PredecessorHalfFin13Atom0850 chi ∧
      PredecessorHalfFin13Atom0941 chi) ∨
      ((PredecessorHalfFin13Atom0395 chi ∧
      PredecessorHalfFin13Atom0398 chi ∧
      PredecessorHalfFin13Atom0401 chi ∧
      PredecessorHalfFin13Atom0404 chi ∧
      PredecessorHalfFin13Atom0407 chi ∧
      PredecessorHalfFin13Atom0419 chi ∧
      PredecessorHalfFin13Atom0453 chi ∧
      PredecessorHalfFin13Atom0456 chi ∧
      PredecessorHalfFin13Atom0468 chi ∧
      PredecessorHalfFin13Atom0483 chi ∧
      PredecessorHalfFin13Atom0822 chi ∧
      PredecessorHalfFin13Atom0825 chi ∧
      PredecessorHalfFin13Atom0837 chi ∧
      PredecessorHalfFin13Atom0852 chi ∧
      PredecessorHalfFin13Atom0943 chi) ∨
      (PredecessorHalfFin13Atom0395 chi ∧
      PredecessorHalfFin13Atom0399 chi ∧
      PredecessorHalfFin13Atom0401 chi ∧
      PredecessorHalfFin13Atom0405 chi ∧
      PredecessorHalfFin13Atom0407 chi ∧
      PredecessorHalfFin13Atom0421 chi ∧
      PredecessorHalfFin13Atom0454 chi ∧
      PredecessorHalfFin13Atom0456 chi ∧
      PredecessorHalfFin13Atom0470 chi ∧
      PredecessorHalfFin13Atom0485 chi ∧
      PredecessorHalfFin13Atom0823 chi ∧
      PredecessorHalfFin13Atom0825 chi ∧
      PredecessorHalfFin13Atom0839 chi ∧
      PredecessorHalfFin13Atom0854 chi ∧
      PredecessorHalfFin13Atom0945 chi)))))) ∨
      (((((PredecessorHalfFin13Atom0396 chi ∧
      PredecessorHalfFin13Atom0397 chi ∧
      PredecessorHalfFin13Atom0398 chi ∧
      PredecessorHalfFin13Atom0408 chi ∧
      PredecessorHalfFin13Atom0409 chi ∧
      PredecessorHalfFin13Atom0413 chi ∧
      PredecessorHalfFin13Atom0457 chi ∧
      PredecessorHalfFin13Atom0458 chi ∧
      PredecessorHalfFin13Atom0462 chi ∧
      PredecessorHalfFin13Atom0487 chi ∧
      PredecessorHalfFin13Atom0826 chi ∧
      PredecessorHalfFin13Atom0827 chi ∧
      PredecessorHalfFin13Atom0831 chi ∧
      PredecessorHalfFin13Atom0856 chi ∧
      PredecessorHalfFin13Atom0947 chi) ∨
      ((PredecessorHalfFin13Atom0396 chi ∧
      PredecessorHalfFin13Atom0397 chi ∧
      PredecessorHalfFin13Atom0399 chi ∧
      PredecessorHalfFin13Atom0408 chi ∧
      PredecessorHalfFin13Atom0410 chi ∧
      PredecessorHalfFin13Atom0414 chi ∧
      PredecessorHalfFin13Atom0457 chi ∧
      PredecessorHalfFin13Atom0459 chi ∧
      PredecessorHalfFin13Atom0463 chi ∧
      PredecessorHalfFin13Atom0488 chi ∧
      PredecessorHalfFin13Atom0826 chi ∧
      PredecessorHalfFin13Atom0828 chi ∧
      PredecessorHalfFin13Atom0832 chi ∧
      PredecessorHalfFin13Atom0857 chi ∧
      PredecessorHalfFin13Atom0948 chi) ∨
      (PredecessorHalfFin13Atom0396 chi ∧
      PredecessorHalfFin13Atom0397 chi ∧
      PredecessorHalfFin13Atom0401 chi ∧
      PredecessorHalfFin13Atom0408 chi ∧
      PredecessorHalfFin13Atom0412 chi ∧
      PredecessorHalfFin13Atom0416 chi ∧
      PredecessorHalfFin13Atom0457 chi ∧
      PredecessorHalfFin13Atom0461 chi ∧
      PredecessorHalfFin13Atom0465 chi ∧
      PredecessorHalfFin13Atom0490 chi ∧
      PredecessorHalfFin13Atom0826 chi ∧
      PredecessorHalfFin13Atom0830 chi ∧
      PredecessorHalfFin13Atom0834 chi ∧
      PredecessorHalfFin13Atom0859 chi ∧
      PredecessorHalfFin13Atom0950 chi))) ∨
      ((PredecessorHalfFin13Atom0396 chi ∧
      PredecessorHalfFin13Atom0398 chi ∧
      PredecessorHalfFin13Atom0399 chi ∧
      PredecessorHalfFin13Atom0409 chi ∧
      PredecessorHalfFin13Atom0410 chi ∧
      PredecessorHalfFin13Atom0417 chi ∧
      PredecessorHalfFin13Atom0458 chi ∧
      PredecessorHalfFin13Atom0459 chi ∧
      PredecessorHalfFin13Atom0466 chi ∧
      PredecessorHalfFin13Atom0491 chi ∧
      PredecessorHalfFin13Atom0827 chi ∧
      PredecessorHalfFin13Atom0828 chi ∧
      PredecessorHalfFin13Atom0835 chi ∧
      PredecessorHalfFin13Atom0860 chi ∧
      PredecessorHalfFin13Atom0951 chi) ∨
      ((PredecessorHalfFin13Atom0396 chi ∧
      PredecessorHalfFin13Atom0398 chi ∧
      PredecessorHalfFin13Atom0401 chi ∧
      PredecessorHalfFin13Atom0409 chi ∧
      PredecessorHalfFin13Atom0412 chi ∧
      PredecessorHalfFin13Atom0419 chi ∧
      PredecessorHalfFin13Atom0458 chi ∧
      PredecessorHalfFin13Atom0461 chi ∧
      PredecessorHalfFin13Atom0468 chi ∧
      PredecessorHalfFin13Atom0493 chi ∧
      PredecessorHalfFin13Atom0827 chi ∧
      PredecessorHalfFin13Atom0830 chi ∧
      PredecessorHalfFin13Atom0837 chi ∧
      PredecessorHalfFin13Atom0862 chi ∧
      PredecessorHalfFin13Atom0953 chi) ∨
      (PredecessorHalfFin13Atom0396 chi ∧
      PredecessorHalfFin13Atom0399 chi ∧
      PredecessorHalfFin13Atom0401 chi ∧
      PredecessorHalfFin13Atom0410 chi ∧
      PredecessorHalfFin13Atom0412 chi ∧
      PredecessorHalfFin13Atom0421 chi ∧
      PredecessorHalfFin13Atom0459 chi ∧
      PredecessorHalfFin13Atom0461 chi ∧
      PredecessorHalfFin13Atom0470 chi ∧
      PredecessorHalfFin13Atom0495 chi ∧
      PredecessorHalfFin13Atom0828 chi ∧
      PredecessorHalfFin13Atom0830 chi ∧
      PredecessorHalfFin13Atom0839 chi ∧
      PredecessorHalfFin13Atom0864 chi ∧
      PredecessorHalfFin13Atom0955 chi)))) ∨
      (((PredecessorHalfFin13Atom0397 chi ∧
      PredecessorHalfFin13Atom0398 chi ∧
      PredecessorHalfFin13Atom0399 chi ∧
      PredecessorHalfFin13Atom0413 chi ∧
      PredecessorHalfFin13Atom0414 chi ∧
      PredecessorHalfFin13Atom0417 chi ∧
      PredecessorHalfFin13Atom0462 chi ∧
      PredecessorHalfFin13Atom0463 chi ∧
      PredecessorHalfFin13Atom0466 chi ∧
      PredecessorHalfFin13Atom0497 chi ∧
      PredecessorHalfFin13Atom0831 chi ∧
      PredecessorHalfFin13Atom0832 chi ∧
      PredecessorHalfFin13Atom0835 chi ∧
      PredecessorHalfFin13Atom0866 chi ∧
      PredecessorHalfFin13Atom0957 chi) ∨
      ((PredecessorHalfFin13Atom0397 chi ∧
      PredecessorHalfFin13Atom0398 chi ∧
      PredecessorHalfFin13Atom0401 chi ∧
      PredecessorHalfFin13Atom0413 chi ∧
      PredecessorHalfFin13Atom0416 chi ∧
      PredecessorHalfFin13Atom0419 chi ∧
      PredecessorHalfFin13Atom0462 chi ∧
      PredecessorHalfFin13Atom0465 chi ∧
      PredecessorHalfFin13Atom0468 chi ∧
      PredecessorHalfFin13Atom0499 chi ∧
      PredecessorHalfFin13Atom0831 chi ∧
      PredecessorHalfFin13Atom0834 chi ∧
      PredecessorHalfFin13Atom0837 chi ∧
      PredecessorHalfFin13Atom0868 chi ∧
      PredecessorHalfFin13Atom0959 chi) ∨
      (PredecessorHalfFin13Atom0397 chi ∧
      PredecessorHalfFin13Atom0399 chi ∧
      PredecessorHalfFin13Atom0401 chi ∧
      PredecessorHalfFin13Atom0414 chi ∧
      PredecessorHalfFin13Atom0416 chi ∧
      PredecessorHalfFin13Atom0421 chi ∧
      PredecessorHalfFin13Atom0463 chi ∧
      PredecessorHalfFin13Atom0465 chi ∧
      PredecessorHalfFin13Atom0470 chi ∧
      PredecessorHalfFin13Atom0501 chi ∧
      PredecessorHalfFin13Atom0832 chi ∧
      PredecessorHalfFin13Atom0834 chi ∧
      PredecessorHalfFin13Atom0839 chi ∧
      PredecessorHalfFin13Atom0870 chi ∧
      PredecessorHalfFin13Atom0961 chi))) ∨
      ((PredecessorHalfFin13Atom0398 chi ∧
      PredecessorHalfFin13Atom0399 chi ∧
      PredecessorHalfFin13Atom0401 chi ∧
      PredecessorHalfFin13Atom0417 chi ∧
      PredecessorHalfFin13Atom0419 chi ∧
      PredecessorHalfFin13Atom0421 chi ∧
      PredecessorHalfFin13Atom0466 chi ∧
      PredecessorHalfFin13Atom0468 chi ∧
      PredecessorHalfFin13Atom0470 chi ∧
      PredecessorHalfFin13Atom0504 chi ∧
      PredecessorHalfFin13Atom0835 chi ∧
      PredecessorHalfFin13Atom0837 chi ∧
      PredecessorHalfFin13Atom0839 chi ∧
      PredecessorHalfFin13Atom0873 chi ∧
      PredecessorHalfFin13Atom0964 chi) ∨
      ((PredecessorHalfFin13Atom0402 chi ∧
      PredecessorHalfFin13Atom0403 chi ∧
      PredecessorHalfFin13Atom0405 chi ∧
      PredecessorHalfFin13Atom0408 chi ∧
      PredecessorHalfFin13Atom0410 chi ∧
      PredecessorHalfFin13Atom0414 chi ∧
      PredecessorHalfFin13Atom0472 chi ∧
      PredecessorHalfFin13Atom0474 chi ∧
      PredecessorHalfFin13Atom0478 chi ∧
      PredecessorHalfFin13Atom0488 chi ∧
      PredecessorHalfFin13Atom0841 chi ∧
      PredecessorHalfFin13Atom0843 chi ∧
      PredecessorHalfFin13Atom0847 chi ∧
      PredecessorHalfFin13Atom0857 chi ∧
      PredecessorHalfFin13Atom0968 chi) ∨
      (PredecessorHalfFin13Atom0402 chi ∧
      PredecessorHalfFin13Atom0404 chi ∧
      PredecessorHalfFin13Atom0405 chi ∧
      PredecessorHalfFin13Atom0409 chi ∧
      PredecessorHalfFin13Atom0410 chi ∧
      PredecessorHalfFin13Atom0417 chi ∧
      PredecessorHalfFin13Atom0473 chi ∧
      PredecessorHalfFin13Atom0474 chi ∧
      PredecessorHalfFin13Atom0481 chi ∧
      PredecessorHalfFin13Atom0491 chi ∧
      PredecessorHalfFin13Atom0842 chi ∧
      PredecessorHalfFin13Atom0843 chi ∧
      PredecessorHalfFin13Atom0850 chi ∧
      PredecessorHalfFin13Atom0860 chi ∧
      PredecessorHalfFin13Atom0971 chi))))) ∨
      ((((PredecessorHalfFin13Atom0402 chi ∧
      PredecessorHalfFin13Atom0404 chi ∧
      PredecessorHalfFin13Atom0407 chi ∧
      PredecessorHalfFin13Atom0409 chi ∧
      PredecessorHalfFin13Atom0412 chi ∧
      PredecessorHalfFin13Atom0419 chi ∧
      PredecessorHalfFin13Atom0473 chi ∧
      PredecessorHalfFin13Atom0476 chi ∧
      PredecessorHalfFin13Atom0483 chi ∧
      PredecessorHalfFin13Atom0493 chi ∧
      PredecessorHalfFin13Atom0842 chi ∧
      PredecessorHalfFin13Atom0845 chi ∧
      PredecessorHalfFin13Atom0852 chi ∧
      PredecessorHalfFin13Atom0862 chi ∧
      PredecessorHalfFin13Atom0973 chi) ∨
      ((PredecessorHalfFin13Atom0402 chi ∧
      PredecessorHalfFin13Atom0405 chi ∧
      PredecessorHalfFin13Atom0407 chi ∧
      PredecessorHalfFin13Atom0410 chi ∧
      PredecessorHalfFin13Atom0412 chi ∧
      PredecessorHalfFin13Atom0421 chi ∧
      PredecessorHalfFin13Atom0474 chi ∧
      PredecessorHalfFin13Atom0476 chi ∧
      PredecessorHalfFin13Atom0485 chi ∧
      PredecessorHalfFin13Atom0495 chi ∧
      PredecessorHalfFin13Atom0843 chi ∧
      PredecessorHalfFin13Atom0845 chi ∧
      PredecessorHalfFin13Atom0854 chi ∧
      PredecessorHalfFin13Atom0864 chi ∧
      PredecessorHalfFin13Atom0975 chi) ∨
      (PredecessorHalfFin13Atom0403 chi ∧
      PredecessorHalfFin13Atom0404 chi ∧
      PredecessorHalfFin13Atom0405 chi ∧
      PredecessorHalfFin13Atom0413 chi ∧
      PredecessorHalfFin13Atom0414 chi ∧
      PredecessorHalfFin13Atom0417 chi ∧
      PredecessorHalfFin13Atom0477 chi ∧
      PredecessorHalfFin13Atom0478 chi ∧
      PredecessorHalfFin13Atom0481 chi ∧
      PredecessorHalfFin13Atom0497 chi ∧
      PredecessorHalfFin13Atom0846 chi ∧
      PredecessorHalfFin13Atom0847 chi ∧
      PredecessorHalfFin13Atom0850 chi ∧
      PredecessorHalfFin13Atom0866 chi ∧
      PredecessorHalfFin13Atom0977 chi))) ∨
      ((PredecessorHalfFin13Atom0403 chi ∧
      PredecessorHalfFin13Atom0405 chi ∧
      PredecessorHalfFin13Atom0407 chi ∧
      PredecessorHalfFin13Atom0414 chi ∧
      PredecessorHalfFin13Atom0416 chi ∧
      PredecessorHalfFin13Atom0421 chi ∧
      PredecessorHalfFin13Atom0478 chi ∧
      PredecessorHalfFin13Atom0480 chi ∧
      PredecessorHalfFin13Atom0485 chi ∧
      PredecessorHalfFin13Atom0501 chi ∧
      PredecessorHalfFin13Atom0847 chi ∧
      PredecessorHalfFin13Atom0849 chi ∧
      PredecessorHalfFin13Atom0854 chi ∧
      PredecessorHalfFin13Atom0870 chi ∧
      PredecessorHalfFin13Atom0981 chi) ∨
      ((PredecessorHalfFin13Atom0404 chi ∧
      PredecessorHalfFin13Atom0405 chi ∧
      PredecessorHalfFin13Atom0407 chi ∧
      PredecessorHalfFin13Atom0417 chi ∧
      PredecessorHalfFin13Atom0419 chi ∧
      PredecessorHalfFin13Atom0421 chi ∧
      PredecessorHalfFin13Atom0481 chi ∧
      PredecessorHalfFin13Atom0483 chi ∧
      PredecessorHalfFin13Atom0485 chi ∧
      PredecessorHalfFin13Atom0504 chi ∧
      PredecessorHalfFin13Atom0850 chi ∧
      PredecessorHalfFin13Atom0852 chi ∧
      PredecessorHalfFin13Atom0854 chi ∧
      PredecessorHalfFin13Atom0873 chi ∧
      PredecessorHalfFin13Atom0984 chi) ∨
      (PredecessorHalfFin13Atom0408 chi ∧
      PredecessorHalfFin13Atom0409 chi ∧
      PredecessorHalfFin13Atom0410 chi ∧
      PredecessorHalfFin13Atom0413 chi ∧
      PredecessorHalfFin13Atom0414 chi ∧
      PredecessorHalfFin13Atom0417 chi ∧
      PredecessorHalfFin13Atom0487 chi ∧
      PredecessorHalfFin13Atom0488 chi ∧
      PredecessorHalfFin13Atom0491 chi ∧
      PredecessorHalfFin13Atom0497 chi ∧
      PredecessorHalfFin13Atom0856 chi ∧
      PredecessorHalfFin13Atom0857 chi ∧
      PredecessorHalfFin13Atom0860 chi ∧
      PredecessorHalfFin13Atom0866 chi ∧
      PredecessorHalfFin13Atom0987 chi)))) ∨
      (((PredecessorHalfFin13Atom0408 chi ∧
      PredecessorHalfFin13Atom0409 chi ∧
      PredecessorHalfFin13Atom0412 chi ∧
      PredecessorHalfFin13Atom0413 chi ∧
      PredecessorHalfFin13Atom0416 chi ∧
      PredecessorHalfFin13Atom0419 chi ∧
      PredecessorHalfFin13Atom0487 chi ∧
      PredecessorHalfFin13Atom0490 chi ∧
      PredecessorHalfFin13Atom0493 chi ∧
      PredecessorHalfFin13Atom0499 chi ∧
      PredecessorHalfFin13Atom0856 chi ∧
      PredecessorHalfFin13Atom0859 chi ∧
      PredecessorHalfFin13Atom0862 chi ∧
      PredecessorHalfFin13Atom0868 chi ∧
      PredecessorHalfFin13Atom0989 chi) ∨
      ((PredecessorHalfFin13Atom0408 chi ∧
      PredecessorHalfFin13Atom0410 chi ∧
      PredecessorHalfFin13Atom0412 chi ∧
      PredecessorHalfFin13Atom0414 chi ∧
      PredecessorHalfFin13Atom0416 chi ∧
      PredecessorHalfFin13Atom0421 chi ∧
      PredecessorHalfFin13Atom0488 chi ∧
      PredecessorHalfFin13Atom0490 chi ∧
      PredecessorHalfFin13Atom0495 chi ∧
      PredecessorHalfFin13Atom0501 chi ∧
      PredecessorHalfFin13Atom0857 chi ∧
      PredecessorHalfFin13Atom0859 chi ∧
      PredecessorHalfFin13Atom0864 chi ∧
      PredecessorHalfFin13Atom0870 chi ∧
      PredecessorHalfFin13Atom0991 chi) ∨
      (PredecessorHalfFin13Atom0413 chi ∧
      PredecessorHalfFin13Atom0414 chi ∧
      PredecessorHalfFin13Atom0416 chi ∧
      PredecessorHalfFin13Atom0417 chi ∧
      PredecessorHalfFin13Atom0419 chi ∧
      PredecessorHalfFin13Atom0421 chi ∧
      PredecessorHalfFin13Atom0497 chi ∧
      PredecessorHalfFin13Atom0499 chi ∧
      PredecessorHalfFin13Atom0501 chi ∧
      PredecessorHalfFin13Atom0504 chi ∧
      PredecessorHalfFin13Atom0866 chi ∧
      PredecessorHalfFin13Atom0868 chi ∧
      PredecessorHalfFin13Atom0870 chi ∧
      PredecessorHalfFin13Atom0873 chi ∧
      PredecessorHalfFin13Atom0998 chi))) ∨
      (((PredecessorHalfFin13Atom0423 chi ∧
      PredecessorHalfFin13Atom0424 chi ∧
      PredecessorHalfFin13Atom0425 chi ∧
      PredecessorHalfFin13Atom0430 chi ∧
      PredecessorHalfFin13Atom0431 chi ∧
      PredecessorHalfFin13Atom0436 chi ∧
      PredecessorHalfFin13Atom0451 chi ∧
      PredecessorHalfFin13Atom0452 chi ∧
      PredecessorHalfFin13Atom0457 chi ∧
      PredecessorHalfFin13Atom0472 chi ∧
      PredecessorHalfFin13Atom0876 chi ∧
      PredecessorHalfFin13Atom0877 chi ∧
      PredecessorHalfFin13Atom0882 chi ∧
      PredecessorHalfFin13Atom0897 chi ∧
      PredecessorHalfFin13Atom0932 chi) ∨
      (PredecessorHalfFin13Atom0423 chi ∧
      PredecessorHalfFin13Atom0424 chi ∧
      PredecessorHalfFin13Atom0426 chi ∧
      PredecessorHalfFin13Atom0430 chi ∧
      PredecessorHalfFin13Atom0432 chi ∧
      PredecessorHalfFin13Atom0437 chi ∧
      PredecessorHalfFin13Atom0451 chi ∧
      PredecessorHalfFin13Atom0453 chi ∧
      PredecessorHalfFin13Atom0458 chi ∧
      PredecessorHalfFin13Atom0473 chi ∧
      PredecessorHalfFin13Atom0876 chi ∧
      PredecessorHalfFin13Atom0878 chi ∧
      PredecessorHalfFin13Atom0883 chi ∧
      PredecessorHalfFin13Atom0898 chi ∧
      PredecessorHalfFin13Atom0933 chi)) ∨
      ((PredecessorHalfFin13Atom0423 chi ∧
      PredecessorHalfFin13Atom0425 chi ∧
      PredecessorHalfFin13Atom0426 chi ∧
      PredecessorHalfFin13Atom0431 chi ∧
      PredecessorHalfFin13Atom0432 chi ∧
      PredecessorHalfFin13Atom0441 chi ∧
      PredecessorHalfFin13Atom0452 chi ∧
      PredecessorHalfFin13Atom0453 chi ∧
      PredecessorHalfFin13Atom0462 chi ∧
      PredecessorHalfFin13Atom0477 chi ∧
      PredecessorHalfFin13Atom0877 chi ∧
      PredecessorHalfFin13Atom0878 chi ∧
      PredecessorHalfFin13Atom0887 chi ∧
      PredecessorHalfFin13Atom0902 chi ∧
      PredecessorHalfFin13Atom0937 chi) ∨
      (PredecessorHalfFin13Atom0423 chi ∧
      PredecessorHalfFin13Atom0425 chi ∧
      PredecessorHalfFin13Atom0427 chi ∧
      PredecessorHalfFin13Atom0431 chi ∧
      PredecessorHalfFin13Atom0433 chi ∧
      PredecessorHalfFin13Atom0442 chi ∧
      PredecessorHalfFin13Atom0452 chi ∧
      PredecessorHalfFin13Atom0454 chi ∧
      PredecessorHalfFin13Atom0463 chi ∧
      PredecessorHalfFin13Atom0478 chi ∧
      PredecessorHalfFin13Atom0877 chi ∧
      PredecessorHalfFin13Atom0879 chi ∧
      PredecessorHalfFin13Atom0888 chi ∧
      PredecessorHalfFin13Atom0903 chi ∧
      PredecessorHalfFin13Atom0938 chi))))))) ∨
      ((((((PredecessorHalfFin13Atom0423 chi ∧
      PredecessorHalfFin13Atom0425 chi ∧
      PredecessorHalfFin13Atom0429 chi ∧
      PredecessorHalfFin13Atom0431 chi ∧
      PredecessorHalfFin13Atom0435 chi ∧
      PredecessorHalfFin13Atom0444 chi ∧
      PredecessorHalfFin13Atom0452 chi ∧
      PredecessorHalfFin13Atom0456 chi ∧
      PredecessorHalfFin13Atom0465 chi ∧
      PredecessorHalfFin13Atom0480 chi ∧
      PredecessorHalfFin13Atom0877 chi ∧
      PredecessorHalfFin13Atom0881 chi ∧
      PredecessorHalfFin13Atom0890 chi ∧
      PredecessorHalfFin13Atom0905 chi ∧
      PredecessorHalfFin13Atom0940 chi) ∨
      ((PredecessorHalfFin13Atom0423 chi ∧
      PredecessorHalfFin13Atom0426 chi ∧
      PredecessorHalfFin13Atom0427 chi ∧
      PredecessorHalfFin13Atom0432 chi ∧
      PredecessorHalfFin13Atom0433 chi ∧
      PredecessorHalfFin13Atom0445 chi ∧
      PredecessorHalfFin13Atom0453 chi ∧
      PredecessorHalfFin13Atom0454 chi ∧
      PredecessorHalfFin13Atom0466 chi ∧
      PredecessorHalfFin13Atom0481 chi ∧
      PredecessorHalfFin13Atom0878 chi ∧
      PredecessorHalfFin13Atom0879 chi ∧
      PredecessorHalfFin13Atom0891 chi ∧
      PredecessorHalfFin13Atom0906 chi ∧
      PredecessorHalfFin13Atom0941 chi) ∨
      (PredecessorHalfFin13Atom0423 chi ∧
      PredecessorHalfFin13Atom0426 chi ∧
      PredecessorHalfFin13Atom0429 chi ∧
      PredecessorHalfFin13Atom0432 chi ∧
      PredecessorHalfFin13Atom0435 chi ∧
      PredecessorHalfFin13Atom0447 chi ∧
      PredecessorHalfFin13Atom0453 chi ∧
      PredecessorHalfFin13Atom0456 chi ∧
      PredecessorHalfFin13Atom0468 chi ∧
      PredecessorHalfFin13Atom0483 chi ∧
      PredecessorHalfFin13Atom0878 chi ∧
      PredecessorHalfFin13Atom0881 chi ∧
      PredecessorHalfFin13Atom0893 chi ∧
      PredecessorHalfFin13Atom0908 chi ∧
      PredecessorHalfFin13Atom0943 chi))) ∨
      ((PredecessorHalfFin13Atom0423 chi ∧
      PredecessorHalfFin13Atom0427 chi ∧
      PredecessorHalfFin13Atom0429 chi ∧
      PredecessorHalfFin13Atom0433 chi ∧
      PredecessorHalfFin13Atom0435 chi ∧
      PredecessorHalfFin13Atom0449 chi ∧
      PredecessorHalfFin13Atom0454 chi ∧
      PredecessorHalfFin13Atom0456 chi ∧
      PredecessorHalfFin13Atom0470 chi ∧
      PredecessorHalfFin13Atom0485 chi ∧
      PredecessorHalfFin13Atom0879 chi ∧
      PredecessorHalfFin13Atom0881 chi ∧
      PredecessorHalfFin13Atom0895 chi ∧
      PredecessorHalfFin13Atom0910 chi ∧
      PredecessorHalfFin13Atom0945 chi) ∨
      ((PredecessorHalfFin13Atom0424 chi ∧
      PredecessorHalfFin13Atom0425 chi ∧
      PredecessorHalfFin13Atom0426 chi ∧
      PredecessorHalfFin13Atom0436 chi ∧
      PredecessorHalfFin13Atom0437 chi ∧
      PredecessorHalfFin13Atom0441 chi ∧
      PredecessorHalfFin13Atom0457 chi ∧
      PredecessorHalfFin13Atom0458 chi ∧
      PredecessorHalfFin13Atom0462 chi ∧
      PredecessorHalfFin13Atom0487 chi ∧
      PredecessorHalfFin13Atom0882 chi ∧
      PredecessorHalfFin13Atom0883 chi ∧
      PredecessorHalfFin13Atom0887 chi ∧
      PredecessorHalfFin13Atom0912 chi ∧
      PredecessorHalfFin13Atom0947 chi) ∨
      (PredecessorHalfFin13Atom0424 chi ∧
      PredecessorHalfFin13Atom0425 chi ∧
      PredecessorHalfFin13Atom0427 chi ∧
      PredecessorHalfFin13Atom0436 chi ∧
      PredecessorHalfFin13Atom0438 chi ∧
      PredecessorHalfFin13Atom0442 chi ∧
      PredecessorHalfFin13Atom0457 chi ∧
      PredecessorHalfFin13Atom0459 chi ∧
      PredecessorHalfFin13Atom0463 chi ∧
      PredecessorHalfFin13Atom0488 chi ∧
      PredecessorHalfFin13Atom0882 chi ∧
      PredecessorHalfFin13Atom0884 chi ∧
      PredecessorHalfFin13Atom0888 chi ∧
      PredecessorHalfFin13Atom0913 chi ∧
      PredecessorHalfFin13Atom0948 chi)))) ∨
      (((PredecessorHalfFin13Atom0424 chi ∧
      PredecessorHalfFin13Atom0425 chi ∧
      PredecessorHalfFin13Atom0429 chi ∧
      PredecessorHalfFin13Atom0436 chi ∧
      PredecessorHalfFin13Atom0440 chi ∧
      PredecessorHalfFin13Atom0444 chi ∧
      PredecessorHalfFin13Atom0457 chi ∧
      PredecessorHalfFin13Atom0461 chi ∧
      PredecessorHalfFin13Atom0465 chi ∧
      PredecessorHalfFin13Atom0490 chi ∧
      PredecessorHalfFin13Atom0882 chi ∧
      PredecessorHalfFin13Atom0886 chi ∧
      PredecessorHalfFin13Atom0890 chi ∧
      PredecessorHalfFin13Atom0915 chi ∧
      PredecessorHalfFin13Atom0950 chi) ∨
      ((PredecessorHalfFin13Atom0424 chi ∧
      PredecessorHalfFin13Atom0426 chi ∧
      PredecessorHalfFin13Atom0427 chi ∧
      PredecessorHalfFin13Atom0437 chi ∧
      PredecessorHalfFin13Atom0438 chi ∧
      PredecessorHalfFin13Atom0445 chi ∧
      PredecessorHalfFin13Atom0458 chi ∧
      PredecessorHalfFin13Atom0459 chi ∧
      PredecessorHalfFin13Atom0466 chi ∧
      PredecessorHalfFin13Atom0491 chi ∧
      PredecessorHalfFin13Atom0883 chi ∧
      PredecessorHalfFin13Atom0884 chi ∧
      PredecessorHalfFin13Atom0891 chi ∧
      PredecessorHalfFin13Atom0916 chi ∧
      PredecessorHalfFin13Atom0951 chi) ∨
      (PredecessorHalfFin13Atom0424 chi ∧
      PredecessorHalfFin13Atom0426 chi ∧
      PredecessorHalfFin13Atom0429 chi ∧
      PredecessorHalfFin13Atom0437 chi ∧
      PredecessorHalfFin13Atom0440 chi ∧
      PredecessorHalfFin13Atom0447 chi ∧
      PredecessorHalfFin13Atom0458 chi ∧
      PredecessorHalfFin13Atom0461 chi ∧
      PredecessorHalfFin13Atom0468 chi ∧
      PredecessorHalfFin13Atom0493 chi ∧
      PredecessorHalfFin13Atom0883 chi ∧
      PredecessorHalfFin13Atom0886 chi ∧
      PredecessorHalfFin13Atom0893 chi ∧
      PredecessorHalfFin13Atom0918 chi ∧
      PredecessorHalfFin13Atom0953 chi))) ∨
      ((PredecessorHalfFin13Atom0425 chi ∧
      PredecessorHalfFin13Atom0426 chi ∧
      PredecessorHalfFin13Atom0427 chi ∧
      PredecessorHalfFin13Atom0441 chi ∧
      PredecessorHalfFin13Atom0442 chi ∧
      PredecessorHalfFin13Atom0445 chi ∧
      PredecessorHalfFin13Atom0462 chi ∧
      PredecessorHalfFin13Atom0463 chi ∧
      PredecessorHalfFin13Atom0466 chi ∧
      PredecessorHalfFin13Atom0497 chi ∧
      PredecessorHalfFin13Atom0887 chi ∧
      PredecessorHalfFin13Atom0888 chi ∧
      PredecessorHalfFin13Atom0891 chi ∧
      PredecessorHalfFin13Atom0922 chi ∧
      PredecessorHalfFin13Atom0957 chi) ∨
      ((PredecessorHalfFin13Atom0425 chi ∧
      PredecessorHalfFin13Atom0426 chi ∧
      PredecessorHalfFin13Atom0429 chi ∧
      PredecessorHalfFin13Atom0441 chi ∧
      PredecessorHalfFin13Atom0444 chi ∧
      PredecessorHalfFin13Atom0447 chi ∧
      PredecessorHalfFin13Atom0462 chi ∧
      PredecessorHalfFin13Atom0465 chi ∧
      PredecessorHalfFin13Atom0468 chi ∧
      PredecessorHalfFin13Atom0499 chi ∧
      PredecessorHalfFin13Atom0887 chi ∧
      PredecessorHalfFin13Atom0890 chi ∧
      PredecessorHalfFin13Atom0893 chi ∧
      PredecessorHalfFin13Atom0924 chi ∧
      PredecessorHalfFin13Atom0959 chi) ∨
      (PredecessorHalfFin13Atom0425 chi ∧
      PredecessorHalfFin13Atom0427 chi ∧
      PredecessorHalfFin13Atom0429 chi ∧
      PredecessorHalfFin13Atom0442 chi ∧
      PredecessorHalfFin13Atom0444 chi ∧
      PredecessorHalfFin13Atom0449 chi ∧
      PredecessorHalfFin13Atom0463 chi ∧
      PredecessorHalfFin13Atom0465 chi ∧
      PredecessorHalfFin13Atom0470 chi ∧
      PredecessorHalfFin13Atom0501 chi ∧
      PredecessorHalfFin13Atom0888 chi ∧
      PredecessorHalfFin13Atom0890 chi ∧
      PredecessorHalfFin13Atom0895 chi ∧
      PredecessorHalfFin13Atom0926 chi ∧
      PredecessorHalfFin13Atom0961 chi))))) ∨
      ((((PredecessorHalfFin13Atom0426 chi ∧
      PredecessorHalfFin13Atom0427 chi ∧
      PredecessorHalfFin13Atom0429 chi ∧
      PredecessorHalfFin13Atom0445 chi ∧
      PredecessorHalfFin13Atom0447 chi ∧
      PredecessorHalfFin13Atom0449 chi ∧
      PredecessorHalfFin13Atom0466 chi ∧
      PredecessorHalfFin13Atom0468 chi ∧
      PredecessorHalfFin13Atom0470 chi ∧
      PredecessorHalfFin13Atom0504 chi ∧
      PredecessorHalfFin13Atom0891 chi ∧
      PredecessorHalfFin13Atom0893 chi ∧
      PredecessorHalfFin13Atom0895 chi ∧
      PredecessorHalfFin13Atom0929 chi ∧
      PredecessorHalfFin13Atom0964 chi) ∨
      ((PredecessorHalfFin13Atom0430 chi ∧
      PredecessorHalfFin13Atom0431 chi ∧
      PredecessorHalfFin13Atom0432 chi ∧
      PredecessorHalfFin13Atom0436 chi ∧
      PredecessorHalfFin13Atom0437 chi ∧
      PredecessorHalfFin13Atom0441 chi ∧
      PredecessorHalfFin13Atom0472 chi ∧
      PredecessorHalfFin13Atom0473 chi ∧
      PredecessorHalfFin13Atom0477 chi ∧
      PredecessorHalfFin13Atom0487 chi ∧
      PredecessorHalfFin13Atom0897 chi ∧
      PredecessorHalfFin13Atom0898 chi ∧
      PredecessorHalfFin13Atom0902 chi ∧
      PredecessorHalfFin13Atom0912 chi ∧
      PredecessorHalfFin13Atom0967 chi) ∨
      (PredecessorHalfFin13Atom0430 chi ∧
      PredecessorHalfFin13Atom0431 chi ∧
      PredecessorHalfFin13Atom0433 chi ∧
      PredecessorHalfFin13Atom0436 chi ∧
      PredecessorHalfFin13Atom0438 chi ∧
      PredecessorHalfFin13Atom0442 chi ∧
      PredecessorHalfFin13Atom0472 chi ∧
      PredecessorHalfFin13Atom0474 chi ∧
      PredecessorHalfFin13Atom0478 chi ∧
      PredecessorHalfFin13Atom0488 chi ∧
      PredecessorHalfFin13Atom0897 chi ∧
      PredecessorHalfFin13Atom0899 chi ∧
      PredecessorHalfFin13Atom0903 chi ∧
      PredecessorHalfFin13Atom0913 chi ∧
      PredecessorHalfFin13Atom0968 chi))) ∨
      ((PredecessorHalfFin13Atom0430 chi ∧
      PredecessorHalfFin13Atom0431 chi ∧
      PredecessorHalfFin13Atom0435 chi ∧
      PredecessorHalfFin13Atom0436 chi ∧
      PredecessorHalfFin13Atom0440 chi ∧
      PredecessorHalfFin13Atom0444 chi ∧
      PredecessorHalfFin13Atom0472 chi ∧
      PredecessorHalfFin13Atom0476 chi ∧
      PredecessorHalfFin13Atom0480 chi ∧
      PredecessorHalfFin13Atom0490 chi ∧
      PredecessorHalfFin13Atom0897 chi ∧
      PredecessorHalfFin13Atom0901 chi ∧
      PredecessorHalfFin13Atom0905 chi ∧
      PredecessorHalfFin13Atom0915 chi ∧
      PredecessorHalfFin13Atom0970 chi) ∨
      ((PredecessorHalfFin13Atom0430 chi ∧
      PredecessorHalfFin13Atom0432 chi ∧
      PredecessorHalfFin13Atom0433 chi ∧
      PredecessorHalfFin13Atom0437 chi ∧
      PredecessorHalfFin13Atom0438 chi ∧
      PredecessorHalfFin13Atom0445 chi ∧
      PredecessorHalfFin13Atom0473 chi ∧
      PredecessorHalfFin13Atom0474 chi ∧
      PredecessorHalfFin13Atom0481 chi ∧
      PredecessorHalfFin13Atom0491 chi ∧
      PredecessorHalfFin13Atom0898 chi ∧
      PredecessorHalfFin13Atom0899 chi ∧
      PredecessorHalfFin13Atom0906 chi ∧
      PredecessorHalfFin13Atom0916 chi ∧
      PredecessorHalfFin13Atom0971 chi) ∨
      (PredecessorHalfFin13Atom0430 chi ∧
      PredecessorHalfFin13Atom0433 chi ∧
      PredecessorHalfFin13Atom0435 chi ∧
      PredecessorHalfFin13Atom0438 chi ∧
      PredecessorHalfFin13Atom0440 chi ∧
      PredecessorHalfFin13Atom0449 chi ∧
      PredecessorHalfFin13Atom0474 chi ∧
      PredecessorHalfFin13Atom0476 chi ∧
      PredecessorHalfFin13Atom0485 chi ∧
      PredecessorHalfFin13Atom0495 chi ∧
      PredecessorHalfFin13Atom0899 chi ∧
      PredecessorHalfFin13Atom0901 chi ∧
      PredecessorHalfFin13Atom0910 chi ∧
      PredecessorHalfFin13Atom0920 chi ∧
      PredecessorHalfFin13Atom0975 chi)))) ∨
      (((PredecessorHalfFin13Atom0431 chi ∧
      PredecessorHalfFin13Atom0432 chi ∧
      PredecessorHalfFin13Atom0433 chi ∧
      PredecessorHalfFin13Atom0441 chi ∧
      PredecessorHalfFin13Atom0442 chi ∧
      PredecessorHalfFin13Atom0445 chi ∧
      PredecessorHalfFin13Atom0477 chi ∧
      PredecessorHalfFin13Atom0478 chi ∧
      PredecessorHalfFin13Atom0481 chi ∧
      PredecessorHalfFin13Atom0497 chi ∧
      PredecessorHalfFin13Atom0902 chi ∧
      PredecessorHalfFin13Atom0903 chi ∧
      PredecessorHalfFin13Atom0906 chi ∧
      PredecessorHalfFin13Atom0922 chi ∧
      PredecessorHalfFin13Atom0977 chi) ∨
      ((PredecessorHalfFin13Atom0431 chi ∧
      PredecessorHalfFin13Atom0433 chi ∧
      PredecessorHalfFin13Atom0435 chi ∧
      PredecessorHalfFin13Atom0442 chi ∧
      PredecessorHalfFin13Atom0444 chi ∧
      PredecessorHalfFin13Atom0449 chi ∧
      PredecessorHalfFin13Atom0478 chi ∧
      PredecessorHalfFin13Atom0480 chi ∧
      PredecessorHalfFin13Atom0485 chi ∧
      PredecessorHalfFin13Atom0501 chi ∧
      PredecessorHalfFin13Atom0903 chi ∧
      PredecessorHalfFin13Atom0905 chi ∧
      PredecessorHalfFin13Atom0910 chi ∧
      PredecessorHalfFin13Atom0926 chi ∧
      PredecessorHalfFin13Atom0981 chi) ∨
      (PredecessorHalfFin13Atom0432 chi ∧
      PredecessorHalfFin13Atom0433 chi ∧
      PredecessorHalfFin13Atom0435 chi ∧
      PredecessorHalfFin13Atom0445 chi ∧
      PredecessorHalfFin13Atom0447 chi ∧
      PredecessorHalfFin13Atom0449 chi ∧
      PredecessorHalfFin13Atom0481 chi ∧
      PredecessorHalfFin13Atom0483 chi ∧
      PredecessorHalfFin13Atom0485 chi ∧
      PredecessorHalfFin13Atom0504 chi ∧
      PredecessorHalfFin13Atom0906 chi ∧
      PredecessorHalfFin13Atom0908 chi ∧
      PredecessorHalfFin13Atom0910 chi ∧
      PredecessorHalfFin13Atom0929 chi ∧
      PredecessorHalfFin13Atom0984 chi))) ∨
      (((PredecessorHalfFin13Atom0436 chi ∧
      PredecessorHalfFin13Atom0437 chi ∧
      PredecessorHalfFin13Atom0438 chi ∧
      PredecessorHalfFin13Atom0441 chi ∧
      PredecessorHalfFin13Atom0442 chi ∧
      PredecessorHalfFin13Atom0445 chi ∧
      PredecessorHalfFin13Atom0487 chi ∧
      PredecessorHalfFin13Atom0488 chi ∧
      PredecessorHalfFin13Atom0491 chi ∧
      PredecessorHalfFin13Atom0497 chi ∧
      PredecessorHalfFin13Atom0912 chi ∧
      PredecessorHalfFin13Atom0913 chi ∧
      PredecessorHalfFin13Atom0916 chi ∧
      PredecessorHalfFin13Atom0922 chi ∧
      PredecessorHalfFin13Atom0987 chi) ∨
      (PredecessorHalfFin13Atom0436 chi ∧
      PredecessorHalfFin13Atom0437 chi ∧
      PredecessorHalfFin13Atom0440 chi ∧
      PredecessorHalfFin13Atom0441 chi ∧
      PredecessorHalfFin13Atom0444 chi ∧
      PredecessorHalfFin13Atom0447 chi ∧
      PredecessorHalfFin13Atom0487 chi ∧
      PredecessorHalfFin13Atom0490 chi ∧
      PredecessorHalfFin13Atom0493 chi ∧
      PredecessorHalfFin13Atom0499 chi ∧
      PredecessorHalfFin13Atom0912 chi ∧
      PredecessorHalfFin13Atom0915 chi ∧
      PredecessorHalfFin13Atom0918 chi ∧
      PredecessorHalfFin13Atom0924 chi ∧
      PredecessorHalfFin13Atom0989 chi)) ∨
      ((PredecessorHalfFin13Atom0436 chi ∧
      PredecessorHalfFin13Atom0438 chi ∧
      PredecessorHalfFin13Atom0440 chi ∧
      PredecessorHalfFin13Atom0442 chi ∧
      PredecessorHalfFin13Atom0444 chi ∧
      PredecessorHalfFin13Atom0449 chi ∧
      PredecessorHalfFin13Atom0488 chi ∧
      PredecessorHalfFin13Atom0490 chi ∧
      PredecessorHalfFin13Atom0495 chi ∧
      PredecessorHalfFin13Atom0501 chi ∧
      PredecessorHalfFin13Atom0913 chi ∧
      PredecessorHalfFin13Atom0915 chi ∧
      PredecessorHalfFin13Atom0920 chi ∧
      PredecessorHalfFin13Atom0926 chi ∧
      PredecessorHalfFin13Atom0991 chi) ∨
      (PredecessorHalfFin13Atom0437 chi ∧
      PredecessorHalfFin13Atom0438 chi ∧
      PredecessorHalfFin13Atom0440 chi ∧
      PredecessorHalfFin13Atom0445 chi ∧
      PredecessorHalfFin13Atom0447 chi ∧
      PredecessorHalfFin13Atom0449 chi ∧
      PredecessorHalfFin13Atom0491 chi ∧
      PredecessorHalfFin13Atom0493 chi ∧
      PredecessorHalfFin13Atom0495 chi ∧
      PredecessorHalfFin13Atom0504 chi ∧
      PredecessorHalfFin13Atom0916 chi ∧
      PredecessorHalfFin13Atom0918 chi ∧
      PredecessorHalfFin13Atom0920 chi ∧
      PredecessorHalfFin13Atom0929 chi ∧
      PredecessorHalfFin13Atom0994 chi)))))) ∨
      (((((PredecessorHalfFin13Atom0451 chi ∧
      PredecessorHalfFin13Atom0454 chi ∧
      PredecessorHalfFin13Atom0456 chi ∧
      PredecessorHalfFin13Atom0459 chi ∧
      PredecessorHalfFin13Atom0461 chi ∧
      PredecessorHalfFin13Atom0470 chi ∧
      PredecessorHalfFin13Atom0474 chi ∧
      PredecessorHalfFin13Atom0476 chi ∧
      PredecessorHalfFin13Atom0485 chi ∧
      PredecessorHalfFin13Atom0495 chi ∧
      PredecessorHalfFin13Atom0934 chi ∧
      PredecessorHalfFin13Atom0936 chi ∧
      PredecessorHalfFin13Atom0945 chi ∧
      PredecessorHalfFin13Atom0955 chi ∧
      PredecessorHalfFin13Atom0975 chi) ∨
      ((PredecessorHalfFin13Atom0452 chi ∧
      PredecessorHalfFin13Atom0453 chi ∧
      PredecessorHalfFin13Atom0454 chi ∧
      PredecessorHalfFin13Atom0462 chi ∧
      PredecessorHalfFin13Atom0463 chi ∧
      PredecessorHalfFin13Atom0466 chi ∧
      PredecessorHalfFin13Atom0477 chi ∧
      PredecessorHalfFin13Atom0478 chi ∧
      PredecessorHalfFin13Atom0481 chi ∧
      PredecessorHalfFin13Atom0497 chi ∧
      PredecessorHalfFin13Atom0937 chi ∧
      PredecessorHalfFin13Atom0938 chi ∧
      PredecessorHalfFin13Atom0941 chi ∧
      PredecessorHalfFin13Atom0957 chi ∧
      PredecessorHalfFin13Atom0977 chi) ∨
      (PredecessorHalfFin13Atom0452 chi ∧
      PredecessorHalfFin13Atom0453 chi ∧
      PredecessorHalfFin13Atom0456 chi ∧
      PredecessorHalfFin13Atom0462 chi ∧
      PredecessorHalfFin13Atom0465 chi ∧
      PredecessorHalfFin13Atom0468 chi ∧
      PredecessorHalfFin13Atom0477 chi ∧
      PredecessorHalfFin13Atom0480 chi ∧
      PredecessorHalfFin13Atom0483 chi ∧
      PredecessorHalfFin13Atom0499 chi ∧
      PredecessorHalfFin13Atom0937 chi ∧
      PredecessorHalfFin13Atom0940 chi ∧
      PredecessorHalfFin13Atom0943 chi ∧
      PredecessorHalfFin13Atom0959 chi ∧
      PredecessorHalfFin13Atom0979 chi))) ∨
      ((PredecessorHalfFin13Atom0452 chi ∧
      PredecessorHalfFin13Atom0454 chi ∧
      PredecessorHalfFin13Atom0456 chi ∧
      PredecessorHalfFin13Atom0463 chi ∧
      PredecessorHalfFin13Atom0465 chi ∧
      PredecessorHalfFin13Atom0470 chi ∧
      PredecessorHalfFin13Atom0478 chi ∧
      PredecessorHalfFin13Atom0480 chi ∧
      PredecessorHalfFin13Atom0485 chi ∧
      PredecessorHalfFin13Atom0501 chi ∧
      PredecessorHalfFin13Atom0938 chi ∧
      PredecessorHalfFin13Atom0940 chi ∧
      PredecessorHalfFin13Atom0945 chi ∧
      PredecessorHalfFin13Atom0961 chi ∧
      PredecessorHalfFin13Atom0981 chi) ∨
      ((PredecessorHalfFin13Atom0453 chi ∧
      PredecessorHalfFin13Atom0454 chi ∧
      PredecessorHalfFin13Atom0456 chi ∧
      PredecessorHalfFin13Atom0466 chi ∧
      PredecessorHalfFin13Atom0468 chi ∧
      PredecessorHalfFin13Atom0470 chi ∧
      PredecessorHalfFin13Atom0481 chi ∧
      PredecessorHalfFin13Atom0483 chi ∧
      PredecessorHalfFin13Atom0485 chi ∧
      PredecessorHalfFin13Atom0504 chi ∧
      PredecessorHalfFin13Atom0941 chi ∧
      PredecessorHalfFin13Atom0943 chi ∧
      PredecessorHalfFin13Atom0945 chi ∧
      PredecessorHalfFin13Atom0964 chi ∧
      PredecessorHalfFin13Atom0984 chi) ∨
      (PredecessorHalfFin13Atom0457 chi ∧
      PredecessorHalfFin13Atom0458 chi ∧
      PredecessorHalfFin13Atom0459 chi ∧
      PredecessorHalfFin13Atom0462 chi ∧
      PredecessorHalfFin13Atom0463 chi ∧
      PredecessorHalfFin13Atom0466 chi ∧
      PredecessorHalfFin13Atom0487 chi ∧
      PredecessorHalfFin13Atom0488 chi ∧
      PredecessorHalfFin13Atom0491 chi ∧
      PredecessorHalfFin13Atom0497 chi ∧
      PredecessorHalfFin13Atom0947 chi ∧
      PredecessorHalfFin13Atom0948 chi ∧
      PredecessorHalfFin13Atom0951 chi ∧
      PredecessorHalfFin13Atom0957 chi ∧
      PredecessorHalfFin13Atom0987 chi)))) ∨
      (((PredecessorHalfFin13Atom0457 chi ∧
      PredecessorHalfFin13Atom0458 chi ∧
      PredecessorHalfFin13Atom0461 chi ∧
      PredecessorHalfFin13Atom0462 chi ∧
      PredecessorHalfFin13Atom0465 chi ∧
      PredecessorHalfFin13Atom0468 chi ∧
      PredecessorHalfFin13Atom0487 chi ∧
      PredecessorHalfFin13Atom0490 chi ∧
      PredecessorHalfFin13Atom0493 chi ∧
      PredecessorHalfFin13Atom0499 chi ∧
      PredecessorHalfFin13Atom0947 chi ∧
      PredecessorHalfFin13Atom0950 chi ∧
      PredecessorHalfFin13Atom0953 chi ∧
      PredecessorHalfFin13Atom0959 chi ∧
      PredecessorHalfFin13Atom0989 chi) ∨
      ((PredecessorHalfFin13Atom0457 chi ∧
      PredecessorHalfFin13Atom0459 chi ∧
      PredecessorHalfFin13Atom0461 chi ∧
      PredecessorHalfFin13Atom0463 chi ∧
      PredecessorHalfFin13Atom0465 chi ∧
      PredecessorHalfFin13Atom0470 chi ∧
      PredecessorHalfFin13Atom0488 chi ∧
      PredecessorHalfFin13Atom0490 chi ∧
      PredecessorHalfFin13Atom0495 chi ∧
      PredecessorHalfFin13Atom0501 chi ∧
      PredecessorHalfFin13Atom0948 chi ∧
      PredecessorHalfFin13Atom0950 chi ∧
      PredecessorHalfFin13Atom0955 chi ∧
      PredecessorHalfFin13Atom0961 chi ∧
      PredecessorHalfFin13Atom0991 chi) ∨
      (PredecessorHalfFin13Atom0458 chi ∧
      PredecessorHalfFin13Atom0459 chi ∧
      PredecessorHalfFin13Atom0461 chi ∧
      PredecessorHalfFin13Atom0466 chi ∧
      PredecessorHalfFin13Atom0468 chi ∧
      PredecessorHalfFin13Atom0470 chi ∧
      PredecessorHalfFin13Atom0491 chi ∧
      PredecessorHalfFin13Atom0493 chi ∧
      PredecessorHalfFin13Atom0495 chi ∧
      PredecessorHalfFin13Atom0504 chi ∧
      PredecessorHalfFin13Atom0951 chi ∧
      PredecessorHalfFin13Atom0953 chi ∧
      PredecessorHalfFin13Atom0955 chi ∧
      PredecessorHalfFin13Atom0964 chi ∧
      PredecessorHalfFin13Atom0994 chi))) ∨
      ((PredecessorHalfFin13Atom0472 chi ∧
      PredecessorHalfFin13Atom0473 chi ∧
      PredecessorHalfFin13Atom0474 chi ∧
      PredecessorHalfFin13Atom0477 chi ∧
      PredecessorHalfFin13Atom0478 chi ∧
      PredecessorHalfFin13Atom0481 chi ∧
      PredecessorHalfFin13Atom0487 chi ∧
      PredecessorHalfFin13Atom0488 chi ∧
      PredecessorHalfFin13Atom0491 chi ∧
      PredecessorHalfFin13Atom0497 chi ∧
      PredecessorHalfFin13Atom0967 chi ∧
      PredecessorHalfFin13Atom0968 chi ∧
      PredecessorHalfFin13Atom0971 chi ∧
      PredecessorHalfFin13Atom0977 chi ∧
      PredecessorHalfFin13Atom0987 chi) ∨
      ((PredecessorHalfFin13Atom0472 chi ∧
      PredecessorHalfFin13Atom0473 chi ∧
      PredecessorHalfFin13Atom0476 chi ∧
      PredecessorHalfFin13Atom0477 chi ∧
      PredecessorHalfFin13Atom0480 chi ∧
      PredecessorHalfFin13Atom0483 chi ∧
      PredecessorHalfFin13Atom0487 chi ∧
      PredecessorHalfFin13Atom0490 chi ∧
      PredecessorHalfFin13Atom0493 chi ∧
      PredecessorHalfFin13Atom0499 chi ∧
      PredecessorHalfFin13Atom0967 chi ∧
      PredecessorHalfFin13Atom0970 chi ∧
      PredecessorHalfFin13Atom0973 chi ∧
      PredecessorHalfFin13Atom0979 chi ∧
      PredecessorHalfFin13Atom0989 chi) ∨
      (PredecessorHalfFin13Atom0472 chi ∧
      PredecessorHalfFin13Atom0474 chi ∧
      PredecessorHalfFin13Atom0476 chi ∧
      PredecessorHalfFin13Atom0478 chi ∧
      PredecessorHalfFin13Atom0480 chi ∧
      PredecessorHalfFin13Atom0485 chi ∧
      PredecessorHalfFin13Atom0488 chi ∧
      PredecessorHalfFin13Atom0490 chi ∧
      PredecessorHalfFin13Atom0495 chi ∧
      PredecessorHalfFin13Atom0501 chi ∧
      PredecessorHalfFin13Atom0968 chi ∧
      PredecessorHalfFin13Atom0970 chi ∧
      PredecessorHalfFin13Atom0975 chi ∧
      PredecessorHalfFin13Atom0981 chi ∧
      PredecessorHalfFin13Atom0991 chi))))) ∨
      ((((PredecessorHalfFin13Atom0473 chi ∧
      PredecessorHalfFin13Atom0474 chi ∧
      PredecessorHalfFin13Atom0476 chi ∧
      PredecessorHalfFin13Atom0481 chi ∧
      PredecessorHalfFin13Atom0483 chi ∧
      PredecessorHalfFin13Atom0485 chi ∧
      PredecessorHalfFin13Atom0491 chi ∧
      PredecessorHalfFin13Atom0493 chi ∧
      PredecessorHalfFin13Atom0495 chi ∧
      PredecessorHalfFin13Atom0504 chi ∧
      PredecessorHalfFin13Atom0971 chi ∧
      PredecessorHalfFin13Atom0973 chi ∧
      PredecessorHalfFin13Atom0975 chi ∧
      PredecessorHalfFin13Atom0984 chi ∧
      PredecessorHalfFin13Atom0994 chi) ∨
      ((PredecessorHalfFin13Atom0672 chi ∧
      PredecessorHalfFin13Atom0673 chi ∧
      PredecessorHalfFin13Atom0674 chi ∧
      PredecessorHalfFin13Atom0680 chi ∧
      PredecessorHalfFin13Atom0681 chi ∧
      PredecessorHalfFin13Atom0687 chi ∧
      PredecessorHalfFin13Atom0708 chi ∧
      PredecessorHalfFin13Atom0709 chi ∧
      PredecessorHalfFin13Atom0715 chi ∧
      PredecessorHalfFin13Atom0736 chi ∧
      PredecessorHalfFin13Atom0792 chi ∧
      PredecessorHalfFin13Atom0793 chi ∧
      PredecessorHalfFin13Atom0799 chi ∧
      PredecessorHalfFin13Atom0820 chi ∧
      PredecessorHalfFin13Atom0876 chi) ∨
      (PredecessorHalfFin13Atom0672 chi ∧
      PredecessorHalfFin13Atom0673 chi ∧
      PredecessorHalfFin13Atom0675 chi ∧
      PredecessorHalfFin13Atom0680 chi ∧
      PredecessorHalfFin13Atom0682 chi ∧
      PredecessorHalfFin13Atom0688 chi ∧
      PredecessorHalfFin13Atom0708 chi ∧
      PredecessorHalfFin13Atom0710 chi ∧
      PredecessorHalfFin13Atom0716 chi ∧
      PredecessorHalfFin13Atom0737 chi ∧
      PredecessorHalfFin13Atom0792 chi ∧
      PredecessorHalfFin13Atom0794 chi ∧
      PredecessorHalfFin13Atom0800 chi ∧
      PredecessorHalfFin13Atom0821 chi ∧
      PredecessorHalfFin13Atom0877 chi))) ∨
      ((PredecessorHalfFin13Atom0672 chi ∧
      PredecessorHalfFin13Atom0673 chi ∧
      PredecessorHalfFin13Atom0676 chi ∧
      PredecessorHalfFin13Atom0680 chi ∧
      PredecessorHalfFin13Atom0683 chi ∧
      PredecessorHalfFin13Atom0689 chi ∧
      PredecessorHalfFin13Atom0708 chi ∧
      PredecessorHalfFin13Atom0711 chi ∧
      PredecessorHalfFin13Atom0717 chi ∧
      PredecessorHalfFin13Atom0738 chi ∧
      PredecessorHalfFin13Atom0792 chi ∧
      PredecessorHalfFin13Atom0795 chi ∧
      PredecessorHalfFin13Atom0801 chi ∧
      PredecessorHalfFin13Atom0822 chi ∧
      PredecessorHalfFin13Atom0878 chi) ∨
      ((PredecessorHalfFin13Atom0672 chi ∧
      PredecessorHalfFin13Atom0673 chi ∧
      PredecessorHalfFin13Atom0677 chi ∧
      PredecessorHalfFin13Atom0680 chi ∧
      PredecessorHalfFin13Atom0684 chi ∧
      PredecessorHalfFin13Atom0690 chi ∧
      PredecessorHalfFin13Atom0708 chi ∧
      PredecessorHalfFin13Atom0712 chi ∧
      PredecessorHalfFin13Atom0718 chi ∧
      PredecessorHalfFin13Atom0739 chi ∧
      PredecessorHalfFin13Atom0792 chi ∧
      PredecessorHalfFin13Atom0796 chi ∧
      PredecessorHalfFin13Atom0802 chi ∧
      PredecessorHalfFin13Atom0823 chi ∧
      PredecessorHalfFin13Atom0879 chi) ∨
      (PredecessorHalfFin13Atom0672 chi ∧
      PredecessorHalfFin13Atom0673 chi ∧
      PredecessorHalfFin13Atom0678 chi ∧
      PredecessorHalfFin13Atom0680 chi ∧
      PredecessorHalfFin13Atom0685 chi ∧
      PredecessorHalfFin13Atom0691 chi ∧
      PredecessorHalfFin13Atom0708 chi ∧
      PredecessorHalfFin13Atom0713 chi ∧
      PredecessorHalfFin13Atom0719 chi ∧
      PredecessorHalfFin13Atom0740 chi ∧
      PredecessorHalfFin13Atom0792 chi ∧
      PredecessorHalfFin13Atom0797 chi ∧
      PredecessorHalfFin13Atom0803 chi ∧
      PredecessorHalfFin13Atom0824 chi ∧
      PredecessorHalfFin13Atom0880 chi)))) ∨
      (((PredecessorHalfFin13Atom0672 chi ∧
      PredecessorHalfFin13Atom0673 chi ∧
      PredecessorHalfFin13Atom0679 chi ∧
      PredecessorHalfFin13Atom0680 chi ∧
      PredecessorHalfFin13Atom0686 chi ∧
      PredecessorHalfFin13Atom0692 chi ∧
      PredecessorHalfFin13Atom0708 chi ∧
      PredecessorHalfFin13Atom0714 chi ∧
      PredecessorHalfFin13Atom0720 chi ∧
      PredecessorHalfFin13Atom0741 chi ∧
      PredecessorHalfFin13Atom0792 chi ∧
      PredecessorHalfFin13Atom0798 chi ∧
      PredecessorHalfFin13Atom0804 chi ∧
      PredecessorHalfFin13Atom0825 chi ∧
      PredecessorHalfFin13Atom0881 chi) ∨
      ((PredecessorHalfFin13Atom0672 chi ∧
      PredecessorHalfFin13Atom0674 chi ∧
      PredecessorHalfFin13Atom0675 chi ∧
      PredecessorHalfFin13Atom0681 chi ∧
      PredecessorHalfFin13Atom0682 chi ∧
      PredecessorHalfFin13Atom0693 chi ∧
      PredecessorHalfFin13Atom0709 chi ∧
      PredecessorHalfFin13Atom0710 chi ∧
      PredecessorHalfFin13Atom0721 chi ∧
      PredecessorHalfFin13Atom0742 chi ∧
      PredecessorHalfFin13Atom0793 chi ∧
      PredecessorHalfFin13Atom0794 chi ∧
      PredecessorHalfFin13Atom0805 chi ∧
      PredecessorHalfFin13Atom0826 chi ∧
      PredecessorHalfFin13Atom0882 chi) ∨
      (PredecessorHalfFin13Atom0672 chi ∧
      PredecessorHalfFin13Atom0674 chi ∧
      PredecessorHalfFin13Atom0676 chi ∧
      PredecessorHalfFin13Atom0681 chi ∧
      PredecessorHalfFin13Atom0683 chi ∧
      PredecessorHalfFin13Atom0694 chi ∧
      PredecessorHalfFin13Atom0709 chi ∧
      PredecessorHalfFin13Atom0711 chi ∧
      PredecessorHalfFin13Atom0722 chi ∧
      PredecessorHalfFin13Atom0743 chi ∧
      PredecessorHalfFin13Atom0793 chi ∧
      PredecessorHalfFin13Atom0795 chi ∧
      PredecessorHalfFin13Atom0806 chi ∧
      PredecessorHalfFin13Atom0827 chi ∧
      PredecessorHalfFin13Atom0883 chi))) ∨
      (((PredecessorHalfFin13Atom0672 chi ∧
      PredecessorHalfFin13Atom0674 chi ∧
      PredecessorHalfFin13Atom0677 chi ∧
      PredecessorHalfFin13Atom0681 chi ∧
      PredecessorHalfFin13Atom0684 chi ∧
      PredecessorHalfFin13Atom0695 chi ∧
      PredecessorHalfFin13Atom0709 chi ∧
      PredecessorHalfFin13Atom0712 chi ∧
      PredecessorHalfFin13Atom0723 chi ∧
      PredecessorHalfFin13Atom0744 chi ∧
      PredecessorHalfFin13Atom0793 chi ∧
      PredecessorHalfFin13Atom0796 chi ∧
      PredecessorHalfFin13Atom0807 chi ∧
      PredecessorHalfFin13Atom0828 chi ∧
      PredecessorHalfFin13Atom0884 chi) ∨
      (PredecessorHalfFin13Atom0672 chi ∧
      PredecessorHalfFin13Atom0674 chi ∧
      PredecessorHalfFin13Atom0678 chi ∧
      PredecessorHalfFin13Atom0681 chi ∧
      PredecessorHalfFin13Atom0685 chi ∧
      PredecessorHalfFin13Atom0696 chi ∧
      PredecessorHalfFin13Atom0709 chi ∧
      PredecessorHalfFin13Atom0713 chi ∧
      PredecessorHalfFin13Atom0724 chi ∧
      PredecessorHalfFin13Atom0745 chi ∧
      PredecessorHalfFin13Atom0793 chi ∧
      PredecessorHalfFin13Atom0797 chi ∧
      PredecessorHalfFin13Atom0808 chi ∧
      PredecessorHalfFin13Atom0829 chi ∧
      PredecessorHalfFin13Atom0885 chi)) ∨
      ((PredecessorHalfFin13Atom0672 chi ∧
      PredecessorHalfFin13Atom0674 chi ∧
      PredecessorHalfFin13Atom0679 chi ∧
      PredecessorHalfFin13Atom0681 chi ∧
      PredecessorHalfFin13Atom0686 chi ∧
      PredecessorHalfFin13Atom0697 chi ∧
      PredecessorHalfFin13Atom0709 chi ∧
      PredecessorHalfFin13Atom0714 chi ∧
      PredecessorHalfFin13Atom0725 chi ∧
      PredecessorHalfFin13Atom0746 chi ∧
      PredecessorHalfFin13Atom0793 chi ∧
      PredecessorHalfFin13Atom0798 chi ∧
      PredecessorHalfFin13Atom0809 chi ∧
      PredecessorHalfFin13Atom0830 chi ∧
      PredecessorHalfFin13Atom0886 chi) ∨
      (PredecessorHalfFin13Atom0672 chi ∧
      PredecessorHalfFin13Atom0675 chi ∧
      PredecessorHalfFin13Atom0676 chi ∧
      PredecessorHalfFin13Atom0682 chi ∧
      PredecessorHalfFin13Atom0683 chi ∧
      PredecessorHalfFin13Atom0698 chi ∧
      PredecessorHalfFin13Atom0710 chi ∧
      PredecessorHalfFin13Atom0711 chi ∧
      PredecessorHalfFin13Atom0726 chi ∧
      PredecessorHalfFin13Atom0747 chi ∧
      PredecessorHalfFin13Atom0794 chi ∧
      PredecessorHalfFin13Atom0795 chi ∧
      PredecessorHalfFin13Atom0810 chi ∧
      PredecessorHalfFin13Atom0831 chi ∧
      PredecessorHalfFin13Atom0887 chi))))))))) := by
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
              exact predecessorHalfFin13_clause25452 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause25453 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause25455 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause25457 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause25459 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause25460 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause25462 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause25463 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause25465 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause25467 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause25469 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause25471 chi hnoStrong hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause25473 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause25476 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause25479 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause25480 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause25481 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause25483 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause25484 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause25485 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause25487 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause25488 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause25490 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause25492 chi hnoStrong hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause25494 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause25495 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause25497 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause25498 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause25500 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause25502 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause25504 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause25506 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause25508 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause25511 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause25515 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause25518 chi hnoStrong hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause25520 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause25522 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause25524 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause25528 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause25531 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause25534 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause25536 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause25538 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause25545 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause25549 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause25550 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause25554 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause25555 chi hnoStrong hbad
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
              exact predecessorHalfFin13_clause25557 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause25558 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause25560 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause25562 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause25564 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause25565 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause25567 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause25568 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause25570 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause25574 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause25576 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause25578 chi hnoStrong hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause25581 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause25584 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause25585 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause25587 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause25588 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause25592 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause25594 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause25598 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause25601 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause25604 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause25606 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause25608 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause25611 chi hnoStrong hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause25627 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause25629 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause25631 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause25633 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause25636 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause25639 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause25641 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause25643 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause25646 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause25654 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause25656 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause25658 chi hnoStrong hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause25661 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause26137 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause26138 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause26139 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause26140 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause26141 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause26142 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause26143 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause26144 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause26145 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause26146 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause26147 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause26148 chi hnoStrong hbad

end ErdosSzekeres

end
