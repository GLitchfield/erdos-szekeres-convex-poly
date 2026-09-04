module

public import ErdosSzekeres.Fin15AnchoredClauseChunk120
public import ErdosSzekeres.Fin15AnchoredClauseChunk121
public import ErdosSzekeres.Fin15AnchoredClauseChunk122

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 061. -/

theorem fin15Anchored_rejectSemanticSegment061
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom0470 chi) ∨
      ((Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom0536 chi) ∨
      (Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom0822 chi))) ∨
      (((¬Fin15AnchoredAtom1823 chi ∧
      Fin15AnchoredAtom0456 chi ∧
      Fin15AnchoredAtom0459 chi ∧
      Fin15AnchoredAtom0470 chi ∧
      Fin15AnchoredAtom0536 chi ∧
      Fin15AnchoredAtom0822 chi) ∨
      (Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom0456 chi)) ∨
      ((Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom0460 chi) ∨
      (Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom0471 chi)))) ∨
      ((((Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom0537 chi) ∨
      (Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom0823 chi)) ∨
      ((¬Fin15AnchoredAtom1824 chi ∧
      Fin15AnchoredAtom0456 chi ∧
      Fin15AnchoredAtom0460 chi ∧
      Fin15AnchoredAtom0471 chi ∧
      Fin15AnchoredAtom0537 chi ∧
      Fin15AnchoredAtom0823 chi) ∨
      (Fin15AnchoredAtom1825 chi ∧
      ¬Fin15AnchoredAtom0456 chi))) ∨
      (((Fin15AnchoredAtom1825 chi ∧
      ¬Fin15AnchoredAtom0461 chi) ∨
      (Fin15AnchoredAtom1825 chi ∧
      ¬Fin15AnchoredAtom0472 chi)) ∨
      ((Fin15AnchoredAtom1825 chi ∧
      ¬Fin15AnchoredAtom0538 chi) ∨
      (Fin15AnchoredAtom1825 chi ∧
      ¬Fin15AnchoredAtom0824 chi))))) ∨
      (((((¬Fin15AnchoredAtom1825 chi ∧
      Fin15AnchoredAtom0456 chi ∧
      Fin15AnchoredAtom0461 chi ∧
      Fin15AnchoredAtom0472 chi ∧
      Fin15AnchoredAtom0538 chi ∧
      Fin15AnchoredAtom0824 chi) ∨
      (Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom0456 chi)) ∨
      ((Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom0462 chi) ∨
      (Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom0473 chi))) ∨
      (((Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom0539 chi) ∨
      (Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom0825 chi)) ∨
      ((¬Fin15AnchoredAtom1826 chi ∧
      Fin15AnchoredAtom0456 chi ∧
      Fin15AnchoredAtom0462 chi ∧
      Fin15AnchoredAtom0473 chi ∧
      Fin15AnchoredAtom0539 chi ∧
      Fin15AnchoredAtom0825 chi) ∨
      (Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom0456 chi)))) ∨
      ((((Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom0463 chi) ∨
      (Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom0474 chi)) ∨
      ((Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom0540 chi) ∨
      (Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom0826 chi))) ∨
      (((¬Fin15AnchoredAtom1827 chi ∧
      Fin15AnchoredAtom0456 chi ∧
      Fin15AnchoredAtom0463 chi ∧
      Fin15AnchoredAtom0474 chi ∧
      Fin15AnchoredAtom0540 chi ∧
      Fin15AnchoredAtom0826 chi) ∨
      (Fin15AnchoredAtom1828 chi ∧
      ¬Fin15AnchoredAtom0456 chi)) ∨
      ((Fin15AnchoredAtom1828 chi ∧
      ¬Fin15AnchoredAtom0464 chi) ∨
      (Fin15AnchoredAtom1828 chi ∧
      ¬Fin15AnchoredAtom0475 chi)))))) ∨
      ((((((Fin15AnchoredAtom1828 chi ∧
      ¬Fin15AnchoredAtom0541 chi) ∨
      (Fin15AnchoredAtom1828 chi ∧
      ¬Fin15AnchoredAtom0827 chi)) ∨
      ((¬Fin15AnchoredAtom1828 chi ∧
      Fin15AnchoredAtom0456 chi ∧
      Fin15AnchoredAtom0464 chi ∧
      Fin15AnchoredAtom0475 chi ∧
      Fin15AnchoredAtom0541 chi ∧
      Fin15AnchoredAtom0827 chi) ∨
      (Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom0456 chi))) ∨
      (((Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom0465 chi) ∨
      (Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom0476 chi)) ∨
      ((Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom0542 chi) ∨
      (Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom0828 chi)))) ∨
      ((((¬Fin15AnchoredAtom1829 chi ∧
      Fin15AnchoredAtom0456 chi ∧
      Fin15AnchoredAtom0465 chi ∧
      Fin15AnchoredAtom0476 chi ∧
      Fin15AnchoredAtom0542 chi ∧
      Fin15AnchoredAtom0828 chi) ∨
      (Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom0456 chi)) ∨
      ((Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom0466 chi) ∨
      (Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom0477 chi))) ∨
      (((Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom0543 chi) ∨
      (Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom0829 chi)) ∨
      ((¬Fin15AnchoredAtom1830 chi ∧
      Fin15AnchoredAtom0456 chi ∧
      Fin15AnchoredAtom0466 chi ∧
      Fin15AnchoredAtom0477 chi ∧
      Fin15AnchoredAtom0543 chi ∧
      Fin15AnchoredAtom0829 chi) ∨
      (Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom0456 chi))))) ∨
      (((((Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom0467 chi) ∨
      (Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom0478 chi)) ∨
      ((Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom0544 chi) ∨
      (Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom0830 chi))) ∨
      (((¬Fin15AnchoredAtom1831 chi ∧
      Fin15AnchoredAtom0456 chi ∧
      Fin15AnchoredAtom0467 chi ∧
      Fin15AnchoredAtom0478 chi ∧
      Fin15AnchoredAtom0544 chi ∧
      Fin15AnchoredAtom0830 chi) ∨
      (Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom0457 chi)) ∨
      ((Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom0458 chi) ∨
      (Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom0479 chi)))) ∨
      ((((Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom0545 chi) ∨
      (Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom0831 chi)) ∨
      ((¬Fin15AnchoredAtom1832 chi ∧
      Fin15AnchoredAtom0457 chi ∧
      Fin15AnchoredAtom0458 chi ∧
      Fin15AnchoredAtom0479 chi ∧
      Fin15AnchoredAtom0545 chi ∧
      Fin15AnchoredAtom0831 chi) ∨
      (Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom0457 chi))) ∨
      (((Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom0459 chi) ∨
      (Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom0480 chi)) ∨
      ((Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom0546 chi) ∨
      (Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom0832 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom1833 chi ∧
      Fin15AnchoredAtom0457 chi ∧
      Fin15AnchoredAtom0459 chi ∧
      Fin15AnchoredAtom0480 chi ∧
      Fin15AnchoredAtom0546 chi ∧
      Fin15AnchoredAtom0832 chi) ∨
      ((Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom0457 chi) ∨
      (Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom0460 chi))) ∨
      (((Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom0481 chi) ∨
      (Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom0547 chi)) ∨
      ((Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom0833 chi) ∨
      (¬Fin15AnchoredAtom1834 chi ∧
      Fin15AnchoredAtom0457 chi ∧
      Fin15AnchoredAtom0460 chi ∧
      Fin15AnchoredAtom0481 chi ∧
      Fin15AnchoredAtom0547 chi ∧
      Fin15AnchoredAtom0833 chi)))) ∨
      ((((Fin15AnchoredAtom1835 chi ∧
      ¬Fin15AnchoredAtom0457 chi) ∨
      (Fin15AnchoredAtom1835 chi ∧
      ¬Fin15AnchoredAtom0461 chi)) ∨
      ((Fin15AnchoredAtom1835 chi ∧
      ¬Fin15AnchoredAtom0482 chi) ∨
      (Fin15AnchoredAtom1835 chi ∧
      ¬Fin15AnchoredAtom0548 chi))) ∨
      (((Fin15AnchoredAtom1835 chi ∧
      ¬Fin15AnchoredAtom0834 chi) ∨
      (¬Fin15AnchoredAtom1835 chi ∧
      Fin15AnchoredAtom0457 chi ∧
      Fin15AnchoredAtom0461 chi ∧
      Fin15AnchoredAtom0482 chi ∧
      Fin15AnchoredAtom0548 chi ∧
      Fin15AnchoredAtom0834 chi)) ∨
      ((Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom0457 chi) ∨
      (Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom0462 chi))))) ∨
      (((((Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom0483 chi) ∨
      (Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom0549 chi)) ∨
      ((Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom0835 chi) ∨
      (¬Fin15AnchoredAtom1836 chi ∧
      Fin15AnchoredAtom0457 chi ∧
      Fin15AnchoredAtom0462 chi ∧
      Fin15AnchoredAtom0483 chi ∧
      Fin15AnchoredAtom0549 chi ∧
      Fin15AnchoredAtom0835 chi))) ∨
      (((Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom0457 chi) ∨
      (Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom0463 chi)) ∨
      ((Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom0484 chi) ∨
      (Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom0550 chi)))) ∨
      ((((Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom0836 chi) ∨
      (¬Fin15AnchoredAtom1837 chi ∧
      Fin15AnchoredAtom0457 chi ∧
      Fin15AnchoredAtom0463 chi ∧
      Fin15AnchoredAtom0484 chi ∧
      Fin15AnchoredAtom0550 chi ∧
      Fin15AnchoredAtom0836 chi)) ∨
      ((Fin15AnchoredAtom1838 chi ∧
      ¬Fin15AnchoredAtom0457 chi) ∨
      (Fin15AnchoredAtom1838 chi ∧
      ¬Fin15AnchoredAtom0551 chi))) ∨
      (((Fin15AnchoredAtom1838 chi ∧
      ¬Fin15AnchoredAtom0837 chi) ∨
      (¬Fin15AnchoredAtom1838 chi ∧
      Fin15AnchoredAtom0457 chi ∧
      Fin15AnchoredAtom0464 chi ∧
      Fin15AnchoredAtom0485 chi ∧
      Fin15AnchoredAtom0551 chi ∧
      Fin15AnchoredAtom0837 chi)) ∨
      ((Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom0457 chi) ∨
      (Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom0465 chi)))))) ∨
      ((((((Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom0486 chi) ∨
      (Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom0552 chi)) ∨
      ((Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom0838 chi) ∨
      (¬Fin15AnchoredAtom1839 chi ∧
      Fin15AnchoredAtom0457 chi ∧
      Fin15AnchoredAtom0465 chi ∧
      Fin15AnchoredAtom0486 chi ∧
      Fin15AnchoredAtom0552 chi ∧
      Fin15AnchoredAtom0838 chi))) ∨
      (((Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom0457 chi) ∨
      (Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom0466 chi)) ∨
      ((Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom0487 chi) ∨
      (Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom0553 chi)))) ∨
      ((((Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom0839 chi) ∨
      (¬Fin15AnchoredAtom1840 chi ∧
      Fin15AnchoredAtom0457 chi ∧
      Fin15AnchoredAtom0466 chi ∧
      Fin15AnchoredAtom0487 chi ∧
      Fin15AnchoredAtom0553 chi ∧
      Fin15AnchoredAtom0839 chi)) ∨
      ((Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom0457 chi) ∨
      (Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom0467 chi))) ∨
      (((Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom0488 chi) ∨
      (Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom0554 chi)) ∨
      ((Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom0840 chi) ∨
      (¬Fin15AnchoredAtom1841 chi ∧
      Fin15AnchoredAtom0457 chi ∧
      Fin15AnchoredAtom0467 chi ∧
      Fin15AnchoredAtom0488 chi ∧
      Fin15AnchoredAtom0554 chi ∧
      Fin15AnchoredAtom0840 chi))))) ∨
      (((((Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom0458 chi) ∨
      (Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom0459 chi)) ∨
      ((Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom0489 chi) ∨
      (Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom0555 chi))) ∨
      (((Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom0841 chi) ∨
      (¬Fin15AnchoredAtom1842 chi ∧
      Fin15AnchoredAtom0458 chi ∧
      Fin15AnchoredAtom0459 chi ∧
      Fin15AnchoredAtom0489 chi ∧
      Fin15AnchoredAtom0555 chi ∧
      Fin15AnchoredAtom0841 chi)) ∨
      ((Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom0458 chi) ∨
      (Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom0460 chi)))) ∨
      ((((Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom0490 chi) ∨
      (Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom0556 chi)) ∨
      ((Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom0842 chi) ∨
      (¬Fin15AnchoredAtom1843 chi ∧
      Fin15AnchoredAtom0458 chi ∧
      Fin15AnchoredAtom0460 chi ∧
      Fin15AnchoredAtom0490 chi ∧
      Fin15AnchoredAtom0556 chi ∧
      Fin15AnchoredAtom0842 chi))) ∨
      (((Fin15AnchoredAtom1844 chi ∧
      ¬Fin15AnchoredAtom0458 chi) ∨
      (Fin15AnchoredAtom1844 chi ∧
      ¬Fin15AnchoredAtom0461 chi)) ∨
      ((Fin15AnchoredAtom1844 chi ∧
      ¬Fin15AnchoredAtom0491 chi) ∨
      (Fin15AnchoredAtom1844 chi ∧
      ¬Fin15AnchoredAtom0843 chi)))))))) ∨
      (((((((¬Fin15AnchoredAtom1844 chi ∧
      Fin15AnchoredAtom0458 chi ∧
      Fin15AnchoredAtom0461 chi ∧
      Fin15AnchoredAtom0491 chi ∧
      Fin15AnchoredAtom0557 chi ∧
      Fin15AnchoredAtom0843 chi) ∨
      ((Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom0458 chi) ∨
      (Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom0462 chi))) ∨
      (((Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom0492 chi) ∨
      (Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom0558 chi)) ∨
      ((Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom0844 chi) ∨
      (¬Fin15AnchoredAtom1845 chi ∧
      Fin15AnchoredAtom0458 chi ∧
      Fin15AnchoredAtom0462 chi ∧
      Fin15AnchoredAtom0492 chi ∧
      Fin15AnchoredAtom0558 chi ∧
      Fin15AnchoredAtom0844 chi)))) ∨
      ((((Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom0458 chi) ∨
      (Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom0463 chi)) ∨
      ((Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom0493 chi) ∨
      (Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom0559 chi))) ∨
      (((Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom0845 chi) ∨
      (¬Fin15AnchoredAtom1846 chi ∧
      Fin15AnchoredAtom0458 chi ∧
      Fin15AnchoredAtom0463 chi ∧
      Fin15AnchoredAtom0493 chi ∧
      Fin15AnchoredAtom0559 chi ∧
      Fin15AnchoredAtom0845 chi)) ∨
      ((Fin15AnchoredAtom1847 chi ∧
      ¬Fin15AnchoredAtom0458 chi) ∨
      (Fin15AnchoredAtom1847 chi ∧
      ¬Fin15AnchoredAtom0494 chi))))) ∨
      (((((Fin15AnchoredAtom1847 chi ∧
      ¬Fin15AnchoredAtom0560 chi) ∨
      (Fin15AnchoredAtom1847 chi ∧
      ¬Fin15AnchoredAtom0846 chi)) ∨
      ((¬Fin15AnchoredAtom1847 chi ∧
      Fin15AnchoredAtom0458 chi ∧
      Fin15AnchoredAtom0464 chi ∧
      Fin15AnchoredAtom0494 chi ∧
      Fin15AnchoredAtom0560 chi ∧
      Fin15AnchoredAtom0846 chi) ∨
      (Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom0458 chi))) ∨
      (((Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom0465 chi) ∨
      (Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom0495 chi)) ∨
      ((Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom0561 chi) ∨
      (Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom0847 chi)))) ∨
      ((((¬Fin15AnchoredAtom1848 chi ∧
      Fin15AnchoredAtom0458 chi ∧
      Fin15AnchoredAtom0465 chi ∧
      Fin15AnchoredAtom0495 chi ∧
      Fin15AnchoredAtom0561 chi ∧
      Fin15AnchoredAtom0847 chi) ∨
      (Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom0458 chi)) ∨
      ((Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom0466 chi) ∨
      (Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom0496 chi))) ∨
      (((Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom0562 chi) ∨
      (Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom0848 chi)) ∨
      ((¬Fin15AnchoredAtom1849 chi ∧
      Fin15AnchoredAtom0458 chi ∧
      Fin15AnchoredAtom0466 chi ∧
      Fin15AnchoredAtom0496 chi ∧
      Fin15AnchoredAtom0562 chi ∧
      Fin15AnchoredAtom0848 chi) ∨
      (Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom0458 chi)))))) ∨
      ((((((Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom0467 chi) ∨
      (Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom0497 chi)) ∨
      ((Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom0563 chi) ∨
      (Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom0849 chi))) ∨
      (((¬Fin15AnchoredAtom1850 chi ∧
      Fin15AnchoredAtom0458 chi ∧
      Fin15AnchoredAtom0467 chi ∧
      Fin15AnchoredAtom0497 chi ∧
      Fin15AnchoredAtom0563 chi ∧
      Fin15AnchoredAtom0849 chi) ∨
      (Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom0459 chi)) ∨
      ((Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom0460 chi) ∨
      (Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom0498 chi)))) ∨
      ((((Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom0564 chi) ∨
      (Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom0850 chi)) ∨
      ((¬Fin15AnchoredAtom1851 chi ∧
      Fin15AnchoredAtom0459 chi ∧
      Fin15AnchoredAtom0460 chi ∧
      Fin15AnchoredAtom0498 chi ∧
      Fin15AnchoredAtom0564 chi ∧
      Fin15AnchoredAtom0850 chi) ∨
      (Fin15AnchoredAtom1852 chi ∧
      ¬Fin15AnchoredAtom0459 chi))) ∨
      (((Fin15AnchoredAtom1852 chi ∧
      ¬Fin15AnchoredAtom0461 chi) ∨
      (Fin15AnchoredAtom1852 chi ∧
      ¬Fin15AnchoredAtom0499 chi)) ∨
      ((Fin15AnchoredAtom1852 chi ∧
      ¬Fin15AnchoredAtom0565 chi) ∨
      (Fin15AnchoredAtom1852 chi ∧
      ¬Fin15AnchoredAtom0851 chi))))) ∨
      (((((¬Fin15AnchoredAtom1852 chi ∧
      Fin15AnchoredAtom0459 chi ∧
      Fin15AnchoredAtom0461 chi ∧
      Fin15AnchoredAtom0499 chi ∧
      Fin15AnchoredAtom0565 chi ∧
      Fin15AnchoredAtom0851 chi) ∨
      (Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom0459 chi)) ∨
      ((Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom0462 chi) ∨
      (Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom0500 chi))) ∨
      (((Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom0566 chi) ∨
      (Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom0852 chi)) ∨
      ((¬Fin15AnchoredAtom1853 chi ∧
      Fin15AnchoredAtom0459 chi ∧
      Fin15AnchoredAtom0462 chi ∧
      Fin15AnchoredAtom0500 chi ∧
      Fin15AnchoredAtom0566 chi ∧
      Fin15AnchoredAtom0852 chi) ∨
      (Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom0459 chi)))) ∨
      ((((Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom0463 chi) ∨
      (Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom0501 chi)) ∨
      ((Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom0567 chi) ∨
      (Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom0853 chi))) ∨
      (((¬Fin15AnchoredAtom1854 chi ∧
      Fin15AnchoredAtom0459 chi ∧
      Fin15AnchoredAtom0463 chi ∧
      Fin15AnchoredAtom0501 chi ∧
      Fin15AnchoredAtom0567 chi ∧
      Fin15AnchoredAtom0853 chi) ∨
      (Fin15AnchoredAtom1855 chi ∧
      ¬Fin15AnchoredAtom0459 chi)) ∨
      ((Fin15AnchoredAtom1855 chi ∧
      ¬Fin15AnchoredAtom0854 chi) ∨
      (¬Fin15AnchoredAtom1855 chi ∧
      Fin15AnchoredAtom0459 chi ∧
      Fin15AnchoredAtom0464 chi ∧
      Fin15AnchoredAtom0502 chi ∧
      Fin15AnchoredAtom0568 chi ∧
      Fin15AnchoredAtom0854 chi))))))) ∨
      (((((((Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom0459 chi) ∨
      (Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom0465 chi)) ∨
      ((Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom0503 chi) ∨
      (Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom0569 chi))) ∨
      (((Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom0855 chi) ∨
      (¬Fin15AnchoredAtom1856 chi ∧
      Fin15AnchoredAtom0459 chi ∧
      Fin15AnchoredAtom0465 chi ∧
      Fin15AnchoredAtom0503 chi ∧
      Fin15AnchoredAtom0569 chi ∧
      Fin15AnchoredAtom0855 chi)) ∨
      ((Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom0459 chi) ∨
      (Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom0466 chi)))) ∨
      ((((Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom0504 chi) ∨
      (Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom0570 chi)) ∨
      ((Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom0856 chi) ∨
      (¬Fin15AnchoredAtom1857 chi ∧
      Fin15AnchoredAtom0459 chi ∧
      Fin15AnchoredAtom0466 chi ∧
      Fin15AnchoredAtom0504 chi ∧
      Fin15AnchoredAtom0570 chi ∧
      Fin15AnchoredAtom0856 chi))) ∨
      (((Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom0459 chi) ∨
      (Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom0467 chi)) ∨
      ((Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom0505 chi) ∨
      (Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom0571 chi))))) ∨
      (((((Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom0857 chi) ∨
      (¬Fin15AnchoredAtom1858 chi ∧
      Fin15AnchoredAtom0459 chi ∧
      Fin15AnchoredAtom0467 chi ∧
      Fin15AnchoredAtom0505 chi ∧
      Fin15AnchoredAtom0571 chi ∧
      Fin15AnchoredAtom0857 chi)) ∨
      ((Fin15AnchoredAtom1859 chi ∧
      ¬Fin15AnchoredAtom0460 chi) ∨
      (Fin15AnchoredAtom1859 chi ∧
      ¬Fin15AnchoredAtom0461 chi))) ∨
      (((Fin15AnchoredAtom1859 chi ∧
      ¬Fin15AnchoredAtom0572 chi) ∨
      (Fin15AnchoredAtom1859 chi ∧
      ¬Fin15AnchoredAtom0858 chi)) ∨
      ((¬Fin15AnchoredAtom1859 chi ∧
      Fin15AnchoredAtom0460 chi ∧
      Fin15AnchoredAtom0461 chi ∧
      Fin15AnchoredAtom0506 chi ∧
      Fin15AnchoredAtom0572 chi ∧
      Fin15AnchoredAtom0858 chi) ∨
      (Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom0460 chi)))) ∨
      ((((Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom0462 chi) ∨
      (Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom0507 chi)) ∨
      ((Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom0573 chi) ∨
      (Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom0859 chi))) ∨
      (((¬Fin15AnchoredAtom1860 chi ∧
      Fin15AnchoredAtom0460 chi ∧
      Fin15AnchoredAtom0462 chi ∧
      Fin15AnchoredAtom0507 chi ∧
      Fin15AnchoredAtom0573 chi ∧
      Fin15AnchoredAtom0859 chi) ∨
      (Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom0460 chi)) ∨
      ((Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom0463 chi) ∨
      (Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom0508 chi)))))) ∨
      ((((((Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom0574 chi) ∨
      (Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom0860 chi)) ∨
      ((¬Fin15AnchoredAtom1861 chi ∧
      Fin15AnchoredAtom0460 chi ∧
      Fin15AnchoredAtom0463 chi ∧
      Fin15AnchoredAtom0508 chi ∧
      Fin15AnchoredAtom0574 chi ∧
      Fin15AnchoredAtom0860 chi) ∨
      (Fin15AnchoredAtom1862 chi ∧
      ¬Fin15AnchoredAtom0460 chi))) ∨
      (((Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom0460 chi) ∨
      (Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom0465 chi)) ∨
      ((Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom0510 chi) ∨
      (Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom0576 chi)))) ∨
      ((((Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom0862 chi) ∨
      (¬Fin15AnchoredAtom1863 chi ∧
      Fin15AnchoredAtom0460 chi ∧
      Fin15AnchoredAtom0465 chi ∧
      Fin15AnchoredAtom0510 chi ∧
      Fin15AnchoredAtom0576 chi ∧
      Fin15AnchoredAtom0862 chi)) ∨
      ((Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom0460 chi) ∨
      (Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom0466 chi))) ∨
      (((Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom0511 chi) ∨
      (Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom0577 chi)) ∨
      ((Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom0863 chi) ∨
      (¬Fin15AnchoredAtom1864 chi ∧
      Fin15AnchoredAtom0460 chi ∧
      Fin15AnchoredAtom0466 chi ∧
      Fin15AnchoredAtom0511 chi ∧
      Fin15AnchoredAtom0577 chi ∧
      Fin15AnchoredAtom0863 chi))))) ∨
      (((((Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom0460 chi) ∨
      (Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom0467 chi)) ∨
      ((Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom0512 chi) ∨
      (Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom0578 chi))) ∨
      (((Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom0864 chi) ∨
      (¬Fin15AnchoredAtom1865 chi ∧
      Fin15AnchoredAtom0460 chi ∧
      Fin15AnchoredAtom0467 chi ∧
      Fin15AnchoredAtom0512 chi ∧
      Fin15AnchoredAtom0578 chi ∧
      Fin15AnchoredAtom0864 chi)) ∨
      ((Fin15AnchoredAtom1866 chi ∧
      ¬Fin15AnchoredAtom0462 chi) ∨
      (Fin15AnchoredAtom1866 chi ∧
      ¬Fin15AnchoredAtom0865 chi)))) ∨
      ((((¬Fin15AnchoredAtom1866 chi ∧
      Fin15AnchoredAtom0461 chi ∧
      Fin15AnchoredAtom0462 chi ∧
      Fin15AnchoredAtom0513 chi ∧
      Fin15AnchoredAtom0579 chi ∧
      Fin15AnchoredAtom0865 chi) ∨
      (Fin15AnchoredAtom1867 chi ∧
      ¬Fin15AnchoredAtom0463 chi)) ∨
      ((Fin15AnchoredAtom1867 chi ∧
      ¬Fin15AnchoredAtom0866 chi) ∨
      (¬Fin15AnchoredAtom1867 chi ∧
      Fin15AnchoredAtom0461 chi ∧
      Fin15AnchoredAtom0463 chi ∧
      Fin15AnchoredAtom0514 chi ∧
      Fin15AnchoredAtom0580 chi ∧
      Fin15AnchoredAtom0866 chi))) ∨
      (((Fin15AnchoredAtom1869 chi ∧
      ¬Fin15AnchoredAtom0868 chi) ∨
      (¬Fin15AnchoredAtom1869 chi ∧
      Fin15AnchoredAtom0461 chi ∧
      Fin15AnchoredAtom0465 chi ∧
      Fin15AnchoredAtom0516 chi ∧
      Fin15AnchoredAtom0582 chi ∧
      Fin15AnchoredAtom0868 chi)) ∨
      ((Fin15AnchoredAtom1871 chi ∧
      ¬Fin15AnchoredAtom0870 chi) ∨
      (¬Fin15AnchoredAtom1871 chi ∧
      Fin15AnchoredAtom0461 chi ∧
      Fin15AnchoredAtom0467 chi ∧
      Fin15AnchoredAtom0518 chi ∧
      Fin15AnchoredAtom0584 chi ∧
      Fin15AnchoredAtom0870 chi)))))))))) := by
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
                exact fin15Anchored_clause15396 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15397 chi hbad
                ·
                  exact fin15Anchored_clause15398 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15399 chi hbad
                ·
                  exact fin15Anchored_clause15400 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15401 chi hbad
                ·
                  exact fin15Anchored_clause15402 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15403 chi hbad
                ·
                  exact fin15Anchored_clause15404 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15405 chi hbad
                ·
                  exact fin15Anchored_clause15406 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15407 chi hbad
                ·
                  exact fin15Anchored_clause15408 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15409 chi hbad
                ·
                  exact fin15Anchored_clause15410 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15411 chi hbad
                ·
                  exact fin15Anchored_clause15412 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15413 chi hbad
                ·
                  exact fin15Anchored_clause15414 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15415 chi hbad
                ·
                  exact fin15Anchored_clause15416 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15417 chi hbad
                ·
                  exact fin15Anchored_clause15418 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15419 chi hbad
                ·
                  exact fin15Anchored_clause15420 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15421 chi hbad
                ·
                  exact fin15Anchored_clause15422 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15423 chi hbad
                ·
                  exact fin15Anchored_clause15424 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15425 chi hbad
                ·
                  exact fin15Anchored_clause15426 chi hbad
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
                  exact fin15Anchored_clause15427 chi hbad
                ·
                  exact fin15Anchored_clause15428 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15429 chi hbad
                ·
                  exact fin15Anchored_clause15430 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15431 chi hbad
                ·
                  exact fin15Anchored_clause15432 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15433 chi hbad
                ·
                  exact fin15Anchored_clause15434 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15435 chi hbad
                ·
                  exact fin15Anchored_clause15436 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15437 chi hbad
                ·
                  exact fin15Anchored_clause15438 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15439 chi hbad
                ·
                  exact fin15Anchored_clause15440 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15441 chi hbad
                ·
                  exact fin15Anchored_clause15442 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15443 chi hbad
                ·
                  exact fin15Anchored_clause15444 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15445 chi hbad
                ·
                  exact fin15Anchored_clause15446 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15447 chi hbad
                ·
                  exact fin15Anchored_clause15448 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15449 chi hbad
                ·
                  exact fin15Anchored_clause15450 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15451 chi hbad
                ·
                  exact fin15Anchored_clause15452 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15453 chi hbad
                ·
                  exact fin15Anchored_clause15454 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15455 chi hbad
                ·
                  exact fin15Anchored_clause15456 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15457 chi hbad
                ·
                  exact fin15Anchored_clause15458 chi hbad
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
                exact fin15Anchored_clause15459 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15460 chi hbad
                ·
                  exact fin15Anchored_clause15461 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15462 chi hbad
                ·
                  exact fin15Anchored_clause15463 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15464 chi hbad
                ·
                  exact fin15Anchored_clause15465 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15466 chi hbad
                ·
                  exact fin15Anchored_clause15467 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15468 chi hbad
                ·
                  exact fin15Anchored_clause15469 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15470 chi hbad
                ·
                  exact fin15Anchored_clause15471 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15472 chi hbad
                ·
                  exact fin15Anchored_clause15473 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15474 chi hbad
                ·
                  exact fin15Anchored_clause15475 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15476 chi hbad
                ·
                  exact fin15Anchored_clause15477 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15478 chi hbad
                ·
                  exact fin15Anchored_clause15479 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15480 chi hbad
                ·
                  exact fin15Anchored_clause15481 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15482 chi hbad
                ·
                  exact fin15Anchored_clause15483 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15484 chi hbad
                ·
                  exact fin15Anchored_clause15485 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15486 chi hbad
                ·
                  exact fin15Anchored_clause15487 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15488 chi hbad
                ·
                  exact fin15Anchored_clause15489 chi hbad
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
                  exact fin15Anchored_clause15490 chi hbad
                ·
                  exact fin15Anchored_clause15491 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15492 chi hbad
                ·
                  exact fin15Anchored_clause15493 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15494 chi hbad
                ·
                  exact fin15Anchored_clause15495 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15496 chi hbad
                ·
                  exact fin15Anchored_clause15497 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15498 chi hbad
                ·
                  exact fin15Anchored_clause15499 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15500 chi hbad
                ·
                  exact fin15Anchored_clause15501 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15502 chi hbad
                ·
                  exact fin15Anchored_clause15503 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15504 chi hbad
                ·
                  exact fin15Anchored_clause15505 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15506 chi hbad
                ·
                  exact fin15Anchored_clause15507 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15508 chi hbad
                ·
                  exact fin15Anchored_clause15509 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15510 chi hbad
                ·
                  exact fin15Anchored_clause15511 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15512 chi hbad
                ·
                  exact fin15Anchored_clause15513 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15514 chi hbad
                ·
                  exact fin15Anchored_clause15515 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15516 chi hbad
                ·
                  exact fin15Anchored_clause15517 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15518 chi hbad
                ·
                  exact fin15Anchored_clause15519 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15520 chi hbad
                ·
                  exact fin15Anchored_clause15521 chi hbad
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
                exact fin15Anchored_clause15522 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15523 chi hbad
                ·
                  exact fin15Anchored_clause15524 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15525 chi hbad
                ·
                  exact fin15Anchored_clause15526 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15527 chi hbad
                ·
                  exact fin15Anchored_clause15528 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15529 chi hbad
                ·
                  exact fin15Anchored_clause15530 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15531 chi hbad
                ·
                  exact fin15Anchored_clause15532 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15533 chi hbad
                ·
                  exact fin15Anchored_clause15534 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15535 chi hbad
                ·
                  exact fin15Anchored_clause15536 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15537 chi hbad
                ·
                  exact fin15Anchored_clause15538 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15539 chi hbad
                ·
                  exact fin15Anchored_clause15540 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15541 chi hbad
                ·
                  exact fin15Anchored_clause15542 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15543 chi hbad
                ·
                  exact fin15Anchored_clause15544 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15545 chi hbad
                ·
                  exact fin15Anchored_clause15546 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15547 chi hbad
                ·
                  exact fin15Anchored_clause15548 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15549 chi hbad
                ·
                  exact fin15Anchored_clause15550 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15551 chi hbad
                ·
                  exact fin15Anchored_clause15552 chi hbad
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
                  exact fin15Anchored_clause15553 chi hbad
                ·
                  exact fin15Anchored_clause15554 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15555 chi hbad
                ·
                  exact fin15Anchored_clause15556 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15557 chi hbad
                ·
                  exact fin15Anchored_clause15558 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15559 chi hbad
                ·
                  exact fin15Anchored_clause15560 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15561 chi hbad
                ·
                  exact fin15Anchored_clause15562 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15563 chi hbad
                ·
                  exact fin15Anchored_clause15564 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15565 chi hbad
                ·
                  exact fin15Anchored_clause15566 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15567 chi hbad
                ·
                  exact fin15Anchored_clause15568 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15569 chi hbad
                ·
                  exact fin15Anchored_clause15570 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15571 chi hbad
                ·
                  exact fin15Anchored_clause15572 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15573 chi hbad
                ·
                  exact fin15Anchored_clause15574 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15575 chi hbad
                ·
                  exact fin15Anchored_clause15576 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15577 chi hbad
                ·
                  exact fin15Anchored_clause15578 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15579 chi hbad
                ·
                  exact fin15Anchored_clause15580 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15581 chi hbad
                ·
                  exact fin15Anchored_clause15582 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15583 chi hbad
                ·
                  exact fin15Anchored_clause15584 chi hbad
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
                  exact fin15Anchored_clause15585 chi hbad
                ·
                  exact fin15Anchored_clause15586 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15587 chi hbad
                ·
                  exact fin15Anchored_clause15588 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15589 chi hbad
                ·
                  exact fin15Anchored_clause15590 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15591 chi hbad
                ·
                  exact fin15Anchored_clause15592 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15593 chi hbad
                ·
                  exact fin15Anchored_clause15594 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15595 chi hbad
                ·
                  exact fin15Anchored_clause15596 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15597 chi hbad
                ·
                  exact fin15Anchored_clause15598 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15599 chi hbad
                ·
                  exact fin15Anchored_clause15600 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15601 chi hbad
                ·
                  exact fin15Anchored_clause15602 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15603 chi hbad
                ·
                  exact fin15Anchored_clause15604 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15605 chi hbad
                ·
                  exact fin15Anchored_clause15606 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15607 chi hbad
                ·
                  exact fin15Anchored_clause15608 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15609 chi hbad
                ·
                  exact fin15Anchored_clause15610 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15611 chi hbad
                ·
                  exact fin15Anchored_clause15612 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15613 chi hbad
                ·
                  exact fin15Anchored_clause15614 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15615 chi hbad
                ·
                  exact fin15Anchored_clause15616 chi hbad
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
                  exact fin15Anchored_clause15617 chi hbad
                ·
                  exact fin15Anchored_clause15618 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15619 chi hbad
                ·
                  exact fin15Anchored_clause15620 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15621 chi hbad
                ·
                  exact fin15Anchored_clause15622 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15623 chi hbad
                ·
                  exact fin15Anchored_clause15624 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15625 chi hbad
                ·
                  exact fin15Anchored_clause15626 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15627 chi hbad
                ·
                  exact fin15Anchored_clause15628 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15629 chi hbad
                ·
                  exact fin15Anchored_clause15630 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15631 chi hbad
                ·
                  exact fin15Anchored_clause15632 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15633 chi hbad
                ·
                  exact fin15Anchored_clause15634 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15635 chi hbad
                ·
                  exact fin15Anchored_clause15636 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15637 chi hbad
                ·
                  exact fin15Anchored_clause15638 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15639 chi hbad
                ·
                  exact fin15Anchored_clause15640 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15641 chi hbad
                ·
                  exact fin15Anchored_clause15642 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15643 chi hbad
                ·
                  exact fin15Anchored_clause15644 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15645 chi hbad
                ·
                  exact fin15Anchored_clause15646 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15647 chi hbad
                ·
                  exact fin15Anchored_clause15648 chi hbad

end ErdosSzekeres

end
