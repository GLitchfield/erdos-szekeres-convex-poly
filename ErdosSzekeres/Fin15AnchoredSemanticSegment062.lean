module

public import ErdosSzekeres.Fin15AnchoredClauseChunk122
public import ErdosSzekeres.Fin15AnchoredClauseChunk123
public import ErdosSzekeres.Fin15AnchoredClauseChunk124

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 062. -/

theorem fin15Anchored_rejectSemanticSegment062
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom0462 chi) ∨
      ((Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom0463 chi) ∨
      (Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom0519 chi))) ∨
      (((Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom0585 chi) ∨
      (Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom0871 chi)) ∨
      ((¬Fin15AnchoredAtom1872 chi ∧
      Fin15AnchoredAtom0462 chi ∧
      Fin15AnchoredAtom0463 chi ∧
      Fin15AnchoredAtom0519 chi ∧
      Fin15AnchoredAtom0585 chi ∧
      Fin15AnchoredAtom0871 chi) ∨
      (Fin15AnchoredAtom1873 chi ∧
      ¬Fin15AnchoredAtom0462 chi)))) ∨
      ((((Fin15AnchoredAtom1873 chi ∧
      ¬Fin15AnchoredAtom0464 chi) ∨
      (Fin15AnchoredAtom1873 chi ∧
      ¬Fin15AnchoredAtom0586 chi)) ∨
      ((Fin15AnchoredAtom1873 chi ∧
      ¬Fin15AnchoredAtom0872 chi) ∨
      (¬Fin15AnchoredAtom1873 chi ∧
      Fin15AnchoredAtom0462 chi ∧
      Fin15AnchoredAtom0464 chi ∧
      Fin15AnchoredAtom0520 chi ∧
      Fin15AnchoredAtom0586 chi ∧
      Fin15AnchoredAtom0872 chi))) ∨
      (((Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom0462 chi) ∨
      (Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom0465 chi)) ∨
      ((Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom0521 chi) ∨
      (Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom0587 chi))))) ∨
      (((((Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom0873 chi) ∨
      (¬Fin15AnchoredAtom1874 chi ∧
      Fin15AnchoredAtom0462 chi ∧
      Fin15AnchoredAtom0465 chi ∧
      Fin15AnchoredAtom0521 chi ∧
      Fin15AnchoredAtom0587 chi ∧
      Fin15AnchoredAtom0873 chi)) ∨
      ((Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom0462 chi) ∨
      (Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom0466 chi))) ∨
      (((Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom0522 chi) ∨
      (Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom0588 chi)) ∨
      ((Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom0874 chi) ∨
      (¬Fin15AnchoredAtom1875 chi ∧
      Fin15AnchoredAtom0462 chi ∧
      Fin15AnchoredAtom0466 chi ∧
      Fin15AnchoredAtom0522 chi ∧
      Fin15AnchoredAtom0588 chi ∧
      Fin15AnchoredAtom0874 chi)))) ∨
      ((((Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom0462 chi) ∨
      (Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom0467 chi)) ∨
      ((Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom0523 chi) ∨
      (Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom0589 chi))) ∨
      (((Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom0875 chi) ∨
      (¬Fin15AnchoredAtom1876 chi ∧
      Fin15AnchoredAtom0462 chi ∧
      Fin15AnchoredAtom0467 chi ∧
      Fin15AnchoredAtom0523 chi ∧
      Fin15AnchoredAtom0589 chi ∧
      Fin15AnchoredAtom0875 chi)) ∨
      ((Fin15AnchoredAtom1877 chi ∧
      ¬Fin15AnchoredAtom0463 chi) ∨
      (Fin15AnchoredAtom1877 chi ∧
      ¬Fin15AnchoredAtom0590 chi)))))) ∨
      ((((((Fin15AnchoredAtom1877 chi ∧
      ¬Fin15AnchoredAtom0876 chi) ∨
      (¬Fin15AnchoredAtom1877 chi ∧
      Fin15AnchoredAtom0463 chi ∧
      Fin15AnchoredAtom0464 chi ∧
      Fin15AnchoredAtom0524 chi ∧
      Fin15AnchoredAtom0590 chi ∧
      Fin15AnchoredAtom0876 chi)) ∨
      ((Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom0463 chi) ∨
      (Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom0465 chi))) ∨
      (((Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom0525 chi) ∨
      (Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom0591 chi)) ∨
      ((Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom0877 chi) ∨
      (¬Fin15AnchoredAtom1878 chi ∧
      Fin15AnchoredAtom0463 chi ∧
      Fin15AnchoredAtom0465 chi ∧
      Fin15AnchoredAtom0525 chi ∧
      Fin15AnchoredAtom0591 chi ∧
      Fin15AnchoredAtom0877 chi)))) ∨
      ((((Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom0463 chi) ∨
      (Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom0466 chi)) ∨
      ((Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom0526 chi) ∨
      (Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom0592 chi))) ∨
      (((Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom0878 chi) ∨
      (¬Fin15AnchoredAtom1879 chi ∧
      Fin15AnchoredAtom0463 chi ∧
      Fin15AnchoredAtom0466 chi ∧
      Fin15AnchoredAtom0526 chi ∧
      Fin15AnchoredAtom0592 chi ∧
      Fin15AnchoredAtom0878 chi)) ∨
      ((Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom0463 chi) ∨
      (Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom0467 chi))))) ∨
      (((((Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom0527 chi) ∨
      (Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom0593 chi)) ∨
      ((Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom0879 chi) ∨
      (¬Fin15AnchoredAtom1880 chi ∧
      Fin15AnchoredAtom0463 chi ∧
      Fin15AnchoredAtom0467 chi ∧
      Fin15AnchoredAtom0527 chi ∧
      Fin15AnchoredAtom0593 chi ∧
      Fin15AnchoredAtom0879 chi))) ∨
      (((Fin15AnchoredAtom1881 chi ∧
      ¬Fin15AnchoredAtom0465 chi) ∨
      (Fin15AnchoredAtom1881 chi ∧
      ¬Fin15AnchoredAtom0594 chi)) ∨
      ((Fin15AnchoredAtom1881 chi ∧
      ¬Fin15AnchoredAtom0880 chi) ∨
      (¬Fin15AnchoredAtom1881 chi ∧
      Fin15AnchoredAtom0464 chi ∧
      Fin15AnchoredAtom0465 chi ∧
      Fin15AnchoredAtom0528 chi ∧
      Fin15AnchoredAtom0594 chi ∧
      Fin15AnchoredAtom0880 chi)))) ∨
      ((((Fin15AnchoredAtom1882 chi ∧
      ¬Fin15AnchoredAtom0881 chi) ∨
      (¬Fin15AnchoredAtom1882 chi ∧
      Fin15AnchoredAtom0464 chi ∧
      Fin15AnchoredAtom0466 chi ∧
      Fin15AnchoredAtom0529 chi ∧
      Fin15AnchoredAtom0595 chi ∧
      Fin15AnchoredAtom0881 chi)) ∨
      ((Fin15AnchoredAtom1883 chi ∧
      ¬Fin15AnchoredAtom0882 chi) ∨
      (¬Fin15AnchoredAtom1883 chi ∧
      Fin15AnchoredAtom0464 chi ∧
      Fin15AnchoredAtom0467 chi ∧
      Fin15AnchoredAtom0530 chi ∧
      Fin15AnchoredAtom0596 chi ∧
      Fin15AnchoredAtom0882 chi))) ∨
      (((Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom0465 chi) ∨
      (Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom0466 chi)) ∨
      ((Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom0531 chi) ∨
      (Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom0597 chi))))))) ∨
      ((((((Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom0883 chi) ∨
      ((¬Fin15AnchoredAtom1884 chi ∧
      Fin15AnchoredAtom0465 chi ∧
      Fin15AnchoredAtom0466 chi ∧
      Fin15AnchoredAtom0531 chi ∧
      Fin15AnchoredAtom0597 chi ∧
      Fin15AnchoredAtom0883 chi) ∨
      (Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom0465 chi))) ∨
      (((Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom0467 chi) ∨
      (Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom0532 chi)) ∨
      ((Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom0598 chi) ∨
      (Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom0884 chi)))) ∨
      ((((¬Fin15AnchoredAtom1885 chi ∧
      Fin15AnchoredAtom0465 chi ∧
      Fin15AnchoredAtom0467 chi ∧
      Fin15AnchoredAtom0532 chi ∧
      Fin15AnchoredAtom0598 chi ∧
      Fin15AnchoredAtom0884 chi) ∨
      (Fin15AnchoredAtom1886 chi ∧
      ¬Fin15AnchoredAtom0466 chi)) ∨
      ((Fin15AnchoredAtom1886 chi ∧
      ¬Fin15AnchoredAtom0467 chi) ∨
      (Fin15AnchoredAtom1886 chi ∧
      ¬Fin15AnchoredAtom0533 chi))) ∨
      (((Fin15AnchoredAtom1886 chi ∧
      ¬Fin15AnchoredAtom0599 chi) ∨
      (Fin15AnchoredAtom1886 chi ∧
      ¬Fin15AnchoredAtom0885 chi)) ∨
      ((¬Fin15AnchoredAtom1886 chi ∧
      Fin15AnchoredAtom0466 chi ∧
      Fin15AnchoredAtom0467 chi ∧
      Fin15AnchoredAtom0533 chi ∧
      Fin15AnchoredAtom0599 chi ∧
      Fin15AnchoredAtom0885 chi) ∨
      (Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom0468 chi))))) ∨
      (((((Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom0469 chi) ∨
      (Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom0479 chi)) ∨
      ((Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom0600 chi) ∨
      (Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom0886 chi))) ∨
      (((¬Fin15AnchoredAtom1887 chi ∧
      Fin15AnchoredAtom0468 chi ∧
      Fin15AnchoredAtom0469 chi ∧
      Fin15AnchoredAtom0479 chi ∧
      Fin15AnchoredAtom0600 chi ∧
      Fin15AnchoredAtom0886 chi) ∨
      (Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom0468 chi)) ∨
      ((Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom0470 chi) ∨
      (Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom0480 chi)))) ∨
      ((((Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom0601 chi) ∨
      (Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom0887 chi)) ∨
      ((¬Fin15AnchoredAtom1888 chi ∧
      Fin15AnchoredAtom0468 chi ∧
      Fin15AnchoredAtom0470 chi ∧
      Fin15AnchoredAtom0480 chi ∧
      Fin15AnchoredAtom0601 chi ∧
      Fin15AnchoredAtom0887 chi) ∨
      (Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom0468 chi))) ∨
      (((Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom0471 chi) ∨
      (Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom0481 chi)) ∨
      ((Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom0602 chi) ∨
      (Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom0888 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom1889 chi ∧
      Fin15AnchoredAtom0468 chi ∧
      Fin15AnchoredAtom0471 chi ∧
      Fin15AnchoredAtom0481 chi ∧
      Fin15AnchoredAtom0602 chi ∧
      Fin15AnchoredAtom0888 chi) ∨
      (Fin15AnchoredAtom1890 chi ∧
      ¬Fin15AnchoredAtom0468 chi)) ∨
      ((Fin15AnchoredAtom1890 chi ∧
      ¬Fin15AnchoredAtom0472 chi) ∨
      (Fin15AnchoredAtom1890 chi ∧
      ¬Fin15AnchoredAtom0482 chi))) ∨
      (((Fin15AnchoredAtom1890 chi ∧
      ¬Fin15AnchoredAtom0603 chi) ∨
      (Fin15AnchoredAtom1890 chi ∧
      ¬Fin15AnchoredAtom0889 chi)) ∨
      ((¬Fin15AnchoredAtom1890 chi ∧
      Fin15AnchoredAtom0468 chi ∧
      Fin15AnchoredAtom0472 chi ∧
      Fin15AnchoredAtom0482 chi ∧
      Fin15AnchoredAtom0603 chi ∧
      Fin15AnchoredAtom0889 chi) ∨
      (Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom0468 chi)))) ∨
      ((((Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom0473 chi) ∨
      (Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom0483 chi)) ∨
      ((Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom0604 chi) ∨
      (Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom0890 chi))) ∨
      (((¬Fin15AnchoredAtom1891 chi ∧
      Fin15AnchoredAtom0468 chi ∧
      Fin15AnchoredAtom0473 chi ∧
      Fin15AnchoredAtom0483 chi ∧
      Fin15AnchoredAtom0604 chi ∧
      Fin15AnchoredAtom0890 chi) ∨
      (Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom0468 chi)) ∨
      ((Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom0474 chi) ∨
      (Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom0484 chi))))) ∨
      (((((Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom0605 chi) ∨
      (Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom0891 chi)) ∨
      ((¬Fin15AnchoredAtom1892 chi ∧
      Fin15AnchoredAtom0468 chi ∧
      Fin15AnchoredAtom0474 chi ∧
      Fin15AnchoredAtom0484 chi ∧
      Fin15AnchoredAtom0605 chi ∧
      Fin15AnchoredAtom0891 chi) ∨
      (Fin15AnchoredAtom1893 chi ∧
      ¬Fin15AnchoredAtom0468 chi))) ∨
      (((Fin15AnchoredAtom1893 chi ∧
      ¬Fin15AnchoredAtom0475 chi) ∨
      (Fin15AnchoredAtom1893 chi ∧
      ¬Fin15AnchoredAtom0485 chi)) ∨
      ((Fin15AnchoredAtom1893 chi ∧
      ¬Fin15AnchoredAtom0606 chi) ∨
      (Fin15AnchoredAtom1893 chi ∧
      ¬Fin15AnchoredAtom0892 chi)))) ∨
      ((((¬Fin15AnchoredAtom1893 chi ∧
      Fin15AnchoredAtom0468 chi ∧
      Fin15AnchoredAtom0475 chi ∧
      Fin15AnchoredAtom0485 chi ∧
      Fin15AnchoredAtom0606 chi ∧
      Fin15AnchoredAtom0892 chi) ∨
      (Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom0468 chi)) ∨
      ((Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom0476 chi) ∨
      (Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom0486 chi))) ∨
      (((Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom0607 chi) ∨
      (Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom0893 chi)) ∨
      ((¬Fin15AnchoredAtom1894 chi ∧
      Fin15AnchoredAtom0468 chi ∧
      Fin15AnchoredAtom0476 chi ∧
      Fin15AnchoredAtom0486 chi ∧
      Fin15AnchoredAtom0607 chi ∧
      Fin15AnchoredAtom0893 chi) ∨
      (Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom0468 chi)))))))) ∨
      (((((((Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom0477 chi) ∨
      ((Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom0487 chi) ∨
      (Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom0608 chi))) ∨
      (((Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom0894 chi) ∨
      (¬Fin15AnchoredAtom1895 chi ∧
      Fin15AnchoredAtom0468 chi ∧
      Fin15AnchoredAtom0477 chi ∧
      Fin15AnchoredAtom0487 chi ∧
      Fin15AnchoredAtom0608 chi ∧
      Fin15AnchoredAtom0894 chi)) ∨
      ((Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom0468 chi) ∨
      (Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom0478 chi)))) ∨
      ((((Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom0488 chi) ∨
      (Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom0609 chi)) ∨
      ((Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom0895 chi) ∨
      (¬Fin15AnchoredAtom1896 chi ∧
      Fin15AnchoredAtom0468 chi ∧
      Fin15AnchoredAtom0478 chi ∧
      Fin15AnchoredAtom0488 chi ∧
      Fin15AnchoredAtom0609 chi ∧
      Fin15AnchoredAtom0895 chi))) ∨
      (((Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom0469 chi) ∨
      (Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom0470 chi)) ∨
      ((Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom0489 chi) ∨
      (Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom0610 chi))))) ∨
      (((((Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom0896 chi) ∨
      (¬Fin15AnchoredAtom1897 chi ∧
      Fin15AnchoredAtom0469 chi ∧
      Fin15AnchoredAtom0470 chi ∧
      Fin15AnchoredAtom0489 chi ∧
      Fin15AnchoredAtom0610 chi ∧
      Fin15AnchoredAtom0896 chi)) ∨
      ((Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom0469 chi) ∨
      (Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom0471 chi))) ∨
      (((Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom0490 chi) ∨
      (Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom0611 chi)) ∨
      ((Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom0897 chi) ∨
      (¬Fin15AnchoredAtom1898 chi ∧
      Fin15AnchoredAtom0469 chi ∧
      Fin15AnchoredAtom0471 chi ∧
      Fin15AnchoredAtom0490 chi ∧
      Fin15AnchoredAtom0611 chi ∧
      Fin15AnchoredAtom0897 chi)))) ∨
      ((((Fin15AnchoredAtom1899 chi ∧
      ¬Fin15AnchoredAtom0469 chi) ∨
      (Fin15AnchoredAtom1899 chi ∧
      ¬Fin15AnchoredAtom0472 chi)) ∨
      ((Fin15AnchoredAtom1899 chi ∧
      ¬Fin15AnchoredAtom0491 chi) ∨
      (Fin15AnchoredAtom1899 chi ∧
      ¬Fin15AnchoredAtom0612 chi))) ∨
      (((Fin15AnchoredAtom1899 chi ∧
      ¬Fin15AnchoredAtom0898 chi) ∨
      (¬Fin15AnchoredAtom1899 chi ∧
      Fin15AnchoredAtom0469 chi ∧
      Fin15AnchoredAtom0472 chi ∧
      Fin15AnchoredAtom0491 chi ∧
      Fin15AnchoredAtom0612 chi ∧
      Fin15AnchoredAtom0898 chi)) ∨
      ((Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom0469 chi) ∨
      (Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom0473 chi)))))) ∨
      ((((((Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom0492 chi) ∨
      (Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom0613 chi)) ∨
      ((Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom0899 chi) ∨
      (¬Fin15AnchoredAtom1900 chi ∧
      Fin15AnchoredAtom0469 chi ∧
      Fin15AnchoredAtom0473 chi ∧
      Fin15AnchoredAtom0492 chi ∧
      Fin15AnchoredAtom0613 chi ∧
      Fin15AnchoredAtom0899 chi))) ∨
      (((Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom0469 chi) ∨
      (Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom0474 chi)) ∨
      ((Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom0493 chi) ∨
      (Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom0614 chi)))) ∨
      ((((Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom0900 chi) ∨
      (¬Fin15AnchoredAtom1901 chi ∧
      Fin15AnchoredAtom0469 chi ∧
      Fin15AnchoredAtom0474 chi ∧
      Fin15AnchoredAtom0493 chi ∧
      Fin15AnchoredAtom0614 chi ∧
      Fin15AnchoredAtom0900 chi)) ∨
      ((Fin15AnchoredAtom1902 chi ∧
      ¬Fin15AnchoredAtom0469 chi) ∨
      (Fin15AnchoredAtom1902 chi ∧
      ¬Fin15AnchoredAtom0615 chi))) ∨
      (((Fin15AnchoredAtom1902 chi ∧
      ¬Fin15AnchoredAtom0901 chi) ∨
      (¬Fin15AnchoredAtom1902 chi ∧
      Fin15AnchoredAtom0469 chi ∧
      Fin15AnchoredAtom0475 chi ∧
      Fin15AnchoredAtom0494 chi ∧
      Fin15AnchoredAtom0615 chi ∧
      Fin15AnchoredAtom0901 chi)) ∨
      ((Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom0469 chi) ∨
      (Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom0476 chi))))) ∨
      (((((Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom0495 chi) ∨
      (Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom0616 chi)) ∨
      ((Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom0902 chi) ∨
      (¬Fin15AnchoredAtom1903 chi ∧
      Fin15AnchoredAtom0469 chi ∧
      Fin15AnchoredAtom0476 chi ∧
      Fin15AnchoredAtom0495 chi ∧
      Fin15AnchoredAtom0616 chi ∧
      Fin15AnchoredAtom0902 chi))) ∨
      (((Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom0469 chi) ∨
      (Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom0477 chi)) ∨
      ((Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom0496 chi) ∨
      (Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom0617 chi)))) ∨
      ((((Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom0903 chi) ∨
      (¬Fin15AnchoredAtom1904 chi ∧
      Fin15AnchoredAtom0469 chi ∧
      Fin15AnchoredAtom0477 chi ∧
      Fin15AnchoredAtom0496 chi ∧
      Fin15AnchoredAtom0617 chi ∧
      Fin15AnchoredAtom0903 chi)) ∨
      ((Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom0469 chi) ∨
      (Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom0478 chi))) ∨
      (((Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom0497 chi) ∨
      (Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom0618 chi)) ∨
      ((Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom0904 chi) ∨
      (¬Fin15AnchoredAtom1905 chi ∧
      Fin15AnchoredAtom0469 chi ∧
      Fin15AnchoredAtom0478 chi ∧
      Fin15AnchoredAtom0497 chi ∧
      Fin15AnchoredAtom0618 chi ∧
      Fin15AnchoredAtom0904 chi))))))) ∨
      ((((((Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom0470 chi) ∨
      ((Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom0471 chi) ∨
      (Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom0498 chi))) ∨
      (((Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom0619 chi) ∨
      (Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom0905 chi)) ∨
      ((¬Fin15AnchoredAtom1906 chi ∧
      Fin15AnchoredAtom0470 chi ∧
      Fin15AnchoredAtom0471 chi ∧
      Fin15AnchoredAtom0498 chi ∧
      Fin15AnchoredAtom0619 chi ∧
      Fin15AnchoredAtom0905 chi) ∨
      (Fin15AnchoredAtom1907 chi ∧
      ¬Fin15AnchoredAtom0470 chi)))) ∨
      ((((Fin15AnchoredAtom1907 chi ∧
      ¬Fin15AnchoredAtom0472 chi) ∨
      (Fin15AnchoredAtom1907 chi ∧
      ¬Fin15AnchoredAtom0499 chi)) ∨
      ((Fin15AnchoredAtom1907 chi ∧
      ¬Fin15AnchoredAtom0620 chi) ∨
      (¬Fin15AnchoredAtom1907 chi ∧
      Fin15AnchoredAtom0470 chi ∧
      Fin15AnchoredAtom0472 chi ∧
      Fin15AnchoredAtom0499 chi ∧
      Fin15AnchoredAtom0620 chi ∧
      Fin15AnchoredAtom0906 chi))) ∨
      (((Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom0470 chi) ∨
      (Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom0473 chi)) ∨
      ((Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom0500 chi) ∨
      (Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom0621 chi))))) ∨
      (((((Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom0907 chi) ∨
      (¬Fin15AnchoredAtom1908 chi ∧
      Fin15AnchoredAtom0470 chi ∧
      Fin15AnchoredAtom0473 chi ∧
      Fin15AnchoredAtom0500 chi ∧
      Fin15AnchoredAtom0621 chi ∧
      Fin15AnchoredAtom0907 chi)) ∨
      ((Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom0470 chi) ∨
      (Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom0474 chi))) ∨
      (((Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom0501 chi) ∨
      (Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom0622 chi)) ∨
      ((Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom0908 chi) ∨
      (¬Fin15AnchoredAtom1909 chi ∧
      Fin15AnchoredAtom0470 chi ∧
      Fin15AnchoredAtom0474 chi ∧
      Fin15AnchoredAtom0501 chi ∧
      Fin15AnchoredAtom0622 chi ∧
      Fin15AnchoredAtom0908 chi)))) ∨
      ((((Fin15AnchoredAtom1910 chi ∧
      ¬Fin15AnchoredAtom0470 chi) ∨
      (Fin15AnchoredAtom1910 chi ∧
      ¬Fin15AnchoredAtom0623 chi)) ∨
      ((Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom0470 chi) ∨
      (Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom0476 chi))) ∨
      (((Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom0503 chi) ∨
      (Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom0624 chi)) ∨
      ((Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom0910 chi) ∨
      (¬Fin15AnchoredAtom1911 chi ∧
      Fin15AnchoredAtom0470 chi ∧
      Fin15AnchoredAtom0476 chi ∧
      Fin15AnchoredAtom0503 chi ∧
      Fin15AnchoredAtom0624 chi ∧
      Fin15AnchoredAtom0910 chi)))))) ∨
      ((((((Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom0470 chi) ∨
      (Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom0477 chi)) ∨
      ((Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom0504 chi) ∨
      (Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom0625 chi))) ∨
      (((Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom0911 chi) ∨
      (¬Fin15AnchoredAtom1912 chi ∧
      Fin15AnchoredAtom0470 chi ∧
      Fin15AnchoredAtom0477 chi ∧
      Fin15AnchoredAtom0504 chi ∧
      Fin15AnchoredAtom0625 chi ∧
      Fin15AnchoredAtom0911 chi)) ∨
      ((Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom0470 chi) ∨
      (Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom0478 chi)))) ∨
      ((((Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom0505 chi) ∨
      (Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom0626 chi)) ∨
      ((Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom0912 chi) ∨
      (¬Fin15AnchoredAtom1913 chi ∧
      Fin15AnchoredAtom0470 chi ∧
      Fin15AnchoredAtom0478 chi ∧
      Fin15AnchoredAtom0505 chi ∧
      Fin15AnchoredAtom0626 chi ∧
      Fin15AnchoredAtom0912 chi))) ∨
      (((Fin15AnchoredAtom1914 chi ∧
      ¬Fin15AnchoredAtom0471 chi) ∨
      (Fin15AnchoredAtom1914 chi ∧
      ¬Fin15AnchoredAtom0472 chi)) ∨
      ((Fin15AnchoredAtom1914 chi ∧
      ¬Fin15AnchoredAtom0506 chi) ∨
      (Fin15AnchoredAtom1914 chi ∧
      ¬Fin15AnchoredAtom0627 chi))))) ∨
      (((((Fin15AnchoredAtom1914 chi ∧
      ¬Fin15AnchoredAtom0913 chi) ∨
      (¬Fin15AnchoredAtom1914 chi ∧
      Fin15AnchoredAtom0471 chi ∧
      Fin15AnchoredAtom0472 chi ∧
      Fin15AnchoredAtom0506 chi ∧
      Fin15AnchoredAtom0627 chi ∧
      Fin15AnchoredAtom0913 chi)) ∨
      ((Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom0471 chi) ∨
      (Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom0473 chi))) ∨
      (((Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom0507 chi) ∨
      (Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom0628 chi)) ∨
      ((Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom0914 chi) ∨
      (¬Fin15AnchoredAtom1915 chi ∧
      Fin15AnchoredAtom0471 chi ∧
      Fin15AnchoredAtom0473 chi ∧
      Fin15AnchoredAtom0507 chi ∧
      Fin15AnchoredAtom0628 chi ∧
      Fin15AnchoredAtom0914 chi)))) ∨
      ((((Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom0471 chi) ∨
      (Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom0474 chi)) ∨
      ((Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom0508 chi) ∨
      (Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom0629 chi))) ∨
      (((Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom0915 chi) ∨
      (¬Fin15AnchoredAtom1916 chi ∧
      Fin15AnchoredAtom0471 chi ∧
      Fin15AnchoredAtom0474 chi ∧
      Fin15AnchoredAtom0508 chi ∧
      Fin15AnchoredAtom0629 chi ∧
      Fin15AnchoredAtom0915 chi)) ∨
      ((Fin15AnchoredAtom1917 chi ∧
      ¬Fin15AnchoredAtom0471 chi) ∨
      (Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom0471 chi)))))))))) := by
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
                exact fin15Anchored_clause15649 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15650 chi hbad
                ·
                  exact fin15Anchored_clause15651 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15652 chi hbad
                ·
                  exact fin15Anchored_clause15653 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15654 chi hbad
                ·
                  exact fin15Anchored_clause15655 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15656 chi hbad
                ·
                  exact fin15Anchored_clause15657 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15658 chi hbad
                ·
                  exact fin15Anchored_clause15659 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15660 chi hbad
                ·
                  exact fin15Anchored_clause15661 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15662 chi hbad
                ·
                  exact fin15Anchored_clause15663 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15664 chi hbad
                ·
                  exact fin15Anchored_clause15665 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15666 chi hbad
                ·
                  exact fin15Anchored_clause15667 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15668 chi hbad
                ·
                  exact fin15Anchored_clause15669 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15670 chi hbad
                ·
                  exact fin15Anchored_clause15671 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15672 chi hbad
                ·
                  exact fin15Anchored_clause15673 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15674 chi hbad
                ·
                  exact fin15Anchored_clause15675 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15676 chi hbad
                ·
                  exact fin15Anchored_clause15677 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15678 chi hbad
                ·
                  exact fin15Anchored_clause15679 chi hbad
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
                  exact fin15Anchored_clause15680 chi hbad
                ·
                  exact fin15Anchored_clause15681 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15682 chi hbad
                ·
                  exact fin15Anchored_clause15683 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15684 chi hbad
                ·
                  exact fin15Anchored_clause15685 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15686 chi hbad
                ·
                  exact fin15Anchored_clause15687 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15688 chi hbad
                ·
                  exact fin15Anchored_clause15689 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15690 chi hbad
                ·
                  exact fin15Anchored_clause15691 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15692 chi hbad
                ·
                  exact fin15Anchored_clause15693 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15694 chi hbad
                ·
                  exact fin15Anchored_clause15695 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15696 chi hbad
                ·
                  exact fin15Anchored_clause15697 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15698 chi hbad
                ·
                  exact fin15Anchored_clause15699 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15700 chi hbad
                ·
                  exact fin15Anchored_clause15701 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15702 chi hbad
                ·
                  exact fin15Anchored_clause15703 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15704 chi hbad
                ·
                  exact fin15Anchored_clause15705 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15706 chi hbad
                ·
                  exact fin15Anchored_clause15707 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15708 chi hbad
                ·
                  exact fin15Anchored_clause15709 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15710 chi hbad
                ·
                  exact fin15Anchored_clause15711 chi hbad
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
                exact fin15Anchored_clause15712 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15713 chi hbad
                ·
                  exact fin15Anchored_clause15714 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15715 chi hbad
                ·
                  exact fin15Anchored_clause15716 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15717 chi hbad
                ·
                  exact fin15Anchored_clause15718 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15719 chi hbad
                ·
                  exact fin15Anchored_clause15720 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15721 chi hbad
                ·
                  exact fin15Anchored_clause15722 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15723 chi hbad
                ·
                  exact fin15Anchored_clause15724 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15725 chi hbad
                ·
                  exact fin15Anchored_clause15726 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15727 chi hbad
                ·
                  exact fin15Anchored_clause15728 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15729 chi hbad
                ·
                  exact fin15Anchored_clause15730 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15731 chi hbad
                ·
                  exact fin15Anchored_clause15732 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15733 chi hbad
                ·
                  exact fin15Anchored_clause15734 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15735 chi hbad
                ·
                  exact fin15Anchored_clause15736 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15737 chi hbad
                ·
                  exact fin15Anchored_clause15738 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15739 chi hbad
                ·
                  exact fin15Anchored_clause15740 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15741 chi hbad
                ·
                  exact fin15Anchored_clause15742 chi hbad
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
                  exact fin15Anchored_clause15743 chi hbad
                ·
                  exact fin15Anchored_clause15744 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15745 chi hbad
                ·
                  exact fin15Anchored_clause15746 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15747 chi hbad
                ·
                  exact fin15Anchored_clause15748 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15749 chi hbad
                ·
                  exact fin15Anchored_clause15750 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15751 chi hbad
                ·
                  exact fin15Anchored_clause15752 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15753 chi hbad
                ·
                  exact fin15Anchored_clause15754 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15755 chi hbad
                ·
                  exact fin15Anchored_clause15756 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15757 chi hbad
                ·
                  exact fin15Anchored_clause15758 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15759 chi hbad
                ·
                  exact fin15Anchored_clause15760 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15761 chi hbad
                ·
                  exact fin15Anchored_clause15762 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15763 chi hbad
                ·
                  exact fin15Anchored_clause15764 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15765 chi hbad
                ·
                  exact fin15Anchored_clause15766 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15767 chi hbad
                ·
                  exact fin15Anchored_clause15768 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15769 chi hbad
                ·
                  exact fin15Anchored_clause15770 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15771 chi hbad
                ·
                  exact fin15Anchored_clause15772 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15773 chi hbad
                ·
                  exact fin15Anchored_clause15774 chi hbad
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
                exact fin15Anchored_clause15775 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15776 chi hbad
                ·
                  exact fin15Anchored_clause15777 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15778 chi hbad
                ·
                  exact fin15Anchored_clause15779 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15780 chi hbad
                ·
                  exact fin15Anchored_clause15781 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15782 chi hbad
                ·
                  exact fin15Anchored_clause15783 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15784 chi hbad
                ·
                  exact fin15Anchored_clause15785 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15786 chi hbad
                ·
                  exact fin15Anchored_clause15787 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15788 chi hbad
                ·
                  exact fin15Anchored_clause15789 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15790 chi hbad
                ·
                  exact fin15Anchored_clause15791 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15792 chi hbad
                ·
                  exact fin15Anchored_clause15793 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15794 chi hbad
                ·
                  exact fin15Anchored_clause15795 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15796 chi hbad
                ·
                  exact fin15Anchored_clause15797 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15798 chi hbad
                ·
                  exact fin15Anchored_clause15799 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15800 chi hbad
                ·
                  exact fin15Anchored_clause15801 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15802 chi hbad
                ·
                  exact fin15Anchored_clause15803 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15804 chi hbad
                ·
                  exact fin15Anchored_clause15805 chi hbad
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
                  exact fin15Anchored_clause15806 chi hbad
                ·
                  exact fin15Anchored_clause15807 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15808 chi hbad
                ·
                  exact fin15Anchored_clause15809 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15810 chi hbad
                ·
                  exact fin15Anchored_clause15811 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15812 chi hbad
                ·
                  exact fin15Anchored_clause15813 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15814 chi hbad
                ·
                  exact fin15Anchored_clause15815 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15816 chi hbad
                ·
                  exact fin15Anchored_clause15817 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15818 chi hbad
                ·
                  exact fin15Anchored_clause15819 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15820 chi hbad
                ·
                  exact fin15Anchored_clause15821 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15822 chi hbad
                ·
                  exact fin15Anchored_clause15823 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15824 chi hbad
                ·
                  exact fin15Anchored_clause15825 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15826 chi hbad
                ·
                  exact fin15Anchored_clause15827 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15828 chi hbad
                ·
                  exact fin15Anchored_clause15829 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15830 chi hbad
                ·
                  exact fin15Anchored_clause15831 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15832 chi hbad
                ·
                  exact fin15Anchored_clause15833 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15834 chi hbad
                ·
                  exact fin15Anchored_clause15835 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15836 chi hbad
                ·
                  exact fin15Anchored_clause15837 chi hbad
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
                exact fin15Anchored_clause15838 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15839 chi hbad
                ·
                  exact fin15Anchored_clause15840 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15841 chi hbad
                ·
                  exact fin15Anchored_clause15842 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15843 chi hbad
                ·
                  exact fin15Anchored_clause15844 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15845 chi hbad
                ·
                  exact fin15Anchored_clause15846 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15847 chi hbad
                ·
                  exact fin15Anchored_clause15848 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15849 chi hbad
                ·
                  exact fin15Anchored_clause15850 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15851 chi hbad
                ·
                  exact fin15Anchored_clause15852 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15853 chi hbad
                ·
                  exact fin15Anchored_clause15854 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15855 chi hbad
                ·
                  exact fin15Anchored_clause15856 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15857 chi hbad
                ·
                  exact fin15Anchored_clause15858 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15859 chi hbad
                ·
                  exact fin15Anchored_clause15860 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15861 chi hbad
                ·
                  exact fin15Anchored_clause15862 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15863 chi hbad
                ·
                  exact fin15Anchored_clause15864 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15865 chi hbad
                ·
                  exact fin15Anchored_clause15866 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15867 chi hbad
                ·
                  exact fin15Anchored_clause15868 chi hbad
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
                  exact fin15Anchored_clause15869 chi hbad
                ·
                  exact fin15Anchored_clause15870 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15871 chi hbad
                ·
                  exact fin15Anchored_clause15872 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15873 chi hbad
                ·
                  exact fin15Anchored_clause15874 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15875 chi hbad
                ·
                  exact fin15Anchored_clause15876 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15877 chi hbad
                ·
                  exact fin15Anchored_clause15878 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15879 chi hbad
                ·
                  exact fin15Anchored_clause15880 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15881 chi hbad
                ·
                  exact fin15Anchored_clause15882 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15883 chi hbad
                ·
                  exact fin15Anchored_clause15884 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15885 chi hbad
                ·
                  exact fin15Anchored_clause15886 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15887 chi hbad
                ·
                  exact fin15Anchored_clause15888 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15889 chi hbad
                ·
                  exact fin15Anchored_clause15890 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15891 chi hbad
                ·
                  exact fin15Anchored_clause15892 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15893 chi hbad
                ·
                  exact fin15Anchored_clause15894 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15895 chi hbad
                ·
                  exact fin15Anchored_clause15896 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15897 chi hbad
                ·
                  exact fin15Anchored_clause15898 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15899 chi hbad
                ·
                  exact fin15Anchored_clause15900 chi hbad

end ErdosSzekeres

end
