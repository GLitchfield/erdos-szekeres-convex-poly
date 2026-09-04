module

public import ErdosSzekeres.Fin15AnchoredClauseChunk124
public import ErdosSzekeres.Fin15AnchoredClauseChunk125
public import ErdosSzekeres.Fin15AnchoredClauseChunk126

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 063. -/

theorem fin15Anchored_rejectSemanticSegment063
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom0476 chi) ∨
      ((Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom0510 chi) ∨
      (Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom0631 chi))) ∨
      (((Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom0917 chi) ∨
      (¬Fin15AnchoredAtom1918 chi ∧
      Fin15AnchoredAtom0471 chi ∧
      Fin15AnchoredAtom0476 chi ∧
      Fin15AnchoredAtom0510 chi ∧
      Fin15AnchoredAtom0631 chi ∧
      Fin15AnchoredAtom0917 chi)) ∨
      ((Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom0471 chi) ∨
      (Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom0477 chi)))) ∨
      ((((Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom0511 chi) ∨
      (Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom0632 chi)) ∨
      ((Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom0918 chi) ∨
      (¬Fin15AnchoredAtom1919 chi ∧
      Fin15AnchoredAtom0471 chi ∧
      Fin15AnchoredAtom0477 chi ∧
      Fin15AnchoredAtom0511 chi ∧
      Fin15AnchoredAtom0632 chi ∧
      Fin15AnchoredAtom0918 chi))) ∨
      (((Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom0471 chi) ∨
      (Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom0478 chi)) ∨
      ((Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom0512 chi) ∨
      (Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom0633 chi))))) ∨
      (((((Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom0919 chi) ∨
      (¬Fin15AnchoredAtom1920 chi ∧
      Fin15AnchoredAtom0471 chi ∧
      Fin15AnchoredAtom0478 chi ∧
      Fin15AnchoredAtom0512 chi ∧
      Fin15AnchoredAtom0633 chi ∧
      Fin15AnchoredAtom0919 chi)) ∨
      ((Fin15AnchoredAtom1921 chi ∧
      ¬Fin15AnchoredAtom0472 chi) ∨
      (Fin15AnchoredAtom1921 chi ∧
      ¬Fin15AnchoredAtom0473 chi))) ∨
      (((Fin15AnchoredAtom1921 chi ∧
      ¬Fin15AnchoredAtom0513 chi) ∨
      (Fin15AnchoredAtom1921 chi ∧
      ¬Fin15AnchoredAtom0634 chi)) ∨
      ((Fin15AnchoredAtom1921 chi ∧
      ¬Fin15AnchoredAtom0920 chi) ∨
      (¬Fin15AnchoredAtom1921 chi ∧
      Fin15AnchoredAtom0472 chi ∧
      Fin15AnchoredAtom0473 chi ∧
      Fin15AnchoredAtom0513 chi ∧
      Fin15AnchoredAtom0634 chi ∧
      Fin15AnchoredAtom0920 chi)))) ∨
      ((((Fin15AnchoredAtom1922 chi ∧
      ¬Fin15AnchoredAtom0472 chi) ∨
      (Fin15AnchoredAtom1922 chi ∧
      ¬Fin15AnchoredAtom0474 chi)) ∨
      ((Fin15AnchoredAtom1922 chi ∧
      ¬Fin15AnchoredAtom0514 chi) ∨
      (Fin15AnchoredAtom1922 chi ∧
      ¬Fin15AnchoredAtom0635 chi))) ∨
      (((Fin15AnchoredAtom1922 chi ∧
      ¬Fin15AnchoredAtom0921 chi) ∨
      (¬Fin15AnchoredAtom1922 chi ∧
      Fin15AnchoredAtom0472 chi ∧
      Fin15AnchoredAtom0474 chi ∧
      Fin15AnchoredAtom0514 chi ∧
      Fin15AnchoredAtom0635 chi ∧
      Fin15AnchoredAtom0921 chi)) ∨
      ((Fin15AnchoredAtom1924 chi ∧
      ¬Fin15AnchoredAtom0472 chi) ∨
      (Fin15AnchoredAtom1924 chi ∧
      ¬Fin15AnchoredAtom0476 chi)))))) ∨
      ((((((Fin15AnchoredAtom1924 chi ∧
      ¬Fin15AnchoredAtom0516 chi) ∨
      (Fin15AnchoredAtom1924 chi ∧
      ¬Fin15AnchoredAtom0637 chi)) ∨
      ((Fin15AnchoredAtom1924 chi ∧
      ¬Fin15AnchoredAtom0923 chi) ∨
      (¬Fin15AnchoredAtom1924 chi ∧
      Fin15AnchoredAtom0472 chi ∧
      Fin15AnchoredAtom0476 chi ∧
      Fin15AnchoredAtom0516 chi ∧
      Fin15AnchoredAtom0637 chi ∧
      Fin15AnchoredAtom0923 chi))) ∨
      (((Fin15AnchoredAtom1925 chi ∧
      ¬Fin15AnchoredAtom0472 chi) ∨
      (Fin15AnchoredAtom1925 chi ∧
      ¬Fin15AnchoredAtom0477 chi)) ∨
      ((Fin15AnchoredAtom1925 chi ∧
      ¬Fin15AnchoredAtom0517 chi) ∨
      (Fin15AnchoredAtom1925 chi ∧
      ¬Fin15AnchoredAtom0638 chi)))) ∨
      ((((Fin15AnchoredAtom1925 chi ∧
      ¬Fin15AnchoredAtom0924 chi) ∨
      (¬Fin15AnchoredAtom1925 chi ∧
      Fin15AnchoredAtom0472 chi ∧
      Fin15AnchoredAtom0477 chi ∧
      Fin15AnchoredAtom0517 chi ∧
      Fin15AnchoredAtom0638 chi ∧
      Fin15AnchoredAtom0924 chi)) ∨
      ((Fin15AnchoredAtom1926 chi ∧
      ¬Fin15AnchoredAtom0472 chi) ∨
      (Fin15AnchoredAtom1926 chi ∧
      ¬Fin15AnchoredAtom0478 chi))) ∨
      (((Fin15AnchoredAtom1926 chi ∧
      ¬Fin15AnchoredAtom0518 chi) ∨
      (Fin15AnchoredAtom1926 chi ∧
      ¬Fin15AnchoredAtom0639 chi)) ∨
      ((Fin15AnchoredAtom1926 chi ∧
      ¬Fin15AnchoredAtom0925 chi) ∨
      (¬Fin15AnchoredAtom1926 chi ∧
      Fin15AnchoredAtom0472 chi ∧
      Fin15AnchoredAtom0478 chi ∧
      Fin15AnchoredAtom0518 chi ∧
      Fin15AnchoredAtom0639 chi ∧
      Fin15AnchoredAtom0925 chi))))) ∨
      (((((Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom0473 chi) ∨
      (Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom0474 chi)) ∨
      ((Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom0519 chi) ∨
      (Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom0640 chi))) ∨
      (((Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom0926 chi) ∨
      (¬Fin15AnchoredAtom1927 chi ∧
      Fin15AnchoredAtom0473 chi ∧
      Fin15AnchoredAtom0474 chi ∧
      Fin15AnchoredAtom0519 chi ∧
      Fin15AnchoredAtom0640 chi ∧
      Fin15AnchoredAtom0926 chi)) ∨
      ((Fin15AnchoredAtom1928 chi ∧
      ¬Fin15AnchoredAtom0473 chi) ∨
      (Fin15AnchoredAtom1928 chi ∧
      ¬Fin15AnchoredAtom0475 chi)))) ∨
      ((((Fin15AnchoredAtom1928 chi ∧
      ¬Fin15AnchoredAtom0520 chi) ∨
      (Fin15AnchoredAtom1928 chi ∧
      ¬Fin15AnchoredAtom0641 chi)) ∨
      ((¬Fin15AnchoredAtom1928 chi ∧
      Fin15AnchoredAtom0473 chi ∧
      Fin15AnchoredAtom0475 chi ∧
      Fin15AnchoredAtom0520 chi ∧
      Fin15AnchoredAtom0641 chi ∧
      Fin15AnchoredAtom0927 chi) ∨
      (Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom0473 chi))) ∨
      (((Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom0476 chi) ∨
      (Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom0521 chi)) ∨
      ((Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom0642 chi) ∨
      (Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom0928 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom1929 chi ∧
      Fin15AnchoredAtom0473 chi ∧
      Fin15AnchoredAtom0476 chi ∧
      Fin15AnchoredAtom0521 chi ∧
      Fin15AnchoredAtom0642 chi ∧
      Fin15AnchoredAtom0928 chi) ∨
      ((Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom0473 chi) ∨
      (Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom0477 chi))) ∨
      (((Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom0522 chi) ∨
      (Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom0643 chi)) ∨
      ((Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom0929 chi) ∨
      (¬Fin15AnchoredAtom1930 chi ∧
      Fin15AnchoredAtom0473 chi ∧
      Fin15AnchoredAtom0477 chi ∧
      Fin15AnchoredAtom0522 chi ∧
      Fin15AnchoredAtom0643 chi ∧
      Fin15AnchoredAtom0929 chi)))) ∨
      ((((Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom0473 chi) ∨
      (Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom0478 chi)) ∨
      ((Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom0523 chi) ∨
      (Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom0644 chi))) ∨
      (((Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom0930 chi) ∨
      (¬Fin15AnchoredAtom1931 chi ∧
      Fin15AnchoredAtom0473 chi ∧
      Fin15AnchoredAtom0478 chi ∧
      Fin15AnchoredAtom0523 chi ∧
      Fin15AnchoredAtom0644 chi ∧
      Fin15AnchoredAtom0930 chi)) ∨
      ((Fin15AnchoredAtom1932 chi ∧
      ¬Fin15AnchoredAtom0474 chi) ∨
      (Fin15AnchoredAtom1932 chi ∧
      ¬Fin15AnchoredAtom0475 chi))))) ∨
      (((((Fin15AnchoredAtom1932 chi ∧
      ¬Fin15AnchoredAtom0524 chi) ∨
      (Fin15AnchoredAtom1932 chi ∧
      ¬Fin15AnchoredAtom0645 chi)) ∨
      ((Fin15AnchoredAtom1932 chi ∧
      ¬Fin15AnchoredAtom0931 chi) ∨
      (¬Fin15AnchoredAtom1932 chi ∧
      Fin15AnchoredAtom0474 chi ∧
      Fin15AnchoredAtom0475 chi ∧
      Fin15AnchoredAtom0524 chi ∧
      Fin15AnchoredAtom0645 chi ∧
      Fin15AnchoredAtom0931 chi))) ∨
      (((Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom0474 chi) ∨
      (Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom0476 chi)) ∨
      ((Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom0525 chi) ∨
      (Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom0646 chi)))) ∨
      ((((Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom0932 chi) ∨
      (¬Fin15AnchoredAtom1933 chi ∧
      Fin15AnchoredAtom0474 chi ∧
      Fin15AnchoredAtom0476 chi ∧
      Fin15AnchoredAtom0525 chi ∧
      Fin15AnchoredAtom0646 chi ∧
      Fin15AnchoredAtom0932 chi)) ∨
      ((Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom0474 chi) ∨
      (Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom0477 chi))) ∨
      (((Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom0526 chi) ∨
      (Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom0647 chi)) ∨
      ((Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom0933 chi) ∨
      (¬Fin15AnchoredAtom1934 chi ∧
      Fin15AnchoredAtom0474 chi ∧
      Fin15AnchoredAtom0477 chi ∧
      Fin15AnchoredAtom0526 chi ∧
      Fin15AnchoredAtom0647 chi ∧
      Fin15AnchoredAtom0933 chi)))))) ∨
      ((((((Fin15AnchoredAtom1935 chi ∧
      ¬Fin15AnchoredAtom0474 chi) ∨
      (Fin15AnchoredAtom1935 chi ∧
      ¬Fin15AnchoredAtom0478 chi)) ∨
      ((Fin15AnchoredAtom1935 chi ∧
      ¬Fin15AnchoredAtom0527 chi) ∨
      (Fin15AnchoredAtom1935 chi ∧
      ¬Fin15AnchoredAtom0648 chi))) ∨
      (((Fin15AnchoredAtom1935 chi ∧
      ¬Fin15AnchoredAtom0934 chi) ∨
      (¬Fin15AnchoredAtom1935 chi ∧
      Fin15AnchoredAtom0474 chi ∧
      Fin15AnchoredAtom0478 chi ∧
      Fin15AnchoredAtom0527 chi ∧
      Fin15AnchoredAtom0648 chi ∧
      Fin15AnchoredAtom0934 chi)) ∨
      ((Fin15AnchoredAtom1936 chi ∧
      ¬Fin15AnchoredAtom0476 chi) ∨
      (Fin15AnchoredAtom1936 chi ∧
      ¬Fin15AnchoredAtom0528 chi)))) ∨
      ((((Fin15AnchoredAtom1936 chi ∧
      ¬Fin15AnchoredAtom0935 chi) ∨
      (¬Fin15AnchoredAtom1936 chi ∧
      Fin15AnchoredAtom0475 chi ∧
      Fin15AnchoredAtom0476 chi ∧
      Fin15AnchoredAtom0528 chi ∧
      Fin15AnchoredAtom0649 chi ∧
      Fin15AnchoredAtom0935 chi)) ∨
      ((Fin15AnchoredAtom1937 chi ∧
      ¬Fin15AnchoredAtom0475 chi) ∨
      (Fin15AnchoredAtom1937 chi ∧
      ¬Fin15AnchoredAtom0529 chi))) ∨
      (((Fin15AnchoredAtom1937 chi ∧
      ¬Fin15AnchoredAtom0650 chi) ∨
      (Fin15AnchoredAtom1937 chi ∧
      ¬Fin15AnchoredAtom0936 chi)) ∨
      ((¬Fin15AnchoredAtom1937 chi ∧
      Fin15AnchoredAtom0475 chi ∧
      Fin15AnchoredAtom0477 chi ∧
      Fin15AnchoredAtom0529 chi ∧
      Fin15AnchoredAtom0650 chi ∧
      Fin15AnchoredAtom0936 chi) ∨
      (Fin15AnchoredAtom1938 chi ∧
      ¬Fin15AnchoredAtom0475 chi))))) ∨
      (((((Fin15AnchoredAtom1938 chi ∧
      ¬Fin15AnchoredAtom0478 chi) ∨
      (Fin15AnchoredAtom1938 chi ∧
      ¬Fin15AnchoredAtom0530 chi)) ∨
      ((Fin15AnchoredAtom1938 chi ∧
      ¬Fin15AnchoredAtom0651 chi) ∨
      (Fin15AnchoredAtom1938 chi ∧
      ¬Fin15AnchoredAtom0937 chi))) ∨
      (((¬Fin15AnchoredAtom1938 chi ∧
      Fin15AnchoredAtom0475 chi ∧
      Fin15AnchoredAtom0478 chi ∧
      Fin15AnchoredAtom0530 chi ∧
      Fin15AnchoredAtom0651 chi ∧
      Fin15AnchoredAtom0937 chi) ∨
      (Fin15AnchoredAtom1939 chi ∧
      ¬Fin15AnchoredAtom0476 chi)) ∨
      ((Fin15AnchoredAtom1939 chi ∧
      ¬Fin15AnchoredAtom0477 chi) ∨
      (Fin15AnchoredAtom1939 chi ∧
      ¬Fin15AnchoredAtom0531 chi)))) ∨
      ((((Fin15AnchoredAtom1939 chi ∧
      ¬Fin15AnchoredAtom0652 chi) ∨
      (Fin15AnchoredAtom1939 chi ∧
      ¬Fin15AnchoredAtom0938 chi)) ∨
      ((¬Fin15AnchoredAtom1939 chi ∧
      Fin15AnchoredAtom0476 chi ∧
      Fin15AnchoredAtom0477 chi ∧
      Fin15AnchoredAtom0531 chi ∧
      Fin15AnchoredAtom0652 chi ∧
      Fin15AnchoredAtom0938 chi) ∨
      (Fin15AnchoredAtom1940 chi ∧
      ¬Fin15AnchoredAtom0476 chi))) ∨
      (((Fin15AnchoredAtom1940 chi ∧
      ¬Fin15AnchoredAtom0478 chi) ∨
      (Fin15AnchoredAtom1940 chi ∧
      ¬Fin15AnchoredAtom0532 chi)) ∨
      ((Fin15AnchoredAtom1940 chi ∧
      ¬Fin15AnchoredAtom0653 chi) ∨
      (Fin15AnchoredAtom1940 chi ∧
      ¬Fin15AnchoredAtom0939 chi)))))))) ∨
      (((((((¬Fin15AnchoredAtom1940 chi ∧
      Fin15AnchoredAtom0476 chi ∧
      Fin15AnchoredAtom0478 chi ∧
      Fin15AnchoredAtom0532 chi ∧
      Fin15AnchoredAtom0653 chi ∧
      Fin15AnchoredAtom0939 chi) ∨
      ((Fin15AnchoredAtom1941 chi ∧
      ¬Fin15AnchoredAtom0477 chi) ∨
      (Fin15AnchoredAtom1941 chi ∧
      ¬Fin15AnchoredAtom0478 chi))) ∨
      (((Fin15AnchoredAtom1941 chi ∧
      ¬Fin15AnchoredAtom0533 chi) ∨
      (Fin15AnchoredAtom1941 chi ∧
      ¬Fin15AnchoredAtom0654 chi)) ∨
      ((Fin15AnchoredAtom1941 chi ∧
      ¬Fin15AnchoredAtom0940 chi) ∨
      (¬Fin15AnchoredAtom1941 chi ∧
      Fin15AnchoredAtom0477 chi ∧
      Fin15AnchoredAtom0478 chi ∧
      Fin15AnchoredAtom0533 chi ∧
      Fin15AnchoredAtom0654 chi ∧
      Fin15AnchoredAtom0940 chi)))) ∨
      ((((Fin15AnchoredAtom1942 chi ∧
      ¬Fin15AnchoredAtom0479 chi) ∨
      (Fin15AnchoredAtom1942 chi ∧
      ¬Fin15AnchoredAtom0480 chi)) ∨
      ((Fin15AnchoredAtom1942 chi ∧
      ¬Fin15AnchoredAtom0489 chi) ∨
      (Fin15AnchoredAtom1942 chi ∧
      ¬Fin15AnchoredAtom0655 chi))) ∨
      (((Fin15AnchoredAtom1942 chi ∧
      ¬Fin15AnchoredAtom0941 chi) ∨
      (¬Fin15AnchoredAtom1942 chi ∧
      Fin15AnchoredAtom0479 chi ∧
      Fin15AnchoredAtom0480 chi ∧
      Fin15AnchoredAtom0489 chi ∧
      Fin15AnchoredAtom0655 chi ∧
      Fin15AnchoredAtom0941 chi)) ∨
      ((Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom0479 chi) ∨
      (Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom0481 chi))))) ∨
      (((((Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom0490 chi) ∨
      (Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom0656 chi)) ∨
      ((Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom0942 chi) ∨
      (¬Fin15AnchoredAtom1943 chi ∧
      Fin15AnchoredAtom0479 chi ∧
      Fin15AnchoredAtom0481 chi ∧
      Fin15AnchoredAtom0490 chi ∧
      Fin15AnchoredAtom0656 chi ∧
      Fin15AnchoredAtom0942 chi))) ∨
      (((Fin15AnchoredAtom1944 chi ∧
      ¬Fin15AnchoredAtom0479 chi) ∨
      (Fin15AnchoredAtom1944 chi ∧
      ¬Fin15AnchoredAtom0482 chi)) ∨
      ((Fin15AnchoredAtom1944 chi ∧
      ¬Fin15AnchoredAtom0657 chi) ∨
      (Fin15AnchoredAtom1944 chi ∧
      ¬Fin15AnchoredAtom0943 chi)))) ∨
      ((((¬Fin15AnchoredAtom1944 chi ∧
      Fin15AnchoredAtom0479 chi ∧
      Fin15AnchoredAtom0482 chi ∧
      Fin15AnchoredAtom0491 chi ∧
      Fin15AnchoredAtom0657 chi ∧
      Fin15AnchoredAtom0943 chi) ∨
      (Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom0479 chi)) ∨
      ((Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom0483 chi) ∨
      (Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom0492 chi))) ∨
      (((Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom0658 chi) ∨
      (Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom0944 chi)) ∨
      ((¬Fin15AnchoredAtom1945 chi ∧
      Fin15AnchoredAtom0479 chi ∧
      Fin15AnchoredAtom0483 chi ∧
      Fin15AnchoredAtom0492 chi ∧
      Fin15AnchoredAtom0658 chi ∧
      Fin15AnchoredAtom0944 chi) ∨
      (Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom0479 chi)))))) ∨
      ((((((Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom0484 chi) ∨
      (Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom0493 chi)) ∨
      ((Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom0659 chi) ∨
      (Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom0945 chi))) ∨
      (((¬Fin15AnchoredAtom1946 chi ∧
      Fin15AnchoredAtom0479 chi ∧
      Fin15AnchoredAtom0484 chi ∧
      Fin15AnchoredAtom0493 chi ∧
      Fin15AnchoredAtom0659 chi ∧
      Fin15AnchoredAtom0945 chi) ∨
      (Fin15AnchoredAtom1947 chi ∧
      ¬Fin15AnchoredAtom0479 chi)) ∨
      ((Fin15AnchoredAtom1947 chi ∧
      ¬Fin15AnchoredAtom0660 chi) ∨
      (Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom0479 chi)))) ∨
      ((((Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom0486 chi) ∨
      (Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom0495 chi)) ∨
      ((Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom0661 chi) ∨
      (Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom0947 chi))) ∨
      (((¬Fin15AnchoredAtom1948 chi ∧
      Fin15AnchoredAtom0479 chi ∧
      Fin15AnchoredAtom0486 chi ∧
      Fin15AnchoredAtom0495 chi ∧
      Fin15AnchoredAtom0661 chi ∧
      Fin15AnchoredAtom0947 chi) ∨
      (Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom0479 chi)) ∨
      ((Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom0487 chi) ∨
      (Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom0496 chi))))) ∨
      (((((Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom0662 chi) ∨
      (Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom0948 chi)) ∨
      ((¬Fin15AnchoredAtom1949 chi ∧
      Fin15AnchoredAtom0479 chi ∧
      Fin15AnchoredAtom0487 chi ∧
      Fin15AnchoredAtom0496 chi ∧
      Fin15AnchoredAtom0662 chi ∧
      Fin15AnchoredAtom0948 chi) ∨
      (Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom0479 chi))) ∨
      (((Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom0488 chi) ∨
      (Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom0497 chi)) ∨
      ((Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom0663 chi) ∨
      (Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom0949 chi)))) ∨
      ((((¬Fin15AnchoredAtom1950 chi ∧
      Fin15AnchoredAtom0479 chi ∧
      Fin15AnchoredAtom0488 chi ∧
      Fin15AnchoredAtom0497 chi ∧
      Fin15AnchoredAtom0663 chi ∧
      Fin15AnchoredAtom0949 chi) ∨
      (Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom0480 chi)) ∨
      ((Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom0481 chi) ∨
      (Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom0498 chi))) ∨
      (((Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom0664 chi) ∨
      (Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom0950 chi)) ∨
      ((¬Fin15AnchoredAtom1951 chi ∧
      Fin15AnchoredAtom0480 chi ∧
      Fin15AnchoredAtom0481 chi ∧
      Fin15AnchoredAtom0498 chi ∧
      Fin15AnchoredAtom0664 chi ∧
      Fin15AnchoredAtom0950 chi) ∨
      (Fin15AnchoredAtom1952 chi ∧
      ¬Fin15AnchoredAtom0480 chi))))))) ∨
      (((((((Fin15AnchoredAtom1952 chi ∧
      ¬Fin15AnchoredAtom0482 chi) ∨
      (Fin15AnchoredAtom1952 chi ∧
      ¬Fin15AnchoredAtom0665 chi)) ∨
      ((Fin15AnchoredAtom1952 chi ∧
      ¬Fin15AnchoredAtom0951 chi) ∨
      (¬Fin15AnchoredAtom1952 chi ∧
      Fin15AnchoredAtom0480 chi ∧
      Fin15AnchoredAtom0482 chi ∧
      Fin15AnchoredAtom0499 chi ∧
      Fin15AnchoredAtom0665 chi ∧
      Fin15AnchoredAtom0951 chi))) ∨
      (((Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom0480 chi) ∨
      (Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom0483 chi)) ∨
      ((Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom0500 chi) ∨
      (Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom0666 chi)))) ∨
      ((((Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom0952 chi) ∨
      (¬Fin15AnchoredAtom1953 chi ∧
      Fin15AnchoredAtom0480 chi ∧
      Fin15AnchoredAtom0483 chi ∧
      Fin15AnchoredAtom0500 chi ∧
      Fin15AnchoredAtom0666 chi ∧
      Fin15AnchoredAtom0952 chi)) ∨
      ((Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom0480 chi) ∨
      (Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom0484 chi))) ∨
      (((Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom0501 chi) ∨
      (Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom0667 chi)) ∨
      ((Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom0953 chi) ∨
      (¬Fin15AnchoredAtom1954 chi ∧
      Fin15AnchoredAtom0480 chi ∧
      Fin15AnchoredAtom0484 chi ∧
      Fin15AnchoredAtom0501 chi ∧
      Fin15AnchoredAtom0667 chi ∧
      Fin15AnchoredAtom0953 chi))))) ∨
      (((((Fin15AnchoredAtom1955 chi ∧
      ¬Fin15AnchoredAtom0480 chi) ∨
      (Fin15AnchoredAtom1955 chi ∧
      ¬Fin15AnchoredAtom0668 chi)) ∨
      ((Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom0480 chi) ∨
      (Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom0486 chi))) ∨
      (((Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom0503 chi) ∨
      (Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom0669 chi)) ∨
      ((Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom0955 chi) ∨
      (¬Fin15AnchoredAtom1956 chi ∧
      Fin15AnchoredAtom0480 chi ∧
      Fin15AnchoredAtom0486 chi ∧
      Fin15AnchoredAtom0503 chi ∧
      Fin15AnchoredAtom0669 chi ∧
      Fin15AnchoredAtom0955 chi)))) ∨
      ((((Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom0480 chi) ∨
      (Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom0487 chi)) ∨
      ((Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom0504 chi) ∨
      (Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom0670 chi))) ∨
      (((Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom0956 chi) ∨
      (¬Fin15AnchoredAtom1957 chi ∧
      Fin15AnchoredAtom0480 chi ∧
      Fin15AnchoredAtom0487 chi ∧
      Fin15AnchoredAtom0504 chi ∧
      Fin15AnchoredAtom0670 chi ∧
      Fin15AnchoredAtom0956 chi)) ∨
      ((Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom0480 chi) ∨
      (Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom0488 chi)))))) ∨
      ((((((Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom0505 chi) ∨
      (Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom0671 chi)) ∨
      ((Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom0957 chi) ∨
      (¬Fin15AnchoredAtom1958 chi ∧
      Fin15AnchoredAtom0480 chi ∧
      Fin15AnchoredAtom0488 chi ∧
      Fin15AnchoredAtom0505 chi ∧
      Fin15AnchoredAtom0671 chi ∧
      Fin15AnchoredAtom0957 chi))) ∨
      (((Fin15AnchoredAtom1959 chi ∧
      ¬Fin15AnchoredAtom0481 chi) ∨
      (Fin15AnchoredAtom1959 chi ∧
      ¬Fin15AnchoredAtom0482 chi)) ∨
      ((Fin15AnchoredAtom1959 chi ∧
      ¬Fin15AnchoredAtom0506 chi) ∨
      (Fin15AnchoredAtom1959 chi ∧
      ¬Fin15AnchoredAtom0672 chi)))) ∨
      ((((¬Fin15AnchoredAtom1959 chi ∧
      Fin15AnchoredAtom0481 chi ∧
      Fin15AnchoredAtom0482 chi ∧
      Fin15AnchoredAtom0506 chi ∧
      Fin15AnchoredAtom0672 chi ∧
      Fin15AnchoredAtom0958 chi) ∨
      (Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom0481 chi)) ∨
      ((Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom0483 chi) ∨
      (Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom0507 chi))) ∨
      (((Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom0673 chi) ∨
      (Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom0959 chi)) ∨
      ((¬Fin15AnchoredAtom1960 chi ∧
      Fin15AnchoredAtom0481 chi ∧
      Fin15AnchoredAtom0483 chi ∧
      Fin15AnchoredAtom0507 chi ∧
      Fin15AnchoredAtom0673 chi ∧
      Fin15AnchoredAtom0959 chi) ∨
      (Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom0481 chi))))) ∨
      (((((Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom0484 chi) ∨
      (Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom0508 chi)) ∨
      ((Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom0674 chi) ∨
      (Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom0960 chi))) ∨
      (((¬Fin15AnchoredAtom1961 chi ∧
      Fin15AnchoredAtom0481 chi ∧
      Fin15AnchoredAtom0484 chi ∧
      Fin15AnchoredAtom0508 chi ∧
      Fin15AnchoredAtom0674 chi ∧
      Fin15AnchoredAtom0960 chi) ∨
      (Fin15AnchoredAtom1962 chi ∧
      ¬Fin15AnchoredAtom0481 chi)) ∨
      ((Fin15AnchoredAtom1962 chi ∧
      ¬Fin15AnchoredAtom0675 chi) ∨
      (Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom0481 chi)))) ∨
      ((((Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom0486 chi) ∨
      (Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom0510 chi)) ∨
      ((Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom0676 chi) ∨
      (Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom0962 chi))) ∨
      (((¬Fin15AnchoredAtom1963 chi ∧
      Fin15AnchoredAtom0481 chi ∧
      Fin15AnchoredAtom0486 chi ∧
      Fin15AnchoredAtom0510 chi ∧
      Fin15AnchoredAtom0676 chi ∧
      Fin15AnchoredAtom0962 chi) ∨
      (Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom0481 chi)) ∨
      ((Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom0487 chi) ∨
      (Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom0511 chi)))))))))) := by
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
                exact fin15Anchored_clause15901 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15902 chi hbad
                ·
                  exact fin15Anchored_clause15903 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15904 chi hbad
                ·
                  exact fin15Anchored_clause15905 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15906 chi hbad
                ·
                  exact fin15Anchored_clause15907 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15908 chi hbad
                ·
                  exact fin15Anchored_clause15909 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15910 chi hbad
                ·
                  exact fin15Anchored_clause15911 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15912 chi hbad
                ·
                  exact fin15Anchored_clause15913 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15914 chi hbad
                ·
                  exact fin15Anchored_clause15915 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15916 chi hbad
                ·
                  exact fin15Anchored_clause15917 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15918 chi hbad
                ·
                  exact fin15Anchored_clause15919 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15920 chi hbad
                ·
                  exact fin15Anchored_clause15921 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15922 chi hbad
                ·
                  exact fin15Anchored_clause15923 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15924 chi hbad
                ·
                  exact fin15Anchored_clause15925 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15926 chi hbad
                ·
                  exact fin15Anchored_clause15927 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15928 chi hbad
                ·
                  exact fin15Anchored_clause15929 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15930 chi hbad
                ·
                  exact fin15Anchored_clause15931 chi hbad
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
                  exact fin15Anchored_clause15932 chi hbad
                ·
                  exact fin15Anchored_clause15933 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15934 chi hbad
                ·
                  exact fin15Anchored_clause15935 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15936 chi hbad
                ·
                  exact fin15Anchored_clause15937 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15938 chi hbad
                ·
                  exact fin15Anchored_clause15939 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15940 chi hbad
                ·
                  exact fin15Anchored_clause15941 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15942 chi hbad
                ·
                  exact fin15Anchored_clause15943 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15944 chi hbad
                ·
                  exact fin15Anchored_clause15945 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15946 chi hbad
                ·
                  exact fin15Anchored_clause15947 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15948 chi hbad
                ·
                  exact fin15Anchored_clause15949 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15950 chi hbad
                ·
                  exact fin15Anchored_clause15951 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15952 chi hbad
                ·
                  exact fin15Anchored_clause15953 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15954 chi hbad
                ·
                  exact fin15Anchored_clause15955 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15956 chi hbad
                ·
                  exact fin15Anchored_clause15957 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15958 chi hbad
                ·
                  exact fin15Anchored_clause15959 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15960 chi hbad
                ·
                  exact fin15Anchored_clause15961 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15962 chi hbad
                ·
                  exact fin15Anchored_clause15963 chi hbad
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
                exact fin15Anchored_clause15964 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15965 chi hbad
                ·
                  exact fin15Anchored_clause15966 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15967 chi hbad
                ·
                  exact fin15Anchored_clause15968 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15969 chi hbad
                ·
                  exact fin15Anchored_clause15970 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15971 chi hbad
                ·
                  exact fin15Anchored_clause15972 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15973 chi hbad
                ·
                  exact fin15Anchored_clause15974 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15975 chi hbad
                ·
                  exact fin15Anchored_clause15976 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15977 chi hbad
                ·
                  exact fin15Anchored_clause15978 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15979 chi hbad
                ·
                  exact fin15Anchored_clause15980 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15981 chi hbad
                ·
                  exact fin15Anchored_clause15982 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15983 chi hbad
                ·
                  exact fin15Anchored_clause15984 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15985 chi hbad
                ·
                  exact fin15Anchored_clause15986 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15987 chi hbad
                ·
                  exact fin15Anchored_clause15988 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15989 chi hbad
                ·
                  exact fin15Anchored_clause15990 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15991 chi hbad
                ·
                  exact fin15Anchored_clause15992 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15993 chi hbad
                ·
                  exact fin15Anchored_clause15994 chi hbad
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
                  exact fin15Anchored_clause15995 chi hbad
                ·
                  exact fin15Anchored_clause15996 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15997 chi hbad
                ·
                  exact fin15Anchored_clause15998 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15999 chi hbad
                ·
                  exact fin15Anchored_clause16000 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16001 chi hbad
                ·
                  exact fin15Anchored_clause16002 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16003 chi hbad
                ·
                  exact fin15Anchored_clause16004 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16005 chi hbad
                ·
                  exact fin15Anchored_clause16006 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16007 chi hbad
                ·
                  exact fin15Anchored_clause16008 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16009 chi hbad
                ·
                  exact fin15Anchored_clause16010 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16011 chi hbad
                ·
                  exact fin15Anchored_clause16012 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16013 chi hbad
                ·
                  exact fin15Anchored_clause16014 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16015 chi hbad
                ·
                  exact fin15Anchored_clause16016 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16017 chi hbad
                ·
                  exact fin15Anchored_clause16018 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16019 chi hbad
                ·
                  exact fin15Anchored_clause16020 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16021 chi hbad
                ·
                  exact fin15Anchored_clause16022 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16023 chi hbad
                ·
                  exact fin15Anchored_clause16024 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16025 chi hbad
                ·
                  exact fin15Anchored_clause16026 chi hbad
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
                exact fin15Anchored_clause16027 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16028 chi hbad
                ·
                  exact fin15Anchored_clause16029 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16030 chi hbad
                ·
                  exact fin15Anchored_clause16031 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16032 chi hbad
                ·
                  exact fin15Anchored_clause16033 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16034 chi hbad
                ·
                  exact fin15Anchored_clause16035 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16036 chi hbad
                ·
                  exact fin15Anchored_clause16037 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16038 chi hbad
                ·
                  exact fin15Anchored_clause16039 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16040 chi hbad
                ·
                  exact fin15Anchored_clause16041 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16042 chi hbad
                ·
                  exact fin15Anchored_clause16043 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16044 chi hbad
                ·
                  exact fin15Anchored_clause16045 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16046 chi hbad
                ·
                  exact fin15Anchored_clause16047 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16048 chi hbad
                ·
                  exact fin15Anchored_clause16049 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16050 chi hbad
                ·
                  exact fin15Anchored_clause16051 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16052 chi hbad
                ·
                  exact fin15Anchored_clause16053 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16054 chi hbad
                ·
                  exact fin15Anchored_clause16055 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16056 chi hbad
                ·
                  exact fin15Anchored_clause16057 chi hbad
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
                  exact fin15Anchored_clause16058 chi hbad
                ·
                  exact fin15Anchored_clause16059 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16060 chi hbad
                ·
                  exact fin15Anchored_clause16061 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16062 chi hbad
                ·
                  exact fin15Anchored_clause16063 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16064 chi hbad
                ·
                  exact fin15Anchored_clause16065 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16066 chi hbad
                ·
                  exact fin15Anchored_clause16067 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16068 chi hbad
                ·
                  exact fin15Anchored_clause16069 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16070 chi hbad
                ·
                  exact fin15Anchored_clause16071 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16072 chi hbad
                ·
                  exact fin15Anchored_clause16073 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16074 chi hbad
                ·
                  exact fin15Anchored_clause16075 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16076 chi hbad
                ·
                  exact fin15Anchored_clause16077 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16078 chi hbad
                ·
                  exact fin15Anchored_clause16079 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16080 chi hbad
                ·
                  exact fin15Anchored_clause16081 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16082 chi hbad
                ·
                  exact fin15Anchored_clause16083 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16084 chi hbad
                ·
                  exact fin15Anchored_clause16085 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16086 chi hbad
                ·
                  exact fin15Anchored_clause16087 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16088 chi hbad
                ·
                  exact fin15Anchored_clause16089 chi hbad
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
                  exact fin15Anchored_clause16090 chi hbad
                ·
                  exact fin15Anchored_clause16091 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16092 chi hbad
                ·
                  exact fin15Anchored_clause16093 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16094 chi hbad
                ·
                  exact fin15Anchored_clause16095 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16096 chi hbad
                ·
                  exact fin15Anchored_clause16097 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16098 chi hbad
                ·
                  exact fin15Anchored_clause16099 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16100 chi hbad
                ·
                  exact fin15Anchored_clause16101 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16102 chi hbad
                ·
                  exact fin15Anchored_clause16103 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16104 chi hbad
                ·
                  exact fin15Anchored_clause16105 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16106 chi hbad
                ·
                  exact fin15Anchored_clause16107 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16108 chi hbad
                ·
                  exact fin15Anchored_clause16109 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16110 chi hbad
                ·
                  exact fin15Anchored_clause16111 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16112 chi hbad
                ·
                  exact fin15Anchored_clause16113 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16114 chi hbad
                ·
                  exact fin15Anchored_clause16115 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16116 chi hbad
                ·
                  exact fin15Anchored_clause16117 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16118 chi hbad
                ·
                  exact fin15Anchored_clause16119 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16120 chi hbad
                ·
                  exact fin15Anchored_clause16121 chi hbad
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
                  exact fin15Anchored_clause16122 chi hbad
                ·
                  exact fin15Anchored_clause16123 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16124 chi hbad
                ·
                  exact fin15Anchored_clause16125 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16126 chi hbad
                ·
                  exact fin15Anchored_clause16127 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16128 chi hbad
                ·
                  exact fin15Anchored_clause16129 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16130 chi hbad
                ·
                  exact fin15Anchored_clause16131 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16132 chi hbad
                ·
                  exact fin15Anchored_clause16133 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16134 chi hbad
                ·
                  exact fin15Anchored_clause16135 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16136 chi hbad
                ·
                  exact fin15Anchored_clause16137 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16138 chi hbad
                ·
                  exact fin15Anchored_clause16139 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16140 chi hbad
                ·
                  exact fin15Anchored_clause16141 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16142 chi hbad
                ·
                  exact fin15Anchored_clause16143 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16144 chi hbad
                ·
                  exact fin15Anchored_clause16145 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16146 chi hbad
                ·
                  exact fin15Anchored_clause16147 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16148 chi hbad
                ·
                  exact fin15Anchored_clause16149 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16150 chi hbad
                ·
                  exact fin15Anchored_clause16151 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16152 chi hbad
                ·
                  exact fin15Anchored_clause16153 chi hbad

end ErdosSzekeres

end
