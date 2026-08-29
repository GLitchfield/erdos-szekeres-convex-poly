module

public import ErdosSzekeres.SynchronizedFiveFanFin11AltDepth2SemanticBase

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Stable original semantic atoms, segment 008. -/

def SynchronizedFiveFanFin11OriginalAtom0473 (chi : TripleColoring 11) : Prop :=
  Fin11AltDepth2StrongQuad
    chi 4 6 7 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11OriginalAtom0474 (chi : TripleColoring 11) : Prop :=
  Fin11AltDepth2StrongQuad
    chi 4 6 8 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11OriginalAtom0475 (chi : TripleColoring 11) : Prop :=
  Fin11AltDepth2StrongQuad
    chi 4 6 8 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11OriginalAtom0476 (chi : TripleColoring 11) : Prop :=
  Fin11AltDepth2StrongQuad
    chi 4 6 9 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11OriginalAtom0477 (chi : TripleColoring 11) : Prop :=
  Fin11AltDepth2StrongQuad
    chi 4 7 8 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11OriginalAtom0478 (chi : TripleColoring 11) : Prop :=
  Fin11AltDepth2StrongQuad
    chi 4 7 8 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11OriginalAtom0479 (chi : TripleColoring 11) : Prop :=
  Fin11AltDepth2StrongQuad
    chi 4 7 9 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11OriginalAtom0480 (chi : TripleColoring 11) : Prop :=
  Fin11AltDepth2StrongQuad
    chi 4 8 9 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11OriginalAtom0481 (chi : TripleColoring 11) : Prop :=
  Fin11AltDepth2StrongQuad
    chi 5 6 7 8 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11OriginalAtom0482 (chi : TripleColoring 11) : Prop :=
  Fin11AltDepth2StrongQuad
    chi 5 6 7 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11OriginalAtom0483 (chi : TripleColoring 11) : Prop :=
  Fin11AltDepth2StrongQuad
    chi 5 6 7 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11OriginalAtom0484 (chi : TripleColoring 11) : Prop :=
  Fin11AltDepth2StrongQuad
    chi 5 6 8 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11OriginalAtom0485 (chi : TripleColoring 11) : Prop :=
  Fin11AltDepth2StrongQuad
    chi 5 6 8 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11OriginalAtom0486 (chi : TripleColoring 11) : Prop :=
  Fin11AltDepth2StrongQuad
    chi 5 6 9 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11OriginalAtom0487 (chi : TripleColoring 11) : Prop :=
  Fin11AltDepth2StrongQuad
    chi 5 7 8 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11OriginalAtom0488 (chi : TripleColoring 11) : Prop :=
  Fin11AltDepth2StrongQuad
    chi 5 7 8 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11OriginalAtom0489 (chi : TripleColoring 11) : Prop :=
  Fin11AltDepth2StrongQuad
    chi 5 7 9 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11OriginalAtom0490 (chi : TripleColoring 11) : Prop :=
  Fin11AltDepth2StrongQuad
    chi 5 8 9 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11OriginalAtom0491 (chi : TripleColoring 11) : Prop :=
  Fin11AltDepth2StrongQuad
    chi 6 7 8 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11OriginalAtom0492 (chi : TripleColoring 11) : Prop :=
  Fin11AltDepth2StrongQuad
    chi 6 7 8 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11OriginalAtom0493 (chi : TripleColoring 11) : Prop :=
  Fin11AltDepth2StrongQuad
    chi 6 7 9 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11OriginalAtom0494 (chi : TripleColoring 11) : Prop :=
  Fin11AltDepth2StrongQuad
    chi 6 8 9 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11OriginalAtom0495 (chi : TripleColoring 11) : Prop :=
  Fin11AltDepth2StrongQuad
    chi 7 8 9 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11OriginalAtom0496 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 3, 4}

def SynchronizedFiveFanFin11OriginalAtom0497 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 3, 5}

def SynchronizedFiveFanFin11OriginalAtom0498 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 3, 6}

def SynchronizedFiveFanFin11OriginalAtom0499 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 3, 7}

def SynchronizedFiveFanFin11OriginalAtom0500 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 3, 8}

def SynchronizedFiveFanFin11OriginalAtom0501 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 3, 9}

def SynchronizedFiveFanFin11OriginalAtom0502 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 3, 10}

def SynchronizedFiveFanFin11OriginalAtom0503 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 4, 5}

def SynchronizedFiveFanFin11OriginalAtom0504 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 4, 6}

def SynchronizedFiveFanFin11OriginalAtom0505 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 4, 7}

def SynchronizedFiveFanFin11OriginalAtom0506 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 4, 8}

def SynchronizedFiveFanFin11OriginalAtom0507 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 4, 9}

def SynchronizedFiveFanFin11OriginalAtom0508 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 4, 10}

def SynchronizedFiveFanFin11OriginalAtom0509 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 5, 6}

def SynchronizedFiveFanFin11OriginalAtom0510 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 5, 7}

def SynchronizedFiveFanFin11OriginalAtom0511 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 5, 8}

def SynchronizedFiveFanFin11OriginalAtom0512 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 5, 9}

def SynchronizedFiveFanFin11OriginalAtom0513 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 5, 10}

def SynchronizedFiveFanFin11OriginalAtom0514 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 6, 7}

def SynchronizedFiveFanFin11OriginalAtom0515 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 6, 8}

def SynchronizedFiveFanFin11OriginalAtom0516 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 6, 9}

def SynchronizedFiveFanFin11OriginalAtom0517 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 6, 10}

def SynchronizedFiveFanFin11OriginalAtom0518 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom0519 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom0520 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom0521 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom0522 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom0523 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom0524 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 4, 5}

def SynchronizedFiveFanFin11OriginalAtom0525 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 4, 6}

def SynchronizedFiveFanFin11OriginalAtom0526 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 4, 7}

def SynchronizedFiveFanFin11OriginalAtom0527 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 4, 8}

def SynchronizedFiveFanFin11OriginalAtom0528 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 4, 9}

def SynchronizedFiveFanFin11OriginalAtom0529 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 4, 10}

def SynchronizedFiveFanFin11OriginalAtom0530 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 5, 6}

def SynchronizedFiveFanFin11OriginalAtom0531 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 5, 7}

end ErdosSzekeres

end
