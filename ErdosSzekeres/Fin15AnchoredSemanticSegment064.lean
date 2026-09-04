module

public import ErdosSzekeres.Fin15AnchoredClauseChunk126
public import ErdosSzekeres.Fin15AnchoredClauseChunk127
public import ErdosSzekeres.Fin15AnchoredClauseChunk128

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 064. -/

theorem fin15Anchored_rejectSemanticSegment064
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom0677 chi) ∨
      ((Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom0963 chi) ∨
      (¬Fin15AnchoredAtom1964 chi ∧
      Fin15AnchoredAtom0481 chi ∧
      Fin15AnchoredAtom0487 chi ∧
      Fin15AnchoredAtom0511 chi ∧
      Fin15AnchoredAtom0677 chi ∧
      Fin15AnchoredAtom0963 chi))) ∨
      (((Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom0481 chi) ∨
      (Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom0488 chi)) ∨
      ((Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom0512 chi) ∨
      (Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom0678 chi)))) ∨
      ((((Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom0964 chi) ∨
      (¬Fin15AnchoredAtom1965 chi ∧
      Fin15AnchoredAtom0481 chi ∧
      Fin15AnchoredAtom0488 chi ∧
      Fin15AnchoredAtom0512 chi ∧
      Fin15AnchoredAtom0678 chi ∧
      Fin15AnchoredAtom0964 chi)) ∨
      ((Fin15AnchoredAtom1966 chi ∧
      ¬Fin15AnchoredAtom0482 chi) ∨
      (Fin15AnchoredAtom1966 chi ∧
      ¬Fin15AnchoredAtom0483 chi))) ∨
      (((Fin15AnchoredAtom1966 chi ∧
      ¬Fin15AnchoredAtom0513 chi) ∨
      (Fin15AnchoredAtom1966 chi ∧
      ¬Fin15AnchoredAtom0679 chi)) ∨
      ((Fin15AnchoredAtom1966 chi ∧
      ¬Fin15AnchoredAtom0965 chi) ∨
      (¬Fin15AnchoredAtom1966 chi ∧
      Fin15AnchoredAtom0482 chi ∧
      Fin15AnchoredAtom0483 chi ∧
      Fin15AnchoredAtom0513 chi ∧
      Fin15AnchoredAtom0679 chi ∧
      Fin15AnchoredAtom0965 chi))))) ∨
      (((((Fin15AnchoredAtom1967 chi ∧
      ¬Fin15AnchoredAtom0482 chi) ∨
      (Fin15AnchoredAtom1967 chi ∧
      ¬Fin15AnchoredAtom0484 chi)) ∨
      ((Fin15AnchoredAtom1967 chi ∧
      ¬Fin15AnchoredAtom0514 chi) ∨
      (Fin15AnchoredAtom1967 chi ∧
      ¬Fin15AnchoredAtom0680 chi))) ∨
      (((Fin15AnchoredAtom1967 chi ∧
      ¬Fin15AnchoredAtom0966 chi) ∨
      (¬Fin15AnchoredAtom1967 chi ∧
      Fin15AnchoredAtom0482 chi ∧
      Fin15AnchoredAtom0484 chi ∧
      Fin15AnchoredAtom0514 chi ∧
      Fin15AnchoredAtom0680 chi ∧
      Fin15AnchoredAtom0966 chi)) ∨
      ((Fin15AnchoredAtom1969 chi ∧
      ¬Fin15AnchoredAtom0482 chi) ∨
      (Fin15AnchoredAtom1969 chi ∧
      ¬Fin15AnchoredAtom0486 chi)))) ∨
      ((((Fin15AnchoredAtom1969 chi ∧
      ¬Fin15AnchoredAtom0682 chi) ∨
      (¬Fin15AnchoredAtom1969 chi ∧
      Fin15AnchoredAtom0482 chi ∧
      Fin15AnchoredAtom0486 chi ∧
      Fin15AnchoredAtom0516 chi ∧
      Fin15AnchoredAtom0682 chi ∧
      Fin15AnchoredAtom0968 chi)) ∨
      ((Fin15AnchoredAtom1970 chi ∧
      ¬Fin15AnchoredAtom0482 chi) ∨
      (Fin15AnchoredAtom1970 chi ∧
      ¬Fin15AnchoredAtom0487 chi))) ∨
      (((Fin15AnchoredAtom1970 chi ∧
      ¬Fin15AnchoredAtom0517 chi) ∨
      (Fin15AnchoredAtom1970 chi ∧
      ¬Fin15AnchoredAtom0683 chi)) ∨
      ((Fin15AnchoredAtom1970 chi ∧
      ¬Fin15AnchoredAtom0969 chi) ∨
      (¬Fin15AnchoredAtom1970 chi ∧
      Fin15AnchoredAtom0482 chi ∧
      Fin15AnchoredAtom0487 chi ∧
      Fin15AnchoredAtom0517 chi ∧
      Fin15AnchoredAtom0683 chi ∧
      Fin15AnchoredAtom0969 chi)))))) ∨
      ((((((Fin15AnchoredAtom1971 chi ∧
      ¬Fin15AnchoredAtom0482 chi) ∨
      (Fin15AnchoredAtom1971 chi ∧
      ¬Fin15AnchoredAtom0488 chi)) ∨
      ((Fin15AnchoredAtom1971 chi ∧
      ¬Fin15AnchoredAtom0518 chi) ∨
      (Fin15AnchoredAtom1971 chi ∧
      ¬Fin15AnchoredAtom0684 chi))) ∨
      (((Fin15AnchoredAtom1971 chi ∧
      ¬Fin15AnchoredAtom0970 chi) ∨
      (¬Fin15AnchoredAtom1971 chi ∧
      Fin15AnchoredAtom0482 chi ∧
      Fin15AnchoredAtom0488 chi ∧
      Fin15AnchoredAtom0518 chi ∧
      Fin15AnchoredAtom0684 chi ∧
      Fin15AnchoredAtom0970 chi)) ∨
      ((Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom0483 chi) ∨
      (Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom0484 chi)))) ∨
      ((((Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom0519 chi) ∨
      (Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom0685 chi)) ∨
      ((Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom0971 chi) ∨
      (¬Fin15AnchoredAtom1972 chi ∧
      Fin15AnchoredAtom0483 chi ∧
      Fin15AnchoredAtom0484 chi ∧
      Fin15AnchoredAtom0519 chi ∧
      Fin15AnchoredAtom0685 chi ∧
      Fin15AnchoredAtom0971 chi))) ∨
      (((Fin15AnchoredAtom1973 chi ∧
      ¬Fin15AnchoredAtom0483 chi) ∨
      (Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom0483 chi)) ∨
      ((Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom0486 chi) ∨
      (Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom0521 chi))))) ∨
      (((((Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom0687 chi) ∨
      (Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom0973 chi)) ∨
      ((¬Fin15AnchoredAtom1974 chi ∧
      Fin15AnchoredAtom0483 chi ∧
      Fin15AnchoredAtom0486 chi ∧
      Fin15AnchoredAtom0521 chi ∧
      Fin15AnchoredAtom0687 chi ∧
      Fin15AnchoredAtom0973 chi) ∨
      (Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom0483 chi))) ∨
      (((Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom0487 chi) ∨
      (Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom0522 chi)) ∨
      ((Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom0688 chi) ∨
      (Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom0974 chi)))) ∨
      ((((¬Fin15AnchoredAtom1975 chi ∧
      Fin15AnchoredAtom0483 chi ∧
      Fin15AnchoredAtom0487 chi ∧
      Fin15AnchoredAtom0522 chi ∧
      Fin15AnchoredAtom0688 chi ∧
      Fin15AnchoredAtom0974 chi) ∨
      (Fin15AnchoredAtom1976 chi ∧
      ¬Fin15AnchoredAtom0483 chi)) ∨
      ((Fin15AnchoredAtom1976 chi ∧
      ¬Fin15AnchoredAtom0488 chi) ∨
      (Fin15AnchoredAtom1976 chi ∧
      ¬Fin15AnchoredAtom0523 chi))) ∨
      (((Fin15AnchoredAtom1976 chi ∧
      ¬Fin15AnchoredAtom0689 chi) ∨
      (Fin15AnchoredAtom1976 chi ∧
      ¬Fin15AnchoredAtom0975 chi)) ∨
      ((¬Fin15AnchoredAtom1976 chi ∧
      Fin15AnchoredAtom0483 chi ∧
      Fin15AnchoredAtom0488 chi ∧
      Fin15AnchoredAtom0523 chi ∧
      Fin15AnchoredAtom0689 chi ∧
      Fin15AnchoredAtom0975 chi) ∨
      (Fin15AnchoredAtom1977 chi ∧
      ¬Fin15AnchoredAtom0484 chi))))))) ∨
      ((((((Fin15AnchoredAtom1977 chi ∧
      ¬Fin15AnchoredAtom0485 chi) ∨
      ((Fin15AnchoredAtom1977 chi ∧
      ¬Fin15AnchoredAtom0524 chi) ∨
      (Fin15AnchoredAtom1977 chi ∧
      ¬Fin15AnchoredAtom0690 chi))) ∨
      (((Fin15AnchoredAtom1978 chi ∧
      ¬Fin15AnchoredAtom0484 chi) ∨
      (Fin15AnchoredAtom1978 chi ∧
      ¬Fin15AnchoredAtom0486 chi)) ∨
      ((Fin15AnchoredAtom1978 chi ∧
      ¬Fin15AnchoredAtom0525 chi) ∨
      (Fin15AnchoredAtom1978 chi ∧
      ¬Fin15AnchoredAtom0691 chi)))) ∨
      ((((Fin15AnchoredAtom1978 chi ∧
      ¬Fin15AnchoredAtom0977 chi) ∨
      (¬Fin15AnchoredAtom1978 chi ∧
      Fin15AnchoredAtom0484 chi ∧
      Fin15AnchoredAtom0486 chi ∧
      Fin15AnchoredAtom0525 chi ∧
      Fin15AnchoredAtom0691 chi ∧
      Fin15AnchoredAtom0977 chi)) ∨
      ((Fin15AnchoredAtom1979 chi ∧
      ¬Fin15AnchoredAtom0484 chi) ∨
      (Fin15AnchoredAtom1979 chi ∧
      ¬Fin15AnchoredAtom0487 chi))) ∨
      (((Fin15AnchoredAtom1979 chi ∧
      ¬Fin15AnchoredAtom0526 chi) ∨
      (Fin15AnchoredAtom1979 chi ∧
      ¬Fin15AnchoredAtom0692 chi)) ∨
      ((Fin15AnchoredAtom1979 chi ∧
      ¬Fin15AnchoredAtom0978 chi) ∨
      (¬Fin15AnchoredAtom1979 chi ∧
      Fin15AnchoredAtom0484 chi ∧
      Fin15AnchoredAtom0487 chi ∧
      Fin15AnchoredAtom0526 chi ∧
      Fin15AnchoredAtom0692 chi ∧
      Fin15AnchoredAtom0978 chi))))) ∨
      (((((Fin15AnchoredAtom1980 chi ∧
      ¬Fin15AnchoredAtom0484 chi) ∨
      (Fin15AnchoredAtom1980 chi ∧
      ¬Fin15AnchoredAtom0488 chi)) ∨
      ((Fin15AnchoredAtom1980 chi ∧
      ¬Fin15AnchoredAtom0527 chi) ∨
      (Fin15AnchoredAtom1980 chi ∧
      ¬Fin15AnchoredAtom0693 chi))) ∨
      (((Fin15AnchoredAtom1980 chi ∧
      ¬Fin15AnchoredAtom0979 chi) ∨
      (¬Fin15AnchoredAtom1980 chi ∧
      Fin15AnchoredAtom0484 chi ∧
      Fin15AnchoredAtom0488 chi ∧
      Fin15AnchoredAtom0527 chi ∧
      Fin15AnchoredAtom0693 chi ∧
      Fin15AnchoredAtom0979 chi)) ∨
      ((Fin15AnchoredAtom1981 chi ∧
      ¬Fin15AnchoredAtom0486 chi) ∨
      (Fin15AnchoredAtom1981 chi ∧
      ¬Fin15AnchoredAtom0694 chi)))) ∨
      ((((Fin15AnchoredAtom1981 chi ∧
      ¬Fin15AnchoredAtom0980 chi) ∨
      (¬Fin15AnchoredAtom1981 chi ∧
      Fin15AnchoredAtom0485 chi ∧
      Fin15AnchoredAtom0486 chi ∧
      Fin15AnchoredAtom0528 chi ∧
      Fin15AnchoredAtom0694 chi ∧
      Fin15AnchoredAtom0980 chi)) ∨
      ((Fin15AnchoredAtom1982 chi ∧
      ¬Fin15AnchoredAtom0485 chi) ∨
      (Fin15AnchoredAtom1982 chi ∧
      ¬Fin15AnchoredAtom0487 chi))) ∨
      (((¬Fin15AnchoredAtom1982 chi ∧
      Fin15AnchoredAtom0485 chi ∧
      Fin15AnchoredAtom0487 chi ∧
      Fin15AnchoredAtom0529 chi ∧
      Fin15AnchoredAtom0695 chi ∧
      Fin15AnchoredAtom0981 chi) ∨
      (Fin15AnchoredAtom1983 chi ∧
      ¬Fin15AnchoredAtom0488 chi)) ∨
      ((Fin15AnchoredAtom1984 chi ∧
      ¬Fin15AnchoredAtom0486 chi) ∨
      (Fin15AnchoredAtom1984 chi ∧
      ¬Fin15AnchoredAtom0487 chi)))))) ∨
      ((((((Fin15AnchoredAtom1984 chi ∧
      ¬Fin15AnchoredAtom0531 chi) ∨
      (Fin15AnchoredAtom1984 chi ∧
      ¬Fin15AnchoredAtom0697 chi)) ∨
      ((Fin15AnchoredAtom1984 chi ∧
      ¬Fin15AnchoredAtom0983 chi) ∨
      (¬Fin15AnchoredAtom1984 chi ∧
      Fin15AnchoredAtom0486 chi ∧
      Fin15AnchoredAtom0487 chi ∧
      Fin15AnchoredAtom0531 chi ∧
      Fin15AnchoredAtom0697 chi ∧
      Fin15AnchoredAtom0983 chi))) ∨
      (((Fin15AnchoredAtom1985 chi ∧
      ¬Fin15AnchoredAtom0486 chi) ∨
      (Fin15AnchoredAtom1985 chi ∧
      ¬Fin15AnchoredAtom0488 chi)) ∨
      ((Fin15AnchoredAtom1985 chi ∧
      ¬Fin15AnchoredAtom0532 chi) ∨
      (Fin15AnchoredAtom1985 chi ∧
      ¬Fin15AnchoredAtom0698 chi)))) ∨
      ((((Fin15AnchoredAtom1985 chi ∧
      ¬Fin15AnchoredAtom0984 chi) ∨
      (¬Fin15AnchoredAtom1985 chi ∧
      Fin15AnchoredAtom0486 chi ∧
      Fin15AnchoredAtom0488 chi ∧
      Fin15AnchoredAtom0532 chi ∧
      Fin15AnchoredAtom0698 chi ∧
      Fin15AnchoredAtom0984 chi)) ∨
      ((Fin15AnchoredAtom1986 chi ∧
      ¬Fin15AnchoredAtom0487 chi) ∨
      (Fin15AnchoredAtom1986 chi ∧
      ¬Fin15AnchoredAtom0488 chi))) ∨
      (((Fin15AnchoredAtom1986 chi ∧
      ¬Fin15AnchoredAtom0533 chi) ∨
      (Fin15AnchoredAtom1986 chi ∧
      ¬Fin15AnchoredAtom0699 chi)) ∨
      ((Fin15AnchoredAtom1986 chi ∧
      ¬Fin15AnchoredAtom0985 chi) ∨
      (¬Fin15AnchoredAtom1986 chi ∧
      Fin15AnchoredAtom0487 chi ∧
      Fin15AnchoredAtom0488 chi ∧
      Fin15AnchoredAtom0533 chi ∧
      Fin15AnchoredAtom0699 chi ∧
      Fin15AnchoredAtom0985 chi))))) ∨
      (((((Fin15AnchoredAtom1987 chi ∧
      ¬Fin15AnchoredAtom0489 chi) ∨
      (Fin15AnchoredAtom1987 chi ∧
      ¬Fin15AnchoredAtom0490 chi)) ∨
      ((Fin15AnchoredAtom1987 chi ∧
      ¬Fin15AnchoredAtom0498 chi) ∨
      (Fin15AnchoredAtom1987 chi ∧
      ¬Fin15AnchoredAtom0700 chi))) ∨
      (((Fin15AnchoredAtom1987 chi ∧
      ¬Fin15AnchoredAtom0986 chi) ∨
      (¬Fin15AnchoredAtom1987 chi ∧
      Fin15AnchoredAtom0489 chi ∧
      Fin15AnchoredAtom0490 chi ∧
      Fin15AnchoredAtom0498 chi ∧
      Fin15AnchoredAtom0700 chi ∧
      Fin15AnchoredAtom0986 chi)) ∨
      ((Fin15AnchoredAtom1988 chi ∧
      ¬Fin15AnchoredAtom0489 chi) ∨
      (Fin15AnchoredAtom1988 chi ∧
      ¬Fin15AnchoredAtom0491 chi)))) ∨
      ((((Fin15AnchoredAtom1988 chi ∧
      ¬Fin15AnchoredAtom0499 chi) ∨
      (Fin15AnchoredAtom1988 chi ∧
      ¬Fin15AnchoredAtom0701 chi)) ∨
      ((Fin15AnchoredAtom1988 chi ∧
      ¬Fin15AnchoredAtom0987 chi) ∨
      (¬Fin15AnchoredAtom1988 chi ∧
      Fin15AnchoredAtom0489 chi ∧
      Fin15AnchoredAtom0491 chi ∧
      Fin15AnchoredAtom0499 chi ∧
      Fin15AnchoredAtom0701 chi ∧
      Fin15AnchoredAtom0987 chi))) ∨
      (((Fin15AnchoredAtom1989 chi ∧
      ¬Fin15AnchoredAtom0489 chi) ∨
      (Fin15AnchoredAtom1989 chi ∧
      ¬Fin15AnchoredAtom0492 chi)) ∨
      ((Fin15AnchoredAtom1989 chi ∧
      ¬Fin15AnchoredAtom0500 chi) ∨
      (Fin15AnchoredAtom1989 chi ∧
      ¬Fin15AnchoredAtom0702 chi)))))))) ∨
      (((((((Fin15AnchoredAtom1989 chi ∧
      ¬Fin15AnchoredAtom0988 chi) ∨
      ((¬Fin15AnchoredAtom1989 chi ∧
      Fin15AnchoredAtom0489 chi ∧
      Fin15AnchoredAtom0492 chi ∧
      Fin15AnchoredAtom0500 chi ∧
      Fin15AnchoredAtom0702 chi ∧
      Fin15AnchoredAtom0988 chi) ∨
      (Fin15AnchoredAtom1990 chi ∧
      ¬Fin15AnchoredAtom0489 chi))) ∨
      (((Fin15AnchoredAtom1990 chi ∧
      ¬Fin15AnchoredAtom0493 chi) ∨
      (Fin15AnchoredAtom1990 chi ∧
      ¬Fin15AnchoredAtom0501 chi)) ∨
      ((Fin15AnchoredAtom1990 chi ∧
      ¬Fin15AnchoredAtom0703 chi) ∨
      (Fin15AnchoredAtom1990 chi ∧
      ¬Fin15AnchoredAtom0989 chi)))) ∨
      ((((¬Fin15AnchoredAtom1990 chi ∧
      Fin15AnchoredAtom0489 chi ∧
      Fin15AnchoredAtom0493 chi ∧
      Fin15AnchoredAtom0501 chi ∧
      Fin15AnchoredAtom0703 chi ∧
      Fin15AnchoredAtom0989 chi) ∨
      (Fin15AnchoredAtom1991 chi ∧
      ¬Fin15AnchoredAtom0489 chi)) ∨
      ((Fin15AnchoredAtom1991 chi ∧
      ¬Fin15AnchoredAtom0502 chi) ∨
      (¬Fin15AnchoredAtom1991 chi ∧
      Fin15AnchoredAtom0489 chi ∧
      Fin15AnchoredAtom0494 chi ∧
      Fin15AnchoredAtom0502 chi ∧
      Fin15AnchoredAtom0704 chi ∧
      Fin15AnchoredAtom0990 chi))) ∨
      (((Fin15AnchoredAtom1992 chi ∧
      ¬Fin15AnchoredAtom0489 chi) ∨
      (Fin15AnchoredAtom1992 chi ∧
      ¬Fin15AnchoredAtom0495 chi)) ∨
      ((Fin15AnchoredAtom1992 chi ∧
      ¬Fin15AnchoredAtom0503 chi) ∨
      (Fin15AnchoredAtom1992 chi ∧
      ¬Fin15AnchoredAtom0705 chi))))) ∨
      (((((Fin15AnchoredAtom1992 chi ∧
      ¬Fin15AnchoredAtom0991 chi) ∨
      (¬Fin15AnchoredAtom1992 chi ∧
      Fin15AnchoredAtom0489 chi ∧
      Fin15AnchoredAtom0495 chi ∧
      Fin15AnchoredAtom0503 chi ∧
      Fin15AnchoredAtom0705 chi ∧
      Fin15AnchoredAtom0991 chi)) ∨
      ((Fin15AnchoredAtom1993 chi ∧
      ¬Fin15AnchoredAtom0489 chi) ∨
      (Fin15AnchoredAtom1993 chi ∧
      ¬Fin15AnchoredAtom0496 chi))) ∨
      (((Fin15AnchoredAtom1993 chi ∧
      ¬Fin15AnchoredAtom0504 chi) ∨
      (Fin15AnchoredAtom1993 chi ∧
      ¬Fin15AnchoredAtom0706 chi)) ∨
      ((Fin15AnchoredAtom1993 chi ∧
      ¬Fin15AnchoredAtom0992 chi) ∨
      (¬Fin15AnchoredAtom1993 chi ∧
      Fin15AnchoredAtom0489 chi ∧
      Fin15AnchoredAtom0496 chi ∧
      Fin15AnchoredAtom0504 chi ∧
      Fin15AnchoredAtom0706 chi ∧
      Fin15AnchoredAtom0992 chi)))) ∨
      ((((Fin15AnchoredAtom1994 chi ∧
      ¬Fin15AnchoredAtom0489 chi) ∨
      (Fin15AnchoredAtom1994 chi ∧
      ¬Fin15AnchoredAtom0497 chi)) ∨
      ((Fin15AnchoredAtom1994 chi ∧
      ¬Fin15AnchoredAtom0505 chi) ∨
      (Fin15AnchoredAtom1994 chi ∧
      ¬Fin15AnchoredAtom0707 chi))) ∨
      (((Fin15AnchoredAtom1994 chi ∧
      ¬Fin15AnchoredAtom0993 chi) ∨
      (¬Fin15AnchoredAtom1994 chi ∧
      Fin15AnchoredAtom0489 chi ∧
      Fin15AnchoredAtom0497 chi ∧
      Fin15AnchoredAtom0505 chi ∧
      Fin15AnchoredAtom0707 chi ∧
      Fin15AnchoredAtom0993 chi)) ∨
      ((Fin15AnchoredAtom1995 chi ∧
      ¬Fin15AnchoredAtom0490 chi) ∨
      (Fin15AnchoredAtom1995 chi ∧
      ¬Fin15AnchoredAtom0491 chi)))))) ∨
      ((((((Fin15AnchoredAtom1995 chi ∧
      ¬Fin15AnchoredAtom0506 chi) ∨
      (Fin15AnchoredAtom1995 chi ∧
      ¬Fin15AnchoredAtom0708 chi)) ∨
      ((Fin15AnchoredAtom1995 chi ∧
      ¬Fin15AnchoredAtom0994 chi) ∨
      (¬Fin15AnchoredAtom1995 chi ∧
      Fin15AnchoredAtom0490 chi ∧
      Fin15AnchoredAtom0491 chi ∧
      Fin15AnchoredAtom0506 chi ∧
      Fin15AnchoredAtom0708 chi ∧
      Fin15AnchoredAtom0994 chi))) ∨
      (((Fin15AnchoredAtom1996 chi ∧
      ¬Fin15AnchoredAtom0490 chi) ∨
      (Fin15AnchoredAtom1996 chi ∧
      ¬Fin15AnchoredAtom0492 chi)) ∨
      ((Fin15AnchoredAtom1996 chi ∧
      ¬Fin15AnchoredAtom0507 chi) ∨
      (Fin15AnchoredAtom1996 chi ∧
      ¬Fin15AnchoredAtom0709 chi)))) ∨
      ((((Fin15AnchoredAtom1996 chi ∧
      ¬Fin15AnchoredAtom0995 chi) ∨
      (¬Fin15AnchoredAtom1996 chi ∧
      Fin15AnchoredAtom0490 chi ∧
      Fin15AnchoredAtom0492 chi ∧
      Fin15AnchoredAtom0507 chi ∧
      Fin15AnchoredAtom0709 chi ∧
      Fin15AnchoredAtom0995 chi)) ∨
      ((Fin15AnchoredAtom1997 chi ∧
      ¬Fin15AnchoredAtom0490 chi) ∨
      (Fin15AnchoredAtom1997 chi ∧
      ¬Fin15AnchoredAtom0493 chi))) ∨
      (((Fin15AnchoredAtom1997 chi ∧
      ¬Fin15AnchoredAtom0508 chi) ∨
      (Fin15AnchoredAtom1997 chi ∧
      ¬Fin15AnchoredAtom0710 chi)) ∨
      ((Fin15AnchoredAtom1997 chi ∧
      ¬Fin15AnchoredAtom0996 chi) ∨
      (¬Fin15AnchoredAtom1997 chi ∧
      Fin15AnchoredAtom0490 chi ∧
      Fin15AnchoredAtom0493 chi ∧
      Fin15AnchoredAtom0508 chi ∧
      Fin15AnchoredAtom0710 chi ∧
      Fin15AnchoredAtom0996 chi))))) ∨
      (((((Fin15AnchoredAtom1998 chi ∧
      ¬Fin15AnchoredAtom0490 chi) ∨
      (Fin15AnchoredAtom1999 chi ∧
      ¬Fin15AnchoredAtom0490 chi)) ∨
      ((Fin15AnchoredAtom1999 chi ∧
      ¬Fin15AnchoredAtom0495 chi) ∨
      (Fin15AnchoredAtom1999 chi ∧
      ¬Fin15AnchoredAtom0510 chi))) ∨
      (((Fin15AnchoredAtom1999 chi ∧
      ¬Fin15AnchoredAtom0712 chi) ∨
      (Fin15AnchoredAtom1999 chi ∧
      ¬Fin15AnchoredAtom0998 chi)) ∨
      ((¬Fin15AnchoredAtom1999 chi ∧
      Fin15AnchoredAtom0490 chi ∧
      Fin15AnchoredAtom0495 chi ∧
      Fin15AnchoredAtom0510 chi ∧
      Fin15AnchoredAtom0712 chi ∧
      Fin15AnchoredAtom0998 chi) ∨
      (Fin15AnchoredAtom2000 chi ∧
      ¬Fin15AnchoredAtom0490 chi)))) ∨
      ((((Fin15AnchoredAtom2000 chi ∧
      ¬Fin15AnchoredAtom0496 chi) ∨
      (Fin15AnchoredAtom2000 chi ∧
      ¬Fin15AnchoredAtom0511 chi)) ∨
      ((Fin15AnchoredAtom2000 chi ∧
      ¬Fin15AnchoredAtom0713 chi) ∨
      (Fin15AnchoredAtom2000 chi ∧
      ¬Fin15AnchoredAtom0999 chi))) ∨
      (((¬Fin15AnchoredAtom2000 chi ∧
      Fin15AnchoredAtom0490 chi ∧
      Fin15AnchoredAtom0496 chi ∧
      Fin15AnchoredAtom0511 chi ∧
      Fin15AnchoredAtom0713 chi ∧
      Fin15AnchoredAtom0999 chi) ∨
      (Fin15AnchoredAtom2001 chi ∧
      ¬Fin15AnchoredAtom0490 chi)) ∨
      ((Fin15AnchoredAtom2001 chi ∧
      ¬Fin15AnchoredAtom0497 chi) ∨
      (Fin15AnchoredAtom2001 chi ∧
      ¬Fin15AnchoredAtom0512 chi))))))) ∨
      ((((((Fin15AnchoredAtom2001 chi ∧
      ¬Fin15AnchoredAtom0714 chi) ∨
      ((Fin15AnchoredAtom2001 chi ∧
      ¬Fin15AnchoredAtom1000 chi) ∨
      (¬Fin15AnchoredAtom2001 chi ∧
      Fin15AnchoredAtom0490 chi ∧
      Fin15AnchoredAtom0497 chi ∧
      Fin15AnchoredAtom0512 chi ∧
      Fin15AnchoredAtom0714 chi ∧
      Fin15AnchoredAtom1000 chi))) ∨
      (((Fin15AnchoredAtom2002 chi ∧
      ¬Fin15AnchoredAtom0491 chi) ∨
      (Fin15AnchoredAtom2002 chi ∧
      ¬Fin15AnchoredAtom0492 chi)) ∨
      ((Fin15AnchoredAtom2002 chi ∧
      ¬Fin15AnchoredAtom0513 chi) ∨
      (Fin15AnchoredAtom2002 chi ∧
      ¬Fin15AnchoredAtom0715 chi)))) ∨
      ((((Fin15AnchoredAtom2002 chi ∧
      ¬Fin15AnchoredAtom1001 chi) ∨
      (¬Fin15AnchoredAtom2002 chi ∧
      Fin15AnchoredAtom0491 chi ∧
      Fin15AnchoredAtom0492 chi ∧
      Fin15AnchoredAtom0513 chi ∧
      Fin15AnchoredAtom0715 chi ∧
      Fin15AnchoredAtom1001 chi)) ∨
      ((Fin15AnchoredAtom2003 chi ∧
      ¬Fin15AnchoredAtom0491 chi) ∨
      (Fin15AnchoredAtom2003 chi ∧
      ¬Fin15AnchoredAtom0493 chi))) ∨
      (((Fin15AnchoredAtom2003 chi ∧
      ¬Fin15AnchoredAtom0514 chi) ∨
      (Fin15AnchoredAtom2003 chi ∧
      ¬Fin15AnchoredAtom0716 chi)) ∨
      ((Fin15AnchoredAtom2003 chi ∧
      ¬Fin15AnchoredAtom1002 chi) ∨
      (¬Fin15AnchoredAtom2003 chi ∧
      Fin15AnchoredAtom0491 chi ∧
      Fin15AnchoredAtom0493 chi ∧
      Fin15AnchoredAtom0514 chi ∧
      Fin15AnchoredAtom0716 chi ∧
      Fin15AnchoredAtom1002 chi))))) ∨
      (((((Fin15AnchoredAtom2005 chi ∧
      ¬Fin15AnchoredAtom0491 chi) ∨
      (Fin15AnchoredAtom2005 chi ∧
      ¬Fin15AnchoredAtom0495 chi)) ∨
      ((Fin15AnchoredAtom2005 chi ∧
      ¬Fin15AnchoredAtom0516 chi) ∨
      (Fin15AnchoredAtom2005 chi ∧
      ¬Fin15AnchoredAtom0718 chi))) ∨
      (((Fin15AnchoredAtom2005 chi ∧
      ¬Fin15AnchoredAtom1004 chi) ∨
      (¬Fin15AnchoredAtom2005 chi ∧
      Fin15AnchoredAtom0491 chi ∧
      Fin15AnchoredAtom0495 chi ∧
      Fin15AnchoredAtom0516 chi ∧
      Fin15AnchoredAtom0718 chi ∧
      Fin15AnchoredAtom1004 chi)) ∨
      ((Fin15AnchoredAtom2006 chi ∧
      ¬Fin15AnchoredAtom0491 chi) ∨
      (Fin15AnchoredAtom2006 chi ∧
      ¬Fin15AnchoredAtom0496 chi)))) ∨
      ((((Fin15AnchoredAtom2006 chi ∧
      ¬Fin15AnchoredAtom0517 chi) ∨
      (Fin15AnchoredAtom2006 chi ∧
      ¬Fin15AnchoredAtom0719 chi)) ∨
      ((Fin15AnchoredAtom2006 chi ∧
      ¬Fin15AnchoredAtom1005 chi) ∨
      (¬Fin15AnchoredAtom2006 chi ∧
      Fin15AnchoredAtom0491 chi ∧
      Fin15AnchoredAtom0496 chi ∧
      Fin15AnchoredAtom0517 chi ∧
      Fin15AnchoredAtom0719 chi ∧
      Fin15AnchoredAtom1005 chi))) ∨
      (((Fin15AnchoredAtom2007 chi ∧
      ¬Fin15AnchoredAtom0491 chi) ∨
      (Fin15AnchoredAtom2007 chi ∧
      ¬Fin15AnchoredAtom0720 chi)) ∨
      ((¬Fin15AnchoredAtom2007 chi ∧
      Fin15AnchoredAtom0491 chi ∧
      Fin15AnchoredAtom0497 chi ∧
      Fin15AnchoredAtom0518 chi ∧
      Fin15AnchoredAtom0720 chi ∧
      Fin15AnchoredAtom1006 chi) ∨
      (Fin15AnchoredAtom2008 chi ∧
      ¬Fin15AnchoredAtom0492 chi)))))) ∨
      ((((((Fin15AnchoredAtom2008 chi ∧
      ¬Fin15AnchoredAtom0493 chi) ∨
      (Fin15AnchoredAtom2008 chi ∧
      ¬Fin15AnchoredAtom0519 chi)) ∨
      ((Fin15AnchoredAtom2008 chi ∧
      ¬Fin15AnchoredAtom0721 chi) ∨
      (Fin15AnchoredAtom2008 chi ∧
      ¬Fin15AnchoredAtom1007 chi))) ∨
      (((¬Fin15AnchoredAtom2008 chi ∧
      Fin15AnchoredAtom0492 chi ∧
      Fin15AnchoredAtom0493 chi ∧
      Fin15AnchoredAtom0519 chi ∧
      Fin15AnchoredAtom0721 chi ∧
      Fin15AnchoredAtom1007 chi) ∨
      (Fin15AnchoredAtom2009 chi ∧
      ¬Fin15AnchoredAtom0492 chi)) ∨
      ((Fin15AnchoredAtom2010 chi ∧
      ¬Fin15AnchoredAtom0492 chi) ∨
      (Fin15AnchoredAtom2010 chi ∧
      ¬Fin15AnchoredAtom0495 chi)))) ∨
      ((((Fin15AnchoredAtom2010 chi ∧
      ¬Fin15AnchoredAtom0521 chi) ∨
      (Fin15AnchoredAtom2010 chi ∧
      ¬Fin15AnchoredAtom0723 chi)) ∨
      ((Fin15AnchoredAtom2010 chi ∧
      ¬Fin15AnchoredAtom1009 chi) ∨
      (¬Fin15AnchoredAtom2010 chi ∧
      Fin15AnchoredAtom0492 chi ∧
      Fin15AnchoredAtom0495 chi ∧
      Fin15AnchoredAtom0521 chi ∧
      Fin15AnchoredAtom0723 chi ∧
      Fin15AnchoredAtom1009 chi))) ∨
      (((Fin15AnchoredAtom2011 chi ∧
      ¬Fin15AnchoredAtom0492 chi) ∨
      (Fin15AnchoredAtom2011 chi ∧
      ¬Fin15AnchoredAtom0496 chi)) ∨
      ((Fin15AnchoredAtom2011 chi ∧
      ¬Fin15AnchoredAtom0522 chi) ∨
      (Fin15AnchoredAtom2011 chi ∧
      ¬Fin15AnchoredAtom0724 chi))))) ∨
      (((((Fin15AnchoredAtom2011 chi ∧
      ¬Fin15AnchoredAtom1010 chi) ∨
      (¬Fin15AnchoredAtom2011 chi ∧
      Fin15AnchoredAtom0492 chi ∧
      Fin15AnchoredAtom0496 chi ∧
      Fin15AnchoredAtom0522 chi ∧
      Fin15AnchoredAtom0724 chi ∧
      Fin15AnchoredAtom1010 chi)) ∨
      ((Fin15AnchoredAtom2012 chi ∧
      ¬Fin15AnchoredAtom0492 chi) ∨
      (Fin15AnchoredAtom2012 chi ∧
      ¬Fin15AnchoredAtom0497 chi))) ∨
      (((Fin15AnchoredAtom2012 chi ∧
      ¬Fin15AnchoredAtom0523 chi) ∨
      (Fin15AnchoredAtom2012 chi ∧
      ¬Fin15AnchoredAtom0725 chi)) ∨
      ((Fin15AnchoredAtom2012 chi ∧
      ¬Fin15AnchoredAtom1011 chi) ∨
      (¬Fin15AnchoredAtom2012 chi ∧
      Fin15AnchoredAtom0492 chi ∧
      Fin15AnchoredAtom0497 chi ∧
      Fin15AnchoredAtom0523 chi ∧
      Fin15AnchoredAtom0725 chi ∧
      Fin15AnchoredAtom1011 chi)))) ∨
      ((((Fin15AnchoredAtom2013 chi ∧
      ¬Fin15AnchoredAtom0493 chi) ∨
      (Fin15AnchoredAtom2013 chi ∧
      ¬Fin15AnchoredAtom0494 chi)) ∨
      ((Fin15AnchoredAtom2013 chi ∧
      ¬Fin15AnchoredAtom0726 chi) ∨
      (Fin15AnchoredAtom2013 chi ∧
      ¬Fin15AnchoredAtom1012 chi))) ∨
      (((¬Fin15AnchoredAtom2013 chi ∧
      Fin15AnchoredAtom0493 chi ∧
      Fin15AnchoredAtom0494 chi ∧
      Fin15AnchoredAtom0524 chi ∧
      Fin15AnchoredAtom0726 chi ∧
      Fin15AnchoredAtom1012 chi) ∨
      (Fin15AnchoredAtom2014 chi ∧
      ¬Fin15AnchoredAtom0493 chi)) ∨
      ((Fin15AnchoredAtom2014 chi ∧
      ¬Fin15AnchoredAtom0495 chi) ∨
      (Fin15AnchoredAtom2014 chi ∧
      ¬Fin15AnchoredAtom0525 chi)))))))))) := by
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
                exact fin15Anchored_clause16154 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16155 chi hbad
                ·
                  exact fin15Anchored_clause16156 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16157 chi hbad
                ·
                  exact fin15Anchored_clause16158 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16159 chi hbad
                ·
                  exact fin15Anchored_clause16160 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16161 chi hbad
                ·
                  exact fin15Anchored_clause16162 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16163 chi hbad
                ·
                  exact fin15Anchored_clause16164 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16165 chi hbad
                ·
                  exact fin15Anchored_clause16166 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16167 chi hbad
                ·
                  exact fin15Anchored_clause16168 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16169 chi hbad
                ·
                  exact fin15Anchored_clause16170 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16171 chi hbad
                ·
                  exact fin15Anchored_clause16172 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16173 chi hbad
                ·
                  exact fin15Anchored_clause16174 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16175 chi hbad
                ·
                  exact fin15Anchored_clause16176 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16177 chi hbad
                ·
                  exact fin15Anchored_clause16178 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16179 chi hbad
                ·
                  exact fin15Anchored_clause16180 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16181 chi hbad
                ·
                  exact fin15Anchored_clause16182 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16183 chi hbad
                ·
                  exact fin15Anchored_clause16184 chi hbad
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
                  exact fin15Anchored_clause16185 chi hbad
                ·
                  exact fin15Anchored_clause16186 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16187 chi hbad
                ·
                  exact fin15Anchored_clause16188 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16189 chi hbad
                ·
                  exact fin15Anchored_clause16190 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16191 chi hbad
                ·
                  exact fin15Anchored_clause16192 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16193 chi hbad
                ·
                  exact fin15Anchored_clause16194 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16195 chi hbad
                ·
                  exact fin15Anchored_clause16196 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16197 chi hbad
                ·
                  exact fin15Anchored_clause16198 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16199 chi hbad
                ·
                  exact fin15Anchored_clause16200 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16201 chi hbad
                ·
                  exact fin15Anchored_clause16202 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16203 chi hbad
                ·
                  exact fin15Anchored_clause16204 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16205 chi hbad
                ·
                  exact fin15Anchored_clause16206 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16207 chi hbad
                ·
                  exact fin15Anchored_clause16208 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16209 chi hbad
                ·
                  exact fin15Anchored_clause16210 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16211 chi hbad
                ·
                  exact fin15Anchored_clause16212 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16213 chi hbad
                ·
                  exact fin15Anchored_clause16214 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16215 chi hbad
                ·
                  exact fin15Anchored_clause16216 chi hbad
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
                exact fin15Anchored_clause16217 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16218 chi hbad
                ·
                  exact fin15Anchored_clause16219 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16220 chi hbad
                ·
                  exact fin15Anchored_clause16221 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16222 chi hbad
                ·
                  exact fin15Anchored_clause16223 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16224 chi hbad
                ·
                  exact fin15Anchored_clause16225 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16226 chi hbad
                ·
                  exact fin15Anchored_clause16227 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16228 chi hbad
                ·
                  exact fin15Anchored_clause16229 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16230 chi hbad
                ·
                  exact fin15Anchored_clause16231 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16232 chi hbad
                ·
                  exact fin15Anchored_clause16233 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16234 chi hbad
                ·
                  exact fin15Anchored_clause16235 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16236 chi hbad
                ·
                  exact fin15Anchored_clause16237 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16238 chi hbad
                ·
                  exact fin15Anchored_clause16239 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16240 chi hbad
                ·
                  exact fin15Anchored_clause16241 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16242 chi hbad
                ·
                  exact fin15Anchored_clause16243 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16244 chi hbad
                ·
                  exact fin15Anchored_clause16245 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16246 chi hbad
                ·
                  exact fin15Anchored_clause16247 chi hbad
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
                  exact fin15Anchored_clause16248 chi hbad
                ·
                  exact fin15Anchored_clause16249 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16250 chi hbad
                ·
                  exact fin15Anchored_clause16251 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16252 chi hbad
                ·
                  exact fin15Anchored_clause16253 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16254 chi hbad
                ·
                  exact fin15Anchored_clause16255 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16256 chi hbad
                ·
                  exact fin15Anchored_clause16257 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16258 chi hbad
                ·
                  exact fin15Anchored_clause16259 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16260 chi hbad
                ·
                  exact fin15Anchored_clause16261 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16262 chi hbad
                ·
                  exact fin15Anchored_clause16263 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16264 chi hbad
                ·
                  exact fin15Anchored_clause16265 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16266 chi hbad
                ·
                  exact fin15Anchored_clause16267 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16268 chi hbad
                ·
                  exact fin15Anchored_clause16269 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16270 chi hbad
                ·
                  exact fin15Anchored_clause16271 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16272 chi hbad
                ·
                  exact fin15Anchored_clause16273 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16274 chi hbad
                ·
                  exact fin15Anchored_clause16275 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16276 chi hbad
                ·
                  exact fin15Anchored_clause16277 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16278 chi hbad
                ·
                  exact fin15Anchored_clause16279 chi hbad
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
                exact fin15Anchored_clause16280 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16281 chi hbad
                ·
                  exact fin15Anchored_clause16282 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16283 chi hbad
                ·
                  exact fin15Anchored_clause16284 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16285 chi hbad
                ·
                  exact fin15Anchored_clause16286 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16287 chi hbad
                ·
                  exact fin15Anchored_clause16288 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16289 chi hbad
                ·
                  exact fin15Anchored_clause16290 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16291 chi hbad
                ·
                  exact fin15Anchored_clause16292 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16293 chi hbad
                ·
                  exact fin15Anchored_clause16294 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16295 chi hbad
                ·
                  exact fin15Anchored_clause16296 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16297 chi hbad
                ·
                  exact fin15Anchored_clause16298 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16299 chi hbad
                ·
                  exact fin15Anchored_clause16300 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16301 chi hbad
                ·
                  exact fin15Anchored_clause16302 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16303 chi hbad
                ·
                  exact fin15Anchored_clause16304 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16305 chi hbad
                ·
                  exact fin15Anchored_clause16306 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16307 chi hbad
                ·
                  exact fin15Anchored_clause16308 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16309 chi hbad
                ·
                  exact fin15Anchored_clause16310 chi hbad
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
                  exact fin15Anchored_clause16311 chi hbad
                ·
                  exact fin15Anchored_clause16312 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16313 chi hbad
                ·
                  exact fin15Anchored_clause16314 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16315 chi hbad
                ·
                  exact fin15Anchored_clause16316 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16317 chi hbad
                ·
                  exact fin15Anchored_clause16318 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16319 chi hbad
                ·
                  exact fin15Anchored_clause16320 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16321 chi hbad
                ·
                  exact fin15Anchored_clause16322 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16323 chi hbad
                ·
                  exact fin15Anchored_clause16324 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16325 chi hbad
                ·
                  exact fin15Anchored_clause16326 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16327 chi hbad
                ·
                  exact fin15Anchored_clause16328 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16329 chi hbad
                ·
                  exact fin15Anchored_clause16330 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16331 chi hbad
                ·
                  exact fin15Anchored_clause16332 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16333 chi hbad
                ·
                  exact fin15Anchored_clause16334 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16335 chi hbad
                ·
                  exact fin15Anchored_clause16336 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16337 chi hbad
                ·
                  exact fin15Anchored_clause16338 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16339 chi hbad
                ·
                  exact fin15Anchored_clause16340 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16341 chi hbad
                ·
                  exact fin15Anchored_clause16342 chi hbad
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
                exact fin15Anchored_clause16343 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16344 chi hbad
                ·
                  exact fin15Anchored_clause16345 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16346 chi hbad
                ·
                  exact fin15Anchored_clause16347 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16348 chi hbad
                ·
                  exact fin15Anchored_clause16349 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16350 chi hbad
                ·
                  exact fin15Anchored_clause16351 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16352 chi hbad
                ·
                  exact fin15Anchored_clause16353 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16354 chi hbad
                ·
                  exact fin15Anchored_clause16355 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16356 chi hbad
                ·
                  exact fin15Anchored_clause16357 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16358 chi hbad
                ·
                  exact fin15Anchored_clause16359 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16360 chi hbad
                ·
                  exact fin15Anchored_clause16361 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16362 chi hbad
                ·
                  exact fin15Anchored_clause16363 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16364 chi hbad
                ·
                  exact fin15Anchored_clause16365 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16366 chi hbad
                ·
                  exact fin15Anchored_clause16367 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16368 chi hbad
                ·
                  exact fin15Anchored_clause16369 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16370 chi hbad
                ·
                  exact fin15Anchored_clause16371 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16372 chi hbad
                ·
                  exact fin15Anchored_clause16373 chi hbad
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
                  exact fin15Anchored_clause16374 chi hbad
                ·
                  exact fin15Anchored_clause16375 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16376 chi hbad
                ·
                  exact fin15Anchored_clause16377 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16378 chi hbad
                ·
                  exact fin15Anchored_clause16379 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16380 chi hbad
                ·
                  exact fin15Anchored_clause16381 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16382 chi hbad
                ·
                  exact fin15Anchored_clause16383 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16384 chi hbad
                ·
                  exact fin15Anchored_clause16385 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16386 chi hbad
                ·
                  exact fin15Anchored_clause16387 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16388 chi hbad
                ·
                  exact fin15Anchored_clause16389 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16390 chi hbad
                ·
                  exact fin15Anchored_clause16391 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16392 chi hbad
                ·
                  exact fin15Anchored_clause16393 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16394 chi hbad
                ·
                  exact fin15Anchored_clause16395 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16396 chi hbad
                ·
                  exact fin15Anchored_clause16397 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16398 chi hbad
                ·
                  exact fin15Anchored_clause16399 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16400 chi hbad
                ·
                  exact fin15Anchored_clause16401 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16402 chi hbad
                ·
                  exact fin15Anchored_clause16403 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16404 chi hbad
                ·
                  exact fin15Anchored_clause16405 chi hbad

end ErdosSzekeres

end
