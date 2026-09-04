module

public import ErdosSzekeres.Fin15AnchoredClauseChunk175
public import ErdosSzekeres.Fin15AnchoredClauseChunk176
public import ErdosSzekeres.Fin15AnchoredClauseChunk177

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 089. -/

theorem fin15Anchored_rejectSemanticSegment089
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom3322 chi ∧
      ¬Fin15AnchoredAtom0978 chi) ∨
      ((Fin15AnchoredAtom3322 chi ∧
      ¬Fin15AnchoredAtom0979 chi) ∨
      (Fin15AnchoredAtom3322 chi ∧
      ¬Fin15AnchoredAtom0985 chi))) ∨
      (((Fin15AnchoredAtom3322 chi ∧
      ¬Fin15AnchoredAtom1101 chi) ∨
      (Fin15AnchoredAtom3322 chi ∧
      ¬Fin15AnchoredAtom1606 chi)) ∨
      ((¬Fin15AnchoredAtom3322 chi ∧
      Fin15AnchoredAtom0978 chi ∧
      Fin15AnchoredAtom0979 chi ∧
      Fin15AnchoredAtom0985 chi ∧
      Fin15AnchoredAtom1101 chi ∧
      Fin15AnchoredAtom1606 chi) ∨
      (Fin15AnchoredAtom3323 chi ∧
      ¬Fin15AnchoredAtom0981 chi)))) ∨
      ((((Fin15AnchoredAtom3323 chi ∧
      ¬Fin15AnchoredAtom0983 chi) ∨
      (Fin15AnchoredAtom3323 chi ∧
      ¬Fin15AnchoredAtom1102 chi)) ∨
      ((Fin15AnchoredAtom3323 chi ∧
      ¬Fin15AnchoredAtom1607 chi) ∨
      (¬Fin15AnchoredAtom3323 chi ∧
      Fin15AnchoredAtom0980 chi ∧
      Fin15AnchoredAtom0981 chi ∧
      Fin15AnchoredAtom0983 chi ∧
      Fin15AnchoredAtom1102 chi ∧
      Fin15AnchoredAtom1607 chi))) ∨
      (((Fin15AnchoredAtom3324 chi ∧
      ¬Fin15AnchoredAtom0984 chi) ∨
      (Fin15AnchoredAtom3324 chi ∧
      ¬Fin15AnchoredAtom1103 chi)) ∨
      ((Fin15AnchoredAtom3326 chi ∧
      ¬Fin15AnchoredAtom0983 chi) ∨
      (Fin15AnchoredAtom3326 chi ∧
      ¬Fin15AnchoredAtom0984 chi))))) ∨
      (((((Fin15AnchoredAtom3326 chi ∧
      ¬Fin15AnchoredAtom0985 chi) ∨
      (Fin15AnchoredAtom3326 chi ∧
      ¬Fin15AnchoredAtom1105 chi)) ∨
      ((Fin15AnchoredAtom3326 chi ∧
      ¬Fin15AnchoredAtom1610 chi) ∨
      (¬Fin15AnchoredAtom3326 chi ∧
      Fin15AnchoredAtom0983 chi ∧
      Fin15AnchoredAtom0984 chi ∧
      Fin15AnchoredAtom0985 chi ∧
      Fin15AnchoredAtom1105 chi ∧
      Fin15AnchoredAtom1610 chi))) ∨
      (((Fin15AnchoredAtom3327 chi ∧
      ¬Fin15AnchoredAtom0986 chi) ∨
      (Fin15AnchoredAtom3327 chi ∧
      ¬Fin15AnchoredAtom0994 chi)) ∨
      ((Fin15AnchoredAtom3327 chi ∧
      ¬Fin15AnchoredAtom1022 chi) ∨
      (Fin15AnchoredAtom3327 chi ∧
      ¬Fin15AnchoredAtom1611 chi)))) ∨
      ((((¬Fin15AnchoredAtom3327 chi ∧
      Fin15AnchoredAtom0986 chi ∧
      Fin15AnchoredAtom0987 chi ∧
      Fin15AnchoredAtom0994 chi ∧
      Fin15AnchoredAtom1022 chi ∧
      Fin15AnchoredAtom1611 chi) ∨
      (Fin15AnchoredAtom3328 chi ∧
      ¬Fin15AnchoredAtom0986 chi)) ∨
      ((Fin15AnchoredAtom3328 chi ∧
      ¬Fin15AnchoredAtom0988 chi) ∨
      (Fin15AnchoredAtom3328 chi ∧
      ¬Fin15AnchoredAtom0995 chi))) ∨
      (((Fin15AnchoredAtom3328 chi ∧
      ¬Fin15AnchoredAtom1023 chi) ∨
      (Fin15AnchoredAtom3328 chi ∧
      ¬Fin15AnchoredAtom1612 chi)) ∨
      ((¬Fin15AnchoredAtom3328 chi ∧
      Fin15AnchoredAtom0986 chi ∧
      Fin15AnchoredAtom0988 chi ∧
      Fin15AnchoredAtom0995 chi ∧
      Fin15AnchoredAtom1023 chi ∧
      Fin15AnchoredAtom1612 chi) ∨
      (Fin15AnchoredAtom3329 chi ∧
      ¬Fin15AnchoredAtom0986 chi)))))) ∨
      ((((((Fin15AnchoredAtom3329 chi ∧
      ¬Fin15AnchoredAtom0989 chi) ∨
      (Fin15AnchoredAtom3329 chi ∧
      ¬Fin15AnchoredAtom0996 chi)) ∨
      ((Fin15AnchoredAtom3329 chi ∧
      ¬Fin15AnchoredAtom1024 chi) ∨
      (Fin15AnchoredAtom3329 chi ∧
      ¬Fin15AnchoredAtom1613 chi))) ∨
      (((¬Fin15AnchoredAtom3329 chi ∧
      Fin15AnchoredAtom0986 chi ∧
      Fin15AnchoredAtom0989 chi ∧
      Fin15AnchoredAtom0996 chi ∧
      Fin15AnchoredAtom1024 chi ∧
      Fin15AnchoredAtom1613 chi) ∨
      (Fin15AnchoredAtom3331 chi ∧
      ¬Fin15AnchoredAtom0986 chi)) ∨
      ((Fin15AnchoredAtom3331 chi ∧
      ¬Fin15AnchoredAtom0991 chi) ∨
      (Fin15AnchoredAtom3331 chi ∧
      ¬Fin15AnchoredAtom0998 chi)))) ∨
      ((((Fin15AnchoredAtom3331 chi ∧
      ¬Fin15AnchoredAtom1026 chi) ∨
      (Fin15AnchoredAtom3331 chi ∧
      ¬Fin15AnchoredAtom1615 chi)) ∨
      ((¬Fin15AnchoredAtom3331 chi ∧
      Fin15AnchoredAtom0986 chi ∧
      Fin15AnchoredAtom0991 chi ∧
      Fin15AnchoredAtom0998 chi ∧
      Fin15AnchoredAtom1026 chi ∧
      Fin15AnchoredAtom1615 chi) ∨
      (Fin15AnchoredAtom3332 chi ∧
      ¬Fin15AnchoredAtom0986 chi))) ∨
      (((Fin15AnchoredAtom3332 chi ∧
      ¬Fin15AnchoredAtom0992 chi) ∨
      (Fin15AnchoredAtom3332 chi ∧
      ¬Fin15AnchoredAtom0999 chi)) ∨
      ((Fin15AnchoredAtom3332 chi ∧
      ¬Fin15AnchoredAtom1027 chi) ∨
      (Fin15AnchoredAtom3332 chi ∧
      ¬Fin15AnchoredAtom1616 chi))))) ∨
      (((((¬Fin15AnchoredAtom3332 chi ∧
      Fin15AnchoredAtom0986 chi ∧
      Fin15AnchoredAtom0992 chi ∧
      Fin15AnchoredAtom0999 chi ∧
      Fin15AnchoredAtom1027 chi ∧
      Fin15AnchoredAtom1616 chi) ∨
      (Fin15AnchoredAtom3333 chi ∧
      ¬Fin15AnchoredAtom0986 chi)) ∨
      ((Fin15AnchoredAtom3333 chi ∧
      ¬Fin15AnchoredAtom0993 chi) ∨
      (Fin15AnchoredAtom3333 chi ∧
      ¬Fin15AnchoredAtom1000 chi))) ∨
      (((Fin15AnchoredAtom3333 chi ∧
      ¬Fin15AnchoredAtom1028 chi) ∨
      (Fin15AnchoredAtom3333 chi ∧
      ¬Fin15AnchoredAtom1617 chi)) ∨
      ((¬Fin15AnchoredAtom3333 chi ∧
      Fin15AnchoredAtom0986 chi ∧
      Fin15AnchoredAtom0993 chi ∧
      Fin15AnchoredAtom1000 chi ∧
      Fin15AnchoredAtom1028 chi ∧
      Fin15AnchoredAtom1617 chi) ∨
      (Fin15AnchoredAtom3334 chi ∧
      ¬Fin15AnchoredAtom0987 chi)))) ∨
      ((((Fin15AnchoredAtom3334 chi ∧
      ¬Fin15AnchoredAtom0988 chi) ∨
      (Fin15AnchoredAtom3334 chi ∧
      ¬Fin15AnchoredAtom1001 chi)) ∨
      ((Fin15AnchoredAtom3334 chi ∧
      ¬Fin15AnchoredAtom1029 chi) ∨
      (Fin15AnchoredAtom3334 chi ∧
      ¬Fin15AnchoredAtom1618 chi))) ∨
      (((¬Fin15AnchoredAtom3334 chi ∧
      Fin15AnchoredAtom0987 chi ∧
      Fin15AnchoredAtom0988 chi ∧
      Fin15AnchoredAtom1001 chi ∧
      Fin15AnchoredAtom1029 chi ∧
      Fin15AnchoredAtom1618 chi) ∨
      (Fin15AnchoredAtom3335 chi ∧
      ¬Fin15AnchoredAtom0987 chi)) ∨
      ((Fin15AnchoredAtom3335 chi ∧
      ¬Fin15AnchoredAtom0989 chi) ∨
      (Fin15AnchoredAtom3335 chi ∧
      ¬Fin15AnchoredAtom1002 chi))))))) ∨
      ((((((Fin15AnchoredAtom3335 chi ∧
      ¬Fin15AnchoredAtom1030 chi) ∨
      ((Fin15AnchoredAtom3335 chi ∧
      ¬Fin15AnchoredAtom1619 chi) ∨
      (¬Fin15AnchoredAtom3335 chi ∧
      Fin15AnchoredAtom0987 chi ∧
      Fin15AnchoredAtom0989 chi ∧
      Fin15AnchoredAtom1002 chi ∧
      Fin15AnchoredAtom1030 chi ∧
      Fin15AnchoredAtom1619 chi))) ∨
      (((Fin15AnchoredAtom3337 chi ∧
      ¬Fin15AnchoredAtom0987 chi) ∨
      (Fin15AnchoredAtom3337 chi ∧
      ¬Fin15AnchoredAtom0991 chi)) ∨
      ((Fin15AnchoredAtom3337 chi ∧
      ¬Fin15AnchoredAtom1032 chi) ∨
      (Fin15AnchoredAtom3337 chi ∧
      ¬Fin15AnchoredAtom1621 chi)))) ∨
      ((((¬Fin15AnchoredAtom3337 chi ∧
      Fin15AnchoredAtom0987 chi ∧
      Fin15AnchoredAtom0991 chi ∧
      Fin15AnchoredAtom1004 chi ∧
      Fin15AnchoredAtom1032 chi ∧
      Fin15AnchoredAtom1621 chi) ∨
      (Fin15AnchoredAtom3338 chi ∧
      ¬Fin15AnchoredAtom0987 chi)) ∨
      ((Fin15AnchoredAtom3338 chi ∧
      ¬Fin15AnchoredAtom0992 chi) ∨
      (Fin15AnchoredAtom3338 chi ∧
      ¬Fin15AnchoredAtom1005 chi))) ∨
      (((Fin15AnchoredAtom3338 chi ∧
      ¬Fin15AnchoredAtom1033 chi) ∨
      (Fin15AnchoredAtom3338 chi ∧
      ¬Fin15AnchoredAtom1622 chi)) ∨
      ((¬Fin15AnchoredAtom3338 chi ∧
      Fin15AnchoredAtom0987 chi ∧
      Fin15AnchoredAtom0992 chi ∧
      Fin15AnchoredAtom1005 chi ∧
      Fin15AnchoredAtom1033 chi ∧
      Fin15AnchoredAtom1622 chi) ∨
      (Fin15AnchoredAtom3339 chi ∧
      ¬Fin15AnchoredAtom0987 chi))))) ∨
      (((((Fin15AnchoredAtom3339 chi ∧
      ¬Fin15AnchoredAtom0993 chi) ∨
      (Fin15AnchoredAtom3339 chi ∧
      ¬Fin15AnchoredAtom1006 chi)) ∨
      ((Fin15AnchoredAtom3339 chi ∧
      ¬Fin15AnchoredAtom1034 chi) ∨
      (Fin15AnchoredAtom3339 chi ∧
      ¬Fin15AnchoredAtom1623 chi))) ∨
      (((Fin15AnchoredAtom3340 chi ∧
      ¬Fin15AnchoredAtom0988 chi) ∨
      (Fin15AnchoredAtom3340 chi ∧
      ¬Fin15AnchoredAtom0989 chi)) ∨
      ((Fin15AnchoredAtom3340 chi ∧
      ¬Fin15AnchoredAtom1007 chi) ∨
      (Fin15AnchoredAtom3340 chi ∧
      ¬Fin15AnchoredAtom1035 chi)))) ∨
      ((((Fin15AnchoredAtom3340 chi ∧
      ¬Fin15AnchoredAtom1624 chi) ∨
      (¬Fin15AnchoredAtom3340 chi ∧
      Fin15AnchoredAtom0988 chi ∧
      Fin15AnchoredAtom0989 chi ∧
      Fin15AnchoredAtom1007 chi ∧
      Fin15AnchoredAtom1035 chi ∧
      Fin15AnchoredAtom1624 chi)) ∨
      ((Fin15AnchoredAtom3341 chi ∧
      ¬Fin15AnchoredAtom0988 chi) ∨
      (Fin15AnchoredAtom3342 chi ∧
      ¬Fin15AnchoredAtom0988 chi))) ∨
      (((Fin15AnchoredAtom3342 chi ∧
      ¬Fin15AnchoredAtom0991 chi) ∨
      (Fin15AnchoredAtom3342 chi ∧
      ¬Fin15AnchoredAtom1009 chi)) ∨
      ((Fin15AnchoredAtom3342 chi ∧
      ¬Fin15AnchoredAtom1037 chi) ∨
      (Fin15AnchoredAtom3342 chi ∧
      ¬Fin15AnchoredAtom1626 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom3342 chi ∧
      Fin15AnchoredAtom0988 chi ∧
      Fin15AnchoredAtom0991 chi ∧
      Fin15AnchoredAtom1009 chi ∧
      Fin15AnchoredAtom1037 chi ∧
      Fin15AnchoredAtom1626 chi) ∨
      (Fin15AnchoredAtom3343 chi ∧
      ¬Fin15AnchoredAtom0988 chi)) ∨
      ((Fin15AnchoredAtom3343 chi ∧
      ¬Fin15AnchoredAtom0992 chi) ∨
      (Fin15AnchoredAtom3343 chi ∧
      ¬Fin15AnchoredAtom1010 chi))) ∨
      (((Fin15AnchoredAtom3343 chi ∧
      ¬Fin15AnchoredAtom1038 chi) ∨
      (Fin15AnchoredAtom3343 chi ∧
      ¬Fin15AnchoredAtom1627 chi)) ∨
      ((¬Fin15AnchoredAtom3343 chi ∧
      Fin15AnchoredAtom0988 chi ∧
      Fin15AnchoredAtom0992 chi ∧
      Fin15AnchoredAtom1010 chi ∧
      Fin15AnchoredAtom1038 chi ∧
      Fin15AnchoredAtom1627 chi) ∨
      (Fin15AnchoredAtom3344 chi ∧
      ¬Fin15AnchoredAtom0988 chi)))) ∨
      ((((Fin15AnchoredAtom3344 chi ∧
      ¬Fin15AnchoredAtom0993 chi) ∨
      (Fin15AnchoredAtom3344 chi ∧
      ¬Fin15AnchoredAtom1011 chi)) ∨
      ((Fin15AnchoredAtom3344 chi ∧
      ¬Fin15AnchoredAtom1039 chi) ∨
      (Fin15AnchoredAtom3344 chi ∧
      ¬Fin15AnchoredAtom1628 chi))) ∨
      (((¬Fin15AnchoredAtom3344 chi ∧
      Fin15AnchoredAtom0988 chi ∧
      Fin15AnchoredAtom0993 chi ∧
      Fin15AnchoredAtom1011 chi ∧
      Fin15AnchoredAtom1039 chi ∧
      Fin15AnchoredAtom1628 chi) ∨
      (Fin15AnchoredAtom3345 chi ∧
      ¬Fin15AnchoredAtom0990 chi)) ∨
      ((Fin15AnchoredAtom3345 chi ∧
      ¬Fin15AnchoredAtom1040 chi) ∨
      (Fin15AnchoredAtom3345 chi ∧
      ¬Fin15AnchoredAtom1629 chi))))) ∨
      (((((Fin15AnchoredAtom3346 chi ∧
      ¬Fin15AnchoredAtom0989 chi) ∨
      (Fin15AnchoredAtom3346 chi ∧
      ¬Fin15AnchoredAtom0991 chi)) ∨
      ((Fin15AnchoredAtom3346 chi ∧
      ¬Fin15AnchoredAtom1013 chi) ∨
      (Fin15AnchoredAtom3346 chi ∧
      ¬Fin15AnchoredAtom1041 chi))) ∨
      (((Fin15AnchoredAtom3346 chi ∧
      ¬Fin15AnchoredAtom1630 chi) ∨
      (¬Fin15AnchoredAtom3346 chi ∧
      Fin15AnchoredAtom0989 chi ∧
      Fin15AnchoredAtom0991 chi ∧
      Fin15AnchoredAtom1013 chi ∧
      Fin15AnchoredAtom1041 chi ∧
      Fin15AnchoredAtom1630 chi)) ∨
      ((Fin15AnchoredAtom3347 chi ∧
      ¬Fin15AnchoredAtom0989 chi) ∨
      (Fin15AnchoredAtom3347 chi ∧
      ¬Fin15AnchoredAtom0992 chi)))) ∨
      ((((Fin15AnchoredAtom3347 chi ∧
      ¬Fin15AnchoredAtom1014 chi) ∨
      (Fin15AnchoredAtom3347 chi ∧
      ¬Fin15AnchoredAtom1042 chi)) ∨
      ((Fin15AnchoredAtom3347 chi ∧
      ¬Fin15AnchoredAtom1631 chi) ∨
      (¬Fin15AnchoredAtom3347 chi ∧
      Fin15AnchoredAtom0989 chi ∧
      Fin15AnchoredAtom0992 chi ∧
      Fin15AnchoredAtom1014 chi ∧
      Fin15AnchoredAtom1042 chi ∧
      Fin15AnchoredAtom1631 chi))) ∨
      (((Fin15AnchoredAtom3348 chi ∧
      ¬Fin15AnchoredAtom0989 chi) ∨
      (Fin15AnchoredAtom3348 chi ∧
      ¬Fin15AnchoredAtom0993 chi)) ∨
      ((Fin15AnchoredAtom3348 chi ∧
      ¬Fin15AnchoredAtom1015 chi) ∨
      (Fin15AnchoredAtom3348 chi ∧
      ¬Fin15AnchoredAtom1043 chi)))))))) ∨
      (((((((Fin15AnchoredAtom3348 chi ∧
      ¬Fin15AnchoredAtom1632 chi) ∨
      ((¬Fin15AnchoredAtom3348 chi ∧
      Fin15AnchoredAtom0989 chi ∧
      Fin15AnchoredAtom0993 chi ∧
      Fin15AnchoredAtom1015 chi ∧
      Fin15AnchoredAtom1043 chi ∧
      Fin15AnchoredAtom1632 chi) ∨
      (Fin15AnchoredAtom3349 chi ∧
      ¬Fin15AnchoredAtom1633 chi))) ∨
      (((¬Fin15AnchoredAtom3349 chi ∧
      Fin15AnchoredAtom0990 chi ∧
      Fin15AnchoredAtom0991 chi ∧
      Fin15AnchoredAtom1016 chi ∧
      Fin15AnchoredAtom1044 chi ∧
      Fin15AnchoredAtom1633 chi) ∨
      (Fin15AnchoredAtom3352 chi ∧
      ¬Fin15AnchoredAtom0991 chi)) ∨
      ((Fin15AnchoredAtom3352 chi ∧
      ¬Fin15AnchoredAtom0992 chi) ∨
      (Fin15AnchoredAtom3352 chi ∧
      ¬Fin15AnchoredAtom1019 chi)))) ∨
      ((((Fin15AnchoredAtom3352 chi ∧
      ¬Fin15AnchoredAtom1047 chi) ∨
      (Fin15AnchoredAtom3352 chi ∧
      ¬Fin15AnchoredAtom1636 chi)) ∨
      ((¬Fin15AnchoredAtom3352 chi ∧
      Fin15AnchoredAtom0991 chi ∧
      Fin15AnchoredAtom0992 chi ∧
      Fin15AnchoredAtom1019 chi ∧
      Fin15AnchoredAtom1047 chi ∧
      Fin15AnchoredAtom1636 chi) ∨
      (Fin15AnchoredAtom3353 chi ∧
      ¬Fin15AnchoredAtom0991 chi))) ∨
      (((Fin15AnchoredAtom3353 chi ∧
      ¬Fin15AnchoredAtom0993 chi) ∨
      (Fin15AnchoredAtom3353 chi ∧
      ¬Fin15AnchoredAtom1020 chi)) ∨
      ((Fin15AnchoredAtom3353 chi ∧
      ¬Fin15AnchoredAtom1048 chi) ∨
      (Fin15AnchoredAtom3353 chi ∧
      ¬Fin15AnchoredAtom1637 chi))))) ∨
      (((((¬Fin15AnchoredAtom3353 chi ∧
      Fin15AnchoredAtom0991 chi ∧
      Fin15AnchoredAtom0993 chi ∧
      Fin15AnchoredAtom1020 chi ∧
      Fin15AnchoredAtom1048 chi ∧
      Fin15AnchoredAtom1637 chi) ∨
      (Fin15AnchoredAtom3354 chi ∧
      ¬Fin15AnchoredAtom0992 chi)) ∨
      ((Fin15AnchoredAtom3354 chi ∧
      ¬Fin15AnchoredAtom0993 chi) ∨
      (Fin15AnchoredAtom3354 chi ∧
      ¬Fin15AnchoredAtom1021 chi))) ∨
      (((Fin15AnchoredAtom3354 chi ∧
      ¬Fin15AnchoredAtom1049 chi) ∨
      (Fin15AnchoredAtom3354 chi ∧
      ¬Fin15AnchoredAtom1638 chi)) ∨
      ((¬Fin15AnchoredAtom3354 chi ∧
      Fin15AnchoredAtom0992 chi ∧
      Fin15AnchoredAtom0993 chi ∧
      Fin15AnchoredAtom1021 chi ∧
      Fin15AnchoredAtom1049 chi ∧
      Fin15AnchoredAtom1638 chi) ∨
      (Fin15AnchoredAtom3355 chi ∧
      ¬Fin15AnchoredAtom0994 chi)))) ∨
      ((((Fin15AnchoredAtom3355 chi ∧
      ¬Fin15AnchoredAtom0995 chi) ∨
      (Fin15AnchoredAtom3355 chi ∧
      ¬Fin15AnchoredAtom1001 chi)) ∨
      ((Fin15AnchoredAtom3355 chi ∧
      ¬Fin15AnchoredAtom1050 chi) ∨
      (Fin15AnchoredAtom3355 chi ∧
      ¬Fin15AnchoredAtom1639 chi))) ∨
      (((¬Fin15AnchoredAtom3355 chi ∧
      Fin15AnchoredAtom0994 chi ∧
      Fin15AnchoredAtom0995 chi ∧
      Fin15AnchoredAtom1001 chi ∧
      Fin15AnchoredAtom1050 chi ∧
      Fin15AnchoredAtom1639 chi) ∨
      (Fin15AnchoredAtom3356 chi ∧
      ¬Fin15AnchoredAtom0994 chi)) ∨
      ((Fin15AnchoredAtom3356 chi ∧
      ¬Fin15AnchoredAtom0996 chi) ∨
      (Fin15AnchoredAtom3356 chi ∧
      ¬Fin15AnchoredAtom1002 chi)))))) ∨
      ((((((Fin15AnchoredAtom3356 chi ∧
      ¬Fin15AnchoredAtom1051 chi) ∨
      (Fin15AnchoredAtom3356 chi ∧
      ¬Fin15AnchoredAtom1640 chi)) ∨
      ((¬Fin15AnchoredAtom3356 chi ∧
      Fin15AnchoredAtom0994 chi ∧
      Fin15AnchoredAtom0996 chi ∧
      Fin15AnchoredAtom1002 chi ∧
      Fin15AnchoredAtom1051 chi ∧
      Fin15AnchoredAtom1640 chi) ∨
      (Fin15AnchoredAtom3358 chi ∧
      ¬Fin15AnchoredAtom0994 chi))) ∨
      (((Fin15AnchoredAtom3358 chi ∧
      ¬Fin15AnchoredAtom0998 chi) ∨
      (Fin15AnchoredAtom3358 chi ∧
      ¬Fin15AnchoredAtom1053 chi)) ∨
      ((Fin15AnchoredAtom3358 chi ∧
      ¬Fin15AnchoredAtom1642 chi) ∨
      (¬Fin15AnchoredAtom3358 chi ∧
      Fin15AnchoredAtom0994 chi ∧
      Fin15AnchoredAtom0998 chi ∧
      Fin15AnchoredAtom1004 chi ∧
      Fin15AnchoredAtom1053 chi ∧
      Fin15AnchoredAtom1642 chi)))) ∨
      ((((Fin15AnchoredAtom3359 chi ∧
      ¬Fin15AnchoredAtom0994 chi) ∨
      (Fin15AnchoredAtom3359 chi ∧
      ¬Fin15AnchoredAtom0999 chi)) ∨
      ((Fin15AnchoredAtom3359 chi ∧
      ¬Fin15AnchoredAtom1005 chi) ∨
      (Fin15AnchoredAtom3359 chi ∧
      ¬Fin15AnchoredAtom1054 chi))) ∨
      (((Fin15AnchoredAtom3359 chi ∧
      ¬Fin15AnchoredAtom1643 chi) ∨
      (¬Fin15AnchoredAtom3359 chi ∧
      Fin15AnchoredAtom0994 chi ∧
      Fin15AnchoredAtom0999 chi ∧
      Fin15AnchoredAtom1005 chi ∧
      Fin15AnchoredAtom1054 chi ∧
      Fin15AnchoredAtom1643 chi)) ∨
      ((Fin15AnchoredAtom3360 chi ∧
      ¬Fin15AnchoredAtom0994 chi) ∨
      (Fin15AnchoredAtom3360 chi ∧
      ¬Fin15AnchoredAtom1000 chi))))) ∨
      (((((Fin15AnchoredAtom3360 chi ∧
      ¬Fin15AnchoredAtom1006 chi) ∨
      (Fin15AnchoredAtom3360 chi ∧
      ¬Fin15AnchoredAtom1644 chi)) ∨
      ((¬Fin15AnchoredAtom3360 chi ∧
      Fin15AnchoredAtom0994 chi ∧
      Fin15AnchoredAtom1000 chi ∧
      Fin15AnchoredAtom1006 chi ∧
      Fin15AnchoredAtom1055 chi ∧
      Fin15AnchoredAtom1644 chi) ∨
      (Fin15AnchoredAtom3361 chi ∧
      ¬Fin15AnchoredAtom0995 chi))) ∨
      (((Fin15AnchoredAtom3361 chi ∧
      ¬Fin15AnchoredAtom0996 chi) ∨
      (Fin15AnchoredAtom3361 chi ∧
      ¬Fin15AnchoredAtom1007 chi)) ∨
      ((Fin15AnchoredAtom3361 chi ∧
      ¬Fin15AnchoredAtom1056 chi) ∨
      (Fin15AnchoredAtom3361 chi ∧
      ¬Fin15AnchoredAtom1645 chi)))) ∨
      ((((¬Fin15AnchoredAtom3361 chi ∧
      Fin15AnchoredAtom0995 chi ∧
      Fin15AnchoredAtom0996 chi ∧
      Fin15AnchoredAtom1007 chi ∧
      Fin15AnchoredAtom1056 chi ∧
      Fin15AnchoredAtom1645 chi) ∨
      (Fin15AnchoredAtom3362 chi ∧
      ¬Fin15AnchoredAtom0995 chi)) ∨
      ((Fin15AnchoredAtom3362 chi ∧
      ¬Fin15AnchoredAtom1057 chi) ∨
      (Fin15AnchoredAtom3363 chi ∧
      ¬Fin15AnchoredAtom0995 chi))) ∨
      (((Fin15AnchoredAtom3363 chi ∧
      ¬Fin15AnchoredAtom0998 chi) ∨
      (Fin15AnchoredAtom3363 chi ∧
      ¬Fin15AnchoredAtom1009 chi)) ∨
      ((Fin15AnchoredAtom3363 chi ∧
      ¬Fin15AnchoredAtom1058 chi) ∨
      (Fin15AnchoredAtom3363 chi ∧
      ¬Fin15AnchoredAtom1647 chi))))))) ∨
      (((((((¬Fin15AnchoredAtom3363 chi ∧
      Fin15AnchoredAtom0995 chi ∧
      Fin15AnchoredAtom0998 chi ∧
      Fin15AnchoredAtom1009 chi ∧
      Fin15AnchoredAtom1058 chi ∧
      Fin15AnchoredAtom1647 chi) ∨
      (Fin15AnchoredAtom3364 chi ∧
      ¬Fin15AnchoredAtom0995 chi)) ∨
      ((Fin15AnchoredAtom3364 chi ∧
      ¬Fin15AnchoredAtom0999 chi) ∨
      (Fin15AnchoredAtom3364 chi ∧
      ¬Fin15AnchoredAtom1010 chi))) ∨
      (((Fin15AnchoredAtom3364 chi ∧
      ¬Fin15AnchoredAtom1059 chi) ∨
      (Fin15AnchoredAtom3364 chi ∧
      ¬Fin15AnchoredAtom1648 chi)) ∨
      ((¬Fin15AnchoredAtom3364 chi ∧
      Fin15AnchoredAtom0995 chi ∧
      Fin15AnchoredAtom0999 chi ∧
      Fin15AnchoredAtom1010 chi ∧
      Fin15AnchoredAtom1059 chi ∧
      Fin15AnchoredAtom1648 chi) ∨
      (Fin15AnchoredAtom3365 chi ∧
      ¬Fin15AnchoredAtom0995 chi)))) ∨
      ((((Fin15AnchoredAtom3365 chi ∧
      ¬Fin15AnchoredAtom1000 chi) ∨
      (Fin15AnchoredAtom3365 chi ∧
      ¬Fin15AnchoredAtom1011 chi)) ∨
      ((Fin15AnchoredAtom3365 chi ∧
      ¬Fin15AnchoredAtom1060 chi) ∨
      (Fin15AnchoredAtom3365 chi ∧
      ¬Fin15AnchoredAtom1649 chi))) ∨
      (((¬Fin15AnchoredAtom3365 chi ∧
      Fin15AnchoredAtom0995 chi ∧
      Fin15AnchoredAtom1000 chi ∧
      Fin15AnchoredAtom1011 chi ∧
      Fin15AnchoredAtom1060 chi ∧
      Fin15AnchoredAtom1649 chi) ∨
      (Fin15AnchoredAtom3366 chi ∧
      ¬Fin15AnchoredAtom0997 chi)) ∨
      ((Fin15AnchoredAtom3366 chi ∧
      ¬Fin15AnchoredAtom1061 chi) ∨
      (Fin15AnchoredAtom3367 chi ∧
      ¬Fin15AnchoredAtom0996 chi))))) ∨
      (((((Fin15AnchoredAtom3367 chi ∧
      ¬Fin15AnchoredAtom0998 chi) ∨
      (Fin15AnchoredAtom3367 chi ∧
      ¬Fin15AnchoredAtom1013 chi)) ∨
      ((Fin15AnchoredAtom3367 chi ∧
      ¬Fin15AnchoredAtom1062 chi) ∨
      (Fin15AnchoredAtom3367 chi ∧
      ¬Fin15AnchoredAtom1651 chi))) ∨
      (((¬Fin15AnchoredAtom3367 chi ∧
      Fin15AnchoredAtom0996 chi ∧
      Fin15AnchoredAtom0998 chi ∧
      Fin15AnchoredAtom1013 chi ∧
      Fin15AnchoredAtom1062 chi ∧
      Fin15AnchoredAtom1651 chi) ∨
      (Fin15AnchoredAtom3368 chi ∧
      ¬Fin15AnchoredAtom0996 chi)) ∨
      ((Fin15AnchoredAtom3368 chi ∧
      ¬Fin15AnchoredAtom0999 chi) ∨
      (Fin15AnchoredAtom3368 chi ∧
      ¬Fin15AnchoredAtom1014 chi)))) ∨
      ((((Fin15AnchoredAtom3368 chi ∧
      ¬Fin15AnchoredAtom1063 chi) ∨
      (Fin15AnchoredAtom3368 chi ∧
      ¬Fin15AnchoredAtom1652 chi)) ∨
      ((¬Fin15AnchoredAtom3368 chi ∧
      Fin15AnchoredAtom0996 chi ∧
      Fin15AnchoredAtom0999 chi ∧
      Fin15AnchoredAtom1014 chi ∧
      Fin15AnchoredAtom1063 chi ∧
      Fin15AnchoredAtom1652 chi) ∨
      (Fin15AnchoredAtom3369 chi ∧
      ¬Fin15AnchoredAtom0996 chi))) ∨
      (((Fin15AnchoredAtom3369 chi ∧
      ¬Fin15AnchoredAtom1000 chi) ∨
      (Fin15AnchoredAtom3369 chi ∧
      ¬Fin15AnchoredAtom1015 chi)) ∨
      ((Fin15AnchoredAtom3369 chi ∧
      ¬Fin15AnchoredAtom1064 chi) ∨
      (Fin15AnchoredAtom3369 chi ∧
      ¬Fin15AnchoredAtom1653 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom3369 chi ∧
      Fin15AnchoredAtom0996 chi ∧
      Fin15AnchoredAtom1000 chi ∧
      Fin15AnchoredAtom1015 chi ∧
      Fin15AnchoredAtom1064 chi ∧
      Fin15AnchoredAtom1653 chi) ∨
      (Fin15AnchoredAtom3370 chi ∧
      ¬Fin15AnchoredAtom0998 chi)) ∨
      ((Fin15AnchoredAtom3370 chi ∧
      ¬Fin15AnchoredAtom1065 chi) ∨
      (Fin15AnchoredAtom3370 chi ∧
      ¬Fin15AnchoredAtom1654 chi))) ∨
      (((Fin15AnchoredAtom3371 chi ∧
      ¬Fin15AnchoredAtom0999 chi) ∨
      (Fin15AnchoredAtom3372 chi ∧
      ¬Fin15AnchoredAtom1000 chi)) ∨
      ((Fin15AnchoredAtom3373 chi ∧
      ¬Fin15AnchoredAtom0998 chi) ∨
      (Fin15AnchoredAtom3373 chi ∧
      ¬Fin15AnchoredAtom0999 chi)))) ∨
      ((((Fin15AnchoredAtom3373 chi ∧
      ¬Fin15AnchoredAtom1019 chi) ∨
      (Fin15AnchoredAtom3373 chi ∧
      ¬Fin15AnchoredAtom1068 chi)) ∨
      ((Fin15AnchoredAtom3373 chi ∧
      ¬Fin15AnchoredAtom1657 chi) ∨
      (¬Fin15AnchoredAtom3373 chi ∧
      Fin15AnchoredAtom0998 chi ∧
      Fin15AnchoredAtom0999 chi ∧
      Fin15AnchoredAtom1019 chi ∧
      Fin15AnchoredAtom1068 chi ∧
      Fin15AnchoredAtom1657 chi))) ∨
      (((Fin15AnchoredAtom3374 chi ∧
      ¬Fin15AnchoredAtom0998 chi) ∨
      (Fin15AnchoredAtom3374 chi ∧
      ¬Fin15AnchoredAtom1000 chi)) ∨
      ((Fin15AnchoredAtom3374 chi ∧
      ¬Fin15AnchoredAtom1020 chi) ∨
      (Fin15AnchoredAtom3374 chi ∧
      ¬Fin15AnchoredAtom1069 chi))))) ∨
      (((((Fin15AnchoredAtom3374 chi ∧
      ¬Fin15AnchoredAtom1658 chi) ∨
      (¬Fin15AnchoredAtom3374 chi ∧
      Fin15AnchoredAtom0998 chi ∧
      Fin15AnchoredAtom1000 chi ∧
      Fin15AnchoredAtom1020 chi ∧
      Fin15AnchoredAtom1069 chi ∧
      Fin15AnchoredAtom1658 chi)) ∨
      ((Fin15AnchoredAtom3375 chi ∧
      ¬Fin15AnchoredAtom0999 chi) ∨
      (Fin15AnchoredAtom3375 chi ∧
      ¬Fin15AnchoredAtom1000 chi))) ∨
      (((Fin15AnchoredAtom3375 chi ∧
      ¬Fin15AnchoredAtom1021 chi) ∨
      (Fin15AnchoredAtom3375 chi ∧
      ¬Fin15AnchoredAtom1070 chi)) ∨
      ((Fin15AnchoredAtom3375 chi ∧
      ¬Fin15AnchoredAtom1659 chi) ∨
      (¬Fin15AnchoredAtom3375 chi ∧
      Fin15AnchoredAtom0999 chi ∧
      Fin15AnchoredAtom1000 chi ∧
      Fin15AnchoredAtom1021 chi ∧
      Fin15AnchoredAtom1070 chi ∧
      Fin15AnchoredAtom1659 chi)))) ∨
      ((((Fin15AnchoredAtom3376 chi ∧
      ¬Fin15AnchoredAtom1001 chi) ∨
      (Fin15AnchoredAtom3376 chi ∧
      ¬Fin15AnchoredAtom1002 chi)) ∨
      ((Fin15AnchoredAtom3376 chi ∧
      ¬Fin15AnchoredAtom1007 chi) ∨
      (Fin15AnchoredAtom3376 chi ∧
      ¬Fin15AnchoredAtom1071 chi))) ∨
      (((Fin15AnchoredAtom3376 chi ∧
      ¬Fin15AnchoredAtom1660 chi) ∨
      (¬Fin15AnchoredAtom3376 chi ∧
      Fin15AnchoredAtom1001 chi ∧
      Fin15AnchoredAtom1002 chi ∧
      Fin15AnchoredAtom1007 chi ∧
      Fin15AnchoredAtom1071 chi ∧
      Fin15AnchoredAtom1660 chi)) ∨
      ((Fin15AnchoredAtom3378 chi ∧
      ¬Fin15AnchoredAtom1001 chi) ∨
      (Fin15AnchoredAtom3378 chi ∧
      ¬Fin15AnchoredAtom1004 chi)))))))))) := by
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
                exact fin15Anchored_clause22463 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22464 chi hbad
                ·
                  exact fin15Anchored_clause22465 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22466 chi hbad
                ·
                  exact fin15Anchored_clause22467 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22468 chi hbad
                ·
                  exact fin15Anchored_clause22469 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22470 chi hbad
                ·
                  exact fin15Anchored_clause22471 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22472 chi hbad
                ·
                  exact fin15Anchored_clause22473 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22474 chi hbad
                ·
                  exact fin15Anchored_clause22475 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22476 chi hbad
                ·
                  exact fin15Anchored_clause22477 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22478 chi hbad
                ·
                  exact fin15Anchored_clause22479 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22480 chi hbad
                ·
                  exact fin15Anchored_clause22481 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22482 chi hbad
                ·
                  exact fin15Anchored_clause22483 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22484 chi hbad
                ·
                  exact fin15Anchored_clause22485 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22486 chi hbad
                ·
                  exact fin15Anchored_clause22487 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22488 chi hbad
                ·
                  exact fin15Anchored_clause22489 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22490 chi hbad
                ·
                  exact fin15Anchored_clause22491 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22492 chi hbad
                ·
                  exact fin15Anchored_clause22493 chi hbad
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
                  exact fin15Anchored_clause22494 chi hbad
                ·
                  exact fin15Anchored_clause22495 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22496 chi hbad
                ·
                  exact fin15Anchored_clause22497 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22498 chi hbad
                ·
                  exact fin15Anchored_clause22499 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22500 chi hbad
                ·
                  exact fin15Anchored_clause22501 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22502 chi hbad
                ·
                  exact fin15Anchored_clause22503 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22504 chi hbad
                ·
                  exact fin15Anchored_clause22505 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22506 chi hbad
                ·
                  exact fin15Anchored_clause22507 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22508 chi hbad
                ·
                  exact fin15Anchored_clause22509 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22510 chi hbad
                ·
                  exact fin15Anchored_clause22511 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22512 chi hbad
                ·
                  exact fin15Anchored_clause22513 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22514 chi hbad
                ·
                  exact fin15Anchored_clause22515 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22516 chi hbad
                ·
                  exact fin15Anchored_clause22517 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22518 chi hbad
                ·
                  exact fin15Anchored_clause22519 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22520 chi hbad
                ·
                  exact fin15Anchored_clause22521 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22522 chi hbad
                ·
                  exact fin15Anchored_clause22523 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22524 chi hbad
                ·
                  exact fin15Anchored_clause22525 chi hbad
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
                exact fin15Anchored_clause22526 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22527 chi hbad
                ·
                  exact fin15Anchored_clause22528 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22529 chi hbad
                ·
                  exact fin15Anchored_clause22530 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22531 chi hbad
                ·
                  exact fin15Anchored_clause22532 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22533 chi hbad
                ·
                  exact fin15Anchored_clause22534 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22535 chi hbad
                ·
                  exact fin15Anchored_clause22536 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22537 chi hbad
                ·
                  exact fin15Anchored_clause22538 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22539 chi hbad
                ·
                  exact fin15Anchored_clause22540 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22541 chi hbad
                ·
                  exact fin15Anchored_clause22542 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22543 chi hbad
                ·
                  exact fin15Anchored_clause22544 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22545 chi hbad
                ·
                  exact fin15Anchored_clause22546 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22547 chi hbad
                ·
                  exact fin15Anchored_clause22548 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22549 chi hbad
                ·
                  exact fin15Anchored_clause22550 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22551 chi hbad
                ·
                  exact fin15Anchored_clause22552 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22553 chi hbad
                ·
                  exact fin15Anchored_clause22554 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22555 chi hbad
                ·
                  exact fin15Anchored_clause22556 chi hbad
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
                  exact fin15Anchored_clause22557 chi hbad
                ·
                  exact fin15Anchored_clause22558 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22559 chi hbad
                ·
                  exact fin15Anchored_clause22560 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22561 chi hbad
                ·
                  exact fin15Anchored_clause22562 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22563 chi hbad
                ·
                  exact fin15Anchored_clause22564 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22565 chi hbad
                ·
                  exact fin15Anchored_clause22566 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22567 chi hbad
                ·
                  exact fin15Anchored_clause22568 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22569 chi hbad
                ·
                  exact fin15Anchored_clause22570 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22571 chi hbad
                ·
                  exact fin15Anchored_clause22572 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22573 chi hbad
                ·
                  exact fin15Anchored_clause22574 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22575 chi hbad
                ·
                  exact fin15Anchored_clause22576 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22577 chi hbad
                ·
                  exact fin15Anchored_clause22578 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22579 chi hbad
                ·
                  exact fin15Anchored_clause22580 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22581 chi hbad
                ·
                  exact fin15Anchored_clause22582 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22583 chi hbad
                ·
                  exact fin15Anchored_clause22584 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22585 chi hbad
                ·
                  exact fin15Anchored_clause22586 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22587 chi hbad
                ·
                  exact fin15Anchored_clause22588 chi hbad
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
                exact fin15Anchored_clause22589 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22590 chi hbad
                ·
                  exact fin15Anchored_clause22591 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22592 chi hbad
                ·
                  exact fin15Anchored_clause22593 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22594 chi hbad
                ·
                  exact fin15Anchored_clause22595 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22596 chi hbad
                ·
                  exact fin15Anchored_clause22597 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22598 chi hbad
                ·
                  exact fin15Anchored_clause22599 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22600 chi hbad
                ·
                  exact fin15Anchored_clause22601 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22602 chi hbad
                ·
                  exact fin15Anchored_clause22603 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22604 chi hbad
                ·
                  exact fin15Anchored_clause22605 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22606 chi hbad
                ·
                  exact fin15Anchored_clause22607 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22608 chi hbad
                ·
                  exact fin15Anchored_clause22609 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22610 chi hbad
                ·
                  exact fin15Anchored_clause22611 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22612 chi hbad
                ·
                  exact fin15Anchored_clause22613 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22614 chi hbad
                ·
                  exact fin15Anchored_clause22615 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22616 chi hbad
                ·
                  exact fin15Anchored_clause22617 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22618 chi hbad
                ·
                  exact fin15Anchored_clause22619 chi hbad
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
                  exact fin15Anchored_clause22620 chi hbad
                ·
                  exact fin15Anchored_clause22621 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22622 chi hbad
                ·
                  exact fin15Anchored_clause22623 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22624 chi hbad
                ·
                  exact fin15Anchored_clause22625 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22626 chi hbad
                ·
                  exact fin15Anchored_clause22627 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22628 chi hbad
                ·
                  exact fin15Anchored_clause22629 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22630 chi hbad
                ·
                  exact fin15Anchored_clause22631 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22632 chi hbad
                ·
                  exact fin15Anchored_clause22633 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22634 chi hbad
                ·
                  exact fin15Anchored_clause22635 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22636 chi hbad
                ·
                  exact fin15Anchored_clause22637 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22638 chi hbad
                ·
                  exact fin15Anchored_clause22639 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22640 chi hbad
                ·
                  exact fin15Anchored_clause22641 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22642 chi hbad
                ·
                  exact fin15Anchored_clause22643 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22644 chi hbad
                ·
                  exact fin15Anchored_clause22645 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22646 chi hbad
                ·
                  exact fin15Anchored_clause22647 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22648 chi hbad
                ·
                  exact fin15Anchored_clause22649 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22650 chi hbad
                ·
                  exact fin15Anchored_clause22651 chi hbad
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
                  exact fin15Anchored_clause22652 chi hbad
                ·
                  exact fin15Anchored_clause22653 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22654 chi hbad
                ·
                  exact fin15Anchored_clause22655 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22656 chi hbad
                ·
                  exact fin15Anchored_clause22657 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22658 chi hbad
                ·
                  exact fin15Anchored_clause22659 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22660 chi hbad
                ·
                  exact fin15Anchored_clause22661 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22662 chi hbad
                ·
                  exact fin15Anchored_clause22663 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22664 chi hbad
                ·
                  exact fin15Anchored_clause22665 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22666 chi hbad
                ·
                  exact fin15Anchored_clause22667 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22668 chi hbad
                ·
                  exact fin15Anchored_clause22669 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22670 chi hbad
                ·
                  exact fin15Anchored_clause22671 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22672 chi hbad
                ·
                  exact fin15Anchored_clause22673 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22674 chi hbad
                ·
                  exact fin15Anchored_clause22675 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22676 chi hbad
                ·
                  exact fin15Anchored_clause22677 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22678 chi hbad
                ·
                  exact fin15Anchored_clause22679 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22680 chi hbad
                ·
                  exact fin15Anchored_clause22681 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22682 chi hbad
                ·
                  exact fin15Anchored_clause22683 chi hbad
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
                  exact fin15Anchored_clause22684 chi hbad
                ·
                  exact fin15Anchored_clause22685 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22686 chi hbad
                ·
                  exact fin15Anchored_clause22687 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22688 chi hbad
                ·
                  exact fin15Anchored_clause22689 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22690 chi hbad
                ·
                  exact fin15Anchored_clause22691 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22692 chi hbad
                ·
                  exact fin15Anchored_clause22693 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22694 chi hbad
                ·
                  exact fin15Anchored_clause22695 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22696 chi hbad
                ·
                  exact fin15Anchored_clause22697 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22698 chi hbad
                ·
                  exact fin15Anchored_clause22699 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22700 chi hbad
                ·
                  exact fin15Anchored_clause22701 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22702 chi hbad
                ·
                  exact fin15Anchored_clause22703 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22704 chi hbad
                ·
                  exact fin15Anchored_clause22705 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22706 chi hbad
                ·
                  exact fin15Anchored_clause22707 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22708 chi hbad
                ·
                  exact fin15Anchored_clause22709 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22710 chi hbad
                ·
                  exact fin15Anchored_clause22711 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22712 chi hbad
                ·
                  exact fin15Anchored_clause22713 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22714 chi hbad
                ·
                  exact fin15Anchored_clause22715 chi hbad

end ErdosSzekeres

end
