module

public import ErdosSzekeres.Fin15AnchoredClauseChunk128
public import ErdosSzekeres.Fin15AnchoredClauseChunk129
public import ErdosSzekeres.Fin15AnchoredClauseChunk130

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 065. -/

theorem fin15Anchored_rejectSemanticSegment065
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom2014 chi ∧
      ¬Fin15AnchoredAtom0727 chi) ∨
      ((Fin15AnchoredAtom2014 chi ∧
      ¬Fin15AnchoredAtom1013 chi) ∨
      (¬Fin15AnchoredAtom2014 chi ∧
      Fin15AnchoredAtom0493 chi ∧
      Fin15AnchoredAtom0495 chi ∧
      Fin15AnchoredAtom0525 chi ∧
      Fin15AnchoredAtom0727 chi ∧
      Fin15AnchoredAtom1013 chi))) ∨
      (((Fin15AnchoredAtom2015 chi ∧
      ¬Fin15AnchoredAtom0493 chi) ∨
      (Fin15AnchoredAtom2015 chi ∧
      ¬Fin15AnchoredAtom0496 chi)) ∨
      ((Fin15AnchoredAtom2015 chi ∧
      ¬Fin15AnchoredAtom0526 chi) ∨
      (Fin15AnchoredAtom2015 chi ∧
      ¬Fin15AnchoredAtom0728 chi)))) ∨
      ((((Fin15AnchoredAtom2015 chi ∧
      ¬Fin15AnchoredAtom1014 chi) ∨
      (¬Fin15AnchoredAtom2015 chi ∧
      Fin15AnchoredAtom0493 chi ∧
      Fin15AnchoredAtom0496 chi ∧
      Fin15AnchoredAtom0526 chi ∧
      Fin15AnchoredAtom0728 chi ∧
      Fin15AnchoredAtom1014 chi)) ∨
      ((Fin15AnchoredAtom2016 chi ∧
      ¬Fin15AnchoredAtom0493 chi) ∨
      (Fin15AnchoredAtom2016 chi ∧
      ¬Fin15AnchoredAtom0497 chi))) ∨
      (((Fin15AnchoredAtom2016 chi ∧
      ¬Fin15AnchoredAtom0527 chi) ∨
      (Fin15AnchoredAtom2016 chi ∧
      ¬Fin15AnchoredAtom0729 chi)) ∨
      ((Fin15AnchoredAtom2016 chi ∧
      ¬Fin15AnchoredAtom1015 chi) ∨
      (¬Fin15AnchoredAtom2016 chi ∧
      Fin15AnchoredAtom0493 chi ∧
      Fin15AnchoredAtom0497 chi ∧
      Fin15AnchoredAtom0527 chi ∧
      Fin15AnchoredAtom0729 chi ∧
      Fin15AnchoredAtom1015 chi))))) ∨
      (((((Fin15AnchoredAtom2017 chi ∧
      ¬Fin15AnchoredAtom0495 chi) ∨
      (Fin15AnchoredAtom2017 chi ∧
      ¬Fin15AnchoredAtom0528 chi)) ∨
      ((Fin15AnchoredAtom2018 chi ∧
      ¬Fin15AnchoredAtom1017 chi) ∨
      (¬Fin15AnchoredAtom2018 chi ∧
      Fin15AnchoredAtom0494 chi ∧
      Fin15AnchoredAtom0496 chi ∧
      Fin15AnchoredAtom0529 chi ∧
      Fin15AnchoredAtom0731 chi ∧
      Fin15AnchoredAtom1017 chi))) ∨
      (((Fin15AnchoredAtom2019 chi ∧
      ¬Fin15AnchoredAtom0497 chi) ∨
      (Fin15AnchoredAtom2020 chi ∧
      ¬Fin15AnchoredAtom0495 chi)) ∨
      ((Fin15AnchoredAtom2020 chi ∧
      ¬Fin15AnchoredAtom0496 chi) ∨
      (Fin15AnchoredAtom2020 chi ∧
      ¬Fin15AnchoredAtom0531 chi)))) ∨
      ((((Fin15AnchoredAtom2020 chi ∧
      ¬Fin15AnchoredAtom0733 chi) ∨
      (Fin15AnchoredAtom2020 chi ∧
      ¬Fin15AnchoredAtom1019 chi)) ∨
      ((¬Fin15AnchoredAtom2020 chi ∧
      Fin15AnchoredAtom0495 chi ∧
      Fin15AnchoredAtom0496 chi ∧
      Fin15AnchoredAtom0531 chi ∧
      Fin15AnchoredAtom0733 chi ∧
      Fin15AnchoredAtom1019 chi) ∨
      (Fin15AnchoredAtom2021 chi ∧
      ¬Fin15AnchoredAtom0495 chi))) ∨
      (((Fin15AnchoredAtom2021 chi ∧
      ¬Fin15AnchoredAtom0497 chi) ∨
      (Fin15AnchoredAtom2021 chi ∧
      ¬Fin15AnchoredAtom0532 chi)) ∨
      ((Fin15AnchoredAtom2021 chi ∧
      ¬Fin15AnchoredAtom0734 chi) ∨
      (Fin15AnchoredAtom2021 chi ∧
      ¬Fin15AnchoredAtom1020 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom2021 chi ∧
      Fin15AnchoredAtom0495 chi ∧
      Fin15AnchoredAtom0497 chi ∧
      Fin15AnchoredAtom0532 chi ∧
      Fin15AnchoredAtom0734 chi ∧
      Fin15AnchoredAtom1020 chi) ∨
      (Fin15AnchoredAtom2022 chi ∧
      ¬Fin15AnchoredAtom0496 chi)) ∨
      ((Fin15AnchoredAtom2022 chi ∧
      ¬Fin15AnchoredAtom0497 chi) ∨
      (Fin15AnchoredAtom2022 chi ∧
      ¬Fin15AnchoredAtom0533 chi))) ∨
      (((Fin15AnchoredAtom2022 chi ∧
      ¬Fin15AnchoredAtom0735 chi) ∨
      (Fin15AnchoredAtom2022 chi ∧
      ¬Fin15AnchoredAtom1021 chi)) ∨
      ((¬Fin15AnchoredAtom2022 chi ∧
      Fin15AnchoredAtom0496 chi ∧
      Fin15AnchoredAtom0497 chi ∧
      Fin15AnchoredAtom0533 chi ∧
      Fin15AnchoredAtom0735 chi ∧
      Fin15AnchoredAtom1021 chi) ∨
      (Fin15AnchoredAtom2023 chi ∧
      ¬Fin15AnchoredAtom0498 chi)))) ∨
      ((((Fin15AnchoredAtom2023 chi ∧
      ¬Fin15AnchoredAtom0736 chi) ∨
      (Fin15AnchoredAtom2023 chi ∧
      ¬Fin15AnchoredAtom1022 chi)) ∨
      ((¬Fin15AnchoredAtom2023 chi ∧
      Fin15AnchoredAtom0498 chi ∧
      Fin15AnchoredAtom0499 chi ∧
      Fin15AnchoredAtom0506 chi ∧
      Fin15AnchoredAtom0736 chi ∧
      Fin15AnchoredAtom1022 chi) ∨
      (Fin15AnchoredAtom2024 chi ∧
      ¬Fin15AnchoredAtom0498 chi))) ∨
      (((Fin15AnchoredAtom2024 chi ∧
      ¬Fin15AnchoredAtom0500 chi) ∨
      (Fin15AnchoredAtom2024 chi ∧
      ¬Fin15AnchoredAtom0507 chi)) ∨
      ((Fin15AnchoredAtom2024 chi ∧
      ¬Fin15AnchoredAtom0737 chi) ∨
      (Fin15AnchoredAtom2024 chi ∧
      ¬Fin15AnchoredAtom1023 chi))))) ∨
      (((((¬Fin15AnchoredAtom2024 chi ∧
      Fin15AnchoredAtom0498 chi ∧
      Fin15AnchoredAtom0500 chi ∧
      Fin15AnchoredAtom0507 chi ∧
      Fin15AnchoredAtom0737 chi ∧
      Fin15AnchoredAtom1023 chi) ∨
      (Fin15AnchoredAtom2025 chi ∧
      ¬Fin15AnchoredAtom0498 chi)) ∨
      ((Fin15AnchoredAtom2025 chi ∧
      ¬Fin15AnchoredAtom0501 chi) ∨
      (Fin15AnchoredAtom2025 chi ∧
      ¬Fin15AnchoredAtom0508 chi))) ∨
      (((Fin15AnchoredAtom2025 chi ∧
      ¬Fin15AnchoredAtom0738 chi) ∨
      (Fin15AnchoredAtom2025 chi ∧
      ¬Fin15AnchoredAtom1024 chi)) ∨
      ((¬Fin15AnchoredAtom2025 chi ∧
      Fin15AnchoredAtom0498 chi ∧
      Fin15AnchoredAtom0501 chi ∧
      Fin15AnchoredAtom0508 chi ∧
      Fin15AnchoredAtom0738 chi ∧
      Fin15AnchoredAtom1024 chi) ∨
      (Fin15AnchoredAtom2026 chi ∧
      ¬Fin15AnchoredAtom0498 chi)))) ∨
      ((((Fin15AnchoredAtom2026 chi ∧
      ¬Fin15AnchoredAtom0739 chi) ∨
      (Fin15AnchoredAtom2027 chi ∧
      ¬Fin15AnchoredAtom0498 chi)) ∨
      ((Fin15AnchoredAtom2027 chi ∧
      ¬Fin15AnchoredAtom0503 chi) ∨
      (Fin15AnchoredAtom2027 chi ∧
      ¬Fin15AnchoredAtom0510 chi))) ∨
      (((Fin15AnchoredAtom2027 chi ∧
      ¬Fin15AnchoredAtom0740 chi) ∨
      (Fin15AnchoredAtom2027 chi ∧
      ¬Fin15AnchoredAtom1026 chi)) ∨
      ((¬Fin15AnchoredAtom2027 chi ∧
      Fin15AnchoredAtom0498 chi ∧
      Fin15AnchoredAtom0503 chi ∧
      Fin15AnchoredAtom0510 chi ∧
      Fin15AnchoredAtom0740 chi ∧
      Fin15AnchoredAtom1026 chi) ∨
      (Fin15AnchoredAtom2028 chi ∧
      ¬Fin15AnchoredAtom0498 chi))))))) ∨
      ((((((Fin15AnchoredAtom2028 chi ∧
      ¬Fin15AnchoredAtom0504 chi) ∨
      ((Fin15AnchoredAtom2028 chi ∧
      ¬Fin15AnchoredAtom0511 chi) ∨
      (Fin15AnchoredAtom2028 chi ∧
      ¬Fin15AnchoredAtom0741 chi))) ∨
      (((Fin15AnchoredAtom2028 chi ∧
      ¬Fin15AnchoredAtom1027 chi) ∨
      (¬Fin15AnchoredAtom2028 chi ∧
      Fin15AnchoredAtom0498 chi ∧
      Fin15AnchoredAtom0504 chi ∧
      Fin15AnchoredAtom0511 chi ∧
      Fin15AnchoredAtom0741 chi ∧
      Fin15AnchoredAtom1027 chi)) ∨
      ((Fin15AnchoredAtom2029 chi ∧
      ¬Fin15AnchoredAtom0498 chi) ∨
      (Fin15AnchoredAtom2029 chi ∧
      ¬Fin15AnchoredAtom0505 chi)))) ∨
      ((((Fin15AnchoredAtom2029 chi ∧
      ¬Fin15AnchoredAtom0512 chi) ∨
      (Fin15AnchoredAtom2029 chi ∧
      ¬Fin15AnchoredAtom0742 chi)) ∨
      ((Fin15AnchoredAtom2029 chi ∧
      ¬Fin15AnchoredAtom1028 chi) ∨
      (¬Fin15AnchoredAtom2029 chi ∧
      Fin15AnchoredAtom0498 chi ∧
      Fin15AnchoredAtom0505 chi ∧
      Fin15AnchoredAtom0512 chi ∧
      Fin15AnchoredAtom0742 chi ∧
      Fin15AnchoredAtom1028 chi))) ∨
      (((Fin15AnchoredAtom2030 chi ∧
      ¬Fin15AnchoredAtom0499 chi) ∨
      (Fin15AnchoredAtom2030 chi ∧
      ¬Fin15AnchoredAtom0500 chi)) ∨
      ((Fin15AnchoredAtom2030 chi ∧
      ¬Fin15AnchoredAtom0513 chi) ∨
      (Fin15AnchoredAtom2030 chi ∧
      ¬Fin15AnchoredAtom0743 chi))))) ∨
      (((((Fin15AnchoredAtom2030 chi ∧
      ¬Fin15AnchoredAtom1029 chi) ∨
      (¬Fin15AnchoredAtom2030 chi ∧
      Fin15AnchoredAtom0499 chi ∧
      Fin15AnchoredAtom0500 chi ∧
      Fin15AnchoredAtom0513 chi ∧
      Fin15AnchoredAtom0743 chi ∧
      Fin15AnchoredAtom1029 chi)) ∨
      ((Fin15AnchoredAtom2031 chi ∧
      ¬Fin15AnchoredAtom0499 chi) ∨
      (Fin15AnchoredAtom2031 chi ∧
      ¬Fin15AnchoredAtom0501 chi))) ∨
      (((Fin15AnchoredAtom2031 chi ∧
      ¬Fin15AnchoredAtom0744 chi) ∨
      (¬Fin15AnchoredAtom2031 chi ∧
      Fin15AnchoredAtom0499 chi ∧
      Fin15AnchoredAtom0501 chi ∧
      Fin15AnchoredAtom0514 chi ∧
      Fin15AnchoredAtom0744 chi ∧
      Fin15AnchoredAtom1030 chi)) ∨
      ((Fin15AnchoredAtom2033 chi ∧
      ¬Fin15AnchoredAtom0499 chi) ∨
      (Fin15AnchoredAtom2033 chi ∧
      ¬Fin15AnchoredAtom0503 chi)))) ∨
      ((((Fin15AnchoredAtom2033 chi ∧
      ¬Fin15AnchoredAtom0516 chi) ∨
      (Fin15AnchoredAtom2033 chi ∧
      ¬Fin15AnchoredAtom0746 chi)) ∨
      ((Fin15AnchoredAtom2033 chi ∧
      ¬Fin15AnchoredAtom1032 chi) ∨
      (¬Fin15AnchoredAtom2033 chi ∧
      Fin15AnchoredAtom0499 chi ∧
      Fin15AnchoredAtom0503 chi ∧
      Fin15AnchoredAtom0516 chi ∧
      Fin15AnchoredAtom0746 chi ∧
      Fin15AnchoredAtom1032 chi))) ∨
      (((Fin15AnchoredAtom2034 chi ∧
      ¬Fin15AnchoredAtom0499 chi) ∨
      (Fin15AnchoredAtom2034 chi ∧
      ¬Fin15AnchoredAtom0504 chi)) ∨
      ((Fin15AnchoredAtom2034 chi ∧
      ¬Fin15AnchoredAtom0517 chi) ∨
      (Fin15AnchoredAtom2034 chi ∧
      ¬Fin15AnchoredAtom0747 chi)))))) ∨
      ((((((Fin15AnchoredAtom2034 chi ∧
      ¬Fin15AnchoredAtom1033 chi) ∨
      (¬Fin15AnchoredAtom2034 chi ∧
      Fin15AnchoredAtom0499 chi ∧
      Fin15AnchoredAtom0504 chi ∧
      Fin15AnchoredAtom0517 chi ∧
      Fin15AnchoredAtom0747 chi ∧
      Fin15AnchoredAtom1033 chi)) ∨
      ((Fin15AnchoredAtom2035 chi ∧
      ¬Fin15AnchoredAtom0499 chi) ∨
      (Fin15AnchoredAtom2035 chi ∧
      ¬Fin15AnchoredAtom0505 chi))) ∨
      (((Fin15AnchoredAtom2035 chi ∧
      ¬Fin15AnchoredAtom0518 chi) ∨
      (Fin15AnchoredAtom2035 chi ∧
      ¬Fin15AnchoredAtom0748 chi)) ∨
      ((Fin15AnchoredAtom2035 chi ∧
      ¬Fin15AnchoredAtom1034 chi) ∨
      (¬Fin15AnchoredAtom2035 chi ∧
      Fin15AnchoredAtom0499 chi ∧
      Fin15AnchoredAtom0505 chi ∧
      Fin15AnchoredAtom0518 chi ∧
      Fin15AnchoredAtom0748 chi ∧
      Fin15AnchoredAtom1034 chi)))) ∨
      ((((Fin15AnchoredAtom2036 chi ∧
      ¬Fin15AnchoredAtom0500 chi) ∨
      (Fin15AnchoredAtom2036 chi ∧
      ¬Fin15AnchoredAtom0501 chi)) ∨
      ((Fin15AnchoredAtom2036 chi ∧
      ¬Fin15AnchoredAtom0519 chi) ∨
      (Fin15AnchoredAtom2036 chi ∧
      ¬Fin15AnchoredAtom0749 chi))) ∨
      (((Fin15AnchoredAtom2036 chi ∧
      ¬Fin15AnchoredAtom1035 chi) ∨
      (¬Fin15AnchoredAtom2036 chi ∧
      Fin15AnchoredAtom0500 chi ∧
      Fin15AnchoredAtom0501 chi ∧
      Fin15AnchoredAtom0519 chi ∧
      Fin15AnchoredAtom0749 chi ∧
      Fin15AnchoredAtom1035 chi)) ∨
      ((Fin15AnchoredAtom2037 chi ∧
      ¬Fin15AnchoredAtom0500 chi) ∨
      (Fin15AnchoredAtom2037 chi ∧
      ¬Fin15AnchoredAtom0750 chi))))) ∨
      (((((Fin15AnchoredAtom2038 chi ∧
      ¬Fin15AnchoredAtom0500 chi) ∨
      (Fin15AnchoredAtom2038 chi ∧
      ¬Fin15AnchoredAtom0503 chi)) ∨
      ((Fin15AnchoredAtom2038 chi ∧
      ¬Fin15AnchoredAtom0521 chi) ∨
      (Fin15AnchoredAtom2038 chi ∧
      ¬Fin15AnchoredAtom0751 chi))) ∨
      (((Fin15AnchoredAtom2038 chi ∧
      ¬Fin15AnchoredAtom1037 chi) ∨
      (¬Fin15AnchoredAtom2038 chi ∧
      Fin15AnchoredAtom0500 chi ∧
      Fin15AnchoredAtom0503 chi ∧
      Fin15AnchoredAtom0521 chi ∧
      Fin15AnchoredAtom0751 chi ∧
      Fin15AnchoredAtom1037 chi)) ∨
      ((Fin15AnchoredAtom2039 chi ∧
      ¬Fin15AnchoredAtom0500 chi) ∨
      (Fin15AnchoredAtom2039 chi ∧
      ¬Fin15AnchoredAtom0504 chi)))) ∨
      ((((Fin15AnchoredAtom2039 chi ∧
      ¬Fin15AnchoredAtom0522 chi) ∨
      (Fin15AnchoredAtom2039 chi ∧
      ¬Fin15AnchoredAtom0752 chi)) ∨
      ((Fin15AnchoredAtom2039 chi ∧
      ¬Fin15AnchoredAtom1038 chi) ∨
      (¬Fin15AnchoredAtom2039 chi ∧
      Fin15AnchoredAtom0500 chi ∧
      Fin15AnchoredAtom0504 chi ∧
      Fin15AnchoredAtom0522 chi ∧
      Fin15AnchoredAtom0752 chi ∧
      Fin15AnchoredAtom1038 chi))) ∨
      (((Fin15AnchoredAtom2040 chi ∧
      ¬Fin15AnchoredAtom0500 chi) ∨
      (Fin15AnchoredAtom2040 chi ∧
      ¬Fin15AnchoredAtom0505 chi)) ∨
      ((Fin15AnchoredAtom2040 chi ∧
      ¬Fin15AnchoredAtom0523 chi) ∨
      (Fin15AnchoredAtom2040 chi ∧
      ¬Fin15AnchoredAtom0753 chi)))))))) ∨
      (((((((Fin15AnchoredAtom2040 chi ∧
      ¬Fin15AnchoredAtom1039 chi) ∨
      ((¬Fin15AnchoredAtom2040 chi ∧
      Fin15AnchoredAtom0500 chi ∧
      Fin15AnchoredAtom0505 chi ∧
      Fin15AnchoredAtom0523 chi ∧
      Fin15AnchoredAtom0753 chi ∧
      Fin15AnchoredAtom1039 chi) ∨
      (Fin15AnchoredAtom2041 chi ∧
      ¬Fin15AnchoredAtom0501 chi))) ∨
      (((Fin15AnchoredAtom2041 chi ∧
      ¬Fin15AnchoredAtom0502 chi) ∨
      (Fin15AnchoredAtom2041 chi ∧
      ¬Fin15AnchoredAtom0524 chi)) ∨
      ((Fin15AnchoredAtom2041 chi ∧
      ¬Fin15AnchoredAtom0754 chi) ∨
      (Fin15AnchoredAtom2041 chi ∧
      ¬Fin15AnchoredAtom1040 chi)))) ∨
      ((((¬Fin15AnchoredAtom2041 chi ∧
      Fin15AnchoredAtom0501 chi ∧
      Fin15AnchoredAtom0502 chi ∧
      Fin15AnchoredAtom0524 chi ∧
      Fin15AnchoredAtom0754 chi ∧
      Fin15AnchoredAtom1040 chi) ∨
      (Fin15AnchoredAtom2042 chi ∧
      ¬Fin15AnchoredAtom0501 chi)) ∨
      ((Fin15AnchoredAtom2042 chi ∧
      ¬Fin15AnchoredAtom0503 chi) ∨
      (Fin15AnchoredAtom2042 chi ∧
      ¬Fin15AnchoredAtom0525 chi))) ∨
      (((Fin15AnchoredAtom2042 chi ∧
      ¬Fin15AnchoredAtom0755 chi) ∨
      (Fin15AnchoredAtom2042 chi ∧
      ¬Fin15AnchoredAtom1041 chi)) ∨
      ((¬Fin15AnchoredAtom2042 chi ∧
      Fin15AnchoredAtom0501 chi ∧
      Fin15AnchoredAtom0503 chi ∧
      Fin15AnchoredAtom0525 chi ∧
      Fin15AnchoredAtom0755 chi ∧
      Fin15AnchoredAtom1041 chi) ∨
      (Fin15AnchoredAtom2043 chi ∧
      ¬Fin15AnchoredAtom0501 chi))))) ∨
      (((((Fin15AnchoredAtom2043 chi ∧
      ¬Fin15AnchoredAtom0504 chi) ∨
      (Fin15AnchoredAtom2043 chi ∧
      ¬Fin15AnchoredAtom0526 chi)) ∨
      ((Fin15AnchoredAtom2043 chi ∧
      ¬Fin15AnchoredAtom0756 chi) ∨
      (Fin15AnchoredAtom2043 chi ∧
      ¬Fin15AnchoredAtom1042 chi))) ∨
      (((¬Fin15AnchoredAtom2043 chi ∧
      Fin15AnchoredAtom0501 chi ∧
      Fin15AnchoredAtom0504 chi ∧
      Fin15AnchoredAtom0526 chi ∧
      Fin15AnchoredAtom0756 chi ∧
      Fin15AnchoredAtom1042 chi) ∨
      (Fin15AnchoredAtom2044 chi ∧
      ¬Fin15AnchoredAtom0501 chi)) ∨
      ((Fin15AnchoredAtom2044 chi ∧
      ¬Fin15AnchoredAtom0505 chi) ∨
      (Fin15AnchoredAtom2044 chi ∧
      ¬Fin15AnchoredAtom0527 chi)))) ∨
      ((((Fin15AnchoredAtom2044 chi ∧
      ¬Fin15AnchoredAtom0757 chi) ∨
      (Fin15AnchoredAtom2044 chi ∧
      ¬Fin15AnchoredAtom1043 chi)) ∨
      ((¬Fin15AnchoredAtom2044 chi ∧
      Fin15AnchoredAtom0501 chi ∧
      Fin15AnchoredAtom0505 chi ∧
      Fin15AnchoredAtom0527 chi ∧
      Fin15AnchoredAtom0757 chi ∧
      Fin15AnchoredAtom1043 chi) ∨
      (Fin15AnchoredAtom2045 chi ∧
      ¬Fin15AnchoredAtom0502 chi))) ∨
      (((Fin15AnchoredAtom2045 chi ∧
      ¬Fin15AnchoredAtom0503 chi) ∨
      (Fin15AnchoredAtom2045 chi ∧
      ¬Fin15AnchoredAtom0528 chi)) ∨
      ((Fin15AnchoredAtom2045 chi ∧
      ¬Fin15AnchoredAtom0758 chi) ∨
      (¬Fin15AnchoredAtom2045 chi ∧
      Fin15AnchoredAtom0502 chi ∧
      Fin15AnchoredAtom0503 chi ∧
      Fin15AnchoredAtom0528 chi ∧
      Fin15AnchoredAtom0758 chi ∧
      Fin15AnchoredAtom1044 chi)))))) ∨
      ((((((Fin15AnchoredAtom2046 chi ∧
      ¬Fin15AnchoredAtom0502 chi) ∨
      (Fin15AnchoredAtom2046 chi ∧
      ¬Fin15AnchoredAtom0504 chi)) ∨
      ((Fin15AnchoredAtom2047 chi ∧
      ¬Fin15AnchoredAtom0502 chi) ∨
      (Fin15AnchoredAtom2047 chi ∧
      ¬Fin15AnchoredAtom0505 chi))) ∨
      (((Fin15AnchoredAtom2048 chi ∧
      ¬Fin15AnchoredAtom0503 chi) ∨
      (Fin15AnchoredAtom2048 chi ∧
      ¬Fin15AnchoredAtom0504 chi)) ∨
      ((Fin15AnchoredAtom2048 chi ∧
      ¬Fin15AnchoredAtom0531 chi) ∨
      (Fin15AnchoredAtom2048 chi ∧
      ¬Fin15AnchoredAtom0761 chi)))) ∨
      ((((Fin15AnchoredAtom2048 chi ∧
      ¬Fin15AnchoredAtom1047 chi) ∨
      (¬Fin15AnchoredAtom2048 chi ∧
      Fin15AnchoredAtom0503 chi ∧
      Fin15AnchoredAtom0504 chi ∧
      Fin15AnchoredAtom0531 chi ∧
      Fin15AnchoredAtom0761 chi ∧
      Fin15AnchoredAtom1047 chi)) ∨
      ((Fin15AnchoredAtom2049 chi ∧
      ¬Fin15AnchoredAtom0503 chi) ∨
      (Fin15AnchoredAtom2049 chi ∧
      ¬Fin15AnchoredAtom0505 chi))) ∨
      (((Fin15AnchoredAtom2049 chi ∧
      ¬Fin15AnchoredAtom0532 chi) ∨
      (Fin15AnchoredAtom2049 chi ∧
      ¬Fin15AnchoredAtom0762 chi)) ∨
      ((Fin15AnchoredAtom2049 chi ∧
      ¬Fin15AnchoredAtom1048 chi) ∨
      (¬Fin15AnchoredAtom2049 chi ∧
      Fin15AnchoredAtom0503 chi ∧
      Fin15AnchoredAtom0505 chi ∧
      Fin15AnchoredAtom0532 chi ∧
      Fin15AnchoredAtom0762 chi ∧
      Fin15AnchoredAtom1048 chi))))) ∨
      (((((Fin15AnchoredAtom2050 chi ∧
      ¬Fin15AnchoredAtom0504 chi) ∨
      (Fin15AnchoredAtom2050 chi ∧
      ¬Fin15AnchoredAtom0505 chi)) ∨
      ((Fin15AnchoredAtom2050 chi ∧
      ¬Fin15AnchoredAtom0533 chi) ∨
      (Fin15AnchoredAtom2050 chi ∧
      ¬Fin15AnchoredAtom0763 chi))) ∨
      (((Fin15AnchoredAtom2050 chi ∧
      ¬Fin15AnchoredAtom1049 chi) ∨
      (¬Fin15AnchoredAtom2050 chi ∧
      Fin15AnchoredAtom0504 chi ∧
      Fin15AnchoredAtom0505 chi ∧
      Fin15AnchoredAtom0533 chi ∧
      Fin15AnchoredAtom0763 chi ∧
      Fin15AnchoredAtom1049 chi)) ∨
      ((Fin15AnchoredAtom2051 chi ∧
      ¬Fin15AnchoredAtom0506 chi) ∨
      (Fin15AnchoredAtom2051 chi ∧
      ¬Fin15AnchoredAtom0507 chi)))) ∨
      ((((Fin15AnchoredAtom2051 chi ∧
      ¬Fin15AnchoredAtom0513 chi) ∨
      (Fin15AnchoredAtom2051 chi ∧
      ¬Fin15AnchoredAtom0764 chi)) ∨
      ((Fin15AnchoredAtom2051 chi ∧
      ¬Fin15AnchoredAtom1050 chi) ∨
      (¬Fin15AnchoredAtom2051 chi ∧
      Fin15AnchoredAtom0506 chi ∧
      Fin15AnchoredAtom0507 chi ∧
      Fin15AnchoredAtom0513 chi ∧
      Fin15AnchoredAtom0764 chi ∧
      Fin15AnchoredAtom1050 chi))) ∨
      (((Fin15AnchoredAtom2052 chi ∧
      ¬Fin15AnchoredAtom0506 chi) ∨
      (Fin15AnchoredAtom2052 chi ∧
      ¬Fin15AnchoredAtom0508 chi)) ∨
      ((Fin15AnchoredAtom2052 chi ∧
      ¬Fin15AnchoredAtom0514 chi) ∨
      (Fin15AnchoredAtom2052 chi ∧
      ¬Fin15AnchoredAtom0765 chi))))))) ∨
      ((((((Fin15AnchoredAtom2052 chi ∧
      ¬Fin15AnchoredAtom1051 chi) ∨
      ((¬Fin15AnchoredAtom2052 chi ∧
      Fin15AnchoredAtom0506 chi ∧
      Fin15AnchoredAtom0508 chi ∧
      Fin15AnchoredAtom0514 chi ∧
      Fin15AnchoredAtom0765 chi ∧
      Fin15AnchoredAtom1051 chi) ∨
      (Fin15AnchoredAtom2054 chi ∧
      ¬Fin15AnchoredAtom0506 chi))) ∨
      (((Fin15AnchoredAtom2054 chi ∧
      ¬Fin15AnchoredAtom0510 chi) ∨
      (Fin15AnchoredAtom2054 chi ∧
      ¬Fin15AnchoredAtom0516 chi)) ∨
      ((Fin15AnchoredAtom2054 chi ∧
      ¬Fin15AnchoredAtom0767 chi) ∨
      (Fin15AnchoredAtom2054 chi ∧
      ¬Fin15AnchoredAtom1053 chi)))) ∨
      ((((¬Fin15AnchoredAtom2054 chi ∧
      Fin15AnchoredAtom0506 chi ∧
      Fin15AnchoredAtom0510 chi ∧
      Fin15AnchoredAtom0516 chi ∧
      Fin15AnchoredAtom0767 chi ∧
      Fin15AnchoredAtom1053 chi) ∨
      (Fin15AnchoredAtom2055 chi ∧
      ¬Fin15AnchoredAtom0506 chi)) ∨
      ((Fin15AnchoredAtom2055 chi ∧
      ¬Fin15AnchoredAtom0511 chi) ∨
      (Fin15AnchoredAtom2055 chi ∧
      ¬Fin15AnchoredAtom0517 chi))) ∨
      (((Fin15AnchoredAtom2055 chi ∧
      ¬Fin15AnchoredAtom0768 chi) ∨
      (Fin15AnchoredAtom2055 chi ∧
      ¬Fin15AnchoredAtom1054 chi)) ∨
      ((¬Fin15AnchoredAtom2055 chi ∧
      Fin15AnchoredAtom0506 chi ∧
      Fin15AnchoredAtom0511 chi ∧
      Fin15AnchoredAtom0517 chi ∧
      Fin15AnchoredAtom0768 chi ∧
      Fin15AnchoredAtom1054 chi) ∨
      (Fin15AnchoredAtom2056 chi ∧
      ¬Fin15AnchoredAtom0506 chi))))) ∨
      (((((Fin15AnchoredAtom2056 chi ∧
      ¬Fin15AnchoredAtom0512 chi) ∨
      (Fin15AnchoredAtom2056 chi ∧
      ¬Fin15AnchoredAtom0518 chi)) ∨
      ((Fin15AnchoredAtom2056 chi ∧
      ¬Fin15AnchoredAtom0769 chi) ∨
      (Fin15AnchoredAtom2056 chi ∧
      ¬Fin15AnchoredAtom1055 chi))) ∨
      (((¬Fin15AnchoredAtom2056 chi ∧
      Fin15AnchoredAtom0506 chi ∧
      Fin15AnchoredAtom0512 chi ∧
      Fin15AnchoredAtom0518 chi ∧
      Fin15AnchoredAtom0769 chi ∧
      Fin15AnchoredAtom1055 chi) ∨
      (Fin15AnchoredAtom2057 chi ∧
      ¬Fin15AnchoredAtom0507 chi)) ∨
      ((Fin15AnchoredAtom2057 chi ∧
      ¬Fin15AnchoredAtom0508 chi) ∨
      (Fin15AnchoredAtom2057 chi ∧
      ¬Fin15AnchoredAtom0519 chi)))) ∨
      ((((Fin15AnchoredAtom2057 chi ∧
      ¬Fin15AnchoredAtom0770 chi) ∨
      (Fin15AnchoredAtom2057 chi ∧
      ¬Fin15AnchoredAtom1056 chi)) ∨
      ((¬Fin15AnchoredAtom2057 chi ∧
      Fin15AnchoredAtom0507 chi ∧
      Fin15AnchoredAtom0508 chi ∧
      Fin15AnchoredAtom0519 chi ∧
      Fin15AnchoredAtom0770 chi ∧
      Fin15AnchoredAtom1056 chi) ∨
      (Fin15AnchoredAtom2058 chi ∧
      ¬Fin15AnchoredAtom0507 chi))) ∨
      (((Fin15AnchoredAtom2058 chi ∧
      ¬Fin15AnchoredAtom0771 chi) ∨
      (Fin15AnchoredAtom2059 chi ∧
      ¬Fin15AnchoredAtom0507 chi)) ∨
      ((Fin15AnchoredAtom2059 chi ∧
      ¬Fin15AnchoredAtom0510 chi) ∨
      (Fin15AnchoredAtom2059 chi ∧
      ¬Fin15AnchoredAtom0521 chi)))))) ∨
      ((((((Fin15AnchoredAtom2059 chi ∧
      ¬Fin15AnchoredAtom0772 chi) ∨
      (Fin15AnchoredAtom2059 chi ∧
      ¬Fin15AnchoredAtom1058 chi)) ∨
      ((¬Fin15AnchoredAtom2059 chi ∧
      Fin15AnchoredAtom0507 chi ∧
      Fin15AnchoredAtom0510 chi ∧
      Fin15AnchoredAtom0521 chi ∧
      Fin15AnchoredAtom0772 chi ∧
      Fin15AnchoredAtom1058 chi) ∨
      (Fin15AnchoredAtom2060 chi ∧
      ¬Fin15AnchoredAtom0507 chi))) ∨
      (((Fin15AnchoredAtom2060 chi ∧
      ¬Fin15AnchoredAtom0511 chi) ∨
      (Fin15AnchoredAtom2060 chi ∧
      ¬Fin15AnchoredAtom0522 chi)) ∨
      ((Fin15AnchoredAtom2060 chi ∧
      ¬Fin15AnchoredAtom0773 chi) ∨
      (Fin15AnchoredAtom2060 chi ∧
      ¬Fin15AnchoredAtom1059 chi)))) ∨
      ((((¬Fin15AnchoredAtom2060 chi ∧
      Fin15AnchoredAtom0507 chi ∧
      Fin15AnchoredAtom0511 chi ∧
      Fin15AnchoredAtom0522 chi ∧
      Fin15AnchoredAtom0773 chi ∧
      Fin15AnchoredAtom1059 chi) ∨
      (Fin15AnchoredAtom2061 chi ∧
      ¬Fin15AnchoredAtom0507 chi)) ∨
      ((Fin15AnchoredAtom2061 chi ∧
      ¬Fin15AnchoredAtom0512 chi) ∨
      (Fin15AnchoredAtom2061 chi ∧
      ¬Fin15AnchoredAtom0523 chi))) ∨
      (((Fin15AnchoredAtom2061 chi ∧
      ¬Fin15AnchoredAtom0774 chi) ∨
      (Fin15AnchoredAtom2061 chi ∧
      ¬Fin15AnchoredAtom1060 chi)) ∨
      ((¬Fin15AnchoredAtom2061 chi ∧
      Fin15AnchoredAtom0507 chi ∧
      Fin15AnchoredAtom0512 chi ∧
      Fin15AnchoredAtom0523 chi ∧
      Fin15AnchoredAtom0774 chi ∧
      Fin15AnchoredAtom1060 chi) ∨
      (Fin15AnchoredAtom2062 chi ∧
      ¬Fin15AnchoredAtom0508 chi))))) ∨
      (((((Fin15AnchoredAtom2062 chi ∧
      ¬Fin15AnchoredAtom0775 chi) ∨
      (Fin15AnchoredAtom2063 chi ∧
      ¬Fin15AnchoredAtom0508 chi)) ∨
      ((Fin15AnchoredAtom2063 chi ∧
      ¬Fin15AnchoredAtom0510 chi) ∨
      (Fin15AnchoredAtom2063 chi ∧
      ¬Fin15AnchoredAtom0525 chi))) ∨
      (((Fin15AnchoredAtom2063 chi ∧
      ¬Fin15AnchoredAtom0776 chi) ∨
      (Fin15AnchoredAtom2063 chi ∧
      ¬Fin15AnchoredAtom1062 chi)) ∨
      ((¬Fin15AnchoredAtom2063 chi ∧
      Fin15AnchoredAtom0508 chi ∧
      Fin15AnchoredAtom0510 chi ∧
      Fin15AnchoredAtom0525 chi ∧
      Fin15AnchoredAtom0776 chi ∧
      Fin15AnchoredAtom1062 chi) ∨
      (Fin15AnchoredAtom2064 chi ∧
      ¬Fin15AnchoredAtom0508 chi)))) ∨
      ((((Fin15AnchoredAtom2064 chi ∧
      ¬Fin15AnchoredAtom0511 chi) ∨
      (Fin15AnchoredAtom2064 chi ∧
      ¬Fin15AnchoredAtom0526 chi)) ∨
      ((Fin15AnchoredAtom2064 chi ∧
      ¬Fin15AnchoredAtom0777 chi) ∨
      (Fin15AnchoredAtom2064 chi ∧
      ¬Fin15AnchoredAtom1063 chi))) ∨
      (((¬Fin15AnchoredAtom2064 chi ∧
      Fin15AnchoredAtom0508 chi ∧
      Fin15AnchoredAtom0511 chi ∧
      Fin15AnchoredAtom0526 chi ∧
      Fin15AnchoredAtom0777 chi ∧
      Fin15AnchoredAtom1063 chi) ∨
      (Fin15AnchoredAtom2065 chi ∧
      ¬Fin15AnchoredAtom0508 chi)) ∨
      ((Fin15AnchoredAtom2065 chi ∧
      ¬Fin15AnchoredAtom0512 chi) ∨
      (Fin15AnchoredAtom2065 chi ∧
      ¬Fin15AnchoredAtom0527 chi)))))))))) := by
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
                exact fin15Anchored_clause16406 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16407 chi hbad
                ·
                  exact fin15Anchored_clause16408 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16409 chi hbad
                ·
                  exact fin15Anchored_clause16410 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16411 chi hbad
                ·
                  exact fin15Anchored_clause16412 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16413 chi hbad
                ·
                  exact fin15Anchored_clause16414 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16415 chi hbad
                ·
                  exact fin15Anchored_clause16416 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16417 chi hbad
                ·
                  exact fin15Anchored_clause16418 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16419 chi hbad
                ·
                  exact fin15Anchored_clause16420 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16421 chi hbad
                ·
                  exact fin15Anchored_clause16422 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16423 chi hbad
                ·
                  exact fin15Anchored_clause16424 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16425 chi hbad
                ·
                  exact fin15Anchored_clause16426 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16427 chi hbad
                ·
                  exact fin15Anchored_clause16428 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16429 chi hbad
                ·
                  exact fin15Anchored_clause16430 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16431 chi hbad
                ·
                  exact fin15Anchored_clause16432 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16433 chi hbad
                ·
                  exact fin15Anchored_clause16434 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16435 chi hbad
                ·
                  exact fin15Anchored_clause16436 chi hbad
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
                  exact fin15Anchored_clause16437 chi hbad
                ·
                  exact fin15Anchored_clause16438 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16439 chi hbad
                ·
                  exact fin15Anchored_clause16440 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16441 chi hbad
                ·
                  exact fin15Anchored_clause16442 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16443 chi hbad
                ·
                  exact fin15Anchored_clause16444 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16445 chi hbad
                ·
                  exact fin15Anchored_clause16446 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16447 chi hbad
                ·
                  exact fin15Anchored_clause16448 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16449 chi hbad
                ·
                  exact fin15Anchored_clause16450 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16451 chi hbad
                ·
                  exact fin15Anchored_clause16452 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16453 chi hbad
                ·
                  exact fin15Anchored_clause16454 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16455 chi hbad
                ·
                  exact fin15Anchored_clause16456 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16457 chi hbad
                ·
                  exact fin15Anchored_clause16458 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16459 chi hbad
                ·
                  exact fin15Anchored_clause16460 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16461 chi hbad
                ·
                  exact fin15Anchored_clause16462 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16463 chi hbad
                ·
                  exact fin15Anchored_clause16464 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16465 chi hbad
                ·
                  exact fin15Anchored_clause16466 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16467 chi hbad
                ·
                  exact fin15Anchored_clause16468 chi hbad
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
                exact fin15Anchored_clause16469 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16470 chi hbad
                ·
                  exact fin15Anchored_clause16471 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16472 chi hbad
                ·
                  exact fin15Anchored_clause16473 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16474 chi hbad
                ·
                  exact fin15Anchored_clause16475 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16476 chi hbad
                ·
                  exact fin15Anchored_clause16477 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16478 chi hbad
                ·
                  exact fin15Anchored_clause16479 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16480 chi hbad
                ·
                  exact fin15Anchored_clause16481 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16482 chi hbad
                ·
                  exact fin15Anchored_clause16483 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16484 chi hbad
                ·
                  exact fin15Anchored_clause16485 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16486 chi hbad
                ·
                  exact fin15Anchored_clause16487 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16488 chi hbad
                ·
                  exact fin15Anchored_clause16489 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16490 chi hbad
                ·
                  exact fin15Anchored_clause16491 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16492 chi hbad
                ·
                  exact fin15Anchored_clause16493 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16494 chi hbad
                ·
                  exact fin15Anchored_clause16495 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16496 chi hbad
                ·
                  exact fin15Anchored_clause16497 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16498 chi hbad
                ·
                  exact fin15Anchored_clause16499 chi hbad
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
                  exact fin15Anchored_clause16500 chi hbad
                ·
                  exact fin15Anchored_clause16501 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16502 chi hbad
                ·
                  exact fin15Anchored_clause16503 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16504 chi hbad
                ·
                  exact fin15Anchored_clause16505 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16506 chi hbad
                ·
                  exact fin15Anchored_clause16507 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16508 chi hbad
                ·
                  exact fin15Anchored_clause16509 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16510 chi hbad
                ·
                  exact fin15Anchored_clause16511 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16512 chi hbad
                ·
                  exact fin15Anchored_clause16513 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16514 chi hbad
                ·
                  exact fin15Anchored_clause16515 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16516 chi hbad
                ·
                  exact fin15Anchored_clause16517 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16518 chi hbad
                ·
                  exact fin15Anchored_clause16519 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16520 chi hbad
                ·
                  exact fin15Anchored_clause16521 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16522 chi hbad
                ·
                  exact fin15Anchored_clause16523 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16524 chi hbad
                ·
                  exact fin15Anchored_clause16525 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16526 chi hbad
                ·
                  exact fin15Anchored_clause16527 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16528 chi hbad
                ·
                  exact fin15Anchored_clause16529 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16530 chi hbad
                ·
                  exact fin15Anchored_clause16531 chi hbad
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
                exact fin15Anchored_clause16532 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16533 chi hbad
                ·
                  exact fin15Anchored_clause16534 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16535 chi hbad
                ·
                  exact fin15Anchored_clause16536 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16537 chi hbad
                ·
                  exact fin15Anchored_clause16538 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16539 chi hbad
                ·
                  exact fin15Anchored_clause16540 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16541 chi hbad
                ·
                  exact fin15Anchored_clause16542 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16543 chi hbad
                ·
                  exact fin15Anchored_clause16544 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16545 chi hbad
                ·
                  exact fin15Anchored_clause16546 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16547 chi hbad
                ·
                  exact fin15Anchored_clause16548 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16549 chi hbad
                ·
                  exact fin15Anchored_clause16550 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16551 chi hbad
                ·
                  exact fin15Anchored_clause16552 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16553 chi hbad
                ·
                  exact fin15Anchored_clause16554 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16555 chi hbad
                ·
                  exact fin15Anchored_clause16556 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16557 chi hbad
                ·
                  exact fin15Anchored_clause16558 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16559 chi hbad
                ·
                  exact fin15Anchored_clause16560 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16561 chi hbad
                ·
                  exact fin15Anchored_clause16562 chi hbad
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
                  exact fin15Anchored_clause16563 chi hbad
                ·
                  exact fin15Anchored_clause16564 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16565 chi hbad
                ·
                  exact fin15Anchored_clause16566 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16567 chi hbad
                ·
                  exact fin15Anchored_clause16568 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16569 chi hbad
                ·
                  exact fin15Anchored_clause16570 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16571 chi hbad
                ·
                  exact fin15Anchored_clause16572 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16573 chi hbad
                ·
                  exact fin15Anchored_clause16574 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16575 chi hbad
                ·
                  exact fin15Anchored_clause16576 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16577 chi hbad
                ·
                  exact fin15Anchored_clause16578 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16579 chi hbad
                ·
                  exact fin15Anchored_clause16580 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16581 chi hbad
                ·
                  exact fin15Anchored_clause16582 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16583 chi hbad
                ·
                  exact fin15Anchored_clause16584 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16585 chi hbad
                ·
                  exact fin15Anchored_clause16586 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16587 chi hbad
                ·
                  exact fin15Anchored_clause16588 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16589 chi hbad
                ·
                  exact fin15Anchored_clause16590 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16591 chi hbad
                ·
                  exact fin15Anchored_clause16592 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16593 chi hbad
                ·
                  exact fin15Anchored_clause16594 chi hbad
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
                exact fin15Anchored_clause16595 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16596 chi hbad
                ·
                  exact fin15Anchored_clause16597 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16598 chi hbad
                ·
                  exact fin15Anchored_clause16599 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16600 chi hbad
                ·
                  exact fin15Anchored_clause16601 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16602 chi hbad
                ·
                  exact fin15Anchored_clause16603 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16604 chi hbad
                ·
                  exact fin15Anchored_clause16605 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16606 chi hbad
                ·
                  exact fin15Anchored_clause16607 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16608 chi hbad
                ·
                  exact fin15Anchored_clause16609 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16610 chi hbad
                ·
                  exact fin15Anchored_clause16611 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16612 chi hbad
                ·
                  exact fin15Anchored_clause16613 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16614 chi hbad
                ·
                  exact fin15Anchored_clause16615 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16616 chi hbad
                ·
                  exact fin15Anchored_clause16617 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16618 chi hbad
                ·
                  exact fin15Anchored_clause16619 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16620 chi hbad
                ·
                  exact fin15Anchored_clause16621 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16622 chi hbad
                ·
                  exact fin15Anchored_clause16623 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16624 chi hbad
                ·
                  exact fin15Anchored_clause16625 chi hbad
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
                  exact fin15Anchored_clause16626 chi hbad
                ·
                  exact fin15Anchored_clause16627 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16628 chi hbad
                ·
                  exact fin15Anchored_clause16629 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16630 chi hbad
                ·
                  exact fin15Anchored_clause16631 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16632 chi hbad
                ·
                  exact fin15Anchored_clause16633 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16634 chi hbad
                ·
                  exact fin15Anchored_clause16635 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16636 chi hbad
                ·
                  exact fin15Anchored_clause16637 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16638 chi hbad
                ·
                  exact fin15Anchored_clause16639 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16640 chi hbad
                ·
                  exact fin15Anchored_clause16641 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16642 chi hbad
                ·
                  exact fin15Anchored_clause16643 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16644 chi hbad
                ·
                  exact fin15Anchored_clause16645 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16646 chi hbad
                ·
                  exact fin15Anchored_clause16647 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16648 chi hbad
                ·
                  exact fin15Anchored_clause16649 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16650 chi hbad
                ·
                  exact fin15Anchored_clause16651 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16652 chi hbad
                ·
                  exact fin15Anchored_clause16653 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16654 chi hbad
                ·
                  exact fin15Anchored_clause16655 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16656 chi hbad
                ·
                  exact fin15Anchored_clause16657 chi hbad

end ErdosSzekeres

end
