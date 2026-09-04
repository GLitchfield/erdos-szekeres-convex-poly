module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 243. -/

theorem fin15Anchored_clause31104 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2024 chi ∧
      ¬Fin15AnchoredAtom2025 chi ∧
      ¬Fin15AnchoredAtom2027 chi ∧
      ¬Fin15AnchoredAtom2029 chi ∧
      ¬Fin15AnchoredAtom2036 chi ∧
      ¬Fin15AnchoredAtom2038 chi ∧
      ¬Fin15AnchoredAtom2040 chi ∧
      ¬Fin15AnchoredAtom2042 chi ∧
      ¬Fin15AnchoredAtom2044 chi ∧
      ¬Fin15AnchoredAtom2049 chi ∧
      ¬Fin15AnchoredAtom2057 chi ∧
      ¬Fin15AnchoredAtom2059 chi ∧
      ¬Fin15AnchoredAtom2061 chi ∧
      ¬Fin15AnchoredAtom2063 chi ∧
      ¬Fin15AnchoredAtom2065 chi ∧
      ¬Fin15AnchoredAtom2070 chi ∧
      ¬Fin15AnchoredAtom2088 chi ∧
      ¬Fin15AnchoredAtom2090 chi ∧
      ¬Fin15AnchoredAtom2095 chi ∧
      ¬Fin15AnchoredAtom2101 chi ∧
      ¬Fin15AnchoredAtom2702 chi ∧
      ¬Fin15AnchoredAtom2704 chi ∧
      ¬Fin15AnchoredAtom2706 chi ∧
      ¬Fin15AnchoredAtom2708 chi ∧
      ¬Fin15AnchoredAtom2710 chi ∧
      ¬Fin15AnchoredAtom2715 chi ∧
      ¬Fin15AnchoredAtom2733 chi ∧
      ¬Fin15AnchoredAtom2735 chi ∧
      ¬Fin15AnchoredAtom2740 chi ∧
      ¬Fin15AnchoredAtom2746 chi ∧
      ¬Fin15AnchoredAtom2768 chi ∧
      ¬Fin15AnchoredAtom2770 chi ∧
      ¬Fin15AnchoredAtom2775 chi ∧
      ¬Fin15AnchoredAtom2781 chi ∧
      ¬Fin15AnchoredAtom2811 chi ∧
      ¬Fin15AnchoredAtom3417 chi ∧
      ¬Fin15AnchoredAtom3419 chi ∧
      ¬Fin15AnchoredAtom3421 chi ∧
      ¬Fin15AnchoredAtom3423 chi ∧
      ¬Fin15AnchoredAtom3425 chi ∧
      ¬Fin15AnchoredAtom3430 chi ∧
      ¬Fin15AnchoredAtom3448 chi ∧
      ¬Fin15AnchoredAtom3450 chi ∧
      ¬Fin15AnchoredAtom3455 chi ∧
      ¬Fin15AnchoredAtom3461 chi ∧
      ¬Fin15AnchoredAtom3483 chi ∧
      ¬Fin15AnchoredAtom3485 chi ∧
      ¬Fin15AnchoredAtom3490 chi ∧
      ¬Fin15AnchoredAtom3496 chi ∧
      ¬Fin15AnchoredAtom3526 chi ∧
      ¬Fin15AnchoredAtom4714 chi ∧
      ¬Fin15AnchoredAtom4716 chi ∧
      ¬Fin15AnchoredAtom4721 chi ∧
      ¬Fin15AnchoredAtom4727 chi ∧
      ¬Fin15AnchoredAtom4757 chi ∧
      ¬Fin15AnchoredAtom4792 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 6, 7, 9, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22211
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2024 Fin15AnchoredAtom2025 Fin15AnchoredAtom2027
    Fin15AnchoredAtom2029 Fin15AnchoredAtom2036 Fin15AnchoredAtom2038 Fin15AnchoredAtom2040
    Fin15AnchoredAtom2042 Fin15AnchoredAtom2044 Fin15AnchoredAtom2049 Fin15AnchoredAtom2057
    Fin15AnchoredAtom2059 Fin15AnchoredAtom2061 Fin15AnchoredAtom2063 Fin15AnchoredAtom2065
    Fin15AnchoredAtom2070 Fin15AnchoredAtom2088 Fin15AnchoredAtom2090 Fin15AnchoredAtom2095
    Fin15AnchoredAtom2101 Fin15AnchoredAtom2702 Fin15AnchoredAtom2704 Fin15AnchoredAtom2706
    Fin15AnchoredAtom2708 Fin15AnchoredAtom2710 Fin15AnchoredAtom2715 Fin15AnchoredAtom2733
    Fin15AnchoredAtom2735 Fin15AnchoredAtom2740 Fin15AnchoredAtom2746 Fin15AnchoredAtom2768
    Fin15AnchoredAtom2770 Fin15AnchoredAtom2775 Fin15AnchoredAtom2781 Fin15AnchoredAtom2811
    Fin15AnchoredAtom3417 Fin15AnchoredAtom3419 Fin15AnchoredAtom3421 Fin15AnchoredAtom3423
    Fin15AnchoredAtom3425 Fin15AnchoredAtom3430 Fin15AnchoredAtom3448 Fin15AnchoredAtom3450
    Fin15AnchoredAtom3455 Fin15AnchoredAtom3461 Fin15AnchoredAtom3483 Fin15AnchoredAtom3485
    Fin15AnchoredAtom3490 Fin15AnchoredAtom3496 Fin15AnchoredAtom3526 Fin15AnchoredAtom4714
    Fin15AnchoredAtom4716 Fin15AnchoredAtom4721 Fin15AnchoredAtom4727 Fin15AnchoredAtom4757
    Fin15AnchoredAtom4792 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31105 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2024 chi ∧
      ¬Fin15AnchoredAtom2025 chi ∧
      ¬Fin15AnchoredAtom2028 chi ∧
      ¬Fin15AnchoredAtom2029 chi ∧
      ¬Fin15AnchoredAtom2036 chi ∧
      ¬Fin15AnchoredAtom2039 chi ∧
      ¬Fin15AnchoredAtom2040 chi ∧
      ¬Fin15AnchoredAtom2043 chi ∧
      ¬Fin15AnchoredAtom2044 chi ∧
      ¬Fin15AnchoredAtom2050 chi ∧
      ¬Fin15AnchoredAtom2057 chi ∧
      ¬Fin15AnchoredAtom2060 chi ∧
      ¬Fin15AnchoredAtom2061 chi ∧
      ¬Fin15AnchoredAtom2064 chi ∧
      ¬Fin15AnchoredAtom2065 chi ∧
      ¬Fin15AnchoredAtom2071 chi ∧
      ¬Fin15AnchoredAtom2089 chi ∧
      ¬Fin15AnchoredAtom2090 chi ∧
      ¬Fin15AnchoredAtom2096 chi ∧
      ¬Fin15AnchoredAtom2102 chi ∧
      ¬Fin15AnchoredAtom2702 chi ∧
      ¬Fin15AnchoredAtom2705 chi ∧
      ¬Fin15AnchoredAtom2706 chi ∧
      ¬Fin15AnchoredAtom2709 chi ∧
      ¬Fin15AnchoredAtom2710 chi ∧
      ¬Fin15AnchoredAtom2716 chi ∧
      ¬Fin15AnchoredAtom2734 chi ∧
      ¬Fin15AnchoredAtom2735 chi ∧
      ¬Fin15AnchoredAtom2741 chi ∧
      ¬Fin15AnchoredAtom2747 chi ∧
      ¬Fin15AnchoredAtom2769 chi ∧
      ¬Fin15AnchoredAtom2770 chi ∧
      ¬Fin15AnchoredAtom2776 chi ∧
      ¬Fin15AnchoredAtom2782 chi ∧
      ¬Fin15AnchoredAtom2812 chi ∧
      ¬Fin15AnchoredAtom3417 chi ∧
      ¬Fin15AnchoredAtom3420 chi ∧
      ¬Fin15AnchoredAtom3421 chi ∧
      ¬Fin15AnchoredAtom3424 chi ∧
      ¬Fin15AnchoredAtom3425 chi ∧
      ¬Fin15AnchoredAtom3431 chi ∧
      ¬Fin15AnchoredAtom3449 chi ∧
      ¬Fin15AnchoredAtom3450 chi ∧
      ¬Fin15AnchoredAtom3456 chi ∧
      ¬Fin15AnchoredAtom3462 chi ∧
      ¬Fin15AnchoredAtom3484 chi ∧
      ¬Fin15AnchoredAtom3485 chi ∧
      ¬Fin15AnchoredAtom3491 chi ∧
      ¬Fin15AnchoredAtom3497 chi ∧
      ¬Fin15AnchoredAtom3527 chi ∧
      ¬Fin15AnchoredAtom4715 chi ∧
      ¬Fin15AnchoredAtom4716 chi ∧
      ¬Fin15AnchoredAtom4722 chi ∧
      ¬Fin15AnchoredAtom4728 chi ∧
      ¬Fin15AnchoredAtom4758 chi ∧
      ¬Fin15AnchoredAtom4793 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 6, 7, 9, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26307
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2024 Fin15AnchoredAtom2025 Fin15AnchoredAtom2028
    Fin15AnchoredAtom2029 Fin15AnchoredAtom2036 Fin15AnchoredAtom2039 Fin15AnchoredAtom2040
    Fin15AnchoredAtom2043 Fin15AnchoredAtom2044 Fin15AnchoredAtom2050 Fin15AnchoredAtom2057
    Fin15AnchoredAtom2060 Fin15AnchoredAtom2061 Fin15AnchoredAtom2064 Fin15AnchoredAtom2065
    Fin15AnchoredAtom2071 Fin15AnchoredAtom2089 Fin15AnchoredAtom2090 Fin15AnchoredAtom2096
    Fin15AnchoredAtom2102 Fin15AnchoredAtom2702 Fin15AnchoredAtom2705 Fin15AnchoredAtom2706
    Fin15AnchoredAtom2709 Fin15AnchoredAtom2710 Fin15AnchoredAtom2716 Fin15AnchoredAtom2734
    Fin15AnchoredAtom2735 Fin15AnchoredAtom2741 Fin15AnchoredAtom2747 Fin15AnchoredAtom2769
    Fin15AnchoredAtom2770 Fin15AnchoredAtom2776 Fin15AnchoredAtom2782 Fin15AnchoredAtom2812
    Fin15AnchoredAtom3417 Fin15AnchoredAtom3420 Fin15AnchoredAtom3421 Fin15AnchoredAtom3424
    Fin15AnchoredAtom3425 Fin15AnchoredAtom3431 Fin15AnchoredAtom3449 Fin15AnchoredAtom3450
    Fin15AnchoredAtom3456 Fin15AnchoredAtom3462 Fin15AnchoredAtom3484 Fin15AnchoredAtom3485
    Fin15AnchoredAtom3491 Fin15AnchoredAtom3497 Fin15AnchoredAtom3527 Fin15AnchoredAtom4715
    Fin15AnchoredAtom4716 Fin15AnchoredAtom4722 Fin15AnchoredAtom4728 Fin15AnchoredAtom4758
    Fin15AnchoredAtom4793 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31106 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2024 chi ∧
      ¬Fin15AnchoredAtom2027 chi ∧
      ¬Fin15AnchoredAtom2028 chi ∧
      ¬Fin15AnchoredAtom2029 chi ∧
      ¬Fin15AnchoredAtom2038 chi ∧
      ¬Fin15AnchoredAtom2039 chi ∧
      ¬Fin15AnchoredAtom2040 chi ∧
      ¬Fin15AnchoredAtom2048 chi ∧
      ¬Fin15AnchoredAtom2049 chi ∧
      ¬Fin15AnchoredAtom2050 chi ∧
      ¬Fin15AnchoredAtom2059 chi ∧
      ¬Fin15AnchoredAtom2060 chi ∧
      ¬Fin15AnchoredAtom2061 chi ∧
      ¬Fin15AnchoredAtom2069 chi ∧
      ¬Fin15AnchoredAtom2070 chi ∧
      ¬Fin15AnchoredAtom2071 chi ∧
      ¬Fin15AnchoredAtom2094 chi ∧
      ¬Fin15AnchoredAtom2095 chi ∧
      ¬Fin15AnchoredAtom2096 chi ∧
      ¬Fin15AnchoredAtom2106 chi ∧
      ¬Fin15AnchoredAtom2704 chi ∧
      ¬Fin15AnchoredAtom2705 chi ∧
      ¬Fin15AnchoredAtom2706 chi ∧
      ¬Fin15AnchoredAtom2714 chi ∧
      ¬Fin15AnchoredAtom2715 chi ∧
      ¬Fin15AnchoredAtom2716 chi ∧
      ¬Fin15AnchoredAtom2739 chi ∧
      ¬Fin15AnchoredAtom2740 chi ∧
      ¬Fin15AnchoredAtom2741 chi ∧
      ¬Fin15AnchoredAtom2751 chi ∧
      ¬Fin15AnchoredAtom2774 chi ∧
      ¬Fin15AnchoredAtom2775 chi ∧
      ¬Fin15AnchoredAtom2776 chi ∧
      ¬Fin15AnchoredAtom2786 chi ∧
      ¬Fin15AnchoredAtom2816 chi ∧
      ¬Fin15AnchoredAtom3419 chi ∧
      ¬Fin15AnchoredAtom3420 chi ∧
      ¬Fin15AnchoredAtom3421 chi ∧
      ¬Fin15AnchoredAtom3429 chi ∧
      ¬Fin15AnchoredAtom3430 chi ∧
      ¬Fin15AnchoredAtom3431 chi ∧
      ¬Fin15AnchoredAtom3454 chi ∧
      ¬Fin15AnchoredAtom3455 chi ∧
      ¬Fin15AnchoredAtom3456 chi ∧
      ¬Fin15AnchoredAtom3466 chi ∧
      ¬Fin15AnchoredAtom3489 chi ∧
      ¬Fin15AnchoredAtom3490 chi ∧
      ¬Fin15AnchoredAtom3491 chi ∧
      ¬Fin15AnchoredAtom3501 chi ∧
      ¬Fin15AnchoredAtom3531 chi ∧
      ¬Fin15AnchoredAtom4720 chi ∧
      ¬Fin15AnchoredAtom4721 chi ∧
      ¬Fin15AnchoredAtom4722 chi ∧
      ¬Fin15AnchoredAtom4732 chi ∧
      ¬Fin15AnchoredAtom4762 chi ∧
      ¬Fin15AnchoredAtom4797 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 6, 7, 9, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29379
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2024 Fin15AnchoredAtom2027 Fin15AnchoredAtom2028
    Fin15AnchoredAtom2029 Fin15AnchoredAtom2038 Fin15AnchoredAtom2039 Fin15AnchoredAtom2040
    Fin15AnchoredAtom2048 Fin15AnchoredAtom2049 Fin15AnchoredAtom2050 Fin15AnchoredAtom2059
    Fin15AnchoredAtom2060 Fin15AnchoredAtom2061 Fin15AnchoredAtom2069 Fin15AnchoredAtom2070
    Fin15AnchoredAtom2071 Fin15AnchoredAtom2094 Fin15AnchoredAtom2095 Fin15AnchoredAtom2096
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2704 Fin15AnchoredAtom2705 Fin15AnchoredAtom2706
    Fin15AnchoredAtom2714 Fin15AnchoredAtom2715 Fin15AnchoredAtom2716 Fin15AnchoredAtom2739
    Fin15AnchoredAtom2740 Fin15AnchoredAtom2741 Fin15AnchoredAtom2751 Fin15AnchoredAtom2774
    Fin15AnchoredAtom2775 Fin15AnchoredAtom2776 Fin15AnchoredAtom2786 Fin15AnchoredAtom2816
    Fin15AnchoredAtom3419 Fin15AnchoredAtom3420 Fin15AnchoredAtom3421 Fin15AnchoredAtom3429
    Fin15AnchoredAtom3430 Fin15AnchoredAtom3431 Fin15AnchoredAtom3454 Fin15AnchoredAtom3455
    Fin15AnchoredAtom3456 Fin15AnchoredAtom3466 Fin15AnchoredAtom3489 Fin15AnchoredAtom3490
    Fin15AnchoredAtom3491 Fin15AnchoredAtom3501 Fin15AnchoredAtom3531 Fin15AnchoredAtom4720
    Fin15AnchoredAtom4721 Fin15AnchoredAtom4722 Fin15AnchoredAtom4732 Fin15AnchoredAtom4762
    Fin15AnchoredAtom4797 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31107 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2025 chi ∧
      ¬Fin15AnchoredAtom2026 chi ∧
      ¬Fin15AnchoredAtom2027 chi ∧
      ¬Fin15AnchoredAtom2029 chi ∧
      ¬Fin15AnchoredAtom2041 chi ∧
      ¬Fin15AnchoredAtom2042 chi ∧
      ¬Fin15AnchoredAtom2044 chi ∧
      ¬Fin15AnchoredAtom2045 chi ∧
      ¬Fin15AnchoredAtom2047 chi ∧
      ¬Fin15AnchoredAtom2049 chi ∧
      ¬Fin15AnchoredAtom2062 chi ∧
      ¬Fin15AnchoredAtom2063 chi ∧
      ¬Fin15AnchoredAtom2065 chi ∧
      ¬Fin15AnchoredAtom2066 chi ∧
      ¬Fin15AnchoredAtom2068 chi ∧
      ¬Fin15AnchoredAtom2070 chi ∧
      ¬Fin15AnchoredAtom2097 chi ∧
      ¬Fin15AnchoredAtom2099 chi ∧
      ¬Fin15AnchoredAtom2101 chi ∧
      ¬Fin15AnchoredAtom2104 chi ∧
      ¬Fin15AnchoredAtom2707 chi ∧
      ¬Fin15AnchoredAtom2708 chi ∧
      ¬Fin15AnchoredAtom2710 chi ∧
      ¬Fin15AnchoredAtom2711 chi ∧
      ¬Fin15AnchoredAtom2713 chi ∧
      ¬Fin15AnchoredAtom2715 chi ∧
      ¬Fin15AnchoredAtom2742 chi ∧
      ¬Fin15AnchoredAtom2744 chi ∧
      ¬Fin15AnchoredAtom2746 chi ∧
      ¬Fin15AnchoredAtom2749 chi ∧
      ¬Fin15AnchoredAtom2777 chi ∧
      ¬Fin15AnchoredAtom2779 chi ∧
      ¬Fin15AnchoredAtom2781 chi ∧
      ¬Fin15AnchoredAtom2784 chi ∧
      ¬Fin15AnchoredAtom2818 chi ∧
      ¬Fin15AnchoredAtom3422 chi ∧
      ¬Fin15AnchoredAtom3423 chi ∧
      ¬Fin15AnchoredAtom3425 chi ∧
      ¬Fin15AnchoredAtom3426 chi ∧
      ¬Fin15AnchoredAtom3428 chi ∧
      ¬Fin15AnchoredAtom3430 chi ∧
      ¬Fin15AnchoredAtom3457 chi ∧
      ¬Fin15AnchoredAtom3459 chi ∧
      ¬Fin15AnchoredAtom3461 chi ∧
      ¬Fin15AnchoredAtom3464 chi ∧
      ¬Fin15AnchoredAtom3492 chi ∧
      ¬Fin15AnchoredAtom3494 chi ∧
      ¬Fin15AnchoredAtom3496 chi ∧
      ¬Fin15AnchoredAtom3499 chi ∧
      ¬Fin15AnchoredAtom3533 chi ∧
      ¬Fin15AnchoredAtom4723 chi ∧
      ¬Fin15AnchoredAtom4725 chi ∧
      ¬Fin15AnchoredAtom4727 chi ∧
      ¬Fin15AnchoredAtom4730 chi ∧
      ¬Fin15AnchoredAtom4764 chi ∧
      ¬Fin15AnchoredAtom4799 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 6, 7, 10, 11, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask23747
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2025 Fin15AnchoredAtom2026 Fin15AnchoredAtom2027
    Fin15AnchoredAtom2029 Fin15AnchoredAtom2041 Fin15AnchoredAtom2042 Fin15AnchoredAtom2044
    Fin15AnchoredAtom2045 Fin15AnchoredAtom2047 Fin15AnchoredAtom2049 Fin15AnchoredAtom2062
    Fin15AnchoredAtom2063 Fin15AnchoredAtom2065 Fin15AnchoredAtom2066 Fin15AnchoredAtom2068
    Fin15AnchoredAtom2070 Fin15AnchoredAtom2097 Fin15AnchoredAtom2099 Fin15AnchoredAtom2101
    Fin15AnchoredAtom2104 Fin15AnchoredAtom2707 Fin15AnchoredAtom2708 Fin15AnchoredAtom2710
    Fin15AnchoredAtom2711 Fin15AnchoredAtom2713 Fin15AnchoredAtom2715 Fin15AnchoredAtom2742
    Fin15AnchoredAtom2744 Fin15AnchoredAtom2746 Fin15AnchoredAtom2749 Fin15AnchoredAtom2777
    Fin15AnchoredAtom2779 Fin15AnchoredAtom2781 Fin15AnchoredAtom2784 Fin15AnchoredAtom2818
    Fin15AnchoredAtom3422 Fin15AnchoredAtom3423 Fin15AnchoredAtom3425 Fin15AnchoredAtom3426
    Fin15AnchoredAtom3428 Fin15AnchoredAtom3430 Fin15AnchoredAtom3457 Fin15AnchoredAtom3459
    Fin15AnchoredAtom3461 Fin15AnchoredAtom3464 Fin15AnchoredAtom3492 Fin15AnchoredAtom3494
    Fin15AnchoredAtom3496 Fin15AnchoredAtom3499 Fin15AnchoredAtom3533 Fin15AnchoredAtom4723
    Fin15AnchoredAtom4725 Fin15AnchoredAtom4727 Fin15AnchoredAtom4730 Fin15AnchoredAtom4764
    Fin15AnchoredAtom4799 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31108 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2025 chi ∧
      ¬Fin15AnchoredAtom2027 chi ∧
      ¬Fin15AnchoredAtom2028 chi ∧
      ¬Fin15AnchoredAtom2029 chi ∧
      ¬Fin15AnchoredAtom2042 chi ∧
      ¬Fin15AnchoredAtom2043 chi ∧
      ¬Fin15AnchoredAtom2044 chi ∧
      ¬Fin15AnchoredAtom2048 chi ∧
      ¬Fin15AnchoredAtom2049 chi ∧
      ¬Fin15AnchoredAtom2050 chi ∧
      ¬Fin15AnchoredAtom2063 chi ∧
      ¬Fin15AnchoredAtom2064 chi ∧
      ¬Fin15AnchoredAtom2065 chi ∧
      ¬Fin15AnchoredAtom2069 chi ∧
      ¬Fin15AnchoredAtom2070 chi ∧
      ¬Fin15AnchoredAtom2071 chi ∧
      ¬Fin15AnchoredAtom2100 chi ∧
      ¬Fin15AnchoredAtom2101 chi ∧
      ¬Fin15AnchoredAtom2102 chi ∧
      ¬Fin15AnchoredAtom2106 chi ∧
      ¬Fin15AnchoredAtom2708 chi ∧
      ¬Fin15AnchoredAtom2709 chi ∧
      ¬Fin15AnchoredAtom2710 chi ∧
      ¬Fin15AnchoredAtom2714 chi ∧
      ¬Fin15AnchoredAtom2715 chi ∧
      ¬Fin15AnchoredAtom2716 chi ∧
      ¬Fin15AnchoredAtom2745 chi ∧
      ¬Fin15AnchoredAtom2746 chi ∧
      ¬Fin15AnchoredAtom2747 chi ∧
      ¬Fin15AnchoredAtom2751 chi ∧
      ¬Fin15AnchoredAtom2780 chi ∧
      ¬Fin15AnchoredAtom2781 chi ∧
      ¬Fin15AnchoredAtom2782 chi ∧
      ¬Fin15AnchoredAtom2786 chi ∧
      ¬Fin15AnchoredAtom2820 chi ∧
      ¬Fin15AnchoredAtom3423 chi ∧
      ¬Fin15AnchoredAtom3424 chi ∧
      ¬Fin15AnchoredAtom3425 chi ∧
      ¬Fin15AnchoredAtom3429 chi ∧
      ¬Fin15AnchoredAtom3430 chi ∧
      ¬Fin15AnchoredAtom3431 chi ∧
      ¬Fin15AnchoredAtom3460 chi ∧
      ¬Fin15AnchoredAtom3461 chi ∧
      ¬Fin15AnchoredAtom3462 chi ∧
      ¬Fin15AnchoredAtom3466 chi ∧
      ¬Fin15AnchoredAtom3495 chi ∧
      ¬Fin15AnchoredAtom3496 chi ∧
      ¬Fin15AnchoredAtom3497 chi ∧
      ¬Fin15AnchoredAtom3501 chi ∧
      ¬Fin15AnchoredAtom3535 chi ∧
      ¬Fin15AnchoredAtom4726 chi ∧
      ¬Fin15AnchoredAtom4727 chi ∧
      ¬Fin15AnchoredAtom4728 chi ∧
      ¬Fin15AnchoredAtom4732 chi ∧
      ¬Fin15AnchoredAtom4766 chi ∧
      ¬Fin15AnchoredAtom4801 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 6, 7, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29891
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2025 Fin15AnchoredAtom2027 Fin15AnchoredAtom2028
    Fin15AnchoredAtom2029 Fin15AnchoredAtom2042 Fin15AnchoredAtom2043 Fin15AnchoredAtom2044
    Fin15AnchoredAtom2048 Fin15AnchoredAtom2049 Fin15AnchoredAtom2050 Fin15AnchoredAtom2063
    Fin15AnchoredAtom2064 Fin15AnchoredAtom2065 Fin15AnchoredAtom2069 Fin15AnchoredAtom2070
    Fin15AnchoredAtom2071 Fin15AnchoredAtom2100 Fin15AnchoredAtom2101 Fin15AnchoredAtom2102
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2708 Fin15AnchoredAtom2709 Fin15AnchoredAtom2710
    Fin15AnchoredAtom2714 Fin15AnchoredAtom2715 Fin15AnchoredAtom2716 Fin15AnchoredAtom2745
    Fin15AnchoredAtom2746 Fin15AnchoredAtom2747 Fin15AnchoredAtom2751 Fin15AnchoredAtom2780
    Fin15AnchoredAtom2781 Fin15AnchoredAtom2782 Fin15AnchoredAtom2786 Fin15AnchoredAtom2820
    Fin15AnchoredAtom3423 Fin15AnchoredAtom3424 Fin15AnchoredAtom3425 Fin15AnchoredAtom3429
    Fin15AnchoredAtom3430 Fin15AnchoredAtom3431 Fin15AnchoredAtom3460 Fin15AnchoredAtom3461
    Fin15AnchoredAtom3462 Fin15AnchoredAtom3466 Fin15AnchoredAtom3495 Fin15AnchoredAtom3496
    Fin15AnchoredAtom3497 Fin15AnchoredAtom3501 Fin15AnchoredAtom3535 Fin15AnchoredAtom4726
    Fin15AnchoredAtom4727 Fin15AnchoredAtom4728 Fin15AnchoredAtom4732 Fin15AnchoredAtom4766
    Fin15AnchoredAtom4801 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31109 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2030 chi ∧
      ¬Fin15AnchoredAtom2031 chi ∧
      ¬Fin15AnchoredAtom2033 chi ∧
      ¬Fin15AnchoredAtom2034 chi ∧
      ¬Fin15AnchoredAtom2036 chi ∧
      ¬Fin15AnchoredAtom2038 chi ∧
      ¬Fin15AnchoredAtom2039 chi ∧
      ¬Fin15AnchoredAtom2042 chi ∧
      ¬Fin15AnchoredAtom2043 chi ∧
      ¬Fin15AnchoredAtom2048 chi ∧
      ¬Fin15AnchoredAtom2072 chi ∧
      ¬Fin15AnchoredAtom2074 chi ∧
      ¬Fin15AnchoredAtom2075 chi ∧
      ¬Fin15AnchoredAtom2078 chi ∧
      ¬Fin15AnchoredAtom2079 chi ∧
      ¬Fin15AnchoredAtom2084 chi ∧
      ¬Fin15AnchoredAtom2088 chi ∧
      ¬Fin15AnchoredAtom2089 chi ∧
      ¬Fin15AnchoredAtom2094 chi ∧
      ¬Fin15AnchoredAtom2100 chi ∧
      ¬Fin15AnchoredAtom2717 chi ∧
      ¬Fin15AnchoredAtom2719 chi ∧
      ¬Fin15AnchoredAtom2720 chi ∧
      ¬Fin15AnchoredAtom2723 chi ∧
      ¬Fin15AnchoredAtom2724 chi ∧
      ¬Fin15AnchoredAtom2729 chi ∧
      ¬Fin15AnchoredAtom2733 chi ∧
      ¬Fin15AnchoredAtom2734 chi ∧
      ¬Fin15AnchoredAtom2739 chi ∧
      ¬Fin15AnchoredAtom2745 chi ∧
      ¬Fin15AnchoredAtom2788 chi ∧
      ¬Fin15AnchoredAtom2789 chi ∧
      ¬Fin15AnchoredAtom2794 chi ∧
      ¬Fin15AnchoredAtom2800 chi ∧
      ¬Fin15AnchoredAtom2810 chi ∧
      ¬Fin15AnchoredAtom3432 chi ∧
      ¬Fin15AnchoredAtom3434 chi ∧
      ¬Fin15AnchoredAtom3435 chi ∧
      ¬Fin15AnchoredAtom3438 chi ∧
      ¬Fin15AnchoredAtom3439 chi ∧
      ¬Fin15AnchoredAtom3444 chi ∧
      ¬Fin15AnchoredAtom3448 chi ∧
      ¬Fin15AnchoredAtom3449 chi ∧
      ¬Fin15AnchoredAtom3454 chi ∧
      ¬Fin15AnchoredAtom3460 chi ∧
      ¬Fin15AnchoredAtom3503 chi ∧
      ¬Fin15AnchoredAtom3504 chi ∧
      ¬Fin15AnchoredAtom3509 chi ∧
      ¬Fin15AnchoredAtom3515 chi ∧
      ¬Fin15AnchoredAtom3525 chi ∧
      ¬Fin15AnchoredAtom4734 chi ∧
      ¬Fin15AnchoredAtom4735 chi ∧
      ¬Fin15AnchoredAtom4740 chi ∧
      ¬Fin15AnchoredAtom4746 chi ∧
      ¬Fin15AnchoredAtom4756 chi ∧
      ¬Fin15AnchoredAtom4806 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 6, 8, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask14147
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2030 Fin15AnchoredAtom2031 Fin15AnchoredAtom2033
    Fin15AnchoredAtom2034 Fin15AnchoredAtom2036 Fin15AnchoredAtom2038 Fin15AnchoredAtom2039
    Fin15AnchoredAtom2042 Fin15AnchoredAtom2043 Fin15AnchoredAtom2048 Fin15AnchoredAtom2072
    Fin15AnchoredAtom2074 Fin15AnchoredAtom2075 Fin15AnchoredAtom2078 Fin15AnchoredAtom2079
    Fin15AnchoredAtom2084 Fin15AnchoredAtom2088 Fin15AnchoredAtom2089 Fin15AnchoredAtom2094
    Fin15AnchoredAtom2100 Fin15AnchoredAtom2717 Fin15AnchoredAtom2719 Fin15AnchoredAtom2720
    Fin15AnchoredAtom2723 Fin15AnchoredAtom2724 Fin15AnchoredAtom2729 Fin15AnchoredAtom2733
    Fin15AnchoredAtom2734 Fin15AnchoredAtom2739 Fin15AnchoredAtom2745 Fin15AnchoredAtom2788
    Fin15AnchoredAtom2789 Fin15AnchoredAtom2794 Fin15AnchoredAtom2800 Fin15AnchoredAtom2810
    Fin15AnchoredAtom3432 Fin15AnchoredAtom3434 Fin15AnchoredAtom3435 Fin15AnchoredAtom3438
    Fin15AnchoredAtom3439 Fin15AnchoredAtom3444 Fin15AnchoredAtom3448 Fin15AnchoredAtom3449
    Fin15AnchoredAtom3454 Fin15AnchoredAtom3460 Fin15AnchoredAtom3503 Fin15AnchoredAtom3504
    Fin15AnchoredAtom3509 Fin15AnchoredAtom3515 Fin15AnchoredAtom3525 Fin15AnchoredAtom4734
    Fin15AnchoredAtom4735 Fin15AnchoredAtom4740 Fin15AnchoredAtom4746 Fin15AnchoredAtom4756
    Fin15AnchoredAtom4806 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31110 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2030 chi ∧
      ¬Fin15AnchoredAtom2031 chi ∧
      ¬Fin15AnchoredAtom2033 chi ∧
      ¬Fin15AnchoredAtom2035 chi ∧
      ¬Fin15AnchoredAtom2036 chi ∧
      ¬Fin15AnchoredAtom2038 chi ∧
      ¬Fin15AnchoredAtom2040 chi ∧
      ¬Fin15AnchoredAtom2042 chi ∧
      ¬Fin15AnchoredAtom2044 chi ∧
      ¬Fin15AnchoredAtom2049 chi ∧
      ¬Fin15AnchoredAtom2072 chi ∧
      ¬Fin15AnchoredAtom2074 chi ∧
      ¬Fin15AnchoredAtom2076 chi ∧
      ¬Fin15AnchoredAtom2078 chi ∧
      ¬Fin15AnchoredAtom2080 chi ∧
      ¬Fin15AnchoredAtom2085 chi ∧
      ¬Fin15AnchoredAtom2088 chi ∧
      ¬Fin15AnchoredAtom2090 chi ∧
      ¬Fin15AnchoredAtom2095 chi ∧
      ¬Fin15AnchoredAtom2101 chi ∧
      ¬Fin15AnchoredAtom2717 chi ∧
      ¬Fin15AnchoredAtom2719 chi ∧
      ¬Fin15AnchoredAtom2721 chi ∧
      ¬Fin15AnchoredAtom2723 chi ∧
      ¬Fin15AnchoredAtom2725 chi ∧
      ¬Fin15AnchoredAtom2730 chi ∧
      ¬Fin15AnchoredAtom2733 chi ∧
      ¬Fin15AnchoredAtom2735 chi ∧
      ¬Fin15AnchoredAtom2740 chi ∧
      ¬Fin15AnchoredAtom2746 chi ∧
      ¬Fin15AnchoredAtom2788 chi ∧
      ¬Fin15AnchoredAtom2790 chi ∧
      ¬Fin15AnchoredAtom2795 chi ∧
      ¬Fin15AnchoredAtom2801 chi ∧
      ¬Fin15AnchoredAtom2811 chi ∧
      ¬Fin15AnchoredAtom3432 chi ∧
      ¬Fin15AnchoredAtom3434 chi ∧
      ¬Fin15AnchoredAtom3436 chi ∧
      ¬Fin15AnchoredAtom3438 chi ∧
      ¬Fin15AnchoredAtom3440 chi ∧
      ¬Fin15AnchoredAtom3445 chi ∧
      ¬Fin15AnchoredAtom3448 chi ∧
      ¬Fin15AnchoredAtom3450 chi ∧
      ¬Fin15AnchoredAtom3455 chi ∧
      ¬Fin15AnchoredAtom3461 chi ∧
      ¬Fin15AnchoredAtom3503 chi ∧
      ¬Fin15AnchoredAtom3505 chi ∧
      ¬Fin15AnchoredAtom3510 chi ∧
      ¬Fin15AnchoredAtom3516 chi ∧
      ¬Fin15AnchoredAtom3526 chi ∧
      ¬Fin15AnchoredAtom4734 chi ∧
      ¬Fin15AnchoredAtom4736 chi ∧
      ¬Fin15AnchoredAtom4741 chi ∧
      ¬Fin15AnchoredAtom4747 chi ∧
      ¬Fin15AnchoredAtom4757 chi ∧
      ¬Fin15AnchoredAtom4807 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 6, 8, 9, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22339
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2030 Fin15AnchoredAtom2031 Fin15AnchoredAtom2033
    Fin15AnchoredAtom2035 Fin15AnchoredAtom2036 Fin15AnchoredAtom2038 Fin15AnchoredAtom2040
    Fin15AnchoredAtom2042 Fin15AnchoredAtom2044 Fin15AnchoredAtom2049 Fin15AnchoredAtom2072
    Fin15AnchoredAtom2074 Fin15AnchoredAtom2076 Fin15AnchoredAtom2078 Fin15AnchoredAtom2080
    Fin15AnchoredAtom2085 Fin15AnchoredAtom2088 Fin15AnchoredAtom2090 Fin15AnchoredAtom2095
    Fin15AnchoredAtom2101 Fin15AnchoredAtom2717 Fin15AnchoredAtom2719 Fin15AnchoredAtom2721
    Fin15AnchoredAtom2723 Fin15AnchoredAtom2725 Fin15AnchoredAtom2730 Fin15AnchoredAtom2733
    Fin15AnchoredAtom2735 Fin15AnchoredAtom2740 Fin15AnchoredAtom2746 Fin15AnchoredAtom2788
    Fin15AnchoredAtom2790 Fin15AnchoredAtom2795 Fin15AnchoredAtom2801 Fin15AnchoredAtom2811
    Fin15AnchoredAtom3432 Fin15AnchoredAtom3434 Fin15AnchoredAtom3436 Fin15AnchoredAtom3438
    Fin15AnchoredAtom3440 Fin15AnchoredAtom3445 Fin15AnchoredAtom3448 Fin15AnchoredAtom3450
    Fin15AnchoredAtom3455 Fin15AnchoredAtom3461 Fin15AnchoredAtom3503 Fin15AnchoredAtom3505
    Fin15AnchoredAtom3510 Fin15AnchoredAtom3516 Fin15AnchoredAtom3526 Fin15AnchoredAtom4734
    Fin15AnchoredAtom4736 Fin15AnchoredAtom4741 Fin15AnchoredAtom4747 Fin15AnchoredAtom4757
    Fin15AnchoredAtom4807 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31111 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2036 chi ∧
      ¬Fin15AnchoredAtom2037 chi ∧
      ¬Fin15AnchoredAtom2038 chi ∧
      ¬Fin15AnchoredAtom2039 chi ∧
      ¬Fin15AnchoredAtom2041 chi ∧
      ¬Fin15AnchoredAtom2042 chi ∧
      ¬Fin15AnchoredAtom2043 chi ∧
      ¬Fin15AnchoredAtom2045 chi ∧
      ¬Fin15AnchoredAtom2046 chi ∧
      ¬Fin15AnchoredAtom2048 chi ∧
      ¬Fin15AnchoredAtom2087 chi ∧
      ¬Fin15AnchoredAtom2088 chi ∧
      ¬Fin15AnchoredAtom2089 chi ∧
      ¬Fin15AnchoredAtom2091 chi ∧
      ¬Fin15AnchoredAtom2092 chi ∧
      ¬Fin15AnchoredAtom2094 chi ∧
      ¬Fin15AnchoredAtom2097 chi ∧
      ¬Fin15AnchoredAtom2098 chi ∧
      ¬Fin15AnchoredAtom2100 chi ∧
      ¬Fin15AnchoredAtom2103 chi ∧
      ¬Fin15AnchoredAtom2732 chi ∧
      ¬Fin15AnchoredAtom2733 chi ∧
      ¬Fin15AnchoredAtom2734 chi ∧
      ¬Fin15AnchoredAtom2736 chi ∧
      ¬Fin15AnchoredAtom2737 chi ∧
      ¬Fin15AnchoredAtom2739 chi ∧
      ¬Fin15AnchoredAtom2742 chi ∧
      ¬Fin15AnchoredAtom2743 chi ∧
      ¬Fin15AnchoredAtom2745 chi ∧
      ¬Fin15AnchoredAtom2748 chi ∧
      ¬Fin15AnchoredAtom2807 chi ∧
      ¬Fin15AnchoredAtom2808 chi ∧
      ¬Fin15AnchoredAtom2810 chi ∧
      ¬Fin15AnchoredAtom2813 chi ∧
      ¬Fin15AnchoredAtom2817 chi ∧
      ¬Fin15AnchoredAtom3447 chi ∧
      ¬Fin15AnchoredAtom3448 chi ∧
      ¬Fin15AnchoredAtom3449 chi ∧
      ¬Fin15AnchoredAtom3451 chi ∧
      ¬Fin15AnchoredAtom3452 chi ∧
      ¬Fin15AnchoredAtom3454 chi ∧
      ¬Fin15AnchoredAtom3457 chi ∧
      ¬Fin15AnchoredAtom3458 chi ∧
      ¬Fin15AnchoredAtom3460 chi ∧
      ¬Fin15AnchoredAtom3463 chi ∧
      ¬Fin15AnchoredAtom3522 chi ∧
      ¬Fin15AnchoredAtom3523 chi ∧
      ¬Fin15AnchoredAtom3525 chi ∧
      ¬Fin15AnchoredAtom3528 chi ∧
      ¬Fin15AnchoredAtom3532 chi ∧
      ¬Fin15AnchoredAtom4753 chi ∧
      ¬Fin15AnchoredAtom4754 chi ∧
      ¬Fin15AnchoredAtom4756 chi ∧
      ¬Fin15AnchoredAtom4759 chi ∧
      ¬Fin15AnchoredAtom4763 chi ∧
      ¬Fin15AnchoredAtom4818 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 6, 9, 10, 11, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask15939
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2036 Fin15AnchoredAtom2037 Fin15AnchoredAtom2038
    Fin15AnchoredAtom2039 Fin15AnchoredAtom2041 Fin15AnchoredAtom2042 Fin15AnchoredAtom2043
    Fin15AnchoredAtom2045 Fin15AnchoredAtom2046 Fin15AnchoredAtom2048 Fin15AnchoredAtom2087
    Fin15AnchoredAtom2088 Fin15AnchoredAtom2089 Fin15AnchoredAtom2091 Fin15AnchoredAtom2092
    Fin15AnchoredAtom2094 Fin15AnchoredAtom2097 Fin15AnchoredAtom2098 Fin15AnchoredAtom2100
    Fin15AnchoredAtom2103 Fin15AnchoredAtom2732 Fin15AnchoredAtom2733 Fin15AnchoredAtom2734
    Fin15AnchoredAtom2736 Fin15AnchoredAtom2737 Fin15AnchoredAtom2739 Fin15AnchoredAtom2742
    Fin15AnchoredAtom2743 Fin15AnchoredAtom2745 Fin15AnchoredAtom2748 Fin15AnchoredAtom2807
    Fin15AnchoredAtom2808 Fin15AnchoredAtom2810 Fin15AnchoredAtom2813 Fin15AnchoredAtom2817
    Fin15AnchoredAtom3447 Fin15AnchoredAtom3448 Fin15AnchoredAtom3449 Fin15AnchoredAtom3451
    Fin15AnchoredAtom3452 Fin15AnchoredAtom3454 Fin15AnchoredAtom3457 Fin15AnchoredAtom3458
    Fin15AnchoredAtom3460 Fin15AnchoredAtom3463 Fin15AnchoredAtom3522 Fin15AnchoredAtom3523
    Fin15AnchoredAtom3525 Fin15AnchoredAtom3528 Fin15AnchoredAtom3532 Fin15AnchoredAtom4753
    Fin15AnchoredAtom4754 Fin15AnchoredAtom4756 Fin15AnchoredAtom4759 Fin15AnchoredAtom4763
    Fin15AnchoredAtom4818 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31112 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2036 chi ∧
      ¬Fin15AnchoredAtom2037 chi ∧
      ¬Fin15AnchoredAtom2038 chi ∧
      ¬Fin15AnchoredAtom2040 chi ∧
      ¬Fin15AnchoredAtom2041 chi ∧
      ¬Fin15AnchoredAtom2042 chi ∧
      ¬Fin15AnchoredAtom2044 chi ∧
      ¬Fin15AnchoredAtom2045 chi ∧
      ¬Fin15AnchoredAtom2047 chi ∧
      ¬Fin15AnchoredAtom2049 chi ∧
      ¬Fin15AnchoredAtom2087 chi ∧
      ¬Fin15AnchoredAtom2088 chi ∧
      ¬Fin15AnchoredAtom2090 chi ∧
      ¬Fin15AnchoredAtom2091 chi ∧
      ¬Fin15AnchoredAtom2093 chi ∧
      ¬Fin15AnchoredAtom2095 chi ∧
      ¬Fin15AnchoredAtom2097 chi ∧
      ¬Fin15AnchoredAtom2099 chi ∧
      ¬Fin15AnchoredAtom2101 chi ∧
      ¬Fin15AnchoredAtom2104 chi ∧
      ¬Fin15AnchoredAtom2732 chi ∧
      ¬Fin15AnchoredAtom2733 chi ∧
      ¬Fin15AnchoredAtom2735 chi ∧
      ¬Fin15AnchoredAtom2736 chi ∧
      ¬Fin15AnchoredAtom2738 chi ∧
      ¬Fin15AnchoredAtom2740 chi ∧
      ¬Fin15AnchoredAtom2742 chi ∧
      ¬Fin15AnchoredAtom2744 chi ∧
      ¬Fin15AnchoredAtom2746 chi ∧
      ¬Fin15AnchoredAtom2749 chi ∧
      ¬Fin15AnchoredAtom2807 chi ∧
      ¬Fin15AnchoredAtom2809 chi ∧
      ¬Fin15AnchoredAtom2811 chi ∧
      ¬Fin15AnchoredAtom2814 chi ∧
      ¬Fin15AnchoredAtom2818 chi ∧
      ¬Fin15AnchoredAtom3447 chi ∧
      ¬Fin15AnchoredAtom3448 chi ∧
      ¬Fin15AnchoredAtom3450 chi ∧
      ¬Fin15AnchoredAtom3451 chi ∧
      ¬Fin15AnchoredAtom3453 chi ∧
      ¬Fin15AnchoredAtom3455 chi ∧
      ¬Fin15AnchoredAtom3457 chi ∧
      ¬Fin15AnchoredAtom3459 chi ∧
      ¬Fin15AnchoredAtom3461 chi ∧
      ¬Fin15AnchoredAtom3464 chi ∧
      ¬Fin15AnchoredAtom3522 chi ∧
      ¬Fin15AnchoredAtom3524 chi ∧
      ¬Fin15AnchoredAtom3526 chi ∧
      ¬Fin15AnchoredAtom3529 chi ∧
      ¬Fin15AnchoredAtom3533 chi ∧
      ¬Fin15AnchoredAtom4753 chi ∧
      ¬Fin15AnchoredAtom4755 chi ∧
      ¬Fin15AnchoredAtom4757 chi ∧
      ¬Fin15AnchoredAtom4760 chi ∧
      ¬Fin15AnchoredAtom4764 chi ∧
      ¬Fin15AnchoredAtom4819 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 6, 9, 10, 11, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask24131
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2036 Fin15AnchoredAtom2037 Fin15AnchoredAtom2038
    Fin15AnchoredAtom2040 Fin15AnchoredAtom2041 Fin15AnchoredAtom2042 Fin15AnchoredAtom2044
    Fin15AnchoredAtom2045 Fin15AnchoredAtom2047 Fin15AnchoredAtom2049 Fin15AnchoredAtom2087
    Fin15AnchoredAtom2088 Fin15AnchoredAtom2090 Fin15AnchoredAtom2091 Fin15AnchoredAtom2093
    Fin15AnchoredAtom2095 Fin15AnchoredAtom2097 Fin15AnchoredAtom2099 Fin15AnchoredAtom2101
    Fin15AnchoredAtom2104 Fin15AnchoredAtom2732 Fin15AnchoredAtom2733 Fin15AnchoredAtom2735
    Fin15AnchoredAtom2736 Fin15AnchoredAtom2738 Fin15AnchoredAtom2740 Fin15AnchoredAtom2742
    Fin15AnchoredAtom2744 Fin15AnchoredAtom2746 Fin15AnchoredAtom2749 Fin15AnchoredAtom2807
    Fin15AnchoredAtom2809 Fin15AnchoredAtom2811 Fin15AnchoredAtom2814 Fin15AnchoredAtom2818
    Fin15AnchoredAtom3447 Fin15AnchoredAtom3448 Fin15AnchoredAtom3450 Fin15AnchoredAtom3451
    Fin15AnchoredAtom3453 Fin15AnchoredAtom3455 Fin15AnchoredAtom3457 Fin15AnchoredAtom3459
    Fin15AnchoredAtom3461 Fin15AnchoredAtom3464 Fin15AnchoredAtom3522 Fin15AnchoredAtom3524
    Fin15AnchoredAtom3526 Fin15AnchoredAtom3529 Fin15AnchoredAtom3533 Fin15AnchoredAtom4753
    Fin15AnchoredAtom4755 Fin15AnchoredAtom4757 Fin15AnchoredAtom4760 Fin15AnchoredAtom4764
    Fin15AnchoredAtom4819 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31113 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2036 chi ∧
      ¬Fin15AnchoredAtom2038 chi ∧
      ¬Fin15AnchoredAtom2039 chi ∧
      ¬Fin15AnchoredAtom2040 chi ∧
      ¬Fin15AnchoredAtom2042 chi ∧
      ¬Fin15AnchoredAtom2043 chi ∧
      ¬Fin15AnchoredAtom2044 chi ∧
      ¬Fin15AnchoredAtom2048 chi ∧
      ¬Fin15AnchoredAtom2049 chi ∧
      ¬Fin15AnchoredAtom2050 chi ∧
      ¬Fin15AnchoredAtom2088 chi ∧
      ¬Fin15AnchoredAtom2089 chi ∧
      ¬Fin15AnchoredAtom2090 chi ∧
      ¬Fin15AnchoredAtom2094 chi ∧
      ¬Fin15AnchoredAtom2095 chi ∧
      ¬Fin15AnchoredAtom2096 chi ∧
      ¬Fin15AnchoredAtom2100 chi ∧
      ¬Fin15AnchoredAtom2101 chi ∧
      ¬Fin15AnchoredAtom2102 chi ∧
      ¬Fin15AnchoredAtom2106 chi ∧
      ¬Fin15AnchoredAtom2733 chi ∧
      ¬Fin15AnchoredAtom2734 chi ∧
      ¬Fin15AnchoredAtom2735 chi ∧
      ¬Fin15AnchoredAtom2739 chi ∧
      ¬Fin15AnchoredAtom2740 chi ∧
      ¬Fin15AnchoredAtom2741 chi ∧
      ¬Fin15AnchoredAtom2745 chi ∧
      ¬Fin15AnchoredAtom2746 chi ∧
      ¬Fin15AnchoredAtom2747 chi ∧
      ¬Fin15AnchoredAtom2751 chi ∧
      ¬Fin15AnchoredAtom2810 chi ∧
      ¬Fin15AnchoredAtom2811 chi ∧
      ¬Fin15AnchoredAtom2812 chi ∧
      ¬Fin15AnchoredAtom2816 chi ∧
      ¬Fin15AnchoredAtom2820 chi ∧
      ¬Fin15AnchoredAtom3448 chi ∧
      ¬Fin15AnchoredAtom3449 chi ∧
      ¬Fin15AnchoredAtom3450 chi ∧
      ¬Fin15AnchoredAtom3454 chi ∧
      ¬Fin15AnchoredAtom3455 chi ∧
      ¬Fin15AnchoredAtom3456 chi ∧
      ¬Fin15AnchoredAtom3460 chi ∧
      ¬Fin15AnchoredAtom3461 chi ∧
      ¬Fin15AnchoredAtom3462 chi ∧
      ¬Fin15AnchoredAtom3466 chi ∧
      ¬Fin15AnchoredAtom3525 chi ∧
      ¬Fin15AnchoredAtom3526 chi ∧
      ¬Fin15AnchoredAtom3527 chi ∧
      ¬Fin15AnchoredAtom3531 chi ∧
      ¬Fin15AnchoredAtom3535 chi ∧
      ¬Fin15AnchoredAtom4756 chi ∧
      ¬Fin15AnchoredAtom4757 chi ∧
      ¬Fin15AnchoredAtom4758 chi ∧
      ¬Fin15AnchoredAtom4762 chi ∧
      ¬Fin15AnchoredAtom4766 chi ∧
      ¬Fin15AnchoredAtom4821 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 6, 9, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask30275
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2036 Fin15AnchoredAtom2038 Fin15AnchoredAtom2039
    Fin15AnchoredAtom2040 Fin15AnchoredAtom2042 Fin15AnchoredAtom2043 Fin15AnchoredAtom2044
    Fin15AnchoredAtom2048 Fin15AnchoredAtom2049 Fin15AnchoredAtom2050 Fin15AnchoredAtom2088
    Fin15AnchoredAtom2089 Fin15AnchoredAtom2090 Fin15AnchoredAtom2094 Fin15AnchoredAtom2095
    Fin15AnchoredAtom2096 Fin15AnchoredAtom2100 Fin15AnchoredAtom2101 Fin15AnchoredAtom2102
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2733 Fin15AnchoredAtom2734 Fin15AnchoredAtom2735
    Fin15AnchoredAtom2739 Fin15AnchoredAtom2740 Fin15AnchoredAtom2741 Fin15AnchoredAtom2745
    Fin15AnchoredAtom2746 Fin15AnchoredAtom2747 Fin15AnchoredAtom2751 Fin15AnchoredAtom2810
    Fin15AnchoredAtom2811 Fin15AnchoredAtom2812 Fin15AnchoredAtom2816 Fin15AnchoredAtom2820
    Fin15AnchoredAtom3448 Fin15AnchoredAtom3449 Fin15AnchoredAtom3450 Fin15AnchoredAtom3454
    Fin15AnchoredAtom3455 Fin15AnchoredAtom3456 Fin15AnchoredAtom3460 Fin15AnchoredAtom3461
    Fin15AnchoredAtom3462 Fin15AnchoredAtom3466 Fin15AnchoredAtom3525 Fin15AnchoredAtom3526
    Fin15AnchoredAtom3527 Fin15AnchoredAtom3531 Fin15AnchoredAtom3535 Fin15AnchoredAtom4756
    Fin15AnchoredAtom4757 Fin15AnchoredAtom4758 Fin15AnchoredAtom4762 Fin15AnchoredAtom4766
    Fin15AnchoredAtom4821 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31114 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2051 chi ∧
      ¬Fin15AnchoredAtom2052 chi ∧
      ¬Fin15AnchoredAtom2054 chi ∧
      ¬Fin15AnchoredAtom2055 chi ∧
      ¬Fin15AnchoredAtom2057 chi ∧
      ¬Fin15AnchoredAtom2059 chi ∧
      ¬Fin15AnchoredAtom2060 chi ∧
      ¬Fin15AnchoredAtom2063 chi ∧
      ¬Fin15AnchoredAtom2064 chi ∧
      ¬Fin15AnchoredAtom2069 chi ∧
      ¬Fin15AnchoredAtom2072 chi ∧
      ¬Fin15AnchoredAtom2074 chi ∧
      ¬Fin15AnchoredAtom2075 chi ∧
      ¬Fin15AnchoredAtom2078 chi ∧
      ¬Fin15AnchoredAtom2079 chi ∧
      ¬Fin15AnchoredAtom2084 chi ∧
      ¬Fin15AnchoredAtom2088 chi ∧
      ¬Fin15AnchoredAtom2089 chi ∧
      ¬Fin15AnchoredAtom2094 chi ∧
      ¬Fin15AnchoredAtom2100 chi ∧
      ¬Fin15AnchoredAtom2752 chi ∧
      ¬Fin15AnchoredAtom2754 chi ∧
      ¬Fin15AnchoredAtom2755 chi ∧
      ¬Fin15AnchoredAtom2758 chi ∧
      ¬Fin15AnchoredAtom2759 chi ∧
      ¬Fin15AnchoredAtom2764 chi ∧
      ¬Fin15AnchoredAtom2768 chi ∧
      ¬Fin15AnchoredAtom2769 chi ∧
      ¬Fin15AnchoredAtom2774 chi ∧
      ¬Fin15AnchoredAtom2780 chi ∧
      ¬Fin15AnchoredAtom2788 chi ∧
      ¬Fin15AnchoredAtom2789 chi ∧
      ¬Fin15AnchoredAtom2794 chi ∧
      ¬Fin15AnchoredAtom2800 chi ∧
      ¬Fin15AnchoredAtom2810 chi ∧
      ¬Fin15AnchoredAtom3467 chi ∧
      ¬Fin15AnchoredAtom3469 chi ∧
      ¬Fin15AnchoredAtom3470 chi ∧
      ¬Fin15AnchoredAtom3473 chi ∧
      ¬Fin15AnchoredAtom3474 chi ∧
      ¬Fin15AnchoredAtom3479 chi ∧
      ¬Fin15AnchoredAtom3483 chi ∧
      ¬Fin15AnchoredAtom3484 chi ∧
      ¬Fin15AnchoredAtom3489 chi ∧
      ¬Fin15AnchoredAtom3495 chi ∧
      ¬Fin15AnchoredAtom3503 chi ∧
      ¬Fin15AnchoredAtom3504 chi ∧
      ¬Fin15AnchoredAtom3509 chi ∧
      ¬Fin15AnchoredAtom3515 chi ∧
      ¬Fin15AnchoredAtom3525 chi ∧
      ¬Fin15AnchoredAtom4769 chi ∧
      ¬Fin15AnchoredAtom4770 chi ∧
      ¬Fin15AnchoredAtom4775 chi ∧
      ¬Fin15AnchoredAtom4781 chi ∧
      ¬Fin15AnchoredAtom4791 chi ∧
      ¬Fin15AnchoredAtom4806 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 7, 8, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask14211
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2051 Fin15AnchoredAtom2052 Fin15AnchoredAtom2054
    Fin15AnchoredAtom2055 Fin15AnchoredAtom2057 Fin15AnchoredAtom2059 Fin15AnchoredAtom2060
    Fin15AnchoredAtom2063 Fin15AnchoredAtom2064 Fin15AnchoredAtom2069 Fin15AnchoredAtom2072
    Fin15AnchoredAtom2074 Fin15AnchoredAtom2075 Fin15AnchoredAtom2078 Fin15AnchoredAtom2079
    Fin15AnchoredAtom2084 Fin15AnchoredAtom2088 Fin15AnchoredAtom2089 Fin15AnchoredAtom2094
    Fin15AnchoredAtom2100 Fin15AnchoredAtom2752 Fin15AnchoredAtom2754 Fin15AnchoredAtom2755
    Fin15AnchoredAtom2758 Fin15AnchoredAtom2759 Fin15AnchoredAtom2764 Fin15AnchoredAtom2768
    Fin15AnchoredAtom2769 Fin15AnchoredAtom2774 Fin15AnchoredAtom2780 Fin15AnchoredAtom2788
    Fin15AnchoredAtom2789 Fin15AnchoredAtom2794 Fin15AnchoredAtom2800 Fin15AnchoredAtom2810
    Fin15AnchoredAtom3467 Fin15AnchoredAtom3469 Fin15AnchoredAtom3470 Fin15AnchoredAtom3473
    Fin15AnchoredAtom3474 Fin15AnchoredAtom3479 Fin15AnchoredAtom3483 Fin15AnchoredAtom3484
    Fin15AnchoredAtom3489 Fin15AnchoredAtom3495 Fin15AnchoredAtom3503 Fin15AnchoredAtom3504
    Fin15AnchoredAtom3509 Fin15AnchoredAtom3515 Fin15AnchoredAtom3525 Fin15AnchoredAtom4769
    Fin15AnchoredAtom4770 Fin15AnchoredAtom4775 Fin15AnchoredAtom4781 Fin15AnchoredAtom4791
    Fin15AnchoredAtom4806 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31115 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2057 chi ∧
      ¬Fin15AnchoredAtom2058 chi ∧
      ¬Fin15AnchoredAtom2059 chi ∧
      ¬Fin15AnchoredAtom2060 chi ∧
      ¬Fin15AnchoredAtom2062 chi ∧
      ¬Fin15AnchoredAtom2063 chi ∧
      ¬Fin15AnchoredAtom2064 chi ∧
      ¬Fin15AnchoredAtom2066 chi ∧
      ¬Fin15AnchoredAtom2067 chi ∧
      ¬Fin15AnchoredAtom2069 chi ∧
      ¬Fin15AnchoredAtom2087 chi ∧
      ¬Fin15AnchoredAtom2088 chi ∧
      ¬Fin15AnchoredAtom2089 chi ∧
      ¬Fin15AnchoredAtom2091 chi ∧
      ¬Fin15AnchoredAtom2092 chi ∧
      ¬Fin15AnchoredAtom2094 chi ∧
      ¬Fin15AnchoredAtom2097 chi ∧
      ¬Fin15AnchoredAtom2098 chi ∧
      ¬Fin15AnchoredAtom2100 chi ∧
      ¬Fin15AnchoredAtom2103 chi ∧
      ¬Fin15AnchoredAtom2767 chi ∧
      ¬Fin15AnchoredAtom2768 chi ∧
      ¬Fin15AnchoredAtom2769 chi ∧
      ¬Fin15AnchoredAtom2771 chi ∧
      ¬Fin15AnchoredAtom2772 chi ∧
      ¬Fin15AnchoredAtom2774 chi ∧
      ¬Fin15AnchoredAtom2777 chi ∧
      ¬Fin15AnchoredAtom2778 chi ∧
      ¬Fin15AnchoredAtom2780 chi ∧
      ¬Fin15AnchoredAtom2783 chi ∧
      ¬Fin15AnchoredAtom2807 chi ∧
      ¬Fin15AnchoredAtom2808 chi ∧
      ¬Fin15AnchoredAtom2810 chi ∧
      ¬Fin15AnchoredAtom2813 chi ∧
      ¬Fin15AnchoredAtom2817 chi ∧
      ¬Fin15AnchoredAtom3482 chi ∧
      ¬Fin15AnchoredAtom3483 chi ∧
      ¬Fin15AnchoredAtom3484 chi ∧
      ¬Fin15AnchoredAtom3486 chi ∧
      ¬Fin15AnchoredAtom3487 chi ∧
      ¬Fin15AnchoredAtom3489 chi ∧
      ¬Fin15AnchoredAtom3492 chi ∧
      ¬Fin15AnchoredAtom3493 chi ∧
      ¬Fin15AnchoredAtom3495 chi ∧
      ¬Fin15AnchoredAtom3498 chi ∧
      ¬Fin15AnchoredAtom3522 chi ∧
      ¬Fin15AnchoredAtom3523 chi ∧
      ¬Fin15AnchoredAtom3525 chi ∧
      ¬Fin15AnchoredAtom3528 chi ∧
      ¬Fin15AnchoredAtom3532 chi ∧
      ¬Fin15AnchoredAtom4788 chi ∧
      ¬Fin15AnchoredAtom4789 chi ∧
      ¬Fin15AnchoredAtom4791 chi ∧
      ¬Fin15AnchoredAtom4794 chi ∧
      ¬Fin15AnchoredAtom4798 chi ∧
      ¬Fin15AnchoredAtom4818 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 7, 9, 10, 11, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask16003
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2057 Fin15AnchoredAtom2058 Fin15AnchoredAtom2059
    Fin15AnchoredAtom2060 Fin15AnchoredAtom2062 Fin15AnchoredAtom2063 Fin15AnchoredAtom2064
    Fin15AnchoredAtom2066 Fin15AnchoredAtom2067 Fin15AnchoredAtom2069 Fin15AnchoredAtom2087
    Fin15AnchoredAtom2088 Fin15AnchoredAtom2089 Fin15AnchoredAtom2091 Fin15AnchoredAtom2092
    Fin15AnchoredAtom2094 Fin15AnchoredAtom2097 Fin15AnchoredAtom2098 Fin15AnchoredAtom2100
    Fin15AnchoredAtom2103 Fin15AnchoredAtom2767 Fin15AnchoredAtom2768 Fin15AnchoredAtom2769
    Fin15AnchoredAtom2771 Fin15AnchoredAtom2772 Fin15AnchoredAtom2774 Fin15AnchoredAtom2777
    Fin15AnchoredAtom2778 Fin15AnchoredAtom2780 Fin15AnchoredAtom2783 Fin15AnchoredAtom2807
    Fin15AnchoredAtom2808 Fin15AnchoredAtom2810 Fin15AnchoredAtom2813 Fin15AnchoredAtom2817
    Fin15AnchoredAtom3482 Fin15AnchoredAtom3483 Fin15AnchoredAtom3484 Fin15AnchoredAtom3486
    Fin15AnchoredAtom3487 Fin15AnchoredAtom3489 Fin15AnchoredAtom3492 Fin15AnchoredAtom3493
    Fin15AnchoredAtom3495 Fin15AnchoredAtom3498 Fin15AnchoredAtom3522 Fin15AnchoredAtom3523
    Fin15AnchoredAtom3525 Fin15AnchoredAtom3528 Fin15AnchoredAtom3532 Fin15AnchoredAtom4788
    Fin15AnchoredAtom4789 Fin15AnchoredAtom4791 Fin15AnchoredAtom4794 Fin15AnchoredAtom4798
    Fin15AnchoredAtom4818 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31116 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2057 chi ∧
      ¬Fin15AnchoredAtom2059 chi ∧
      ¬Fin15AnchoredAtom2060 chi ∧
      ¬Fin15AnchoredAtom2061 chi ∧
      ¬Fin15AnchoredAtom2063 chi ∧
      ¬Fin15AnchoredAtom2064 chi ∧
      ¬Fin15AnchoredAtom2065 chi ∧
      ¬Fin15AnchoredAtom2069 chi ∧
      ¬Fin15AnchoredAtom2070 chi ∧
      ¬Fin15AnchoredAtom2071 chi ∧
      ¬Fin15AnchoredAtom2088 chi ∧
      ¬Fin15AnchoredAtom2089 chi ∧
      ¬Fin15AnchoredAtom2090 chi ∧
      ¬Fin15AnchoredAtom2094 chi ∧
      ¬Fin15AnchoredAtom2095 chi ∧
      ¬Fin15AnchoredAtom2096 chi ∧
      ¬Fin15AnchoredAtom2100 chi ∧
      ¬Fin15AnchoredAtom2101 chi ∧
      ¬Fin15AnchoredAtom2102 chi ∧
      ¬Fin15AnchoredAtom2106 chi ∧
      ¬Fin15AnchoredAtom2768 chi ∧
      ¬Fin15AnchoredAtom2769 chi ∧
      ¬Fin15AnchoredAtom2770 chi ∧
      ¬Fin15AnchoredAtom2774 chi ∧
      ¬Fin15AnchoredAtom2775 chi ∧
      ¬Fin15AnchoredAtom2776 chi ∧
      ¬Fin15AnchoredAtom2780 chi ∧
      ¬Fin15AnchoredAtom2781 chi ∧
      ¬Fin15AnchoredAtom2782 chi ∧
      ¬Fin15AnchoredAtom2786 chi ∧
      ¬Fin15AnchoredAtom2810 chi ∧
      ¬Fin15AnchoredAtom2811 chi ∧
      ¬Fin15AnchoredAtom2812 chi ∧
      ¬Fin15AnchoredAtom2816 chi ∧
      ¬Fin15AnchoredAtom2820 chi ∧
      ¬Fin15AnchoredAtom3483 chi ∧
      ¬Fin15AnchoredAtom3484 chi ∧
      ¬Fin15AnchoredAtom3485 chi ∧
      ¬Fin15AnchoredAtom3489 chi ∧
      ¬Fin15AnchoredAtom3490 chi ∧
      ¬Fin15AnchoredAtom3491 chi ∧
      ¬Fin15AnchoredAtom3495 chi ∧
      ¬Fin15AnchoredAtom3496 chi ∧
      ¬Fin15AnchoredAtom3497 chi ∧
      ¬Fin15AnchoredAtom3501 chi ∧
      ¬Fin15AnchoredAtom3525 chi ∧
      ¬Fin15AnchoredAtom3526 chi ∧
      ¬Fin15AnchoredAtom3527 chi ∧
      ¬Fin15AnchoredAtom3531 chi ∧
      ¬Fin15AnchoredAtom3535 chi ∧
      ¬Fin15AnchoredAtom4791 chi ∧
      ¬Fin15AnchoredAtom4792 chi ∧
      ¬Fin15AnchoredAtom4793 chi ∧
      ¬Fin15AnchoredAtom4797 chi ∧
      ¬Fin15AnchoredAtom4801 chi ∧
      ¬Fin15AnchoredAtom4821 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 7, 9, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask30339
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2057 Fin15AnchoredAtom2059 Fin15AnchoredAtom2060
    Fin15AnchoredAtom2061 Fin15AnchoredAtom2063 Fin15AnchoredAtom2064 Fin15AnchoredAtom2065
    Fin15AnchoredAtom2069 Fin15AnchoredAtom2070 Fin15AnchoredAtom2071 Fin15AnchoredAtom2088
    Fin15AnchoredAtom2089 Fin15AnchoredAtom2090 Fin15AnchoredAtom2094 Fin15AnchoredAtom2095
    Fin15AnchoredAtom2096 Fin15AnchoredAtom2100 Fin15AnchoredAtom2101 Fin15AnchoredAtom2102
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2768 Fin15AnchoredAtom2769 Fin15AnchoredAtom2770
    Fin15AnchoredAtom2774 Fin15AnchoredAtom2775 Fin15AnchoredAtom2776 Fin15AnchoredAtom2780
    Fin15AnchoredAtom2781 Fin15AnchoredAtom2782 Fin15AnchoredAtom2786 Fin15AnchoredAtom2810
    Fin15AnchoredAtom2811 Fin15AnchoredAtom2812 Fin15AnchoredAtom2816 Fin15AnchoredAtom2820
    Fin15AnchoredAtom3483 Fin15AnchoredAtom3484 Fin15AnchoredAtom3485 Fin15AnchoredAtom3489
    Fin15AnchoredAtom3490 Fin15AnchoredAtom3491 Fin15AnchoredAtom3495 Fin15AnchoredAtom3496
    Fin15AnchoredAtom3497 Fin15AnchoredAtom3501 Fin15AnchoredAtom3525 Fin15AnchoredAtom3526
    Fin15AnchoredAtom3527 Fin15AnchoredAtom3531 Fin15AnchoredAtom3535 Fin15AnchoredAtom4791
    Fin15AnchoredAtom4792 Fin15AnchoredAtom4793 Fin15AnchoredAtom4797 Fin15AnchoredAtom4801
    Fin15AnchoredAtom4821 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31117 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2062 chi ∧
      ¬Fin15AnchoredAtom2063 chi ∧
      ¬Fin15AnchoredAtom2064 chi ∧
      ¬Fin15AnchoredAtom2065 chi ∧
      ¬Fin15AnchoredAtom2066 chi ∧
      ¬Fin15AnchoredAtom2067 chi ∧
      ¬Fin15AnchoredAtom2068 chi ∧
      ¬Fin15AnchoredAtom2069 chi ∧
      ¬Fin15AnchoredAtom2070 chi ∧
      ¬Fin15AnchoredAtom2071 chi ∧
      ¬Fin15AnchoredAtom2097 chi ∧
      ¬Fin15AnchoredAtom2098 chi ∧
      ¬Fin15AnchoredAtom2099 chi ∧
      ¬Fin15AnchoredAtom2100 chi ∧
      ¬Fin15AnchoredAtom2101 chi ∧
      ¬Fin15AnchoredAtom2102 chi ∧
      ¬Fin15AnchoredAtom2103 chi ∧
      ¬Fin15AnchoredAtom2104 chi ∧
      ¬Fin15AnchoredAtom2105 chi ∧
      ¬Fin15AnchoredAtom2106 chi ∧
      ¬Fin15AnchoredAtom2777 chi ∧
      ¬Fin15AnchoredAtom2778 chi ∧
      ¬Fin15AnchoredAtom2779 chi ∧
      ¬Fin15AnchoredAtom2780 chi ∧
      ¬Fin15AnchoredAtom2781 chi ∧
      ¬Fin15AnchoredAtom2782 chi ∧
      ¬Fin15AnchoredAtom2783 chi ∧
      ¬Fin15AnchoredAtom2784 chi ∧
      ¬Fin15AnchoredAtom2785 chi ∧
      ¬Fin15AnchoredAtom2786 chi ∧
      ¬Fin15AnchoredAtom2817 chi ∧
      ¬Fin15AnchoredAtom2818 chi ∧
      ¬Fin15AnchoredAtom2819 chi ∧
      ¬Fin15AnchoredAtom2820 chi ∧
      ¬Fin15AnchoredAtom2821 chi ∧
      ¬Fin15AnchoredAtom3492 chi ∧
      ¬Fin15AnchoredAtom3493 chi ∧
      ¬Fin15AnchoredAtom3494 chi ∧
      ¬Fin15AnchoredAtom3495 chi ∧
      ¬Fin15AnchoredAtom3496 chi ∧
      ¬Fin15AnchoredAtom3497 chi ∧
      ¬Fin15AnchoredAtom3498 chi ∧
      ¬Fin15AnchoredAtom3499 chi ∧
      ¬Fin15AnchoredAtom3500 chi ∧
      ¬Fin15AnchoredAtom3501 chi ∧
      ¬Fin15AnchoredAtom3532 chi ∧
      ¬Fin15AnchoredAtom3533 chi ∧
      ¬Fin15AnchoredAtom3534 chi ∧
      ¬Fin15AnchoredAtom3535 chi ∧
      ¬Fin15AnchoredAtom3536 chi ∧
      ¬Fin15AnchoredAtom4798 chi ∧
      ¬Fin15AnchoredAtom4799 chi ∧
      ¬Fin15AnchoredAtom4800 chi ∧
      ¬Fin15AnchoredAtom4801 chi ∧
      ¬Fin15AnchoredAtom4802 chi ∧
      ¬Fin15AnchoredAtom4823 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 7, 10, 11, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask31875
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2062 Fin15AnchoredAtom2063 Fin15AnchoredAtom2064
    Fin15AnchoredAtom2065 Fin15AnchoredAtom2066 Fin15AnchoredAtom2067 Fin15AnchoredAtom2068
    Fin15AnchoredAtom2069 Fin15AnchoredAtom2070 Fin15AnchoredAtom2071 Fin15AnchoredAtom2097
    Fin15AnchoredAtom2098 Fin15AnchoredAtom2099 Fin15AnchoredAtom2100 Fin15AnchoredAtom2101
    Fin15AnchoredAtom2102 Fin15AnchoredAtom2103 Fin15AnchoredAtom2104 Fin15AnchoredAtom2105
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2777 Fin15AnchoredAtom2778 Fin15AnchoredAtom2779
    Fin15AnchoredAtom2780 Fin15AnchoredAtom2781 Fin15AnchoredAtom2782 Fin15AnchoredAtom2783
    Fin15AnchoredAtom2784 Fin15AnchoredAtom2785 Fin15AnchoredAtom2786 Fin15AnchoredAtom2817
    Fin15AnchoredAtom2818 Fin15AnchoredAtom2819 Fin15AnchoredAtom2820 Fin15AnchoredAtom2821
    Fin15AnchoredAtom3492 Fin15AnchoredAtom3493 Fin15AnchoredAtom3494 Fin15AnchoredAtom3495
    Fin15AnchoredAtom3496 Fin15AnchoredAtom3497 Fin15AnchoredAtom3498 Fin15AnchoredAtom3499
    Fin15AnchoredAtom3500 Fin15AnchoredAtom3501 Fin15AnchoredAtom3532 Fin15AnchoredAtom3533
    Fin15AnchoredAtom3534 Fin15AnchoredAtom3535 Fin15AnchoredAtom3536 Fin15AnchoredAtom4798
    Fin15AnchoredAtom4799 Fin15AnchoredAtom4800 Fin15AnchoredAtom4801 Fin15AnchoredAtom4802
    Fin15AnchoredAtom4823 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31118 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom2126 chi ∧
      ¬Fin15AnchoredAtom2128 chi ∧
      ¬Fin15AnchoredAtom2135 chi ∧
      ¬Fin15AnchoredAtom2162 chi ∧
      ¬Fin15AnchoredAtom2163 chi ∧
      ¬Fin15AnchoredAtom2165 chi ∧
      ¬Fin15AnchoredAtom2171 chi ∧
      ¬Fin15AnchoredAtom2173 chi ∧
      ¬Fin15AnchoredAtom2180 chi ∧
      ¬Fin15AnchoredAtom2207 chi ∧
      ¬Fin15AnchoredAtom2209 chi ∧
      ¬Fin15AnchoredAtom2216 chi ∧
      ¬Fin15AnchoredAtom2244 chi ∧
      ¬Fin15AnchoredAtom2327 chi ∧
      ¬Fin15AnchoredAtom2328 chi ∧
      ¬Fin15AnchoredAtom2330 chi ∧
      ¬Fin15AnchoredAtom2336 chi ∧
      ¬Fin15AnchoredAtom2338 chi ∧
      ¬Fin15AnchoredAtom2345 chi ∧
      ¬Fin15AnchoredAtom2372 chi ∧
      ¬Fin15AnchoredAtom2374 chi ∧
      ¬Fin15AnchoredAtom2381 chi ∧
      ¬Fin15AnchoredAtom2409 chi ∧
      ¬Fin15AnchoredAtom2492 chi ∧
      ¬Fin15AnchoredAtom2494 chi ∧
      ¬Fin15AnchoredAtom2501 chi ∧
      ¬Fin15AnchoredAtom2529 chi ∧
      ¬Fin15AnchoredAtom2613 chi ∧
      ¬Fin15AnchoredAtom3537 chi ∧
      ¬Fin15AnchoredAtom3538 chi ∧
      ¬Fin15AnchoredAtom3540 chi ∧
      ¬Fin15AnchoredAtom3546 chi ∧
      ¬Fin15AnchoredAtom3548 chi ∧
      ¬Fin15AnchoredAtom3555 chi ∧
      ¬Fin15AnchoredAtom3582 chi ∧
      ¬Fin15AnchoredAtom3584 chi ∧
      ¬Fin15AnchoredAtom3591 chi ∧
      ¬Fin15AnchoredAtom3619 chi ∧
      ¬Fin15AnchoredAtom3702 chi ∧
      ¬Fin15AnchoredAtom3704 chi ∧
      ¬Fin15AnchoredAtom3711 chi ∧
      ¬Fin15AnchoredAtom3739 chi ∧
      ¬Fin15AnchoredAtom3823 chi ∧
      ¬Fin15AnchoredAtom4032 chi ∧
      ¬Fin15AnchoredAtom4034 chi ∧
      ¬Fin15AnchoredAtom4041 chi ∧
      ¬Fin15AnchoredAtom4069 chi ∧
      ¬Fin15AnchoredAtom4153 chi ∧
      ¬Fin15AnchoredAtom4363 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 5, 6, 7, 9}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask00765
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2107 Fin15AnchoredAtom2108 Fin15AnchoredAtom2109
    Fin15AnchoredAtom2111 Fin15AnchoredAtom2117 Fin15AnchoredAtom2118 Fin15AnchoredAtom2120
    Fin15AnchoredAtom2126 Fin15AnchoredAtom2128 Fin15AnchoredAtom2135 Fin15AnchoredAtom2162
    Fin15AnchoredAtom2163 Fin15AnchoredAtom2165 Fin15AnchoredAtom2171 Fin15AnchoredAtom2173
    Fin15AnchoredAtom2180 Fin15AnchoredAtom2207 Fin15AnchoredAtom2209 Fin15AnchoredAtom2216
    Fin15AnchoredAtom2244 Fin15AnchoredAtom2327 Fin15AnchoredAtom2328 Fin15AnchoredAtom2330
    Fin15AnchoredAtom2336 Fin15AnchoredAtom2338 Fin15AnchoredAtom2345 Fin15AnchoredAtom2372
    Fin15AnchoredAtom2374 Fin15AnchoredAtom2381 Fin15AnchoredAtom2409 Fin15AnchoredAtom2492
    Fin15AnchoredAtom2494 Fin15AnchoredAtom2501 Fin15AnchoredAtom2529 Fin15AnchoredAtom2613
    Fin15AnchoredAtom3537 Fin15AnchoredAtom3538 Fin15AnchoredAtom3540 Fin15AnchoredAtom3546
    Fin15AnchoredAtom3548 Fin15AnchoredAtom3555 Fin15AnchoredAtom3582 Fin15AnchoredAtom3584
    Fin15AnchoredAtom3591 Fin15AnchoredAtom3619 Fin15AnchoredAtom3702 Fin15AnchoredAtom3704
    Fin15AnchoredAtom3711 Fin15AnchoredAtom3739 Fin15AnchoredAtom3823 Fin15AnchoredAtom4032
    Fin15AnchoredAtom4034 Fin15AnchoredAtom4041 Fin15AnchoredAtom4069 Fin15AnchoredAtom4153
    Fin15AnchoredAtom4363 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31119 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2126 chi ∧
      ¬Fin15AnchoredAtom2129 chi ∧
      ¬Fin15AnchoredAtom2136 chi ∧
      ¬Fin15AnchoredAtom2162 chi ∧
      ¬Fin15AnchoredAtom2163 chi ∧
      ¬Fin15AnchoredAtom2166 chi ∧
      ¬Fin15AnchoredAtom2171 chi ∧
      ¬Fin15AnchoredAtom2174 chi ∧
      ¬Fin15AnchoredAtom2181 chi ∧
      ¬Fin15AnchoredAtom2207 chi ∧
      ¬Fin15AnchoredAtom2210 chi ∧
      ¬Fin15AnchoredAtom2217 chi ∧
      ¬Fin15AnchoredAtom2245 chi ∧
      ¬Fin15AnchoredAtom2327 chi ∧
      ¬Fin15AnchoredAtom2328 chi ∧
      ¬Fin15AnchoredAtom2331 chi ∧
      ¬Fin15AnchoredAtom2336 chi ∧
      ¬Fin15AnchoredAtom2339 chi ∧
      ¬Fin15AnchoredAtom2346 chi ∧
      ¬Fin15AnchoredAtom2372 chi ∧
      ¬Fin15AnchoredAtom2375 chi ∧
      ¬Fin15AnchoredAtom2382 chi ∧
      ¬Fin15AnchoredAtom2410 chi ∧
      ¬Fin15AnchoredAtom2492 chi ∧
      ¬Fin15AnchoredAtom2495 chi ∧
      ¬Fin15AnchoredAtom2502 chi ∧
      ¬Fin15AnchoredAtom2530 chi ∧
      ¬Fin15AnchoredAtom2614 chi ∧
      ¬Fin15AnchoredAtom3537 chi ∧
      ¬Fin15AnchoredAtom3538 chi ∧
      ¬Fin15AnchoredAtom3541 chi ∧
      ¬Fin15AnchoredAtom3546 chi ∧
      ¬Fin15AnchoredAtom3549 chi ∧
      ¬Fin15AnchoredAtom3556 chi ∧
      ¬Fin15AnchoredAtom3582 chi ∧
      ¬Fin15AnchoredAtom3585 chi ∧
      ¬Fin15AnchoredAtom3592 chi ∧
      ¬Fin15AnchoredAtom3620 chi ∧
      ¬Fin15AnchoredAtom3702 chi ∧
      ¬Fin15AnchoredAtom3705 chi ∧
      ¬Fin15AnchoredAtom3712 chi ∧
      ¬Fin15AnchoredAtom3740 chi ∧
      ¬Fin15AnchoredAtom3824 chi ∧
      ¬Fin15AnchoredAtom4032 chi ∧
      ¬Fin15AnchoredAtom4035 chi ∧
      ¬Fin15AnchoredAtom4042 chi ∧
      ¬Fin15AnchoredAtom4070 chi ∧
      ¬Fin15AnchoredAtom4154 chi ∧
      ¬Fin15AnchoredAtom4364 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 5, 6, 7, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask01277
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2107 Fin15AnchoredAtom2108 Fin15AnchoredAtom2109
    Fin15AnchoredAtom2112 Fin15AnchoredAtom2117 Fin15AnchoredAtom2118 Fin15AnchoredAtom2121
    Fin15AnchoredAtom2126 Fin15AnchoredAtom2129 Fin15AnchoredAtom2136 Fin15AnchoredAtom2162
    Fin15AnchoredAtom2163 Fin15AnchoredAtom2166 Fin15AnchoredAtom2171 Fin15AnchoredAtom2174
    Fin15AnchoredAtom2181 Fin15AnchoredAtom2207 Fin15AnchoredAtom2210 Fin15AnchoredAtom2217
    Fin15AnchoredAtom2245 Fin15AnchoredAtom2327 Fin15AnchoredAtom2328 Fin15AnchoredAtom2331
    Fin15AnchoredAtom2336 Fin15AnchoredAtom2339 Fin15AnchoredAtom2346 Fin15AnchoredAtom2372
    Fin15AnchoredAtom2375 Fin15AnchoredAtom2382 Fin15AnchoredAtom2410 Fin15AnchoredAtom2492
    Fin15AnchoredAtom2495 Fin15AnchoredAtom2502 Fin15AnchoredAtom2530 Fin15AnchoredAtom2614
    Fin15AnchoredAtom3537 Fin15AnchoredAtom3538 Fin15AnchoredAtom3541 Fin15AnchoredAtom3546
    Fin15AnchoredAtom3549 Fin15AnchoredAtom3556 Fin15AnchoredAtom3582 Fin15AnchoredAtom3585
    Fin15AnchoredAtom3592 Fin15AnchoredAtom3620 Fin15AnchoredAtom3702 Fin15AnchoredAtom3705
    Fin15AnchoredAtom3712 Fin15AnchoredAtom3740 Fin15AnchoredAtom3824 Fin15AnchoredAtom4032
    Fin15AnchoredAtom4035 Fin15AnchoredAtom4042 Fin15AnchoredAtom4070 Fin15AnchoredAtom4154
    Fin15AnchoredAtom4364 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31120 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom2126 chi ∧
      ¬Fin15AnchoredAtom2131 chi ∧
      ¬Fin15AnchoredAtom2138 chi ∧
      ¬Fin15AnchoredAtom2162 chi ∧
      ¬Fin15AnchoredAtom2163 chi ∧
      ¬Fin15AnchoredAtom2168 chi ∧
      ¬Fin15AnchoredAtom2171 chi ∧
      ¬Fin15AnchoredAtom2176 chi ∧
      ¬Fin15AnchoredAtom2183 chi ∧
      ¬Fin15AnchoredAtom2207 chi ∧
      ¬Fin15AnchoredAtom2212 chi ∧
      ¬Fin15AnchoredAtom2219 chi ∧
      ¬Fin15AnchoredAtom2247 chi ∧
      ¬Fin15AnchoredAtom2327 chi ∧
      ¬Fin15AnchoredAtom2328 chi ∧
      ¬Fin15AnchoredAtom2333 chi ∧
      ¬Fin15AnchoredAtom2336 chi ∧
      ¬Fin15AnchoredAtom2341 chi ∧
      ¬Fin15AnchoredAtom2348 chi ∧
      ¬Fin15AnchoredAtom2372 chi ∧
      ¬Fin15AnchoredAtom2377 chi ∧
      ¬Fin15AnchoredAtom2384 chi ∧
      ¬Fin15AnchoredAtom2412 chi ∧
      ¬Fin15AnchoredAtom2492 chi ∧
      ¬Fin15AnchoredAtom2497 chi ∧
      ¬Fin15AnchoredAtom2504 chi ∧
      ¬Fin15AnchoredAtom2532 chi ∧
      ¬Fin15AnchoredAtom2616 chi ∧
      ¬Fin15AnchoredAtom3537 chi ∧
      ¬Fin15AnchoredAtom3538 chi ∧
      ¬Fin15AnchoredAtom3543 chi ∧
      ¬Fin15AnchoredAtom3546 chi ∧
      ¬Fin15AnchoredAtom3551 chi ∧
      ¬Fin15AnchoredAtom3558 chi ∧
      ¬Fin15AnchoredAtom3582 chi ∧
      ¬Fin15AnchoredAtom3587 chi ∧
      ¬Fin15AnchoredAtom3594 chi ∧
      ¬Fin15AnchoredAtom3622 chi ∧
      ¬Fin15AnchoredAtom3702 chi ∧
      ¬Fin15AnchoredAtom3707 chi ∧
      ¬Fin15AnchoredAtom3714 chi ∧
      ¬Fin15AnchoredAtom3742 chi ∧
      ¬Fin15AnchoredAtom3826 chi ∧
      ¬Fin15AnchoredAtom4032 chi ∧
      ¬Fin15AnchoredAtom4037 chi ∧
      ¬Fin15AnchoredAtom4044 chi ∧
      ¬Fin15AnchoredAtom4072 chi ∧
      ¬Fin15AnchoredAtom4156 chi ∧
      ¬Fin15AnchoredAtom4366 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 5, 6, 7, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask04349
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2107 Fin15AnchoredAtom2108 Fin15AnchoredAtom2109
    Fin15AnchoredAtom2114 Fin15AnchoredAtom2117 Fin15AnchoredAtom2118 Fin15AnchoredAtom2123
    Fin15AnchoredAtom2126 Fin15AnchoredAtom2131 Fin15AnchoredAtom2138 Fin15AnchoredAtom2162
    Fin15AnchoredAtom2163 Fin15AnchoredAtom2168 Fin15AnchoredAtom2171 Fin15AnchoredAtom2176
    Fin15AnchoredAtom2183 Fin15AnchoredAtom2207 Fin15AnchoredAtom2212 Fin15AnchoredAtom2219
    Fin15AnchoredAtom2247 Fin15AnchoredAtom2327 Fin15AnchoredAtom2328 Fin15AnchoredAtom2333
    Fin15AnchoredAtom2336 Fin15AnchoredAtom2341 Fin15AnchoredAtom2348 Fin15AnchoredAtom2372
    Fin15AnchoredAtom2377 Fin15AnchoredAtom2384 Fin15AnchoredAtom2412 Fin15AnchoredAtom2492
    Fin15AnchoredAtom2497 Fin15AnchoredAtom2504 Fin15AnchoredAtom2532 Fin15AnchoredAtom2616
    Fin15AnchoredAtom3537 Fin15AnchoredAtom3538 Fin15AnchoredAtom3543 Fin15AnchoredAtom3546
    Fin15AnchoredAtom3551 Fin15AnchoredAtom3558 Fin15AnchoredAtom3582 Fin15AnchoredAtom3587
    Fin15AnchoredAtom3594 Fin15AnchoredAtom3622 Fin15AnchoredAtom3702 Fin15AnchoredAtom3707
    Fin15AnchoredAtom3714 Fin15AnchoredAtom3742 Fin15AnchoredAtom3826 Fin15AnchoredAtom4032
    Fin15AnchoredAtom4037 Fin15AnchoredAtom4044 Fin15AnchoredAtom4072 Fin15AnchoredAtom4156
    Fin15AnchoredAtom4366 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31121 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom2126 chi ∧
      ¬Fin15AnchoredAtom2132 chi ∧
      ¬Fin15AnchoredAtom2139 chi ∧
      ¬Fin15AnchoredAtom2162 chi ∧
      ¬Fin15AnchoredAtom2163 chi ∧
      ¬Fin15AnchoredAtom2169 chi ∧
      ¬Fin15AnchoredAtom2171 chi ∧
      ¬Fin15AnchoredAtom2177 chi ∧
      ¬Fin15AnchoredAtom2184 chi ∧
      ¬Fin15AnchoredAtom2207 chi ∧
      ¬Fin15AnchoredAtom2213 chi ∧
      ¬Fin15AnchoredAtom2220 chi ∧
      ¬Fin15AnchoredAtom2248 chi ∧
      ¬Fin15AnchoredAtom2327 chi ∧
      ¬Fin15AnchoredAtom2328 chi ∧
      ¬Fin15AnchoredAtom2334 chi ∧
      ¬Fin15AnchoredAtom2336 chi ∧
      ¬Fin15AnchoredAtom2342 chi ∧
      ¬Fin15AnchoredAtom2349 chi ∧
      ¬Fin15AnchoredAtom2372 chi ∧
      ¬Fin15AnchoredAtom2378 chi ∧
      ¬Fin15AnchoredAtom2385 chi ∧
      ¬Fin15AnchoredAtom2413 chi ∧
      ¬Fin15AnchoredAtom2492 chi ∧
      ¬Fin15AnchoredAtom2498 chi ∧
      ¬Fin15AnchoredAtom2505 chi ∧
      ¬Fin15AnchoredAtom2533 chi ∧
      ¬Fin15AnchoredAtom2617 chi ∧
      ¬Fin15AnchoredAtom3537 chi ∧
      ¬Fin15AnchoredAtom3538 chi ∧
      ¬Fin15AnchoredAtom3544 chi ∧
      ¬Fin15AnchoredAtom3546 chi ∧
      ¬Fin15AnchoredAtom3552 chi ∧
      ¬Fin15AnchoredAtom3559 chi ∧
      ¬Fin15AnchoredAtom3582 chi ∧
      ¬Fin15AnchoredAtom3588 chi ∧
      ¬Fin15AnchoredAtom3595 chi ∧
      ¬Fin15AnchoredAtom3623 chi ∧
      ¬Fin15AnchoredAtom3702 chi ∧
      ¬Fin15AnchoredAtom3708 chi ∧
      ¬Fin15AnchoredAtom3715 chi ∧
      ¬Fin15AnchoredAtom3743 chi ∧
      ¬Fin15AnchoredAtom3827 chi ∧
      ¬Fin15AnchoredAtom4032 chi ∧
      ¬Fin15AnchoredAtom4038 chi ∧
      ¬Fin15AnchoredAtom4045 chi ∧
      ¬Fin15AnchoredAtom4073 chi ∧
      ¬Fin15AnchoredAtom4157 chi ∧
      ¬Fin15AnchoredAtom4367 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 5, 6, 7, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask08445
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2107 Fin15AnchoredAtom2108 Fin15AnchoredAtom2109
    Fin15AnchoredAtom2115 Fin15AnchoredAtom2117 Fin15AnchoredAtom2118 Fin15AnchoredAtom2124
    Fin15AnchoredAtom2126 Fin15AnchoredAtom2132 Fin15AnchoredAtom2139 Fin15AnchoredAtom2162
    Fin15AnchoredAtom2163 Fin15AnchoredAtom2169 Fin15AnchoredAtom2171 Fin15AnchoredAtom2177
    Fin15AnchoredAtom2184 Fin15AnchoredAtom2207 Fin15AnchoredAtom2213 Fin15AnchoredAtom2220
    Fin15AnchoredAtom2248 Fin15AnchoredAtom2327 Fin15AnchoredAtom2328 Fin15AnchoredAtom2334
    Fin15AnchoredAtom2336 Fin15AnchoredAtom2342 Fin15AnchoredAtom2349 Fin15AnchoredAtom2372
    Fin15AnchoredAtom2378 Fin15AnchoredAtom2385 Fin15AnchoredAtom2413 Fin15AnchoredAtom2492
    Fin15AnchoredAtom2498 Fin15AnchoredAtom2505 Fin15AnchoredAtom2533 Fin15AnchoredAtom2617
    Fin15AnchoredAtom3537 Fin15AnchoredAtom3538 Fin15AnchoredAtom3544 Fin15AnchoredAtom3546
    Fin15AnchoredAtom3552 Fin15AnchoredAtom3559 Fin15AnchoredAtom3582 Fin15AnchoredAtom3588
    Fin15AnchoredAtom3595 Fin15AnchoredAtom3623 Fin15AnchoredAtom3702 Fin15AnchoredAtom3708
    Fin15AnchoredAtom3715 Fin15AnchoredAtom3743 Fin15AnchoredAtom3827 Fin15AnchoredAtom4032
    Fin15AnchoredAtom4038 Fin15AnchoredAtom4045 Fin15AnchoredAtom4073 Fin15AnchoredAtom4157
    Fin15AnchoredAtom4367 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31122 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom2126 chi ∧
      ¬Fin15AnchoredAtom2133 chi ∧
      ¬Fin15AnchoredAtom2140 chi ∧
      ¬Fin15AnchoredAtom2162 chi ∧
      ¬Fin15AnchoredAtom2163 chi ∧
      ¬Fin15AnchoredAtom2170 chi ∧
      ¬Fin15AnchoredAtom2171 chi ∧
      ¬Fin15AnchoredAtom2178 chi ∧
      ¬Fin15AnchoredAtom2185 chi ∧
      ¬Fin15AnchoredAtom2207 chi ∧
      ¬Fin15AnchoredAtom2214 chi ∧
      ¬Fin15AnchoredAtom2221 chi ∧
      ¬Fin15AnchoredAtom2249 chi ∧
      ¬Fin15AnchoredAtom2327 chi ∧
      ¬Fin15AnchoredAtom2328 chi ∧
      ¬Fin15AnchoredAtom2335 chi ∧
      ¬Fin15AnchoredAtom2336 chi ∧
      ¬Fin15AnchoredAtom2343 chi ∧
      ¬Fin15AnchoredAtom2350 chi ∧
      ¬Fin15AnchoredAtom2372 chi ∧
      ¬Fin15AnchoredAtom2379 chi ∧
      ¬Fin15AnchoredAtom2386 chi ∧
      ¬Fin15AnchoredAtom2414 chi ∧
      ¬Fin15AnchoredAtom2492 chi ∧
      ¬Fin15AnchoredAtom2499 chi ∧
      ¬Fin15AnchoredAtom2506 chi ∧
      ¬Fin15AnchoredAtom2534 chi ∧
      ¬Fin15AnchoredAtom2618 chi ∧
      ¬Fin15AnchoredAtom3537 chi ∧
      ¬Fin15AnchoredAtom3538 chi ∧
      ¬Fin15AnchoredAtom3545 chi ∧
      ¬Fin15AnchoredAtom3546 chi ∧
      ¬Fin15AnchoredAtom3553 chi ∧
      ¬Fin15AnchoredAtom3560 chi ∧
      ¬Fin15AnchoredAtom3582 chi ∧
      ¬Fin15AnchoredAtom3589 chi ∧
      ¬Fin15AnchoredAtom3596 chi ∧
      ¬Fin15AnchoredAtom3624 chi ∧
      ¬Fin15AnchoredAtom3702 chi ∧
      ¬Fin15AnchoredAtom3709 chi ∧
      ¬Fin15AnchoredAtom3716 chi ∧
      ¬Fin15AnchoredAtom3744 chi ∧
      ¬Fin15AnchoredAtom3828 chi ∧
      ¬Fin15AnchoredAtom4032 chi ∧
      ¬Fin15AnchoredAtom4039 chi ∧
      ¬Fin15AnchoredAtom4046 chi ∧
      ¬Fin15AnchoredAtom4074 chi ∧
      ¬Fin15AnchoredAtom4158 chi ∧
      ¬Fin15AnchoredAtom4368 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 5, 6, 7, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask16637
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2107 Fin15AnchoredAtom2108 Fin15AnchoredAtom2109
    Fin15AnchoredAtom2116 Fin15AnchoredAtom2117 Fin15AnchoredAtom2118 Fin15AnchoredAtom2125
    Fin15AnchoredAtom2126 Fin15AnchoredAtom2133 Fin15AnchoredAtom2140 Fin15AnchoredAtom2162
    Fin15AnchoredAtom2163 Fin15AnchoredAtom2170 Fin15AnchoredAtom2171 Fin15AnchoredAtom2178
    Fin15AnchoredAtom2185 Fin15AnchoredAtom2207 Fin15AnchoredAtom2214 Fin15AnchoredAtom2221
    Fin15AnchoredAtom2249 Fin15AnchoredAtom2327 Fin15AnchoredAtom2328 Fin15AnchoredAtom2335
    Fin15AnchoredAtom2336 Fin15AnchoredAtom2343 Fin15AnchoredAtom2350 Fin15AnchoredAtom2372
    Fin15AnchoredAtom2379 Fin15AnchoredAtom2386 Fin15AnchoredAtom2414 Fin15AnchoredAtom2492
    Fin15AnchoredAtom2499 Fin15AnchoredAtom2506 Fin15AnchoredAtom2534 Fin15AnchoredAtom2618
    Fin15AnchoredAtom3537 Fin15AnchoredAtom3538 Fin15AnchoredAtom3545 Fin15AnchoredAtom3546
    Fin15AnchoredAtom3553 Fin15AnchoredAtom3560 Fin15AnchoredAtom3582 Fin15AnchoredAtom3589
    Fin15AnchoredAtom3596 Fin15AnchoredAtom3624 Fin15AnchoredAtom3702 Fin15AnchoredAtom3709
    Fin15AnchoredAtom3716 Fin15AnchoredAtom3744 Fin15AnchoredAtom3828 Fin15AnchoredAtom4032
    Fin15AnchoredAtom4039 Fin15AnchoredAtom4046 Fin15AnchoredAtom4074 Fin15AnchoredAtom4158
    Fin15AnchoredAtom4368 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31123 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2110 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom2119 chi ∧
      ¬Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom2127 chi ∧
      ¬Fin15AnchoredAtom2132 chi ∧
      ¬Fin15AnchoredAtom2145 chi ∧
      ¬Fin15AnchoredAtom2162 chi ∧
      ¬Fin15AnchoredAtom2164 chi ∧
      ¬Fin15AnchoredAtom2169 chi ∧
      ¬Fin15AnchoredAtom2172 chi ∧
      ¬Fin15AnchoredAtom2177 chi ∧
      ¬Fin15AnchoredAtom2190 chi ∧
      ¬Fin15AnchoredAtom2208 chi ∧
      ¬Fin15AnchoredAtom2213 chi ∧
      ¬Fin15AnchoredAtom2226 chi ∧
      ¬Fin15AnchoredAtom2254 chi ∧
      ¬Fin15AnchoredAtom2327 chi ∧
      ¬Fin15AnchoredAtom2329 chi ∧
      ¬Fin15AnchoredAtom2334 chi ∧
      ¬Fin15AnchoredAtom2337 chi ∧
      ¬Fin15AnchoredAtom2342 chi ∧
      ¬Fin15AnchoredAtom2355 chi ∧
      ¬Fin15AnchoredAtom2373 chi ∧
      ¬Fin15AnchoredAtom2378 chi ∧
      ¬Fin15AnchoredAtom2391 chi ∧
      ¬Fin15AnchoredAtom2419 chi ∧
      ¬Fin15AnchoredAtom2493 chi ∧
      ¬Fin15AnchoredAtom2498 chi ∧
      ¬Fin15AnchoredAtom2511 chi ∧
      ¬Fin15AnchoredAtom2539 chi ∧
      ¬Fin15AnchoredAtom2623 chi ∧
      ¬Fin15AnchoredAtom3537 chi ∧
      ¬Fin15AnchoredAtom3539 chi ∧
      ¬Fin15AnchoredAtom3544 chi ∧
      ¬Fin15AnchoredAtom3547 chi ∧
      ¬Fin15AnchoredAtom3552 chi ∧
      ¬Fin15AnchoredAtom3565 chi ∧
      ¬Fin15AnchoredAtom3583 chi ∧
      ¬Fin15AnchoredAtom3588 chi ∧
      ¬Fin15AnchoredAtom3601 chi ∧
      ¬Fin15AnchoredAtom3629 chi ∧
      ¬Fin15AnchoredAtom3703 chi ∧
      ¬Fin15AnchoredAtom3708 chi ∧
      ¬Fin15AnchoredAtom3721 chi ∧
      ¬Fin15AnchoredAtom3749 chi ∧
      ¬Fin15AnchoredAtom3833 chi ∧
      ¬Fin15AnchoredAtom4033 chi ∧
      ¬Fin15AnchoredAtom4038 chi ∧
      ¬Fin15AnchoredAtom4051 chi ∧
      ¬Fin15AnchoredAtom4079 chi ∧
      ¬Fin15AnchoredAtom4163 chi ∧
      ¬Fin15AnchoredAtom4373 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 5, 6, 8, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask08573
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2107 Fin15AnchoredAtom2108 Fin15AnchoredAtom2110
    Fin15AnchoredAtom2115 Fin15AnchoredAtom2117 Fin15AnchoredAtom2119 Fin15AnchoredAtom2124
    Fin15AnchoredAtom2127 Fin15AnchoredAtom2132 Fin15AnchoredAtom2145 Fin15AnchoredAtom2162
    Fin15AnchoredAtom2164 Fin15AnchoredAtom2169 Fin15AnchoredAtom2172 Fin15AnchoredAtom2177
    Fin15AnchoredAtom2190 Fin15AnchoredAtom2208 Fin15AnchoredAtom2213 Fin15AnchoredAtom2226
    Fin15AnchoredAtom2254 Fin15AnchoredAtom2327 Fin15AnchoredAtom2329 Fin15AnchoredAtom2334
    Fin15AnchoredAtom2337 Fin15AnchoredAtom2342 Fin15AnchoredAtom2355 Fin15AnchoredAtom2373
    Fin15AnchoredAtom2378 Fin15AnchoredAtom2391 Fin15AnchoredAtom2419 Fin15AnchoredAtom2493
    Fin15AnchoredAtom2498 Fin15AnchoredAtom2511 Fin15AnchoredAtom2539 Fin15AnchoredAtom2623
    Fin15AnchoredAtom3537 Fin15AnchoredAtom3539 Fin15AnchoredAtom3544 Fin15AnchoredAtom3547
    Fin15AnchoredAtom3552 Fin15AnchoredAtom3565 Fin15AnchoredAtom3583 Fin15AnchoredAtom3588
    Fin15AnchoredAtom3601 Fin15AnchoredAtom3629 Fin15AnchoredAtom3703 Fin15AnchoredAtom3708
    Fin15AnchoredAtom3721 Fin15AnchoredAtom3749 Fin15AnchoredAtom3833 Fin15AnchoredAtom4033
    Fin15AnchoredAtom4038 Fin15AnchoredAtom4051 Fin15AnchoredAtom4079 Fin15AnchoredAtom4163
    Fin15AnchoredAtom4373 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31124 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2128 chi ∧
      ¬Fin15AnchoredAtom2129 chi ∧
      ¬Fin15AnchoredAtom2147 chi ∧
      ¬Fin15AnchoredAtom2162 chi ∧
      ¬Fin15AnchoredAtom2165 chi ∧
      ¬Fin15AnchoredAtom2166 chi ∧
      ¬Fin15AnchoredAtom2173 chi ∧
      ¬Fin15AnchoredAtom2174 chi ∧
      ¬Fin15AnchoredAtom2192 chi ∧
      ¬Fin15AnchoredAtom2209 chi ∧
      ¬Fin15AnchoredAtom2210 chi ∧
      ¬Fin15AnchoredAtom2228 chi ∧
      ¬Fin15AnchoredAtom2256 chi ∧
      ¬Fin15AnchoredAtom2327 chi ∧
      ¬Fin15AnchoredAtom2330 chi ∧
      ¬Fin15AnchoredAtom2331 chi ∧
      ¬Fin15AnchoredAtom2338 chi ∧
      ¬Fin15AnchoredAtom2339 chi ∧
      ¬Fin15AnchoredAtom2357 chi ∧
      ¬Fin15AnchoredAtom2374 chi ∧
      ¬Fin15AnchoredAtom2375 chi ∧
      ¬Fin15AnchoredAtom2393 chi ∧
      ¬Fin15AnchoredAtom2421 chi ∧
      ¬Fin15AnchoredAtom2494 chi ∧
      ¬Fin15AnchoredAtom2495 chi ∧
      ¬Fin15AnchoredAtom2513 chi ∧
      ¬Fin15AnchoredAtom2541 chi ∧
      ¬Fin15AnchoredAtom2625 chi ∧
      ¬Fin15AnchoredAtom3537 chi ∧
      ¬Fin15AnchoredAtom3540 chi ∧
      ¬Fin15AnchoredAtom3541 chi ∧
      ¬Fin15AnchoredAtom3548 chi ∧
      ¬Fin15AnchoredAtom3549 chi ∧
      ¬Fin15AnchoredAtom3567 chi ∧
      ¬Fin15AnchoredAtom3584 chi ∧
      ¬Fin15AnchoredAtom3585 chi ∧
      ¬Fin15AnchoredAtom3603 chi ∧
      ¬Fin15AnchoredAtom3631 chi ∧
      ¬Fin15AnchoredAtom3704 chi ∧
      ¬Fin15AnchoredAtom3705 chi ∧
      ¬Fin15AnchoredAtom3723 chi ∧
      ¬Fin15AnchoredAtom3751 chi ∧
      ¬Fin15AnchoredAtom3835 chi ∧
      ¬Fin15AnchoredAtom4034 chi ∧
      ¬Fin15AnchoredAtom4035 chi ∧
      ¬Fin15AnchoredAtom4053 chi ∧
      ¬Fin15AnchoredAtom4081 chi ∧
      ¬Fin15AnchoredAtom4165 chi ∧
      ¬Fin15AnchoredAtom4375 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 5, 6, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask01661
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2107 Fin15AnchoredAtom2108 Fin15AnchoredAtom2111
    Fin15AnchoredAtom2112 Fin15AnchoredAtom2117 Fin15AnchoredAtom2120 Fin15AnchoredAtom2121
    Fin15AnchoredAtom2128 Fin15AnchoredAtom2129 Fin15AnchoredAtom2147 Fin15AnchoredAtom2162
    Fin15AnchoredAtom2165 Fin15AnchoredAtom2166 Fin15AnchoredAtom2173 Fin15AnchoredAtom2174
    Fin15AnchoredAtom2192 Fin15AnchoredAtom2209 Fin15AnchoredAtom2210 Fin15AnchoredAtom2228
    Fin15AnchoredAtom2256 Fin15AnchoredAtom2327 Fin15AnchoredAtom2330 Fin15AnchoredAtom2331
    Fin15AnchoredAtom2338 Fin15AnchoredAtom2339 Fin15AnchoredAtom2357 Fin15AnchoredAtom2374
    Fin15AnchoredAtom2375 Fin15AnchoredAtom2393 Fin15AnchoredAtom2421 Fin15AnchoredAtom2494
    Fin15AnchoredAtom2495 Fin15AnchoredAtom2513 Fin15AnchoredAtom2541 Fin15AnchoredAtom2625
    Fin15AnchoredAtom3537 Fin15AnchoredAtom3540 Fin15AnchoredAtom3541 Fin15AnchoredAtom3548
    Fin15AnchoredAtom3549 Fin15AnchoredAtom3567 Fin15AnchoredAtom3584 Fin15AnchoredAtom3585
    Fin15AnchoredAtom3603 Fin15AnchoredAtom3631 Fin15AnchoredAtom3704 Fin15AnchoredAtom3705
    Fin15AnchoredAtom3723 Fin15AnchoredAtom3751 Fin15AnchoredAtom3835 Fin15AnchoredAtom4034
    Fin15AnchoredAtom4035 Fin15AnchoredAtom4053 Fin15AnchoredAtom4081 Fin15AnchoredAtom4165
    Fin15AnchoredAtom4375 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31125 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom2128 chi ∧
      ¬Fin15AnchoredAtom2131 chi ∧
      ¬Fin15AnchoredAtom2149 chi ∧
      ¬Fin15AnchoredAtom2162 chi ∧
      ¬Fin15AnchoredAtom2165 chi ∧
      ¬Fin15AnchoredAtom2168 chi ∧
      ¬Fin15AnchoredAtom2173 chi ∧
      ¬Fin15AnchoredAtom2176 chi ∧
      ¬Fin15AnchoredAtom2194 chi ∧
      ¬Fin15AnchoredAtom2209 chi ∧
      ¬Fin15AnchoredAtom2212 chi ∧
      ¬Fin15AnchoredAtom2230 chi ∧
      ¬Fin15AnchoredAtom2258 chi ∧
      ¬Fin15AnchoredAtom2327 chi ∧
      ¬Fin15AnchoredAtom2330 chi ∧
      ¬Fin15AnchoredAtom2333 chi ∧
      ¬Fin15AnchoredAtom2338 chi ∧
      ¬Fin15AnchoredAtom2341 chi ∧
      ¬Fin15AnchoredAtom2359 chi ∧
      ¬Fin15AnchoredAtom2374 chi ∧
      ¬Fin15AnchoredAtom2377 chi ∧
      ¬Fin15AnchoredAtom2395 chi ∧
      ¬Fin15AnchoredAtom2423 chi ∧
      ¬Fin15AnchoredAtom2494 chi ∧
      ¬Fin15AnchoredAtom2497 chi ∧
      ¬Fin15AnchoredAtom2515 chi ∧
      ¬Fin15AnchoredAtom2543 chi ∧
      ¬Fin15AnchoredAtom2627 chi ∧
      ¬Fin15AnchoredAtom3537 chi ∧
      ¬Fin15AnchoredAtom3540 chi ∧
      ¬Fin15AnchoredAtom3543 chi ∧
      ¬Fin15AnchoredAtom3548 chi ∧
      ¬Fin15AnchoredAtom3551 chi ∧
      ¬Fin15AnchoredAtom3569 chi ∧
      ¬Fin15AnchoredAtom3584 chi ∧
      ¬Fin15AnchoredAtom3587 chi ∧
      ¬Fin15AnchoredAtom3605 chi ∧
      ¬Fin15AnchoredAtom3633 chi ∧
      ¬Fin15AnchoredAtom3704 chi ∧
      ¬Fin15AnchoredAtom3707 chi ∧
      ¬Fin15AnchoredAtom3725 chi ∧
      ¬Fin15AnchoredAtom3753 chi ∧
      ¬Fin15AnchoredAtom3837 chi ∧
      ¬Fin15AnchoredAtom4034 chi ∧
      ¬Fin15AnchoredAtom4037 chi ∧
      ¬Fin15AnchoredAtom4055 chi ∧
      ¬Fin15AnchoredAtom4083 chi ∧
      ¬Fin15AnchoredAtom4167 chi ∧
      ¬Fin15AnchoredAtom4377 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 5, 6, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask04733
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2107 Fin15AnchoredAtom2108 Fin15AnchoredAtom2111
    Fin15AnchoredAtom2114 Fin15AnchoredAtom2117 Fin15AnchoredAtom2120 Fin15AnchoredAtom2123
    Fin15AnchoredAtom2128 Fin15AnchoredAtom2131 Fin15AnchoredAtom2149 Fin15AnchoredAtom2162
    Fin15AnchoredAtom2165 Fin15AnchoredAtom2168 Fin15AnchoredAtom2173 Fin15AnchoredAtom2176
    Fin15AnchoredAtom2194 Fin15AnchoredAtom2209 Fin15AnchoredAtom2212 Fin15AnchoredAtom2230
    Fin15AnchoredAtom2258 Fin15AnchoredAtom2327 Fin15AnchoredAtom2330 Fin15AnchoredAtom2333
    Fin15AnchoredAtom2338 Fin15AnchoredAtom2341 Fin15AnchoredAtom2359 Fin15AnchoredAtom2374
    Fin15AnchoredAtom2377 Fin15AnchoredAtom2395 Fin15AnchoredAtom2423 Fin15AnchoredAtom2494
    Fin15AnchoredAtom2497 Fin15AnchoredAtom2515 Fin15AnchoredAtom2543 Fin15AnchoredAtom2627
    Fin15AnchoredAtom3537 Fin15AnchoredAtom3540 Fin15AnchoredAtom3543 Fin15AnchoredAtom3548
    Fin15AnchoredAtom3551 Fin15AnchoredAtom3569 Fin15AnchoredAtom3584 Fin15AnchoredAtom3587
    Fin15AnchoredAtom3605 Fin15AnchoredAtom3633 Fin15AnchoredAtom3704 Fin15AnchoredAtom3707
    Fin15AnchoredAtom3725 Fin15AnchoredAtom3753 Fin15AnchoredAtom3837 Fin15AnchoredAtom4034
    Fin15AnchoredAtom4037 Fin15AnchoredAtom4055 Fin15AnchoredAtom4083 Fin15AnchoredAtom4167
    Fin15AnchoredAtom4377 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31126 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom2128 chi ∧
      ¬Fin15AnchoredAtom2132 chi ∧
      ¬Fin15AnchoredAtom2150 chi ∧
      ¬Fin15AnchoredAtom2162 chi ∧
      ¬Fin15AnchoredAtom2165 chi ∧
      ¬Fin15AnchoredAtom2169 chi ∧
      ¬Fin15AnchoredAtom2173 chi ∧
      ¬Fin15AnchoredAtom2177 chi ∧
      ¬Fin15AnchoredAtom2195 chi ∧
      ¬Fin15AnchoredAtom2209 chi ∧
      ¬Fin15AnchoredAtom2213 chi ∧
      ¬Fin15AnchoredAtom2231 chi ∧
      ¬Fin15AnchoredAtom2259 chi ∧
      ¬Fin15AnchoredAtom2327 chi ∧
      ¬Fin15AnchoredAtom2330 chi ∧
      ¬Fin15AnchoredAtom2334 chi ∧
      ¬Fin15AnchoredAtom2338 chi ∧
      ¬Fin15AnchoredAtom2342 chi ∧
      ¬Fin15AnchoredAtom2360 chi ∧
      ¬Fin15AnchoredAtom2374 chi ∧
      ¬Fin15AnchoredAtom2378 chi ∧
      ¬Fin15AnchoredAtom2396 chi ∧
      ¬Fin15AnchoredAtom2424 chi ∧
      ¬Fin15AnchoredAtom2494 chi ∧
      ¬Fin15AnchoredAtom2498 chi ∧
      ¬Fin15AnchoredAtom2516 chi ∧
      ¬Fin15AnchoredAtom2544 chi ∧
      ¬Fin15AnchoredAtom2628 chi ∧
      ¬Fin15AnchoredAtom3537 chi ∧
      ¬Fin15AnchoredAtom3540 chi ∧
      ¬Fin15AnchoredAtom3544 chi ∧
      ¬Fin15AnchoredAtom3548 chi ∧
      ¬Fin15AnchoredAtom3552 chi ∧
      ¬Fin15AnchoredAtom3570 chi ∧
      ¬Fin15AnchoredAtom3584 chi ∧
      ¬Fin15AnchoredAtom3588 chi ∧
      ¬Fin15AnchoredAtom3606 chi ∧
      ¬Fin15AnchoredAtom3634 chi ∧
      ¬Fin15AnchoredAtom3704 chi ∧
      ¬Fin15AnchoredAtom3708 chi ∧
      ¬Fin15AnchoredAtom3726 chi ∧
      ¬Fin15AnchoredAtom3754 chi ∧
      ¬Fin15AnchoredAtom3838 chi ∧
      ¬Fin15AnchoredAtom4034 chi ∧
      ¬Fin15AnchoredAtom4038 chi ∧
      ¬Fin15AnchoredAtom4056 chi ∧
      ¬Fin15AnchoredAtom4084 chi ∧
      ¬Fin15AnchoredAtom4168 chi ∧
      ¬Fin15AnchoredAtom4378 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 5, 6, 9, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask08829
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2107 Fin15AnchoredAtom2108 Fin15AnchoredAtom2111
    Fin15AnchoredAtom2115 Fin15AnchoredAtom2117 Fin15AnchoredAtom2120 Fin15AnchoredAtom2124
    Fin15AnchoredAtom2128 Fin15AnchoredAtom2132 Fin15AnchoredAtom2150 Fin15AnchoredAtom2162
    Fin15AnchoredAtom2165 Fin15AnchoredAtom2169 Fin15AnchoredAtom2173 Fin15AnchoredAtom2177
    Fin15AnchoredAtom2195 Fin15AnchoredAtom2209 Fin15AnchoredAtom2213 Fin15AnchoredAtom2231
    Fin15AnchoredAtom2259 Fin15AnchoredAtom2327 Fin15AnchoredAtom2330 Fin15AnchoredAtom2334
    Fin15AnchoredAtom2338 Fin15AnchoredAtom2342 Fin15AnchoredAtom2360 Fin15AnchoredAtom2374
    Fin15AnchoredAtom2378 Fin15AnchoredAtom2396 Fin15AnchoredAtom2424 Fin15AnchoredAtom2494
    Fin15AnchoredAtom2498 Fin15AnchoredAtom2516 Fin15AnchoredAtom2544 Fin15AnchoredAtom2628
    Fin15AnchoredAtom3537 Fin15AnchoredAtom3540 Fin15AnchoredAtom3544 Fin15AnchoredAtom3548
    Fin15AnchoredAtom3552 Fin15AnchoredAtom3570 Fin15AnchoredAtom3584 Fin15AnchoredAtom3588
    Fin15AnchoredAtom3606 Fin15AnchoredAtom3634 Fin15AnchoredAtom3704 Fin15AnchoredAtom3708
    Fin15AnchoredAtom3726 Fin15AnchoredAtom3754 Fin15AnchoredAtom3838 Fin15AnchoredAtom4034
    Fin15AnchoredAtom4038 Fin15AnchoredAtom4056 Fin15AnchoredAtom4084 Fin15AnchoredAtom4168
    Fin15AnchoredAtom4378 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31127 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom2128 chi ∧
      ¬Fin15AnchoredAtom2133 chi ∧
      ¬Fin15AnchoredAtom2151 chi ∧
      ¬Fin15AnchoredAtom2162 chi ∧
      ¬Fin15AnchoredAtom2165 chi ∧
      ¬Fin15AnchoredAtom2170 chi ∧
      ¬Fin15AnchoredAtom2173 chi ∧
      ¬Fin15AnchoredAtom2178 chi ∧
      ¬Fin15AnchoredAtom2196 chi ∧
      ¬Fin15AnchoredAtom2209 chi ∧
      ¬Fin15AnchoredAtom2214 chi ∧
      ¬Fin15AnchoredAtom2232 chi ∧
      ¬Fin15AnchoredAtom2260 chi ∧
      ¬Fin15AnchoredAtom2327 chi ∧
      ¬Fin15AnchoredAtom2330 chi ∧
      ¬Fin15AnchoredAtom2335 chi ∧
      ¬Fin15AnchoredAtom2338 chi ∧
      ¬Fin15AnchoredAtom2343 chi ∧
      ¬Fin15AnchoredAtom2361 chi ∧
      ¬Fin15AnchoredAtom2374 chi ∧
      ¬Fin15AnchoredAtom2379 chi ∧
      ¬Fin15AnchoredAtom2397 chi ∧
      ¬Fin15AnchoredAtom2425 chi ∧
      ¬Fin15AnchoredAtom2494 chi ∧
      ¬Fin15AnchoredAtom2499 chi ∧
      ¬Fin15AnchoredAtom2517 chi ∧
      ¬Fin15AnchoredAtom2545 chi ∧
      ¬Fin15AnchoredAtom2629 chi ∧
      ¬Fin15AnchoredAtom3537 chi ∧
      ¬Fin15AnchoredAtom3540 chi ∧
      ¬Fin15AnchoredAtom3545 chi ∧
      ¬Fin15AnchoredAtom3548 chi ∧
      ¬Fin15AnchoredAtom3553 chi ∧
      ¬Fin15AnchoredAtom3571 chi ∧
      ¬Fin15AnchoredAtom3584 chi ∧
      ¬Fin15AnchoredAtom3589 chi ∧
      ¬Fin15AnchoredAtom3607 chi ∧
      ¬Fin15AnchoredAtom3635 chi ∧
      ¬Fin15AnchoredAtom3704 chi ∧
      ¬Fin15AnchoredAtom3709 chi ∧
      ¬Fin15AnchoredAtom3727 chi ∧
      ¬Fin15AnchoredAtom3755 chi ∧
      ¬Fin15AnchoredAtom3839 chi ∧
      ¬Fin15AnchoredAtom4034 chi ∧
      ¬Fin15AnchoredAtom4039 chi ∧
      ¬Fin15AnchoredAtom4057 chi ∧
      ¬Fin15AnchoredAtom4085 chi ∧
      ¬Fin15AnchoredAtom4169 chi ∧
      ¬Fin15AnchoredAtom4379 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 5, 6, 9, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17021
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2107 Fin15AnchoredAtom2108 Fin15AnchoredAtom2111
    Fin15AnchoredAtom2116 Fin15AnchoredAtom2117 Fin15AnchoredAtom2120 Fin15AnchoredAtom2125
    Fin15AnchoredAtom2128 Fin15AnchoredAtom2133 Fin15AnchoredAtom2151 Fin15AnchoredAtom2162
    Fin15AnchoredAtom2165 Fin15AnchoredAtom2170 Fin15AnchoredAtom2173 Fin15AnchoredAtom2178
    Fin15AnchoredAtom2196 Fin15AnchoredAtom2209 Fin15AnchoredAtom2214 Fin15AnchoredAtom2232
    Fin15AnchoredAtom2260 Fin15AnchoredAtom2327 Fin15AnchoredAtom2330 Fin15AnchoredAtom2335
    Fin15AnchoredAtom2338 Fin15AnchoredAtom2343 Fin15AnchoredAtom2361 Fin15AnchoredAtom2374
    Fin15AnchoredAtom2379 Fin15AnchoredAtom2397 Fin15AnchoredAtom2425 Fin15AnchoredAtom2494
    Fin15AnchoredAtom2499 Fin15AnchoredAtom2517 Fin15AnchoredAtom2545 Fin15AnchoredAtom2629
    Fin15AnchoredAtom3537 Fin15AnchoredAtom3540 Fin15AnchoredAtom3545 Fin15AnchoredAtom3548
    Fin15AnchoredAtom3553 Fin15AnchoredAtom3571 Fin15AnchoredAtom3584 Fin15AnchoredAtom3589
    Fin15AnchoredAtom3607 Fin15AnchoredAtom3635 Fin15AnchoredAtom3704 Fin15AnchoredAtom3709
    Fin15AnchoredAtom3727 Fin15AnchoredAtom3755 Fin15AnchoredAtom3839 Fin15AnchoredAtom4034
    Fin15AnchoredAtom4039 Fin15AnchoredAtom4057 Fin15AnchoredAtom4085 Fin15AnchoredAtom4169
    Fin15AnchoredAtom4379 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31128 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom2129 chi ∧
      ¬Fin15AnchoredAtom2131 chi ∧
      ¬Fin15AnchoredAtom2153 chi ∧
      ¬Fin15AnchoredAtom2162 chi ∧
      ¬Fin15AnchoredAtom2166 chi ∧
      ¬Fin15AnchoredAtom2168 chi ∧
      ¬Fin15AnchoredAtom2174 chi ∧
      ¬Fin15AnchoredAtom2176 chi ∧
      ¬Fin15AnchoredAtom2198 chi ∧
      ¬Fin15AnchoredAtom2210 chi ∧
      ¬Fin15AnchoredAtom2212 chi ∧
      ¬Fin15AnchoredAtom2234 chi ∧
      ¬Fin15AnchoredAtom2262 chi ∧
      ¬Fin15AnchoredAtom2327 chi ∧
      ¬Fin15AnchoredAtom2331 chi ∧
      ¬Fin15AnchoredAtom2333 chi ∧
      ¬Fin15AnchoredAtom2339 chi ∧
      ¬Fin15AnchoredAtom2341 chi ∧
      ¬Fin15AnchoredAtom2363 chi ∧
      ¬Fin15AnchoredAtom2375 chi ∧
      ¬Fin15AnchoredAtom2377 chi ∧
      ¬Fin15AnchoredAtom2399 chi ∧
      ¬Fin15AnchoredAtom2427 chi ∧
      ¬Fin15AnchoredAtom2495 chi ∧
      ¬Fin15AnchoredAtom2497 chi ∧
      ¬Fin15AnchoredAtom2519 chi ∧
      ¬Fin15AnchoredAtom2547 chi ∧
      ¬Fin15AnchoredAtom2631 chi ∧
      ¬Fin15AnchoredAtom3537 chi ∧
      ¬Fin15AnchoredAtom3541 chi ∧
      ¬Fin15AnchoredAtom3543 chi ∧
      ¬Fin15AnchoredAtom3549 chi ∧
      ¬Fin15AnchoredAtom3551 chi ∧
      ¬Fin15AnchoredAtom3573 chi ∧
      ¬Fin15AnchoredAtom3585 chi ∧
      ¬Fin15AnchoredAtom3587 chi ∧
      ¬Fin15AnchoredAtom3609 chi ∧
      ¬Fin15AnchoredAtom3637 chi ∧
      ¬Fin15AnchoredAtom3705 chi ∧
      ¬Fin15AnchoredAtom3707 chi ∧
      ¬Fin15AnchoredAtom3729 chi ∧
      ¬Fin15AnchoredAtom3757 chi ∧
      ¬Fin15AnchoredAtom3841 chi ∧
      ¬Fin15AnchoredAtom4035 chi ∧
      ¬Fin15AnchoredAtom4037 chi ∧
      ¬Fin15AnchoredAtom4059 chi ∧
      ¬Fin15AnchoredAtom4087 chi ∧
      ¬Fin15AnchoredAtom4171 chi ∧
      ¬Fin15AnchoredAtom4381 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 5, 6, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05245
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2107 Fin15AnchoredAtom2108 Fin15AnchoredAtom2112
    Fin15AnchoredAtom2114 Fin15AnchoredAtom2117 Fin15AnchoredAtom2121 Fin15AnchoredAtom2123
    Fin15AnchoredAtom2129 Fin15AnchoredAtom2131 Fin15AnchoredAtom2153 Fin15AnchoredAtom2162
    Fin15AnchoredAtom2166 Fin15AnchoredAtom2168 Fin15AnchoredAtom2174 Fin15AnchoredAtom2176
    Fin15AnchoredAtom2198 Fin15AnchoredAtom2210 Fin15AnchoredAtom2212 Fin15AnchoredAtom2234
    Fin15AnchoredAtom2262 Fin15AnchoredAtom2327 Fin15AnchoredAtom2331 Fin15AnchoredAtom2333
    Fin15AnchoredAtom2339 Fin15AnchoredAtom2341 Fin15AnchoredAtom2363 Fin15AnchoredAtom2375
    Fin15AnchoredAtom2377 Fin15AnchoredAtom2399 Fin15AnchoredAtom2427 Fin15AnchoredAtom2495
    Fin15AnchoredAtom2497 Fin15AnchoredAtom2519 Fin15AnchoredAtom2547 Fin15AnchoredAtom2631
    Fin15AnchoredAtom3537 Fin15AnchoredAtom3541 Fin15AnchoredAtom3543 Fin15AnchoredAtom3549
    Fin15AnchoredAtom3551 Fin15AnchoredAtom3573 Fin15AnchoredAtom3585 Fin15AnchoredAtom3587
    Fin15AnchoredAtom3609 Fin15AnchoredAtom3637 Fin15AnchoredAtom3705 Fin15AnchoredAtom3707
    Fin15AnchoredAtom3729 Fin15AnchoredAtom3757 Fin15AnchoredAtom3841 Fin15AnchoredAtom4035
    Fin15AnchoredAtom4037 Fin15AnchoredAtom4059 Fin15AnchoredAtom4087 Fin15AnchoredAtom4171
    Fin15AnchoredAtom4381 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31129 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom2129 chi ∧
      ¬Fin15AnchoredAtom2132 chi ∧
      ¬Fin15AnchoredAtom2154 chi ∧
      ¬Fin15AnchoredAtom2162 chi ∧
      ¬Fin15AnchoredAtom2166 chi ∧
      ¬Fin15AnchoredAtom2169 chi ∧
      ¬Fin15AnchoredAtom2174 chi ∧
      ¬Fin15AnchoredAtom2177 chi ∧
      ¬Fin15AnchoredAtom2199 chi ∧
      ¬Fin15AnchoredAtom2210 chi ∧
      ¬Fin15AnchoredAtom2213 chi ∧
      ¬Fin15AnchoredAtom2235 chi ∧
      ¬Fin15AnchoredAtom2263 chi ∧
      ¬Fin15AnchoredAtom2327 chi ∧
      ¬Fin15AnchoredAtom2331 chi ∧
      ¬Fin15AnchoredAtom2334 chi ∧
      ¬Fin15AnchoredAtom2339 chi ∧
      ¬Fin15AnchoredAtom2342 chi ∧
      ¬Fin15AnchoredAtom2364 chi ∧
      ¬Fin15AnchoredAtom2375 chi ∧
      ¬Fin15AnchoredAtom2378 chi ∧
      ¬Fin15AnchoredAtom2400 chi ∧
      ¬Fin15AnchoredAtom2428 chi ∧
      ¬Fin15AnchoredAtom2495 chi ∧
      ¬Fin15AnchoredAtom2498 chi ∧
      ¬Fin15AnchoredAtom2520 chi ∧
      ¬Fin15AnchoredAtom2548 chi ∧
      ¬Fin15AnchoredAtom2632 chi ∧
      ¬Fin15AnchoredAtom3537 chi ∧
      ¬Fin15AnchoredAtom3541 chi ∧
      ¬Fin15AnchoredAtom3544 chi ∧
      ¬Fin15AnchoredAtom3549 chi ∧
      ¬Fin15AnchoredAtom3552 chi ∧
      ¬Fin15AnchoredAtom3574 chi ∧
      ¬Fin15AnchoredAtom3585 chi ∧
      ¬Fin15AnchoredAtom3588 chi ∧
      ¬Fin15AnchoredAtom3610 chi ∧
      ¬Fin15AnchoredAtom3638 chi ∧
      ¬Fin15AnchoredAtom3705 chi ∧
      ¬Fin15AnchoredAtom3708 chi ∧
      ¬Fin15AnchoredAtom3730 chi ∧
      ¬Fin15AnchoredAtom3758 chi ∧
      ¬Fin15AnchoredAtom3842 chi ∧
      ¬Fin15AnchoredAtom4035 chi ∧
      ¬Fin15AnchoredAtom4038 chi ∧
      ¬Fin15AnchoredAtom4060 chi ∧
      ¬Fin15AnchoredAtom4088 chi ∧
      ¬Fin15AnchoredAtom4172 chi ∧
      ¬Fin15AnchoredAtom4382 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 5, 6, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09341
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2107 Fin15AnchoredAtom2108 Fin15AnchoredAtom2112
    Fin15AnchoredAtom2115 Fin15AnchoredAtom2117 Fin15AnchoredAtom2121 Fin15AnchoredAtom2124
    Fin15AnchoredAtom2129 Fin15AnchoredAtom2132 Fin15AnchoredAtom2154 Fin15AnchoredAtom2162
    Fin15AnchoredAtom2166 Fin15AnchoredAtom2169 Fin15AnchoredAtom2174 Fin15AnchoredAtom2177
    Fin15AnchoredAtom2199 Fin15AnchoredAtom2210 Fin15AnchoredAtom2213 Fin15AnchoredAtom2235
    Fin15AnchoredAtom2263 Fin15AnchoredAtom2327 Fin15AnchoredAtom2331 Fin15AnchoredAtom2334
    Fin15AnchoredAtom2339 Fin15AnchoredAtom2342 Fin15AnchoredAtom2364 Fin15AnchoredAtom2375
    Fin15AnchoredAtom2378 Fin15AnchoredAtom2400 Fin15AnchoredAtom2428 Fin15AnchoredAtom2495
    Fin15AnchoredAtom2498 Fin15AnchoredAtom2520 Fin15AnchoredAtom2548 Fin15AnchoredAtom2632
    Fin15AnchoredAtom3537 Fin15AnchoredAtom3541 Fin15AnchoredAtom3544 Fin15AnchoredAtom3549
    Fin15AnchoredAtom3552 Fin15AnchoredAtom3574 Fin15AnchoredAtom3585 Fin15AnchoredAtom3588
    Fin15AnchoredAtom3610 Fin15AnchoredAtom3638 Fin15AnchoredAtom3705 Fin15AnchoredAtom3708
    Fin15AnchoredAtom3730 Fin15AnchoredAtom3758 Fin15AnchoredAtom3842 Fin15AnchoredAtom4035
    Fin15AnchoredAtom4038 Fin15AnchoredAtom4060 Fin15AnchoredAtom4088 Fin15AnchoredAtom4172
    Fin15AnchoredAtom4382 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31130 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom2129 chi ∧
      ¬Fin15AnchoredAtom2133 chi ∧
      ¬Fin15AnchoredAtom2155 chi ∧
      ¬Fin15AnchoredAtom2162 chi ∧
      ¬Fin15AnchoredAtom2166 chi ∧
      ¬Fin15AnchoredAtom2170 chi ∧
      ¬Fin15AnchoredAtom2174 chi ∧
      ¬Fin15AnchoredAtom2178 chi ∧
      ¬Fin15AnchoredAtom2200 chi ∧
      ¬Fin15AnchoredAtom2210 chi ∧
      ¬Fin15AnchoredAtom2214 chi ∧
      ¬Fin15AnchoredAtom2236 chi ∧
      ¬Fin15AnchoredAtom2264 chi ∧
      ¬Fin15AnchoredAtom2327 chi ∧
      ¬Fin15AnchoredAtom2331 chi ∧
      ¬Fin15AnchoredAtom2335 chi ∧
      ¬Fin15AnchoredAtom2339 chi ∧
      ¬Fin15AnchoredAtom2343 chi ∧
      ¬Fin15AnchoredAtom2365 chi ∧
      ¬Fin15AnchoredAtom2375 chi ∧
      ¬Fin15AnchoredAtom2379 chi ∧
      ¬Fin15AnchoredAtom2401 chi ∧
      ¬Fin15AnchoredAtom2429 chi ∧
      ¬Fin15AnchoredAtom2495 chi ∧
      ¬Fin15AnchoredAtom2499 chi ∧
      ¬Fin15AnchoredAtom2521 chi ∧
      ¬Fin15AnchoredAtom2549 chi ∧
      ¬Fin15AnchoredAtom2633 chi ∧
      ¬Fin15AnchoredAtom3537 chi ∧
      ¬Fin15AnchoredAtom3541 chi ∧
      ¬Fin15AnchoredAtom3545 chi ∧
      ¬Fin15AnchoredAtom3549 chi ∧
      ¬Fin15AnchoredAtom3553 chi ∧
      ¬Fin15AnchoredAtom3575 chi ∧
      ¬Fin15AnchoredAtom3585 chi ∧
      ¬Fin15AnchoredAtom3589 chi ∧
      ¬Fin15AnchoredAtom3611 chi ∧
      ¬Fin15AnchoredAtom3639 chi ∧
      ¬Fin15AnchoredAtom3705 chi ∧
      ¬Fin15AnchoredAtom3709 chi ∧
      ¬Fin15AnchoredAtom3731 chi ∧
      ¬Fin15AnchoredAtom3759 chi ∧
      ¬Fin15AnchoredAtom3843 chi ∧
      ¬Fin15AnchoredAtom4035 chi ∧
      ¬Fin15AnchoredAtom4039 chi ∧
      ¬Fin15AnchoredAtom4061 chi ∧
      ¬Fin15AnchoredAtom4089 chi ∧
      ¬Fin15AnchoredAtom4173 chi ∧
      ¬Fin15AnchoredAtom4383 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 5, 6, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17533
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2107 Fin15AnchoredAtom2108 Fin15AnchoredAtom2112
    Fin15AnchoredAtom2116 Fin15AnchoredAtom2117 Fin15AnchoredAtom2121 Fin15AnchoredAtom2125
    Fin15AnchoredAtom2129 Fin15AnchoredAtom2133 Fin15AnchoredAtom2155 Fin15AnchoredAtom2162
    Fin15AnchoredAtom2166 Fin15AnchoredAtom2170 Fin15AnchoredAtom2174 Fin15AnchoredAtom2178
    Fin15AnchoredAtom2200 Fin15AnchoredAtom2210 Fin15AnchoredAtom2214 Fin15AnchoredAtom2236
    Fin15AnchoredAtom2264 Fin15AnchoredAtom2327 Fin15AnchoredAtom2331 Fin15AnchoredAtom2335
    Fin15AnchoredAtom2339 Fin15AnchoredAtom2343 Fin15AnchoredAtom2365 Fin15AnchoredAtom2375
    Fin15AnchoredAtom2379 Fin15AnchoredAtom2401 Fin15AnchoredAtom2429 Fin15AnchoredAtom2495
    Fin15AnchoredAtom2499 Fin15AnchoredAtom2521 Fin15AnchoredAtom2549 Fin15AnchoredAtom2633
    Fin15AnchoredAtom3537 Fin15AnchoredAtom3541 Fin15AnchoredAtom3545 Fin15AnchoredAtom3549
    Fin15AnchoredAtom3553 Fin15AnchoredAtom3575 Fin15AnchoredAtom3585 Fin15AnchoredAtom3589
    Fin15AnchoredAtom3611 Fin15AnchoredAtom3639 Fin15AnchoredAtom3705 Fin15AnchoredAtom3709
    Fin15AnchoredAtom3731 Fin15AnchoredAtom3759 Fin15AnchoredAtom3843 Fin15AnchoredAtom4035
    Fin15AnchoredAtom4039 Fin15AnchoredAtom4061 Fin15AnchoredAtom4089 Fin15AnchoredAtom4173
    Fin15AnchoredAtom4383 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31131 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom2131 chi ∧
      ¬Fin15AnchoredAtom2132 chi ∧
      ¬Fin15AnchoredAtom2159 chi ∧
      ¬Fin15AnchoredAtom2162 chi ∧
      ¬Fin15AnchoredAtom2168 chi ∧
      ¬Fin15AnchoredAtom2169 chi ∧
      ¬Fin15AnchoredAtom2176 chi ∧
      ¬Fin15AnchoredAtom2177 chi ∧
      ¬Fin15AnchoredAtom2204 chi ∧
      ¬Fin15AnchoredAtom2212 chi ∧
      ¬Fin15AnchoredAtom2213 chi ∧
      ¬Fin15AnchoredAtom2240 chi ∧
      ¬Fin15AnchoredAtom2268 chi ∧
      ¬Fin15AnchoredAtom2327 chi ∧
      ¬Fin15AnchoredAtom2333 chi ∧
      ¬Fin15AnchoredAtom2334 chi ∧
      ¬Fin15AnchoredAtom2341 chi ∧
      ¬Fin15AnchoredAtom2342 chi ∧
      ¬Fin15AnchoredAtom2369 chi ∧
      ¬Fin15AnchoredAtom2377 chi ∧
      ¬Fin15AnchoredAtom2378 chi ∧
      ¬Fin15AnchoredAtom2405 chi ∧
      ¬Fin15AnchoredAtom2433 chi ∧
      ¬Fin15AnchoredAtom2497 chi ∧
      ¬Fin15AnchoredAtom2498 chi ∧
      ¬Fin15AnchoredAtom2525 chi ∧
      ¬Fin15AnchoredAtom2553 chi ∧
      ¬Fin15AnchoredAtom2637 chi ∧
      ¬Fin15AnchoredAtom3537 chi ∧
      ¬Fin15AnchoredAtom3543 chi ∧
      ¬Fin15AnchoredAtom3544 chi ∧
      ¬Fin15AnchoredAtom3551 chi ∧
      ¬Fin15AnchoredAtom3552 chi ∧
      ¬Fin15AnchoredAtom3579 chi ∧
      ¬Fin15AnchoredAtom3587 chi ∧
      ¬Fin15AnchoredAtom3588 chi ∧
      ¬Fin15AnchoredAtom3615 chi ∧
      ¬Fin15AnchoredAtom3643 chi ∧
      ¬Fin15AnchoredAtom3707 chi ∧
      ¬Fin15AnchoredAtom3708 chi ∧
      ¬Fin15AnchoredAtom3735 chi ∧
      ¬Fin15AnchoredAtom3763 chi ∧
      ¬Fin15AnchoredAtom3847 chi ∧
      ¬Fin15AnchoredAtom4037 chi ∧
      ¬Fin15AnchoredAtom4038 chi ∧
      ¬Fin15AnchoredAtom4065 chi ∧
      ¬Fin15AnchoredAtom4093 chi ∧
      ¬Fin15AnchoredAtom4177 chi ∧
      ¬Fin15AnchoredAtom4387 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 5, 6, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask12413
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2107 Fin15AnchoredAtom2108 Fin15AnchoredAtom2114
    Fin15AnchoredAtom2115 Fin15AnchoredAtom2117 Fin15AnchoredAtom2123 Fin15AnchoredAtom2124
    Fin15AnchoredAtom2131 Fin15AnchoredAtom2132 Fin15AnchoredAtom2159 Fin15AnchoredAtom2162
    Fin15AnchoredAtom2168 Fin15AnchoredAtom2169 Fin15AnchoredAtom2176 Fin15AnchoredAtom2177
    Fin15AnchoredAtom2204 Fin15AnchoredAtom2212 Fin15AnchoredAtom2213 Fin15AnchoredAtom2240
    Fin15AnchoredAtom2268 Fin15AnchoredAtom2327 Fin15AnchoredAtom2333 Fin15AnchoredAtom2334
    Fin15AnchoredAtom2341 Fin15AnchoredAtom2342 Fin15AnchoredAtom2369 Fin15AnchoredAtom2377
    Fin15AnchoredAtom2378 Fin15AnchoredAtom2405 Fin15AnchoredAtom2433 Fin15AnchoredAtom2497
    Fin15AnchoredAtom2498 Fin15AnchoredAtom2525 Fin15AnchoredAtom2553 Fin15AnchoredAtom2637
    Fin15AnchoredAtom3537 Fin15AnchoredAtom3543 Fin15AnchoredAtom3544 Fin15AnchoredAtom3551
    Fin15AnchoredAtom3552 Fin15AnchoredAtom3579 Fin15AnchoredAtom3587 Fin15AnchoredAtom3588
    Fin15AnchoredAtom3615 Fin15AnchoredAtom3643 Fin15AnchoredAtom3707 Fin15AnchoredAtom3708
    Fin15AnchoredAtom3735 Fin15AnchoredAtom3763 Fin15AnchoredAtom3847 Fin15AnchoredAtom4037
    Fin15AnchoredAtom4038 Fin15AnchoredAtom4065 Fin15AnchoredAtom4093 Fin15AnchoredAtom4177
    Fin15AnchoredAtom4387 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31132 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom2131 chi ∧
      ¬Fin15AnchoredAtom2133 chi ∧
      ¬Fin15AnchoredAtom2160 chi ∧
      ¬Fin15AnchoredAtom2162 chi ∧
      ¬Fin15AnchoredAtom2168 chi ∧
      ¬Fin15AnchoredAtom2170 chi ∧
      ¬Fin15AnchoredAtom2176 chi ∧
      ¬Fin15AnchoredAtom2178 chi ∧
      ¬Fin15AnchoredAtom2205 chi ∧
      ¬Fin15AnchoredAtom2212 chi ∧
      ¬Fin15AnchoredAtom2214 chi ∧
      ¬Fin15AnchoredAtom2241 chi ∧
      ¬Fin15AnchoredAtom2269 chi ∧
      ¬Fin15AnchoredAtom2327 chi ∧
      ¬Fin15AnchoredAtom2333 chi ∧
      ¬Fin15AnchoredAtom2335 chi ∧
      ¬Fin15AnchoredAtom2341 chi ∧
      ¬Fin15AnchoredAtom2343 chi ∧
      ¬Fin15AnchoredAtom2370 chi ∧
      ¬Fin15AnchoredAtom2377 chi ∧
      ¬Fin15AnchoredAtom2379 chi ∧
      ¬Fin15AnchoredAtom2406 chi ∧
      ¬Fin15AnchoredAtom2434 chi ∧
      ¬Fin15AnchoredAtom2497 chi ∧
      ¬Fin15AnchoredAtom2499 chi ∧
      ¬Fin15AnchoredAtom2526 chi ∧
      ¬Fin15AnchoredAtom2554 chi ∧
      ¬Fin15AnchoredAtom2638 chi ∧
      ¬Fin15AnchoredAtom3537 chi ∧
      ¬Fin15AnchoredAtom3543 chi ∧
      ¬Fin15AnchoredAtom3545 chi ∧
      ¬Fin15AnchoredAtom3551 chi ∧
      ¬Fin15AnchoredAtom3553 chi ∧
      ¬Fin15AnchoredAtom3580 chi ∧
      ¬Fin15AnchoredAtom3587 chi ∧
      ¬Fin15AnchoredAtom3589 chi ∧
      ¬Fin15AnchoredAtom3616 chi ∧
      ¬Fin15AnchoredAtom3644 chi ∧
      ¬Fin15AnchoredAtom3707 chi ∧
      ¬Fin15AnchoredAtom3709 chi ∧
      ¬Fin15AnchoredAtom3736 chi ∧
      ¬Fin15AnchoredAtom3764 chi ∧
      ¬Fin15AnchoredAtom3848 chi ∧
      ¬Fin15AnchoredAtom4037 chi ∧
      ¬Fin15AnchoredAtom4039 chi ∧
      ¬Fin15AnchoredAtom4066 chi ∧
      ¬Fin15AnchoredAtom4094 chi ∧
      ¬Fin15AnchoredAtom4178 chi ∧
      ¬Fin15AnchoredAtom4388 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 5, 6, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask20605
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2107 Fin15AnchoredAtom2108 Fin15AnchoredAtom2114
    Fin15AnchoredAtom2116 Fin15AnchoredAtom2117 Fin15AnchoredAtom2123 Fin15AnchoredAtom2125
    Fin15AnchoredAtom2131 Fin15AnchoredAtom2133 Fin15AnchoredAtom2160 Fin15AnchoredAtom2162
    Fin15AnchoredAtom2168 Fin15AnchoredAtom2170 Fin15AnchoredAtom2176 Fin15AnchoredAtom2178
    Fin15AnchoredAtom2205 Fin15AnchoredAtom2212 Fin15AnchoredAtom2214 Fin15AnchoredAtom2241
    Fin15AnchoredAtom2269 Fin15AnchoredAtom2327 Fin15AnchoredAtom2333 Fin15AnchoredAtom2335
    Fin15AnchoredAtom2341 Fin15AnchoredAtom2343 Fin15AnchoredAtom2370 Fin15AnchoredAtom2377
    Fin15AnchoredAtom2379 Fin15AnchoredAtom2406 Fin15AnchoredAtom2434 Fin15AnchoredAtom2497
    Fin15AnchoredAtom2499 Fin15AnchoredAtom2526 Fin15AnchoredAtom2554 Fin15AnchoredAtom2638
    Fin15AnchoredAtom3537 Fin15AnchoredAtom3543 Fin15AnchoredAtom3545 Fin15AnchoredAtom3551
    Fin15AnchoredAtom3553 Fin15AnchoredAtom3580 Fin15AnchoredAtom3587 Fin15AnchoredAtom3589
    Fin15AnchoredAtom3616 Fin15AnchoredAtom3644 Fin15AnchoredAtom3707 Fin15AnchoredAtom3709
    Fin15AnchoredAtom3736 Fin15AnchoredAtom3764 Fin15AnchoredAtom3848 Fin15AnchoredAtom4037
    Fin15AnchoredAtom4039 Fin15AnchoredAtom4066 Fin15AnchoredAtom4094 Fin15AnchoredAtom4178
    Fin15AnchoredAtom4388 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31133 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom2132 chi ∧
      ¬Fin15AnchoredAtom2133 chi ∧
      ¬Fin15AnchoredAtom2161 chi ∧
      ¬Fin15AnchoredAtom2162 chi ∧
      ¬Fin15AnchoredAtom2169 chi ∧
      ¬Fin15AnchoredAtom2170 chi ∧
      ¬Fin15AnchoredAtom2177 chi ∧
      ¬Fin15AnchoredAtom2178 chi ∧
      ¬Fin15AnchoredAtom2206 chi ∧
      ¬Fin15AnchoredAtom2213 chi ∧
      ¬Fin15AnchoredAtom2214 chi ∧
      ¬Fin15AnchoredAtom2242 chi ∧
      ¬Fin15AnchoredAtom2270 chi ∧
      ¬Fin15AnchoredAtom2327 chi ∧
      ¬Fin15AnchoredAtom2334 chi ∧
      ¬Fin15AnchoredAtom2335 chi ∧
      ¬Fin15AnchoredAtom2342 chi ∧
      ¬Fin15AnchoredAtom2343 chi ∧
      ¬Fin15AnchoredAtom2371 chi ∧
      ¬Fin15AnchoredAtom2378 chi ∧
      ¬Fin15AnchoredAtom2379 chi ∧
      ¬Fin15AnchoredAtom2407 chi ∧
      ¬Fin15AnchoredAtom2435 chi ∧
      ¬Fin15AnchoredAtom2498 chi ∧
      ¬Fin15AnchoredAtom2499 chi ∧
      ¬Fin15AnchoredAtom2527 chi ∧
      ¬Fin15AnchoredAtom2555 chi ∧
      ¬Fin15AnchoredAtom2639 chi ∧
      ¬Fin15AnchoredAtom3537 chi ∧
      ¬Fin15AnchoredAtom3544 chi ∧
      ¬Fin15AnchoredAtom3545 chi ∧
      ¬Fin15AnchoredAtom3552 chi ∧
      ¬Fin15AnchoredAtom3553 chi ∧
      ¬Fin15AnchoredAtom3581 chi ∧
      ¬Fin15AnchoredAtom3588 chi ∧
      ¬Fin15AnchoredAtom3589 chi ∧
      ¬Fin15AnchoredAtom3617 chi ∧
      ¬Fin15AnchoredAtom3645 chi ∧
      ¬Fin15AnchoredAtom3708 chi ∧
      ¬Fin15AnchoredAtom3709 chi ∧
      ¬Fin15AnchoredAtom3737 chi ∧
      ¬Fin15AnchoredAtom3765 chi ∧
      ¬Fin15AnchoredAtom3849 chi ∧
      ¬Fin15AnchoredAtom4038 chi ∧
      ¬Fin15AnchoredAtom4039 chi ∧
      ¬Fin15AnchoredAtom4067 chi ∧
      ¬Fin15AnchoredAtom4095 chi ∧
      ¬Fin15AnchoredAtom4179 chi ∧
      ¬Fin15AnchoredAtom4389 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 5, 6, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask24701
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2107 Fin15AnchoredAtom2108 Fin15AnchoredAtom2115
    Fin15AnchoredAtom2116 Fin15AnchoredAtom2117 Fin15AnchoredAtom2124 Fin15AnchoredAtom2125
    Fin15AnchoredAtom2132 Fin15AnchoredAtom2133 Fin15AnchoredAtom2161 Fin15AnchoredAtom2162
    Fin15AnchoredAtom2169 Fin15AnchoredAtom2170 Fin15AnchoredAtom2177 Fin15AnchoredAtom2178
    Fin15AnchoredAtom2206 Fin15AnchoredAtom2213 Fin15AnchoredAtom2214 Fin15AnchoredAtom2242
    Fin15AnchoredAtom2270 Fin15AnchoredAtom2327 Fin15AnchoredAtom2334 Fin15AnchoredAtom2335
    Fin15AnchoredAtom2342 Fin15AnchoredAtom2343 Fin15AnchoredAtom2371 Fin15AnchoredAtom2378
    Fin15AnchoredAtom2379 Fin15AnchoredAtom2407 Fin15AnchoredAtom2435 Fin15AnchoredAtom2498
    Fin15AnchoredAtom2499 Fin15AnchoredAtom2527 Fin15AnchoredAtom2555 Fin15AnchoredAtom2639
    Fin15AnchoredAtom3537 Fin15AnchoredAtom3544 Fin15AnchoredAtom3545 Fin15AnchoredAtom3552
    Fin15AnchoredAtom3553 Fin15AnchoredAtom3581 Fin15AnchoredAtom3588 Fin15AnchoredAtom3589
    Fin15AnchoredAtom3617 Fin15AnchoredAtom3645 Fin15AnchoredAtom3708 Fin15AnchoredAtom3709
    Fin15AnchoredAtom3737 Fin15AnchoredAtom3765 Fin15AnchoredAtom3849 Fin15AnchoredAtom4038
    Fin15AnchoredAtom4039 Fin15AnchoredAtom4067 Fin15AnchoredAtom4095 Fin15AnchoredAtom4179
    Fin15AnchoredAtom4389 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31134 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2135 chi ∧
      ¬Fin15AnchoredAtom2136 chi ∧
      ¬Fin15AnchoredAtom2147 chi ∧
      ¬Fin15AnchoredAtom2163 chi ∧
      ¬Fin15AnchoredAtom2165 chi ∧
      ¬Fin15AnchoredAtom2166 chi ∧
      ¬Fin15AnchoredAtom2180 chi ∧
      ¬Fin15AnchoredAtom2181 chi ∧
      ¬Fin15AnchoredAtom2192 chi ∧
      ¬Fin15AnchoredAtom2216 chi ∧
      ¬Fin15AnchoredAtom2217 chi ∧
      ¬Fin15AnchoredAtom2228 chi ∧
      ¬Fin15AnchoredAtom2277 chi ∧
      ¬Fin15AnchoredAtom2328 chi ∧
      ¬Fin15AnchoredAtom2330 chi ∧
      ¬Fin15AnchoredAtom2331 chi ∧
      ¬Fin15AnchoredAtom2345 chi ∧
      ¬Fin15AnchoredAtom2346 chi ∧
      ¬Fin15AnchoredAtom2357 chi ∧
      ¬Fin15AnchoredAtom2381 chi ∧
      ¬Fin15AnchoredAtom2382 chi ∧
      ¬Fin15AnchoredAtom2393 chi ∧
      ¬Fin15AnchoredAtom2442 chi ∧
      ¬Fin15AnchoredAtom2501 chi ∧
      ¬Fin15AnchoredAtom2502 chi ∧
      ¬Fin15AnchoredAtom2513 chi ∧
      ¬Fin15AnchoredAtom2562 chi ∧
      ¬Fin15AnchoredAtom2646 chi ∧
      ¬Fin15AnchoredAtom3538 chi ∧
      ¬Fin15AnchoredAtom3540 chi ∧
      ¬Fin15AnchoredAtom3541 chi ∧
      ¬Fin15AnchoredAtom3555 chi ∧
      ¬Fin15AnchoredAtom3556 chi ∧
      ¬Fin15AnchoredAtom3567 chi ∧
      ¬Fin15AnchoredAtom3591 chi ∧
      ¬Fin15AnchoredAtom3592 chi ∧
      ¬Fin15AnchoredAtom3603 chi ∧
      ¬Fin15AnchoredAtom3652 chi ∧
      ¬Fin15AnchoredAtom3711 chi ∧
      ¬Fin15AnchoredAtom3712 chi ∧
      ¬Fin15AnchoredAtom3723 chi ∧
      ¬Fin15AnchoredAtom3772 chi ∧
      ¬Fin15AnchoredAtom3856 chi ∧
      ¬Fin15AnchoredAtom4041 chi ∧
      ¬Fin15AnchoredAtom4042 chi ∧
      ¬Fin15AnchoredAtom4053 chi ∧
      ¬Fin15AnchoredAtom4102 chi ∧
      ¬Fin15AnchoredAtom4186 chi ∧
      ¬Fin15AnchoredAtom4396 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 5, 7, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask01725
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2107 Fin15AnchoredAtom2109 Fin15AnchoredAtom2111
    Fin15AnchoredAtom2112 Fin15AnchoredAtom2118 Fin15AnchoredAtom2120 Fin15AnchoredAtom2121
    Fin15AnchoredAtom2135 Fin15AnchoredAtom2136 Fin15AnchoredAtom2147 Fin15AnchoredAtom2163
    Fin15AnchoredAtom2165 Fin15AnchoredAtom2166 Fin15AnchoredAtom2180 Fin15AnchoredAtom2181
    Fin15AnchoredAtom2192 Fin15AnchoredAtom2216 Fin15AnchoredAtom2217 Fin15AnchoredAtom2228
    Fin15AnchoredAtom2277 Fin15AnchoredAtom2328 Fin15AnchoredAtom2330 Fin15AnchoredAtom2331
    Fin15AnchoredAtom2345 Fin15AnchoredAtom2346 Fin15AnchoredAtom2357 Fin15AnchoredAtom2381
    Fin15AnchoredAtom2382 Fin15AnchoredAtom2393 Fin15AnchoredAtom2442 Fin15AnchoredAtom2501
    Fin15AnchoredAtom2502 Fin15AnchoredAtom2513 Fin15AnchoredAtom2562 Fin15AnchoredAtom2646
    Fin15AnchoredAtom3538 Fin15AnchoredAtom3540 Fin15AnchoredAtom3541 Fin15AnchoredAtom3555
    Fin15AnchoredAtom3556 Fin15AnchoredAtom3567 Fin15AnchoredAtom3591 Fin15AnchoredAtom3592
    Fin15AnchoredAtom3603 Fin15AnchoredAtom3652 Fin15AnchoredAtom3711 Fin15AnchoredAtom3712
    Fin15AnchoredAtom3723 Fin15AnchoredAtom3772 Fin15AnchoredAtom3856 Fin15AnchoredAtom4041
    Fin15AnchoredAtom4042 Fin15AnchoredAtom4053 Fin15AnchoredAtom4102 Fin15AnchoredAtom4186
    Fin15AnchoredAtom4396 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31135 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom2135 chi ∧
      ¬Fin15AnchoredAtom2138 chi ∧
      ¬Fin15AnchoredAtom2149 chi ∧
      ¬Fin15AnchoredAtom2163 chi ∧
      ¬Fin15AnchoredAtom2165 chi ∧
      ¬Fin15AnchoredAtom2168 chi ∧
      ¬Fin15AnchoredAtom2180 chi ∧
      ¬Fin15AnchoredAtom2183 chi ∧
      ¬Fin15AnchoredAtom2194 chi ∧
      ¬Fin15AnchoredAtom2216 chi ∧
      ¬Fin15AnchoredAtom2219 chi ∧
      ¬Fin15AnchoredAtom2230 chi ∧
      ¬Fin15AnchoredAtom2279 chi ∧
      ¬Fin15AnchoredAtom2328 chi ∧
      ¬Fin15AnchoredAtom2330 chi ∧
      ¬Fin15AnchoredAtom2333 chi ∧
      ¬Fin15AnchoredAtom2345 chi ∧
      ¬Fin15AnchoredAtom2348 chi ∧
      ¬Fin15AnchoredAtom2359 chi ∧
      ¬Fin15AnchoredAtom2381 chi ∧
      ¬Fin15AnchoredAtom2384 chi ∧
      ¬Fin15AnchoredAtom2395 chi ∧
      ¬Fin15AnchoredAtom2444 chi ∧
      ¬Fin15AnchoredAtom2501 chi ∧
      ¬Fin15AnchoredAtom2504 chi ∧
      ¬Fin15AnchoredAtom2515 chi ∧
      ¬Fin15AnchoredAtom2564 chi ∧
      ¬Fin15AnchoredAtom2648 chi ∧
      ¬Fin15AnchoredAtom3538 chi ∧
      ¬Fin15AnchoredAtom3540 chi ∧
      ¬Fin15AnchoredAtom3543 chi ∧
      ¬Fin15AnchoredAtom3555 chi ∧
      ¬Fin15AnchoredAtom3558 chi ∧
      ¬Fin15AnchoredAtom3569 chi ∧
      ¬Fin15AnchoredAtom3591 chi ∧
      ¬Fin15AnchoredAtom3594 chi ∧
      ¬Fin15AnchoredAtom3605 chi ∧
      ¬Fin15AnchoredAtom3654 chi ∧
      ¬Fin15AnchoredAtom3711 chi ∧
      ¬Fin15AnchoredAtom3714 chi ∧
      ¬Fin15AnchoredAtom3725 chi ∧
      ¬Fin15AnchoredAtom3774 chi ∧
      ¬Fin15AnchoredAtom3858 chi ∧
      ¬Fin15AnchoredAtom4041 chi ∧
      ¬Fin15AnchoredAtom4044 chi ∧
      ¬Fin15AnchoredAtom4055 chi ∧
      ¬Fin15AnchoredAtom4104 chi ∧
      ¬Fin15AnchoredAtom4188 chi ∧
      ¬Fin15AnchoredAtom4398 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 5, 7, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask04797
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2107 Fin15AnchoredAtom2109 Fin15AnchoredAtom2111
    Fin15AnchoredAtom2114 Fin15AnchoredAtom2118 Fin15AnchoredAtom2120 Fin15AnchoredAtom2123
    Fin15AnchoredAtom2135 Fin15AnchoredAtom2138 Fin15AnchoredAtom2149 Fin15AnchoredAtom2163
    Fin15AnchoredAtom2165 Fin15AnchoredAtom2168 Fin15AnchoredAtom2180 Fin15AnchoredAtom2183
    Fin15AnchoredAtom2194 Fin15AnchoredAtom2216 Fin15AnchoredAtom2219 Fin15AnchoredAtom2230
    Fin15AnchoredAtom2279 Fin15AnchoredAtom2328 Fin15AnchoredAtom2330 Fin15AnchoredAtom2333
    Fin15AnchoredAtom2345 Fin15AnchoredAtom2348 Fin15AnchoredAtom2359 Fin15AnchoredAtom2381
    Fin15AnchoredAtom2384 Fin15AnchoredAtom2395 Fin15AnchoredAtom2444 Fin15AnchoredAtom2501
    Fin15AnchoredAtom2504 Fin15AnchoredAtom2515 Fin15AnchoredAtom2564 Fin15AnchoredAtom2648
    Fin15AnchoredAtom3538 Fin15AnchoredAtom3540 Fin15AnchoredAtom3543 Fin15AnchoredAtom3555
    Fin15AnchoredAtom3558 Fin15AnchoredAtom3569 Fin15AnchoredAtom3591 Fin15AnchoredAtom3594
    Fin15AnchoredAtom3605 Fin15AnchoredAtom3654 Fin15AnchoredAtom3711 Fin15AnchoredAtom3714
    Fin15AnchoredAtom3725 Fin15AnchoredAtom3774 Fin15AnchoredAtom3858 Fin15AnchoredAtom4041
    Fin15AnchoredAtom4044 Fin15AnchoredAtom4055 Fin15AnchoredAtom4104 Fin15AnchoredAtom4188
    Fin15AnchoredAtom4398 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31136 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom2135 chi ∧
      ¬Fin15AnchoredAtom2139 chi ∧
      ¬Fin15AnchoredAtom2150 chi ∧
      ¬Fin15AnchoredAtom2163 chi ∧
      ¬Fin15AnchoredAtom2165 chi ∧
      ¬Fin15AnchoredAtom2169 chi ∧
      ¬Fin15AnchoredAtom2180 chi ∧
      ¬Fin15AnchoredAtom2184 chi ∧
      ¬Fin15AnchoredAtom2195 chi ∧
      ¬Fin15AnchoredAtom2216 chi ∧
      ¬Fin15AnchoredAtom2220 chi ∧
      ¬Fin15AnchoredAtom2231 chi ∧
      ¬Fin15AnchoredAtom2280 chi ∧
      ¬Fin15AnchoredAtom2328 chi ∧
      ¬Fin15AnchoredAtom2330 chi ∧
      ¬Fin15AnchoredAtom2334 chi ∧
      ¬Fin15AnchoredAtom2345 chi ∧
      ¬Fin15AnchoredAtom2349 chi ∧
      ¬Fin15AnchoredAtom2360 chi ∧
      ¬Fin15AnchoredAtom2381 chi ∧
      ¬Fin15AnchoredAtom2385 chi ∧
      ¬Fin15AnchoredAtom2396 chi ∧
      ¬Fin15AnchoredAtom2445 chi ∧
      ¬Fin15AnchoredAtom2501 chi ∧
      ¬Fin15AnchoredAtom2505 chi ∧
      ¬Fin15AnchoredAtom2516 chi ∧
      ¬Fin15AnchoredAtom2565 chi ∧
      ¬Fin15AnchoredAtom2649 chi ∧
      ¬Fin15AnchoredAtom3538 chi ∧
      ¬Fin15AnchoredAtom3540 chi ∧
      ¬Fin15AnchoredAtom3544 chi ∧
      ¬Fin15AnchoredAtom3555 chi ∧
      ¬Fin15AnchoredAtom3559 chi ∧
      ¬Fin15AnchoredAtom3570 chi ∧
      ¬Fin15AnchoredAtom3591 chi ∧
      ¬Fin15AnchoredAtom3595 chi ∧
      ¬Fin15AnchoredAtom3606 chi ∧
      ¬Fin15AnchoredAtom3655 chi ∧
      ¬Fin15AnchoredAtom3711 chi ∧
      ¬Fin15AnchoredAtom3715 chi ∧
      ¬Fin15AnchoredAtom3726 chi ∧
      ¬Fin15AnchoredAtom3775 chi ∧
      ¬Fin15AnchoredAtom3859 chi ∧
      ¬Fin15AnchoredAtom4041 chi ∧
      ¬Fin15AnchoredAtom4045 chi ∧
      ¬Fin15AnchoredAtom4056 chi ∧
      ¬Fin15AnchoredAtom4105 chi ∧
      ¬Fin15AnchoredAtom4189 chi ∧
      ¬Fin15AnchoredAtom4399 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 5, 7, 9, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask08893
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2107 Fin15AnchoredAtom2109 Fin15AnchoredAtom2111
    Fin15AnchoredAtom2115 Fin15AnchoredAtom2118 Fin15AnchoredAtom2120 Fin15AnchoredAtom2124
    Fin15AnchoredAtom2135 Fin15AnchoredAtom2139 Fin15AnchoredAtom2150 Fin15AnchoredAtom2163
    Fin15AnchoredAtom2165 Fin15AnchoredAtom2169 Fin15AnchoredAtom2180 Fin15AnchoredAtom2184
    Fin15AnchoredAtom2195 Fin15AnchoredAtom2216 Fin15AnchoredAtom2220 Fin15AnchoredAtom2231
    Fin15AnchoredAtom2280 Fin15AnchoredAtom2328 Fin15AnchoredAtom2330 Fin15AnchoredAtom2334
    Fin15AnchoredAtom2345 Fin15AnchoredAtom2349 Fin15AnchoredAtom2360 Fin15AnchoredAtom2381
    Fin15AnchoredAtom2385 Fin15AnchoredAtom2396 Fin15AnchoredAtom2445 Fin15AnchoredAtom2501
    Fin15AnchoredAtom2505 Fin15AnchoredAtom2516 Fin15AnchoredAtom2565 Fin15AnchoredAtom2649
    Fin15AnchoredAtom3538 Fin15AnchoredAtom3540 Fin15AnchoredAtom3544 Fin15AnchoredAtom3555
    Fin15AnchoredAtom3559 Fin15AnchoredAtom3570 Fin15AnchoredAtom3591 Fin15AnchoredAtom3595
    Fin15AnchoredAtom3606 Fin15AnchoredAtom3655 Fin15AnchoredAtom3711 Fin15AnchoredAtom3715
    Fin15AnchoredAtom3726 Fin15AnchoredAtom3775 Fin15AnchoredAtom3859 Fin15AnchoredAtom4041
    Fin15AnchoredAtom4045 Fin15AnchoredAtom4056 Fin15AnchoredAtom4105 Fin15AnchoredAtom4189
    Fin15AnchoredAtom4399 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31137 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom2135 chi ∧
      ¬Fin15AnchoredAtom2140 chi ∧
      ¬Fin15AnchoredAtom2151 chi ∧
      ¬Fin15AnchoredAtom2163 chi ∧
      ¬Fin15AnchoredAtom2165 chi ∧
      ¬Fin15AnchoredAtom2170 chi ∧
      ¬Fin15AnchoredAtom2180 chi ∧
      ¬Fin15AnchoredAtom2185 chi ∧
      ¬Fin15AnchoredAtom2196 chi ∧
      ¬Fin15AnchoredAtom2216 chi ∧
      ¬Fin15AnchoredAtom2221 chi ∧
      ¬Fin15AnchoredAtom2232 chi ∧
      ¬Fin15AnchoredAtom2281 chi ∧
      ¬Fin15AnchoredAtom2328 chi ∧
      ¬Fin15AnchoredAtom2330 chi ∧
      ¬Fin15AnchoredAtom2335 chi ∧
      ¬Fin15AnchoredAtom2345 chi ∧
      ¬Fin15AnchoredAtom2350 chi ∧
      ¬Fin15AnchoredAtom2361 chi ∧
      ¬Fin15AnchoredAtom2381 chi ∧
      ¬Fin15AnchoredAtom2386 chi ∧
      ¬Fin15AnchoredAtom2397 chi ∧
      ¬Fin15AnchoredAtom2446 chi ∧
      ¬Fin15AnchoredAtom2501 chi ∧
      ¬Fin15AnchoredAtom2506 chi ∧
      ¬Fin15AnchoredAtom2517 chi ∧
      ¬Fin15AnchoredAtom2566 chi ∧
      ¬Fin15AnchoredAtom2650 chi ∧
      ¬Fin15AnchoredAtom3538 chi ∧
      ¬Fin15AnchoredAtom3540 chi ∧
      ¬Fin15AnchoredAtom3545 chi ∧
      ¬Fin15AnchoredAtom3555 chi ∧
      ¬Fin15AnchoredAtom3560 chi ∧
      ¬Fin15AnchoredAtom3571 chi ∧
      ¬Fin15AnchoredAtom3591 chi ∧
      ¬Fin15AnchoredAtom3596 chi ∧
      ¬Fin15AnchoredAtom3607 chi ∧
      ¬Fin15AnchoredAtom3656 chi ∧
      ¬Fin15AnchoredAtom3711 chi ∧
      ¬Fin15AnchoredAtom3716 chi ∧
      ¬Fin15AnchoredAtom3727 chi ∧
      ¬Fin15AnchoredAtom3776 chi ∧
      ¬Fin15AnchoredAtom3860 chi ∧
      ¬Fin15AnchoredAtom4041 chi ∧
      ¬Fin15AnchoredAtom4046 chi ∧
      ¬Fin15AnchoredAtom4057 chi ∧
      ¬Fin15AnchoredAtom4106 chi ∧
      ¬Fin15AnchoredAtom4190 chi ∧
      ¬Fin15AnchoredAtom4400 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 5, 7, 9, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17085
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2107 Fin15AnchoredAtom2109 Fin15AnchoredAtom2111
    Fin15AnchoredAtom2116 Fin15AnchoredAtom2118 Fin15AnchoredAtom2120 Fin15AnchoredAtom2125
    Fin15AnchoredAtom2135 Fin15AnchoredAtom2140 Fin15AnchoredAtom2151 Fin15AnchoredAtom2163
    Fin15AnchoredAtom2165 Fin15AnchoredAtom2170 Fin15AnchoredAtom2180 Fin15AnchoredAtom2185
    Fin15AnchoredAtom2196 Fin15AnchoredAtom2216 Fin15AnchoredAtom2221 Fin15AnchoredAtom2232
    Fin15AnchoredAtom2281 Fin15AnchoredAtom2328 Fin15AnchoredAtom2330 Fin15AnchoredAtom2335
    Fin15AnchoredAtom2345 Fin15AnchoredAtom2350 Fin15AnchoredAtom2361 Fin15AnchoredAtom2381
    Fin15AnchoredAtom2386 Fin15AnchoredAtom2397 Fin15AnchoredAtom2446 Fin15AnchoredAtom2501
    Fin15AnchoredAtom2506 Fin15AnchoredAtom2517 Fin15AnchoredAtom2566 Fin15AnchoredAtom2650
    Fin15AnchoredAtom3538 Fin15AnchoredAtom3540 Fin15AnchoredAtom3545 Fin15AnchoredAtom3555
    Fin15AnchoredAtom3560 Fin15AnchoredAtom3571 Fin15AnchoredAtom3591 Fin15AnchoredAtom3596
    Fin15AnchoredAtom3607 Fin15AnchoredAtom3656 Fin15AnchoredAtom3711 Fin15AnchoredAtom3716
    Fin15AnchoredAtom3727 Fin15AnchoredAtom3776 Fin15AnchoredAtom3860 Fin15AnchoredAtom4041
    Fin15AnchoredAtom4046 Fin15AnchoredAtom4057 Fin15AnchoredAtom4106 Fin15AnchoredAtom4190
    Fin15AnchoredAtom4400 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31138 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom2136 chi ∧
      ¬Fin15AnchoredAtom2138 chi ∧
      ¬Fin15AnchoredAtom2153 chi ∧
      ¬Fin15AnchoredAtom2163 chi ∧
      ¬Fin15AnchoredAtom2166 chi ∧
      ¬Fin15AnchoredAtom2168 chi ∧
      ¬Fin15AnchoredAtom2181 chi ∧
      ¬Fin15AnchoredAtom2183 chi ∧
      ¬Fin15AnchoredAtom2198 chi ∧
      ¬Fin15AnchoredAtom2217 chi ∧
      ¬Fin15AnchoredAtom2219 chi ∧
      ¬Fin15AnchoredAtom2234 chi ∧
      ¬Fin15AnchoredAtom2283 chi ∧
      ¬Fin15AnchoredAtom2328 chi ∧
      ¬Fin15AnchoredAtom2331 chi ∧
      ¬Fin15AnchoredAtom2333 chi ∧
      ¬Fin15AnchoredAtom2346 chi ∧
      ¬Fin15AnchoredAtom2348 chi ∧
      ¬Fin15AnchoredAtom2363 chi ∧
      ¬Fin15AnchoredAtom2382 chi ∧
      ¬Fin15AnchoredAtom2384 chi ∧
      ¬Fin15AnchoredAtom2399 chi ∧
      ¬Fin15AnchoredAtom2448 chi ∧
      ¬Fin15AnchoredAtom2502 chi ∧
      ¬Fin15AnchoredAtom2504 chi ∧
      ¬Fin15AnchoredAtom2519 chi ∧
      ¬Fin15AnchoredAtom2568 chi ∧
      ¬Fin15AnchoredAtom2652 chi ∧
      ¬Fin15AnchoredAtom3538 chi ∧
      ¬Fin15AnchoredAtom3541 chi ∧
      ¬Fin15AnchoredAtom3543 chi ∧
      ¬Fin15AnchoredAtom3556 chi ∧
      ¬Fin15AnchoredAtom3558 chi ∧
      ¬Fin15AnchoredAtom3573 chi ∧
      ¬Fin15AnchoredAtom3592 chi ∧
      ¬Fin15AnchoredAtom3594 chi ∧
      ¬Fin15AnchoredAtom3609 chi ∧
      ¬Fin15AnchoredAtom3658 chi ∧
      ¬Fin15AnchoredAtom3712 chi ∧
      ¬Fin15AnchoredAtom3714 chi ∧
      ¬Fin15AnchoredAtom3729 chi ∧
      ¬Fin15AnchoredAtom3778 chi ∧
      ¬Fin15AnchoredAtom3862 chi ∧
      ¬Fin15AnchoredAtom4042 chi ∧
      ¬Fin15AnchoredAtom4044 chi ∧
      ¬Fin15AnchoredAtom4059 chi ∧
      ¬Fin15AnchoredAtom4108 chi ∧
      ¬Fin15AnchoredAtom4192 chi ∧
      ¬Fin15AnchoredAtom4402 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 5, 7, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05309
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2107 Fin15AnchoredAtom2109 Fin15AnchoredAtom2112
    Fin15AnchoredAtom2114 Fin15AnchoredAtom2118 Fin15AnchoredAtom2121 Fin15AnchoredAtom2123
    Fin15AnchoredAtom2136 Fin15AnchoredAtom2138 Fin15AnchoredAtom2153 Fin15AnchoredAtom2163
    Fin15AnchoredAtom2166 Fin15AnchoredAtom2168 Fin15AnchoredAtom2181 Fin15AnchoredAtom2183
    Fin15AnchoredAtom2198 Fin15AnchoredAtom2217 Fin15AnchoredAtom2219 Fin15AnchoredAtom2234
    Fin15AnchoredAtom2283 Fin15AnchoredAtom2328 Fin15AnchoredAtom2331 Fin15AnchoredAtom2333
    Fin15AnchoredAtom2346 Fin15AnchoredAtom2348 Fin15AnchoredAtom2363 Fin15AnchoredAtom2382
    Fin15AnchoredAtom2384 Fin15AnchoredAtom2399 Fin15AnchoredAtom2448 Fin15AnchoredAtom2502
    Fin15AnchoredAtom2504 Fin15AnchoredAtom2519 Fin15AnchoredAtom2568 Fin15AnchoredAtom2652
    Fin15AnchoredAtom3538 Fin15AnchoredAtom3541 Fin15AnchoredAtom3543 Fin15AnchoredAtom3556
    Fin15AnchoredAtom3558 Fin15AnchoredAtom3573 Fin15AnchoredAtom3592 Fin15AnchoredAtom3594
    Fin15AnchoredAtom3609 Fin15AnchoredAtom3658 Fin15AnchoredAtom3712 Fin15AnchoredAtom3714
    Fin15AnchoredAtom3729 Fin15AnchoredAtom3778 Fin15AnchoredAtom3862 Fin15AnchoredAtom4042
    Fin15AnchoredAtom4044 Fin15AnchoredAtom4059 Fin15AnchoredAtom4108 Fin15AnchoredAtom4192
    Fin15AnchoredAtom4402 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31139 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom2136 chi ∧
      ¬Fin15AnchoredAtom2139 chi ∧
      ¬Fin15AnchoredAtom2154 chi ∧
      ¬Fin15AnchoredAtom2163 chi ∧
      ¬Fin15AnchoredAtom2166 chi ∧
      ¬Fin15AnchoredAtom2169 chi ∧
      ¬Fin15AnchoredAtom2181 chi ∧
      ¬Fin15AnchoredAtom2184 chi ∧
      ¬Fin15AnchoredAtom2199 chi ∧
      ¬Fin15AnchoredAtom2217 chi ∧
      ¬Fin15AnchoredAtom2220 chi ∧
      ¬Fin15AnchoredAtom2235 chi ∧
      ¬Fin15AnchoredAtom2284 chi ∧
      ¬Fin15AnchoredAtom2328 chi ∧
      ¬Fin15AnchoredAtom2331 chi ∧
      ¬Fin15AnchoredAtom2334 chi ∧
      ¬Fin15AnchoredAtom2346 chi ∧
      ¬Fin15AnchoredAtom2349 chi ∧
      ¬Fin15AnchoredAtom2364 chi ∧
      ¬Fin15AnchoredAtom2382 chi ∧
      ¬Fin15AnchoredAtom2385 chi ∧
      ¬Fin15AnchoredAtom2400 chi ∧
      ¬Fin15AnchoredAtom2449 chi ∧
      ¬Fin15AnchoredAtom2502 chi ∧
      ¬Fin15AnchoredAtom2505 chi ∧
      ¬Fin15AnchoredAtom2520 chi ∧
      ¬Fin15AnchoredAtom2569 chi ∧
      ¬Fin15AnchoredAtom2653 chi ∧
      ¬Fin15AnchoredAtom3538 chi ∧
      ¬Fin15AnchoredAtom3541 chi ∧
      ¬Fin15AnchoredAtom3544 chi ∧
      ¬Fin15AnchoredAtom3556 chi ∧
      ¬Fin15AnchoredAtom3559 chi ∧
      ¬Fin15AnchoredAtom3574 chi ∧
      ¬Fin15AnchoredAtom3592 chi ∧
      ¬Fin15AnchoredAtom3595 chi ∧
      ¬Fin15AnchoredAtom3610 chi ∧
      ¬Fin15AnchoredAtom3659 chi ∧
      ¬Fin15AnchoredAtom3712 chi ∧
      ¬Fin15AnchoredAtom3715 chi ∧
      ¬Fin15AnchoredAtom3730 chi ∧
      ¬Fin15AnchoredAtom3779 chi ∧
      ¬Fin15AnchoredAtom3863 chi ∧
      ¬Fin15AnchoredAtom4042 chi ∧
      ¬Fin15AnchoredAtom4045 chi ∧
      ¬Fin15AnchoredAtom4060 chi ∧
      ¬Fin15AnchoredAtom4109 chi ∧
      ¬Fin15AnchoredAtom4193 chi ∧
      ¬Fin15AnchoredAtom4403 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 5, 7, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09405
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2107 Fin15AnchoredAtom2109 Fin15AnchoredAtom2112
    Fin15AnchoredAtom2115 Fin15AnchoredAtom2118 Fin15AnchoredAtom2121 Fin15AnchoredAtom2124
    Fin15AnchoredAtom2136 Fin15AnchoredAtom2139 Fin15AnchoredAtom2154 Fin15AnchoredAtom2163
    Fin15AnchoredAtom2166 Fin15AnchoredAtom2169 Fin15AnchoredAtom2181 Fin15AnchoredAtom2184
    Fin15AnchoredAtom2199 Fin15AnchoredAtom2217 Fin15AnchoredAtom2220 Fin15AnchoredAtom2235
    Fin15AnchoredAtom2284 Fin15AnchoredAtom2328 Fin15AnchoredAtom2331 Fin15AnchoredAtom2334
    Fin15AnchoredAtom2346 Fin15AnchoredAtom2349 Fin15AnchoredAtom2364 Fin15AnchoredAtom2382
    Fin15AnchoredAtom2385 Fin15AnchoredAtom2400 Fin15AnchoredAtom2449 Fin15AnchoredAtom2502
    Fin15AnchoredAtom2505 Fin15AnchoredAtom2520 Fin15AnchoredAtom2569 Fin15AnchoredAtom2653
    Fin15AnchoredAtom3538 Fin15AnchoredAtom3541 Fin15AnchoredAtom3544 Fin15AnchoredAtom3556
    Fin15AnchoredAtom3559 Fin15AnchoredAtom3574 Fin15AnchoredAtom3592 Fin15AnchoredAtom3595
    Fin15AnchoredAtom3610 Fin15AnchoredAtom3659 Fin15AnchoredAtom3712 Fin15AnchoredAtom3715
    Fin15AnchoredAtom3730 Fin15AnchoredAtom3779 Fin15AnchoredAtom3863 Fin15AnchoredAtom4042
    Fin15AnchoredAtom4045 Fin15AnchoredAtom4060 Fin15AnchoredAtom4109 Fin15AnchoredAtom4193
    Fin15AnchoredAtom4403 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31140 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom2136 chi ∧
      ¬Fin15AnchoredAtom2140 chi ∧
      ¬Fin15AnchoredAtom2155 chi ∧
      ¬Fin15AnchoredAtom2163 chi ∧
      ¬Fin15AnchoredAtom2166 chi ∧
      ¬Fin15AnchoredAtom2170 chi ∧
      ¬Fin15AnchoredAtom2181 chi ∧
      ¬Fin15AnchoredAtom2185 chi ∧
      ¬Fin15AnchoredAtom2200 chi ∧
      ¬Fin15AnchoredAtom2217 chi ∧
      ¬Fin15AnchoredAtom2221 chi ∧
      ¬Fin15AnchoredAtom2236 chi ∧
      ¬Fin15AnchoredAtom2285 chi ∧
      ¬Fin15AnchoredAtom2328 chi ∧
      ¬Fin15AnchoredAtom2331 chi ∧
      ¬Fin15AnchoredAtom2335 chi ∧
      ¬Fin15AnchoredAtom2346 chi ∧
      ¬Fin15AnchoredAtom2350 chi ∧
      ¬Fin15AnchoredAtom2365 chi ∧
      ¬Fin15AnchoredAtom2382 chi ∧
      ¬Fin15AnchoredAtom2386 chi ∧
      ¬Fin15AnchoredAtom2401 chi ∧
      ¬Fin15AnchoredAtom2450 chi ∧
      ¬Fin15AnchoredAtom2502 chi ∧
      ¬Fin15AnchoredAtom2506 chi ∧
      ¬Fin15AnchoredAtom2521 chi ∧
      ¬Fin15AnchoredAtom2570 chi ∧
      ¬Fin15AnchoredAtom2654 chi ∧
      ¬Fin15AnchoredAtom3538 chi ∧
      ¬Fin15AnchoredAtom3541 chi ∧
      ¬Fin15AnchoredAtom3545 chi ∧
      ¬Fin15AnchoredAtom3556 chi ∧
      ¬Fin15AnchoredAtom3560 chi ∧
      ¬Fin15AnchoredAtom3575 chi ∧
      ¬Fin15AnchoredAtom3592 chi ∧
      ¬Fin15AnchoredAtom3596 chi ∧
      ¬Fin15AnchoredAtom3611 chi ∧
      ¬Fin15AnchoredAtom3660 chi ∧
      ¬Fin15AnchoredAtom3712 chi ∧
      ¬Fin15AnchoredAtom3716 chi ∧
      ¬Fin15AnchoredAtom3731 chi ∧
      ¬Fin15AnchoredAtom3780 chi ∧
      ¬Fin15AnchoredAtom3864 chi ∧
      ¬Fin15AnchoredAtom4042 chi ∧
      ¬Fin15AnchoredAtom4046 chi ∧
      ¬Fin15AnchoredAtom4061 chi ∧
      ¬Fin15AnchoredAtom4110 chi ∧
      ¬Fin15AnchoredAtom4194 chi ∧
      ¬Fin15AnchoredAtom4404 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 5, 7, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17597
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2107 Fin15AnchoredAtom2109 Fin15AnchoredAtom2112
    Fin15AnchoredAtom2116 Fin15AnchoredAtom2118 Fin15AnchoredAtom2121 Fin15AnchoredAtom2125
    Fin15AnchoredAtom2136 Fin15AnchoredAtom2140 Fin15AnchoredAtom2155 Fin15AnchoredAtom2163
    Fin15AnchoredAtom2166 Fin15AnchoredAtom2170 Fin15AnchoredAtom2181 Fin15AnchoredAtom2185
    Fin15AnchoredAtom2200 Fin15AnchoredAtom2217 Fin15AnchoredAtom2221 Fin15AnchoredAtom2236
    Fin15AnchoredAtom2285 Fin15AnchoredAtom2328 Fin15AnchoredAtom2331 Fin15AnchoredAtom2335
    Fin15AnchoredAtom2346 Fin15AnchoredAtom2350 Fin15AnchoredAtom2365 Fin15AnchoredAtom2382
    Fin15AnchoredAtom2386 Fin15AnchoredAtom2401 Fin15AnchoredAtom2450 Fin15AnchoredAtom2502
    Fin15AnchoredAtom2506 Fin15AnchoredAtom2521 Fin15AnchoredAtom2570 Fin15AnchoredAtom2654
    Fin15AnchoredAtom3538 Fin15AnchoredAtom3541 Fin15AnchoredAtom3545 Fin15AnchoredAtom3556
    Fin15AnchoredAtom3560 Fin15AnchoredAtom3575 Fin15AnchoredAtom3592 Fin15AnchoredAtom3596
    Fin15AnchoredAtom3611 Fin15AnchoredAtom3660 Fin15AnchoredAtom3712 Fin15AnchoredAtom3716
    Fin15AnchoredAtom3731 Fin15AnchoredAtom3780 Fin15AnchoredAtom3864 Fin15AnchoredAtom4042
    Fin15AnchoredAtom4046 Fin15AnchoredAtom4061 Fin15AnchoredAtom4110 Fin15AnchoredAtom4194
    Fin15AnchoredAtom4404 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31141 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2113 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom2122 chi ∧
      ¬Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom2137 chi ∧
      ¬Fin15AnchoredAtom2138 chi ∧
      ¬Fin15AnchoredAtom2156 chi ∧
      ¬Fin15AnchoredAtom2163 chi ∧
      ¬Fin15AnchoredAtom2167 chi ∧
      ¬Fin15AnchoredAtom2168 chi ∧
      ¬Fin15AnchoredAtom2182 chi ∧
      ¬Fin15AnchoredAtom2183 chi ∧
      ¬Fin15AnchoredAtom2201 chi ∧
      ¬Fin15AnchoredAtom2218 chi ∧
      ¬Fin15AnchoredAtom2219 chi ∧
      ¬Fin15AnchoredAtom2237 chi ∧
      ¬Fin15AnchoredAtom2286 chi ∧
      ¬Fin15AnchoredAtom2328 chi ∧
      ¬Fin15AnchoredAtom2332 chi ∧
      ¬Fin15AnchoredAtom2333 chi ∧
      ¬Fin15AnchoredAtom2347 chi ∧
      ¬Fin15AnchoredAtom2348 chi ∧
      ¬Fin15AnchoredAtom2366 chi ∧
      ¬Fin15AnchoredAtom2383 chi ∧
      ¬Fin15AnchoredAtom2384 chi ∧
      ¬Fin15AnchoredAtom2402 chi ∧
      ¬Fin15AnchoredAtom2451 chi ∧
      ¬Fin15AnchoredAtom2503 chi ∧
      ¬Fin15AnchoredAtom2504 chi ∧
      ¬Fin15AnchoredAtom2522 chi ∧
      ¬Fin15AnchoredAtom2571 chi ∧
      ¬Fin15AnchoredAtom2655 chi ∧
      ¬Fin15AnchoredAtom3538 chi ∧
      ¬Fin15AnchoredAtom3542 chi ∧
      ¬Fin15AnchoredAtom3543 chi ∧
      ¬Fin15AnchoredAtom3557 chi ∧
      ¬Fin15AnchoredAtom3558 chi ∧
      ¬Fin15AnchoredAtom3576 chi ∧
      ¬Fin15AnchoredAtom3593 chi ∧
      ¬Fin15AnchoredAtom3594 chi ∧
      ¬Fin15AnchoredAtom3612 chi ∧
      ¬Fin15AnchoredAtom3661 chi ∧
      ¬Fin15AnchoredAtom3713 chi ∧
      ¬Fin15AnchoredAtom3714 chi ∧
      ¬Fin15AnchoredAtom3732 chi ∧
      ¬Fin15AnchoredAtom3781 chi ∧
      ¬Fin15AnchoredAtom3865 chi ∧
      ¬Fin15AnchoredAtom4043 chi ∧
      ¬Fin15AnchoredAtom4044 chi ∧
      ¬Fin15AnchoredAtom4062 chi ∧
      ¬Fin15AnchoredAtom4111 chi ∧
      ¬Fin15AnchoredAtom4195 chi ∧
      ¬Fin15AnchoredAtom4405 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 5, 7, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask06333
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2107 Fin15AnchoredAtom2109 Fin15AnchoredAtom2113
    Fin15AnchoredAtom2114 Fin15AnchoredAtom2118 Fin15AnchoredAtom2122 Fin15AnchoredAtom2123
    Fin15AnchoredAtom2137 Fin15AnchoredAtom2138 Fin15AnchoredAtom2156 Fin15AnchoredAtom2163
    Fin15AnchoredAtom2167 Fin15AnchoredAtom2168 Fin15AnchoredAtom2182 Fin15AnchoredAtom2183
    Fin15AnchoredAtom2201 Fin15AnchoredAtom2218 Fin15AnchoredAtom2219 Fin15AnchoredAtom2237
    Fin15AnchoredAtom2286 Fin15AnchoredAtom2328 Fin15AnchoredAtom2332 Fin15AnchoredAtom2333
    Fin15AnchoredAtom2347 Fin15AnchoredAtom2348 Fin15AnchoredAtom2366 Fin15AnchoredAtom2383
    Fin15AnchoredAtom2384 Fin15AnchoredAtom2402 Fin15AnchoredAtom2451 Fin15AnchoredAtom2503
    Fin15AnchoredAtom2504 Fin15AnchoredAtom2522 Fin15AnchoredAtom2571 Fin15AnchoredAtom2655
    Fin15AnchoredAtom3538 Fin15AnchoredAtom3542 Fin15AnchoredAtom3543 Fin15AnchoredAtom3557
    Fin15AnchoredAtom3558 Fin15AnchoredAtom3576 Fin15AnchoredAtom3593 Fin15AnchoredAtom3594
    Fin15AnchoredAtom3612 Fin15AnchoredAtom3661 Fin15AnchoredAtom3713 Fin15AnchoredAtom3714
    Fin15AnchoredAtom3732 Fin15AnchoredAtom3781 Fin15AnchoredAtom3865 Fin15AnchoredAtom4043
    Fin15AnchoredAtom4044 Fin15AnchoredAtom4062 Fin15AnchoredAtom4111 Fin15AnchoredAtom4195
    Fin15AnchoredAtom4405 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31142 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom2138 chi ∧
      ¬Fin15AnchoredAtom2139 chi ∧
      ¬Fin15AnchoredAtom2159 chi ∧
      ¬Fin15AnchoredAtom2163 chi ∧
      ¬Fin15AnchoredAtom2168 chi ∧
      ¬Fin15AnchoredAtom2169 chi ∧
      ¬Fin15AnchoredAtom2183 chi ∧
      ¬Fin15AnchoredAtom2184 chi ∧
      ¬Fin15AnchoredAtom2204 chi ∧
      ¬Fin15AnchoredAtom2219 chi ∧
      ¬Fin15AnchoredAtom2220 chi ∧
      ¬Fin15AnchoredAtom2240 chi ∧
      ¬Fin15AnchoredAtom2289 chi ∧
      ¬Fin15AnchoredAtom2328 chi ∧
      ¬Fin15AnchoredAtom2333 chi ∧
      ¬Fin15AnchoredAtom2334 chi ∧
      ¬Fin15AnchoredAtom2348 chi ∧
      ¬Fin15AnchoredAtom2349 chi ∧
      ¬Fin15AnchoredAtom2369 chi ∧
      ¬Fin15AnchoredAtom2384 chi ∧
      ¬Fin15AnchoredAtom2385 chi ∧
      ¬Fin15AnchoredAtom2405 chi ∧
      ¬Fin15AnchoredAtom2454 chi ∧
      ¬Fin15AnchoredAtom2504 chi ∧
      ¬Fin15AnchoredAtom2505 chi ∧
      ¬Fin15AnchoredAtom2525 chi ∧
      ¬Fin15AnchoredAtom2574 chi ∧
      ¬Fin15AnchoredAtom2658 chi ∧
      ¬Fin15AnchoredAtom3538 chi ∧
      ¬Fin15AnchoredAtom3543 chi ∧
      ¬Fin15AnchoredAtom3544 chi ∧
      ¬Fin15AnchoredAtom3558 chi ∧
      ¬Fin15AnchoredAtom3559 chi ∧
      ¬Fin15AnchoredAtom3579 chi ∧
      ¬Fin15AnchoredAtom3594 chi ∧
      ¬Fin15AnchoredAtom3595 chi ∧
      ¬Fin15AnchoredAtom3615 chi ∧
      ¬Fin15AnchoredAtom3664 chi ∧
      ¬Fin15AnchoredAtom3714 chi ∧
      ¬Fin15AnchoredAtom3715 chi ∧
      ¬Fin15AnchoredAtom3735 chi ∧
      ¬Fin15AnchoredAtom3784 chi ∧
      ¬Fin15AnchoredAtom3868 chi ∧
      ¬Fin15AnchoredAtom4044 chi ∧
      ¬Fin15AnchoredAtom4045 chi ∧
      ¬Fin15AnchoredAtom4065 chi ∧
      ¬Fin15AnchoredAtom4114 chi ∧
      ¬Fin15AnchoredAtom4198 chi ∧
      ¬Fin15AnchoredAtom4408 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 5, 7, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask12477
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2107 Fin15AnchoredAtom2109 Fin15AnchoredAtom2114
    Fin15AnchoredAtom2115 Fin15AnchoredAtom2118 Fin15AnchoredAtom2123 Fin15AnchoredAtom2124
    Fin15AnchoredAtom2138 Fin15AnchoredAtom2139 Fin15AnchoredAtom2159 Fin15AnchoredAtom2163
    Fin15AnchoredAtom2168 Fin15AnchoredAtom2169 Fin15AnchoredAtom2183 Fin15AnchoredAtom2184
    Fin15AnchoredAtom2204 Fin15AnchoredAtom2219 Fin15AnchoredAtom2220 Fin15AnchoredAtom2240
    Fin15AnchoredAtom2289 Fin15AnchoredAtom2328 Fin15AnchoredAtom2333 Fin15AnchoredAtom2334
    Fin15AnchoredAtom2348 Fin15AnchoredAtom2349 Fin15AnchoredAtom2369 Fin15AnchoredAtom2384
    Fin15AnchoredAtom2385 Fin15AnchoredAtom2405 Fin15AnchoredAtom2454 Fin15AnchoredAtom2504
    Fin15AnchoredAtom2505 Fin15AnchoredAtom2525 Fin15AnchoredAtom2574 Fin15AnchoredAtom2658
    Fin15AnchoredAtom3538 Fin15AnchoredAtom3543 Fin15AnchoredAtom3544 Fin15AnchoredAtom3558
    Fin15AnchoredAtom3559 Fin15AnchoredAtom3579 Fin15AnchoredAtom3594 Fin15AnchoredAtom3595
    Fin15AnchoredAtom3615 Fin15AnchoredAtom3664 Fin15AnchoredAtom3714 Fin15AnchoredAtom3715
    Fin15AnchoredAtom3735 Fin15AnchoredAtom3784 Fin15AnchoredAtom3868 Fin15AnchoredAtom4044
    Fin15AnchoredAtom4045 Fin15AnchoredAtom4065 Fin15AnchoredAtom4114 Fin15AnchoredAtom4198
    Fin15AnchoredAtom4408 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31143 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom2138 chi ∧
      ¬Fin15AnchoredAtom2140 chi ∧
      ¬Fin15AnchoredAtom2160 chi ∧
      ¬Fin15AnchoredAtom2163 chi ∧
      ¬Fin15AnchoredAtom2168 chi ∧
      ¬Fin15AnchoredAtom2170 chi ∧
      ¬Fin15AnchoredAtom2183 chi ∧
      ¬Fin15AnchoredAtom2185 chi ∧
      ¬Fin15AnchoredAtom2205 chi ∧
      ¬Fin15AnchoredAtom2219 chi ∧
      ¬Fin15AnchoredAtom2221 chi ∧
      ¬Fin15AnchoredAtom2241 chi ∧
      ¬Fin15AnchoredAtom2290 chi ∧
      ¬Fin15AnchoredAtom2328 chi ∧
      ¬Fin15AnchoredAtom2333 chi ∧
      ¬Fin15AnchoredAtom2335 chi ∧
      ¬Fin15AnchoredAtom2348 chi ∧
      ¬Fin15AnchoredAtom2350 chi ∧
      ¬Fin15AnchoredAtom2370 chi ∧
      ¬Fin15AnchoredAtom2384 chi ∧
      ¬Fin15AnchoredAtom2386 chi ∧
      ¬Fin15AnchoredAtom2406 chi ∧
      ¬Fin15AnchoredAtom2455 chi ∧
      ¬Fin15AnchoredAtom2504 chi ∧
      ¬Fin15AnchoredAtom2506 chi ∧
      ¬Fin15AnchoredAtom2526 chi ∧
      ¬Fin15AnchoredAtom2575 chi ∧
      ¬Fin15AnchoredAtom2659 chi ∧
      ¬Fin15AnchoredAtom3538 chi ∧
      ¬Fin15AnchoredAtom3543 chi ∧
      ¬Fin15AnchoredAtom3545 chi ∧
      ¬Fin15AnchoredAtom3558 chi ∧
      ¬Fin15AnchoredAtom3560 chi ∧
      ¬Fin15AnchoredAtom3580 chi ∧
      ¬Fin15AnchoredAtom3594 chi ∧
      ¬Fin15AnchoredAtom3596 chi ∧
      ¬Fin15AnchoredAtom3616 chi ∧
      ¬Fin15AnchoredAtom3665 chi ∧
      ¬Fin15AnchoredAtom3714 chi ∧
      ¬Fin15AnchoredAtom3716 chi ∧
      ¬Fin15AnchoredAtom3736 chi ∧
      ¬Fin15AnchoredAtom3785 chi ∧
      ¬Fin15AnchoredAtom3869 chi ∧
      ¬Fin15AnchoredAtom4044 chi ∧
      ¬Fin15AnchoredAtom4046 chi ∧
      ¬Fin15AnchoredAtom4066 chi ∧
      ¬Fin15AnchoredAtom4115 chi ∧
      ¬Fin15AnchoredAtom4199 chi ∧
      ¬Fin15AnchoredAtom4409 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 5, 7, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask20669
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2107 Fin15AnchoredAtom2109 Fin15AnchoredAtom2114
    Fin15AnchoredAtom2116 Fin15AnchoredAtom2118 Fin15AnchoredAtom2123 Fin15AnchoredAtom2125
    Fin15AnchoredAtom2138 Fin15AnchoredAtom2140 Fin15AnchoredAtom2160 Fin15AnchoredAtom2163
    Fin15AnchoredAtom2168 Fin15AnchoredAtom2170 Fin15AnchoredAtom2183 Fin15AnchoredAtom2185
    Fin15AnchoredAtom2205 Fin15AnchoredAtom2219 Fin15AnchoredAtom2221 Fin15AnchoredAtom2241
    Fin15AnchoredAtom2290 Fin15AnchoredAtom2328 Fin15AnchoredAtom2333 Fin15AnchoredAtom2335
    Fin15AnchoredAtom2348 Fin15AnchoredAtom2350 Fin15AnchoredAtom2370 Fin15AnchoredAtom2384
    Fin15AnchoredAtom2386 Fin15AnchoredAtom2406 Fin15AnchoredAtom2455 Fin15AnchoredAtom2504
    Fin15AnchoredAtom2506 Fin15AnchoredAtom2526 Fin15AnchoredAtom2575 Fin15AnchoredAtom2659
    Fin15AnchoredAtom3538 Fin15AnchoredAtom3543 Fin15AnchoredAtom3545 Fin15AnchoredAtom3558
    Fin15AnchoredAtom3560 Fin15AnchoredAtom3580 Fin15AnchoredAtom3594 Fin15AnchoredAtom3596
    Fin15AnchoredAtom3616 Fin15AnchoredAtom3665 Fin15AnchoredAtom3714 Fin15AnchoredAtom3716
    Fin15AnchoredAtom3736 Fin15AnchoredAtom3785 Fin15AnchoredAtom3869 Fin15AnchoredAtom4044
    Fin15AnchoredAtom4046 Fin15AnchoredAtom4066 Fin15AnchoredAtom4115 Fin15AnchoredAtom4199
    Fin15AnchoredAtom4409 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31144 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom2139 chi ∧
      ¬Fin15AnchoredAtom2140 chi ∧
      ¬Fin15AnchoredAtom2161 chi ∧
      ¬Fin15AnchoredAtom2163 chi ∧
      ¬Fin15AnchoredAtom2169 chi ∧
      ¬Fin15AnchoredAtom2170 chi ∧
      ¬Fin15AnchoredAtom2184 chi ∧
      ¬Fin15AnchoredAtom2185 chi ∧
      ¬Fin15AnchoredAtom2206 chi ∧
      ¬Fin15AnchoredAtom2220 chi ∧
      ¬Fin15AnchoredAtom2221 chi ∧
      ¬Fin15AnchoredAtom2242 chi ∧
      ¬Fin15AnchoredAtom2291 chi ∧
      ¬Fin15AnchoredAtom2328 chi ∧
      ¬Fin15AnchoredAtom2334 chi ∧
      ¬Fin15AnchoredAtom2335 chi ∧
      ¬Fin15AnchoredAtom2349 chi ∧
      ¬Fin15AnchoredAtom2350 chi ∧
      ¬Fin15AnchoredAtom2371 chi ∧
      ¬Fin15AnchoredAtom2385 chi ∧
      ¬Fin15AnchoredAtom2386 chi ∧
      ¬Fin15AnchoredAtom2407 chi ∧
      ¬Fin15AnchoredAtom2456 chi ∧
      ¬Fin15AnchoredAtom2505 chi ∧
      ¬Fin15AnchoredAtom2506 chi ∧
      ¬Fin15AnchoredAtom2527 chi ∧
      ¬Fin15AnchoredAtom2576 chi ∧
      ¬Fin15AnchoredAtom2660 chi ∧
      ¬Fin15AnchoredAtom3538 chi ∧
      ¬Fin15AnchoredAtom3544 chi ∧
      ¬Fin15AnchoredAtom3545 chi ∧
      ¬Fin15AnchoredAtom3559 chi ∧
      ¬Fin15AnchoredAtom3560 chi ∧
      ¬Fin15AnchoredAtom3581 chi ∧
      ¬Fin15AnchoredAtom3595 chi ∧
      ¬Fin15AnchoredAtom3596 chi ∧
      ¬Fin15AnchoredAtom3617 chi ∧
      ¬Fin15AnchoredAtom3666 chi ∧
      ¬Fin15AnchoredAtom3715 chi ∧
      ¬Fin15AnchoredAtom3716 chi ∧
      ¬Fin15AnchoredAtom3737 chi ∧
      ¬Fin15AnchoredAtom3786 chi ∧
      ¬Fin15AnchoredAtom3870 chi ∧
      ¬Fin15AnchoredAtom4045 chi ∧
      ¬Fin15AnchoredAtom4046 chi ∧
      ¬Fin15AnchoredAtom4067 chi ∧
      ¬Fin15AnchoredAtom4116 chi ∧
      ¬Fin15AnchoredAtom4200 chi ∧
      ¬Fin15AnchoredAtom4410 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 5, 7, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask24765
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2107 Fin15AnchoredAtom2109 Fin15AnchoredAtom2115
    Fin15AnchoredAtom2116 Fin15AnchoredAtom2118 Fin15AnchoredAtom2124 Fin15AnchoredAtom2125
    Fin15AnchoredAtom2139 Fin15AnchoredAtom2140 Fin15AnchoredAtom2161 Fin15AnchoredAtom2163
    Fin15AnchoredAtom2169 Fin15AnchoredAtom2170 Fin15AnchoredAtom2184 Fin15AnchoredAtom2185
    Fin15AnchoredAtom2206 Fin15AnchoredAtom2220 Fin15AnchoredAtom2221 Fin15AnchoredAtom2242
    Fin15AnchoredAtom2291 Fin15AnchoredAtom2328 Fin15AnchoredAtom2334 Fin15AnchoredAtom2335
    Fin15AnchoredAtom2349 Fin15AnchoredAtom2350 Fin15AnchoredAtom2371 Fin15AnchoredAtom2385
    Fin15AnchoredAtom2386 Fin15AnchoredAtom2407 Fin15AnchoredAtom2456 Fin15AnchoredAtom2505
    Fin15AnchoredAtom2506 Fin15AnchoredAtom2527 Fin15AnchoredAtom2576 Fin15AnchoredAtom2660
    Fin15AnchoredAtom3538 Fin15AnchoredAtom3544 Fin15AnchoredAtom3545 Fin15AnchoredAtom3559
    Fin15AnchoredAtom3560 Fin15AnchoredAtom3581 Fin15AnchoredAtom3595 Fin15AnchoredAtom3596
    Fin15AnchoredAtom3617 Fin15AnchoredAtom3666 Fin15AnchoredAtom3715 Fin15AnchoredAtom3716
    Fin15AnchoredAtom3737 Fin15AnchoredAtom3786 Fin15AnchoredAtom3870 Fin15AnchoredAtom4045
    Fin15AnchoredAtom4046 Fin15AnchoredAtom4067 Fin15AnchoredAtom4116 Fin15AnchoredAtom4200
    Fin15AnchoredAtom4410 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31145 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom2147 chi ∧
      ¬Fin15AnchoredAtom2149 chi ∧
      ¬Fin15AnchoredAtom2153 chi ∧
      ¬Fin15AnchoredAtom2165 chi ∧
      ¬Fin15AnchoredAtom2166 chi ∧
      ¬Fin15AnchoredAtom2168 chi ∧
      ¬Fin15AnchoredAtom2192 chi ∧
      ¬Fin15AnchoredAtom2194 chi ∧
      ¬Fin15AnchoredAtom2198 chi ∧
      ¬Fin15AnchoredAtom2228 chi ∧
      ¬Fin15AnchoredAtom2230 chi ∧
      ¬Fin15AnchoredAtom2234 chi ∧
      ¬Fin15AnchoredAtom2308 chi ∧
      ¬Fin15AnchoredAtom2330 chi ∧
      ¬Fin15AnchoredAtom2331 chi ∧
      ¬Fin15AnchoredAtom2333 chi ∧
      ¬Fin15AnchoredAtom2357 chi ∧
      ¬Fin15AnchoredAtom2359 chi ∧
      ¬Fin15AnchoredAtom2363 chi ∧
      ¬Fin15AnchoredAtom2393 chi ∧
      ¬Fin15AnchoredAtom2395 chi ∧
      ¬Fin15AnchoredAtom2399 chi ∧
      ¬Fin15AnchoredAtom2473 chi ∧
      ¬Fin15AnchoredAtom2513 chi ∧
      ¬Fin15AnchoredAtom2515 chi ∧
      ¬Fin15AnchoredAtom2519 chi ∧
      ¬Fin15AnchoredAtom2593 chi ∧
      ¬Fin15AnchoredAtom2677 chi ∧
      ¬Fin15AnchoredAtom3540 chi ∧
      ¬Fin15AnchoredAtom3541 chi ∧
      ¬Fin15AnchoredAtom3543 chi ∧
      ¬Fin15AnchoredAtom3567 chi ∧
      ¬Fin15AnchoredAtom3569 chi ∧
      ¬Fin15AnchoredAtom3573 chi ∧
      ¬Fin15AnchoredAtom3603 chi ∧
      ¬Fin15AnchoredAtom3605 chi ∧
      ¬Fin15AnchoredAtom3609 chi ∧
      ¬Fin15AnchoredAtom3683 chi ∧
      ¬Fin15AnchoredAtom3723 chi ∧
      ¬Fin15AnchoredAtom3725 chi ∧
      ¬Fin15AnchoredAtom3729 chi ∧
      ¬Fin15AnchoredAtom3803 chi ∧
      ¬Fin15AnchoredAtom3887 chi ∧
      ¬Fin15AnchoredAtom4053 chi ∧
      ¬Fin15AnchoredAtom4055 chi ∧
      ¬Fin15AnchoredAtom4059 chi ∧
      ¬Fin15AnchoredAtom4133 chi ∧
      ¬Fin15AnchoredAtom4217 chi ∧
      ¬Fin15AnchoredAtom4427 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 5, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05693
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2107 Fin15AnchoredAtom2111 Fin15AnchoredAtom2112
    Fin15AnchoredAtom2114 Fin15AnchoredAtom2120 Fin15AnchoredAtom2121 Fin15AnchoredAtom2123
    Fin15AnchoredAtom2147 Fin15AnchoredAtom2149 Fin15AnchoredAtom2153 Fin15AnchoredAtom2165
    Fin15AnchoredAtom2166 Fin15AnchoredAtom2168 Fin15AnchoredAtom2192 Fin15AnchoredAtom2194
    Fin15AnchoredAtom2198 Fin15AnchoredAtom2228 Fin15AnchoredAtom2230 Fin15AnchoredAtom2234
    Fin15AnchoredAtom2308 Fin15AnchoredAtom2330 Fin15AnchoredAtom2331 Fin15AnchoredAtom2333
    Fin15AnchoredAtom2357 Fin15AnchoredAtom2359 Fin15AnchoredAtom2363 Fin15AnchoredAtom2393
    Fin15AnchoredAtom2395 Fin15AnchoredAtom2399 Fin15AnchoredAtom2473 Fin15AnchoredAtom2513
    Fin15AnchoredAtom2515 Fin15AnchoredAtom2519 Fin15AnchoredAtom2593 Fin15AnchoredAtom2677
    Fin15AnchoredAtom3540 Fin15AnchoredAtom3541 Fin15AnchoredAtom3543 Fin15AnchoredAtom3567
    Fin15AnchoredAtom3569 Fin15AnchoredAtom3573 Fin15AnchoredAtom3603 Fin15AnchoredAtom3605
    Fin15AnchoredAtom3609 Fin15AnchoredAtom3683 Fin15AnchoredAtom3723 Fin15AnchoredAtom3725
    Fin15AnchoredAtom3729 Fin15AnchoredAtom3803 Fin15AnchoredAtom3887 Fin15AnchoredAtom4053
    Fin15AnchoredAtom4055 Fin15AnchoredAtom4059 Fin15AnchoredAtom4133 Fin15AnchoredAtom4217
    Fin15AnchoredAtom4427 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31146 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom2147 chi ∧
      ¬Fin15AnchoredAtom2150 chi ∧
      ¬Fin15AnchoredAtom2154 chi ∧
      ¬Fin15AnchoredAtom2165 chi ∧
      ¬Fin15AnchoredAtom2166 chi ∧
      ¬Fin15AnchoredAtom2169 chi ∧
      ¬Fin15AnchoredAtom2192 chi ∧
      ¬Fin15AnchoredAtom2195 chi ∧
      ¬Fin15AnchoredAtom2199 chi ∧
      ¬Fin15AnchoredAtom2228 chi ∧
      ¬Fin15AnchoredAtom2231 chi ∧
      ¬Fin15AnchoredAtom2235 chi ∧
      ¬Fin15AnchoredAtom2309 chi ∧
      ¬Fin15AnchoredAtom2330 chi ∧
      ¬Fin15AnchoredAtom2331 chi ∧
      ¬Fin15AnchoredAtom2334 chi ∧
      ¬Fin15AnchoredAtom2357 chi ∧
      ¬Fin15AnchoredAtom2360 chi ∧
      ¬Fin15AnchoredAtom2364 chi ∧
      ¬Fin15AnchoredAtom2393 chi ∧
      ¬Fin15AnchoredAtom2396 chi ∧
      ¬Fin15AnchoredAtom2400 chi ∧
      ¬Fin15AnchoredAtom2474 chi ∧
      ¬Fin15AnchoredAtom2513 chi ∧
      ¬Fin15AnchoredAtom2516 chi ∧
      ¬Fin15AnchoredAtom2520 chi ∧
      ¬Fin15AnchoredAtom2594 chi ∧
      ¬Fin15AnchoredAtom2678 chi ∧
      ¬Fin15AnchoredAtom3540 chi ∧
      ¬Fin15AnchoredAtom3541 chi ∧
      ¬Fin15AnchoredAtom3544 chi ∧
      ¬Fin15AnchoredAtom3567 chi ∧
      ¬Fin15AnchoredAtom3570 chi ∧
      ¬Fin15AnchoredAtom3574 chi ∧
      ¬Fin15AnchoredAtom3603 chi ∧
      ¬Fin15AnchoredAtom3606 chi ∧
      ¬Fin15AnchoredAtom3610 chi ∧
      ¬Fin15AnchoredAtom3684 chi ∧
      ¬Fin15AnchoredAtom3723 chi ∧
      ¬Fin15AnchoredAtom3726 chi ∧
      ¬Fin15AnchoredAtom3730 chi ∧
      ¬Fin15AnchoredAtom3804 chi ∧
      ¬Fin15AnchoredAtom3888 chi ∧
      ¬Fin15AnchoredAtom4053 chi ∧
      ¬Fin15AnchoredAtom4056 chi ∧
      ¬Fin15AnchoredAtom4060 chi ∧
      ¬Fin15AnchoredAtom4134 chi ∧
      ¬Fin15AnchoredAtom4218 chi ∧
      ¬Fin15AnchoredAtom4428 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 5, 9, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09789
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2107 Fin15AnchoredAtom2111 Fin15AnchoredAtom2112
    Fin15AnchoredAtom2115 Fin15AnchoredAtom2120 Fin15AnchoredAtom2121 Fin15AnchoredAtom2124
    Fin15AnchoredAtom2147 Fin15AnchoredAtom2150 Fin15AnchoredAtom2154 Fin15AnchoredAtom2165
    Fin15AnchoredAtom2166 Fin15AnchoredAtom2169 Fin15AnchoredAtom2192 Fin15AnchoredAtom2195
    Fin15AnchoredAtom2199 Fin15AnchoredAtom2228 Fin15AnchoredAtom2231 Fin15AnchoredAtom2235
    Fin15AnchoredAtom2309 Fin15AnchoredAtom2330 Fin15AnchoredAtom2331 Fin15AnchoredAtom2334
    Fin15AnchoredAtom2357 Fin15AnchoredAtom2360 Fin15AnchoredAtom2364 Fin15AnchoredAtom2393
    Fin15AnchoredAtom2396 Fin15AnchoredAtom2400 Fin15AnchoredAtom2474 Fin15AnchoredAtom2513
    Fin15AnchoredAtom2516 Fin15AnchoredAtom2520 Fin15AnchoredAtom2594 Fin15AnchoredAtom2678
    Fin15AnchoredAtom3540 Fin15AnchoredAtom3541 Fin15AnchoredAtom3544 Fin15AnchoredAtom3567
    Fin15AnchoredAtom3570 Fin15AnchoredAtom3574 Fin15AnchoredAtom3603 Fin15AnchoredAtom3606
    Fin15AnchoredAtom3610 Fin15AnchoredAtom3684 Fin15AnchoredAtom3723 Fin15AnchoredAtom3726
    Fin15AnchoredAtom3730 Fin15AnchoredAtom3804 Fin15AnchoredAtom3888 Fin15AnchoredAtom4053
    Fin15AnchoredAtom4056 Fin15AnchoredAtom4060 Fin15AnchoredAtom4134 Fin15AnchoredAtom4218
    Fin15AnchoredAtom4428 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31147 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom2147 chi ∧
      ¬Fin15AnchoredAtom2151 chi ∧
      ¬Fin15AnchoredAtom2155 chi ∧
      ¬Fin15AnchoredAtom2165 chi ∧
      ¬Fin15AnchoredAtom2166 chi ∧
      ¬Fin15AnchoredAtom2170 chi ∧
      ¬Fin15AnchoredAtom2192 chi ∧
      ¬Fin15AnchoredAtom2196 chi ∧
      ¬Fin15AnchoredAtom2200 chi ∧
      ¬Fin15AnchoredAtom2228 chi ∧
      ¬Fin15AnchoredAtom2232 chi ∧
      ¬Fin15AnchoredAtom2236 chi ∧
      ¬Fin15AnchoredAtom2310 chi ∧
      ¬Fin15AnchoredAtom2330 chi ∧
      ¬Fin15AnchoredAtom2331 chi ∧
      ¬Fin15AnchoredAtom2335 chi ∧
      ¬Fin15AnchoredAtom2357 chi ∧
      ¬Fin15AnchoredAtom2361 chi ∧
      ¬Fin15AnchoredAtom2365 chi ∧
      ¬Fin15AnchoredAtom2393 chi ∧
      ¬Fin15AnchoredAtom2397 chi ∧
      ¬Fin15AnchoredAtom2401 chi ∧
      ¬Fin15AnchoredAtom2475 chi ∧
      ¬Fin15AnchoredAtom2513 chi ∧
      ¬Fin15AnchoredAtom2517 chi ∧
      ¬Fin15AnchoredAtom2521 chi ∧
      ¬Fin15AnchoredAtom2595 chi ∧
      ¬Fin15AnchoredAtom2679 chi ∧
      ¬Fin15AnchoredAtom3540 chi ∧
      ¬Fin15AnchoredAtom3541 chi ∧
      ¬Fin15AnchoredAtom3545 chi ∧
      ¬Fin15AnchoredAtom3567 chi ∧
      ¬Fin15AnchoredAtom3571 chi ∧
      ¬Fin15AnchoredAtom3575 chi ∧
      ¬Fin15AnchoredAtom3603 chi ∧
      ¬Fin15AnchoredAtom3607 chi ∧
      ¬Fin15AnchoredAtom3611 chi ∧
      ¬Fin15AnchoredAtom3685 chi ∧
      ¬Fin15AnchoredAtom3723 chi ∧
      ¬Fin15AnchoredAtom3727 chi ∧
      ¬Fin15AnchoredAtom3731 chi ∧
      ¬Fin15AnchoredAtom3805 chi ∧
      ¬Fin15AnchoredAtom3889 chi ∧
      ¬Fin15AnchoredAtom4053 chi ∧
      ¬Fin15AnchoredAtom4057 chi ∧
      ¬Fin15AnchoredAtom4061 chi ∧
      ¬Fin15AnchoredAtom4135 chi ∧
      ¬Fin15AnchoredAtom4219 chi ∧
      ¬Fin15AnchoredAtom4429 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 5, 9, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17981
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2107 Fin15AnchoredAtom2111 Fin15AnchoredAtom2112
    Fin15AnchoredAtom2116 Fin15AnchoredAtom2120 Fin15AnchoredAtom2121 Fin15AnchoredAtom2125
    Fin15AnchoredAtom2147 Fin15AnchoredAtom2151 Fin15AnchoredAtom2155 Fin15AnchoredAtom2165
    Fin15AnchoredAtom2166 Fin15AnchoredAtom2170 Fin15AnchoredAtom2192 Fin15AnchoredAtom2196
    Fin15AnchoredAtom2200 Fin15AnchoredAtom2228 Fin15AnchoredAtom2232 Fin15AnchoredAtom2236
    Fin15AnchoredAtom2310 Fin15AnchoredAtom2330 Fin15AnchoredAtom2331 Fin15AnchoredAtom2335
    Fin15AnchoredAtom2357 Fin15AnchoredAtom2361 Fin15AnchoredAtom2365 Fin15AnchoredAtom2393
    Fin15AnchoredAtom2397 Fin15AnchoredAtom2401 Fin15AnchoredAtom2475 Fin15AnchoredAtom2513
    Fin15AnchoredAtom2517 Fin15AnchoredAtom2521 Fin15AnchoredAtom2595 Fin15AnchoredAtom2679
    Fin15AnchoredAtom3540 Fin15AnchoredAtom3541 Fin15AnchoredAtom3545 Fin15AnchoredAtom3567
    Fin15AnchoredAtom3571 Fin15AnchoredAtom3575 Fin15AnchoredAtom3603 Fin15AnchoredAtom3607
    Fin15AnchoredAtom3611 Fin15AnchoredAtom3685 Fin15AnchoredAtom3723 Fin15AnchoredAtom3727
    Fin15AnchoredAtom3731 Fin15AnchoredAtom3805 Fin15AnchoredAtom3889 Fin15AnchoredAtom4053
    Fin15AnchoredAtom4057 Fin15AnchoredAtom4061 Fin15AnchoredAtom4135 Fin15AnchoredAtom4219
    Fin15AnchoredAtom4429 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31148 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom2149 chi ∧
      ¬Fin15AnchoredAtom2150 chi ∧
      ¬Fin15AnchoredAtom2159 chi ∧
      ¬Fin15AnchoredAtom2165 chi ∧
      ¬Fin15AnchoredAtom2168 chi ∧
      ¬Fin15AnchoredAtom2169 chi ∧
      ¬Fin15AnchoredAtom2194 chi ∧
      ¬Fin15AnchoredAtom2195 chi ∧
      ¬Fin15AnchoredAtom2204 chi ∧
      ¬Fin15AnchoredAtom2230 chi ∧
      ¬Fin15AnchoredAtom2231 chi ∧
      ¬Fin15AnchoredAtom2240 chi ∧
      ¬Fin15AnchoredAtom2314 chi ∧
      ¬Fin15AnchoredAtom2330 chi ∧
      ¬Fin15AnchoredAtom2333 chi ∧
      ¬Fin15AnchoredAtom2334 chi ∧
      ¬Fin15AnchoredAtom2359 chi ∧
      ¬Fin15AnchoredAtom2360 chi ∧
      ¬Fin15AnchoredAtom2369 chi ∧
      ¬Fin15AnchoredAtom2395 chi ∧
      ¬Fin15AnchoredAtom2396 chi ∧
      ¬Fin15AnchoredAtom2405 chi ∧
      ¬Fin15AnchoredAtom2479 chi ∧
      ¬Fin15AnchoredAtom2515 chi ∧
      ¬Fin15AnchoredAtom2516 chi ∧
      ¬Fin15AnchoredAtom2525 chi ∧
      ¬Fin15AnchoredAtom2599 chi ∧
      ¬Fin15AnchoredAtom2683 chi ∧
      ¬Fin15AnchoredAtom3540 chi ∧
      ¬Fin15AnchoredAtom3543 chi ∧
      ¬Fin15AnchoredAtom3544 chi ∧
      ¬Fin15AnchoredAtom3569 chi ∧
      ¬Fin15AnchoredAtom3570 chi ∧
      ¬Fin15AnchoredAtom3579 chi ∧
      ¬Fin15AnchoredAtom3605 chi ∧
      ¬Fin15AnchoredAtom3606 chi ∧
      ¬Fin15AnchoredAtom3615 chi ∧
      ¬Fin15AnchoredAtom3689 chi ∧
      ¬Fin15AnchoredAtom3725 chi ∧
      ¬Fin15AnchoredAtom3726 chi ∧
      ¬Fin15AnchoredAtom3735 chi ∧
      ¬Fin15AnchoredAtom3809 chi ∧
      ¬Fin15AnchoredAtom3893 chi ∧
      ¬Fin15AnchoredAtom4055 chi ∧
      ¬Fin15AnchoredAtom4056 chi ∧
      ¬Fin15AnchoredAtom4065 chi ∧
      ¬Fin15AnchoredAtom4139 chi ∧
      ¬Fin15AnchoredAtom4223 chi ∧
      ¬Fin15AnchoredAtom4433 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 5, 9, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask12861
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2107 Fin15AnchoredAtom2111 Fin15AnchoredAtom2114
    Fin15AnchoredAtom2115 Fin15AnchoredAtom2120 Fin15AnchoredAtom2123 Fin15AnchoredAtom2124
    Fin15AnchoredAtom2149 Fin15AnchoredAtom2150 Fin15AnchoredAtom2159 Fin15AnchoredAtom2165
    Fin15AnchoredAtom2168 Fin15AnchoredAtom2169 Fin15AnchoredAtom2194 Fin15AnchoredAtom2195
    Fin15AnchoredAtom2204 Fin15AnchoredAtom2230 Fin15AnchoredAtom2231 Fin15AnchoredAtom2240
    Fin15AnchoredAtom2314 Fin15AnchoredAtom2330 Fin15AnchoredAtom2333 Fin15AnchoredAtom2334
    Fin15AnchoredAtom2359 Fin15AnchoredAtom2360 Fin15AnchoredAtom2369 Fin15AnchoredAtom2395
    Fin15AnchoredAtom2396 Fin15AnchoredAtom2405 Fin15AnchoredAtom2479 Fin15AnchoredAtom2515
    Fin15AnchoredAtom2516 Fin15AnchoredAtom2525 Fin15AnchoredAtom2599 Fin15AnchoredAtom2683
    Fin15AnchoredAtom3540 Fin15AnchoredAtom3543 Fin15AnchoredAtom3544 Fin15AnchoredAtom3569
    Fin15AnchoredAtom3570 Fin15AnchoredAtom3579 Fin15AnchoredAtom3605 Fin15AnchoredAtom3606
    Fin15AnchoredAtom3615 Fin15AnchoredAtom3689 Fin15AnchoredAtom3725 Fin15AnchoredAtom3726
    Fin15AnchoredAtom3735 Fin15AnchoredAtom3809 Fin15AnchoredAtom3893 Fin15AnchoredAtom4055
    Fin15AnchoredAtom4056 Fin15AnchoredAtom4065 Fin15AnchoredAtom4139 Fin15AnchoredAtom4223
    Fin15AnchoredAtom4433 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31149 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom2149 chi ∧
      ¬Fin15AnchoredAtom2151 chi ∧
      ¬Fin15AnchoredAtom2160 chi ∧
      ¬Fin15AnchoredAtom2165 chi ∧
      ¬Fin15AnchoredAtom2168 chi ∧
      ¬Fin15AnchoredAtom2170 chi ∧
      ¬Fin15AnchoredAtom2194 chi ∧
      ¬Fin15AnchoredAtom2196 chi ∧
      ¬Fin15AnchoredAtom2205 chi ∧
      ¬Fin15AnchoredAtom2230 chi ∧
      ¬Fin15AnchoredAtom2232 chi ∧
      ¬Fin15AnchoredAtom2241 chi ∧
      ¬Fin15AnchoredAtom2315 chi ∧
      ¬Fin15AnchoredAtom2330 chi ∧
      ¬Fin15AnchoredAtom2333 chi ∧
      ¬Fin15AnchoredAtom2335 chi ∧
      ¬Fin15AnchoredAtom2359 chi ∧
      ¬Fin15AnchoredAtom2361 chi ∧
      ¬Fin15AnchoredAtom2370 chi ∧
      ¬Fin15AnchoredAtom2395 chi ∧
      ¬Fin15AnchoredAtom2397 chi ∧
      ¬Fin15AnchoredAtom2406 chi ∧
      ¬Fin15AnchoredAtom2480 chi ∧
      ¬Fin15AnchoredAtom2515 chi ∧
      ¬Fin15AnchoredAtom2517 chi ∧
      ¬Fin15AnchoredAtom2526 chi ∧
      ¬Fin15AnchoredAtom2600 chi ∧
      ¬Fin15AnchoredAtom2684 chi ∧
      ¬Fin15AnchoredAtom3540 chi ∧
      ¬Fin15AnchoredAtom3543 chi ∧
      ¬Fin15AnchoredAtom3545 chi ∧
      ¬Fin15AnchoredAtom3569 chi ∧
      ¬Fin15AnchoredAtom3571 chi ∧
      ¬Fin15AnchoredAtom3580 chi ∧
      ¬Fin15AnchoredAtom3605 chi ∧
      ¬Fin15AnchoredAtom3607 chi ∧
      ¬Fin15AnchoredAtom3616 chi ∧
      ¬Fin15AnchoredAtom3690 chi ∧
      ¬Fin15AnchoredAtom3725 chi ∧
      ¬Fin15AnchoredAtom3727 chi ∧
      ¬Fin15AnchoredAtom3736 chi ∧
      ¬Fin15AnchoredAtom3810 chi ∧
      ¬Fin15AnchoredAtom3894 chi ∧
      ¬Fin15AnchoredAtom4055 chi ∧
      ¬Fin15AnchoredAtom4057 chi ∧
      ¬Fin15AnchoredAtom4066 chi ∧
      ¬Fin15AnchoredAtom4140 chi ∧
      ¬Fin15AnchoredAtom4224 chi ∧
      ¬Fin15AnchoredAtom4434 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 5, 9, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21053
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2107 Fin15AnchoredAtom2111 Fin15AnchoredAtom2114
    Fin15AnchoredAtom2116 Fin15AnchoredAtom2120 Fin15AnchoredAtom2123 Fin15AnchoredAtom2125
    Fin15AnchoredAtom2149 Fin15AnchoredAtom2151 Fin15AnchoredAtom2160 Fin15AnchoredAtom2165
    Fin15AnchoredAtom2168 Fin15AnchoredAtom2170 Fin15AnchoredAtom2194 Fin15AnchoredAtom2196
    Fin15AnchoredAtom2205 Fin15AnchoredAtom2230 Fin15AnchoredAtom2232 Fin15AnchoredAtom2241
    Fin15AnchoredAtom2315 Fin15AnchoredAtom2330 Fin15AnchoredAtom2333 Fin15AnchoredAtom2335
    Fin15AnchoredAtom2359 Fin15AnchoredAtom2361 Fin15AnchoredAtom2370 Fin15AnchoredAtom2395
    Fin15AnchoredAtom2397 Fin15AnchoredAtom2406 Fin15AnchoredAtom2480 Fin15AnchoredAtom2515
    Fin15AnchoredAtom2517 Fin15AnchoredAtom2526 Fin15AnchoredAtom2600 Fin15AnchoredAtom2684
    Fin15AnchoredAtom3540 Fin15AnchoredAtom3543 Fin15AnchoredAtom3545 Fin15AnchoredAtom3569
    Fin15AnchoredAtom3571 Fin15AnchoredAtom3580 Fin15AnchoredAtom3605 Fin15AnchoredAtom3607
    Fin15AnchoredAtom3616 Fin15AnchoredAtom3690 Fin15AnchoredAtom3725 Fin15AnchoredAtom3727
    Fin15AnchoredAtom3736 Fin15AnchoredAtom3810 Fin15AnchoredAtom3894 Fin15AnchoredAtom4055
    Fin15AnchoredAtom4057 Fin15AnchoredAtom4066 Fin15AnchoredAtom4140 Fin15AnchoredAtom4224
    Fin15AnchoredAtom4434 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31150 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom2150 chi ∧
      ¬Fin15AnchoredAtom2151 chi ∧
      ¬Fin15AnchoredAtom2161 chi ∧
      ¬Fin15AnchoredAtom2165 chi ∧
      ¬Fin15AnchoredAtom2169 chi ∧
      ¬Fin15AnchoredAtom2170 chi ∧
      ¬Fin15AnchoredAtom2195 chi ∧
      ¬Fin15AnchoredAtom2196 chi ∧
      ¬Fin15AnchoredAtom2206 chi ∧
      ¬Fin15AnchoredAtom2231 chi ∧
      ¬Fin15AnchoredAtom2232 chi ∧
      ¬Fin15AnchoredAtom2242 chi ∧
      ¬Fin15AnchoredAtom2316 chi ∧
      ¬Fin15AnchoredAtom2330 chi ∧
      ¬Fin15AnchoredAtom2334 chi ∧
      ¬Fin15AnchoredAtom2335 chi ∧
      ¬Fin15AnchoredAtom2360 chi ∧
      ¬Fin15AnchoredAtom2361 chi ∧
      ¬Fin15AnchoredAtom2371 chi ∧
      ¬Fin15AnchoredAtom2396 chi ∧
      ¬Fin15AnchoredAtom2397 chi ∧
      ¬Fin15AnchoredAtom2407 chi ∧
      ¬Fin15AnchoredAtom2481 chi ∧
      ¬Fin15AnchoredAtom2516 chi ∧
      ¬Fin15AnchoredAtom2517 chi ∧
      ¬Fin15AnchoredAtom2527 chi ∧
      ¬Fin15AnchoredAtom2601 chi ∧
      ¬Fin15AnchoredAtom2685 chi ∧
      ¬Fin15AnchoredAtom3540 chi ∧
      ¬Fin15AnchoredAtom3544 chi ∧
      ¬Fin15AnchoredAtom3545 chi ∧
      ¬Fin15AnchoredAtom3570 chi ∧
      ¬Fin15AnchoredAtom3571 chi ∧
      ¬Fin15AnchoredAtom3581 chi ∧
      ¬Fin15AnchoredAtom3606 chi ∧
      ¬Fin15AnchoredAtom3607 chi ∧
      ¬Fin15AnchoredAtom3617 chi ∧
      ¬Fin15AnchoredAtom3691 chi ∧
      ¬Fin15AnchoredAtom3726 chi ∧
      ¬Fin15AnchoredAtom3727 chi ∧
      ¬Fin15AnchoredAtom3737 chi ∧
      ¬Fin15AnchoredAtom3811 chi ∧
      ¬Fin15AnchoredAtom3895 chi ∧
      ¬Fin15AnchoredAtom4056 chi ∧
      ¬Fin15AnchoredAtom4057 chi ∧
      ¬Fin15AnchoredAtom4067 chi ∧
      ¬Fin15AnchoredAtom4141 chi ∧
      ¬Fin15AnchoredAtom4225 chi ∧
      ¬Fin15AnchoredAtom4435 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 5, 9, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25149
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2107 Fin15AnchoredAtom2111 Fin15AnchoredAtom2115
    Fin15AnchoredAtom2116 Fin15AnchoredAtom2120 Fin15AnchoredAtom2124 Fin15AnchoredAtom2125
    Fin15AnchoredAtom2150 Fin15AnchoredAtom2151 Fin15AnchoredAtom2161 Fin15AnchoredAtom2165
    Fin15AnchoredAtom2169 Fin15AnchoredAtom2170 Fin15AnchoredAtom2195 Fin15AnchoredAtom2196
    Fin15AnchoredAtom2206 Fin15AnchoredAtom2231 Fin15AnchoredAtom2232 Fin15AnchoredAtom2242
    Fin15AnchoredAtom2316 Fin15AnchoredAtom2330 Fin15AnchoredAtom2334 Fin15AnchoredAtom2335
    Fin15AnchoredAtom2360 Fin15AnchoredAtom2361 Fin15AnchoredAtom2371 Fin15AnchoredAtom2396
    Fin15AnchoredAtom2397 Fin15AnchoredAtom2407 Fin15AnchoredAtom2481 Fin15AnchoredAtom2516
    Fin15AnchoredAtom2517 Fin15AnchoredAtom2527 Fin15AnchoredAtom2601 Fin15AnchoredAtom2685
    Fin15AnchoredAtom3540 Fin15AnchoredAtom3544 Fin15AnchoredAtom3545 Fin15AnchoredAtom3570
    Fin15AnchoredAtom3571 Fin15AnchoredAtom3581 Fin15AnchoredAtom3606 Fin15AnchoredAtom3607
    Fin15AnchoredAtom3617 Fin15AnchoredAtom3691 Fin15AnchoredAtom3726 Fin15AnchoredAtom3727
    Fin15AnchoredAtom3737 Fin15AnchoredAtom3811 Fin15AnchoredAtom3895 Fin15AnchoredAtom4056
    Fin15AnchoredAtom4057 Fin15AnchoredAtom4067 Fin15AnchoredAtom4141 Fin15AnchoredAtom4225
    Fin15AnchoredAtom4435 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31151 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2113 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2122 chi ∧
      ¬Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom2152 chi ∧
      ¬Fin15AnchoredAtom2153 chi ∧
      ¬Fin15AnchoredAtom2156 chi ∧
      ¬Fin15AnchoredAtom2166 chi ∧
      ¬Fin15AnchoredAtom2167 chi ∧
      ¬Fin15AnchoredAtom2168 chi ∧
      ¬Fin15AnchoredAtom2197 chi ∧
      ¬Fin15AnchoredAtom2198 chi ∧
      ¬Fin15AnchoredAtom2201 chi ∧
      ¬Fin15AnchoredAtom2233 chi ∧
      ¬Fin15AnchoredAtom2234 chi ∧
      ¬Fin15AnchoredAtom2237 chi ∧
      ¬Fin15AnchoredAtom2317 chi ∧
      ¬Fin15AnchoredAtom2331 chi ∧
      ¬Fin15AnchoredAtom2332 chi ∧
      ¬Fin15AnchoredAtom2333 chi ∧
      ¬Fin15AnchoredAtom2362 chi ∧
      ¬Fin15AnchoredAtom2363 chi ∧
      ¬Fin15AnchoredAtom2366 chi ∧
      ¬Fin15AnchoredAtom2398 chi ∧
      ¬Fin15AnchoredAtom2399 chi ∧
      ¬Fin15AnchoredAtom2402 chi ∧
      ¬Fin15AnchoredAtom2482 chi ∧
      ¬Fin15AnchoredAtom2518 chi ∧
      ¬Fin15AnchoredAtom2519 chi ∧
      ¬Fin15AnchoredAtom2522 chi ∧
      ¬Fin15AnchoredAtom2602 chi ∧
      ¬Fin15AnchoredAtom2686 chi ∧
      ¬Fin15AnchoredAtom3541 chi ∧
      ¬Fin15AnchoredAtom3542 chi ∧
      ¬Fin15AnchoredAtom3543 chi ∧
      ¬Fin15AnchoredAtom3572 chi ∧
      ¬Fin15AnchoredAtom3573 chi ∧
      ¬Fin15AnchoredAtom3576 chi ∧
      ¬Fin15AnchoredAtom3608 chi ∧
      ¬Fin15AnchoredAtom3609 chi ∧
      ¬Fin15AnchoredAtom3612 chi ∧
      ¬Fin15AnchoredAtom3692 chi ∧
      ¬Fin15AnchoredAtom3728 chi ∧
      ¬Fin15AnchoredAtom3729 chi ∧
      ¬Fin15AnchoredAtom3732 chi ∧
      ¬Fin15AnchoredAtom3812 chi ∧
      ¬Fin15AnchoredAtom3896 chi ∧
      ¬Fin15AnchoredAtom4058 chi ∧
      ¬Fin15AnchoredAtom4059 chi ∧
      ¬Fin15AnchoredAtom4062 chi ∧
      ¬Fin15AnchoredAtom4142 chi ∧
      ¬Fin15AnchoredAtom4226 chi ∧
      ¬Fin15AnchoredAtom4436 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 5, 10, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask07229
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2107 Fin15AnchoredAtom2112 Fin15AnchoredAtom2113
    Fin15AnchoredAtom2114 Fin15AnchoredAtom2121 Fin15AnchoredAtom2122 Fin15AnchoredAtom2123
    Fin15AnchoredAtom2152 Fin15AnchoredAtom2153 Fin15AnchoredAtom2156 Fin15AnchoredAtom2166
    Fin15AnchoredAtom2167 Fin15AnchoredAtom2168 Fin15AnchoredAtom2197 Fin15AnchoredAtom2198
    Fin15AnchoredAtom2201 Fin15AnchoredAtom2233 Fin15AnchoredAtom2234 Fin15AnchoredAtom2237
    Fin15AnchoredAtom2317 Fin15AnchoredAtom2331 Fin15AnchoredAtom2332 Fin15AnchoredAtom2333
    Fin15AnchoredAtom2362 Fin15AnchoredAtom2363 Fin15AnchoredAtom2366 Fin15AnchoredAtom2398
    Fin15AnchoredAtom2399 Fin15AnchoredAtom2402 Fin15AnchoredAtom2482 Fin15AnchoredAtom2518
    Fin15AnchoredAtom2519 Fin15AnchoredAtom2522 Fin15AnchoredAtom2602 Fin15AnchoredAtom2686
    Fin15AnchoredAtom3541 Fin15AnchoredAtom3542 Fin15AnchoredAtom3543 Fin15AnchoredAtom3572
    Fin15AnchoredAtom3573 Fin15AnchoredAtom3576 Fin15AnchoredAtom3608 Fin15AnchoredAtom3609
    Fin15AnchoredAtom3612 Fin15AnchoredAtom3692 Fin15AnchoredAtom3728 Fin15AnchoredAtom3729
    Fin15AnchoredAtom3732 Fin15AnchoredAtom3812 Fin15AnchoredAtom3896 Fin15AnchoredAtom4058
    Fin15AnchoredAtom4059 Fin15AnchoredAtom4062 Fin15AnchoredAtom4142 Fin15AnchoredAtom4226
    Fin15AnchoredAtom4436 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31152 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom2153 chi ∧
      ¬Fin15AnchoredAtom2154 chi ∧
      ¬Fin15AnchoredAtom2159 chi ∧
      ¬Fin15AnchoredAtom2166 chi ∧
      ¬Fin15AnchoredAtom2168 chi ∧
      ¬Fin15AnchoredAtom2169 chi ∧
      ¬Fin15AnchoredAtom2198 chi ∧
      ¬Fin15AnchoredAtom2199 chi ∧
      ¬Fin15AnchoredAtom2204 chi ∧
      ¬Fin15AnchoredAtom2234 chi ∧
      ¬Fin15AnchoredAtom2235 chi ∧
      ¬Fin15AnchoredAtom2240 chi ∧
      ¬Fin15AnchoredAtom2320 chi ∧
      ¬Fin15AnchoredAtom2331 chi ∧
      ¬Fin15AnchoredAtom2333 chi ∧
      ¬Fin15AnchoredAtom2334 chi ∧
      ¬Fin15AnchoredAtom2363 chi ∧
      ¬Fin15AnchoredAtom2364 chi ∧
      ¬Fin15AnchoredAtom2369 chi ∧
      ¬Fin15AnchoredAtom2399 chi ∧
      ¬Fin15AnchoredAtom2400 chi ∧
      ¬Fin15AnchoredAtom2405 chi ∧
      ¬Fin15AnchoredAtom2485 chi ∧
      ¬Fin15AnchoredAtom2519 chi ∧
      ¬Fin15AnchoredAtom2520 chi ∧
      ¬Fin15AnchoredAtom2525 chi ∧
      ¬Fin15AnchoredAtom2605 chi ∧
      ¬Fin15AnchoredAtom2689 chi ∧
      ¬Fin15AnchoredAtom3541 chi ∧
      ¬Fin15AnchoredAtom3543 chi ∧
      ¬Fin15AnchoredAtom3544 chi ∧
      ¬Fin15AnchoredAtom3573 chi ∧
      ¬Fin15AnchoredAtom3574 chi ∧
      ¬Fin15AnchoredAtom3579 chi ∧
      ¬Fin15AnchoredAtom3609 chi ∧
      ¬Fin15AnchoredAtom3610 chi ∧
      ¬Fin15AnchoredAtom3615 chi ∧
      ¬Fin15AnchoredAtom3695 chi ∧
      ¬Fin15AnchoredAtom3729 chi ∧
      ¬Fin15AnchoredAtom3730 chi ∧
      ¬Fin15AnchoredAtom3735 chi ∧
      ¬Fin15AnchoredAtom3815 chi ∧
      ¬Fin15AnchoredAtom3899 chi ∧
      ¬Fin15AnchoredAtom4059 chi ∧
      ¬Fin15AnchoredAtom4060 chi ∧
      ¬Fin15AnchoredAtom4065 chi ∧
      ¬Fin15AnchoredAtom4145 chi ∧
      ¬Fin15AnchoredAtom4229 chi ∧
      ¬Fin15AnchoredAtom4439 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 5, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13373
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2107 Fin15AnchoredAtom2112 Fin15AnchoredAtom2114
    Fin15AnchoredAtom2115 Fin15AnchoredAtom2121 Fin15AnchoredAtom2123 Fin15AnchoredAtom2124
    Fin15AnchoredAtom2153 Fin15AnchoredAtom2154 Fin15AnchoredAtom2159 Fin15AnchoredAtom2166
    Fin15AnchoredAtom2168 Fin15AnchoredAtom2169 Fin15AnchoredAtom2198 Fin15AnchoredAtom2199
    Fin15AnchoredAtom2204 Fin15AnchoredAtom2234 Fin15AnchoredAtom2235 Fin15AnchoredAtom2240
    Fin15AnchoredAtom2320 Fin15AnchoredAtom2331 Fin15AnchoredAtom2333 Fin15AnchoredAtom2334
    Fin15AnchoredAtom2363 Fin15AnchoredAtom2364 Fin15AnchoredAtom2369 Fin15AnchoredAtom2399
    Fin15AnchoredAtom2400 Fin15AnchoredAtom2405 Fin15AnchoredAtom2485 Fin15AnchoredAtom2519
    Fin15AnchoredAtom2520 Fin15AnchoredAtom2525 Fin15AnchoredAtom2605 Fin15AnchoredAtom2689
    Fin15AnchoredAtom3541 Fin15AnchoredAtom3543 Fin15AnchoredAtom3544 Fin15AnchoredAtom3573
    Fin15AnchoredAtom3574 Fin15AnchoredAtom3579 Fin15AnchoredAtom3609 Fin15AnchoredAtom3610
    Fin15AnchoredAtom3615 Fin15AnchoredAtom3695 Fin15AnchoredAtom3729 Fin15AnchoredAtom3730
    Fin15AnchoredAtom3735 Fin15AnchoredAtom3815 Fin15AnchoredAtom3899 Fin15AnchoredAtom4059
    Fin15AnchoredAtom4060 Fin15AnchoredAtom4065 Fin15AnchoredAtom4145 Fin15AnchoredAtom4229
    Fin15AnchoredAtom4439 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31153 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom2153 chi ∧
      ¬Fin15AnchoredAtom2155 chi ∧
      ¬Fin15AnchoredAtom2160 chi ∧
      ¬Fin15AnchoredAtom2166 chi ∧
      ¬Fin15AnchoredAtom2168 chi ∧
      ¬Fin15AnchoredAtom2170 chi ∧
      ¬Fin15AnchoredAtom2198 chi ∧
      ¬Fin15AnchoredAtom2200 chi ∧
      ¬Fin15AnchoredAtom2205 chi ∧
      ¬Fin15AnchoredAtom2234 chi ∧
      ¬Fin15AnchoredAtom2236 chi ∧
      ¬Fin15AnchoredAtom2241 chi ∧
      ¬Fin15AnchoredAtom2321 chi ∧
      ¬Fin15AnchoredAtom2331 chi ∧
      ¬Fin15AnchoredAtom2333 chi ∧
      ¬Fin15AnchoredAtom2335 chi ∧
      ¬Fin15AnchoredAtom2363 chi ∧
      ¬Fin15AnchoredAtom2365 chi ∧
      ¬Fin15AnchoredAtom2370 chi ∧
      ¬Fin15AnchoredAtom2399 chi ∧
      ¬Fin15AnchoredAtom2401 chi ∧
      ¬Fin15AnchoredAtom2406 chi ∧
      ¬Fin15AnchoredAtom2486 chi ∧
      ¬Fin15AnchoredAtom2519 chi ∧
      ¬Fin15AnchoredAtom2521 chi ∧
      ¬Fin15AnchoredAtom2526 chi ∧
      ¬Fin15AnchoredAtom2606 chi ∧
      ¬Fin15AnchoredAtom2690 chi ∧
      ¬Fin15AnchoredAtom3541 chi ∧
      ¬Fin15AnchoredAtom3543 chi ∧
      ¬Fin15AnchoredAtom3545 chi ∧
      ¬Fin15AnchoredAtom3573 chi ∧
      ¬Fin15AnchoredAtom3575 chi ∧
      ¬Fin15AnchoredAtom3580 chi ∧
      ¬Fin15AnchoredAtom3609 chi ∧
      ¬Fin15AnchoredAtom3611 chi ∧
      ¬Fin15AnchoredAtom3616 chi ∧
      ¬Fin15AnchoredAtom3696 chi ∧
      ¬Fin15AnchoredAtom3729 chi ∧
      ¬Fin15AnchoredAtom3731 chi ∧
      ¬Fin15AnchoredAtom3736 chi ∧
      ¬Fin15AnchoredAtom3816 chi ∧
      ¬Fin15AnchoredAtom3900 chi ∧
      ¬Fin15AnchoredAtom4059 chi ∧
      ¬Fin15AnchoredAtom4061 chi ∧
      ¬Fin15AnchoredAtom4066 chi ∧
      ¬Fin15AnchoredAtom4146 chi ∧
      ¬Fin15AnchoredAtom4230 chi ∧
      ¬Fin15AnchoredAtom4440 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 5, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21565
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2107 Fin15AnchoredAtom2112 Fin15AnchoredAtom2114
    Fin15AnchoredAtom2116 Fin15AnchoredAtom2121 Fin15AnchoredAtom2123 Fin15AnchoredAtom2125
    Fin15AnchoredAtom2153 Fin15AnchoredAtom2155 Fin15AnchoredAtom2160 Fin15AnchoredAtom2166
    Fin15AnchoredAtom2168 Fin15AnchoredAtom2170 Fin15AnchoredAtom2198 Fin15AnchoredAtom2200
    Fin15AnchoredAtom2205 Fin15AnchoredAtom2234 Fin15AnchoredAtom2236 Fin15AnchoredAtom2241
    Fin15AnchoredAtom2321 Fin15AnchoredAtom2331 Fin15AnchoredAtom2333 Fin15AnchoredAtom2335
    Fin15AnchoredAtom2363 Fin15AnchoredAtom2365 Fin15AnchoredAtom2370 Fin15AnchoredAtom2399
    Fin15AnchoredAtom2401 Fin15AnchoredAtom2406 Fin15AnchoredAtom2486 Fin15AnchoredAtom2519
    Fin15AnchoredAtom2521 Fin15AnchoredAtom2526 Fin15AnchoredAtom2606 Fin15AnchoredAtom2690
    Fin15AnchoredAtom3541 Fin15AnchoredAtom3543 Fin15AnchoredAtom3545 Fin15AnchoredAtom3573
    Fin15AnchoredAtom3575 Fin15AnchoredAtom3580 Fin15AnchoredAtom3609 Fin15AnchoredAtom3611
    Fin15AnchoredAtom3616 Fin15AnchoredAtom3696 Fin15AnchoredAtom3729 Fin15AnchoredAtom3731
    Fin15AnchoredAtom3736 Fin15AnchoredAtom3816 Fin15AnchoredAtom3900 Fin15AnchoredAtom4059
    Fin15AnchoredAtom4061 Fin15AnchoredAtom4066 Fin15AnchoredAtom4146 Fin15AnchoredAtom4230
    Fin15AnchoredAtom4440 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31154 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom2154 chi ∧
      ¬Fin15AnchoredAtom2155 chi ∧
      ¬Fin15AnchoredAtom2161 chi ∧
      ¬Fin15AnchoredAtom2166 chi ∧
      ¬Fin15AnchoredAtom2169 chi ∧
      ¬Fin15AnchoredAtom2170 chi ∧
      ¬Fin15AnchoredAtom2199 chi ∧
      ¬Fin15AnchoredAtom2200 chi ∧
      ¬Fin15AnchoredAtom2206 chi ∧
      ¬Fin15AnchoredAtom2235 chi ∧
      ¬Fin15AnchoredAtom2236 chi ∧
      ¬Fin15AnchoredAtom2242 chi ∧
      ¬Fin15AnchoredAtom2322 chi ∧
      ¬Fin15AnchoredAtom2331 chi ∧
      ¬Fin15AnchoredAtom2334 chi ∧
      ¬Fin15AnchoredAtom2335 chi ∧
      ¬Fin15AnchoredAtom2364 chi ∧
      ¬Fin15AnchoredAtom2365 chi ∧
      ¬Fin15AnchoredAtom2371 chi ∧
      ¬Fin15AnchoredAtom2400 chi ∧
      ¬Fin15AnchoredAtom2401 chi ∧
      ¬Fin15AnchoredAtom2407 chi ∧
      ¬Fin15AnchoredAtom2487 chi ∧
      ¬Fin15AnchoredAtom2520 chi ∧
      ¬Fin15AnchoredAtom2521 chi ∧
      ¬Fin15AnchoredAtom2527 chi ∧
      ¬Fin15AnchoredAtom2607 chi ∧
      ¬Fin15AnchoredAtom2691 chi ∧
      ¬Fin15AnchoredAtom3541 chi ∧
      ¬Fin15AnchoredAtom3544 chi ∧
      ¬Fin15AnchoredAtom3545 chi ∧
      ¬Fin15AnchoredAtom3574 chi ∧
      ¬Fin15AnchoredAtom3575 chi ∧
      ¬Fin15AnchoredAtom3581 chi ∧
      ¬Fin15AnchoredAtom3610 chi ∧
      ¬Fin15AnchoredAtom3611 chi ∧
      ¬Fin15AnchoredAtom3617 chi ∧
      ¬Fin15AnchoredAtom3697 chi ∧
      ¬Fin15AnchoredAtom3730 chi ∧
      ¬Fin15AnchoredAtom3731 chi ∧
      ¬Fin15AnchoredAtom3737 chi ∧
      ¬Fin15AnchoredAtom3817 chi ∧
      ¬Fin15AnchoredAtom3901 chi ∧
      ¬Fin15AnchoredAtom4060 chi ∧
      ¬Fin15AnchoredAtom4061 chi ∧
      ¬Fin15AnchoredAtom4067 chi ∧
      ¬Fin15AnchoredAtom4147 chi ∧
      ¬Fin15AnchoredAtom4231 chi ∧
      ¬Fin15AnchoredAtom4441 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 5, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25661
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2107 Fin15AnchoredAtom2112 Fin15AnchoredAtom2115
    Fin15AnchoredAtom2116 Fin15AnchoredAtom2121 Fin15AnchoredAtom2124 Fin15AnchoredAtom2125
    Fin15AnchoredAtom2154 Fin15AnchoredAtom2155 Fin15AnchoredAtom2161 Fin15AnchoredAtom2166
    Fin15AnchoredAtom2169 Fin15AnchoredAtom2170 Fin15AnchoredAtom2199 Fin15AnchoredAtom2200
    Fin15AnchoredAtom2206 Fin15AnchoredAtom2235 Fin15AnchoredAtom2236 Fin15AnchoredAtom2242
    Fin15AnchoredAtom2322 Fin15AnchoredAtom2331 Fin15AnchoredAtom2334 Fin15AnchoredAtom2335
    Fin15AnchoredAtom2364 Fin15AnchoredAtom2365 Fin15AnchoredAtom2371 Fin15AnchoredAtom2400
    Fin15AnchoredAtom2401 Fin15AnchoredAtom2407 Fin15AnchoredAtom2487 Fin15AnchoredAtom2520
    Fin15AnchoredAtom2521 Fin15AnchoredAtom2527 Fin15AnchoredAtom2607 Fin15AnchoredAtom2691
    Fin15AnchoredAtom3541 Fin15AnchoredAtom3544 Fin15AnchoredAtom3545 Fin15AnchoredAtom3574
    Fin15AnchoredAtom3575 Fin15AnchoredAtom3581 Fin15AnchoredAtom3610 Fin15AnchoredAtom3611
    Fin15AnchoredAtom3617 Fin15AnchoredAtom3697 Fin15AnchoredAtom3730 Fin15AnchoredAtom3731
    Fin15AnchoredAtom3737 Fin15AnchoredAtom3817 Fin15AnchoredAtom3901 Fin15AnchoredAtom4060
    Fin15AnchoredAtom4061 Fin15AnchoredAtom4067 Fin15AnchoredAtom4147 Fin15AnchoredAtom4231
    Fin15AnchoredAtom4441 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31155 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom2159 chi ∧
      ¬Fin15AnchoredAtom2160 chi ∧
      ¬Fin15AnchoredAtom2161 chi ∧
      ¬Fin15AnchoredAtom2168 chi ∧
      ¬Fin15AnchoredAtom2169 chi ∧
      ¬Fin15AnchoredAtom2170 chi ∧
      ¬Fin15AnchoredAtom2204 chi ∧
      ¬Fin15AnchoredAtom2205 chi ∧
      ¬Fin15AnchoredAtom2206 chi ∧
      ¬Fin15AnchoredAtom2240 chi ∧
      ¬Fin15AnchoredAtom2241 chi ∧
      ¬Fin15AnchoredAtom2242 chi ∧
      ¬Fin15AnchoredAtom2326 chi ∧
      ¬Fin15AnchoredAtom2333 chi ∧
      ¬Fin15AnchoredAtom2334 chi ∧
      ¬Fin15AnchoredAtom2335 chi ∧
      ¬Fin15AnchoredAtom2369 chi ∧
      ¬Fin15AnchoredAtom2370 chi ∧
      ¬Fin15AnchoredAtom2371 chi ∧
      ¬Fin15AnchoredAtom2405 chi ∧
      ¬Fin15AnchoredAtom2406 chi ∧
      ¬Fin15AnchoredAtom2407 chi ∧
      ¬Fin15AnchoredAtom2491 chi ∧
      ¬Fin15AnchoredAtom2525 chi ∧
      ¬Fin15AnchoredAtom2526 chi ∧
      ¬Fin15AnchoredAtom2527 chi ∧
      ¬Fin15AnchoredAtom2611 chi ∧
      ¬Fin15AnchoredAtom2695 chi ∧
      ¬Fin15AnchoredAtom3543 chi ∧
      ¬Fin15AnchoredAtom3544 chi ∧
      ¬Fin15AnchoredAtom3545 chi ∧
      ¬Fin15AnchoredAtom3579 chi ∧
      ¬Fin15AnchoredAtom3580 chi ∧
      ¬Fin15AnchoredAtom3581 chi ∧
      ¬Fin15AnchoredAtom3615 chi ∧
      ¬Fin15AnchoredAtom3616 chi ∧
      ¬Fin15AnchoredAtom3617 chi ∧
      ¬Fin15AnchoredAtom3701 chi ∧
      ¬Fin15AnchoredAtom3735 chi ∧
      ¬Fin15AnchoredAtom3736 chi ∧
      ¬Fin15AnchoredAtom3737 chi ∧
      ¬Fin15AnchoredAtom3821 chi ∧
      ¬Fin15AnchoredAtom3905 chi ∧
      ¬Fin15AnchoredAtom4065 chi ∧
      ¬Fin15AnchoredAtom4066 chi ∧
      ¬Fin15AnchoredAtom4067 chi ∧
      ¬Fin15AnchoredAtom4151 chi ∧
      ¬Fin15AnchoredAtom4235 chi ∧
      ¬Fin15AnchoredAtom4445 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 5, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask28733
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2107 Fin15AnchoredAtom2114 Fin15AnchoredAtom2115
    Fin15AnchoredAtom2116 Fin15AnchoredAtom2123 Fin15AnchoredAtom2124 Fin15AnchoredAtom2125
    Fin15AnchoredAtom2159 Fin15AnchoredAtom2160 Fin15AnchoredAtom2161 Fin15AnchoredAtom2168
    Fin15AnchoredAtom2169 Fin15AnchoredAtom2170 Fin15AnchoredAtom2204 Fin15AnchoredAtom2205
    Fin15AnchoredAtom2206 Fin15AnchoredAtom2240 Fin15AnchoredAtom2241 Fin15AnchoredAtom2242
    Fin15AnchoredAtom2326 Fin15AnchoredAtom2333 Fin15AnchoredAtom2334 Fin15AnchoredAtom2335
    Fin15AnchoredAtom2369 Fin15AnchoredAtom2370 Fin15AnchoredAtom2371 Fin15AnchoredAtom2405
    Fin15AnchoredAtom2406 Fin15AnchoredAtom2407 Fin15AnchoredAtom2491 Fin15AnchoredAtom2525
    Fin15AnchoredAtom2526 Fin15AnchoredAtom2527 Fin15AnchoredAtom2611 Fin15AnchoredAtom2695
    Fin15AnchoredAtom3543 Fin15AnchoredAtom3544 Fin15AnchoredAtom3545 Fin15AnchoredAtom3579
    Fin15AnchoredAtom3580 Fin15AnchoredAtom3581 Fin15AnchoredAtom3615 Fin15AnchoredAtom3616
    Fin15AnchoredAtom3617 Fin15AnchoredAtom3701 Fin15AnchoredAtom3735 Fin15AnchoredAtom3736
    Fin15AnchoredAtom3737 Fin15AnchoredAtom3821 Fin15AnchoredAtom3905 Fin15AnchoredAtom4065
    Fin15AnchoredAtom4066 Fin15AnchoredAtom4067 Fin15AnchoredAtom4151 Fin15AnchoredAtom4235
    Fin15AnchoredAtom4445 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31156 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2126 chi ∧
      ¬Fin15AnchoredAtom2128 chi ∧
      ¬Fin15AnchoredAtom2129 chi ∧
      ¬Fin15AnchoredAtom2135 chi ∧
      ¬Fin15AnchoredAtom2136 chi ∧
      ¬Fin15AnchoredAtom2147 chi ∧
      ¬Fin15AnchoredAtom2171 chi ∧
      ¬Fin15AnchoredAtom2173 chi ∧
      ¬Fin15AnchoredAtom2174 chi ∧
      ¬Fin15AnchoredAtom2180 chi ∧
      ¬Fin15AnchoredAtom2181 chi ∧
      ¬Fin15AnchoredAtom2192 chi ∧
      ¬Fin15AnchoredAtom2244 chi ∧
      ¬Fin15AnchoredAtom2245 chi ∧
      ¬Fin15AnchoredAtom2256 chi ∧
      ¬Fin15AnchoredAtom2277 chi ∧
      ¬Fin15AnchoredAtom2336 chi ∧
      ¬Fin15AnchoredAtom2338 chi ∧
      ¬Fin15AnchoredAtom2339 chi ∧
      ¬Fin15AnchoredAtom2345 chi ∧
      ¬Fin15AnchoredAtom2346 chi ∧
      ¬Fin15AnchoredAtom2357 chi ∧
      ¬Fin15AnchoredAtom2409 chi ∧
      ¬Fin15AnchoredAtom2410 chi ∧
      ¬Fin15AnchoredAtom2421 chi ∧
      ¬Fin15AnchoredAtom2442 chi ∧
      ¬Fin15AnchoredAtom2529 chi ∧
      ¬Fin15AnchoredAtom2530 chi ∧
      ¬Fin15AnchoredAtom2541 chi ∧
      ¬Fin15AnchoredAtom2562 chi ∧
      ¬Fin15AnchoredAtom2702 chi ∧
      ¬Fin15AnchoredAtom3546 chi ∧
      ¬Fin15AnchoredAtom3548 chi ∧
      ¬Fin15AnchoredAtom3549 chi ∧
      ¬Fin15AnchoredAtom3555 chi ∧
      ¬Fin15AnchoredAtom3556 chi ∧
      ¬Fin15AnchoredAtom3567 chi ∧
      ¬Fin15AnchoredAtom3619 chi ∧
      ¬Fin15AnchoredAtom3620 chi ∧
      ¬Fin15AnchoredAtom3631 chi ∧
      ¬Fin15AnchoredAtom3652 chi ∧
      ¬Fin15AnchoredAtom3739 chi ∧
      ¬Fin15AnchoredAtom3740 chi ∧
      ¬Fin15AnchoredAtom3751 chi ∧
      ¬Fin15AnchoredAtom3772 chi ∧
      ¬Fin15AnchoredAtom3912 chi ∧
      ¬Fin15AnchoredAtom4069 chi ∧
      ¬Fin15AnchoredAtom4070 chi ∧
      ¬Fin15AnchoredAtom4081 chi ∧
      ¬Fin15AnchoredAtom4102 chi ∧
      ¬Fin15AnchoredAtom4242 chi ∧
      ¬Fin15AnchoredAtom4452 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 6, 7, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask01757
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2108 Fin15AnchoredAtom2109 Fin15AnchoredAtom2111
    Fin15AnchoredAtom2112 Fin15AnchoredAtom2126 Fin15AnchoredAtom2128 Fin15AnchoredAtom2129
    Fin15AnchoredAtom2135 Fin15AnchoredAtom2136 Fin15AnchoredAtom2147 Fin15AnchoredAtom2171
    Fin15AnchoredAtom2173 Fin15AnchoredAtom2174 Fin15AnchoredAtom2180 Fin15AnchoredAtom2181
    Fin15AnchoredAtom2192 Fin15AnchoredAtom2244 Fin15AnchoredAtom2245 Fin15AnchoredAtom2256
    Fin15AnchoredAtom2277 Fin15AnchoredAtom2336 Fin15AnchoredAtom2338 Fin15AnchoredAtom2339
    Fin15AnchoredAtom2345 Fin15AnchoredAtom2346 Fin15AnchoredAtom2357 Fin15AnchoredAtom2409
    Fin15AnchoredAtom2410 Fin15AnchoredAtom2421 Fin15AnchoredAtom2442 Fin15AnchoredAtom2529
    Fin15AnchoredAtom2530 Fin15AnchoredAtom2541 Fin15AnchoredAtom2562 Fin15AnchoredAtom2702
    Fin15AnchoredAtom3546 Fin15AnchoredAtom3548 Fin15AnchoredAtom3549 Fin15AnchoredAtom3555
    Fin15AnchoredAtom3556 Fin15AnchoredAtom3567 Fin15AnchoredAtom3619 Fin15AnchoredAtom3620
    Fin15AnchoredAtom3631 Fin15AnchoredAtom3652 Fin15AnchoredAtom3739 Fin15AnchoredAtom3740
    Fin15AnchoredAtom3751 Fin15AnchoredAtom3772 Fin15AnchoredAtom3912 Fin15AnchoredAtom4069
    Fin15AnchoredAtom4070 Fin15AnchoredAtom4081 Fin15AnchoredAtom4102 Fin15AnchoredAtom4242
    Fin15AnchoredAtom4452 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31157 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2126 chi ∧
      ¬Fin15AnchoredAtom2128 chi ∧
      ¬Fin15AnchoredAtom2131 chi ∧
      ¬Fin15AnchoredAtom2135 chi ∧
      ¬Fin15AnchoredAtom2138 chi ∧
      ¬Fin15AnchoredAtom2149 chi ∧
      ¬Fin15AnchoredAtom2171 chi ∧
      ¬Fin15AnchoredAtom2173 chi ∧
      ¬Fin15AnchoredAtom2176 chi ∧
      ¬Fin15AnchoredAtom2180 chi ∧
      ¬Fin15AnchoredAtom2183 chi ∧
      ¬Fin15AnchoredAtom2194 chi ∧
      ¬Fin15AnchoredAtom2244 chi ∧
      ¬Fin15AnchoredAtom2247 chi ∧
      ¬Fin15AnchoredAtom2258 chi ∧
      ¬Fin15AnchoredAtom2279 chi ∧
      ¬Fin15AnchoredAtom2336 chi ∧
      ¬Fin15AnchoredAtom2338 chi ∧
      ¬Fin15AnchoredAtom2341 chi ∧
      ¬Fin15AnchoredAtom2345 chi ∧
      ¬Fin15AnchoredAtom2348 chi ∧
      ¬Fin15AnchoredAtom2359 chi ∧
      ¬Fin15AnchoredAtom2409 chi ∧
      ¬Fin15AnchoredAtom2412 chi ∧
      ¬Fin15AnchoredAtom2423 chi ∧
      ¬Fin15AnchoredAtom2444 chi ∧
      ¬Fin15AnchoredAtom2529 chi ∧
      ¬Fin15AnchoredAtom2532 chi ∧
      ¬Fin15AnchoredAtom2543 chi ∧
      ¬Fin15AnchoredAtom2564 chi ∧
      ¬Fin15AnchoredAtom2704 chi ∧
      ¬Fin15AnchoredAtom3546 chi ∧
      ¬Fin15AnchoredAtom3548 chi ∧
      ¬Fin15AnchoredAtom3551 chi ∧
      ¬Fin15AnchoredAtom3555 chi ∧
      ¬Fin15AnchoredAtom3558 chi ∧
      ¬Fin15AnchoredAtom3569 chi ∧
      ¬Fin15AnchoredAtom3619 chi ∧
      ¬Fin15AnchoredAtom3622 chi ∧
      ¬Fin15AnchoredAtom3633 chi ∧
      ¬Fin15AnchoredAtom3654 chi ∧
      ¬Fin15AnchoredAtom3739 chi ∧
      ¬Fin15AnchoredAtom3742 chi ∧
      ¬Fin15AnchoredAtom3753 chi ∧
      ¬Fin15AnchoredAtom3774 chi ∧
      ¬Fin15AnchoredAtom3914 chi ∧
      ¬Fin15AnchoredAtom4069 chi ∧
      ¬Fin15AnchoredAtom4072 chi ∧
      ¬Fin15AnchoredAtom4083 chi ∧
      ¬Fin15AnchoredAtom4104 chi ∧
      ¬Fin15AnchoredAtom4244 chi ∧
      ¬Fin15AnchoredAtom4454 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 6, 7, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask04829
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2108 Fin15AnchoredAtom2109 Fin15AnchoredAtom2111
    Fin15AnchoredAtom2114 Fin15AnchoredAtom2126 Fin15AnchoredAtom2128 Fin15AnchoredAtom2131
    Fin15AnchoredAtom2135 Fin15AnchoredAtom2138 Fin15AnchoredAtom2149 Fin15AnchoredAtom2171
    Fin15AnchoredAtom2173 Fin15AnchoredAtom2176 Fin15AnchoredAtom2180 Fin15AnchoredAtom2183
    Fin15AnchoredAtom2194 Fin15AnchoredAtom2244 Fin15AnchoredAtom2247 Fin15AnchoredAtom2258
    Fin15AnchoredAtom2279 Fin15AnchoredAtom2336 Fin15AnchoredAtom2338 Fin15AnchoredAtom2341
    Fin15AnchoredAtom2345 Fin15AnchoredAtom2348 Fin15AnchoredAtom2359 Fin15AnchoredAtom2409
    Fin15AnchoredAtom2412 Fin15AnchoredAtom2423 Fin15AnchoredAtom2444 Fin15AnchoredAtom2529
    Fin15AnchoredAtom2532 Fin15AnchoredAtom2543 Fin15AnchoredAtom2564 Fin15AnchoredAtom2704
    Fin15AnchoredAtom3546 Fin15AnchoredAtom3548 Fin15AnchoredAtom3551 Fin15AnchoredAtom3555
    Fin15AnchoredAtom3558 Fin15AnchoredAtom3569 Fin15AnchoredAtom3619 Fin15AnchoredAtom3622
    Fin15AnchoredAtom3633 Fin15AnchoredAtom3654 Fin15AnchoredAtom3739 Fin15AnchoredAtom3742
    Fin15AnchoredAtom3753 Fin15AnchoredAtom3774 Fin15AnchoredAtom3914 Fin15AnchoredAtom4069
    Fin15AnchoredAtom4072 Fin15AnchoredAtom4083 Fin15AnchoredAtom4104 Fin15AnchoredAtom4244
    Fin15AnchoredAtom4454 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31158 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2126 chi ∧
      ¬Fin15AnchoredAtom2128 chi ∧
      ¬Fin15AnchoredAtom2132 chi ∧
      ¬Fin15AnchoredAtom2135 chi ∧
      ¬Fin15AnchoredAtom2139 chi ∧
      ¬Fin15AnchoredAtom2150 chi ∧
      ¬Fin15AnchoredAtom2171 chi ∧
      ¬Fin15AnchoredAtom2173 chi ∧
      ¬Fin15AnchoredAtom2177 chi ∧
      ¬Fin15AnchoredAtom2180 chi ∧
      ¬Fin15AnchoredAtom2184 chi ∧
      ¬Fin15AnchoredAtom2195 chi ∧
      ¬Fin15AnchoredAtom2244 chi ∧
      ¬Fin15AnchoredAtom2248 chi ∧
      ¬Fin15AnchoredAtom2259 chi ∧
      ¬Fin15AnchoredAtom2280 chi ∧
      ¬Fin15AnchoredAtom2336 chi ∧
      ¬Fin15AnchoredAtom2338 chi ∧
      ¬Fin15AnchoredAtom2342 chi ∧
      ¬Fin15AnchoredAtom2345 chi ∧
      ¬Fin15AnchoredAtom2349 chi ∧
      ¬Fin15AnchoredAtom2360 chi ∧
      ¬Fin15AnchoredAtom2409 chi ∧
      ¬Fin15AnchoredAtom2413 chi ∧
      ¬Fin15AnchoredAtom2424 chi ∧
      ¬Fin15AnchoredAtom2445 chi ∧
      ¬Fin15AnchoredAtom2529 chi ∧
      ¬Fin15AnchoredAtom2533 chi ∧
      ¬Fin15AnchoredAtom2544 chi ∧
      ¬Fin15AnchoredAtom2565 chi ∧
      ¬Fin15AnchoredAtom2705 chi ∧
      ¬Fin15AnchoredAtom3546 chi ∧
      ¬Fin15AnchoredAtom3548 chi ∧
      ¬Fin15AnchoredAtom3552 chi ∧
      ¬Fin15AnchoredAtom3555 chi ∧
      ¬Fin15AnchoredAtom3559 chi ∧
      ¬Fin15AnchoredAtom3570 chi ∧
      ¬Fin15AnchoredAtom3619 chi ∧
      ¬Fin15AnchoredAtom3623 chi ∧
      ¬Fin15AnchoredAtom3634 chi ∧
      ¬Fin15AnchoredAtom3655 chi ∧
      ¬Fin15AnchoredAtom3739 chi ∧
      ¬Fin15AnchoredAtom3743 chi ∧
      ¬Fin15AnchoredAtom3754 chi ∧
      ¬Fin15AnchoredAtom3775 chi ∧
      ¬Fin15AnchoredAtom3915 chi ∧
      ¬Fin15AnchoredAtom4069 chi ∧
      ¬Fin15AnchoredAtom4073 chi ∧
      ¬Fin15AnchoredAtom4084 chi ∧
      ¬Fin15AnchoredAtom4105 chi ∧
      ¬Fin15AnchoredAtom4245 chi ∧
      ¬Fin15AnchoredAtom4455 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 6, 7, 9, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask08925
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2108 Fin15AnchoredAtom2109 Fin15AnchoredAtom2111
    Fin15AnchoredAtom2115 Fin15AnchoredAtom2126 Fin15AnchoredAtom2128 Fin15AnchoredAtom2132
    Fin15AnchoredAtom2135 Fin15AnchoredAtom2139 Fin15AnchoredAtom2150 Fin15AnchoredAtom2171
    Fin15AnchoredAtom2173 Fin15AnchoredAtom2177 Fin15AnchoredAtom2180 Fin15AnchoredAtom2184
    Fin15AnchoredAtom2195 Fin15AnchoredAtom2244 Fin15AnchoredAtom2248 Fin15AnchoredAtom2259
    Fin15AnchoredAtom2280 Fin15AnchoredAtom2336 Fin15AnchoredAtom2338 Fin15AnchoredAtom2342
    Fin15AnchoredAtom2345 Fin15AnchoredAtom2349 Fin15AnchoredAtom2360 Fin15AnchoredAtom2409
    Fin15AnchoredAtom2413 Fin15AnchoredAtom2424 Fin15AnchoredAtom2445 Fin15AnchoredAtom2529
    Fin15AnchoredAtom2533 Fin15AnchoredAtom2544 Fin15AnchoredAtom2565 Fin15AnchoredAtom2705
    Fin15AnchoredAtom3546 Fin15AnchoredAtom3548 Fin15AnchoredAtom3552 Fin15AnchoredAtom3555
    Fin15AnchoredAtom3559 Fin15AnchoredAtom3570 Fin15AnchoredAtom3619 Fin15AnchoredAtom3623
    Fin15AnchoredAtom3634 Fin15AnchoredAtom3655 Fin15AnchoredAtom3739 Fin15AnchoredAtom3743
    Fin15AnchoredAtom3754 Fin15AnchoredAtom3775 Fin15AnchoredAtom3915 Fin15AnchoredAtom4069
    Fin15AnchoredAtom4073 Fin15AnchoredAtom4084 Fin15AnchoredAtom4105 Fin15AnchoredAtom4245
    Fin15AnchoredAtom4455 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31159 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2126 chi ∧
      ¬Fin15AnchoredAtom2128 chi ∧
      ¬Fin15AnchoredAtom2133 chi ∧
      ¬Fin15AnchoredAtom2135 chi ∧
      ¬Fin15AnchoredAtom2140 chi ∧
      ¬Fin15AnchoredAtom2151 chi ∧
      ¬Fin15AnchoredAtom2171 chi ∧
      ¬Fin15AnchoredAtom2173 chi ∧
      ¬Fin15AnchoredAtom2178 chi ∧
      ¬Fin15AnchoredAtom2180 chi ∧
      ¬Fin15AnchoredAtom2185 chi ∧
      ¬Fin15AnchoredAtom2196 chi ∧
      ¬Fin15AnchoredAtom2244 chi ∧
      ¬Fin15AnchoredAtom2249 chi ∧
      ¬Fin15AnchoredAtom2260 chi ∧
      ¬Fin15AnchoredAtom2281 chi ∧
      ¬Fin15AnchoredAtom2336 chi ∧
      ¬Fin15AnchoredAtom2338 chi ∧
      ¬Fin15AnchoredAtom2343 chi ∧
      ¬Fin15AnchoredAtom2345 chi ∧
      ¬Fin15AnchoredAtom2350 chi ∧
      ¬Fin15AnchoredAtom2361 chi ∧
      ¬Fin15AnchoredAtom2409 chi ∧
      ¬Fin15AnchoredAtom2414 chi ∧
      ¬Fin15AnchoredAtom2425 chi ∧
      ¬Fin15AnchoredAtom2446 chi ∧
      ¬Fin15AnchoredAtom2529 chi ∧
      ¬Fin15AnchoredAtom2534 chi ∧
      ¬Fin15AnchoredAtom2545 chi ∧
      ¬Fin15AnchoredAtom2566 chi ∧
      ¬Fin15AnchoredAtom2706 chi ∧
      ¬Fin15AnchoredAtom3546 chi ∧
      ¬Fin15AnchoredAtom3548 chi ∧
      ¬Fin15AnchoredAtom3553 chi ∧
      ¬Fin15AnchoredAtom3555 chi ∧
      ¬Fin15AnchoredAtom3560 chi ∧
      ¬Fin15AnchoredAtom3571 chi ∧
      ¬Fin15AnchoredAtom3619 chi ∧
      ¬Fin15AnchoredAtom3624 chi ∧
      ¬Fin15AnchoredAtom3635 chi ∧
      ¬Fin15AnchoredAtom3656 chi ∧
      ¬Fin15AnchoredAtom3739 chi ∧
      ¬Fin15AnchoredAtom3744 chi ∧
      ¬Fin15AnchoredAtom3755 chi ∧
      ¬Fin15AnchoredAtom3776 chi ∧
      ¬Fin15AnchoredAtom3916 chi ∧
      ¬Fin15AnchoredAtom4069 chi ∧
      ¬Fin15AnchoredAtom4074 chi ∧
      ¬Fin15AnchoredAtom4085 chi ∧
      ¬Fin15AnchoredAtom4106 chi ∧
      ¬Fin15AnchoredAtom4246 chi ∧
      ¬Fin15AnchoredAtom4456 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 6, 7, 9, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17117
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2108 Fin15AnchoredAtom2109 Fin15AnchoredAtom2111
    Fin15AnchoredAtom2116 Fin15AnchoredAtom2126 Fin15AnchoredAtom2128 Fin15AnchoredAtom2133
    Fin15AnchoredAtom2135 Fin15AnchoredAtom2140 Fin15AnchoredAtom2151 Fin15AnchoredAtom2171
    Fin15AnchoredAtom2173 Fin15AnchoredAtom2178 Fin15AnchoredAtom2180 Fin15AnchoredAtom2185
    Fin15AnchoredAtom2196 Fin15AnchoredAtom2244 Fin15AnchoredAtom2249 Fin15AnchoredAtom2260
    Fin15AnchoredAtom2281 Fin15AnchoredAtom2336 Fin15AnchoredAtom2338 Fin15AnchoredAtom2343
    Fin15AnchoredAtom2345 Fin15AnchoredAtom2350 Fin15AnchoredAtom2361 Fin15AnchoredAtom2409
    Fin15AnchoredAtom2414 Fin15AnchoredAtom2425 Fin15AnchoredAtom2446 Fin15AnchoredAtom2529
    Fin15AnchoredAtom2534 Fin15AnchoredAtom2545 Fin15AnchoredAtom2566 Fin15AnchoredAtom2706
    Fin15AnchoredAtom3546 Fin15AnchoredAtom3548 Fin15AnchoredAtom3553 Fin15AnchoredAtom3555
    Fin15AnchoredAtom3560 Fin15AnchoredAtom3571 Fin15AnchoredAtom3619 Fin15AnchoredAtom3624
    Fin15AnchoredAtom3635 Fin15AnchoredAtom3656 Fin15AnchoredAtom3739 Fin15AnchoredAtom3744
    Fin15AnchoredAtom3755 Fin15AnchoredAtom3776 Fin15AnchoredAtom3916 Fin15AnchoredAtom4069
    Fin15AnchoredAtom4074 Fin15AnchoredAtom4085 Fin15AnchoredAtom4106 Fin15AnchoredAtom4246
    Fin15AnchoredAtom4456 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31160 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2126 chi ∧
      ¬Fin15AnchoredAtom2129 chi ∧
      ¬Fin15AnchoredAtom2131 chi ∧
      ¬Fin15AnchoredAtom2136 chi ∧
      ¬Fin15AnchoredAtom2138 chi ∧
      ¬Fin15AnchoredAtom2153 chi ∧
      ¬Fin15AnchoredAtom2171 chi ∧
      ¬Fin15AnchoredAtom2174 chi ∧
      ¬Fin15AnchoredAtom2176 chi ∧
      ¬Fin15AnchoredAtom2181 chi ∧
      ¬Fin15AnchoredAtom2183 chi ∧
      ¬Fin15AnchoredAtom2198 chi ∧
      ¬Fin15AnchoredAtom2245 chi ∧
      ¬Fin15AnchoredAtom2247 chi ∧
      ¬Fin15AnchoredAtom2262 chi ∧
      ¬Fin15AnchoredAtom2283 chi ∧
      ¬Fin15AnchoredAtom2336 chi ∧
      ¬Fin15AnchoredAtom2339 chi ∧
      ¬Fin15AnchoredAtom2341 chi ∧
      ¬Fin15AnchoredAtom2346 chi ∧
      ¬Fin15AnchoredAtom2348 chi ∧
      ¬Fin15AnchoredAtom2363 chi ∧
      ¬Fin15AnchoredAtom2410 chi ∧
      ¬Fin15AnchoredAtom2412 chi ∧
      ¬Fin15AnchoredAtom2427 chi ∧
      ¬Fin15AnchoredAtom2448 chi ∧
      ¬Fin15AnchoredAtom2530 chi ∧
      ¬Fin15AnchoredAtom2532 chi ∧
      ¬Fin15AnchoredAtom2547 chi ∧
      ¬Fin15AnchoredAtom2568 chi ∧
      ¬Fin15AnchoredAtom2708 chi ∧
      ¬Fin15AnchoredAtom3546 chi ∧
      ¬Fin15AnchoredAtom3549 chi ∧
      ¬Fin15AnchoredAtom3551 chi ∧
      ¬Fin15AnchoredAtom3556 chi ∧
      ¬Fin15AnchoredAtom3558 chi ∧
      ¬Fin15AnchoredAtom3573 chi ∧
      ¬Fin15AnchoredAtom3620 chi ∧
      ¬Fin15AnchoredAtom3622 chi ∧
      ¬Fin15AnchoredAtom3637 chi ∧
      ¬Fin15AnchoredAtom3658 chi ∧
      ¬Fin15AnchoredAtom3740 chi ∧
      ¬Fin15AnchoredAtom3742 chi ∧
      ¬Fin15AnchoredAtom3757 chi ∧
      ¬Fin15AnchoredAtom3778 chi ∧
      ¬Fin15AnchoredAtom3918 chi ∧
      ¬Fin15AnchoredAtom4070 chi ∧
      ¬Fin15AnchoredAtom4072 chi ∧
      ¬Fin15AnchoredAtom4087 chi ∧
      ¬Fin15AnchoredAtom4108 chi ∧
      ¬Fin15AnchoredAtom4248 chi ∧
      ¬Fin15AnchoredAtom4458 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 6, 7, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05341
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2108 Fin15AnchoredAtom2109 Fin15AnchoredAtom2112
    Fin15AnchoredAtom2114 Fin15AnchoredAtom2126 Fin15AnchoredAtom2129 Fin15AnchoredAtom2131
    Fin15AnchoredAtom2136 Fin15AnchoredAtom2138 Fin15AnchoredAtom2153 Fin15AnchoredAtom2171
    Fin15AnchoredAtom2174 Fin15AnchoredAtom2176 Fin15AnchoredAtom2181 Fin15AnchoredAtom2183
    Fin15AnchoredAtom2198 Fin15AnchoredAtom2245 Fin15AnchoredAtom2247 Fin15AnchoredAtom2262
    Fin15AnchoredAtom2283 Fin15AnchoredAtom2336 Fin15AnchoredAtom2339 Fin15AnchoredAtom2341
    Fin15AnchoredAtom2346 Fin15AnchoredAtom2348 Fin15AnchoredAtom2363 Fin15AnchoredAtom2410
    Fin15AnchoredAtom2412 Fin15AnchoredAtom2427 Fin15AnchoredAtom2448 Fin15AnchoredAtom2530
    Fin15AnchoredAtom2532 Fin15AnchoredAtom2547 Fin15AnchoredAtom2568 Fin15AnchoredAtom2708
    Fin15AnchoredAtom3546 Fin15AnchoredAtom3549 Fin15AnchoredAtom3551 Fin15AnchoredAtom3556
    Fin15AnchoredAtom3558 Fin15AnchoredAtom3573 Fin15AnchoredAtom3620 Fin15AnchoredAtom3622
    Fin15AnchoredAtom3637 Fin15AnchoredAtom3658 Fin15AnchoredAtom3740 Fin15AnchoredAtom3742
    Fin15AnchoredAtom3757 Fin15AnchoredAtom3778 Fin15AnchoredAtom3918 Fin15AnchoredAtom4070
    Fin15AnchoredAtom4072 Fin15AnchoredAtom4087 Fin15AnchoredAtom4108 Fin15AnchoredAtom4248
    Fin15AnchoredAtom4458 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31161 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2126 chi ∧
      ¬Fin15AnchoredAtom2129 chi ∧
      ¬Fin15AnchoredAtom2132 chi ∧
      ¬Fin15AnchoredAtom2136 chi ∧
      ¬Fin15AnchoredAtom2139 chi ∧
      ¬Fin15AnchoredAtom2154 chi ∧
      ¬Fin15AnchoredAtom2171 chi ∧
      ¬Fin15AnchoredAtom2174 chi ∧
      ¬Fin15AnchoredAtom2177 chi ∧
      ¬Fin15AnchoredAtom2181 chi ∧
      ¬Fin15AnchoredAtom2184 chi ∧
      ¬Fin15AnchoredAtom2199 chi ∧
      ¬Fin15AnchoredAtom2245 chi ∧
      ¬Fin15AnchoredAtom2248 chi ∧
      ¬Fin15AnchoredAtom2263 chi ∧
      ¬Fin15AnchoredAtom2284 chi ∧
      ¬Fin15AnchoredAtom2336 chi ∧
      ¬Fin15AnchoredAtom2339 chi ∧
      ¬Fin15AnchoredAtom2342 chi ∧
      ¬Fin15AnchoredAtom2346 chi ∧
      ¬Fin15AnchoredAtom2349 chi ∧
      ¬Fin15AnchoredAtom2364 chi ∧
      ¬Fin15AnchoredAtom2410 chi ∧
      ¬Fin15AnchoredAtom2413 chi ∧
      ¬Fin15AnchoredAtom2428 chi ∧
      ¬Fin15AnchoredAtom2449 chi ∧
      ¬Fin15AnchoredAtom2530 chi ∧
      ¬Fin15AnchoredAtom2533 chi ∧
      ¬Fin15AnchoredAtom2548 chi ∧
      ¬Fin15AnchoredAtom2569 chi ∧
      ¬Fin15AnchoredAtom2709 chi ∧
      ¬Fin15AnchoredAtom3546 chi ∧
      ¬Fin15AnchoredAtom3549 chi ∧
      ¬Fin15AnchoredAtom3552 chi ∧
      ¬Fin15AnchoredAtom3556 chi ∧
      ¬Fin15AnchoredAtom3559 chi ∧
      ¬Fin15AnchoredAtom3574 chi ∧
      ¬Fin15AnchoredAtom3620 chi ∧
      ¬Fin15AnchoredAtom3623 chi ∧
      ¬Fin15AnchoredAtom3638 chi ∧
      ¬Fin15AnchoredAtom3659 chi ∧
      ¬Fin15AnchoredAtom3740 chi ∧
      ¬Fin15AnchoredAtom3743 chi ∧
      ¬Fin15AnchoredAtom3758 chi ∧
      ¬Fin15AnchoredAtom3779 chi ∧
      ¬Fin15AnchoredAtom3919 chi ∧
      ¬Fin15AnchoredAtom4070 chi ∧
      ¬Fin15AnchoredAtom4073 chi ∧
      ¬Fin15AnchoredAtom4088 chi ∧
      ¬Fin15AnchoredAtom4109 chi ∧
      ¬Fin15AnchoredAtom4249 chi ∧
      ¬Fin15AnchoredAtom4459 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 6, 7, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09437
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2108 Fin15AnchoredAtom2109 Fin15AnchoredAtom2112
    Fin15AnchoredAtom2115 Fin15AnchoredAtom2126 Fin15AnchoredAtom2129 Fin15AnchoredAtom2132
    Fin15AnchoredAtom2136 Fin15AnchoredAtom2139 Fin15AnchoredAtom2154 Fin15AnchoredAtom2171
    Fin15AnchoredAtom2174 Fin15AnchoredAtom2177 Fin15AnchoredAtom2181 Fin15AnchoredAtom2184
    Fin15AnchoredAtom2199 Fin15AnchoredAtom2245 Fin15AnchoredAtom2248 Fin15AnchoredAtom2263
    Fin15AnchoredAtom2284 Fin15AnchoredAtom2336 Fin15AnchoredAtom2339 Fin15AnchoredAtom2342
    Fin15AnchoredAtom2346 Fin15AnchoredAtom2349 Fin15AnchoredAtom2364 Fin15AnchoredAtom2410
    Fin15AnchoredAtom2413 Fin15AnchoredAtom2428 Fin15AnchoredAtom2449 Fin15AnchoredAtom2530
    Fin15AnchoredAtom2533 Fin15AnchoredAtom2548 Fin15AnchoredAtom2569 Fin15AnchoredAtom2709
    Fin15AnchoredAtom3546 Fin15AnchoredAtom3549 Fin15AnchoredAtom3552 Fin15AnchoredAtom3556
    Fin15AnchoredAtom3559 Fin15AnchoredAtom3574 Fin15AnchoredAtom3620 Fin15AnchoredAtom3623
    Fin15AnchoredAtom3638 Fin15AnchoredAtom3659 Fin15AnchoredAtom3740 Fin15AnchoredAtom3743
    Fin15AnchoredAtom3758 Fin15AnchoredAtom3779 Fin15AnchoredAtom3919 Fin15AnchoredAtom4070
    Fin15AnchoredAtom4073 Fin15AnchoredAtom4088 Fin15AnchoredAtom4109 Fin15AnchoredAtom4249
    Fin15AnchoredAtom4459 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31162 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2126 chi ∧
      ¬Fin15AnchoredAtom2129 chi ∧
      ¬Fin15AnchoredAtom2133 chi ∧
      ¬Fin15AnchoredAtom2136 chi ∧
      ¬Fin15AnchoredAtom2140 chi ∧
      ¬Fin15AnchoredAtom2155 chi ∧
      ¬Fin15AnchoredAtom2171 chi ∧
      ¬Fin15AnchoredAtom2174 chi ∧
      ¬Fin15AnchoredAtom2178 chi ∧
      ¬Fin15AnchoredAtom2181 chi ∧
      ¬Fin15AnchoredAtom2185 chi ∧
      ¬Fin15AnchoredAtom2200 chi ∧
      ¬Fin15AnchoredAtom2245 chi ∧
      ¬Fin15AnchoredAtom2249 chi ∧
      ¬Fin15AnchoredAtom2264 chi ∧
      ¬Fin15AnchoredAtom2285 chi ∧
      ¬Fin15AnchoredAtom2336 chi ∧
      ¬Fin15AnchoredAtom2339 chi ∧
      ¬Fin15AnchoredAtom2343 chi ∧
      ¬Fin15AnchoredAtom2346 chi ∧
      ¬Fin15AnchoredAtom2350 chi ∧
      ¬Fin15AnchoredAtom2365 chi ∧
      ¬Fin15AnchoredAtom2410 chi ∧
      ¬Fin15AnchoredAtom2414 chi ∧
      ¬Fin15AnchoredAtom2429 chi ∧
      ¬Fin15AnchoredAtom2450 chi ∧
      ¬Fin15AnchoredAtom2530 chi ∧
      ¬Fin15AnchoredAtom2534 chi ∧
      ¬Fin15AnchoredAtom2549 chi ∧
      ¬Fin15AnchoredAtom2570 chi ∧
      ¬Fin15AnchoredAtom2710 chi ∧
      ¬Fin15AnchoredAtom3546 chi ∧
      ¬Fin15AnchoredAtom3549 chi ∧
      ¬Fin15AnchoredAtom3553 chi ∧
      ¬Fin15AnchoredAtom3556 chi ∧
      ¬Fin15AnchoredAtom3560 chi ∧
      ¬Fin15AnchoredAtom3575 chi ∧
      ¬Fin15AnchoredAtom3620 chi ∧
      ¬Fin15AnchoredAtom3624 chi ∧
      ¬Fin15AnchoredAtom3639 chi ∧
      ¬Fin15AnchoredAtom3660 chi ∧
      ¬Fin15AnchoredAtom3740 chi ∧
      ¬Fin15AnchoredAtom3744 chi ∧
      ¬Fin15AnchoredAtom3759 chi ∧
      ¬Fin15AnchoredAtom3780 chi ∧
      ¬Fin15AnchoredAtom3920 chi ∧
      ¬Fin15AnchoredAtom4070 chi ∧
      ¬Fin15AnchoredAtom4074 chi ∧
      ¬Fin15AnchoredAtom4089 chi ∧
      ¬Fin15AnchoredAtom4110 chi ∧
      ¬Fin15AnchoredAtom4250 chi ∧
      ¬Fin15AnchoredAtom4460 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 6, 7, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17629
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2108 Fin15AnchoredAtom2109 Fin15AnchoredAtom2112
    Fin15AnchoredAtom2116 Fin15AnchoredAtom2126 Fin15AnchoredAtom2129 Fin15AnchoredAtom2133
    Fin15AnchoredAtom2136 Fin15AnchoredAtom2140 Fin15AnchoredAtom2155 Fin15AnchoredAtom2171
    Fin15AnchoredAtom2174 Fin15AnchoredAtom2178 Fin15AnchoredAtom2181 Fin15AnchoredAtom2185
    Fin15AnchoredAtom2200 Fin15AnchoredAtom2245 Fin15AnchoredAtom2249 Fin15AnchoredAtom2264
    Fin15AnchoredAtom2285 Fin15AnchoredAtom2336 Fin15AnchoredAtom2339 Fin15AnchoredAtom2343
    Fin15AnchoredAtom2346 Fin15AnchoredAtom2350 Fin15AnchoredAtom2365 Fin15AnchoredAtom2410
    Fin15AnchoredAtom2414 Fin15AnchoredAtom2429 Fin15AnchoredAtom2450 Fin15AnchoredAtom2530
    Fin15AnchoredAtom2534 Fin15AnchoredAtom2549 Fin15AnchoredAtom2570 Fin15AnchoredAtom2710
    Fin15AnchoredAtom3546 Fin15AnchoredAtom3549 Fin15AnchoredAtom3553 Fin15AnchoredAtom3556
    Fin15AnchoredAtom3560 Fin15AnchoredAtom3575 Fin15AnchoredAtom3620 Fin15AnchoredAtom3624
    Fin15AnchoredAtom3639 Fin15AnchoredAtom3660 Fin15AnchoredAtom3740 Fin15AnchoredAtom3744
    Fin15AnchoredAtom3759 Fin15AnchoredAtom3780 Fin15AnchoredAtom3920 Fin15AnchoredAtom4070
    Fin15AnchoredAtom4074 Fin15AnchoredAtom4089 Fin15AnchoredAtom4110 Fin15AnchoredAtom4250
    Fin15AnchoredAtom4460 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31163 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2126 chi ∧
      ¬Fin15AnchoredAtom2131 chi ∧
      ¬Fin15AnchoredAtom2132 chi ∧
      ¬Fin15AnchoredAtom2138 chi ∧
      ¬Fin15AnchoredAtom2139 chi ∧
      ¬Fin15AnchoredAtom2159 chi ∧
      ¬Fin15AnchoredAtom2171 chi ∧
      ¬Fin15AnchoredAtom2176 chi ∧
      ¬Fin15AnchoredAtom2177 chi ∧
      ¬Fin15AnchoredAtom2183 chi ∧
      ¬Fin15AnchoredAtom2184 chi ∧
      ¬Fin15AnchoredAtom2204 chi ∧
      ¬Fin15AnchoredAtom2247 chi ∧
      ¬Fin15AnchoredAtom2248 chi ∧
      ¬Fin15AnchoredAtom2268 chi ∧
      ¬Fin15AnchoredAtom2289 chi ∧
      ¬Fin15AnchoredAtom2336 chi ∧
      ¬Fin15AnchoredAtom2341 chi ∧
      ¬Fin15AnchoredAtom2342 chi ∧
      ¬Fin15AnchoredAtom2348 chi ∧
      ¬Fin15AnchoredAtom2349 chi ∧
      ¬Fin15AnchoredAtom2369 chi ∧
      ¬Fin15AnchoredAtom2412 chi ∧
      ¬Fin15AnchoredAtom2413 chi ∧
      ¬Fin15AnchoredAtom2433 chi ∧
      ¬Fin15AnchoredAtom2454 chi ∧
      ¬Fin15AnchoredAtom2532 chi ∧
      ¬Fin15AnchoredAtom2533 chi ∧
      ¬Fin15AnchoredAtom2553 chi ∧
      ¬Fin15AnchoredAtom2574 chi ∧
      ¬Fin15AnchoredAtom2714 chi ∧
      ¬Fin15AnchoredAtom3546 chi ∧
      ¬Fin15AnchoredAtom3551 chi ∧
      ¬Fin15AnchoredAtom3552 chi ∧
      ¬Fin15AnchoredAtom3558 chi ∧
      ¬Fin15AnchoredAtom3559 chi ∧
      ¬Fin15AnchoredAtom3579 chi ∧
      ¬Fin15AnchoredAtom3622 chi ∧
      ¬Fin15AnchoredAtom3623 chi ∧
      ¬Fin15AnchoredAtom3643 chi ∧
      ¬Fin15AnchoredAtom3664 chi ∧
      ¬Fin15AnchoredAtom3742 chi ∧
      ¬Fin15AnchoredAtom3743 chi ∧
      ¬Fin15AnchoredAtom3763 chi ∧
      ¬Fin15AnchoredAtom3784 chi ∧
      ¬Fin15AnchoredAtom3924 chi ∧
      ¬Fin15AnchoredAtom4072 chi ∧
      ¬Fin15AnchoredAtom4073 chi ∧
      ¬Fin15AnchoredAtom4093 chi ∧
      ¬Fin15AnchoredAtom4114 chi ∧
      ¬Fin15AnchoredAtom4254 chi ∧
      ¬Fin15AnchoredAtom4464 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 6, 7, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask12509
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2108 Fin15AnchoredAtom2109 Fin15AnchoredAtom2114
    Fin15AnchoredAtom2115 Fin15AnchoredAtom2126 Fin15AnchoredAtom2131 Fin15AnchoredAtom2132
    Fin15AnchoredAtom2138 Fin15AnchoredAtom2139 Fin15AnchoredAtom2159 Fin15AnchoredAtom2171
    Fin15AnchoredAtom2176 Fin15AnchoredAtom2177 Fin15AnchoredAtom2183 Fin15AnchoredAtom2184
    Fin15AnchoredAtom2204 Fin15AnchoredAtom2247 Fin15AnchoredAtom2248 Fin15AnchoredAtom2268
    Fin15AnchoredAtom2289 Fin15AnchoredAtom2336 Fin15AnchoredAtom2341 Fin15AnchoredAtom2342
    Fin15AnchoredAtom2348 Fin15AnchoredAtom2349 Fin15AnchoredAtom2369 Fin15AnchoredAtom2412
    Fin15AnchoredAtom2413 Fin15AnchoredAtom2433 Fin15AnchoredAtom2454 Fin15AnchoredAtom2532
    Fin15AnchoredAtom2533 Fin15AnchoredAtom2553 Fin15AnchoredAtom2574 Fin15AnchoredAtom2714
    Fin15AnchoredAtom3546 Fin15AnchoredAtom3551 Fin15AnchoredAtom3552 Fin15AnchoredAtom3558
    Fin15AnchoredAtom3559 Fin15AnchoredAtom3579 Fin15AnchoredAtom3622 Fin15AnchoredAtom3623
    Fin15AnchoredAtom3643 Fin15AnchoredAtom3664 Fin15AnchoredAtom3742 Fin15AnchoredAtom3743
    Fin15AnchoredAtom3763 Fin15AnchoredAtom3784 Fin15AnchoredAtom3924 Fin15AnchoredAtom4072
    Fin15AnchoredAtom4073 Fin15AnchoredAtom4093 Fin15AnchoredAtom4114 Fin15AnchoredAtom4254
    Fin15AnchoredAtom4464 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31164 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2126 chi ∧
      ¬Fin15AnchoredAtom2131 chi ∧
      ¬Fin15AnchoredAtom2133 chi ∧
      ¬Fin15AnchoredAtom2138 chi ∧
      ¬Fin15AnchoredAtom2140 chi ∧
      ¬Fin15AnchoredAtom2160 chi ∧
      ¬Fin15AnchoredAtom2171 chi ∧
      ¬Fin15AnchoredAtom2176 chi ∧
      ¬Fin15AnchoredAtom2178 chi ∧
      ¬Fin15AnchoredAtom2183 chi ∧
      ¬Fin15AnchoredAtom2185 chi ∧
      ¬Fin15AnchoredAtom2205 chi ∧
      ¬Fin15AnchoredAtom2247 chi ∧
      ¬Fin15AnchoredAtom2249 chi ∧
      ¬Fin15AnchoredAtom2269 chi ∧
      ¬Fin15AnchoredAtom2290 chi ∧
      ¬Fin15AnchoredAtom2336 chi ∧
      ¬Fin15AnchoredAtom2341 chi ∧
      ¬Fin15AnchoredAtom2343 chi ∧
      ¬Fin15AnchoredAtom2348 chi ∧
      ¬Fin15AnchoredAtom2350 chi ∧
      ¬Fin15AnchoredAtom2370 chi ∧
      ¬Fin15AnchoredAtom2412 chi ∧
      ¬Fin15AnchoredAtom2414 chi ∧
      ¬Fin15AnchoredAtom2434 chi ∧
      ¬Fin15AnchoredAtom2455 chi ∧
      ¬Fin15AnchoredAtom2532 chi ∧
      ¬Fin15AnchoredAtom2534 chi ∧
      ¬Fin15AnchoredAtom2554 chi ∧
      ¬Fin15AnchoredAtom2575 chi ∧
      ¬Fin15AnchoredAtom2715 chi ∧
      ¬Fin15AnchoredAtom3546 chi ∧
      ¬Fin15AnchoredAtom3551 chi ∧
      ¬Fin15AnchoredAtom3553 chi ∧
      ¬Fin15AnchoredAtom3558 chi ∧
      ¬Fin15AnchoredAtom3560 chi ∧
      ¬Fin15AnchoredAtom3580 chi ∧
      ¬Fin15AnchoredAtom3622 chi ∧
      ¬Fin15AnchoredAtom3624 chi ∧
      ¬Fin15AnchoredAtom3644 chi ∧
      ¬Fin15AnchoredAtom3665 chi ∧
      ¬Fin15AnchoredAtom3742 chi ∧
      ¬Fin15AnchoredAtom3744 chi ∧
      ¬Fin15AnchoredAtom3764 chi ∧
      ¬Fin15AnchoredAtom3785 chi ∧
      ¬Fin15AnchoredAtom3925 chi ∧
      ¬Fin15AnchoredAtom4072 chi ∧
      ¬Fin15AnchoredAtom4074 chi ∧
      ¬Fin15AnchoredAtom4094 chi ∧
      ¬Fin15AnchoredAtom4115 chi ∧
      ¬Fin15AnchoredAtom4255 chi ∧
      ¬Fin15AnchoredAtom4465 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 6, 7, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask20701
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2108 Fin15AnchoredAtom2109 Fin15AnchoredAtom2114
    Fin15AnchoredAtom2116 Fin15AnchoredAtom2126 Fin15AnchoredAtom2131 Fin15AnchoredAtom2133
    Fin15AnchoredAtom2138 Fin15AnchoredAtom2140 Fin15AnchoredAtom2160 Fin15AnchoredAtom2171
    Fin15AnchoredAtom2176 Fin15AnchoredAtom2178 Fin15AnchoredAtom2183 Fin15AnchoredAtom2185
    Fin15AnchoredAtom2205 Fin15AnchoredAtom2247 Fin15AnchoredAtom2249 Fin15AnchoredAtom2269
    Fin15AnchoredAtom2290 Fin15AnchoredAtom2336 Fin15AnchoredAtom2341 Fin15AnchoredAtom2343
    Fin15AnchoredAtom2348 Fin15AnchoredAtom2350 Fin15AnchoredAtom2370 Fin15AnchoredAtom2412
    Fin15AnchoredAtom2414 Fin15AnchoredAtom2434 Fin15AnchoredAtom2455 Fin15AnchoredAtom2532
    Fin15AnchoredAtom2534 Fin15AnchoredAtom2554 Fin15AnchoredAtom2575 Fin15AnchoredAtom2715
    Fin15AnchoredAtom3546 Fin15AnchoredAtom3551 Fin15AnchoredAtom3553 Fin15AnchoredAtom3558
    Fin15AnchoredAtom3560 Fin15AnchoredAtom3580 Fin15AnchoredAtom3622 Fin15AnchoredAtom3624
    Fin15AnchoredAtom3644 Fin15AnchoredAtom3665 Fin15AnchoredAtom3742 Fin15AnchoredAtom3744
    Fin15AnchoredAtom3764 Fin15AnchoredAtom3785 Fin15AnchoredAtom3925 Fin15AnchoredAtom4072
    Fin15AnchoredAtom4074 Fin15AnchoredAtom4094 Fin15AnchoredAtom4115 Fin15AnchoredAtom4255
    Fin15AnchoredAtom4465 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31165 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2126 chi ∧
      ¬Fin15AnchoredAtom2132 chi ∧
      ¬Fin15AnchoredAtom2133 chi ∧
      ¬Fin15AnchoredAtom2139 chi ∧
      ¬Fin15AnchoredAtom2140 chi ∧
      ¬Fin15AnchoredAtom2161 chi ∧
      ¬Fin15AnchoredAtom2171 chi ∧
      ¬Fin15AnchoredAtom2177 chi ∧
      ¬Fin15AnchoredAtom2178 chi ∧
      ¬Fin15AnchoredAtom2184 chi ∧
      ¬Fin15AnchoredAtom2185 chi ∧
      ¬Fin15AnchoredAtom2206 chi ∧
      ¬Fin15AnchoredAtom2248 chi ∧
      ¬Fin15AnchoredAtom2249 chi ∧
      ¬Fin15AnchoredAtom2270 chi ∧
      ¬Fin15AnchoredAtom2291 chi ∧
      ¬Fin15AnchoredAtom2336 chi ∧
      ¬Fin15AnchoredAtom2342 chi ∧
      ¬Fin15AnchoredAtom2343 chi ∧
      ¬Fin15AnchoredAtom2349 chi ∧
      ¬Fin15AnchoredAtom2350 chi ∧
      ¬Fin15AnchoredAtom2371 chi ∧
      ¬Fin15AnchoredAtom2413 chi ∧
      ¬Fin15AnchoredAtom2414 chi ∧
      ¬Fin15AnchoredAtom2435 chi ∧
      ¬Fin15AnchoredAtom2456 chi ∧
      ¬Fin15AnchoredAtom2533 chi ∧
      ¬Fin15AnchoredAtom2534 chi ∧
      ¬Fin15AnchoredAtom2555 chi ∧
      ¬Fin15AnchoredAtom2576 chi ∧
      ¬Fin15AnchoredAtom2716 chi ∧
      ¬Fin15AnchoredAtom3546 chi ∧
      ¬Fin15AnchoredAtom3552 chi ∧
      ¬Fin15AnchoredAtom3553 chi ∧
      ¬Fin15AnchoredAtom3559 chi ∧
      ¬Fin15AnchoredAtom3560 chi ∧
      ¬Fin15AnchoredAtom3581 chi ∧
      ¬Fin15AnchoredAtom3623 chi ∧
      ¬Fin15AnchoredAtom3624 chi ∧
      ¬Fin15AnchoredAtom3645 chi ∧
      ¬Fin15AnchoredAtom3666 chi ∧
      ¬Fin15AnchoredAtom3743 chi ∧
      ¬Fin15AnchoredAtom3744 chi ∧
      ¬Fin15AnchoredAtom3765 chi ∧
      ¬Fin15AnchoredAtom3786 chi ∧
      ¬Fin15AnchoredAtom3926 chi ∧
      ¬Fin15AnchoredAtom4073 chi ∧
      ¬Fin15AnchoredAtom4074 chi ∧
      ¬Fin15AnchoredAtom4095 chi ∧
      ¬Fin15AnchoredAtom4116 chi ∧
      ¬Fin15AnchoredAtom4256 chi ∧
      ¬Fin15AnchoredAtom4466 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 6, 7, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask24797
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2108 Fin15AnchoredAtom2109 Fin15AnchoredAtom2115
    Fin15AnchoredAtom2116 Fin15AnchoredAtom2126 Fin15AnchoredAtom2132 Fin15AnchoredAtom2133
    Fin15AnchoredAtom2139 Fin15AnchoredAtom2140 Fin15AnchoredAtom2161 Fin15AnchoredAtom2171
    Fin15AnchoredAtom2177 Fin15AnchoredAtom2178 Fin15AnchoredAtom2184 Fin15AnchoredAtom2185
    Fin15AnchoredAtom2206 Fin15AnchoredAtom2248 Fin15AnchoredAtom2249 Fin15AnchoredAtom2270
    Fin15AnchoredAtom2291 Fin15AnchoredAtom2336 Fin15AnchoredAtom2342 Fin15AnchoredAtom2343
    Fin15AnchoredAtom2349 Fin15AnchoredAtom2350 Fin15AnchoredAtom2371 Fin15AnchoredAtom2413
    Fin15AnchoredAtom2414 Fin15AnchoredAtom2435 Fin15AnchoredAtom2456 Fin15AnchoredAtom2533
    Fin15AnchoredAtom2534 Fin15AnchoredAtom2555 Fin15AnchoredAtom2576 Fin15AnchoredAtom2716
    Fin15AnchoredAtom3546 Fin15AnchoredAtom3552 Fin15AnchoredAtom3553 Fin15AnchoredAtom3559
    Fin15AnchoredAtom3560 Fin15AnchoredAtom3581 Fin15AnchoredAtom3623 Fin15AnchoredAtom3624
    Fin15AnchoredAtom3645 Fin15AnchoredAtom3666 Fin15AnchoredAtom3743 Fin15AnchoredAtom3744
    Fin15AnchoredAtom3765 Fin15AnchoredAtom3786 Fin15AnchoredAtom3926 Fin15AnchoredAtom4073
    Fin15AnchoredAtom4074 Fin15AnchoredAtom4095 Fin15AnchoredAtom4116 Fin15AnchoredAtom4256
    Fin15AnchoredAtom4466 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31166 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2128 chi ∧
      ¬Fin15AnchoredAtom2129 chi ∧
      ¬Fin15AnchoredAtom2131 chi ∧
      ¬Fin15AnchoredAtom2147 chi ∧
      ¬Fin15AnchoredAtom2149 chi ∧
      ¬Fin15AnchoredAtom2153 chi ∧
      ¬Fin15AnchoredAtom2173 chi ∧
      ¬Fin15AnchoredAtom2174 chi ∧
      ¬Fin15AnchoredAtom2176 chi ∧
      ¬Fin15AnchoredAtom2192 chi ∧
      ¬Fin15AnchoredAtom2194 chi ∧
      ¬Fin15AnchoredAtom2198 chi ∧
      ¬Fin15AnchoredAtom2256 chi ∧
      ¬Fin15AnchoredAtom2258 chi ∧
      ¬Fin15AnchoredAtom2262 chi ∧
      ¬Fin15AnchoredAtom2308 chi ∧
      ¬Fin15AnchoredAtom2338 chi ∧
      ¬Fin15AnchoredAtom2339 chi ∧
      ¬Fin15AnchoredAtom2341 chi ∧
      ¬Fin15AnchoredAtom2357 chi ∧
      ¬Fin15AnchoredAtom2359 chi ∧
      ¬Fin15AnchoredAtom2363 chi ∧
      ¬Fin15AnchoredAtom2421 chi ∧
      ¬Fin15AnchoredAtom2423 chi ∧
      ¬Fin15AnchoredAtom2427 chi ∧
      ¬Fin15AnchoredAtom2473 chi ∧
      ¬Fin15AnchoredAtom2541 chi ∧
      ¬Fin15AnchoredAtom2543 chi ∧
      ¬Fin15AnchoredAtom2547 chi ∧
      ¬Fin15AnchoredAtom2593 chi ∧
      ¬Fin15AnchoredAtom2733 chi ∧
      ¬Fin15AnchoredAtom3548 chi ∧
      ¬Fin15AnchoredAtom3549 chi ∧
      ¬Fin15AnchoredAtom3551 chi ∧
      ¬Fin15AnchoredAtom3567 chi ∧
      ¬Fin15AnchoredAtom3569 chi ∧
      ¬Fin15AnchoredAtom3573 chi ∧
      ¬Fin15AnchoredAtom3631 chi ∧
      ¬Fin15AnchoredAtom3633 chi ∧
      ¬Fin15AnchoredAtom3637 chi ∧
      ¬Fin15AnchoredAtom3683 chi ∧
      ¬Fin15AnchoredAtom3751 chi ∧
      ¬Fin15AnchoredAtom3753 chi ∧
      ¬Fin15AnchoredAtom3757 chi ∧
      ¬Fin15AnchoredAtom3803 chi ∧
      ¬Fin15AnchoredAtom3943 chi ∧
      ¬Fin15AnchoredAtom4081 chi ∧
      ¬Fin15AnchoredAtom4083 chi ∧
      ¬Fin15AnchoredAtom4087 chi ∧
      ¬Fin15AnchoredAtom4133 chi ∧
      ¬Fin15AnchoredAtom4273 chi ∧
      ¬Fin15AnchoredAtom4483 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 6, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05725
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2108 Fin15AnchoredAtom2111 Fin15AnchoredAtom2112
    Fin15AnchoredAtom2114 Fin15AnchoredAtom2128 Fin15AnchoredAtom2129 Fin15AnchoredAtom2131
    Fin15AnchoredAtom2147 Fin15AnchoredAtom2149 Fin15AnchoredAtom2153 Fin15AnchoredAtom2173
    Fin15AnchoredAtom2174 Fin15AnchoredAtom2176 Fin15AnchoredAtom2192 Fin15AnchoredAtom2194
    Fin15AnchoredAtom2198 Fin15AnchoredAtom2256 Fin15AnchoredAtom2258 Fin15AnchoredAtom2262
    Fin15AnchoredAtom2308 Fin15AnchoredAtom2338 Fin15AnchoredAtom2339 Fin15AnchoredAtom2341
    Fin15AnchoredAtom2357 Fin15AnchoredAtom2359 Fin15AnchoredAtom2363 Fin15AnchoredAtom2421
    Fin15AnchoredAtom2423 Fin15AnchoredAtom2427 Fin15AnchoredAtom2473 Fin15AnchoredAtom2541
    Fin15AnchoredAtom2543 Fin15AnchoredAtom2547 Fin15AnchoredAtom2593 Fin15AnchoredAtom2733
    Fin15AnchoredAtom3548 Fin15AnchoredAtom3549 Fin15AnchoredAtom3551 Fin15AnchoredAtom3567
    Fin15AnchoredAtom3569 Fin15AnchoredAtom3573 Fin15AnchoredAtom3631 Fin15AnchoredAtom3633
    Fin15AnchoredAtom3637 Fin15AnchoredAtom3683 Fin15AnchoredAtom3751 Fin15AnchoredAtom3753
    Fin15AnchoredAtom3757 Fin15AnchoredAtom3803 Fin15AnchoredAtom3943 Fin15AnchoredAtom4081
    Fin15AnchoredAtom4083 Fin15AnchoredAtom4087 Fin15AnchoredAtom4133 Fin15AnchoredAtom4273
    Fin15AnchoredAtom4483 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31167 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2128 chi ∧
      ¬Fin15AnchoredAtom2129 chi ∧
      ¬Fin15AnchoredAtom2132 chi ∧
      ¬Fin15AnchoredAtom2147 chi ∧
      ¬Fin15AnchoredAtom2150 chi ∧
      ¬Fin15AnchoredAtom2154 chi ∧
      ¬Fin15AnchoredAtom2173 chi ∧
      ¬Fin15AnchoredAtom2174 chi ∧
      ¬Fin15AnchoredAtom2177 chi ∧
      ¬Fin15AnchoredAtom2192 chi ∧
      ¬Fin15AnchoredAtom2195 chi ∧
      ¬Fin15AnchoredAtom2199 chi ∧
      ¬Fin15AnchoredAtom2256 chi ∧
      ¬Fin15AnchoredAtom2259 chi ∧
      ¬Fin15AnchoredAtom2263 chi ∧
      ¬Fin15AnchoredAtom2309 chi ∧
      ¬Fin15AnchoredAtom2338 chi ∧
      ¬Fin15AnchoredAtom2339 chi ∧
      ¬Fin15AnchoredAtom2342 chi ∧
      ¬Fin15AnchoredAtom2357 chi ∧
      ¬Fin15AnchoredAtom2360 chi ∧
      ¬Fin15AnchoredAtom2364 chi ∧
      ¬Fin15AnchoredAtom2421 chi ∧
      ¬Fin15AnchoredAtom2424 chi ∧
      ¬Fin15AnchoredAtom2428 chi ∧
      ¬Fin15AnchoredAtom2474 chi ∧
      ¬Fin15AnchoredAtom2541 chi ∧
      ¬Fin15AnchoredAtom2544 chi ∧
      ¬Fin15AnchoredAtom2548 chi ∧
      ¬Fin15AnchoredAtom2594 chi ∧
      ¬Fin15AnchoredAtom2734 chi ∧
      ¬Fin15AnchoredAtom3548 chi ∧
      ¬Fin15AnchoredAtom3549 chi ∧
      ¬Fin15AnchoredAtom3552 chi ∧
      ¬Fin15AnchoredAtom3567 chi ∧
      ¬Fin15AnchoredAtom3570 chi ∧
      ¬Fin15AnchoredAtom3574 chi ∧
      ¬Fin15AnchoredAtom3631 chi ∧
      ¬Fin15AnchoredAtom3634 chi ∧
      ¬Fin15AnchoredAtom3638 chi ∧
      ¬Fin15AnchoredAtom3684 chi ∧
      ¬Fin15AnchoredAtom3751 chi ∧
      ¬Fin15AnchoredAtom3754 chi ∧
      ¬Fin15AnchoredAtom3758 chi ∧
      ¬Fin15AnchoredAtom3804 chi ∧
      ¬Fin15AnchoredAtom3944 chi ∧
      ¬Fin15AnchoredAtom4081 chi ∧
      ¬Fin15AnchoredAtom4084 chi ∧
      ¬Fin15AnchoredAtom4088 chi ∧
      ¬Fin15AnchoredAtom4134 chi ∧
      ¬Fin15AnchoredAtom4274 chi ∧
      ¬Fin15AnchoredAtom4484 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 6, 9, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09821
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2108 Fin15AnchoredAtom2111 Fin15AnchoredAtom2112
    Fin15AnchoredAtom2115 Fin15AnchoredAtom2128 Fin15AnchoredAtom2129 Fin15AnchoredAtom2132
    Fin15AnchoredAtom2147 Fin15AnchoredAtom2150 Fin15AnchoredAtom2154 Fin15AnchoredAtom2173
    Fin15AnchoredAtom2174 Fin15AnchoredAtom2177 Fin15AnchoredAtom2192 Fin15AnchoredAtom2195
    Fin15AnchoredAtom2199 Fin15AnchoredAtom2256 Fin15AnchoredAtom2259 Fin15AnchoredAtom2263
    Fin15AnchoredAtom2309 Fin15AnchoredAtom2338 Fin15AnchoredAtom2339 Fin15AnchoredAtom2342
    Fin15AnchoredAtom2357 Fin15AnchoredAtom2360 Fin15AnchoredAtom2364 Fin15AnchoredAtom2421
    Fin15AnchoredAtom2424 Fin15AnchoredAtom2428 Fin15AnchoredAtom2474 Fin15AnchoredAtom2541
    Fin15AnchoredAtom2544 Fin15AnchoredAtom2548 Fin15AnchoredAtom2594 Fin15AnchoredAtom2734
    Fin15AnchoredAtom3548 Fin15AnchoredAtom3549 Fin15AnchoredAtom3552 Fin15AnchoredAtom3567
    Fin15AnchoredAtom3570 Fin15AnchoredAtom3574 Fin15AnchoredAtom3631 Fin15AnchoredAtom3634
    Fin15AnchoredAtom3638 Fin15AnchoredAtom3684 Fin15AnchoredAtom3751 Fin15AnchoredAtom3754
    Fin15AnchoredAtom3758 Fin15AnchoredAtom3804 Fin15AnchoredAtom3944 Fin15AnchoredAtom4081
    Fin15AnchoredAtom4084 Fin15AnchoredAtom4088 Fin15AnchoredAtom4134 Fin15AnchoredAtom4274
    Fin15AnchoredAtom4484 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31168 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2128 chi ∧
      ¬Fin15AnchoredAtom2129 chi ∧
      ¬Fin15AnchoredAtom2133 chi ∧
      ¬Fin15AnchoredAtom2147 chi ∧
      ¬Fin15AnchoredAtom2151 chi ∧
      ¬Fin15AnchoredAtom2155 chi ∧
      ¬Fin15AnchoredAtom2173 chi ∧
      ¬Fin15AnchoredAtom2174 chi ∧
      ¬Fin15AnchoredAtom2178 chi ∧
      ¬Fin15AnchoredAtom2192 chi ∧
      ¬Fin15AnchoredAtom2196 chi ∧
      ¬Fin15AnchoredAtom2200 chi ∧
      ¬Fin15AnchoredAtom2256 chi ∧
      ¬Fin15AnchoredAtom2260 chi ∧
      ¬Fin15AnchoredAtom2264 chi ∧
      ¬Fin15AnchoredAtom2310 chi ∧
      ¬Fin15AnchoredAtom2338 chi ∧
      ¬Fin15AnchoredAtom2339 chi ∧
      ¬Fin15AnchoredAtom2343 chi ∧
      ¬Fin15AnchoredAtom2357 chi ∧
      ¬Fin15AnchoredAtom2361 chi ∧
      ¬Fin15AnchoredAtom2365 chi ∧
      ¬Fin15AnchoredAtom2421 chi ∧
      ¬Fin15AnchoredAtom2425 chi ∧
      ¬Fin15AnchoredAtom2429 chi ∧
      ¬Fin15AnchoredAtom2475 chi ∧
      ¬Fin15AnchoredAtom2541 chi ∧
      ¬Fin15AnchoredAtom2545 chi ∧
      ¬Fin15AnchoredAtom2549 chi ∧
      ¬Fin15AnchoredAtom2595 chi ∧
      ¬Fin15AnchoredAtom2735 chi ∧
      ¬Fin15AnchoredAtom3548 chi ∧
      ¬Fin15AnchoredAtom3549 chi ∧
      ¬Fin15AnchoredAtom3553 chi ∧
      ¬Fin15AnchoredAtom3567 chi ∧
      ¬Fin15AnchoredAtom3571 chi ∧
      ¬Fin15AnchoredAtom3575 chi ∧
      ¬Fin15AnchoredAtom3631 chi ∧
      ¬Fin15AnchoredAtom3635 chi ∧
      ¬Fin15AnchoredAtom3639 chi ∧
      ¬Fin15AnchoredAtom3685 chi ∧
      ¬Fin15AnchoredAtom3751 chi ∧
      ¬Fin15AnchoredAtom3755 chi ∧
      ¬Fin15AnchoredAtom3759 chi ∧
      ¬Fin15AnchoredAtom3805 chi ∧
      ¬Fin15AnchoredAtom3945 chi ∧
      ¬Fin15AnchoredAtom4081 chi ∧
      ¬Fin15AnchoredAtom4085 chi ∧
      ¬Fin15AnchoredAtom4089 chi ∧
      ¬Fin15AnchoredAtom4135 chi ∧
      ¬Fin15AnchoredAtom4275 chi ∧
      ¬Fin15AnchoredAtom4485 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 6, 9, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask18013
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2108 Fin15AnchoredAtom2111 Fin15AnchoredAtom2112
    Fin15AnchoredAtom2116 Fin15AnchoredAtom2128 Fin15AnchoredAtom2129 Fin15AnchoredAtom2133
    Fin15AnchoredAtom2147 Fin15AnchoredAtom2151 Fin15AnchoredAtom2155 Fin15AnchoredAtom2173
    Fin15AnchoredAtom2174 Fin15AnchoredAtom2178 Fin15AnchoredAtom2192 Fin15AnchoredAtom2196
    Fin15AnchoredAtom2200 Fin15AnchoredAtom2256 Fin15AnchoredAtom2260 Fin15AnchoredAtom2264
    Fin15AnchoredAtom2310 Fin15AnchoredAtom2338 Fin15AnchoredAtom2339 Fin15AnchoredAtom2343
    Fin15AnchoredAtom2357 Fin15AnchoredAtom2361 Fin15AnchoredAtom2365 Fin15AnchoredAtom2421
    Fin15AnchoredAtom2425 Fin15AnchoredAtom2429 Fin15AnchoredAtom2475 Fin15AnchoredAtom2541
    Fin15AnchoredAtom2545 Fin15AnchoredAtom2549 Fin15AnchoredAtom2595 Fin15AnchoredAtom2735
    Fin15AnchoredAtom3548 Fin15AnchoredAtom3549 Fin15AnchoredAtom3553 Fin15AnchoredAtom3567
    Fin15AnchoredAtom3571 Fin15AnchoredAtom3575 Fin15AnchoredAtom3631 Fin15AnchoredAtom3635
    Fin15AnchoredAtom3639 Fin15AnchoredAtom3685 Fin15AnchoredAtom3751 Fin15AnchoredAtom3755
    Fin15AnchoredAtom3759 Fin15AnchoredAtom3805 Fin15AnchoredAtom3945 Fin15AnchoredAtom4081
    Fin15AnchoredAtom4085 Fin15AnchoredAtom4089 Fin15AnchoredAtom4135 Fin15AnchoredAtom4275
    Fin15AnchoredAtom4485 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31169 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2113 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2128 chi ∧
      ¬Fin15AnchoredAtom2130 chi ∧
      ¬Fin15AnchoredAtom2132 chi ∧
      ¬Fin15AnchoredAtom2148 chi ∧
      ¬Fin15AnchoredAtom2150 chi ∧
      ¬Fin15AnchoredAtom2157 chi ∧
      ¬Fin15AnchoredAtom2173 chi ∧
      ¬Fin15AnchoredAtom2175 chi ∧
      ¬Fin15AnchoredAtom2177 chi ∧
      ¬Fin15AnchoredAtom2193 chi ∧
      ¬Fin15AnchoredAtom2195 chi ∧
      ¬Fin15AnchoredAtom2202 chi ∧
      ¬Fin15AnchoredAtom2257 chi ∧
      ¬Fin15AnchoredAtom2259 chi ∧
      ¬Fin15AnchoredAtom2266 chi ∧
      ¬Fin15AnchoredAtom2312 chi ∧
      ¬Fin15AnchoredAtom2338 chi ∧
      ¬Fin15AnchoredAtom2340 chi ∧
      ¬Fin15AnchoredAtom2342 chi ∧
      ¬Fin15AnchoredAtom2358 chi ∧
      ¬Fin15AnchoredAtom2360 chi ∧
      ¬Fin15AnchoredAtom2367 chi ∧
      ¬Fin15AnchoredAtom2422 chi ∧
      ¬Fin15AnchoredAtom2424 chi ∧
      ¬Fin15AnchoredAtom2431 chi ∧
      ¬Fin15AnchoredAtom2477 chi ∧
      ¬Fin15AnchoredAtom2542 chi ∧
      ¬Fin15AnchoredAtom2544 chi ∧
      ¬Fin15AnchoredAtom2551 chi ∧
      ¬Fin15AnchoredAtom2597 chi ∧
      ¬Fin15AnchoredAtom2737 chi ∧
      ¬Fin15AnchoredAtom3548 chi ∧
      ¬Fin15AnchoredAtom3550 chi ∧
      ¬Fin15AnchoredAtom3552 chi ∧
      ¬Fin15AnchoredAtom3568 chi ∧
      ¬Fin15AnchoredAtom3570 chi ∧
      ¬Fin15AnchoredAtom3577 chi ∧
      ¬Fin15AnchoredAtom3632 chi ∧
      ¬Fin15AnchoredAtom3634 chi ∧
      ¬Fin15AnchoredAtom3641 chi ∧
      ¬Fin15AnchoredAtom3687 chi ∧
      ¬Fin15AnchoredAtom3752 chi ∧
      ¬Fin15AnchoredAtom3754 chi ∧
      ¬Fin15AnchoredAtom3761 chi ∧
      ¬Fin15AnchoredAtom3807 chi ∧
      ¬Fin15AnchoredAtom3947 chi ∧
      ¬Fin15AnchoredAtom4082 chi ∧
      ¬Fin15AnchoredAtom4084 chi ∧
      ¬Fin15AnchoredAtom4091 chi ∧
      ¬Fin15AnchoredAtom4137 chi ∧
      ¬Fin15AnchoredAtom4277 chi ∧
      ¬Fin15AnchoredAtom4487 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 6, 9, 11, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask10845
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2108 Fin15AnchoredAtom2111 Fin15AnchoredAtom2113
    Fin15AnchoredAtom2115 Fin15AnchoredAtom2128 Fin15AnchoredAtom2130 Fin15AnchoredAtom2132
    Fin15AnchoredAtom2148 Fin15AnchoredAtom2150 Fin15AnchoredAtom2157 Fin15AnchoredAtom2173
    Fin15AnchoredAtom2175 Fin15AnchoredAtom2177 Fin15AnchoredAtom2193 Fin15AnchoredAtom2195
    Fin15AnchoredAtom2202 Fin15AnchoredAtom2257 Fin15AnchoredAtom2259 Fin15AnchoredAtom2266
    Fin15AnchoredAtom2312 Fin15AnchoredAtom2338 Fin15AnchoredAtom2340 Fin15AnchoredAtom2342
    Fin15AnchoredAtom2358 Fin15AnchoredAtom2360 Fin15AnchoredAtom2367 Fin15AnchoredAtom2422
    Fin15AnchoredAtom2424 Fin15AnchoredAtom2431 Fin15AnchoredAtom2477 Fin15AnchoredAtom2542
    Fin15AnchoredAtom2544 Fin15AnchoredAtom2551 Fin15AnchoredAtom2597 Fin15AnchoredAtom2737
    Fin15AnchoredAtom3548 Fin15AnchoredAtom3550 Fin15AnchoredAtom3552 Fin15AnchoredAtom3568
    Fin15AnchoredAtom3570 Fin15AnchoredAtom3577 Fin15AnchoredAtom3632 Fin15AnchoredAtom3634
    Fin15AnchoredAtom3641 Fin15AnchoredAtom3687 Fin15AnchoredAtom3752 Fin15AnchoredAtom3754
    Fin15AnchoredAtom3761 Fin15AnchoredAtom3807 Fin15AnchoredAtom3947 Fin15AnchoredAtom4082
    Fin15AnchoredAtom4084 Fin15AnchoredAtom4091 Fin15AnchoredAtom4137 Fin15AnchoredAtom4277
    Fin15AnchoredAtom4487 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31170 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2128 chi ∧
      ¬Fin15AnchoredAtom2131 chi ∧
      ¬Fin15AnchoredAtom2132 chi ∧
      ¬Fin15AnchoredAtom2149 chi ∧
      ¬Fin15AnchoredAtom2150 chi ∧
      ¬Fin15AnchoredAtom2159 chi ∧
      ¬Fin15AnchoredAtom2173 chi ∧
      ¬Fin15AnchoredAtom2176 chi ∧
      ¬Fin15AnchoredAtom2177 chi ∧
      ¬Fin15AnchoredAtom2194 chi ∧
      ¬Fin15AnchoredAtom2195 chi ∧
      ¬Fin15AnchoredAtom2204 chi ∧
      ¬Fin15AnchoredAtom2258 chi ∧
      ¬Fin15AnchoredAtom2259 chi ∧
      ¬Fin15AnchoredAtom2268 chi ∧
      ¬Fin15AnchoredAtom2314 chi ∧
      ¬Fin15AnchoredAtom2338 chi ∧
      ¬Fin15AnchoredAtom2341 chi ∧
      ¬Fin15AnchoredAtom2342 chi ∧
      ¬Fin15AnchoredAtom2359 chi ∧
      ¬Fin15AnchoredAtom2360 chi ∧
      ¬Fin15AnchoredAtom2369 chi ∧
      ¬Fin15AnchoredAtom2423 chi ∧
      ¬Fin15AnchoredAtom2424 chi ∧
      ¬Fin15AnchoredAtom2433 chi ∧
      ¬Fin15AnchoredAtom2479 chi ∧
      ¬Fin15AnchoredAtom2543 chi ∧
      ¬Fin15AnchoredAtom2544 chi ∧
      ¬Fin15AnchoredAtom2553 chi ∧
      ¬Fin15AnchoredAtom2599 chi ∧
      ¬Fin15AnchoredAtom2739 chi ∧
      ¬Fin15AnchoredAtom3548 chi ∧
      ¬Fin15AnchoredAtom3551 chi ∧
      ¬Fin15AnchoredAtom3552 chi ∧
      ¬Fin15AnchoredAtom3569 chi ∧
      ¬Fin15AnchoredAtom3570 chi ∧
      ¬Fin15AnchoredAtom3579 chi ∧
      ¬Fin15AnchoredAtom3633 chi ∧
      ¬Fin15AnchoredAtom3634 chi ∧
      ¬Fin15AnchoredAtom3643 chi ∧
      ¬Fin15AnchoredAtom3689 chi ∧
      ¬Fin15AnchoredAtom3753 chi ∧
      ¬Fin15AnchoredAtom3754 chi ∧
      ¬Fin15AnchoredAtom3763 chi ∧
      ¬Fin15AnchoredAtom3809 chi ∧
      ¬Fin15AnchoredAtom3949 chi ∧
      ¬Fin15AnchoredAtom4083 chi ∧
      ¬Fin15AnchoredAtom4084 chi ∧
      ¬Fin15AnchoredAtom4093 chi ∧
      ¬Fin15AnchoredAtom4139 chi ∧
      ¬Fin15AnchoredAtom4279 chi ∧
      ¬Fin15AnchoredAtom4489 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 6, 9, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask12893
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2108 Fin15AnchoredAtom2111 Fin15AnchoredAtom2114
    Fin15AnchoredAtom2115 Fin15AnchoredAtom2128 Fin15AnchoredAtom2131 Fin15AnchoredAtom2132
    Fin15AnchoredAtom2149 Fin15AnchoredAtom2150 Fin15AnchoredAtom2159 Fin15AnchoredAtom2173
    Fin15AnchoredAtom2176 Fin15AnchoredAtom2177 Fin15AnchoredAtom2194 Fin15AnchoredAtom2195
    Fin15AnchoredAtom2204 Fin15AnchoredAtom2258 Fin15AnchoredAtom2259 Fin15AnchoredAtom2268
    Fin15AnchoredAtom2314 Fin15AnchoredAtom2338 Fin15AnchoredAtom2341 Fin15AnchoredAtom2342
    Fin15AnchoredAtom2359 Fin15AnchoredAtom2360 Fin15AnchoredAtom2369 Fin15AnchoredAtom2423
    Fin15AnchoredAtom2424 Fin15AnchoredAtom2433 Fin15AnchoredAtom2479 Fin15AnchoredAtom2543
    Fin15AnchoredAtom2544 Fin15AnchoredAtom2553 Fin15AnchoredAtom2599 Fin15AnchoredAtom2739
    Fin15AnchoredAtom3548 Fin15AnchoredAtom3551 Fin15AnchoredAtom3552 Fin15AnchoredAtom3569
    Fin15AnchoredAtom3570 Fin15AnchoredAtom3579 Fin15AnchoredAtom3633 Fin15AnchoredAtom3634
    Fin15AnchoredAtom3643 Fin15AnchoredAtom3689 Fin15AnchoredAtom3753 Fin15AnchoredAtom3754
    Fin15AnchoredAtom3763 Fin15AnchoredAtom3809 Fin15AnchoredAtom3949 Fin15AnchoredAtom4083
    Fin15AnchoredAtom4084 Fin15AnchoredAtom4093 Fin15AnchoredAtom4139 Fin15AnchoredAtom4279
    Fin15AnchoredAtom4489 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31171 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2128 chi ∧
      ¬Fin15AnchoredAtom2131 chi ∧
      ¬Fin15AnchoredAtom2133 chi ∧
      ¬Fin15AnchoredAtom2149 chi ∧
      ¬Fin15AnchoredAtom2151 chi ∧
      ¬Fin15AnchoredAtom2160 chi ∧
      ¬Fin15AnchoredAtom2173 chi ∧
      ¬Fin15AnchoredAtom2176 chi ∧
      ¬Fin15AnchoredAtom2178 chi ∧
      ¬Fin15AnchoredAtom2194 chi ∧
      ¬Fin15AnchoredAtom2196 chi ∧
      ¬Fin15AnchoredAtom2205 chi ∧
      ¬Fin15AnchoredAtom2258 chi ∧
      ¬Fin15AnchoredAtom2260 chi ∧
      ¬Fin15AnchoredAtom2269 chi ∧
      ¬Fin15AnchoredAtom2315 chi ∧
      ¬Fin15AnchoredAtom2338 chi ∧
      ¬Fin15AnchoredAtom2341 chi ∧
      ¬Fin15AnchoredAtom2343 chi ∧
      ¬Fin15AnchoredAtom2359 chi ∧
      ¬Fin15AnchoredAtom2361 chi ∧
      ¬Fin15AnchoredAtom2370 chi ∧
      ¬Fin15AnchoredAtom2423 chi ∧
      ¬Fin15AnchoredAtom2425 chi ∧
      ¬Fin15AnchoredAtom2434 chi ∧
      ¬Fin15AnchoredAtom2480 chi ∧
      ¬Fin15AnchoredAtom2543 chi ∧
      ¬Fin15AnchoredAtom2545 chi ∧
      ¬Fin15AnchoredAtom2554 chi ∧
      ¬Fin15AnchoredAtom2600 chi ∧
      ¬Fin15AnchoredAtom2740 chi ∧
      ¬Fin15AnchoredAtom3548 chi ∧
      ¬Fin15AnchoredAtom3551 chi ∧
      ¬Fin15AnchoredAtom3553 chi ∧
      ¬Fin15AnchoredAtom3569 chi ∧
      ¬Fin15AnchoredAtom3571 chi ∧
      ¬Fin15AnchoredAtom3580 chi ∧
      ¬Fin15AnchoredAtom3633 chi ∧
      ¬Fin15AnchoredAtom3635 chi ∧
      ¬Fin15AnchoredAtom3644 chi ∧
      ¬Fin15AnchoredAtom3690 chi ∧
      ¬Fin15AnchoredAtom3753 chi ∧
      ¬Fin15AnchoredAtom3755 chi ∧
      ¬Fin15AnchoredAtom3764 chi ∧
      ¬Fin15AnchoredAtom3810 chi ∧
      ¬Fin15AnchoredAtom3950 chi ∧
      ¬Fin15AnchoredAtom4083 chi ∧
      ¬Fin15AnchoredAtom4085 chi ∧
      ¬Fin15AnchoredAtom4094 chi ∧
      ¬Fin15AnchoredAtom4140 chi ∧
      ¬Fin15AnchoredAtom4280 chi ∧
      ¬Fin15AnchoredAtom4490 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 6, 9, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21085
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2108 Fin15AnchoredAtom2111 Fin15AnchoredAtom2114
    Fin15AnchoredAtom2116 Fin15AnchoredAtom2128 Fin15AnchoredAtom2131 Fin15AnchoredAtom2133
    Fin15AnchoredAtom2149 Fin15AnchoredAtom2151 Fin15AnchoredAtom2160 Fin15AnchoredAtom2173
    Fin15AnchoredAtom2176 Fin15AnchoredAtom2178 Fin15AnchoredAtom2194 Fin15AnchoredAtom2196
    Fin15AnchoredAtom2205 Fin15AnchoredAtom2258 Fin15AnchoredAtom2260 Fin15AnchoredAtom2269
    Fin15AnchoredAtom2315 Fin15AnchoredAtom2338 Fin15AnchoredAtom2341 Fin15AnchoredAtom2343
    Fin15AnchoredAtom2359 Fin15AnchoredAtom2361 Fin15AnchoredAtom2370 Fin15AnchoredAtom2423
    Fin15AnchoredAtom2425 Fin15AnchoredAtom2434 Fin15AnchoredAtom2480 Fin15AnchoredAtom2543
    Fin15AnchoredAtom2545 Fin15AnchoredAtom2554 Fin15AnchoredAtom2600 Fin15AnchoredAtom2740
    Fin15AnchoredAtom3548 Fin15AnchoredAtom3551 Fin15AnchoredAtom3553 Fin15AnchoredAtom3569
    Fin15AnchoredAtom3571 Fin15AnchoredAtom3580 Fin15AnchoredAtom3633 Fin15AnchoredAtom3635
    Fin15AnchoredAtom3644 Fin15AnchoredAtom3690 Fin15AnchoredAtom3753 Fin15AnchoredAtom3755
    Fin15AnchoredAtom3764 Fin15AnchoredAtom3810 Fin15AnchoredAtom3950 Fin15AnchoredAtom4083
    Fin15AnchoredAtom4085 Fin15AnchoredAtom4094 Fin15AnchoredAtom4140 Fin15AnchoredAtom4280
    Fin15AnchoredAtom4490 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31172 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2128 chi ∧
      ¬Fin15AnchoredAtom2132 chi ∧
      ¬Fin15AnchoredAtom2133 chi ∧
      ¬Fin15AnchoredAtom2150 chi ∧
      ¬Fin15AnchoredAtom2151 chi ∧
      ¬Fin15AnchoredAtom2161 chi ∧
      ¬Fin15AnchoredAtom2173 chi ∧
      ¬Fin15AnchoredAtom2177 chi ∧
      ¬Fin15AnchoredAtom2178 chi ∧
      ¬Fin15AnchoredAtom2195 chi ∧
      ¬Fin15AnchoredAtom2196 chi ∧
      ¬Fin15AnchoredAtom2206 chi ∧
      ¬Fin15AnchoredAtom2259 chi ∧
      ¬Fin15AnchoredAtom2260 chi ∧
      ¬Fin15AnchoredAtom2270 chi ∧
      ¬Fin15AnchoredAtom2316 chi ∧
      ¬Fin15AnchoredAtom2338 chi ∧
      ¬Fin15AnchoredAtom2342 chi ∧
      ¬Fin15AnchoredAtom2343 chi ∧
      ¬Fin15AnchoredAtom2360 chi ∧
      ¬Fin15AnchoredAtom2361 chi ∧
      ¬Fin15AnchoredAtom2371 chi ∧
      ¬Fin15AnchoredAtom2424 chi ∧
      ¬Fin15AnchoredAtom2425 chi ∧
      ¬Fin15AnchoredAtom2435 chi ∧
      ¬Fin15AnchoredAtom2481 chi ∧
      ¬Fin15AnchoredAtom2544 chi ∧
      ¬Fin15AnchoredAtom2545 chi ∧
      ¬Fin15AnchoredAtom2555 chi ∧
      ¬Fin15AnchoredAtom2601 chi ∧
      ¬Fin15AnchoredAtom2741 chi ∧
      ¬Fin15AnchoredAtom3548 chi ∧
      ¬Fin15AnchoredAtom3552 chi ∧
      ¬Fin15AnchoredAtom3553 chi ∧
      ¬Fin15AnchoredAtom3570 chi ∧
      ¬Fin15AnchoredAtom3571 chi ∧
      ¬Fin15AnchoredAtom3581 chi ∧
      ¬Fin15AnchoredAtom3634 chi ∧
      ¬Fin15AnchoredAtom3635 chi ∧
      ¬Fin15AnchoredAtom3645 chi ∧
      ¬Fin15AnchoredAtom3691 chi ∧
      ¬Fin15AnchoredAtom3754 chi ∧
      ¬Fin15AnchoredAtom3755 chi ∧
      ¬Fin15AnchoredAtom3765 chi ∧
      ¬Fin15AnchoredAtom3811 chi ∧
      ¬Fin15AnchoredAtom3951 chi ∧
      ¬Fin15AnchoredAtom4084 chi ∧
      ¬Fin15AnchoredAtom4085 chi ∧
      ¬Fin15AnchoredAtom4095 chi ∧
      ¬Fin15AnchoredAtom4141 chi ∧
      ¬Fin15AnchoredAtom4281 chi ∧
      ¬Fin15AnchoredAtom4491 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 6, 9, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25181
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2108 Fin15AnchoredAtom2111 Fin15AnchoredAtom2115
    Fin15AnchoredAtom2116 Fin15AnchoredAtom2128 Fin15AnchoredAtom2132 Fin15AnchoredAtom2133
    Fin15AnchoredAtom2150 Fin15AnchoredAtom2151 Fin15AnchoredAtom2161 Fin15AnchoredAtom2173
    Fin15AnchoredAtom2177 Fin15AnchoredAtom2178 Fin15AnchoredAtom2195 Fin15AnchoredAtom2196
    Fin15AnchoredAtom2206 Fin15AnchoredAtom2259 Fin15AnchoredAtom2260 Fin15AnchoredAtom2270
    Fin15AnchoredAtom2316 Fin15AnchoredAtom2338 Fin15AnchoredAtom2342 Fin15AnchoredAtom2343
    Fin15AnchoredAtom2360 Fin15AnchoredAtom2361 Fin15AnchoredAtom2371 Fin15AnchoredAtom2424
    Fin15AnchoredAtom2425 Fin15AnchoredAtom2435 Fin15AnchoredAtom2481 Fin15AnchoredAtom2544
    Fin15AnchoredAtom2545 Fin15AnchoredAtom2555 Fin15AnchoredAtom2601 Fin15AnchoredAtom2741
    Fin15AnchoredAtom3548 Fin15AnchoredAtom3552 Fin15AnchoredAtom3553 Fin15AnchoredAtom3570
    Fin15AnchoredAtom3571 Fin15AnchoredAtom3581 Fin15AnchoredAtom3634 Fin15AnchoredAtom3635
    Fin15AnchoredAtom3645 Fin15AnchoredAtom3691 Fin15AnchoredAtom3754 Fin15AnchoredAtom3755
    Fin15AnchoredAtom3765 Fin15AnchoredAtom3811 Fin15AnchoredAtom3951 Fin15AnchoredAtom4084
    Fin15AnchoredAtom4085 Fin15AnchoredAtom4095 Fin15AnchoredAtom4141 Fin15AnchoredAtom4281
    Fin15AnchoredAtom4491 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31173 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2129 chi ∧
      ¬Fin15AnchoredAtom2131 chi ∧
      ¬Fin15AnchoredAtom2132 chi ∧
      ¬Fin15AnchoredAtom2153 chi ∧
      ¬Fin15AnchoredAtom2154 chi ∧
      ¬Fin15AnchoredAtom2159 chi ∧
      ¬Fin15AnchoredAtom2174 chi ∧
      ¬Fin15AnchoredAtom2176 chi ∧
      ¬Fin15AnchoredAtom2177 chi ∧
      ¬Fin15AnchoredAtom2198 chi ∧
      ¬Fin15AnchoredAtom2199 chi ∧
      ¬Fin15AnchoredAtom2204 chi ∧
      ¬Fin15AnchoredAtom2262 chi ∧
      ¬Fin15AnchoredAtom2263 chi ∧
      ¬Fin15AnchoredAtom2268 chi ∧
      ¬Fin15AnchoredAtom2320 chi ∧
      ¬Fin15AnchoredAtom2339 chi ∧
      ¬Fin15AnchoredAtom2341 chi ∧
      ¬Fin15AnchoredAtom2342 chi ∧
      ¬Fin15AnchoredAtom2363 chi ∧
      ¬Fin15AnchoredAtom2364 chi ∧
      ¬Fin15AnchoredAtom2369 chi ∧
      ¬Fin15AnchoredAtom2427 chi ∧
      ¬Fin15AnchoredAtom2428 chi ∧
      ¬Fin15AnchoredAtom2433 chi ∧
      ¬Fin15AnchoredAtom2485 chi ∧
      ¬Fin15AnchoredAtom2547 chi ∧
      ¬Fin15AnchoredAtom2548 chi ∧
      ¬Fin15AnchoredAtom2553 chi ∧
      ¬Fin15AnchoredAtom2605 chi ∧
      ¬Fin15AnchoredAtom2745 chi ∧
      ¬Fin15AnchoredAtom3549 chi ∧
      ¬Fin15AnchoredAtom3551 chi ∧
      ¬Fin15AnchoredAtom3552 chi ∧
      ¬Fin15AnchoredAtom3573 chi ∧
      ¬Fin15AnchoredAtom3574 chi ∧
      ¬Fin15AnchoredAtom3579 chi ∧
      ¬Fin15AnchoredAtom3637 chi ∧
      ¬Fin15AnchoredAtom3638 chi ∧
      ¬Fin15AnchoredAtom3643 chi ∧
      ¬Fin15AnchoredAtom3695 chi ∧
      ¬Fin15AnchoredAtom3757 chi ∧
      ¬Fin15AnchoredAtom3758 chi ∧
      ¬Fin15AnchoredAtom3763 chi ∧
      ¬Fin15AnchoredAtom3815 chi ∧
      ¬Fin15AnchoredAtom3955 chi ∧
      ¬Fin15AnchoredAtom4087 chi ∧
      ¬Fin15AnchoredAtom4088 chi ∧
      ¬Fin15AnchoredAtom4093 chi ∧
      ¬Fin15AnchoredAtom4145 chi ∧
      ¬Fin15AnchoredAtom4285 chi ∧
      ¬Fin15AnchoredAtom4495 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 6, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13405
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2108 Fin15AnchoredAtom2112 Fin15AnchoredAtom2114
    Fin15AnchoredAtom2115 Fin15AnchoredAtom2129 Fin15AnchoredAtom2131 Fin15AnchoredAtom2132
    Fin15AnchoredAtom2153 Fin15AnchoredAtom2154 Fin15AnchoredAtom2159 Fin15AnchoredAtom2174
    Fin15AnchoredAtom2176 Fin15AnchoredAtom2177 Fin15AnchoredAtom2198 Fin15AnchoredAtom2199
    Fin15AnchoredAtom2204 Fin15AnchoredAtom2262 Fin15AnchoredAtom2263 Fin15AnchoredAtom2268
    Fin15AnchoredAtom2320 Fin15AnchoredAtom2339 Fin15AnchoredAtom2341 Fin15AnchoredAtom2342
    Fin15AnchoredAtom2363 Fin15AnchoredAtom2364 Fin15AnchoredAtom2369 Fin15AnchoredAtom2427
    Fin15AnchoredAtom2428 Fin15AnchoredAtom2433 Fin15AnchoredAtom2485 Fin15AnchoredAtom2547
    Fin15AnchoredAtom2548 Fin15AnchoredAtom2553 Fin15AnchoredAtom2605 Fin15AnchoredAtom2745
    Fin15AnchoredAtom3549 Fin15AnchoredAtom3551 Fin15AnchoredAtom3552 Fin15AnchoredAtom3573
    Fin15AnchoredAtom3574 Fin15AnchoredAtom3579 Fin15AnchoredAtom3637 Fin15AnchoredAtom3638
    Fin15AnchoredAtom3643 Fin15AnchoredAtom3695 Fin15AnchoredAtom3757 Fin15AnchoredAtom3758
    Fin15AnchoredAtom3763 Fin15AnchoredAtom3815 Fin15AnchoredAtom3955 Fin15AnchoredAtom4087
    Fin15AnchoredAtom4088 Fin15AnchoredAtom4093 Fin15AnchoredAtom4145 Fin15AnchoredAtom4285
    Fin15AnchoredAtom4495 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31174 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2129 chi ∧
      ¬Fin15AnchoredAtom2131 chi ∧
      ¬Fin15AnchoredAtom2133 chi ∧
      ¬Fin15AnchoredAtom2153 chi ∧
      ¬Fin15AnchoredAtom2155 chi ∧
      ¬Fin15AnchoredAtom2160 chi ∧
      ¬Fin15AnchoredAtom2174 chi ∧
      ¬Fin15AnchoredAtom2176 chi ∧
      ¬Fin15AnchoredAtom2178 chi ∧
      ¬Fin15AnchoredAtom2198 chi ∧
      ¬Fin15AnchoredAtom2200 chi ∧
      ¬Fin15AnchoredAtom2205 chi ∧
      ¬Fin15AnchoredAtom2262 chi ∧
      ¬Fin15AnchoredAtom2264 chi ∧
      ¬Fin15AnchoredAtom2269 chi ∧
      ¬Fin15AnchoredAtom2321 chi ∧
      ¬Fin15AnchoredAtom2339 chi ∧
      ¬Fin15AnchoredAtom2341 chi ∧
      ¬Fin15AnchoredAtom2343 chi ∧
      ¬Fin15AnchoredAtom2363 chi ∧
      ¬Fin15AnchoredAtom2365 chi ∧
      ¬Fin15AnchoredAtom2370 chi ∧
      ¬Fin15AnchoredAtom2427 chi ∧
      ¬Fin15AnchoredAtom2429 chi ∧
      ¬Fin15AnchoredAtom2434 chi ∧
      ¬Fin15AnchoredAtom2486 chi ∧
      ¬Fin15AnchoredAtom2547 chi ∧
      ¬Fin15AnchoredAtom2549 chi ∧
      ¬Fin15AnchoredAtom2554 chi ∧
      ¬Fin15AnchoredAtom2606 chi ∧
      ¬Fin15AnchoredAtom2746 chi ∧
      ¬Fin15AnchoredAtom3549 chi ∧
      ¬Fin15AnchoredAtom3551 chi ∧
      ¬Fin15AnchoredAtom3553 chi ∧
      ¬Fin15AnchoredAtom3573 chi ∧
      ¬Fin15AnchoredAtom3575 chi ∧
      ¬Fin15AnchoredAtom3580 chi ∧
      ¬Fin15AnchoredAtom3637 chi ∧
      ¬Fin15AnchoredAtom3639 chi ∧
      ¬Fin15AnchoredAtom3644 chi ∧
      ¬Fin15AnchoredAtom3696 chi ∧
      ¬Fin15AnchoredAtom3757 chi ∧
      ¬Fin15AnchoredAtom3759 chi ∧
      ¬Fin15AnchoredAtom3764 chi ∧
      ¬Fin15AnchoredAtom3816 chi ∧
      ¬Fin15AnchoredAtom3956 chi ∧
      ¬Fin15AnchoredAtom4087 chi ∧
      ¬Fin15AnchoredAtom4089 chi ∧
      ¬Fin15AnchoredAtom4094 chi ∧
      ¬Fin15AnchoredAtom4146 chi ∧
      ¬Fin15AnchoredAtom4286 chi ∧
      ¬Fin15AnchoredAtom4496 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 6, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21597
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2108 Fin15AnchoredAtom2112 Fin15AnchoredAtom2114
    Fin15AnchoredAtom2116 Fin15AnchoredAtom2129 Fin15AnchoredAtom2131 Fin15AnchoredAtom2133
    Fin15AnchoredAtom2153 Fin15AnchoredAtom2155 Fin15AnchoredAtom2160 Fin15AnchoredAtom2174
    Fin15AnchoredAtom2176 Fin15AnchoredAtom2178 Fin15AnchoredAtom2198 Fin15AnchoredAtom2200
    Fin15AnchoredAtom2205 Fin15AnchoredAtom2262 Fin15AnchoredAtom2264 Fin15AnchoredAtom2269
    Fin15AnchoredAtom2321 Fin15AnchoredAtom2339 Fin15AnchoredAtom2341 Fin15AnchoredAtom2343
    Fin15AnchoredAtom2363 Fin15AnchoredAtom2365 Fin15AnchoredAtom2370 Fin15AnchoredAtom2427
    Fin15AnchoredAtom2429 Fin15AnchoredAtom2434 Fin15AnchoredAtom2486 Fin15AnchoredAtom2547
    Fin15AnchoredAtom2549 Fin15AnchoredAtom2554 Fin15AnchoredAtom2606 Fin15AnchoredAtom2746
    Fin15AnchoredAtom3549 Fin15AnchoredAtom3551 Fin15AnchoredAtom3553 Fin15AnchoredAtom3573
    Fin15AnchoredAtom3575 Fin15AnchoredAtom3580 Fin15AnchoredAtom3637 Fin15AnchoredAtom3639
    Fin15AnchoredAtom3644 Fin15AnchoredAtom3696 Fin15AnchoredAtom3757 Fin15AnchoredAtom3759
    Fin15AnchoredAtom3764 Fin15AnchoredAtom3816 Fin15AnchoredAtom3956 Fin15AnchoredAtom4087
    Fin15AnchoredAtom4089 Fin15AnchoredAtom4094 Fin15AnchoredAtom4146 Fin15AnchoredAtom4286
    Fin15AnchoredAtom4496 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31175 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2129 chi ∧
      ¬Fin15AnchoredAtom2132 chi ∧
      ¬Fin15AnchoredAtom2133 chi ∧
      ¬Fin15AnchoredAtom2154 chi ∧
      ¬Fin15AnchoredAtom2155 chi ∧
      ¬Fin15AnchoredAtom2161 chi ∧
      ¬Fin15AnchoredAtom2174 chi ∧
      ¬Fin15AnchoredAtom2177 chi ∧
      ¬Fin15AnchoredAtom2178 chi ∧
      ¬Fin15AnchoredAtom2199 chi ∧
      ¬Fin15AnchoredAtom2200 chi ∧
      ¬Fin15AnchoredAtom2206 chi ∧
      ¬Fin15AnchoredAtom2263 chi ∧
      ¬Fin15AnchoredAtom2264 chi ∧
      ¬Fin15AnchoredAtom2270 chi ∧
      ¬Fin15AnchoredAtom2322 chi ∧
      ¬Fin15AnchoredAtom2339 chi ∧
      ¬Fin15AnchoredAtom2342 chi ∧
      ¬Fin15AnchoredAtom2343 chi ∧
      ¬Fin15AnchoredAtom2364 chi ∧
      ¬Fin15AnchoredAtom2365 chi ∧
      ¬Fin15AnchoredAtom2371 chi ∧
      ¬Fin15AnchoredAtom2428 chi ∧
      ¬Fin15AnchoredAtom2429 chi ∧
      ¬Fin15AnchoredAtom2435 chi ∧
      ¬Fin15AnchoredAtom2487 chi ∧
      ¬Fin15AnchoredAtom2548 chi ∧
      ¬Fin15AnchoredAtom2549 chi ∧
      ¬Fin15AnchoredAtom2555 chi ∧
      ¬Fin15AnchoredAtom2607 chi ∧
      ¬Fin15AnchoredAtom2747 chi ∧
      ¬Fin15AnchoredAtom3549 chi ∧
      ¬Fin15AnchoredAtom3552 chi ∧
      ¬Fin15AnchoredAtom3553 chi ∧
      ¬Fin15AnchoredAtom3574 chi ∧
      ¬Fin15AnchoredAtom3575 chi ∧
      ¬Fin15AnchoredAtom3581 chi ∧
      ¬Fin15AnchoredAtom3638 chi ∧
      ¬Fin15AnchoredAtom3639 chi ∧
      ¬Fin15AnchoredAtom3645 chi ∧
      ¬Fin15AnchoredAtom3697 chi ∧
      ¬Fin15AnchoredAtom3758 chi ∧
      ¬Fin15AnchoredAtom3759 chi ∧
      ¬Fin15AnchoredAtom3765 chi ∧
      ¬Fin15AnchoredAtom3817 chi ∧
      ¬Fin15AnchoredAtom3957 chi ∧
      ¬Fin15AnchoredAtom4088 chi ∧
      ¬Fin15AnchoredAtom4089 chi ∧
      ¬Fin15AnchoredAtom4095 chi ∧
      ¬Fin15AnchoredAtom4147 chi ∧
      ¬Fin15AnchoredAtom4287 chi ∧
      ¬Fin15AnchoredAtom4497 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 6, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25693
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2108 Fin15AnchoredAtom2112 Fin15AnchoredAtom2115
    Fin15AnchoredAtom2116 Fin15AnchoredAtom2129 Fin15AnchoredAtom2132 Fin15AnchoredAtom2133
    Fin15AnchoredAtom2154 Fin15AnchoredAtom2155 Fin15AnchoredAtom2161 Fin15AnchoredAtom2174
    Fin15AnchoredAtom2177 Fin15AnchoredAtom2178 Fin15AnchoredAtom2199 Fin15AnchoredAtom2200
    Fin15AnchoredAtom2206 Fin15AnchoredAtom2263 Fin15AnchoredAtom2264 Fin15AnchoredAtom2270
    Fin15AnchoredAtom2322 Fin15AnchoredAtom2339 Fin15AnchoredAtom2342 Fin15AnchoredAtom2343
    Fin15AnchoredAtom2364 Fin15AnchoredAtom2365 Fin15AnchoredAtom2371 Fin15AnchoredAtom2428
    Fin15AnchoredAtom2429 Fin15AnchoredAtom2435 Fin15AnchoredAtom2487 Fin15AnchoredAtom2548
    Fin15AnchoredAtom2549 Fin15AnchoredAtom2555 Fin15AnchoredAtom2607 Fin15AnchoredAtom2747
    Fin15AnchoredAtom3549 Fin15AnchoredAtom3552 Fin15AnchoredAtom3553 Fin15AnchoredAtom3574
    Fin15AnchoredAtom3575 Fin15AnchoredAtom3581 Fin15AnchoredAtom3638 Fin15AnchoredAtom3639
    Fin15AnchoredAtom3645 Fin15AnchoredAtom3697 Fin15AnchoredAtom3758 Fin15AnchoredAtom3759
    Fin15AnchoredAtom3765 Fin15AnchoredAtom3817 Fin15AnchoredAtom3957 Fin15AnchoredAtom4088
    Fin15AnchoredAtom4089 Fin15AnchoredAtom4095 Fin15AnchoredAtom4147 Fin15AnchoredAtom4287
    Fin15AnchoredAtom4497 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31176 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2131 chi ∧
      ¬Fin15AnchoredAtom2132 chi ∧
      ¬Fin15AnchoredAtom2133 chi ∧
      ¬Fin15AnchoredAtom2159 chi ∧
      ¬Fin15AnchoredAtom2160 chi ∧
      ¬Fin15AnchoredAtom2161 chi ∧
      ¬Fin15AnchoredAtom2176 chi ∧
      ¬Fin15AnchoredAtom2177 chi ∧
      ¬Fin15AnchoredAtom2178 chi ∧
      ¬Fin15AnchoredAtom2204 chi ∧
      ¬Fin15AnchoredAtom2205 chi ∧
      ¬Fin15AnchoredAtom2206 chi ∧
      ¬Fin15AnchoredAtom2268 chi ∧
      ¬Fin15AnchoredAtom2269 chi ∧
      ¬Fin15AnchoredAtom2270 chi ∧
      ¬Fin15AnchoredAtom2326 chi ∧
      ¬Fin15AnchoredAtom2341 chi ∧
      ¬Fin15AnchoredAtom2342 chi ∧
      ¬Fin15AnchoredAtom2343 chi ∧
      ¬Fin15AnchoredAtom2369 chi ∧
      ¬Fin15AnchoredAtom2370 chi ∧
      ¬Fin15AnchoredAtom2371 chi ∧
      ¬Fin15AnchoredAtom2433 chi ∧
      ¬Fin15AnchoredAtom2434 chi ∧
      ¬Fin15AnchoredAtom2435 chi ∧
      ¬Fin15AnchoredAtom2491 chi ∧
      ¬Fin15AnchoredAtom2553 chi ∧
      ¬Fin15AnchoredAtom2554 chi ∧
      ¬Fin15AnchoredAtom2555 chi ∧
      ¬Fin15AnchoredAtom2611 chi ∧
      ¬Fin15AnchoredAtom2751 chi ∧
      ¬Fin15AnchoredAtom3551 chi ∧
      ¬Fin15AnchoredAtom3552 chi ∧
      ¬Fin15AnchoredAtom3553 chi ∧
      ¬Fin15AnchoredAtom3579 chi ∧
      ¬Fin15AnchoredAtom3580 chi ∧
      ¬Fin15AnchoredAtom3581 chi ∧
      ¬Fin15AnchoredAtom3643 chi ∧
      ¬Fin15AnchoredAtom3644 chi ∧
      ¬Fin15AnchoredAtom3645 chi ∧
      ¬Fin15AnchoredAtom3701 chi ∧
      ¬Fin15AnchoredAtom3763 chi ∧
      ¬Fin15AnchoredAtom3764 chi ∧
      ¬Fin15AnchoredAtom3765 chi ∧
      ¬Fin15AnchoredAtom3821 chi ∧
      ¬Fin15AnchoredAtom3961 chi ∧
      ¬Fin15AnchoredAtom4093 chi ∧
      ¬Fin15AnchoredAtom4094 chi ∧
      ¬Fin15AnchoredAtom4095 chi ∧
      ¬Fin15AnchoredAtom4151 chi ∧
      ¬Fin15AnchoredAtom4291 chi ∧
      ¬Fin15AnchoredAtom4501 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 6, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask28765
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2108 Fin15AnchoredAtom2114 Fin15AnchoredAtom2115
    Fin15AnchoredAtom2116 Fin15AnchoredAtom2131 Fin15AnchoredAtom2132 Fin15AnchoredAtom2133
    Fin15AnchoredAtom2159 Fin15AnchoredAtom2160 Fin15AnchoredAtom2161 Fin15AnchoredAtom2176
    Fin15AnchoredAtom2177 Fin15AnchoredAtom2178 Fin15AnchoredAtom2204 Fin15AnchoredAtom2205
    Fin15AnchoredAtom2206 Fin15AnchoredAtom2268 Fin15AnchoredAtom2269 Fin15AnchoredAtom2270
    Fin15AnchoredAtom2326 Fin15AnchoredAtom2341 Fin15AnchoredAtom2342 Fin15AnchoredAtom2343
    Fin15AnchoredAtom2369 Fin15AnchoredAtom2370 Fin15AnchoredAtom2371 Fin15AnchoredAtom2433
    Fin15AnchoredAtom2434 Fin15AnchoredAtom2435 Fin15AnchoredAtom2491 Fin15AnchoredAtom2553
    Fin15AnchoredAtom2554 Fin15AnchoredAtom2555 Fin15AnchoredAtom2611 Fin15AnchoredAtom2751
    Fin15AnchoredAtom3551 Fin15AnchoredAtom3552 Fin15AnchoredAtom3553 Fin15AnchoredAtom3579
    Fin15AnchoredAtom3580 Fin15AnchoredAtom3581 Fin15AnchoredAtom3643 Fin15AnchoredAtom3644
    Fin15AnchoredAtom3645 Fin15AnchoredAtom3701 Fin15AnchoredAtom3763 Fin15AnchoredAtom3764
    Fin15AnchoredAtom3765 Fin15AnchoredAtom3821 Fin15AnchoredAtom3961 Fin15AnchoredAtom4093
    Fin15AnchoredAtom4094 Fin15AnchoredAtom4095 Fin15AnchoredAtom4151 Fin15AnchoredAtom4291
    Fin15AnchoredAtom4501 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31177 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2135 chi ∧
      ¬Fin15AnchoredAtom2136 chi ∧
      ¬Fin15AnchoredAtom2138 chi ∧
      ¬Fin15AnchoredAtom2147 chi ∧
      ¬Fin15AnchoredAtom2149 chi ∧
      ¬Fin15AnchoredAtom2153 chi ∧
      ¬Fin15AnchoredAtom2180 chi ∧
      ¬Fin15AnchoredAtom2181 chi ∧
      ¬Fin15AnchoredAtom2183 chi ∧
      ¬Fin15AnchoredAtom2192 chi ∧
      ¬Fin15AnchoredAtom2194 chi ∧
      ¬Fin15AnchoredAtom2198 chi ∧
      ¬Fin15AnchoredAtom2277 chi ∧
      ¬Fin15AnchoredAtom2279 chi ∧
      ¬Fin15AnchoredAtom2283 chi ∧
      ¬Fin15AnchoredAtom2308 chi ∧
      ¬Fin15AnchoredAtom2345 chi ∧
      ¬Fin15AnchoredAtom2346 chi ∧
      ¬Fin15AnchoredAtom2348 chi ∧
      ¬Fin15AnchoredAtom2357 chi ∧
      ¬Fin15AnchoredAtom2359 chi ∧
      ¬Fin15AnchoredAtom2363 chi ∧
      ¬Fin15AnchoredAtom2442 chi ∧
      ¬Fin15AnchoredAtom2444 chi ∧
      ¬Fin15AnchoredAtom2448 chi ∧
      ¬Fin15AnchoredAtom2473 chi ∧
      ¬Fin15AnchoredAtom2562 chi ∧
      ¬Fin15AnchoredAtom2564 chi ∧
      ¬Fin15AnchoredAtom2568 chi ∧
      ¬Fin15AnchoredAtom2593 chi ∧
      ¬Fin15AnchoredAtom2768 chi ∧
      ¬Fin15AnchoredAtom3555 chi ∧
      ¬Fin15AnchoredAtom3556 chi ∧
      ¬Fin15AnchoredAtom3558 chi ∧
      ¬Fin15AnchoredAtom3567 chi ∧
      ¬Fin15AnchoredAtom3569 chi ∧
      ¬Fin15AnchoredAtom3573 chi ∧
      ¬Fin15AnchoredAtom3652 chi ∧
      ¬Fin15AnchoredAtom3654 chi ∧
      ¬Fin15AnchoredAtom3658 chi ∧
      ¬Fin15AnchoredAtom3683 chi ∧
      ¬Fin15AnchoredAtom3772 chi ∧
      ¬Fin15AnchoredAtom3774 chi ∧
      ¬Fin15AnchoredAtom3778 chi ∧
      ¬Fin15AnchoredAtom3803 chi ∧
      ¬Fin15AnchoredAtom3978 chi ∧
      ¬Fin15AnchoredAtom4102 chi ∧
      ¬Fin15AnchoredAtom4104 chi ∧
      ¬Fin15AnchoredAtom4108 chi ∧
      ¬Fin15AnchoredAtom4133 chi ∧
      ¬Fin15AnchoredAtom4308 chi ∧
      ¬Fin15AnchoredAtom4518 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 7, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05789
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2109 Fin15AnchoredAtom2111 Fin15AnchoredAtom2112
    Fin15AnchoredAtom2114 Fin15AnchoredAtom2135 Fin15AnchoredAtom2136 Fin15AnchoredAtom2138
    Fin15AnchoredAtom2147 Fin15AnchoredAtom2149 Fin15AnchoredAtom2153 Fin15AnchoredAtom2180
    Fin15AnchoredAtom2181 Fin15AnchoredAtom2183 Fin15AnchoredAtom2192 Fin15AnchoredAtom2194
    Fin15AnchoredAtom2198 Fin15AnchoredAtom2277 Fin15AnchoredAtom2279 Fin15AnchoredAtom2283
    Fin15AnchoredAtom2308 Fin15AnchoredAtom2345 Fin15AnchoredAtom2346 Fin15AnchoredAtom2348
    Fin15AnchoredAtom2357 Fin15AnchoredAtom2359 Fin15AnchoredAtom2363 Fin15AnchoredAtom2442
    Fin15AnchoredAtom2444 Fin15AnchoredAtom2448 Fin15AnchoredAtom2473 Fin15AnchoredAtom2562
    Fin15AnchoredAtom2564 Fin15AnchoredAtom2568 Fin15AnchoredAtom2593 Fin15AnchoredAtom2768
    Fin15AnchoredAtom3555 Fin15AnchoredAtom3556 Fin15AnchoredAtom3558 Fin15AnchoredAtom3567
    Fin15AnchoredAtom3569 Fin15AnchoredAtom3573 Fin15AnchoredAtom3652 Fin15AnchoredAtom3654
    Fin15AnchoredAtom3658 Fin15AnchoredAtom3683 Fin15AnchoredAtom3772 Fin15AnchoredAtom3774
    Fin15AnchoredAtom3778 Fin15AnchoredAtom3803 Fin15AnchoredAtom3978 Fin15AnchoredAtom4102
    Fin15AnchoredAtom4104 Fin15AnchoredAtom4108 Fin15AnchoredAtom4133 Fin15AnchoredAtom4308
    Fin15AnchoredAtom4518 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31178 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2135 chi ∧
      ¬Fin15AnchoredAtom2136 chi ∧
      ¬Fin15AnchoredAtom2139 chi ∧
      ¬Fin15AnchoredAtom2147 chi ∧
      ¬Fin15AnchoredAtom2150 chi ∧
      ¬Fin15AnchoredAtom2154 chi ∧
      ¬Fin15AnchoredAtom2180 chi ∧
      ¬Fin15AnchoredAtom2181 chi ∧
      ¬Fin15AnchoredAtom2184 chi ∧
      ¬Fin15AnchoredAtom2192 chi ∧
      ¬Fin15AnchoredAtom2195 chi ∧
      ¬Fin15AnchoredAtom2199 chi ∧
      ¬Fin15AnchoredAtom2277 chi ∧
      ¬Fin15AnchoredAtom2280 chi ∧
      ¬Fin15AnchoredAtom2284 chi ∧
      ¬Fin15AnchoredAtom2309 chi ∧
      ¬Fin15AnchoredAtom2345 chi ∧
      ¬Fin15AnchoredAtom2346 chi ∧
      ¬Fin15AnchoredAtom2349 chi ∧
      ¬Fin15AnchoredAtom2357 chi ∧
      ¬Fin15AnchoredAtom2360 chi ∧
      ¬Fin15AnchoredAtom2364 chi ∧
      ¬Fin15AnchoredAtom2442 chi ∧
      ¬Fin15AnchoredAtom2445 chi ∧
      ¬Fin15AnchoredAtom2449 chi ∧
      ¬Fin15AnchoredAtom2474 chi ∧
      ¬Fin15AnchoredAtom2562 chi ∧
      ¬Fin15AnchoredAtom2565 chi ∧
      ¬Fin15AnchoredAtom2569 chi ∧
      ¬Fin15AnchoredAtom2594 chi ∧
      ¬Fin15AnchoredAtom2769 chi ∧
      ¬Fin15AnchoredAtom3555 chi ∧
      ¬Fin15AnchoredAtom3556 chi ∧
      ¬Fin15AnchoredAtom3559 chi ∧
      ¬Fin15AnchoredAtom3567 chi ∧
      ¬Fin15AnchoredAtom3570 chi ∧
      ¬Fin15AnchoredAtom3574 chi ∧
      ¬Fin15AnchoredAtom3652 chi ∧
      ¬Fin15AnchoredAtom3655 chi ∧
      ¬Fin15AnchoredAtom3659 chi ∧
      ¬Fin15AnchoredAtom3684 chi ∧
      ¬Fin15AnchoredAtom3772 chi ∧
      ¬Fin15AnchoredAtom3775 chi ∧
      ¬Fin15AnchoredAtom3779 chi ∧
      ¬Fin15AnchoredAtom3804 chi ∧
      ¬Fin15AnchoredAtom3979 chi ∧
      ¬Fin15AnchoredAtom4102 chi ∧
      ¬Fin15AnchoredAtom4105 chi ∧
      ¬Fin15AnchoredAtom4109 chi ∧
      ¬Fin15AnchoredAtom4134 chi ∧
      ¬Fin15AnchoredAtom4309 chi ∧
      ¬Fin15AnchoredAtom4519 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 7, 9, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09885
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2109 Fin15AnchoredAtom2111 Fin15AnchoredAtom2112
    Fin15AnchoredAtom2115 Fin15AnchoredAtom2135 Fin15AnchoredAtom2136 Fin15AnchoredAtom2139
    Fin15AnchoredAtom2147 Fin15AnchoredAtom2150 Fin15AnchoredAtom2154 Fin15AnchoredAtom2180
    Fin15AnchoredAtom2181 Fin15AnchoredAtom2184 Fin15AnchoredAtom2192 Fin15AnchoredAtom2195
    Fin15AnchoredAtom2199 Fin15AnchoredAtom2277 Fin15AnchoredAtom2280 Fin15AnchoredAtom2284
    Fin15AnchoredAtom2309 Fin15AnchoredAtom2345 Fin15AnchoredAtom2346 Fin15AnchoredAtom2349
    Fin15AnchoredAtom2357 Fin15AnchoredAtom2360 Fin15AnchoredAtom2364 Fin15AnchoredAtom2442
    Fin15AnchoredAtom2445 Fin15AnchoredAtom2449 Fin15AnchoredAtom2474 Fin15AnchoredAtom2562
    Fin15AnchoredAtom2565 Fin15AnchoredAtom2569 Fin15AnchoredAtom2594 Fin15AnchoredAtom2769
    Fin15AnchoredAtom3555 Fin15AnchoredAtom3556 Fin15AnchoredAtom3559 Fin15AnchoredAtom3567
    Fin15AnchoredAtom3570 Fin15AnchoredAtom3574 Fin15AnchoredAtom3652 Fin15AnchoredAtom3655
    Fin15AnchoredAtom3659 Fin15AnchoredAtom3684 Fin15AnchoredAtom3772 Fin15AnchoredAtom3775
    Fin15AnchoredAtom3779 Fin15AnchoredAtom3804 Fin15AnchoredAtom3979 Fin15AnchoredAtom4102
    Fin15AnchoredAtom4105 Fin15AnchoredAtom4109 Fin15AnchoredAtom4134 Fin15AnchoredAtom4309
    Fin15AnchoredAtom4519 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31179 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2135 chi ∧
      ¬Fin15AnchoredAtom2136 chi ∧
      ¬Fin15AnchoredAtom2140 chi ∧
      ¬Fin15AnchoredAtom2147 chi ∧
      ¬Fin15AnchoredAtom2151 chi ∧
      ¬Fin15AnchoredAtom2155 chi ∧
      ¬Fin15AnchoredAtom2180 chi ∧
      ¬Fin15AnchoredAtom2181 chi ∧
      ¬Fin15AnchoredAtom2185 chi ∧
      ¬Fin15AnchoredAtom2192 chi ∧
      ¬Fin15AnchoredAtom2196 chi ∧
      ¬Fin15AnchoredAtom2200 chi ∧
      ¬Fin15AnchoredAtom2277 chi ∧
      ¬Fin15AnchoredAtom2281 chi ∧
      ¬Fin15AnchoredAtom2285 chi ∧
      ¬Fin15AnchoredAtom2310 chi ∧
      ¬Fin15AnchoredAtom2345 chi ∧
      ¬Fin15AnchoredAtom2346 chi ∧
      ¬Fin15AnchoredAtom2350 chi ∧
      ¬Fin15AnchoredAtom2357 chi ∧
      ¬Fin15AnchoredAtom2361 chi ∧
      ¬Fin15AnchoredAtom2365 chi ∧
      ¬Fin15AnchoredAtom2442 chi ∧
      ¬Fin15AnchoredAtom2446 chi ∧
      ¬Fin15AnchoredAtom2450 chi ∧
      ¬Fin15AnchoredAtom2475 chi ∧
      ¬Fin15AnchoredAtom2562 chi ∧
      ¬Fin15AnchoredAtom2566 chi ∧
      ¬Fin15AnchoredAtom2570 chi ∧
      ¬Fin15AnchoredAtom2595 chi ∧
      ¬Fin15AnchoredAtom2770 chi ∧
      ¬Fin15AnchoredAtom3555 chi ∧
      ¬Fin15AnchoredAtom3556 chi ∧
      ¬Fin15AnchoredAtom3560 chi ∧
      ¬Fin15AnchoredAtom3567 chi ∧
      ¬Fin15AnchoredAtom3571 chi ∧
      ¬Fin15AnchoredAtom3575 chi ∧
      ¬Fin15AnchoredAtom3652 chi ∧
      ¬Fin15AnchoredAtom3656 chi ∧
      ¬Fin15AnchoredAtom3660 chi ∧
      ¬Fin15AnchoredAtom3685 chi ∧
      ¬Fin15AnchoredAtom3772 chi ∧
      ¬Fin15AnchoredAtom3776 chi ∧
      ¬Fin15AnchoredAtom3780 chi ∧
      ¬Fin15AnchoredAtom3805 chi ∧
      ¬Fin15AnchoredAtom3980 chi ∧
      ¬Fin15AnchoredAtom4102 chi ∧
      ¬Fin15AnchoredAtom4106 chi ∧
      ¬Fin15AnchoredAtom4110 chi ∧
      ¬Fin15AnchoredAtom4135 chi ∧
      ¬Fin15AnchoredAtom4310 chi ∧
      ¬Fin15AnchoredAtom4520 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 7, 9, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask18077
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2109 Fin15AnchoredAtom2111 Fin15AnchoredAtom2112
    Fin15AnchoredAtom2116 Fin15AnchoredAtom2135 Fin15AnchoredAtom2136 Fin15AnchoredAtom2140
    Fin15AnchoredAtom2147 Fin15AnchoredAtom2151 Fin15AnchoredAtom2155 Fin15AnchoredAtom2180
    Fin15AnchoredAtom2181 Fin15AnchoredAtom2185 Fin15AnchoredAtom2192 Fin15AnchoredAtom2196
    Fin15AnchoredAtom2200 Fin15AnchoredAtom2277 Fin15AnchoredAtom2281 Fin15AnchoredAtom2285
    Fin15AnchoredAtom2310 Fin15AnchoredAtom2345 Fin15AnchoredAtom2346 Fin15AnchoredAtom2350
    Fin15AnchoredAtom2357 Fin15AnchoredAtom2361 Fin15AnchoredAtom2365 Fin15AnchoredAtom2442
    Fin15AnchoredAtom2446 Fin15AnchoredAtom2450 Fin15AnchoredAtom2475 Fin15AnchoredAtom2562
    Fin15AnchoredAtom2566 Fin15AnchoredAtom2570 Fin15AnchoredAtom2595 Fin15AnchoredAtom2770
    Fin15AnchoredAtom3555 Fin15AnchoredAtom3556 Fin15AnchoredAtom3560 Fin15AnchoredAtom3567
    Fin15AnchoredAtom3571 Fin15AnchoredAtom3575 Fin15AnchoredAtom3652 Fin15AnchoredAtom3656
    Fin15AnchoredAtom3660 Fin15AnchoredAtom3685 Fin15AnchoredAtom3772 Fin15AnchoredAtom3776
    Fin15AnchoredAtom3780 Fin15AnchoredAtom3805 Fin15AnchoredAtom3980 Fin15AnchoredAtom4102
    Fin15AnchoredAtom4106 Fin15AnchoredAtom4110 Fin15AnchoredAtom4135 Fin15AnchoredAtom4310
    Fin15AnchoredAtom4520 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31180 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2135 chi ∧
      ¬Fin15AnchoredAtom2138 chi ∧
      ¬Fin15AnchoredAtom2139 chi ∧
      ¬Fin15AnchoredAtom2149 chi ∧
      ¬Fin15AnchoredAtom2150 chi ∧
      ¬Fin15AnchoredAtom2159 chi ∧
      ¬Fin15AnchoredAtom2180 chi ∧
      ¬Fin15AnchoredAtom2183 chi ∧
      ¬Fin15AnchoredAtom2184 chi ∧
      ¬Fin15AnchoredAtom2194 chi ∧
      ¬Fin15AnchoredAtom2195 chi ∧
      ¬Fin15AnchoredAtom2204 chi ∧
      ¬Fin15AnchoredAtom2279 chi ∧
      ¬Fin15AnchoredAtom2280 chi ∧
      ¬Fin15AnchoredAtom2289 chi ∧
      ¬Fin15AnchoredAtom2314 chi ∧
      ¬Fin15AnchoredAtom2345 chi ∧
      ¬Fin15AnchoredAtom2348 chi ∧
      ¬Fin15AnchoredAtom2349 chi ∧
      ¬Fin15AnchoredAtom2359 chi ∧
      ¬Fin15AnchoredAtom2360 chi ∧
      ¬Fin15AnchoredAtom2369 chi ∧
      ¬Fin15AnchoredAtom2444 chi ∧
      ¬Fin15AnchoredAtom2445 chi ∧
      ¬Fin15AnchoredAtom2454 chi ∧
      ¬Fin15AnchoredAtom2479 chi ∧
      ¬Fin15AnchoredAtom2564 chi ∧
      ¬Fin15AnchoredAtom2565 chi ∧
      ¬Fin15AnchoredAtom2574 chi ∧
      ¬Fin15AnchoredAtom2599 chi ∧
      ¬Fin15AnchoredAtom2774 chi ∧
      ¬Fin15AnchoredAtom3555 chi ∧
      ¬Fin15AnchoredAtom3558 chi ∧
      ¬Fin15AnchoredAtom3559 chi ∧
      ¬Fin15AnchoredAtom3569 chi ∧
      ¬Fin15AnchoredAtom3570 chi ∧
      ¬Fin15AnchoredAtom3579 chi ∧
      ¬Fin15AnchoredAtom3654 chi ∧
      ¬Fin15AnchoredAtom3655 chi ∧
      ¬Fin15AnchoredAtom3664 chi ∧
      ¬Fin15AnchoredAtom3689 chi ∧
      ¬Fin15AnchoredAtom3774 chi ∧
      ¬Fin15AnchoredAtom3775 chi ∧
      ¬Fin15AnchoredAtom3784 chi ∧
      ¬Fin15AnchoredAtom3809 chi ∧
      ¬Fin15AnchoredAtom3984 chi ∧
      ¬Fin15AnchoredAtom4104 chi ∧
      ¬Fin15AnchoredAtom4105 chi ∧
      ¬Fin15AnchoredAtom4114 chi ∧
      ¬Fin15AnchoredAtom4139 chi ∧
      ¬Fin15AnchoredAtom4314 chi ∧
      ¬Fin15AnchoredAtom4524 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 7, 9, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask12957
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2109 Fin15AnchoredAtom2111 Fin15AnchoredAtom2114
    Fin15AnchoredAtom2115 Fin15AnchoredAtom2135 Fin15AnchoredAtom2138 Fin15AnchoredAtom2139
    Fin15AnchoredAtom2149 Fin15AnchoredAtom2150 Fin15AnchoredAtom2159 Fin15AnchoredAtom2180
    Fin15AnchoredAtom2183 Fin15AnchoredAtom2184 Fin15AnchoredAtom2194 Fin15AnchoredAtom2195
    Fin15AnchoredAtom2204 Fin15AnchoredAtom2279 Fin15AnchoredAtom2280 Fin15AnchoredAtom2289
    Fin15AnchoredAtom2314 Fin15AnchoredAtom2345 Fin15AnchoredAtom2348 Fin15AnchoredAtom2349
    Fin15AnchoredAtom2359 Fin15AnchoredAtom2360 Fin15AnchoredAtom2369 Fin15AnchoredAtom2444
    Fin15AnchoredAtom2445 Fin15AnchoredAtom2454 Fin15AnchoredAtom2479 Fin15AnchoredAtom2564
    Fin15AnchoredAtom2565 Fin15AnchoredAtom2574 Fin15AnchoredAtom2599 Fin15AnchoredAtom2774
    Fin15AnchoredAtom3555 Fin15AnchoredAtom3558 Fin15AnchoredAtom3559 Fin15AnchoredAtom3569
    Fin15AnchoredAtom3570 Fin15AnchoredAtom3579 Fin15AnchoredAtom3654 Fin15AnchoredAtom3655
    Fin15AnchoredAtom3664 Fin15AnchoredAtom3689 Fin15AnchoredAtom3774 Fin15AnchoredAtom3775
    Fin15AnchoredAtom3784 Fin15AnchoredAtom3809 Fin15AnchoredAtom3984 Fin15AnchoredAtom4104
    Fin15AnchoredAtom4105 Fin15AnchoredAtom4114 Fin15AnchoredAtom4139 Fin15AnchoredAtom4314
    Fin15AnchoredAtom4524 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31181 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2135 chi ∧
      ¬Fin15AnchoredAtom2138 chi ∧
      ¬Fin15AnchoredAtom2140 chi ∧
      ¬Fin15AnchoredAtom2149 chi ∧
      ¬Fin15AnchoredAtom2151 chi ∧
      ¬Fin15AnchoredAtom2160 chi ∧
      ¬Fin15AnchoredAtom2180 chi ∧
      ¬Fin15AnchoredAtom2183 chi ∧
      ¬Fin15AnchoredAtom2185 chi ∧
      ¬Fin15AnchoredAtom2194 chi ∧
      ¬Fin15AnchoredAtom2196 chi ∧
      ¬Fin15AnchoredAtom2205 chi ∧
      ¬Fin15AnchoredAtom2279 chi ∧
      ¬Fin15AnchoredAtom2281 chi ∧
      ¬Fin15AnchoredAtom2290 chi ∧
      ¬Fin15AnchoredAtom2315 chi ∧
      ¬Fin15AnchoredAtom2345 chi ∧
      ¬Fin15AnchoredAtom2348 chi ∧
      ¬Fin15AnchoredAtom2350 chi ∧
      ¬Fin15AnchoredAtom2359 chi ∧
      ¬Fin15AnchoredAtom2361 chi ∧
      ¬Fin15AnchoredAtom2370 chi ∧
      ¬Fin15AnchoredAtom2444 chi ∧
      ¬Fin15AnchoredAtom2446 chi ∧
      ¬Fin15AnchoredAtom2455 chi ∧
      ¬Fin15AnchoredAtom2480 chi ∧
      ¬Fin15AnchoredAtom2564 chi ∧
      ¬Fin15AnchoredAtom2566 chi ∧
      ¬Fin15AnchoredAtom2575 chi ∧
      ¬Fin15AnchoredAtom2600 chi ∧
      ¬Fin15AnchoredAtom2775 chi ∧
      ¬Fin15AnchoredAtom3555 chi ∧
      ¬Fin15AnchoredAtom3558 chi ∧
      ¬Fin15AnchoredAtom3560 chi ∧
      ¬Fin15AnchoredAtom3569 chi ∧
      ¬Fin15AnchoredAtom3571 chi ∧
      ¬Fin15AnchoredAtom3580 chi ∧
      ¬Fin15AnchoredAtom3654 chi ∧
      ¬Fin15AnchoredAtom3656 chi ∧
      ¬Fin15AnchoredAtom3665 chi ∧
      ¬Fin15AnchoredAtom3690 chi ∧
      ¬Fin15AnchoredAtom3774 chi ∧
      ¬Fin15AnchoredAtom3776 chi ∧
      ¬Fin15AnchoredAtom3785 chi ∧
      ¬Fin15AnchoredAtom3810 chi ∧
      ¬Fin15AnchoredAtom3985 chi ∧
      ¬Fin15AnchoredAtom4104 chi ∧
      ¬Fin15AnchoredAtom4106 chi ∧
      ¬Fin15AnchoredAtom4115 chi ∧
      ¬Fin15AnchoredAtom4140 chi ∧
      ¬Fin15AnchoredAtom4315 chi ∧
      ¬Fin15AnchoredAtom4525 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 7, 9, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21149
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2109 Fin15AnchoredAtom2111 Fin15AnchoredAtom2114
    Fin15AnchoredAtom2116 Fin15AnchoredAtom2135 Fin15AnchoredAtom2138 Fin15AnchoredAtom2140
    Fin15AnchoredAtom2149 Fin15AnchoredAtom2151 Fin15AnchoredAtom2160 Fin15AnchoredAtom2180
    Fin15AnchoredAtom2183 Fin15AnchoredAtom2185 Fin15AnchoredAtom2194 Fin15AnchoredAtom2196
    Fin15AnchoredAtom2205 Fin15AnchoredAtom2279 Fin15AnchoredAtom2281 Fin15AnchoredAtom2290
    Fin15AnchoredAtom2315 Fin15AnchoredAtom2345 Fin15AnchoredAtom2348 Fin15AnchoredAtom2350
    Fin15AnchoredAtom2359 Fin15AnchoredAtom2361 Fin15AnchoredAtom2370 Fin15AnchoredAtom2444
    Fin15AnchoredAtom2446 Fin15AnchoredAtom2455 Fin15AnchoredAtom2480 Fin15AnchoredAtom2564
    Fin15AnchoredAtom2566 Fin15AnchoredAtom2575 Fin15AnchoredAtom2600 Fin15AnchoredAtom2775
    Fin15AnchoredAtom3555 Fin15AnchoredAtom3558 Fin15AnchoredAtom3560 Fin15AnchoredAtom3569
    Fin15AnchoredAtom3571 Fin15AnchoredAtom3580 Fin15AnchoredAtom3654 Fin15AnchoredAtom3656
    Fin15AnchoredAtom3665 Fin15AnchoredAtom3690 Fin15AnchoredAtom3774 Fin15AnchoredAtom3776
    Fin15AnchoredAtom3785 Fin15AnchoredAtom3810 Fin15AnchoredAtom3985 Fin15AnchoredAtom4104
    Fin15AnchoredAtom4106 Fin15AnchoredAtom4115 Fin15AnchoredAtom4140 Fin15AnchoredAtom4315
    Fin15AnchoredAtom4525 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31182 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2135 chi ∧
      ¬Fin15AnchoredAtom2139 chi ∧
      ¬Fin15AnchoredAtom2140 chi ∧
      ¬Fin15AnchoredAtom2150 chi ∧
      ¬Fin15AnchoredAtom2151 chi ∧
      ¬Fin15AnchoredAtom2161 chi ∧
      ¬Fin15AnchoredAtom2180 chi ∧
      ¬Fin15AnchoredAtom2184 chi ∧
      ¬Fin15AnchoredAtom2185 chi ∧
      ¬Fin15AnchoredAtom2195 chi ∧
      ¬Fin15AnchoredAtom2196 chi ∧
      ¬Fin15AnchoredAtom2206 chi ∧
      ¬Fin15AnchoredAtom2280 chi ∧
      ¬Fin15AnchoredAtom2281 chi ∧
      ¬Fin15AnchoredAtom2291 chi ∧
      ¬Fin15AnchoredAtom2316 chi ∧
      ¬Fin15AnchoredAtom2345 chi ∧
      ¬Fin15AnchoredAtom2349 chi ∧
      ¬Fin15AnchoredAtom2350 chi ∧
      ¬Fin15AnchoredAtom2360 chi ∧
      ¬Fin15AnchoredAtom2361 chi ∧
      ¬Fin15AnchoredAtom2371 chi ∧
      ¬Fin15AnchoredAtom2445 chi ∧
      ¬Fin15AnchoredAtom2446 chi ∧
      ¬Fin15AnchoredAtom2456 chi ∧
      ¬Fin15AnchoredAtom2481 chi ∧
      ¬Fin15AnchoredAtom2565 chi ∧
      ¬Fin15AnchoredAtom2566 chi ∧
      ¬Fin15AnchoredAtom2576 chi ∧
      ¬Fin15AnchoredAtom2601 chi ∧
      ¬Fin15AnchoredAtom2776 chi ∧
      ¬Fin15AnchoredAtom3555 chi ∧
      ¬Fin15AnchoredAtom3559 chi ∧
      ¬Fin15AnchoredAtom3560 chi ∧
      ¬Fin15AnchoredAtom3570 chi ∧
      ¬Fin15AnchoredAtom3571 chi ∧
      ¬Fin15AnchoredAtom3581 chi ∧
      ¬Fin15AnchoredAtom3655 chi ∧
      ¬Fin15AnchoredAtom3656 chi ∧
      ¬Fin15AnchoredAtom3666 chi ∧
      ¬Fin15AnchoredAtom3691 chi ∧
      ¬Fin15AnchoredAtom3775 chi ∧
      ¬Fin15AnchoredAtom3776 chi ∧
      ¬Fin15AnchoredAtom3786 chi ∧
      ¬Fin15AnchoredAtom3811 chi ∧
      ¬Fin15AnchoredAtom3986 chi ∧
      ¬Fin15AnchoredAtom4105 chi ∧
      ¬Fin15AnchoredAtom4106 chi ∧
      ¬Fin15AnchoredAtom4116 chi ∧
      ¬Fin15AnchoredAtom4141 chi ∧
      ¬Fin15AnchoredAtom4316 chi ∧
      ¬Fin15AnchoredAtom4526 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 7, 9, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25245
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2109 Fin15AnchoredAtom2111 Fin15AnchoredAtom2115
    Fin15AnchoredAtom2116 Fin15AnchoredAtom2135 Fin15AnchoredAtom2139 Fin15AnchoredAtom2140
    Fin15AnchoredAtom2150 Fin15AnchoredAtom2151 Fin15AnchoredAtom2161 Fin15AnchoredAtom2180
    Fin15AnchoredAtom2184 Fin15AnchoredAtom2185 Fin15AnchoredAtom2195 Fin15AnchoredAtom2196
    Fin15AnchoredAtom2206 Fin15AnchoredAtom2280 Fin15AnchoredAtom2281 Fin15AnchoredAtom2291
    Fin15AnchoredAtom2316 Fin15AnchoredAtom2345 Fin15AnchoredAtom2349 Fin15AnchoredAtom2350
    Fin15AnchoredAtom2360 Fin15AnchoredAtom2361 Fin15AnchoredAtom2371 Fin15AnchoredAtom2445
    Fin15AnchoredAtom2446 Fin15AnchoredAtom2456 Fin15AnchoredAtom2481 Fin15AnchoredAtom2565
    Fin15AnchoredAtom2566 Fin15AnchoredAtom2576 Fin15AnchoredAtom2601 Fin15AnchoredAtom2776
    Fin15AnchoredAtom3555 Fin15AnchoredAtom3559 Fin15AnchoredAtom3560 Fin15AnchoredAtom3570
    Fin15AnchoredAtom3571 Fin15AnchoredAtom3581 Fin15AnchoredAtom3655 Fin15AnchoredAtom3656
    Fin15AnchoredAtom3666 Fin15AnchoredAtom3691 Fin15AnchoredAtom3775 Fin15AnchoredAtom3776
    Fin15AnchoredAtom3786 Fin15AnchoredAtom3811 Fin15AnchoredAtom3986 Fin15AnchoredAtom4105
    Fin15AnchoredAtom4106 Fin15AnchoredAtom4116 Fin15AnchoredAtom4141 Fin15AnchoredAtom4316
    Fin15AnchoredAtom4526 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31183 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2136 chi ∧
      ¬Fin15AnchoredAtom2138 chi ∧
      ¬Fin15AnchoredAtom2139 chi ∧
      ¬Fin15AnchoredAtom2153 chi ∧
      ¬Fin15AnchoredAtom2154 chi ∧
      ¬Fin15AnchoredAtom2159 chi ∧
      ¬Fin15AnchoredAtom2181 chi ∧
      ¬Fin15AnchoredAtom2183 chi ∧
      ¬Fin15AnchoredAtom2184 chi ∧
      ¬Fin15AnchoredAtom2198 chi ∧
      ¬Fin15AnchoredAtom2199 chi ∧
      ¬Fin15AnchoredAtom2204 chi ∧
      ¬Fin15AnchoredAtom2283 chi ∧
      ¬Fin15AnchoredAtom2284 chi ∧
      ¬Fin15AnchoredAtom2289 chi ∧
      ¬Fin15AnchoredAtom2320 chi ∧
      ¬Fin15AnchoredAtom2346 chi ∧
      ¬Fin15AnchoredAtom2348 chi ∧
      ¬Fin15AnchoredAtom2349 chi ∧
      ¬Fin15AnchoredAtom2363 chi ∧
      ¬Fin15AnchoredAtom2364 chi ∧
      ¬Fin15AnchoredAtom2369 chi ∧
      ¬Fin15AnchoredAtom2448 chi ∧
      ¬Fin15AnchoredAtom2449 chi ∧
      ¬Fin15AnchoredAtom2454 chi ∧
      ¬Fin15AnchoredAtom2485 chi ∧
      ¬Fin15AnchoredAtom2568 chi ∧
      ¬Fin15AnchoredAtom2569 chi ∧
      ¬Fin15AnchoredAtom2574 chi ∧
      ¬Fin15AnchoredAtom2605 chi ∧
      ¬Fin15AnchoredAtom2780 chi ∧
      ¬Fin15AnchoredAtom3556 chi ∧
      ¬Fin15AnchoredAtom3558 chi ∧
      ¬Fin15AnchoredAtom3559 chi ∧
      ¬Fin15AnchoredAtom3573 chi ∧
      ¬Fin15AnchoredAtom3574 chi ∧
      ¬Fin15AnchoredAtom3579 chi ∧
      ¬Fin15AnchoredAtom3658 chi ∧
      ¬Fin15AnchoredAtom3659 chi ∧
      ¬Fin15AnchoredAtom3664 chi ∧
      ¬Fin15AnchoredAtom3695 chi ∧
      ¬Fin15AnchoredAtom3778 chi ∧
      ¬Fin15AnchoredAtom3779 chi ∧
      ¬Fin15AnchoredAtom3784 chi ∧
      ¬Fin15AnchoredAtom3815 chi ∧
      ¬Fin15AnchoredAtom3990 chi ∧
      ¬Fin15AnchoredAtom4108 chi ∧
      ¬Fin15AnchoredAtom4109 chi ∧
      ¬Fin15AnchoredAtom4114 chi ∧
      ¬Fin15AnchoredAtom4145 chi ∧
      ¬Fin15AnchoredAtom4320 chi ∧
      ¬Fin15AnchoredAtom4530 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 7, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13469
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2109 Fin15AnchoredAtom2112 Fin15AnchoredAtom2114
    Fin15AnchoredAtom2115 Fin15AnchoredAtom2136 Fin15AnchoredAtom2138 Fin15AnchoredAtom2139
    Fin15AnchoredAtom2153 Fin15AnchoredAtom2154 Fin15AnchoredAtom2159 Fin15AnchoredAtom2181
    Fin15AnchoredAtom2183 Fin15AnchoredAtom2184 Fin15AnchoredAtom2198 Fin15AnchoredAtom2199
    Fin15AnchoredAtom2204 Fin15AnchoredAtom2283 Fin15AnchoredAtom2284 Fin15AnchoredAtom2289
    Fin15AnchoredAtom2320 Fin15AnchoredAtom2346 Fin15AnchoredAtom2348 Fin15AnchoredAtom2349
    Fin15AnchoredAtom2363 Fin15AnchoredAtom2364 Fin15AnchoredAtom2369 Fin15AnchoredAtom2448
    Fin15AnchoredAtom2449 Fin15AnchoredAtom2454 Fin15AnchoredAtom2485 Fin15AnchoredAtom2568
    Fin15AnchoredAtom2569 Fin15AnchoredAtom2574 Fin15AnchoredAtom2605 Fin15AnchoredAtom2780
    Fin15AnchoredAtom3556 Fin15AnchoredAtom3558 Fin15AnchoredAtom3559 Fin15AnchoredAtom3573
    Fin15AnchoredAtom3574 Fin15AnchoredAtom3579 Fin15AnchoredAtom3658 Fin15AnchoredAtom3659
    Fin15AnchoredAtom3664 Fin15AnchoredAtom3695 Fin15AnchoredAtom3778 Fin15AnchoredAtom3779
    Fin15AnchoredAtom3784 Fin15AnchoredAtom3815 Fin15AnchoredAtom3990 Fin15AnchoredAtom4108
    Fin15AnchoredAtom4109 Fin15AnchoredAtom4114 Fin15AnchoredAtom4145 Fin15AnchoredAtom4320
    Fin15AnchoredAtom4530 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31184 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2136 chi ∧
      ¬Fin15AnchoredAtom2138 chi ∧
      ¬Fin15AnchoredAtom2140 chi ∧
      ¬Fin15AnchoredAtom2153 chi ∧
      ¬Fin15AnchoredAtom2155 chi ∧
      ¬Fin15AnchoredAtom2160 chi ∧
      ¬Fin15AnchoredAtom2181 chi ∧
      ¬Fin15AnchoredAtom2183 chi ∧
      ¬Fin15AnchoredAtom2185 chi ∧
      ¬Fin15AnchoredAtom2198 chi ∧
      ¬Fin15AnchoredAtom2200 chi ∧
      ¬Fin15AnchoredAtom2205 chi ∧
      ¬Fin15AnchoredAtom2283 chi ∧
      ¬Fin15AnchoredAtom2285 chi ∧
      ¬Fin15AnchoredAtom2290 chi ∧
      ¬Fin15AnchoredAtom2321 chi ∧
      ¬Fin15AnchoredAtom2346 chi ∧
      ¬Fin15AnchoredAtom2348 chi ∧
      ¬Fin15AnchoredAtom2350 chi ∧
      ¬Fin15AnchoredAtom2363 chi ∧
      ¬Fin15AnchoredAtom2365 chi ∧
      ¬Fin15AnchoredAtom2370 chi ∧
      ¬Fin15AnchoredAtom2448 chi ∧
      ¬Fin15AnchoredAtom2450 chi ∧
      ¬Fin15AnchoredAtom2455 chi ∧
      ¬Fin15AnchoredAtom2486 chi ∧
      ¬Fin15AnchoredAtom2568 chi ∧
      ¬Fin15AnchoredAtom2570 chi ∧
      ¬Fin15AnchoredAtom2575 chi ∧
      ¬Fin15AnchoredAtom2606 chi ∧
      ¬Fin15AnchoredAtom2781 chi ∧
      ¬Fin15AnchoredAtom3556 chi ∧
      ¬Fin15AnchoredAtom3558 chi ∧
      ¬Fin15AnchoredAtom3560 chi ∧
      ¬Fin15AnchoredAtom3573 chi ∧
      ¬Fin15AnchoredAtom3575 chi ∧
      ¬Fin15AnchoredAtom3580 chi ∧
      ¬Fin15AnchoredAtom3658 chi ∧
      ¬Fin15AnchoredAtom3660 chi ∧
      ¬Fin15AnchoredAtom3665 chi ∧
      ¬Fin15AnchoredAtom3696 chi ∧
      ¬Fin15AnchoredAtom3778 chi ∧
      ¬Fin15AnchoredAtom3780 chi ∧
      ¬Fin15AnchoredAtom3785 chi ∧
      ¬Fin15AnchoredAtom3816 chi ∧
      ¬Fin15AnchoredAtom3991 chi ∧
      ¬Fin15AnchoredAtom4108 chi ∧
      ¬Fin15AnchoredAtom4110 chi ∧
      ¬Fin15AnchoredAtom4115 chi ∧
      ¬Fin15AnchoredAtom4146 chi ∧
      ¬Fin15AnchoredAtom4321 chi ∧
      ¬Fin15AnchoredAtom4531 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 7, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21661
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2109 Fin15AnchoredAtom2112 Fin15AnchoredAtom2114
    Fin15AnchoredAtom2116 Fin15AnchoredAtom2136 Fin15AnchoredAtom2138 Fin15AnchoredAtom2140
    Fin15AnchoredAtom2153 Fin15AnchoredAtom2155 Fin15AnchoredAtom2160 Fin15AnchoredAtom2181
    Fin15AnchoredAtom2183 Fin15AnchoredAtom2185 Fin15AnchoredAtom2198 Fin15AnchoredAtom2200
    Fin15AnchoredAtom2205 Fin15AnchoredAtom2283 Fin15AnchoredAtom2285 Fin15AnchoredAtom2290
    Fin15AnchoredAtom2321 Fin15AnchoredAtom2346 Fin15AnchoredAtom2348 Fin15AnchoredAtom2350
    Fin15AnchoredAtom2363 Fin15AnchoredAtom2365 Fin15AnchoredAtom2370 Fin15AnchoredAtom2448
    Fin15AnchoredAtom2450 Fin15AnchoredAtom2455 Fin15AnchoredAtom2486 Fin15AnchoredAtom2568
    Fin15AnchoredAtom2570 Fin15AnchoredAtom2575 Fin15AnchoredAtom2606 Fin15AnchoredAtom2781
    Fin15AnchoredAtom3556 Fin15AnchoredAtom3558 Fin15AnchoredAtom3560 Fin15AnchoredAtom3573
    Fin15AnchoredAtom3575 Fin15AnchoredAtom3580 Fin15AnchoredAtom3658 Fin15AnchoredAtom3660
    Fin15AnchoredAtom3665 Fin15AnchoredAtom3696 Fin15AnchoredAtom3778 Fin15AnchoredAtom3780
    Fin15AnchoredAtom3785 Fin15AnchoredAtom3816 Fin15AnchoredAtom3991 Fin15AnchoredAtom4108
    Fin15AnchoredAtom4110 Fin15AnchoredAtom4115 Fin15AnchoredAtom4146 Fin15AnchoredAtom4321
    Fin15AnchoredAtom4531 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31185 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2136 chi ∧
      ¬Fin15AnchoredAtom2139 chi ∧
      ¬Fin15AnchoredAtom2140 chi ∧
      ¬Fin15AnchoredAtom2154 chi ∧
      ¬Fin15AnchoredAtom2155 chi ∧
      ¬Fin15AnchoredAtom2161 chi ∧
      ¬Fin15AnchoredAtom2181 chi ∧
      ¬Fin15AnchoredAtom2184 chi ∧
      ¬Fin15AnchoredAtom2185 chi ∧
      ¬Fin15AnchoredAtom2199 chi ∧
      ¬Fin15AnchoredAtom2200 chi ∧
      ¬Fin15AnchoredAtom2206 chi ∧
      ¬Fin15AnchoredAtom2284 chi ∧
      ¬Fin15AnchoredAtom2285 chi ∧
      ¬Fin15AnchoredAtom2291 chi ∧
      ¬Fin15AnchoredAtom2322 chi ∧
      ¬Fin15AnchoredAtom2346 chi ∧
      ¬Fin15AnchoredAtom2349 chi ∧
      ¬Fin15AnchoredAtom2350 chi ∧
      ¬Fin15AnchoredAtom2364 chi ∧
      ¬Fin15AnchoredAtom2365 chi ∧
      ¬Fin15AnchoredAtom2371 chi ∧
      ¬Fin15AnchoredAtom2449 chi ∧
      ¬Fin15AnchoredAtom2450 chi ∧
      ¬Fin15AnchoredAtom2456 chi ∧
      ¬Fin15AnchoredAtom2487 chi ∧
      ¬Fin15AnchoredAtom2569 chi ∧
      ¬Fin15AnchoredAtom2570 chi ∧
      ¬Fin15AnchoredAtom2576 chi ∧
      ¬Fin15AnchoredAtom2607 chi ∧
      ¬Fin15AnchoredAtom2782 chi ∧
      ¬Fin15AnchoredAtom3556 chi ∧
      ¬Fin15AnchoredAtom3559 chi ∧
      ¬Fin15AnchoredAtom3560 chi ∧
      ¬Fin15AnchoredAtom3574 chi ∧
      ¬Fin15AnchoredAtom3575 chi ∧
      ¬Fin15AnchoredAtom3581 chi ∧
      ¬Fin15AnchoredAtom3659 chi ∧
      ¬Fin15AnchoredAtom3660 chi ∧
      ¬Fin15AnchoredAtom3666 chi ∧
      ¬Fin15AnchoredAtom3697 chi ∧
      ¬Fin15AnchoredAtom3779 chi ∧
      ¬Fin15AnchoredAtom3780 chi ∧
      ¬Fin15AnchoredAtom3786 chi ∧
      ¬Fin15AnchoredAtom3817 chi ∧
      ¬Fin15AnchoredAtom3992 chi ∧
      ¬Fin15AnchoredAtom4109 chi ∧
      ¬Fin15AnchoredAtom4110 chi ∧
      ¬Fin15AnchoredAtom4116 chi ∧
      ¬Fin15AnchoredAtom4147 chi ∧
      ¬Fin15AnchoredAtom4322 chi ∧
      ¬Fin15AnchoredAtom4532 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 7, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25757
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2109 Fin15AnchoredAtom2112 Fin15AnchoredAtom2115
    Fin15AnchoredAtom2116 Fin15AnchoredAtom2136 Fin15AnchoredAtom2139 Fin15AnchoredAtom2140
    Fin15AnchoredAtom2154 Fin15AnchoredAtom2155 Fin15AnchoredAtom2161 Fin15AnchoredAtom2181
    Fin15AnchoredAtom2184 Fin15AnchoredAtom2185 Fin15AnchoredAtom2199 Fin15AnchoredAtom2200
    Fin15AnchoredAtom2206 Fin15AnchoredAtom2284 Fin15AnchoredAtom2285 Fin15AnchoredAtom2291
    Fin15AnchoredAtom2322 Fin15AnchoredAtom2346 Fin15AnchoredAtom2349 Fin15AnchoredAtom2350
    Fin15AnchoredAtom2364 Fin15AnchoredAtom2365 Fin15AnchoredAtom2371 Fin15AnchoredAtom2449
    Fin15AnchoredAtom2450 Fin15AnchoredAtom2456 Fin15AnchoredAtom2487 Fin15AnchoredAtom2569
    Fin15AnchoredAtom2570 Fin15AnchoredAtom2576 Fin15AnchoredAtom2607 Fin15AnchoredAtom2782
    Fin15AnchoredAtom3556 Fin15AnchoredAtom3559 Fin15AnchoredAtom3560 Fin15AnchoredAtom3574
    Fin15AnchoredAtom3575 Fin15AnchoredAtom3581 Fin15AnchoredAtom3659 Fin15AnchoredAtom3660
    Fin15AnchoredAtom3666 Fin15AnchoredAtom3697 Fin15AnchoredAtom3779 Fin15AnchoredAtom3780
    Fin15AnchoredAtom3786 Fin15AnchoredAtom3817 Fin15AnchoredAtom3992 Fin15AnchoredAtom4109
    Fin15AnchoredAtom4110 Fin15AnchoredAtom4116 Fin15AnchoredAtom4147 Fin15AnchoredAtom4322
    Fin15AnchoredAtom4532 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31186 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2138 chi ∧
      ¬Fin15AnchoredAtom2139 chi ∧
      ¬Fin15AnchoredAtom2140 chi ∧
      ¬Fin15AnchoredAtom2159 chi ∧
      ¬Fin15AnchoredAtom2160 chi ∧
      ¬Fin15AnchoredAtom2161 chi ∧
      ¬Fin15AnchoredAtom2183 chi ∧
      ¬Fin15AnchoredAtom2184 chi ∧
      ¬Fin15AnchoredAtom2185 chi ∧
      ¬Fin15AnchoredAtom2204 chi ∧
      ¬Fin15AnchoredAtom2205 chi ∧
      ¬Fin15AnchoredAtom2206 chi ∧
      ¬Fin15AnchoredAtom2289 chi ∧
      ¬Fin15AnchoredAtom2290 chi ∧
      ¬Fin15AnchoredAtom2291 chi ∧
      ¬Fin15AnchoredAtom2326 chi ∧
      ¬Fin15AnchoredAtom2348 chi ∧
      ¬Fin15AnchoredAtom2349 chi ∧
      ¬Fin15AnchoredAtom2350 chi ∧
      ¬Fin15AnchoredAtom2369 chi ∧
      ¬Fin15AnchoredAtom2370 chi ∧
      ¬Fin15AnchoredAtom2371 chi ∧
      ¬Fin15AnchoredAtom2454 chi ∧
      ¬Fin15AnchoredAtom2455 chi ∧
      ¬Fin15AnchoredAtom2456 chi ∧
      ¬Fin15AnchoredAtom2491 chi ∧
      ¬Fin15AnchoredAtom2574 chi ∧
      ¬Fin15AnchoredAtom2575 chi ∧
      ¬Fin15AnchoredAtom2576 chi ∧
      ¬Fin15AnchoredAtom2611 chi ∧
      ¬Fin15AnchoredAtom2786 chi ∧
      ¬Fin15AnchoredAtom3558 chi ∧
      ¬Fin15AnchoredAtom3559 chi ∧
      ¬Fin15AnchoredAtom3560 chi ∧
      ¬Fin15AnchoredAtom3579 chi ∧
      ¬Fin15AnchoredAtom3580 chi ∧
      ¬Fin15AnchoredAtom3581 chi ∧
      ¬Fin15AnchoredAtom3664 chi ∧
      ¬Fin15AnchoredAtom3665 chi ∧
      ¬Fin15AnchoredAtom3666 chi ∧
      ¬Fin15AnchoredAtom3701 chi ∧
      ¬Fin15AnchoredAtom3784 chi ∧
      ¬Fin15AnchoredAtom3785 chi ∧
      ¬Fin15AnchoredAtom3786 chi ∧
      ¬Fin15AnchoredAtom3821 chi ∧
      ¬Fin15AnchoredAtom3996 chi ∧
      ¬Fin15AnchoredAtom4114 chi ∧
      ¬Fin15AnchoredAtom4115 chi ∧
      ¬Fin15AnchoredAtom4116 chi ∧
      ¬Fin15AnchoredAtom4151 chi ∧
      ¬Fin15AnchoredAtom4326 chi ∧
      ¬Fin15AnchoredAtom4536 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 7, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask28829
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2109 Fin15AnchoredAtom2114 Fin15AnchoredAtom2115
    Fin15AnchoredAtom2116 Fin15AnchoredAtom2138 Fin15AnchoredAtom2139 Fin15AnchoredAtom2140
    Fin15AnchoredAtom2159 Fin15AnchoredAtom2160 Fin15AnchoredAtom2161 Fin15AnchoredAtom2183
    Fin15AnchoredAtom2184 Fin15AnchoredAtom2185 Fin15AnchoredAtom2204 Fin15AnchoredAtom2205
    Fin15AnchoredAtom2206 Fin15AnchoredAtom2289 Fin15AnchoredAtom2290 Fin15AnchoredAtom2291
    Fin15AnchoredAtom2326 Fin15AnchoredAtom2348 Fin15AnchoredAtom2349 Fin15AnchoredAtom2350
    Fin15AnchoredAtom2369 Fin15AnchoredAtom2370 Fin15AnchoredAtom2371 Fin15AnchoredAtom2454
    Fin15AnchoredAtom2455 Fin15AnchoredAtom2456 Fin15AnchoredAtom2491 Fin15AnchoredAtom2574
    Fin15AnchoredAtom2575 Fin15AnchoredAtom2576 Fin15AnchoredAtom2611 Fin15AnchoredAtom2786
    Fin15AnchoredAtom3558 Fin15AnchoredAtom3559 Fin15AnchoredAtom3560 Fin15AnchoredAtom3579
    Fin15AnchoredAtom3580 Fin15AnchoredAtom3581 Fin15AnchoredAtom3664 Fin15AnchoredAtom3665
    Fin15AnchoredAtom3666 Fin15AnchoredAtom3701 Fin15AnchoredAtom3784 Fin15AnchoredAtom3785
    Fin15AnchoredAtom3786 Fin15AnchoredAtom3821 Fin15AnchoredAtom3996 Fin15AnchoredAtom4114
    Fin15AnchoredAtom4115 Fin15AnchoredAtom4116 Fin15AnchoredAtom4151 Fin15AnchoredAtom4326
    Fin15AnchoredAtom4536 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31187 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2113 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2147 chi ∧
      ¬Fin15AnchoredAtom2148 chi ∧
      ¬Fin15AnchoredAtom2150 chi ∧
      ¬Fin15AnchoredAtom2152 chi ∧
      ¬Fin15AnchoredAtom2154 chi ∧
      ¬Fin15AnchoredAtom2157 chi ∧
      ¬Fin15AnchoredAtom2192 chi ∧
      ¬Fin15AnchoredAtom2193 chi ∧
      ¬Fin15AnchoredAtom2195 chi ∧
      ¬Fin15AnchoredAtom2197 chi ∧
      ¬Fin15AnchoredAtom2199 chi ∧
      ¬Fin15AnchoredAtom2202 chi ∧
      ¬Fin15AnchoredAtom2307 chi ∧
      ¬Fin15AnchoredAtom2309 chi ∧
      ¬Fin15AnchoredAtom2312 chi ∧
      ¬Fin15AnchoredAtom2318 chi ∧
      ¬Fin15AnchoredAtom2357 chi ∧
      ¬Fin15AnchoredAtom2358 chi ∧
      ¬Fin15AnchoredAtom2360 chi ∧
      ¬Fin15AnchoredAtom2362 chi ∧
      ¬Fin15AnchoredAtom2364 chi ∧
      ¬Fin15AnchoredAtom2367 chi ∧
      ¬Fin15AnchoredAtom2472 chi ∧
      ¬Fin15AnchoredAtom2474 chi ∧
      ¬Fin15AnchoredAtom2477 chi ∧
      ¬Fin15AnchoredAtom2483 chi ∧
      ¬Fin15AnchoredAtom2592 chi ∧
      ¬Fin15AnchoredAtom2594 chi ∧
      ¬Fin15AnchoredAtom2597 chi ∧
      ¬Fin15AnchoredAtom2603 chi ∧
      ¬Fin15AnchoredAtom2808 chi ∧
      ¬Fin15AnchoredAtom3567 chi ∧
      ¬Fin15AnchoredAtom3568 chi ∧
      ¬Fin15AnchoredAtom3570 chi ∧
      ¬Fin15AnchoredAtom3572 chi ∧
      ¬Fin15AnchoredAtom3574 chi ∧
      ¬Fin15AnchoredAtom3577 chi ∧
      ¬Fin15AnchoredAtom3682 chi ∧
      ¬Fin15AnchoredAtom3684 chi ∧
      ¬Fin15AnchoredAtom3687 chi ∧
      ¬Fin15AnchoredAtom3693 chi ∧
      ¬Fin15AnchoredAtom3802 chi ∧
      ¬Fin15AnchoredAtom3804 chi ∧
      ¬Fin15AnchoredAtom3807 chi ∧
      ¬Fin15AnchoredAtom3813 chi ∧
      ¬Fin15AnchoredAtom4018 chi ∧
      ¬Fin15AnchoredAtom4132 chi ∧
      ¬Fin15AnchoredAtom4134 chi ∧
      ¬Fin15AnchoredAtom4137 chi ∧
      ¬Fin15AnchoredAtom4143 chi ∧
      ¬Fin15AnchoredAtom4348 chi ∧
      ¬Fin15AnchoredAtom4558 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 9, 10, 11, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask11805
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2111 Fin15AnchoredAtom2112 Fin15AnchoredAtom2113
    Fin15AnchoredAtom2115 Fin15AnchoredAtom2147 Fin15AnchoredAtom2148 Fin15AnchoredAtom2150
    Fin15AnchoredAtom2152 Fin15AnchoredAtom2154 Fin15AnchoredAtom2157 Fin15AnchoredAtom2192
    Fin15AnchoredAtom2193 Fin15AnchoredAtom2195 Fin15AnchoredAtom2197 Fin15AnchoredAtom2199
    Fin15AnchoredAtom2202 Fin15AnchoredAtom2307 Fin15AnchoredAtom2309 Fin15AnchoredAtom2312
    Fin15AnchoredAtom2318 Fin15AnchoredAtom2357 Fin15AnchoredAtom2358 Fin15AnchoredAtom2360
    Fin15AnchoredAtom2362 Fin15AnchoredAtom2364 Fin15AnchoredAtom2367 Fin15AnchoredAtom2472
    Fin15AnchoredAtom2474 Fin15AnchoredAtom2477 Fin15AnchoredAtom2483 Fin15AnchoredAtom2592
    Fin15AnchoredAtom2594 Fin15AnchoredAtom2597 Fin15AnchoredAtom2603 Fin15AnchoredAtom2808
    Fin15AnchoredAtom3567 Fin15AnchoredAtom3568 Fin15AnchoredAtom3570 Fin15AnchoredAtom3572
    Fin15AnchoredAtom3574 Fin15AnchoredAtom3577 Fin15AnchoredAtom3682 Fin15AnchoredAtom3684
    Fin15AnchoredAtom3687 Fin15AnchoredAtom3693 Fin15AnchoredAtom3802 Fin15AnchoredAtom3804
    Fin15AnchoredAtom3807 Fin15AnchoredAtom3813 Fin15AnchoredAtom4018 Fin15AnchoredAtom4132
    Fin15AnchoredAtom4134 Fin15AnchoredAtom4137 Fin15AnchoredAtom4143 Fin15AnchoredAtom4348
    Fin15AnchoredAtom4558 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31188 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2147 chi ∧
      ¬Fin15AnchoredAtom2149 chi ∧
      ¬Fin15AnchoredAtom2150 chi ∧
      ¬Fin15AnchoredAtom2153 chi ∧
      ¬Fin15AnchoredAtom2154 chi ∧
      ¬Fin15AnchoredAtom2159 chi ∧
      ¬Fin15AnchoredAtom2192 chi ∧
      ¬Fin15AnchoredAtom2194 chi ∧
      ¬Fin15AnchoredAtom2195 chi ∧
      ¬Fin15AnchoredAtom2198 chi ∧
      ¬Fin15AnchoredAtom2199 chi ∧
      ¬Fin15AnchoredAtom2204 chi ∧
      ¬Fin15AnchoredAtom2308 chi ∧
      ¬Fin15AnchoredAtom2309 chi ∧
      ¬Fin15AnchoredAtom2314 chi ∧
      ¬Fin15AnchoredAtom2320 chi ∧
      ¬Fin15AnchoredAtom2357 chi ∧
      ¬Fin15AnchoredAtom2359 chi ∧
      ¬Fin15AnchoredAtom2360 chi ∧
      ¬Fin15AnchoredAtom2363 chi ∧
      ¬Fin15AnchoredAtom2364 chi ∧
      ¬Fin15AnchoredAtom2369 chi ∧
      ¬Fin15AnchoredAtom2473 chi ∧
      ¬Fin15AnchoredAtom2474 chi ∧
      ¬Fin15AnchoredAtom2479 chi ∧
      ¬Fin15AnchoredAtom2485 chi ∧
      ¬Fin15AnchoredAtom2593 chi ∧
      ¬Fin15AnchoredAtom2594 chi ∧
      ¬Fin15AnchoredAtom2599 chi ∧
      ¬Fin15AnchoredAtom2605 chi ∧
      ¬Fin15AnchoredAtom2810 chi ∧
      ¬Fin15AnchoredAtom3567 chi ∧
      ¬Fin15AnchoredAtom3569 chi ∧
      ¬Fin15AnchoredAtom3570 chi ∧
      ¬Fin15AnchoredAtom3573 chi ∧
      ¬Fin15AnchoredAtom3574 chi ∧
      ¬Fin15AnchoredAtom3579 chi ∧
      ¬Fin15AnchoredAtom3683 chi ∧
      ¬Fin15AnchoredAtom3684 chi ∧
      ¬Fin15AnchoredAtom3689 chi ∧
      ¬Fin15AnchoredAtom3695 chi ∧
      ¬Fin15AnchoredAtom3803 chi ∧
      ¬Fin15AnchoredAtom3804 chi ∧
      ¬Fin15AnchoredAtom3809 chi ∧
      ¬Fin15AnchoredAtom3815 chi ∧
      ¬Fin15AnchoredAtom4020 chi ∧
      ¬Fin15AnchoredAtom4133 chi ∧
      ¬Fin15AnchoredAtom4134 chi ∧
      ¬Fin15AnchoredAtom4139 chi ∧
      ¬Fin15AnchoredAtom4145 chi ∧
      ¬Fin15AnchoredAtom4350 chi ∧
      ¬Fin15AnchoredAtom4560 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13853
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2111 Fin15AnchoredAtom2112 Fin15AnchoredAtom2114
    Fin15AnchoredAtom2115 Fin15AnchoredAtom2147 Fin15AnchoredAtom2149 Fin15AnchoredAtom2150
    Fin15AnchoredAtom2153 Fin15AnchoredAtom2154 Fin15AnchoredAtom2159 Fin15AnchoredAtom2192
    Fin15AnchoredAtom2194 Fin15AnchoredAtom2195 Fin15AnchoredAtom2198 Fin15AnchoredAtom2199
    Fin15AnchoredAtom2204 Fin15AnchoredAtom2308 Fin15AnchoredAtom2309 Fin15AnchoredAtom2314
    Fin15AnchoredAtom2320 Fin15AnchoredAtom2357 Fin15AnchoredAtom2359 Fin15AnchoredAtom2360
    Fin15AnchoredAtom2363 Fin15AnchoredAtom2364 Fin15AnchoredAtom2369 Fin15AnchoredAtom2473
    Fin15AnchoredAtom2474 Fin15AnchoredAtom2479 Fin15AnchoredAtom2485 Fin15AnchoredAtom2593
    Fin15AnchoredAtom2594 Fin15AnchoredAtom2599 Fin15AnchoredAtom2605 Fin15AnchoredAtom2810
    Fin15AnchoredAtom3567 Fin15AnchoredAtom3569 Fin15AnchoredAtom3570 Fin15AnchoredAtom3573
    Fin15AnchoredAtom3574 Fin15AnchoredAtom3579 Fin15AnchoredAtom3683 Fin15AnchoredAtom3684
    Fin15AnchoredAtom3689 Fin15AnchoredAtom3695 Fin15AnchoredAtom3803 Fin15AnchoredAtom3804
    Fin15AnchoredAtom3809 Fin15AnchoredAtom3815 Fin15AnchoredAtom4020 Fin15AnchoredAtom4133
    Fin15AnchoredAtom4134 Fin15AnchoredAtom4139 Fin15AnchoredAtom4145 Fin15AnchoredAtom4350
    Fin15AnchoredAtom4560 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31189 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2147 chi ∧
      ¬Fin15AnchoredAtom2149 chi ∧
      ¬Fin15AnchoredAtom2151 chi ∧
      ¬Fin15AnchoredAtom2153 chi ∧
      ¬Fin15AnchoredAtom2155 chi ∧
      ¬Fin15AnchoredAtom2160 chi ∧
      ¬Fin15AnchoredAtom2192 chi ∧
      ¬Fin15AnchoredAtom2194 chi ∧
      ¬Fin15AnchoredAtom2196 chi ∧
      ¬Fin15AnchoredAtom2198 chi ∧
      ¬Fin15AnchoredAtom2200 chi ∧
      ¬Fin15AnchoredAtom2205 chi ∧
      ¬Fin15AnchoredAtom2308 chi ∧
      ¬Fin15AnchoredAtom2310 chi ∧
      ¬Fin15AnchoredAtom2315 chi ∧
      ¬Fin15AnchoredAtom2321 chi ∧
      ¬Fin15AnchoredAtom2357 chi ∧
      ¬Fin15AnchoredAtom2359 chi ∧
      ¬Fin15AnchoredAtom2361 chi ∧
      ¬Fin15AnchoredAtom2363 chi ∧
      ¬Fin15AnchoredAtom2365 chi ∧
      ¬Fin15AnchoredAtom2370 chi ∧
      ¬Fin15AnchoredAtom2473 chi ∧
      ¬Fin15AnchoredAtom2475 chi ∧
      ¬Fin15AnchoredAtom2480 chi ∧
      ¬Fin15AnchoredAtom2486 chi ∧
      ¬Fin15AnchoredAtom2593 chi ∧
      ¬Fin15AnchoredAtom2595 chi ∧
      ¬Fin15AnchoredAtom2600 chi ∧
      ¬Fin15AnchoredAtom2606 chi ∧
      ¬Fin15AnchoredAtom2811 chi ∧
      ¬Fin15AnchoredAtom3567 chi ∧
      ¬Fin15AnchoredAtom3569 chi ∧
      ¬Fin15AnchoredAtom3571 chi ∧
      ¬Fin15AnchoredAtom3573 chi ∧
      ¬Fin15AnchoredAtom3575 chi ∧
      ¬Fin15AnchoredAtom3580 chi ∧
      ¬Fin15AnchoredAtom3683 chi ∧
      ¬Fin15AnchoredAtom3685 chi ∧
      ¬Fin15AnchoredAtom3690 chi ∧
      ¬Fin15AnchoredAtom3696 chi ∧
      ¬Fin15AnchoredAtom3803 chi ∧
      ¬Fin15AnchoredAtom3805 chi ∧
      ¬Fin15AnchoredAtom3810 chi ∧
      ¬Fin15AnchoredAtom3816 chi ∧
      ¬Fin15AnchoredAtom4021 chi ∧
      ¬Fin15AnchoredAtom4133 chi ∧
      ¬Fin15AnchoredAtom4135 chi ∧
      ¬Fin15AnchoredAtom4140 chi ∧
      ¬Fin15AnchoredAtom4146 chi ∧
      ¬Fin15AnchoredAtom4351 chi ∧
      ¬Fin15AnchoredAtom4561 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 9, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22045
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2111 Fin15AnchoredAtom2112 Fin15AnchoredAtom2114
    Fin15AnchoredAtom2116 Fin15AnchoredAtom2147 Fin15AnchoredAtom2149 Fin15AnchoredAtom2151
    Fin15AnchoredAtom2153 Fin15AnchoredAtom2155 Fin15AnchoredAtom2160 Fin15AnchoredAtom2192
    Fin15AnchoredAtom2194 Fin15AnchoredAtom2196 Fin15AnchoredAtom2198 Fin15AnchoredAtom2200
    Fin15AnchoredAtom2205 Fin15AnchoredAtom2308 Fin15AnchoredAtom2310 Fin15AnchoredAtom2315
    Fin15AnchoredAtom2321 Fin15AnchoredAtom2357 Fin15AnchoredAtom2359 Fin15AnchoredAtom2361
    Fin15AnchoredAtom2363 Fin15AnchoredAtom2365 Fin15AnchoredAtom2370 Fin15AnchoredAtom2473
    Fin15AnchoredAtom2475 Fin15AnchoredAtom2480 Fin15AnchoredAtom2486 Fin15AnchoredAtom2593
    Fin15AnchoredAtom2595 Fin15AnchoredAtom2600 Fin15AnchoredAtom2606 Fin15AnchoredAtom2811
    Fin15AnchoredAtom3567 Fin15AnchoredAtom3569 Fin15AnchoredAtom3571 Fin15AnchoredAtom3573
    Fin15AnchoredAtom3575 Fin15AnchoredAtom3580 Fin15AnchoredAtom3683 Fin15AnchoredAtom3685
    Fin15AnchoredAtom3690 Fin15AnchoredAtom3696 Fin15AnchoredAtom3803 Fin15AnchoredAtom3805
    Fin15AnchoredAtom3810 Fin15AnchoredAtom3816 Fin15AnchoredAtom4021 Fin15AnchoredAtom4133
    Fin15AnchoredAtom4135 Fin15AnchoredAtom4140 Fin15AnchoredAtom4146 Fin15AnchoredAtom4351
    Fin15AnchoredAtom4561 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31190 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2147 chi ∧
      ¬Fin15AnchoredAtom2150 chi ∧
      ¬Fin15AnchoredAtom2151 chi ∧
      ¬Fin15AnchoredAtom2154 chi ∧
      ¬Fin15AnchoredAtom2155 chi ∧
      ¬Fin15AnchoredAtom2161 chi ∧
      ¬Fin15AnchoredAtom2192 chi ∧
      ¬Fin15AnchoredAtom2195 chi ∧
      ¬Fin15AnchoredAtom2196 chi ∧
      ¬Fin15AnchoredAtom2199 chi ∧
      ¬Fin15AnchoredAtom2200 chi ∧
      ¬Fin15AnchoredAtom2206 chi ∧
      ¬Fin15AnchoredAtom2309 chi ∧
      ¬Fin15AnchoredAtom2310 chi ∧
      ¬Fin15AnchoredAtom2316 chi ∧
      ¬Fin15AnchoredAtom2322 chi ∧
      ¬Fin15AnchoredAtom2357 chi ∧
      ¬Fin15AnchoredAtom2360 chi ∧
      ¬Fin15AnchoredAtom2361 chi ∧
      ¬Fin15AnchoredAtom2364 chi ∧
      ¬Fin15AnchoredAtom2365 chi ∧
      ¬Fin15AnchoredAtom2371 chi ∧
      ¬Fin15AnchoredAtom2474 chi ∧
      ¬Fin15AnchoredAtom2475 chi ∧
      ¬Fin15AnchoredAtom2481 chi ∧
      ¬Fin15AnchoredAtom2487 chi ∧
      ¬Fin15AnchoredAtom2594 chi ∧
      ¬Fin15AnchoredAtom2595 chi ∧
      ¬Fin15AnchoredAtom2601 chi ∧
      ¬Fin15AnchoredAtom2607 chi ∧
      ¬Fin15AnchoredAtom2812 chi ∧
      ¬Fin15AnchoredAtom3567 chi ∧
      ¬Fin15AnchoredAtom3570 chi ∧
      ¬Fin15AnchoredAtom3571 chi ∧
      ¬Fin15AnchoredAtom3574 chi ∧
      ¬Fin15AnchoredAtom3575 chi ∧
      ¬Fin15AnchoredAtom3581 chi ∧
      ¬Fin15AnchoredAtom3684 chi ∧
      ¬Fin15AnchoredAtom3685 chi ∧
      ¬Fin15AnchoredAtom3691 chi ∧
      ¬Fin15AnchoredAtom3697 chi ∧
      ¬Fin15AnchoredAtom3804 chi ∧
      ¬Fin15AnchoredAtom3805 chi ∧
      ¬Fin15AnchoredAtom3811 chi ∧
      ¬Fin15AnchoredAtom3817 chi ∧
      ¬Fin15AnchoredAtom4022 chi ∧
      ¬Fin15AnchoredAtom4134 chi ∧
      ¬Fin15AnchoredAtom4135 chi ∧
      ¬Fin15AnchoredAtom4141 chi ∧
      ¬Fin15AnchoredAtom4147 chi ∧
      ¬Fin15AnchoredAtom4352 chi ∧
      ¬Fin15AnchoredAtom4562 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 9, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26141
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2111 Fin15AnchoredAtom2112 Fin15AnchoredAtom2115
    Fin15AnchoredAtom2116 Fin15AnchoredAtom2147 Fin15AnchoredAtom2150 Fin15AnchoredAtom2151
    Fin15AnchoredAtom2154 Fin15AnchoredAtom2155 Fin15AnchoredAtom2161 Fin15AnchoredAtom2192
    Fin15AnchoredAtom2195 Fin15AnchoredAtom2196 Fin15AnchoredAtom2199 Fin15AnchoredAtom2200
    Fin15AnchoredAtom2206 Fin15AnchoredAtom2309 Fin15AnchoredAtom2310 Fin15AnchoredAtom2316
    Fin15AnchoredAtom2322 Fin15AnchoredAtom2357 Fin15AnchoredAtom2360 Fin15AnchoredAtom2361
    Fin15AnchoredAtom2364 Fin15AnchoredAtom2365 Fin15AnchoredAtom2371 Fin15AnchoredAtom2474
    Fin15AnchoredAtom2475 Fin15AnchoredAtom2481 Fin15AnchoredAtom2487 Fin15AnchoredAtom2594
    Fin15AnchoredAtom2595 Fin15AnchoredAtom2601 Fin15AnchoredAtom2607 Fin15AnchoredAtom2812
    Fin15AnchoredAtom3567 Fin15AnchoredAtom3570 Fin15AnchoredAtom3571 Fin15AnchoredAtom3574
    Fin15AnchoredAtom3575 Fin15AnchoredAtom3581 Fin15AnchoredAtom3684 Fin15AnchoredAtom3685
    Fin15AnchoredAtom3691 Fin15AnchoredAtom3697 Fin15AnchoredAtom3804 Fin15AnchoredAtom3805
    Fin15AnchoredAtom3811 Fin15AnchoredAtom3817 Fin15AnchoredAtom4022 Fin15AnchoredAtom4134
    Fin15AnchoredAtom4135 Fin15AnchoredAtom4141 Fin15AnchoredAtom4147 Fin15AnchoredAtom4352
    Fin15AnchoredAtom4562 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31191 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2113 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2148 chi ∧
      ¬Fin15AnchoredAtom2149 chi ∧
      ¬Fin15AnchoredAtom2150 chi ∧
      ¬Fin15AnchoredAtom2156 chi ∧
      ¬Fin15AnchoredAtom2157 chi ∧
      ¬Fin15AnchoredAtom2159 chi ∧
      ¬Fin15AnchoredAtom2193 chi ∧
      ¬Fin15AnchoredAtom2194 chi ∧
      ¬Fin15AnchoredAtom2195 chi ∧
      ¬Fin15AnchoredAtom2201 chi ∧
      ¬Fin15AnchoredAtom2202 chi ∧
      ¬Fin15AnchoredAtom2204 chi ∧
      ¬Fin15AnchoredAtom2311 chi ∧
      ¬Fin15AnchoredAtom2312 chi ∧
      ¬Fin15AnchoredAtom2314 chi ∧
      ¬Fin15AnchoredAtom2323 chi ∧
      ¬Fin15AnchoredAtom2358 chi ∧
      ¬Fin15AnchoredAtom2359 chi ∧
      ¬Fin15AnchoredAtom2360 chi ∧
      ¬Fin15AnchoredAtom2366 chi ∧
      ¬Fin15AnchoredAtom2367 chi ∧
      ¬Fin15AnchoredAtom2369 chi ∧
      ¬Fin15AnchoredAtom2476 chi ∧
      ¬Fin15AnchoredAtom2477 chi ∧
      ¬Fin15AnchoredAtom2479 chi ∧
      ¬Fin15AnchoredAtom2488 chi ∧
      ¬Fin15AnchoredAtom2596 chi ∧
      ¬Fin15AnchoredAtom2597 chi ∧
      ¬Fin15AnchoredAtom2599 chi ∧
      ¬Fin15AnchoredAtom2608 chi ∧
      ¬Fin15AnchoredAtom2813 chi ∧
      ¬Fin15AnchoredAtom3568 chi ∧
      ¬Fin15AnchoredAtom3569 chi ∧
      ¬Fin15AnchoredAtom3570 chi ∧
      ¬Fin15AnchoredAtom3576 chi ∧
      ¬Fin15AnchoredAtom3577 chi ∧
      ¬Fin15AnchoredAtom3579 chi ∧
      ¬Fin15AnchoredAtom3686 chi ∧
      ¬Fin15AnchoredAtom3687 chi ∧
      ¬Fin15AnchoredAtom3689 chi ∧
      ¬Fin15AnchoredAtom3698 chi ∧
      ¬Fin15AnchoredAtom3806 chi ∧
      ¬Fin15AnchoredAtom3807 chi ∧
      ¬Fin15AnchoredAtom3809 chi ∧
      ¬Fin15AnchoredAtom3818 chi ∧
      ¬Fin15AnchoredAtom4023 chi ∧
      ¬Fin15AnchoredAtom4136 chi ∧
      ¬Fin15AnchoredAtom4137 chi ∧
      ¬Fin15AnchoredAtom4139 chi ∧
      ¬Fin15AnchoredAtom4148 chi ∧
      ¬Fin15AnchoredAtom4353 chi ∧
      ¬Fin15AnchoredAtom4563 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 9, 11, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask14877
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2111 Fin15AnchoredAtom2113 Fin15AnchoredAtom2114
    Fin15AnchoredAtom2115 Fin15AnchoredAtom2148 Fin15AnchoredAtom2149 Fin15AnchoredAtom2150
    Fin15AnchoredAtom2156 Fin15AnchoredAtom2157 Fin15AnchoredAtom2159 Fin15AnchoredAtom2193
    Fin15AnchoredAtom2194 Fin15AnchoredAtom2195 Fin15AnchoredAtom2201 Fin15AnchoredAtom2202
    Fin15AnchoredAtom2204 Fin15AnchoredAtom2311 Fin15AnchoredAtom2312 Fin15AnchoredAtom2314
    Fin15AnchoredAtom2323 Fin15AnchoredAtom2358 Fin15AnchoredAtom2359 Fin15AnchoredAtom2360
    Fin15AnchoredAtom2366 Fin15AnchoredAtom2367 Fin15AnchoredAtom2369 Fin15AnchoredAtom2476
    Fin15AnchoredAtom2477 Fin15AnchoredAtom2479 Fin15AnchoredAtom2488 Fin15AnchoredAtom2596
    Fin15AnchoredAtom2597 Fin15AnchoredAtom2599 Fin15AnchoredAtom2608 Fin15AnchoredAtom2813
    Fin15AnchoredAtom3568 Fin15AnchoredAtom3569 Fin15AnchoredAtom3570 Fin15AnchoredAtom3576
    Fin15AnchoredAtom3577 Fin15AnchoredAtom3579 Fin15AnchoredAtom3686 Fin15AnchoredAtom3687
    Fin15AnchoredAtom3689 Fin15AnchoredAtom3698 Fin15AnchoredAtom3806 Fin15AnchoredAtom3807
    Fin15AnchoredAtom3809 Fin15AnchoredAtom3818 Fin15AnchoredAtom4023 Fin15AnchoredAtom4136
    Fin15AnchoredAtom4137 Fin15AnchoredAtom4139 Fin15AnchoredAtom4148 Fin15AnchoredAtom4353
    Fin15AnchoredAtom4563 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31192 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2113 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2148 chi ∧
      ¬Fin15AnchoredAtom2149 chi ∧
      ¬Fin15AnchoredAtom2151 chi ∧
      ¬Fin15AnchoredAtom2156 chi ∧
      ¬Fin15AnchoredAtom2158 chi ∧
      ¬Fin15AnchoredAtom2160 chi ∧
      ¬Fin15AnchoredAtom2193 chi ∧
      ¬Fin15AnchoredAtom2194 chi ∧
      ¬Fin15AnchoredAtom2196 chi ∧
      ¬Fin15AnchoredAtom2201 chi ∧
      ¬Fin15AnchoredAtom2203 chi ∧
      ¬Fin15AnchoredAtom2205 chi ∧
      ¬Fin15AnchoredAtom2311 chi ∧
      ¬Fin15AnchoredAtom2313 chi ∧
      ¬Fin15AnchoredAtom2315 chi ∧
      ¬Fin15AnchoredAtom2324 chi ∧
      ¬Fin15AnchoredAtom2358 chi ∧
      ¬Fin15AnchoredAtom2359 chi ∧
      ¬Fin15AnchoredAtom2361 chi ∧
      ¬Fin15AnchoredAtom2366 chi ∧
      ¬Fin15AnchoredAtom2368 chi ∧
      ¬Fin15AnchoredAtom2370 chi ∧
      ¬Fin15AnchoredAtom2476 chi ∧
      ¬Fin15AnchoredAtom2478 chi ∧
      ¬Fin15AnchoredAtom2480 chi ∧
      ¬Fin15AnchoredAtom2489 chi ∧
      ¬Fin15AnchoredAtom2596 chi ∧
      ¬Fin15AnchoredAtom2598 chi ∧
      ¬Fin15AnchoredAtom2600 chi ∧
      ¬Fin15AnchoredAtom2609 chi ∧
      ¬Fin15AnchoredAtom2814 chi ∧
      ¬Fin15AnchoredAtom3568 chi ∧
      ¬Fin15AnchoredAtom3569 chi ∧
      ¬Fin15AnchoredAtom3571 chi ∧
      ¬Fin15AnchoredAtom3576 chi ∧
      ¬Fin15AnchoredAtom3578 chi ∧
      ¬Fin15AnchoredAtom3580 chi ∧
      ¬Fin15AnchoredAtom3686 chi ∧
      ¬Fin15AnchoredAtom3688 chi ∧
      ¬Fin15AnchoredAtom3690 chi ∧
      ¬Fin15AnchoredAtom3699 chi ∧
      ¬Fin15AnchoredAtom3806 chi ∧
      ¬Fin15AnchoredAtom3808 chi ∧
      ¬Fin15AnchoredAtom3810 chi ∧
      ¬Fin15AnchoredAtom3819 chi ∧
      ¬Fin15AnchoredAtom4024 chi ∧
      ¬Fin15AnchoredAtom4136 chi ∧
      ¬Fin15AnchoredAtom4138 chi ∧
      ¬Fin15AnchoredAtom4140 chi ∧
      ¬Fin15AnchoredAtom4149 chi ∧
      ¬Fin15AnchoredAtom4354 chi ∧
      ¬Fin15AnchoredAtom4564 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 9, 11, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask23069
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2111 Fin15AnchoredAtom2113 Fin15AnchoredAtom2114
    Fin15AnchoredAtom2116 Fin15AnchoredAtom2148 Fin15AnchoredAtom2149 Fin15AnchoredAtom2151
    Fin15AnchoredAtom2156 Fin15AnchoredAtom2158 Fin15AnchoredAtom2160 Fin15AnchoredAtom2193
    Fin15AnchoredAtom2194 Fin15AnchoredAtom2196 Fin15AnchoredAtom2201 Fin15AnchoredAtom2203
    Fin15AnchoredAtom2205 Fin15AnchoredAtom2311 Fin15AnchoredAtom2313 Fin15AnchoredAtom2315
    Fin15AnchoredAtom2324 Fin15AnchoredAtom2358 Fin15AnchoredAtom2359 Fin15AnchoredAtom2361
    Fin15AnchoredAtom2366 Fin15AnchoredAtom2368 Fin15AnchoredAtom2370 Fin15AnchoredAtom2476
    Fin15AnchoredAtom2478 Fin15AnchoredAtom2480 Fin15AnchoredAtom2489 Fin15AnchoredAtom2596
    Fin15AnchoredAtom2598 Fin15AnchoredAtom2600 Fin15AnchoredAtom2609 Fin15AnchoredAtom2814
    Fin15AnchoredAtom3568 Fin15AnchoredAtom3569 Fin15AnchoredAtom3571 Fin15AnchoredAtom3576
    Fin15AnchoredAtom3578 Fin15AnchoredAtom3580 Fin15AnchoredAtom3686 Fin15AnchoredAtom3688
    Fin15AnchoredAtom3690 Fin15AnchoredAtom3699 Fin15AnchoredAtom3806 Fin15AnchoredAtom3808
    Fin15AnchoredAtom3810 Fin15AnchoredAtom3819 Fin15AnchoredAtom4024 Fin15AnchoredAtom4136
    Fin15AnchoredAtom4138 Fin15AnchoredAtom4140 Fin15AnchoredAtom4149 Fin15AnchoredAtom4354
    Fin15AnchoredAtom4564 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31193 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2149 chi ∧
      ¬Fin15AnchoredAtom2150 chi ∧
      ¬Fin15AnchoredAtom2151 chi ∧
      ¬Fin15AnchoredAtom2159 chi ∧
      ¬Fin15AnchoredAtom2160 chi ∧
      ¬Fin15AnchoredAtom2161 chi ∧
      ¬Fin15AnchoredAtom2194 chi ∧
      ¬Fin15AnchoredAtom2195 chi ∧
      ¬Fin15AnchoredAtom2196 chi ∧
      ¬Fin15AnchoredAtom2204 chi ∧
      ¬Fin15AnchoredAtom2205 chi ∧
      ¬Fin15AnchoredAtom2206 chi ∧
      ¬Fin15AnchoredAtom2314 chi ∧
      ¬Fin15AnchoredAtom2315 chi ∧
      ¬Fin15AnchoredAtom2316 chi ∧
      ¬Fin15AnchoredAtom2326 chi ∧
      ¬Fin15AnchoredAtom2359 chi ∧
      ¬Fin15AnchoredAtom2360 chi ∧
      ¬Fin15AnchoredAtom2361 chi ∧
      ¬Fin15AnchoredAtom2369 chi ∧
      ¬Fin15AnchoredAtom2370 chi ∧
      ¬Fin15AnchoredAtom2371 chi ∧
      ¬Fin15AnchoredAtom2479 chi ∧
      ¬Fin15AnchoredAtom2480 chi ∧
      ¬Fin15AnchoredAtom2481 chi ∧
      ¬Fin15AnchoredAtom2491 chi ∧
      ¬Fin15AnchoredAtom2599 chi ∧
      ¬Fin15AnchoredAtom2600 chi ∧
      ¬Fin15AnchoredAtom2601 chi ∧
      ¬Fin15AnchoredAtom2611 chi ∧
      ¬Fin15AnchoredAtom2816 chi ∧
      ¬Fin15AnchoredAtom3569 chi ∧
      ¬Fin15AnchoredAtom3570 chi ∧
      ¬Fin15AnchoredAtom3571 chi ∧
      ¬Fin15AnchoredAtom3579 chi ∧
      ¬Fin15AnchoredAtom3580 chi ∧
      ¬Fin15AnchoredAtom3581 chi ∧
      ¬Fin15AnchoredAtom3689 chi ∧
      ¬Fin15AnchoredAtom3690 chi ∧
      ¬Fin15AnchoredAtom3691 chi ∧
      ¬Fin15AnchoredAtom3701 chi ∧
      ¬Fin15AnchoredAtom3809 chi ∧
      ¬Fin15AnchoredAtom3810 chi ∧
      ¬Fin15AnchoredAtom3811 chi ∧
      ¬Fin15AnchoredAtom3821 chi ∧
      ¬Fin15AnchoredAtom4026 chi ∧
      ¬Fin15AnchoredAtom4139 chi ∧
      ¬Fin15AnchoredAtom4140 chi ∧
      ¬Fin15AnchoredAtom4141 chi ∧
      ¬Fin15AnchoredAtom4151 chi ∧
      ¬Fin15AnchoredAtom4356 chi ∧
      ¬Fin15AnchoredAtom4566 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 9, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29213
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2111 Fin15AnchoredAtom2114 Fin15AnchoredAtom2115
    Fin15AnchoredAtom2116 Fin15AnchoredAtom2149 Fin15AnchoredAtom2150 Fin15AnchoredAtom2151
    Fin15AnchoredAtom2159 Fin15AnchoredAtom2160 Fin15AnchoredAtom2161 Fin15AnchoredAtom2194
    Fin15AnchoredAtom2195 Fin15AnchoredAtom2196 Fin15AnchoredAtom2204 Fin15AnchoredAtom2205
    Fin15AnchoredAtom2206 Fin15AnchoredAtom2314 Fin15AnchoredAtom2315 Fin15AnchoredAtom2316
    Fin15AnchoredAtom2326 Fin15AnchoredAtom2359 Fin15AnchoredAtom2360 Fin15AnchoredAtom2361
    Fin15AnchoredAtom2369 Fin15AnchoredAtom2370 Fin15AnchoredAtom2371 Fin15AnchoredAtom2479
    Fin15AnchoredAtom2480 Fin15AnchoredAtom2481 Fin15AnchoredAtom2491 Fin15AnchoredAtom2599
    Fin15AnchoredAtom2600 Fin15AnchoredAtom2601 Fin15AnchoredAtom2611 Fin15AnchoredAtom2816
    Fin15AnchoredAtom3569 Fin15AnchoredAtom3570 Fin15AnchoredAtom3571 Fin15AnchoredAtom3579
    Fin15AnchoredAtom3580 Fin15AnchoredAtom3581 Fin15AnchoredAtom3689 Fin15AnchoredAtom3690
    Fin15AnchoredAtom3691 Fin15AnchoredAtom3701 Fin15AnchoredAtom3809 Fin15AnchoredAtom3810
    Fin15AnchoredAtom3811 Fin15AnchoredAtom3821 Fin15AnchoredAtom4026 Fin15AnchoredAtom4139
    Fin15AnchoredAtom4140 Fin15AnchoredAtom4141 Fin15AnchoredAtom4151 Fin15AnchoredAtom4356
    Fin15AnchoredAtom4566 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31194 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2153 chi ∧
      ¬Fin15AnchoredAtom2154 chi ∧
      ¬Fin15AnchoredAtom2155 chi ∧
      ¬Fin15AnchoredAtom2159 chi ∧
      ¬Fin15AnchoredAtom2160 chi ∧
      ¬Fin15AnchoredAtom2161 chi ∧
      ¬Fin15AnchoredAtom2198 chi ∧
      ¬Fin15AnchoredAtom2199 chi ∧
      ¬Fin15AnchoredAtom2200 chi ∧
      ¬Fin15AnchoredAtom2204 chi ∧
      ¬Fin15AnchoredAtom2205 chi ∧
      ¬Fin15AnchoredAtom2206 chi ∧
      ¬Fin15AnchoredAtom2320 chi ∧
      ¬Fin15AnchoredAtom2321 chi ∧
      ¬Fin15AnchoredAtom2322 chi ∧
      ¬Fin15AnchoredAtom2326 chi ∧
      ¬Fin15AnchoredAtom2363 chi ∧
      ¬Fin15AnchoredAtom2364 chi ∧
      ¬Fin15AnchoredAtom2365 chi ∧
      ¬Fin15AnchoredAtom2369 chi ∧
      ¬Fin15AnchoredAtom2370 chi ∧
      ¬Fin15AnchoredAtom2371 chi ∧
      ¬Fin15AnchoredAtom2485 chi ∧
      ¬Fin15AnchoredAtom2486 chi ∧
      ¬Fin15AnchoredAtom2487 chi ∧
      ¬Fin15AnchoredAtom2491 chi ∧
      ¬Fin15AnchoredAtom2605 chi ∧
      ¬Fin15AnchoredAtom2606 chi ∧
      ¬Fin15AnchoredAtom2607 chi ∧
      ¬Fin15AnchoredAtom2611 chi ∧
      ¬Fin15AnchoredAtom2820 chi ∧
      ¬Fin15AnchoredAtom3573 chi ∧
      ¬Fin15AnchoredAtom3574 chi ∧
      ¬Fin15AnchoredAtom3575 chi ∧
      ¬Fin15AnchoredAtom3579 chi ∧
      ¬Fin15AnchoredAtom3580 chi ∧
      ¬Fin15AnchoredAtom3581 chi ∧
      ¬Fin15AnchoredAtom3695 chi ∧
      ¬Fin15AnchoredAtom3696 chi ∧
      ¬Fin15AnchoredAtom3697 chi ∧
      ¬Fin15AnchoredAtom3701 chi ∧
      ¬Fin15AnchoredAtom3815 chi ∧
      ¬Fin15AnchoredAtom3816 chi ∧
      ¬Fin15AnchoredAtom3817 chi ∧
      ¬Fin15AnchoredAtom3821 chi ∧
      ¬Fin15AnchoredAtom4030 chi ∧
      ¬Fin15AnchoredAtom4145 chi ∧
      ¬Fin15AnchoredAtom4146 chi ∧
      ¬Fin15AnchoredAtom4147 chi ∧
      ¬Fin15AnchoredAtom4151 chi ∧
      ¬Fin15AnchoredAtom4360 chi ∧
      ¬Fin15AnchoredAtom4570 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29725
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2112 Fin15AnchoredAtom2114 Fin15AnchoredAtom2115
    Fin15AnchoredAtom2116 Fin15AnchoredAtom2153 Fin15AnchoredAtom2154 Fin15AnchoredAtom2155
    Fin15AnchoredAtom2159 Fin15AnchoredAtom2160 Fin15AnchoredAtom2161 Fin15AnchoredAtom2198
    Fin15AnchoredAtom2199 Fin15AnchoredAtom2200 Fin15AnchoredAtom2204 Fin15AnchoredAtom2205
    Fin15AnchoredAtom2206 Fin15AnchoredAtom2320 Fin15AnchoredAtom2321 Fin15AnchoredAtom2322
    Fin15AnchoredAtom2326 Fin15AnchoredAtom2363 Fin15AnchoredAtom2364 Fin15AnchoredAtom2365
    Fin15AnchoredAtom2369 Fin15AnchoredAtom2370 Fin15AnchoredAtom2371 Fin15AnchoredAtom2485
    Fin15AnchoredAtom2486 Fin15AnchoredAtom2487 Fin15AnchoredAtom2491 Fin15AnchoredAtom2605
    Fin15AnchoredAtom2606 Fin15AnchoredAtom2607 Fin15AnchoredAtom2611 Fin15AnchoredAtom2820
    Fin15AnchoredAtom3573 Fin15AnchoredAtom3574 Fin15AnchoredAtom3575 Fin15AnchoredAtom3579
    Fin15AnchoredAtom3580 Fin15AnchoredAtom3581 Fin15AnchoredAtom3695 Fin15AnchoredAtom3696
    Fin15AnchoredAtom3697 Fin15AnchoredAtom3701 Fin15AnchoredAtom3815 Fin15AnchoredAtom3816
    Fin15AnchoredAtom3817 Fin15AnchoredAtom3821 Fin15AnchoredAtom4030 Fin15AnchoredAtom4145
    Fin15AnchoredAtom4146 Fin15AnchoredAtom4147 Fin15AnchoredAtom4151 Fin15AnchoredAtom4360
    Fin15AnchoredAtom4570 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31195 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2126 chi ∧
      ¬Fin15AnchoredAtom2128 chi ∧
      ¬Fin15AnchoredAtom2129 chi ∧
      ¬Fin15AnchoredAtom2135 chi ∧
      ¬Fin15AnchoredAtom2136 chi ∧
      ¬Fin15AnchoredAtom2147 chi ∧
      ¬Fin15AnchoredAtom2207 chi ∧
      ¬Fin15AnchoredAtom2209 chi ∧
      ¬Fin15AnchoredAtom2210 chi ∧
      ¬Fin15AnchoredAtom2216 chi ∧
      ¬Fin15AnchoredAtom2217 chi ∧
      ¬Fin15AnchoredAtom2228 chi ∧
      ¬Fin15AnchoredAtom2244 chi ∧
      ¬Fin15AnchoredAtom2245 chi ∧
      ¬Fin15AnchoredAtom2256 chi ∧
      ¬Fin15AnchoredAtom2277 chi ∧
      ¬Fin15AnchoredAtom2372 chi ∧
      ¬Fin15AnchoredAtom2374 chi ∧
      ¬Fin15AnchoredAtom2375 chi ∧
      ¬Fin15AnchoredAtom2381 chi ∧
      ¬Fin15AnchoredAtom2382 chi ∧
      ¬Fin15AnchoredAtom2393 chi ∧
      ¬Fin15AnchoredAtom2409 chi ∧
      ¬Fin15AnchoredAtom2410 chi ∧
      ¬Fin15AnchoredAtom2421 chi ∧
      ¬Fin15AnchoredAtom2442 chi ∧
      ¬Fin15AnchoredAtom2613 chi ∧
      ¬Fin15AnchoredAtom2614 chi ∧
      ¬Fin15AnchoredAtom2625 chi ∧
      ¬Fin15AnchoredAtom2646 chi ∧
      ¬Fin15AnchoredAtom2702 chi ∧
      ¬Fin15AnchoredAtom3582 chi ∧
      ¬Fin15AnchoredAtom3584 chi ∧
      ¬Fin15AnchoredAtom3585 chi ∧
      ¬Fin15AnchoredAtom3591 chi ∧
      ¬Fin15AnchoredAtom3592 chi ∧
      ¬Fin15AnchoredAtom3603 chi ∧
      ¬Fin15AnchoredAtom3619 chi ∧
      ¬Fin15AnchoredAtom3620 chi ∧
      ¬Fin15AnchoredAtom3631 chi ∧
      ¬Fin15AnchoredAtom3652 chi ∧
      ¬Fin15AnchoredAtom3823 chi ∧
      ¬Fin15AnchoredAtom3824 chi ∧
      ¬Fin15AnchoredAtom3835 chi ∧
      ¬Fin15AnchoredAtom3856 chi ∧
      ¬Fin15AnchoredAtom3912 chi ∧
      ¬Fin15AnchoredAtom4153 chi ∧
      ¬Fin15AnchoredAtom4154 chi ∧
      ¬Fin15AnchoredAtom4165 chi ∧
      ¬Fin15AnchoredAtom4186 chi ∧
      ¬Fin15AnchoredAtom4242 chi ∧
      ¬Fin15AnchoredAtom4578 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 5, 6, 7, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask01773
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2117 Fin15AnchoredAtom2118 Fin15AnchoredAtom2120
    Fin15AnchoredAtom2121 Fin15AnchoredAtom2126 Fin15AnchoredAtom2128 Fin15AnchoredAtom2129
    Fin15AnchoredAtom2135 Fin15AnchoredAtom2136 Fin15AnchoredAtom2147 Fin15AnchoredAtom2207
    Fin15AnchoredAtom2209 Fin15AnchoredAtom2210 Fin15AnchoredAtom2216 Fin15AnchoredAtom2217
    Fin15AnchoredAtom2228 Fin15AnchoredAtom2244 Fin15AnchoredAtom2245 Fin15AnchoredAtom2256
    Fin15AnchoredAtom2277 Fin15AnchoredAtom2372 Fin15AnchoredAtom2374 Fin15AnchoredAtom2375
    Fin15AnchoredAtom2381 Fin15AnchoredAtom2382 Fin15AnchoredAtom2393 Fin15AnchoredAtom2409
    Fin15AnchoredAtom2410 Fin15AnchoredAtom2421 Fin15AnchoredAtom2442 Fin15AnchoredAtom2613
    Fin15AnchoredAtom2614 Fin15AnchoredAtom2625 Fin15AnchoredAtom2646 Fin15AnchoredAtom2702
    Fin15AnchoredAtom3582 Fin15AnchoredAtom3584 Fin15AnchoredAtom3585 Fin15AnchoredAtom3591
    Fin15AnchoredAtom3592 Fin15AnchoredAtom3603 Fin15AnchoredAtom3619 Fin15AnchoredAtom3620
    Fin15AnchoredAtom3631 Fin15AnchoredAtom3652 Fin15AnchoredAtom3823 Fin15AnchoredAtom3824
    Fin15AnchoredAtom3835 Fin15AnchoredAtom3856 Fin15AnchoredAtom3912 Fin15AnchoredAtom4153
    Fin15AnchoredAtom4154 Fin15AnchoredAtom4165 Fin15AnchoredAtom4186 Fin15AnchoredAtom4242
    Fin15AnchoredAtom4578 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31196 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom2126 chi ∧
      ¬Fin15AnchoredAtom2128 chi ∧
      ¬Fin15AnchoredAtom2131 chi ∧
      ¬Fin15AnchoredAtom2135 chi ∧
      ¬Fin15AnchoredAtom2138 chi ∧
      ¬Fin15AnchoredAtom2149 chi ∧
      ¬Fin15AnchoredAtom2207 chi ∧
      ¬Fin15AnchoredAtom2209 chi ∧
      ¬Fin15AnchoredAtom2212 chi ∧
      ¬Fin15AnchoredAtom2216 chi ∧
      ¬Fin15AnchoredAtom2219 chi ∧
      ¬Fin15AnchoredAtom2230 chi ∧
      ¬Fin15AnchoredAtom2244 chi ∧
      ¬Fin15AnchoredAtom2247 chi ∧
      ¬Fin15AnchoredAtom2258 chi ∧
      ¬Fin15AnchoredAtom2279 chi ∧
      ¬Fin15AnchoredAtom2372 chi ∧
      ¬Fin15AnchoredAtom2374 chi ∧
      ¬Fin15AnchoredAtom2377 chi ∧
      ¬Fin15AnchoredAtom2381 chi ∧
      ¬Fin15AnchoredAtom2384 chi ∧
      ¬Fin15AnchoredAtom2395 chi ∧
      ¬Fin15AnchoredAtom2409 chi ∧
      ¬Fin15AnchoredAtom2412 chi ∧
      ¬Fin15AnchoredAtom2423 chi ∧
      ¬Fin15AnchoredAtom2444 chi ∧
      ¬Fin15AnchoredAtom2613 chi ∧
      ¬Fin15AnchoredAtom2616 chi ∧
      ¬Fin15AnchoredAtom2627 chi ∧
      ¬Fin15AnchoredAtom2648 chi ∧
      ¬Fin15AnchoredAtom2704 chi ∧
      ¬Fin15AnchoredAtom3582 chi ∧
      ¬Fin15AnchoredAtom3584 chi ∧
      ¬Fin15AnchoredAtom3587 chi ∧
      ¬Fin15AnchoredAtom3591 chi ∧
      ¬Fin15AnchoredAtom3594 chi ∧
      ¬Fin15AnchoredAtom3605 chi ∧
      ¬Fin15AnchoredAtom3619 chi ∧
      ¬Fin15AnchoredAtom3622 chi ∧
      ¬Fin15AnchoredAtom3633 chi ∧
      ¬Fin15AnchoredAtom3654 chi ∧
      ¬Fin15AnchoredAtom3823 chi ∧
      ¬Fin15AnchoredAtom3826 chi ∧
      ¬Fin15AnchoredAtom3837 chi ∧
      ¬Fin15AnchoredAtom3858 chi ∧
      ¬Fin15AnchoredAtom3914 chi ∧
      ¬Fin15AnchoredAtom4153 chi ∧
      ¬Fin15AnchoredAtom4156 chi ∧
      ¬Fin15AnchoredAtom4167 chi ∧
      ¬Fin15AnchoredAtom4188 chi ∧
      ¬Fin15AnchoredAtom4244 chi ∧
      ¬Fin15AnchoredAtom4580 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 5, 6, 7, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask04845
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2117 Fin15AnchoredAtom2118 Fin15AnchoredAtom2120
    Fin15AnchoredAtom2123 Fin15AnchoredAtom2126 Fin15AnchoredAtom2128 Fin15AnchoredAtom2131
    Fin15AnchoredAtom2135 Fin15AnchoredAtom2138 Fin15AnchoredAtom2149 Fin15AnchoredAtom2207
    Fin15AnchoredAtom2209 Fin15AnchoredAtom2212 Fin15AnchoredAtom2216 Fin15AnchoredAtom2219
    Fin15AnchoredAtom2230 Fin15AnchoredAtom2244 Fin15AnchoredAtom2247 Fin15AnchoredAtom2258
    Fin15AnchoredAtom2279 Fin15AnchoredAtom2372 Fin15AnchoredAtom2374 Fin15AnchoredAtom2377
    Fin15AnchoredAtom2381 Fin15AnchoredAtom2384 Fin15AnchoredAtom2395 Fin15AnchoredAtom2409
    Fin15AnchoredAtom2412 Fin15AnchoredAtom2423 Fin15AnchoredAtom2444 Fin15AnchoredAtom2613
    Fin15AnchoredAtom2616 Fin15AnchoredAtom2627 Fin15AnchoredAtom2648 Fin15AnchoredAtom2704
    Fin15AnchoredAtom3582 Fin15AnchoredAtom3584 Fin15AnchoredAtom3587 Fin15AnchoredAtom3591
    Fin15AnchoredAtom3594 Fin15AnchoredAtom3605 Fin15AnchoredAtom3619 Fin15AnchoredAtom3622
    Fin15AnchoredAtom3633 Fin15AnchoredAtom3654 Fin15AnchoredAtom3823 Fin15AnchoredAtom3826
    Fin15AnchoredAtom3837 Fin15AnchoredAtom3858 Fin15AnchoredAtom3914 Fin15AnchoredAtom4153
    Fin15AnchoredAtom4156 Fin15AnchoredAtom4167 Fin15AnchoredAtom4188 Fin15AnchoredAtom4244
    Fin15AnchoredAtom4580 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31197 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom2126 chi ∧
      ¬Fin15AnchoredAtom2128 chi ∧
      ¬Fin15AnchoredAtom2132 chi ∧
      ¬Fin15AnchoredAtom2135 chi ∧
      ¬Fin15AnchoredAtom2139 chi ∧
      ¬Fin15AnchoredAtom2150 chi ∧
      ¬Fin15AnchoredAtom2207 chi ∧
      ¬Fin15AnchoredAtom2209 chi ∧
      ¬Fin15AnchoredAtom2213 chi ∧
      ¬Fin15AnchoredAtom2216 chi ∧
      ¬Fin15AnchoredAtom2220 chi ∧
      ¬Fin15AnchoredAtom2231 chi ∧
      ¬Fin15AnchoredAtom2244 chi ∧
      ¬Fin15AnchoredAtom2248 chi ∧
      ¬Fin15AnchoredAtom2259 chi ∧
      ¬Fin15AnchoredAtom2280 chi ∧
      ¬Fin15AnchoredAtom2372 chi ∧
      ¬Fin15AnchoredAtom2374 chi ∧
      ¬Fin15AnchoredAtom2378 chi ∧
      ¬Fin15AnchoredAtom2381 chi ∧
      ¬Fin15AnchoredAtom2385 chi ∧
      ¬Fin15AnchoredAtom2396 chi ∧
      ¬Fin15AnchoredAtom2409 chi ∧
      ¬Fin15AnchoredAtom2413 chi ∧
      ¬Fin15AnchoredAtom2424 chi ∧
      ¬Fin15AnchoredAtom2445 chi ∧
      ¬Fin15AnchoredAtom2613 chi ∧
      ¬Fin15AnchoredAtom2617 chi ∧
      ¬Fin15AnchoredAtom2628 chi ∧
      ¬Fin15AnchoredAtom2649 chi ∧
      ¬Fin15AnchoredAtom2705 chi ∧
      ¬Fin15AnchoredAtom3582 chi ∧
      ¬Fin15AnchoredAtom3584 chi ∧
      ¬Fin15AnchoredAtom3588 chi ∧
      ¬Fin15AnchoredAtom3591 chi ∧
      ¬Fin15AnchoredAtom3595 chi ∧
      ¬Fin15AnchoredAtom3606 chi ∧
      ¬Fin15AnchoredAtom3619 chi ∧
      ¬Fin15AnchoredAtom3623 chi ∧
      ¬Fin15AnchoredAtom3634 chi ∧
      ¬Fin15AnchoredAtom3655 chi ∧
      ¬Fin15AnchoredAtom3823 chi ∧
      ¬Fin15AnchoredAtom3827 chi ∧
      ¬Fin15AnchoredAtom3838 chi ∧
      ¬Fin15AnchoredAtom3859 chi ∧
      ¬Fin15AnchoredAtom3915 chi ∧
      ¬Fin15AnchoredAtom4153 chi ∧
      ¬Fin15AnchoredAtom4157 chi ∧
      ¬Fin15AnchoredAtom4168 chi ∧
      ¬Fin15AnchoredAtom4189 chi ∧
      ¬Fin15AnchoredAtom4245 chi ∧
      ¬Fin15AnchoredAtom4581 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 5, 6, 7, 9, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask08941
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2117 Fin15AnchoredAtom2118 Fin15AnchoredAtom2120
    Fin15AnchoredAtom2124 Fin15AnchoredAtom2126 Fin15AnchoredAtom2128 Fin15AnchoredAtom2132
    Fin15AnchoredAtom2135 Fin15AnchoredAtom2139 Fin15AnchoredAtom2150 Fin15AnchoredAtom2207
    Fin15AnchoredAtom2209 Fin15AnchoredAtom2213 Fin15AnchoredAtom2216 Fin15AnchoredAtom2220
    Fin15AnchoredAtom2231 Fin15AnchoredAtom2244 Fin15AnchoredAtom2248 Fin15AnchoredAtom2259
    Fin15AnchoredAtom2280 Fin15AnchoredAtom2372 Fin15AnchoredAtom2374 Fin15AnchoredAtom2378
    Fin15AnchoredAtom2381 Fin15AnchoredAtom2385 Fin15AnchoredAtom2396 Fin15AnchoredAtom2409
    Fin15AnchoredAtom2413 Fin15AnchoredAtom2424 Fin15AnchoredAtom2445 Fin15AnchoredAtom2613
    Fin15AnchoredAtom2617 Fin15AnchoredAtom2628 Fin15AnchoredAtom2649 Fin15AnchoredAtom2705
    Fin15AnchoredAtom3582 Fin15AnchoredAtom3584 Fin15AnchoredAtom3588 Fin15AnchoredAtom3591
    Fin15AnchoredAtom3595 Fin15AnchoredAtom3606 Fin15AnchoredAtom3619 Fin15AnchoredAtom3623
    Fin15AnchoredAtom3634 Fin15AnchoredAtom3655 Fin15AnchoredAtom3823 Fin15AnchoredAtom3827
    Fin15AnchoredAtom3838 Fin15AnchoredAtom3859 Fin15AnchoredAtom3915 Fin15AnchoredAtom4153
    Fin15AnchoredAtom4157 Fin15AnchoredAtom4168 Fin15AnchoredAtom4189 Fin15AnchoredAtom4245
    Fin15AnchoredAtom4581 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31198 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom2126 chi ∧
      ¬Fin15AnchoredAtom2128 chi ∧
      ¬Fin15AnchoredAtom2133 chi ∧
      ¬Fin15AnchoredAtom2135 chi ∧
      ¬Fin15AnchoredAtom2140 chi ∧
      ¬Fin15AnchoredAtom2151 chi ∧
      ¬Fin15AnchoredAtom2207 chi ∧
      ¬Fin15AnchoredAtom2209 chi ∧
      ¬Fin15AnchoredAtom2214 chi ∧
      ¬Fin15AnchoredAtom2216 chi ∧
      ¬Fin15AnchoredAtom2221 chi ∧
      ¬Fin15AnchoredAtom2232 chi ∧
      ¬Fin15AnchoredAtom2244 chi ∧
      ¬Fin15AnchoredAtom2249 chi ∧
      ¬Fin15AnchoredAtom2260 chi ∧
      ¬Fin15AnchoredAtom2281 chi ∧
      ¬Fin15AnchoredAtom2372 chi ∧
      ¬Fin15AnchoredAtom2374 chi ∧
      ¬Fin15AnchoredAtom2379 chi ∧
      ¬Fin15AnchoredAtom2381 chi ∧
      ¬Fin15AnchoredAtom2386 chi ∧
      ¬Fin15AnchoredAtom2397 chi ∧
      ¬Fin15AnchoredAtom2409 chi ∧
      ¬Fin15AnchoredAtom2414 chi ∧
      ¬Fin15AnchoredAtom2425 chi ∧
      ¬Fin15AnchoredAtom2446 chi ∧
      ¬Fin15AnchoredAtom2613 chi ∧
      ¬Fin15AnchoredAtom2618 chi ∧
      ¬Fin15AnchoredAtom2629 chi ∧
      ¬Fin15AnchoredAtom2650 chi ∧
      ¬Fin15AnchoredAtom2706 chi ∧
      ¬Fin15AnchoredAtom3582 chi ∧
      ¬Fin15AnchoredAtom3584 chi ∧
      ¬Fin15AnchoredAtom3589 chi ∧
      ¬Fin15AnchoredAtom3591 chi ∧
      ¬Fin15AnchoredAtom3596 chi ∧
      ¬Fin15AnchoredAtom3607 chi ∧
      ¬Fin15AnchoredAtom3619 chi ∧
      ¬Fin15AnchoredAtom3624 chi ∧
      ¬Fin15AnchoredAtom3635 chi ∧
      ¬Fin15AnchoredAtom3656 chi ∧
      ¬Fin15AnchoredAtom3823 chi ∧
      ¬Fin15AnchoredAtom3828 chi ∧
      ¬Fin15AnchoredAtom3839 chi ∧
      ¬Fin15AnchoredAtom3860 chi ∧
      ¬Fin15AnchoredAtom3916 chi ∧
      ¬Fin15AnchoredAtom4153 chi ∧
      ¬Fin15AnchoredAtom4158 chi ∧
      ¬Fin15AnchoredAtom4169 chi ∧
      ¬Fin15AnchoredAtom4190 chi ∧
      ¬Fin15AnchoredAtom4246 chi ∧
      ¬Fin15AnchoredAtom4582 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 5, 6, 7, 9, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17133
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2117 Fin15AnchoredAtom2118 Fin15AnchoredAtom2120
    Fin15AnchoredAtom2125 Fin15AnchoredAtom2126 Fin15AnchoredAtom2128 Fin15AnchoredAtom2133
    Fin15AnchoredAtom2135 Fin15AnchoredAtom2140 Fin15AnchoredAtom2151 Fin15AnchoredAtom2207
    Fin15AnchoredAtom2209 Fin15AnchoredAtom2214 Fin15AnchoredAtom2216 Fin15AnchoredAtom2221
    Fin15AnchoredAtom2232 Fin15AnchoredAtom2244 Fin15AnchoredAtom2249 Fin15AnchoredAtom2260
    Fin15AnchoredAtom2281 Fin15AnchoredAtom2372 Fin15AnchoredAtom2374 Fin15AnchoredAtom2379
    Fin15AnchoredAtom2381 Fin15AnchoredAtom2386 Fin15AnchoredAtom2397 Fin15AnchoredAtom2409
    Fin15AnchoredAtom2414 Fin15AnchoredAtom2425 Fin15AnchoredAtom2446 Fin15AnchoredAtom2613
    Fin15AnchoredAtom2618 Fin15AnchoredAtom2629 Fin15AnchoredAtom2650 Fin15AnchoredAtom2706
    Fin15AnchoredAtom3582 Fin15AnchoredAtom3584 Fin15AnchoredAtom3589 Fin15AnchoredAtom3591
    Fin15AnchoredAtom3596 Fin15AnchoredAtom3607 Fin15AnchoredAtom3619 Fin15AnchoredAtom3624
    Fin15AnchoredAtom3635 Fin15AnchoredAtom3656 Fin15AnchoredAtom3823 Fin15AnchoredAtom3828
    Fin15AnchoredAtom3839 Fin15AnchoredAtom3860 Fin15AnchoredAtom3916 Fin15AnchoredAtom4153
    Fin15AnchoredAtom4158 Fin15AnchoredAtom4169 Fin15AnchoredAtom4190 Fin15AnchoredAtom4246
    Fin15AnchoredAtom4582 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31199 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom2126 chi ∧
      ¬Fin15AnchoredAtom2129 chi ∧
      ¬Fin15AnchoredAtom2131 chi ∧
      ¬Fin15AnchoredAtom2136 chi ∧
      ¬Fin15AnchoredAtom2138 chi ∧
      ¬Fin15AnchoredAtom2153 chi ∧
      ¬Fin15AnchoredAtom2207 chi ∧
      ¬Fin15AnchoredAtom2210 chi ∧
      ¬Fin15AnchoredAtom2212 chi ∧
      ¬Fin15AnchoredAtom2217 chi ∧
      ¬Fin15AnchoredAtom2219 chi ∧
      ¬Fin15AnchoredAtom2234 chi ∧
      ¬Fin15AnchoredAtom2245 chi ∧
      ¬Fin15AnchoredAtom2247 chi ∧
      ¬Fin15AnchoredAtom2262 chi ∧
      ¬Fin15AnchoredAtom2283 chi ∧
      ¬Fin15AnchoredAtom2372 chi ∧
      ¬Fin15AnchoredAtom2375 chi ∧
      ¬Fin15AnchoredAtom2377 chi ∧
      ¬Fin15AnchoredAtom2382 chi ∧
      ¬Fin15AnchoredAtom2384 chi ∧
      ¬Fin15AnchoredAtom2399 chi ∧
      ¬Fin15AnchoredAtom2410 chi ∧
      ¬Fin15AnchoredAtom2412 chi ∧
      ¬Fin15AnchoredAtom2427 chi ∧
      ¬Fin15AnchoredAtom2448 chi ∧
      ¬Fin15AnchoredAtom2614 chi ∧
      ¬Fin15AnchoredAtom2616 chi ∧
      ¬Fin15AnchoredAtom2631 chi ∧
      ¬Fin15AnchoredAtom2652 chi ∧
      ¬Fin15AnchoredAtom2708 chi ∧
      ¬Fin15AnchoredAtom3582 chi ∧
      ¬Fin15AnchoredAtom3585 chi ∧
      ¬Fin15AnchoredAtom3587 chi ∧
      ¬Fin15AnchoredAtom3592 chi ∧
      ¬Fin15AnchoredAtom3594 chi ∧
      ¬Fin15AnchoredAtom3609 chi ∧
      ¬Fin15AnchoredAtom3620 chi ∧
      ¬Fin15AnchoredAtom3622 chi ∧
      ¬Fin15AnchoredAtom3637 chi ∧
      ¬Fin15AnchoredAtom3658 chi ∧
      ¬Fin15AnchoredAtom3824 chi ∧
      ¬Fin15AnchoredAtom3826 chi ∧
      ¬Fin15AnchoredAtom3841 chi ∧
      ¬Fin15AnchoredAtom3862 chi ∧
      ¬Fin15AnchoredAtom3918 chi ∧
      ¬Fin15AnchoredAtom4154 chi ∧
      ¬Fin15AnchoredAtom4156 chi ∧
      ¬Fin15AnchoredAtom4171 chi ∧
      ¬Fin15AnchoredAtom4192 chi ∧
      ¬Fin15AnchoredAtom4248 chi ∧
      ¬Fin15AnchoredAtom4584 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 5, 6, 7, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05357
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2117 Fin15AnchoredAtom2118 Fin15AnchoredAtom2121
    Fin15AnchoredAtom2123 Fin15AnchoredAtom2126 Fin15AnchoredAtom2129 Fin15AnchoredAtom2131
    Fin15AnchoredAtom2136 Fin15AnchoredAtom2138 Fin15AnchoredAtom2153 Fin15AnchoredAtom2207
    Fin15AnchoredAtom2210 Fin15AnchoredAtom2212 Fin15AnchoredAtom2217 Fin15AnchoredAtom2219
    Fin15AnchoredAtom2234 Fin15AnchoredAtom2245 Fin15AnchoredAtom2247 Fin15AnchoredAtom2262
    Fin15AnchoredAtom2283 Fin15AnchoredAtom2372 Fin15AnchoredAtom2375 Fin15AnchoredAtom2377
    Fin15AnchoredAtom2382 Fin15AnchoredAtom2384 Fin15AnchoredAtom2399 Fin15AnchoredAtom2410
    Fin15AnchoredAtom2412 Fin15AnchoredAtom2427 Fin15AnchoredAtom2448 Fin15AnchoredAtom2614
    Fin15AnchoredAtom2616 Fin15AnchoredAtom2631 Fin15AnchoredAtom2652 Fin15AnchoredAtom2708
    Fin15AnchoredAtom3582 Fin15AnchoredAtom3585 Fin15AnchoredAtom3587 Fin15AnchoredAtom3592
    Fin15AnchoredAtom3594 Fin15AnchoredAtom3609 Fin15AnchoredAtom3620 Fin15AnchoredAtom3622
    Fin15AnchoredAtom3637 Fin15AnchoredAtom3658 Fin15AnchoredAtom3824 Fin15AnchoredAtom3826
    Fin15AnchoredAtom3841 Fin15AnchoredAtom3862 Fin15AnchoredAtom3918 Fin15AnchoredAtom4154
    Fin15AnchoredAtom4156 Fin15AnchoredAtom4171 Fin15AnchoredAtom4192 Fin15AnchoredAtom4248
    Fin15AnchoredAtom4584 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31200 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom2126 chi ∧
      ¬Fin15AnchoredAtom2129 chi ∧
      ¬Fin15AnchoredAtom2132 chi ∧
      ¬Fin15AnchoredAtom2136 chi ∧
      ¬Fin15AnchoredAtom2139 chi ∧
      ¬Fin15AnchoredAtom2154 chi ∧
      ¬Fin15AnchoredAtom2207 chi ∧
      ¬Fin15AnchoredAtom2210 chi ∧
      ¬Fin15AnchoredAtom2213 chi ∧
      ¬Fin15AnchoredAtom2217 chi ∧
      ¬Fin15AnchoredAtom2220 chi ∧
      ¬Fin15AnchoredAtom2235 chi ∧
      ¬Fin15AnchoredAtom2245 chi ∧
      ¬Fin15AnchoredAtom2248 chi ∧
      ¬Fin15AnchoredAtom2263 chi ∧
      ¬Fin15AnchoredAtom2284 chi ∧
      ¬Fin15AnchoredAtom2372 chi ∧
      ¬Fin15AnchoredAtom2375 chi ∧
      ¬Fin15AnchoredAtom2378 chi ∧
      ¬Fin15AnchoredAtom2382 chi ∧
      ¬Fin15AnchoredAtom2385 chi ∧
      ¬Fin15AnchoredAtom2400 chi ∧
      ¬Fin15AnchoredAtom2410 chi ∧
      ¬Fin15AnchoredAtom2413 chi ∧
      ¬Fin15AnchoredAtom2428 chi ∧
      ¬Fin15AnchoredAtom2449 chi ∧
      ¬Fin15AnchoredAtom2614 chi ∧
      ¬Fin15AnchoredAtom2617 chi ∧
      ¬Fin15AnchoredAtom2632 chi ∧
      ¬Fin15AnchoredAtom2653 chi ∧
      ¬Fin15AnchoredAtom2709 chi ∧
      ¬Fin15AnchoredAtom3582 chi ∧
      ¬Fin15AnchoredAtom3585 chi ∧
      ¬Fin15AnchoredAtom3588 chi ∧
      ¬Fin15AnchoredAtom3592 chi ∧
      ¬Fin15AnchoredAtom3595 chi ∧
      ¬Fin15AnchoredAtom3610 chi ∧
      ¬Fin15AnchoredAtom3620 chi ∧
      ¬Fin15AnchoredAtom3623 chi ∧
      ¬Fin15AnchoredAtom3638 chi ∧
      ¬Fin15AnchoredAtom3659 chi ∧
      ¬Fin15AnchoredAtom3824 chi ∧
      ¬Fin15AnchoredAtom3827 chi ∧
      ¬Fin15AnchoredAtom3842 chi ∧
      ¬Fin15AnchoredAtom3863 chi ∧
      ¬Fin15AnchoredAtom3919 chi ∧
      ¬Fin15AnchoredAtom4154 chi ∧
      ¬Fin15AnchoredAtom4157 chi ∧
      ¬Fin15AnchoredAtom4172 chi ∧
      ¬Fin15AnchoredAtom4193 chi ∧
      ¬Fin15AnchoredAtom4249 chi ∧
      ¬Fin15AnchoredAtom4585 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 5, 6, 7, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09453
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2117 Fin15AnchoredAtom2118 Fin15AnchoredAtom2121
    Fin15AnchoredAtom2124 Fin15AnchoredAtom2126 Fin15AnchoredAtom2129 Fin15AnchoredAtom2132
    Fin15AnchoredAtom2136 Fin15AnchoredAtom2139 Fin15AnchoredAtom2154 Fin15AnchoredAtom2207
    Fin15AnchoredAtom2210 Fin15AnchoredAtom2213 Fin15AnchoredAtom2217 Fin15AnchoredAtom2220
    Fin15AnchoredAtom2235 Fin15AnchoredAtom2245 Fin15AnchoredAtom2248 Fin15AnchoredAtom2263
    Fin15AnchoredAtom2284 Fin15AnchoredAtom2372 Fin15AnchoredAtom2375 Fin15AnchoredAtom2378
    Fin15AnchoredAtom2382 Fin15AnchoredAtom2385 Fin15AnchoredAtom2400 Fin15AnchoredAtom2410
    Fin15AnchoredAtom2413 Fin15AnchoredAtom2428 Fin15AnchoredAtom2449 Fin15AnchoredAtom2614
    Fin15AnchoredAtom2617 Fin15AnchoredAtom2632 Fin15AnchoredAtom2653 Fin15AnchoredAtom2709
    Fin15AnchoredAtom3582 Fin15AnchoredAtom3585 Fin15AnchoredAtom3588 Fin15AnchoredAtom3592
    Fin15AnchoredAtom3595 Fin15AnchoredAtom3610 Fin15AnchoredAtom3620 Fin15AnchoredAtom3623
    Fin15AnchoredAtom3638 Fin15AnchoredAtom3659 Fin15AnchoredAtom3824 Fin15AnchoredAtom3827
    Fin15AnchoredAtom3842 Fin15AnchoredAtom3863 Fin15AnchoredAtom3919 Fin15AnchoredAtom4154
    Fin15AnchoredAtom4157 Fin15AnchoredAtom4172 Fin15AnchoredAtom4193 Fin15AnchoredAtom4249
    Fin15AnchoredAtom4585 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31201 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom2126 chi ∧
      ¬Fin15AnchoredAtom2129 chi ∧
      ¬Fin15AnchoredAtom2133 chi ∧
      ¬Fin15AnchoredAtom2136 chi ∧
      ¬Fin15AnchoredAtom2140 chi ∧
      ¬Fin15AnchoredAtom2155 chi ∧
      ¬Fin15AnchoredAtom2207 chi ∧
      ¬Fin15AnchoredAtom2210 chi ∧
      ¬Fin15AnchoredAtom2214 chi ∧
      ¬Fin15AnchoredAtom2217 chi ∧
      ¬Fin15AnchoredAtom2221 chi ∧
      ¬Fin15AnchoredAtom2236 chi ∧
      ¬Fin15AnchoredAtom2245 chi ∧
      ¬Fin15AnchoredAtom2249 chi ∧
      ¬Fin15AnchoredAtom2264 chi ∧
      ¬Fin15AnchoredAtom2285 chi ∧
      ¬Fin15AnchoredAtom2372 chi ∧
      ¬Fin15AnchoredAtom2375 chi ∧
      ¬Fin15AnchoredAtom2379 chi ∧
      ¬Fin15AnchoredAtom2382 chi ∧
      ¬Fin15AnchoredAtom2386 chi ∧
      ¬Fin15AnchoredAtom2401 chi ∧
      ¬Fin15AnchoredAtom2410 chi ∧
      ¬Fin15AnchoredAtom2414 chi ∧
      ¬Fin15AnchoredAtom2429 chi ∧
      ¬Fin15AnchoredAtom2450 chi ∧
      ¬Fin15AnchoredAtom2614 chi ∧
      ¬Fin15AnchoredAtom2618 chi ∧
      ¬Fin15AnchoredAtom2633 chi ∧
      ¬Fin15AnchoredAtom2654 chi ∧
      ¬Fin15AnchoredAtom2710 chi ∧
      ¬Fin15AnchoredAtom3582 chi ∧
      ¬Fin15AnchoredAtom3585 chi ∧
      ¬Fin15AnchoredAtom3589 chi ∧
      ¬Fin15AnchoredAtom3592 chi ∧
      ¬Fin15AnchoredAtom3596 chi ∧
      ¬Fin15AnchoredAtom3611 chi ∧
      ¬Fin15AnchoredAtom3620 chi ∧
      ¬Fin15AnchoredAtom3624 chi ∧
      ¬Fin15AnchoredAtom3639 chi ∧
      ¬Fin15AnchoredAtom3660 chi ∧
      ¬Fin15AnchoredAtom3824 chi ∧
      ¬Fin15AnchoredAtom3828 chi ∧
      ¬Fin15AnchoredAtom3843 chi ∧
      ¬Fin15AnchoredAtom3864 chi ∧
      ¬Fin15AnchoredAtom3920 chi ∧
      ¬Fin15AnchoredAtom4154 chi ∧
      ¬Fin15AnchoredAtom4158 chi ∧
      ¬Fin15AnchoredAtom4173 chi ∧
      ¬Fin15AnchoredAtom4194 chi ∧
      ¬Fin15AnchoredAtom4250 chi ∧
      ¬Fin15AnchoredAtom4586 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 5, 6, 7, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17645
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2117 Fin15AnchoredAtom2118 Fin15AnchoredAtom2121
    Fin15AnchoredAtom2125 Fin15AnchoredAtom2126 Fin15AnchoredAtom2129 Fin15AnchoredAtom2133
    Fin15AnchoredAtom2136 Fin15AnchoredAtom2140 Fin15AnchoredAtom2155 Fin15AnchoredAtom2207
    Fin15AnchoredAtom2210 Fin15AnchoredAtom2214 Fin15AnchoredAtom2217 Fin15AnchoredAtom2221
    Fin15AnchoredAtom2236 Fin15AnchoredAtom2245 Fin15AnchoredAtom2249 Fin15AnchoredAtom2264
    Fin15AnchoredAtom2285 Fin15AnchoredAtom2372 Fin15AnchoredAtom2375 Fin15AnchoredAtom2379
    Fin15AnchoredAtom2382 Fin15AnchoredAtom2386 Fin15AnchoredAtom2401 Fin15AnchoredAtom2410
    Fin15AnchoredAtom2414 Fin15AnchoredAtom2429 Fin15AnchoredAtom2450 Fin15AnchoredAtom2614
    Fin15AnchoredAtom2618 Fin15AnchoredAtom2633 Fin15AnchoredAtom2654 Fin15AnchoredAtom2710
    Fin15AnchoredAtom3582 Fin15AnchoredAtom3585 Fin15AnchoredAtom3589 Fin15AnchoredAtom3592
    Fin15AnchoredAtom3596 Fin15AnchoredAtom3611 Fin15AnchoredAtom3620 Fin15AnchoredAtom3624
    Fin15AnchoredAtom3639 Fin15AnchoredAtom3660 Fin15AnchoredAtom3824 Fin15AnchoredAtom3828
    Fin15AnchoredAtom3843 Fin15AnchoredAtom3864 Fin15AnchoredAtom3920 Fin15AnchoredAtom4154
    Fin15AnchoredAtom4158 Fin15AnchoredAtom4173 Fin15AnchoredAtom4194 Fin15AnchoredAtom4250
    Fin15AnchoredAtom4586 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31202 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom2126 chi ∧
      ¬Fin15AnchoredAtom2131 chi ∧
      ¬Fin15AnchoredAtom2132 chi ∧
      ¬Fin15AnchoredAtom2138 chi ∧
      ¬Fin15AnchoredAtom2139 chi ∧
      ¬Fin15AnchoredAtom2159 chi ∧
      ¬Fin15AnchoredAtom2207 chi ∧
      ¬Fin15AnchoredAtom2212 chi ∧
      ¬Fin15AnchoredAtom2213 chi ∧
      ¬Fin15AnchoredAtom2219 chi ∧
      ¬Fin15AnchoredAtom2220 chi ∧
      ¬Fin15AnchoredAtom2240 chi ∧
      ¬Fin15AnchoredAtom2247 chi ∧
      ¬Fin15AnchoredAtom2248 chi ∧
      ¬Fin15AnchoredAtom2268 chi ∧
      ¬Fin15AnchoredAtom2289 chi ∧
      ¬Fin15AnchoredAtom2372 chi ∧
      ¬Fin15AnchoredAtom2377 chi ∧
      ¬Fin15AnchoredAtom2378 chi ∧
      ¬Fin15AnchoredAtom2384 chi ∧
      ¬Fin15AnchoredAtom2385 chi ∧
      ¬Fin15AnchoredAtom2405 chi ∧
      ¬Fin15AnchoredAtom2412 chi ∧
      ¬Fin15AnchoredAtom2413 chi ∧
      ¬Fin15AnchoredAtom2433 chi ∧
      ¬Fin15AnchoredAtom2454 chi ∧
      ¬Fin15AnchoredAtom2616 chi ∧
      ¬Fin15AnchoredAtom2617 chi ∧
      ¬Fin15AnchoredAtom2637 chi ∧
      ¬Fin15AnchoredAtom2658 chi ∧
      ¬Fin15AnchoredAtom2714 chi ∧
      ¬Fin15AnchoredAtom3582 chi ∧
      ¬Fin15AnchoredAtom3587 chi ∧
      ¬Fin15AnchoredAtom3588 chi ∧
      ¬Fin15AnchoredAtom3594 chi ∧
      ¬Fin15AnchoredAtom3595 chi ∧
      ¬Fin15AnchoredAtom3615 chi ∧
      ¬Fin15AnchoredAtom3622 chi ∧
      ¬Fin15AnchoredAtom3623 chi ∧
      ¬Fin15AnchoredAtom3643 chi ∧
      ¬Fin15AnchoredAtom3664 chi ∧
      ¬Fin15AnchoredAtom3826 chi ∧
      ¬Fin15AnchoredAtom3827 chi ∧
      ¬Fin15AnchoredAtom3847 chi ∧
      ¬Fin15AnchoredAtom3868 chi ∧
      ¬Fin15AnchoredAtom3924 chi ∧
      ¬Fin15AnchoredAtom4156 chi ∧
      ¬Fin15AnchoredAtom4157 chi ∧
      ¬Fin15AnchoredAtom4177 chi ∧
      ¬Fin15AnchoredAtom4198 chi ∧
      ¬Fin15AnchoredAtom4254 chi ∧
      ¬Fin15AnchoredAtom4590 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 5, 6, 7, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask12525
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2117 Fin15AnchoredAtom2118 Fin15AnchoredAtom2123
    Fin15AnchoredAtom2124 Fin15AnchoredAtom2126 Fin15AnchoredAtom2131 Fin15AnchoredAtom2132
    Fin15AnchoredAtom2138 Fin15AnchoredAtom2139 Fin15AnchoredAtom2159 Fin15AnchoredAtom2207
    Fin15AnchoredAtom2212 Fin15AnchoredAtom2213 Fin15AnchoredAtom2219 Fin15AnchoredAtom2220
    Fin15AnchoredAtom2240 Fin15AnchoredAtom2247 Fin15AnchoredAtom2248 Fin15AnchoredAtom2268
    Fin15AnchoredAtom2289 Fin15AnchoredAtom2372 Fin15AnchoredAtom2377 Fin15AnchoredAtom2378
    Fin15AnchoredAtom2384 Fin15AnchoredAtom2385 Fin15AnchoredAtom2405 Fin15AnchoredAtom2412
    Fin15AnchoredAtom2413 Fin15AnchoredAtom2433 Fin15AnchoredAtom2454 Fin15AnchoredAtom2616
    Fin15AnchoredAtom2617 Fin15AnchoredAtom2637 Fin15AnchoredAtom2658 Fin15AnchoredAtom2714
    Fin15AnchoredAtom3582 Fin15AnchoredAtom3587 Fin15AnchoredAtom3588 Fin15AnchoredAtom3594
    Fin15AnchoredAtom3595 Fin15AnchoredAtom3615 Fin15AnchoredAtom3622 Fin15AnchoredAtom3623
    Fin15AnchoredAtom3643 Fin15AnchoredAtom3664 Fin15AnchoredAtom3826 Fin15AnchoredAtom3827
    Fin15AnchoredAtom3847 Fin15AnchoredAtom3868 Fin15AnchoredAtom3924 Fin15AnchoredAtom4156
    Fin15AnchoredAtom4157 Fin15AnchoredAtom4177 Fin15AnchoredAtom4198 Fin15AnchoredAtom4254
    Fin15AnchoredAtom4590 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31203 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom2126 chi ∧
      ¬Fin15AnchoredAtom2131 chi ∧
      ¬Fin15AnchoredAtom2133 chi ∧
      ¬Fin15AnchoredAtom2138 chi ∧
      ¬Fin15AnchoredAtom2140 chi ∧
      ¬Fin15AnchoredAtom2160 chi ∧
      ¬Fin15AnchoredAtom2207 chi ∧
      ¬Fin15AnchoredAtom2212 chi ∧
      ¬Fin15AnchoredAtom2214 chi ∧
      ¬Fin15AnchoredAtom2219 chi ∧
      ¬Fin15AnchoredAtom2221 chi ∧
      ¬Fin15AnchoredAtom2241 chi ∧
      ¬Fin15AnchoredAtom2247 chi ∧
      ¬Fin15AnchoredAtom2249 chi ∧
      ¬Fin15AnchoredAtom2269 chi ∧
      ¬Fin15AnchoredAtom2290 chi ∧
      ¬Fin15AnchoredAtom2372 chi ∧
      ¬Fin15AnchoredAtom2377 chi ∧
      ¬Fin15AnchoredAtom2379 chi ∧
      ¬Fin15AnchoredAtom2384 chi ∧
      ¬Fin15AnchoredAtom2386 chi ∧
      ¬Fin15AnchoredAtom2406 chi ∧
      ¬Fin15AnchoredAtom2412 chi ∧
      ¬Fin15AnchoredAtom2414 chi ∧
      ¬Fin15AnchoredAtom2434 chi ∧
      ¬Fin15AnchoredAtom2455 chi ∧
      ¬Fin15AnchoredAtom2616 chi ∧
      ¬Fin15AnchoredAtom2618 chi ∧
      ¬Fin15AnchoredAtom2638 chi ∧
      ¬Fin15AnchoredAtom2659 chi ∧
      ¬Fin15AnchoredAtom2715 chi ∧
      ¬Fin15AnchoredAtom3582 chi ∧
      ¬Fin15AnchoredAtom3587 chi ∧
      ¬Fin15AnchoredAtom3589 chi ∧
      ¬Fin15AnchoredAtom3594 chi ∧
      ¬Fin15AnchoredAtom3596 chi ∧
      ¬Fin15AnchoredAtom3616 chi ∧
      ¬Fin15AnchoredAtom3622 chi ∧
      ¬Fin15AnchoredAtom3624 chi ∧
      ¬Fin15AnchoredAtom3644 chi ∧
      ¬Fin15AnchoredAtom3665 chi ∧
      ¬Fin15AnchoredAtom3826 chi ∧
      ¬Fin15AnchoredAtom3828 chi ∧
      ¬Fin15AnchoredAtom3848 chi ∧
      ¬Fin15AnchoredAtom3869 chi ∧
      ¬Fin15AnchoredAtom3925 chi ∧
      ¬Fin15AnchoredAtom4156 chi ∧
      ¬Fin15AnchoredAtom4158 chi ∧
      ¬Fin15AnchoredAtom4178 chi ∧
      ¬Fin15AnchoredAtom4199 chi ∧
      ¬Fin15AnchoredAtom4255 chi ∧
      ¬Fin15AnchoredAtom4591 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 5, 6, 7, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask20717
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2117 Fin15AnchoredAtom2118 Fin15AnchoredAtom2123
    Fin15AnchoredAtom2125 Fin15AnchoredAtom2126 Fin15AnchoredAtom2131 Fin15AnchoredAtom2133
    Fin15AnchoredAtom2138 Fin15AnchoredAtom2140 Fin15AnchoredAtom2160 Fin15AnchoredAtom2207
    Fin15AnchoredAtom2212 Fin15AnchoredAtom2214 Fin15AnchoredAtom2219 Fin15AnchoredAtom2221
    Fin15AnchoredAtom2241 Fin15AnchoredAtom2247 Fin15AnchoredAtom2249 Fin15AnchoredAtom2269
    Fin15AnchoredAtom2290 Fin15AnchoredAtom2372 Fin15AnchoredAtom2377 Fin15AnchoredAtom2379
    Fin15AnchoredAtom2384 Fin15AnchoredAtom2386 Fin15AnchoredAtom2406 Fin15AnchoredAtom2412
    Fin15AnchoredAtom2414 Fin15AnchoredAtom2434 Fin15AnchoredAtom2455 Fin15AnchoredAtom2616
    Fin15AnchoredAtom2618 Fin15AnchoredAtom2638 Fin15AnchoredAtom2659 Fin15AnchoredAtom2715
    Fin15AnchoredAtom3582 Fin15AnchoredAtom3587 Fin15AnchoredAtom3589 Fin15AnchoredAtom3594
    Fin15AnchoredAtom3596 Fin15AnchoredAtom3616 Fin15AnchoredAtom3622 Fin15AnchoredAtom3624
    Fin15AnchoredAtom3644 Fin15AnchoredAtom3665 Fin15AnchoredAtom3826 Fin15AnchoredAtom3828
    Fin15AnchoredAtom3848 Fin15AnchoredAtom3869 Fin15AnchoredAtom3925 Fin15AnchoredAtom4156
    Fin15AnchoredAtom4158 Fin15AnchoredAtom4178 Fin15AnchoredAtom4199 Fin15AnchoredAtom4255
    Fin15AnchoredAtom4591 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31204 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom2126 chi ∧
      ¬Fin15AnchoredAtom2132 chi ∧
      ¬Fin15AnchoredAtom2133 chi ∧
      ¬Fin15AnchoredAtom2139 chi ∧
      ¬Fin15AnchoredAtom2140 chi ∧
      ¬Fin15AnchoredAtom2161 chi ∧
      ¬Fin15AnchoredAtom2207 chi ∧
      ¬Fin15AnchoredAtom2213 chi ∧
      ¬Fin15AnchoredAtom2214 chi ∧
      ¬Fin15AnchoredAtom2220 chi ∧
      ¬Fin15AnchoredAtom2221 chi ∧
      ¬Fin15AnchoredAtom2242 chi ∧
      ¬Fin15AnchoredAtom2248 chi ∧
      ¬Fin15AnchoredAtom2249 chi ∧
      ¬Fin15AnchoredAtom2270 chi ∧
      ¬Fin15AnchoredAtom2291 chi ∧
      ¬Fin15AnchoredAtom2372 chi ∧
      ¬Fin15AnchoredAtom2378 chi ∧
      ¬Fin15AnchoredAtom2379 chi ∧
      ¬Fin15AnchoredAtom2385 chi ∧
      ¬Fin15AnchoredAtom2386 chi ∧
      ¬Fin15AnchoredAtom2407 chi ∧
      ¬Fin15AnchoredAtom2413 chi ∧
      ¬Fin15AnchoredAtom2414 chi ∧
      ¬Fin15AnchoredAtom2435 chi ∧
      ¬Fin15AnchoredAtom2456 chi ∧
      ¬Fin15AnchoredAtom2617 chi ∧
      ¬Fin15AnchoredAtom2618 chi ∧
      ¬Fin15AnchoredAtom2639 chi ∧
      ¬Fin15AnchoredAtom2660 chi ∧
      ¬Fin15AnchoredAtom2716 chi ∧
      ¬Fin15AnchoredAtom3582 chi ∧
      ¬Fin15AnchoredAtom3588 chi ∧
      ¬Fin15AnchoredAtom3589 chi ∧
      ¬Fin15AnchoredAtom3595 chi ∧
      ¬Fin15AnchoredAtom3596 chi ∧
      ¬Fin15AnchoredAtom3617 chi ∧
      ¬Fin15AnchoredAtom3623 chi ∧
      ¬Fin15AnchoredAtom3624 chi ∧
      ¬Fin15AnchoredAtom3645 chi ∧
      ¬Fin15AnchoredAtom3666 chi ∧
      ¬Fin15AnchoredAtom3827 chi ∧
      ¬Fin15AnchoredAtom3828 chi ∧
      ¬Fin15AnchoredAtom3849 chi ∧
      ¬Fin15AnchoredAtom3870 chi ∧
      ¬Fin15AnchoredAtom3926 chi ∧
      ¬Fin15AnchoredAtom4157 chi ∧
      ¬Fin15AnchoredAtom4158 chi ∧
      ¬Fin15AnchoredAtom4179 chi ∧
      ¬Fin15AnchoredAtom4200 chi ∧
      ¬Fin15AnchoredAtom4256 chi ∧
      ¬Fin15AnchoredAtom4592 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 5, 6, 7, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask24813
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2117 Fin15AnchoredAtom2118 Fin15AnchoredAtom2124
    Fin15AnchoredAtom2125 Fin15AnchoredAtom2126 Fin15AnchoredAtom2132 Fin15AnchoredAtom2133
    Fin15AnchoredAtom2139 Fin15AnchoredAtom2140 Fin15AnchoredAtom2161 Fin15AnchoredAtom2207
    Fin15AnchoredAtom2213 Fin15AnchoredAtom2214 Fin15AnchoredAtom2220 Fin15AnchoredAtom2221
    Fin15AnchoredAtom2242 Fin15AnchoredAtom2248 Fin15AnchoredAtom2249 Fin15AnchoredAtom2270
    Fin15AnchoredAtom2291 Fin15AnchoredAtom2372 Fin15AnchoredAtom2378 Fin15AnchoredAtom2379
    Fin15AnchoredAtom2385 Fin15AnchoredAtom2386 Fin15AnchoredAtom2407 Fin15AnchoredAtom2413
    Fin15AnchoredAtom2414 Fin15AnchoredAtom2435 Fin15AnchoredAtom2456 Fin15AnchoredAtom2617
    Fin15AnchoredAtom2618 Fin15AnchoredAtom2639 Fin15AnchoredAtom2660 Fin15AnchoredAtom2716
    Fin15AnchoredAtom3582 Fin15AnchoredAtom3588 Fin15AnchoredAtom3589 Fin15AnchoredAtom3595
    Fin15AnchoredAtom3596 Fin15AnchoredAtom3617 Fin15AnchoredAtom3623 Fin15AnchoredAtom3624
    Fin15AnchoredAtom3645 Fin15AnchoredAtom3666 Fin15AnchoredAtom3827 Fin15AnchoredAtom3828
    Fin15AnchoredAtom3849 Fin15AnchoredAtom3870 Fin15AnchoredAtom3926 Fin15AnchoredAtom4157
    Fin15AnchoredAtom4158 Fin15AnchoredAtom4179 Fin15AnchoredAtom4200 Fin15AnchoredAtom4256
    Fin15AnchoredAtom4592 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31205 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom2128 chi ∧
      ¬Fin15AnchoredAtom2129 chi ∧
      ¬Fin15AnchoredAtom2131 chi ∧
      ¬Fin15AnchoredAtom2147 chi ∧
      ¬Fin15AnchoredAtom2149 chi ∧
      ¬Fin15AnchoredAtom2153 chi ∧
      ¬Fin15AnchoredAtom2209 chi ∧
      ¬Fin15AnchoredAtom2210 chi ∧
      ¬Fin15AnchoredAtom2212 chi ∧
      ¬Fin15AnchoredAtom2228 chi ∧
      ¬Fin15AnchoredAtom2230 chi ∧
      ¬Fin15AnchoredAtom2234 chi ∧
      ¬Fin15AnchoredAtom2256 chi ∧
      ¬Fin15AnchoredAtom2258 chi ∧
      ¬Fin15AnchoredAtom2262 chi ∧
      ¬Fin15AnchoredAtom2308 chi ∧
      ¬Fin15AnchoredAtom2374 chi ∧
      ¬Fin15AnchoredAtom2375 chi ∧
      ¬Fin15AnchoredAtom2377 chi ∧
      ¬Fin15AnchoredAtom2393 chi ∧
      ¬Fin15AnchoredAtom2395 chi ∧
      ¬Fin15AnchoredAtom2399 chi ∧
      ¬Fin15AnchoredAtom2421 chi ∧
      ¬Fin15AnchoredAtom2423 chi ∧
      ¬Fin15AnchoredAtom2427 chi ∧
      ¬Fin15AnchoredAtom2473 chi ∧
      ¬Fin15AnchoredAtom2625 chi ∧
      ¬Fin15AnchoredAtom2627 chi ∧
      ¬Fin15AnchoredAtom2631 chi ∧
      ¬Fin15AnchoredAtom2677 chi ∧
      ¬Fin15AnchoredAtom2733 chi ∧
      ¬Fin15AnchoredAtom3584 chi ∧
      ¬Fin15AnchoredAtom3585 chi ∧
      ¬Fin15AnchoredAtom3587 chi ∧
      ¬Fin15AnchoredAtom3603 chi ∧
      ¬Fin15AnchoredAtom3605 chi ∧
      ¬Fin15AnchoredAtom3609 chi ∧
      ¬Fin15AnchoredAtom3631 chi ∧
      ¬Fin15AnchoredAtom3633 chi ∧
      ¬Fin15AnchoredAtom3637 chi ∧
      ¬Fin15AnchoredAtom3683 chi ∧
      ¬Fin15AnchoredAtom3835 chi ∧
      ¬Fin15AnchoredAtom3837 chi ∧
      ¬Fin15AnchoredAtom3841 chi ∧
      ¬Fin15AnchoredAtom3887 chi ∧
      ¬Fin15AnchoredAtom3943 chi ∧
      ¬Fin15AnchoredAtom4165 chi ∧
      ¬Fin15AnchoredAtom4167 chi ∧
      ¬Fin15AnchoredAtom4171 chi ∧
      ¬Fin15AnchoredAtom4217 chi ∧
      ¬Fin15AnchoredAtom4273 chi ∧
      ¬Fin15AnchoredAtom4609 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 5, 6, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05741
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2117 Fin15AnchoredAtom2120 Fin15AnchoredAtom2121
    Fin15AnchoredAtom2123 Fin15AnchoredAtom2128 Fin15AnchoredAtom2129 Fin15AnchoredAtom2131
    Fin15AnchoredAtom2147 Fin15AnchoredAtom2149 Fin15AnchoredAtom2153 Fin15AnchoredAtom2209
    Fin15AnchoredAtom2210 Fin15AnchoredAtom2212 Fin15AnchoredAtom2228 Fin15AnchoredAtom2230
    Fin15AnchoredAtom2234 Fin15AnchoredAtom2256 Fin15AnchoredAtom2258 Fin15AnchoredAtom2262
    Fin15AnchoredAtom2308 Fin15AnchoredAtom2374 Fin15AnchoredAtom2375 Fin15AnchoredAtom2377
    Fin15AnchoredAtom2393 Fin15AnchoredAtom2395 Fin15AnchoredAtom2399 Fin15AnchoredAtom2421
    Fin15AnchoredAtom2423 Fin15AnchoredAtom2427 Fin15AnchoredAtom2473 Fin15AnchoredAtom2625
    Fin15AnchoredAtom2627 Fin15AnchoredAtom2631 Fin15AnchoredAtom2677 Fin15AnchoredAtom2733
    Fin15AnchoredAtom3584 Fin15AnchoredAtom3585 Fin15AnchoredAtom3587 Fin15AnchoredAtom3603
    Fin15AnchoredAtom3605 Fin15AnchoredAtom3609 Fin15AnchoredAtom3631 Fin15AnchoredAtom3633
    Fin15AnchoredAtom3637 Fin15AnchoredAtom3683 Fin15AnchoredAtom3835 Fin15AnchoredAtom3837
    Fin15AnchoredAtom3841 Fin15AnchoredAtom3887 Fin15AnchoredAtom3943 Fin15AnchoredAtom4165
    Fin15AnchoredAtom4167 Fin15AnchoredAtom4171 Fin15AnchoredAtom4217 Fin15AnchoredAtom4273
    Fin15AnchoredAtom4609 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31206 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom2128 chi ∧
      ¬Fin15AnchoredAtom2129 chi ∧
      ¬Fin15AnchoredAtom2132 chi ∧
      ¬Fin15AnchoredAtom2147 chi ∧
      ¬Fin15AnchoredAtom2150 chi ∧
      ¬Fin15AnchoredAtom2154 chi ∧
      ¬Fin15AnchoredAtom2209 chi ∧
      ¬Fin15AnchoredAtom2210 chi ∧
      ¬Fin15AnchoredAtom2213 chi ∧
      ¬Fin15AnchoredAtom2228 chi ∧
      ¬Fin15AnchoredAtom2231 chi ∧
      ¬Fin15AnchoredAtom2235 chi ∧
      ¬Fin15AnchoredAtom2256 chi ∧
      ¬Fin15AnchoredAtom2259 chi ∧
      ¬Fin15AnchoredAtom2263 chi ∧
      ¬Fin15AnchoredAtom2309 chi ∧
      ¬Fin15AnchoredAtom2374 chi ∧
      ¬Fin15AnchoredAtom2375 chi ∧
      ¬Fin15AnchoredAtom2378 chi ∧
      ¬Fin15AnchoredAtom2393 chi ∧
      ¬Fin15AnchoredAtom2396 chi ∧
      ¬Fin15AnchoredAtom2400 chi ∧
      ¬Fin15AnchoredAtom2421 chi ∧
      ¬Fin15AnchoredAtom2424 chi ∧
      ¬Fin15AnchoredAtom2428 chi ∧
      ¬Fin15AnchoredAtom2474 chi ∧
      ¬Fin15AnchoredAtom2625 chi ∧
      ¬Fin15AnchoredAtom2628 chi ∧
      ¬Fin15AnchoredAtom2632 chi ∧
      ¬Fin15AnchoredAtom2678 chi ∧
      ¬Fin15AnchoredAtom2734 chi ∧
      ¬Fin15AnchoredAtom3584 chi ∧
      ¬Fin15AnchoredAtom3585 chi ∧
      ¬Fin15AnchoredAtom3588 chi ∧
      ¬Fin15AnchoredAtom3603 chi ∧
      ¬Fin15AnchoredAtom3606 chi ∧
      ¬Fin15AnchoredAtom3610 chi ∧
      ¬Fin15AnchoredAtom3631 chi ∧
      ¬Fin15AnchoredAtom3634 chi ∧
      ¬Fin15AnchoredAtom3638 chi ∧
      ¬Fin15AnchoredAtom3684 chi ∧
      ¬Fin15AnchoredAtom3835 chi ∧
      ¬Fin15AnchoredAtom3838 chi ∧
      ¬Fin15AnchoredAtom3842 chi ∧
      ¬Fin15AnchoredAtom3888 chi ∧
      ¬Fin15AnchoredAtom3944 chi ∧
      ¬Fin15AnchoredAtom4165 chi ∧
      ¬Fin15AnchoredAtom4168 chi ∧
      ¬Fin15AnchoredAtom4172 chi ∧
      ¬Fin15AnchoredAtom4218 chi ∧
      ¬Fin15AnchoredAtom4274 chi ∧
      ¬Fin15AnchoredAtom4610 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 5, 6, 9, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09837
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2117 Fin15AnchoredAtom2120 Fin15AnchoredAtom2121
    Fin15AnchoredAtom2124 Fin15AnchoredAtom2128 Fin15AnchoredAtom2129 Fin15AnchoredAtom2132
    Fin15AnchoredAtom2147 Fin15AnchoredAtom2150 Fin15AnchoredAtom2154 Fin15AnchoredAtom2209
    Fin15AnchoredAtom2210 Fin15AnchoredAtom2213 Fin15AnchoredAtom2228 Fin15AnchoredAtom2231
    Fin15AnchoredAtom2235 Fin15AnchoredAtom2256 Fin15AnchoredAtom2259 Fin15AnchoredAtom2263
    Fin15AnchoredAtom2309 Fin15AnchoredAtom2374 Fin15AnchoredAtom2375 Fin15AnchoredAtom2378
    Fin15AnchoredAtom2393 Fin15AnchoredAtom2396 Fin15AnchoredAtom2400 Fin15AnchoredAtom2421
    Fin15AnchoredAtom2424 Fin15AnchoredAtom2428 Fin15AnchoredAtom2474 Fin15AnchoredAtom2625
    Fin15AnchoredAtom2628 Fin15AnchoredAtom2632 Fin15AnchoredAtom2678 Fin15AnchoredAtom2734
    Fin15AnchoredAtom3584 Fin15AnchoredAtom3585 Fin15AnchoredAtom3588 Fin15AnchoredAtom3603
    Fin15AnchoredAtom3606 Fin15AnchoredAtom3610 Fin15AnchoredAtom3631 Fin15AnchoredAtom3634
    Fin15AnchoredAtom3638 Fin15AnchoredAtom3684 Fin15AnchoredAtom3835 Fin15AnchoredAtom3838
    Fin15AnchoredAtom3842 Fin15AnchoredAtom3888 Fin15AnchoredAtom3944 Fin15AnchoredAtom4165
    Fin15AnchoredAtom4168 Fin15AnchoredAtom4172 Fin15AnchoredAtom4218 Fin15AnchoredAtom4274
    Fin15AnchoredAtom4610 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31207 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom2128 chi ∧
      ¬Fin15AnchoredAtom2129 chi ∧
      ¬Fin15AnchoredAtom2133 chi ∧
      ¬Fin15AnchoredAtom2147 chi ∧
      ¬Fin15AnchoredAtom2151 chi ∧
      ¬Fin15AnchoredAtom2155 chi ∧
      ¬Fin15AnchoredAtom2209 chi ∧
      ¬Fin15AnchoredAtom2210 chi ∧
      ¬Fin15AnchoredAtom2214 chi ∧
      ¬Fin15AnchoredAtom2228 chi ∧
      ¬Fin15AnchoredAtom2232 chi ∧
      ¬Fin15AnchoredAtom2236 chi ∧
      ¬Fin15AnchoredAtom2256 chi ∧
      ¬Fin15AnchoredAtom2260 chi ∧
      ¬Fin15AnchoredAtom2264 chi ∧
      ¬Fin15AnchoredAtom2310 chi ∧
      ¬Fin15AnchoredAtom2374 chi ∧
      ¬Fin15AnchoredAtom2375 chi ∧
      ¬Fin15AnchoredAtom2379 chi ∧
      ¬Fin15AnchoredAtom2393 chi ∧
      ¬Fin15AnchoredAtom2397 chi ∧
      ¬Fin15AnchoredAtom2401 chi ∧
      ¬Fin15AnchoredAtom2421 chi ∧
      ¬Fin15AnchoredAtom2425 chi ∧
      ¬Fin15AnchoredAtom2429 chi ∧
      ¬Fin15AnchoredAtom2475 chi ∧
      ¬Fin15AnchoredAtom2625 chi ∧
      ¬Fin15AnchoredAtom2629 chi ∧
      ¬Fin15AnchoredAtom2633 chi ∧
      ¬Fin15AnchoredAtom2679 chi ∧
      ¬Fin15AnchoredAtom2735 chi ∧
      ¬Fin15AnchoredAtom3584 chi ∧
      ¬Fin15AnchoredAtom3585 chi ∧
      ¬Fin15AnchoredAtom3589 chi ∧
      ¬Fin15AnchoredAtom3603 chi ∧
      ¬Fin15AnchoredAtom3607 chi ∧
      ¬Fin15AnchoredAtom3611 chi ∧
      ¬Fin15AnchoredAtom3631 chi ∧
      ¬Fin15AnchoredAtom3635 chi ∧
      ¬Fin15AnchoredAtom3639 chi ∧
      ¬Fin15AnchoredAtom3685 chi ∧
      ¬Fin15AnchoredAtom3835 chi ∧
      ¬Fin15AnchoredAtom3839 chi ∧
      ¬Fin15AnchoredAtom3843 chi ∧
      ¬Fin15AnchoredAtom3889 chi ∧
      ¬Fin15AnchoredAtom3945 chi ∧
      ¬Fin15AnchoredAtom4165 chi ∧
      ¬Fin15AnchoredAtom4169 chi ∧
      ¬Fin15AnchoredAtom4173 chi ∧
      ¬Fin15AnchoredAtom4219 chi ∧
      ¬Fin15AnchoredAtom4275 chi ∧
      ¬Fin15AnchoredAtom4611 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 5, 6, 9, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask18029
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2117 Fin15AnchoredAtom2120 Fin15AnchoredAtom2121
    Fin15AnchoredAtom2125 Fin15AnchoredAtom2128 Fin15AnchoredAtom2129 Fin15AnchoredAtom2133
    Fin15AnchoredAtom2147 Fin15AnchoredAtom2151 Fin15AnchoredAtom2155 Fin15AnchoredAtom2209
    Fin15AnchoredAtom2210 Fin15AnchoredAtom2214 Fin15AnchoredAtom2228 Fin15AnchoredAtom2232
    Fin15AnchoredAtom2236 Fin15AnchoredAtom2256 Fin15AnchoredAtom2260 Fin15AnchoredAtom2264
    Fin15AnchoredAtom2310 Fin15AnchoredAtom2374 Fin15AnchoredAtom2375 Fin15AnchoredAtom2379
    Fin15AnchoredAtom2393 Fin15AnchoredAtom2397 Fin15AnchoredAtom2401 Fin15AnchoredAtom2421
    Fin15AnchoredAtom2425 Fin15AnchoredAtom2429 Fin15AnchoredAtom2475 Fin15AnchoredAtom2625
    Fin15AnchoredAtom2629 Fin15AnchoredAtom2633 Fin15AnchoredAtom2679 Fin15AnchoredAtom2735
    Fin15AnchoredAtom3584 Fin15AnchoredAtom3585 Fin15AnchoredAtom3589 Fin15AnchoredAtom3603
    Fin15AnchoredAtom3607 Fin15AnchoredAtom3611 Fin15AnchoredAtom3631 Fin15AnchoredAtom3635
    Fin15AnchoredAtom3639 Fin15AnchoredAtom3685 Fin15AnchoredAtom3835 Fin15AnchoredAtom3839
    Fin15AnchoredAtom3843 Fin15AnchoredAtom3889 Fin15AnchoredAtom3945 Fin15AnchoredAtom4165
    Fin15AnchoredAtom4169 Fin15AnchoredAtom4173 Fin15AnchoredAtom4219 Fin15AnchoredAtom4275
    Fin15AnchoredAtom4611 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31208 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom2128 chi ∧
      ¬Fin15AnchoredAtom2131 chi ∧
      ¬Fin15AnchoredAtom2132 chi ∧
      ¬Fin15AnchoredAtom2149 chi ∧
      ¬Fin15AnchoredAtom2150 chi ∧
      ¬Fin15AnchoredAtom2159 chi ∧
      ¬Fin15AnchoredAtom2209 chi ∧
      ¬Fin15AnchoredAtom2212 chi ∧
      ¬Fin15AnchoredAtom2213 chi ∧
      ¬Fin15AnchoredAtom2230 chi ∧
      ¬Fin15AnchoredAtom2231 chi ∧
      ¬Fin15AnchoredAtom2240 chi ∧
      ¬Fin15AnchoredAtom2258 chi ∧
      ¬Fin15AnchoredAtom2259 chi ∧
      ¬Fin15AnchoredAtom2268 chi ∧
      ¬Fin15AnchoredAtom2314 chi ∧
      ¬Fin15AnchoredAtom2374 chi ∧
      ¬Fin15AnchoredAtom2377 chi ∧
      ¬Fin15AnchoredAtom2378 chi ∧
      ¬Fin15AnchoredAtom2395 chi ∧
      ¬Fin15AnchoredAtom2396 chi ∧
      ¬Fin15AnchoredAtom2405 chi ∧
      ¬Fin15AnchoredAtom2423 chi ∧
      ¬Fin15AnchoredAtom2424 chi ∧
      ¬Fin15AnchoredAtom2433 chi ∧
      ¬Fin15AnchoredAtom2479 chi ∧
      ¬Fin15AnchoredAtom2627 chi ∧
      ¬Fin15AnchoredAtom2628 chi ∧
      ¬Fin15AnchoredAtom2637 chi ∧
      ¬Fin15AnchoredAtom2683 chi ∧
      ¬Fin15AnchoredAtom2739 chi ∧
      ¬Fin15AnchoredAtom3584 chi ∧
      ¬Fin15AnchoredAtom3587 chi ∧
      ¬Fin15AnchoredAtom3588 chi ∧
      ¬Fin15AnchoredAtom3605 chi ∧
      ¬Fin15AnchoredAtom3606 chi ∧
      ¬Fin15AnchoredAtom3615 chi ∧
      ¬Fin15AnchoredAtom3633 chi ∧
      ¬Fin15AnchoredAtom3634 chi ∧
      ¬Fin15AnchoredAtom3643 chi ∧
      ¬Fin15AnchoredAtom3689 chi ∧
      ¬Fin15AnchoredAtom3837 chi ∧
      ¬Fin15AnchoredAtom3838 chi ∧
      ¬Fin15AnchoredAtom3847 chi ∧
      ¬Fin15AnchoredAtom3893 chi ∧
      ¬Fin15AnchoredAtom3949 chi ∧
      ¬Fin15AnchoredAtom4167 chi ∧
      ¬Fin15AnchoredAtom4168 chi ∧
      ¬Fin15AnchoredAtom4177 chi ∧
      ¬Fin15AnchoredAtom4223 chi ∧
      ¬Fin15AnchoredAtom4279 chi ∧
      ¬Fin15AnchoredAtom4615 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 5, 6, 9, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask12909
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2117 Fin15AnchoredAtom2120 Fin15AnchoredAtom2123
    Fin15AnchoredAtom2124 Fin15AnchoredAtom2128 Fin15AnchoredAtom2131 Fin15AnchoredAtom2132
    Fin15AnchoredAtom2149 Fin15AnchoredAtom2150 Fin15AnchoredAtom2159 Fin15AnchoredAtom2209
    Fin15AnchoredAtom2212 Fin15AnchoredAtom2213 Fin15AnchoredAtom2230 Fin15AnchoredAtom2231
    Fin15AnchoredAtom2240 Fin15AnchoredAtom2258 Fin15AnchoredAtom2259 Fin15AnchoredAtom2268
    Fin15AnchoredAtom2314 Fin15AnchoredAtom2374 Fin15AnchoredAtom2377 Fin15AnchoredAtom2378
    Fin15AnchoredAtom2395 Fin15AnchoredAtom2396 Fin15AnchoredAtom2405 Fin15AnchoredAtom2423
    Fin15AnchoredAtom2424 Fin15AnchoredAtom2433 Fin15AnchoredAtom2479 Fin15AnchoredAtom2627
    Fin15AnchoredAtom2628 Fin15AnchoredAtom2637 Fin15AnchoredAtom2683 Fin15AnchoredAtom2739
    Fin15AnchoredAtom3584 Fin15AnchoredAtom3587 Fin15AnchoredAtom3588 Fin15AnchoredAtom3605
    Fin15AnchoredAtom3606 Fin15AnchoredAtom3615 Fin15AnchoredAtom3633 Fin15AnchoredAtom3634
    Fin15AnchoredAtom3643 Fin15AnchoredAtom3689 Fin15AnchoredAtom3837 Fin15AnchoredAtom3838
    Fin15AnchoredAtom3847 Fin15AnchoredAtom3893 Fin15AnchoredAtom3949 Fin15AnchoredAtom4167
    Fin15AnchoredAtom4168 Fin15AnchoredAtom4177 Fin15AnchoredAtom4223 Fin15AnchoredAtom4279
    Fin15AnchoredAtom4615 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31209 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom2128 chi ∧
      ¬Fin15AnchoredAtom2131 chi ∧
      ¬Fin15AnchoredAtom2133 chi ∧
      ¬Fin15AnchoredAtom2149 chi ∧
      ¬Fin15AnchoredAtom2151 chi ∧
      ¬Fin15AnchoredAtom2160 chi ∧
      ¬Fin15AnchoredAtom2209 chi ∧
      ¬Fin15AnchoredAtom2212 chi ∧
      ¬Fin15AnchoredAtom2214 chi ∧
      ¬Fin15AnchoredAtom2230 chi ∧
      ¬Fin15AnchoredAtom2232 chi ∧
      ¬Fin15AnchoredAtom2241 chi ∧
      ¬Fin15AnchoredAtom2258 chi ∧
      ¬Fin15AnchoredAtom2260 chi ∧
      ¬Fin15AnchoredAtom2269 chi ∧
      ¬Fin15AnchoredAtom2315 chi ∧
      ¬Fin15AnchoredAtom2374 chi ∧
      ¬Fin15AnchoredAtom2377 chi ∧
      ¬Fin15AnchoredAtom2379 chi ∧
      ¬Fin15AnchoredAtom2395 chi ∧
      ¬Fin15AnchoredAtom2397 chi ∧
      ¬Fin15AnchoredAtom2406 chi ∧
      ¬Fin15AnchoredAtom2423 chi ∧
      ¬Fin15AnchoredAtom2425 chi ∧
      ¬Fin15AnchoredAtom2434 chi ∧
      ¬Fin15AnchoredAtom2480 chi ∧
      ¬Fin15AnchoredAtom2627 chi ∧
      ¬Fin15AnchoredAtom2629 chi ∧
      ¬Fin15AnchoredAtom2638 chi ∧
      ¬Fin15AnchoredAtom2684 chi ∧
      ¬Fin15AnchoredAtom2740 chi ∧
      ¬Fin15AnchoredAtom3584 chi ∧
      ¬Fin15AnchoredAtom3587 chi ∧
      ¬Fin15AnchoredAtom3589 chi ∧
      ¬Fin15AnchoredAtom3605 chi ∧
      ¬Fin15AnchoredAtom3607 chi ∧
      ¬Fin15AnchoredAtom3616 chi ∧
      ¬Fin15AnchoredAtom3633 chi ∧
      ¬Fin15AnchoredAtom3635 chi ∧
      ¬Fin15AnchoredAtom3644 chi ∧
      ¬Fin15AnchoredAtom3690 chi ∧
      ¬Fin15AnchoredAtom3837 chi ∧
      ¬Fin15AnchoredAtom3839 chi ∧
      ¬Fin15AnchoredAtom3848 chi ∧
      ¬Fin15AnchoredAtom3894 chi ∧
      ¬Fin15AnchoredAtom3950 chi ∧
      ¬Fin15AnchoredAtom4167 chi ∧
      ¬Fin15AnchoredAtom4169 chi ∧
      ¬Fin15AnchoredAtom4178 chi ∧
      ¬Fin15AnchoredAtom4224 chi ∧
      ¬Fin15AnchoredAtom4280 chi ∧
      ¬Fin15AnchoredAtom4616 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 5, 6, 9, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21101
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2117 Fin15AnchoredAtom2120 Fin15AnchoredAtom2123
    Fin15AnchoredAtom2125 Fin15AnchoredAtom2128 Fin15AnchoredAtom2131 Fin15AnchoredAtom2133
    Fin15AnchoredAtom2149 Fin15AnchoredAtom2151 Fin15AnchoredAtom2160 Fin15AnchoredAtom2209
    Fin15AnchoredAtom2212 Fin15AnchoredAtom2214 Fin15AnchoredAtom2230 Fin15AnchoredAtom2232
    Fin15AnchoredAtom2241 Fin15AnchoredAtom2258 Fin15AnchoredAtom2260 Fin15AnchoredAtom2269
    Fin15AnchoredAtom2315 Fin15AnchoredAtom2374 Fin15AnchoredAtom2377 Fin15AnchoredAtom2379
    Fin15AnchoredAtom2395 Fin15AnchoredAtom2397 Fin15AnchoredAtom2406 Fin15AnchoredAtom2423
    Fin15AnchoredAtom2425 Fin15AnchoredAtom2434 Fin15AnchoredAtom2480 Fin15AnchoredAtom2627
    Fin15AnchoredAtom2629 Fin15AnchoredAtom2638 Fin15AnchoredAtom2684 Fin15AnchoredAtom2740
    Fin15AnchoredAtom3584 Fin15AnchoredAtom3587 Fin15AnchoredAtom3589 Fin15AnchoredAtom3605
    Fin15AnchoredAtom3607 Fin15AnchoredAtom3616 Fin15AnchoredAtom3633 Fin15AnchoredAtom3635
    Fin15AnchoredAtom3644 Fin15AnchoredAtom3690 Fin15AnchoredAtom3837 Fin15AnchoredAtom3839
    Fin15AnchoredAtom3848 Fin15AnchoredAtom3894 Fin15AnchoredAtom3950 Fin15AnchoredAtom4167
    Fin15AnchoredAtom4169 Fin15AnchoredAtom4178 Fin15AnchoredAtom4224 Fin15AnchoredAtom4280
    Fin15AnchoredAtom4616 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31210 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom2128 chi ∧
      ¬Fin15AnchoredAtom2132 chi ∧
      ¬Fin15AnchoredAtom2133 chi ∧
      ¬Fin15AnchoredAtom2150 chi ∧
      ¬Fin15AnchoredAtom2151 chi ∧
      ¬Fin15AnchoredAtom2161 chi ∧
      ¬Fin15AnchoredAtom2209 chi ∧
      ¬Fin15AnchoredAtom2213 chi ∧
      ¬Fin15AnchoredAtom2214 chi ∧
      ¬Fin15AnchoredAtom2231 chi ∧
      ¬Fin15AnchoredAtom2232 chi ∧
      ¬Fin15AnchoredAtom2242 chi ∧
      ¬Fin15AnchoredAtom2259 chi ∧
      ¬Fin15AnchoredAtom2260 chi ∧
      ¬Fin15AnchoredAtom2270 chi ∧
      ¬Fin15AnchoredAtom2316 chi ∧
      ¬Fin15AnchoredAtom2374 chi ∧
      ¬Fin15AnchoredAtom2378 chi ∧
      ¬Fin15AnchoredAtom2379 chi ∧
      ¬Fin15AnchoredAtom2396 chi ∧
      ¬Fin15AnchoredAtom2397 chi ∧
      ¬Fin15AnchoredAtom2407 chi ∧
      ¬Fin15AnchoredAtom2424 chi ∧
      ¬Fin15AnchoredAtom2425 chi ∧
      ¬Fin15AnchoredAtom2435 chi ∧
      ¬Fin15AnchoredAtom2481 chi ∧
      ¬Fin15AnchoredAtom2628 chi ∧
      ¬Fin15AnchoredAtom2629 chi ∧
      ¬Fin15AnchoredAtom2639 chi ∧
      ¬Fin15AnchoredAtom2685 chi ∧
      ¬Fin15AnchoredAtom2741 chi ∧
      ¬Fin15AnchoredAtom3584 chi ∧
      ¬Fin15AnchoredAtom3588 chi ∧
      ¬Fin15AnchoredAtom3589 chi ∧
      ¬Fin15AnchoredAtom3606 chi ∧
      ¬Fin15AnchoredAtom3607 chi ∧
      ¬Fin15AnchoredAtom3617 chi ∧
      ¬Fin15AnchoredAtom3634 chi ∧
      ¬Fin15AnchoredAtom3635 chi ∧
      ¬Fin15AnchoredAtom3645 chi ∧
      ¬Fin15AnchoredAtom3691 chi ∧
      ¬Fin15AnchoredAtom3838 chi ∧
      ¬Fin15AnchoredAtom3839 chi ∧
      ¬Fin15AnchoredAtom3849 chi ∧
      ¬Fin15AnchoredAtom3895 chi ∧
      ¬Fin15AnchoredAtom3951 chi ∧
      ¬Fin15AnchoredAtom4168 chi ∧
      ¬Fin15AnchoredAtom4169 chi ∧
      ¬Fin15AnchoredAtom4179 chi ∧
      ¬Fin15AnchoredAtom4225 chi ∧
      ¬Fin15AnchoredAtom4281 chi ∧
      ¬Fin15AnchoredAtom4617 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 5, 6, 9, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25197
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2117 Fin15AnchoredAtom2120 Fin15AnchoredAtom2124
    Fin15AnchoredAtom2125 Fin15AnchoredAtom2128 Fin15AnchoredAtom2132 Fin15AnchoredAtom2133
    Fin15AnchoredAtom2150 Fin15AnchoredAtom2151 Fin15AnchoredAtom2161 Fin15AnchoredAtom2209
    Fin15AnchoredAtom2213 Fin15AnchoredAtom2214 Fin15AnchoredAtom2231 Fin15AnchoredAtom2232
    Fin15AnchoredAtom2242 Fin15AnchoredAtom2259 Fin15AnchoredAtom2260 Fin15AnchoredAtom2270
    Fin15AnchoredAtom2316 Fin15AnchoredAtom2374 Fin15AnchoredAtom2378 Fin15AnchoredAtom2379
    Fin15AnchoredAtom2396 Fin15AnchoredAtom2397 Fin15AnchoredAtom2407 Fin15AnchoredAtom2424
    Fin15AnchoredAtom2425 Fin15AnchoredAtom2435 Fin15AnchoredAtom2481 Fin15AnchoredAtom2628
    Fin15AnchoredAtom2629 Fin15AnchoredAtom2639 Fin15AnchoredAtom2685 Fin15AnchoredAtom2741
    Fin15AnchoredAtom3584 Fin15AnchoredAtom3588 Fin15AnchoredAtom3589 Fin15AnchoredAtom3606
    Fin15AnchoredAtom3607 Fin15AnchoredAtom3617 Fin15AnchoredAtom3634 Fin15AnchoredAtom3635
    Fin15AnchoredAtom3645 Fin15AnchoredAtom3691 Fin15AnchoredAtom3838 Fin15AnchoredAtom3839
    Fin15AnchoredAtom3849 Fin15AnchoredAtom3895 Fin15AnchoredAtom3951 Fin15AnchoredAtom4168
    Fin15AnchoredAtom4169 Fin15AnchoredAtom4179 Fin15AnchoredAtom4225 Fin15AnchoredAtom4281
    Fin15AnchoredAtom4617 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31211 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom2129 chi ∧
      ¬Fin15AnchoredAtom2131 chi ∧
      ¬Fin15AnchoredAtom2132 chi ∧
      ¬Fin15AnchoredAtom2153 chi ∧
      ¬Fin15AnchoredAtom2154 chi ∧
      ¬Fin15AnchoredAtom2159 chi ∧
      ¬Fin15AnchoredAtom2210 chi ∧
      ¬Fin15AnchoredAtom2212 chi ∧
      ¬Fin15AnchoredAtom2213 chi ∧
      ¬Fin15AnchoredAtom2234 chi ∧
      ¬Fin15AnchoredAtom2235 chi ∧
      ¬Fin15AnchoredAtom2240 chi ∧
      ¬Fin15AnchoredAtom2262 chi ∧
      ¬Fin15AnchoredAtom2263 chi ∧
      ¬Fin15AnchoredAtom2268 chi ∧
      ¬Fin15AnchoredAtom2320 chi ∧
      ¬Fin15AnchoredAtom2375 chi ∧
      ¬Fin15AnchoredAtom2377 chi ∧
      ¬Fin15AnchoredAtom2378 chi ∧
      ¬Fin15AnchoredAtom2399 chi ∧
      ¬Fin15AnchoredAtom2400 chi ∧
      ¬Fin15AnchoredAtom2405 chi ∧
      ¬Fin15AnchoredAtom2427 chi ∧
      ¬Fin15AnchoredAtom2428 chi ∧
      ¬Fin15AnchoredAtom2433 chi ∧
      ¬Fin15AnchoredAtom2485 chi ∧
      ¬Fin15AnchoredAtom2631 chi ∧
      ¬Fin15AnchoredAtom2632 chi ∧
      ¬Fin15AnchoredAtom2637 chi ∧
      ¬Fin15AnchoredAtom2689 chi ∧
      ¬Fin15AnchoredAtom2745 chi ∧
      ¬Fin15AnchoredAtom3585 chi ∧
      ¬Fin15AnchoredAtom3587 chi ∧
      ¬Fin15AnchoredAtom3588 chi ∧
      ¬Fin15AnchoredAtom3609 chi ∧
      ¬Fin15AnchoredAtom3610 chi ∧
      ¬Fin15AnchoredAtom3615 chi ∧
      ¬Fin15AnchoredAtom3637 chi ∧
      ¬Fin15AnchoredAtom3638 chi ∧
      ¬Fin15AnchoredAtom3643 chi ∧
      ¬Fin15AnchoredAtom3695 chi ∧
      ¬Fin15AnchoredAtom3841 chi ∧
      ¬Fin15AnchoredAtom3842 chi ∧
      ¬Fin15AnchoredAtom3847 chi ∧
      ¬Fin15AnchoredAtom3899 chi ∧
      ¬Fin15AnchoredAtom3955 chi ∧
      ¬Fin15AnchoredAtom4171 chi ∧
      ¬Fin15AnchoredAtom4172 chi ∧
      ¬Fin15AnchoredAtom4177 chi ∧
      ¬Fin15AnchoredAtom4229 chi ∧
      ¬Fin15AnchoredAtom4285 chi ∧
      ¬Fin15AnchoredAtom4621 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 5, 6, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13421
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2117 Fin15AnchoredAtom2121 Fin15AnchoredAtom2123
    Fin15AnchoredAtom2124 Fin15AnchoredAtom2129 Fin15AnchoredAtom2131 Fin15AnchoredAtom2132
    Fin15AnchoredAtom2153 Fin15AnchoredAtom2154 Fin15AnchoredAtom2159 Fin15AnchoredAtom2210
    Fin15AnchoredAtom2212 Fin15AnchoredAtom2213 Fin15AnchoredAtom2234 Fin15AnchoredAtom2235
    Fin15AnchoredAtom2240 Fin15AnchoredAtom2262 Fin15AnchoredAtom2263 Fin15AnchoredAtom2268
    Fin15AnchoredAtom2320 Fin15AnchoredAtom2375 Fin15AnchoredAtom2377 Fin15AnchoredAtom2378
    Fin15AnchoredAtom2399 Fin15AnchoredAtom2400 Fin15AnchoredAtom2405 Fin15AnchoredAtom2427
    Fin15AnchoredAtom2428 Fin15AnchoredAtom2433 Fin15AnchoredAtom2485 Fin15AnchoredAtom2631
    Fin15AnchoredAtom2632 Fin15AnchoredAtom2637 Fin15AnchoredAtom2689 Fin15AnchoredAtom2745
    Fin15AnchoredAtom3585 Fin15AnchoredAtom3587 Fin15AnchoredAtom3588 Fin15AnchoredAtom3609
    Fin15AnchoredAtom3610 Fin15AnchoredAtom3615 Fin15AnchoredAtom3637 Fin15AnchoredAtom3638
    Fin15AnchoredAtom3643 Fin15AnchoredAtom3695 Fin15AnchoredAtom3841 Fin15AnchoredAtom3842
    Fin15AnchoredAtom3847 Fin15AnchoredAtom3899 Fin15AnchoredAtom3955 Fin15AnchoredAtom4171
    Fin15AnchoredAtom4172 Fin15AnchoredAtom4177 Fin15AnchoredAtom4229 Fin15AnchoredAtom4285
    Fin15AnchoredAtom4621 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31212 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom2129 chi ∧
      ¬Fin15AnchoredAtom2131 chi ∧
      ¬Fin15AnchoredAtom2133 chi ∧
      ¬Fin15AnchoredAtom2153 chi ∧
      ¬Fin15AnchoredAtom2155 chi ∧
      ¬Fin15AnchoredAtom2160 chi ∧
      ¬Fin15AnchoredAtom2210 chi ∧
      ¬Fin15AnchoredAtom2212 chi ∧
      ¬Fin15AnchoredAtom2214 chi ∧
      ¬Fin15AnchoredAtom2234 chi ∧
      ¬Fin15AnchoredAtom2236 chi ∧
      ¬Fin15AnchoredAtom2241 chi ∧
      ¬Fin15AnchoredAtom2262 chi ∧
      ¬Fin15AnchoredAtom2264 chi ∧
      ¬Fin15AnchoredAtom2269 chi ∧
      ¬Fin15AnchoredAtom2321 chi ∧
      ¬Fin15AnchoredAtom2375 chi ∧
      ¬Fin15AnchoredAtom2377 chi ∧
      ¬Fin15AnchoredAtom2379 chi ∧
      ¬Fin15AnchoredAtom2399 chi ∧
      ¬Fin15AnchoredAtom2401 chi ∧
      ¬Fin15AnchoredAtom2406 chi ∧
      ¬Fin15AnchoredAtom2427 chi ∧
      ¬Fin15AnchoredAtom2429 chi ∧
      ¬Fin15AnchoredAtom2434 chi ∧
      ¬Fin15AnchoredAtom2486 chi ∧
      ¬Fin15AnchoredAtom2631 chi ∧
      ¬Fin15AnchoredAtom2633 chi ∧
      ¬Fin15AnchoredAtom2638 chi ∧
      ¬Fin15AnchoredAtom2690 chi ∧
      ¬Fin15AnchoredAtom2746 chi ∧
      ¬Fin15AnchoredAtom3585 chi ∧
      ¬Fin15AnchoredAtom3587 chi ∧
      ¬Fin15AnchoredAtom3589 chi ∧
      ¬Fin15AnchoredAtom3609 chi ∧
      ¬Fin15AnchoredAtom3611 chi ∧
      ¬Fin15AnchoredAtom3616 chi ∧
      ¬Fin15AnchoredAtom3637 chi ∧
      ¬Fin15AnchoredAtom3639 chi ∧
      ¬Fin15AnchoredAtom3644 chi ∧
      ¬Fin15AnchoredAtom3696 chi ∧
      ¬Fin15AnchoredAtom3841 chi ∧
      ¬Fin15AnchoredAtom3843 chi ∧
      ¬Fin15AnchoredAtom3848 chi ∧
      ¬Fin15AnchoredAtom3900 chi ∧
      ¬Fin15AnchoredAtom3956 chi ∧
      ¬Fin15AnchoredAtom4171 chi ∧
      ¬Fin15AnchoredAtom4173 chi ∧
      ¬Fin15AnchoredAtom4178 chi ∧
      ¬Fin15AnchoredAtom4230 chi ∧
      ¬Fin15AnchoredAtom4286 chi ∧
      ¬Fin15AnchoredAtom4622 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 5, 6, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21613
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2117 Fin15AnchoredAtom2121 Fin15AnchoredAtom2123
    Fin15AnchoredAtom2125 Fin15AnchoredAtom2129 Fin15AnchoredAtom2131 Fin15AnchoredAtom2133
    Fin15AnchoredAtom2153 Fin15AnchoredAtom2155 Fin15AnchoredAtom2160 Fin15AnchoredAtom2210
    Fin15AnchoredAtom2212 Fin15AnchoredAtom2214 Fin15AnchoredAtom2234 Fin15AnchoredAtom2236
    Fin15AnchoredAtom2241 Fin15AnchoredAtom2262 Fin15AnchoredAtom2264 Fin15AnchoredAtom2269
    Fin15AnchoredAtom2321 Fin15AnchoredAtom2375 Fin15AnchoredAtom2377 Fin15AnchoredAtom2379
    Fin15AnchoredAtom2399 Fin15AnchoredAtom2401 Fin15AnchoredAtom2406 Fin15AnchoredAtom2427
    Fin15AnchoredAtom2429 Fin15AnchoredAtom2434 Fin15AnchoredAtom2486 Fin15AnchoredAtom2631
    Fin15AnchoredAtom2633 Fin15AnchoredAtom2638 Fin15AnchoredAtom2690 Fin15AnchoredAtom2746
    Fin15AnchoredAtom3585 Fin15AnchoredAtom3587 Fin15AnchoredAtom3589 Fin15AnchoredAtom3609
    Fin15AnchoredAtom3611 Fin15AnchoredAtom3616 Fin15AnchoredAtom3637 Fin15AnchoredAtom3639
    Fin15AnchoredAtom3644 Fin15AnchoredAtom3696 Fin15AnchoredAtom3841 Fin15AnchoredAtom3843
    Fin15AnchoredAtom3848 Fin15AnchoredAtom3900 Fin15AnchoredAtom3956 Fin15AnchoredAtom4171
    Fin15AnchoredAtom4173 Fin15AnchoredAtom4178 Fin15AnchoredAtom4230 Fin15AnchoredAtom4286
    Fin15AnchoredAtom4622 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31213 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom2129 chi ∧
      ¬Fin15AnchoredAtom2132 chi ∧
      ¬Fin15AnchoredAtom2133 chi ∧
      ¬Fin15AnchoredAtom2154 chi ∧
      ¬Fin15AnchoredAtom2155 chi ∧
      ¬Fin15AnchoredAtom2161 chi ∧
      ¬Fin15AnchoredAtom2210 chi ∧
      ¬Fin15AnchoredAtom2213 chi ∧
      ¬Fin15AnchoredAtom2214 chi ∧
      ¬Fin15AnchoredAtom2235 chi ∧
      ¬Fin15AnchoredAtom2236 chi ∧
      ¬Fin15AnchoredAtom2242 chi ∧
      ¬Fin15AnchoredAtom2263 chi ∧
      ¬Fin15AnchoredAtom2264 chi ∧
      ¬Fin15AnchoredAtom2270 chi ∧
      ¬Fin15AnchoredAtom2322 chi ∧
      ¬Fin15AnchoredAtom2375 chi ∧
      ¬Fin15AnchoredAtom2378 chi ∧
      ¬Fin15AnchoredAtom2379 chi ∧
      ¬Fin15AnchoredAtom2400 chi ∧
      ¬Fin15AnchoredAtom2401 chi ∧
      ¬Fin15AnchoredAtom2407 chi ∧
      ¬Fin15AnchoredAtom2428 chi ∧
      ¬Fin15AnchoredAtom2429 chi ∧
      ¬Fin15AnchoredAtom2435 chi ∧
      ¬Fin15AnchoredAtom2487 chi ∧
      ¬Fin15AnchoredAtom2632 chi ∧
      ¬Fin15AnchoredAtom2633 chi ∧
      ¬Fin15AnchoredAtom2639 chi ∧
      ¬Fin15AnchoredAtom2691 chi ∧
      ¬Fin15AnchoredAtom2747 chi ∧
      ¬Fin15AnchoredAtom3585 chi ∧
      ¬Fin15AnchoredAtom3588 chi ∧
      ¬Fin15AnchoredAtom3589 chi ∧
      ¬Fin15AnchoredAtom3610 chi ∧
      ¬Fin15AnchoredAtom3611 chi ∧
      ¬Fin15AnchoredAtom3617 chi ∧
      ¬Fin15AnchoredAtom3638 chi ∧
      ¬Fin15AnchoredAtom3639 chi ∧
      ¬Fin15AnchoredAtom3645 chi ∧
      ¬Fin15AnchoredAtom3697 chi ∧
      ¬Fin15AnchoredAtom3842 chi ∧
      ¬Fin15AnchoredAtom3843 chi ∧
      ¬Fin15AnchoredAtom3849 chi ∧
      ¬Fin15AnchoredAtom3901 chi ∧
      ¬Fin15AnchoredAtom3957 chi ∧
      ¬Fin15AnchoredAtom4172 chi ∧
      ¬Fin15AnchoredAtom4173 chi ∧
      ¬Fin15AnchoredAtom4179 chi ∧
      ¬Fin15AnchoredAtom4231 chi ∧
      ¬Fin15AnchoredAtom4287 chi ∧
      ¬Fin15AnchoredAtom4623 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 5, 6, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25709
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2117 Fin15AnchoredAtom2121 Fin15AnchoredAtom2124
    Fin15AnchoredAtom2125 Fin15AnchoredAtom2129 Fin15AnchoredAtom2132 Fin15AnchoredAtom2133
    Fin15AnchoredAtom2154 Fin15AnchoredAtom2155 Fin15AnchoredAtom2161 Fin15AnchoredAtom2210
    Fin15AnchoredAtom2213 Fin15AnchoredAtom2214 Fin15AnchoredAtom2235 Fin15AnchoredAtom2236
    Fin15AnchoredAtom2242 Fin15AnchoredAtom2263 Fin15AnchoredAtom2264 Fin15AnchoredAtom2270
    Fin15AnchoredAtom2322 Fin15AnchoredAtom2375 Fin15AnchoredAtom2378 Fin15AnchoredAtom2379
    Fin15AnchoredAtom2400 Fin15AnchoredAtom2401 Fin15AnchoredAtom2407 Fin15AnchoredAtom2428
    Fin15AnchoredAtom2429 Fin15AnchoredAtom2435 Fin15AnchoredAtom2487 Fin15AnchoredAtom2632
    Fin15AnchoredAtom2633 Fin15AnchoredAtom2639 Fin15AnchoredAtom2691 Fin15AnchoredAtom2747
    Fin15AnchoredAtom3585 Fin15AnchoredAtom3588 Fin15AnchoredAtom3589 Fin15AnchoredAtom3610
    Fin15AnchoredAtom3611 Fin15AnchoredAtom3617 Fin15AnchoredAtom3638 Fin15AnchoredAtom3639
    Fin15AnchoredAtom3645 Fin15AnchoredAtom3697 Fin15AnchoredAtom3842 Fin15AnchoredAtom3843
    Fin15AnchoredAtom3849 Fin15AnchoredAtom3901 Fin15AnchoredAtom3957 Fin15AnchoredAtom4172
    Fin15AnchoredAtom4173 Fin15AnchoredAtom4179 Fin15AnchoredAtom4231 Fin15AnchoredAtom4287
    Fin15AnchoredAtom4623 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31214 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom2131 chi ∧
      ¬Fin15AnchoredAtom2132 chi ∧
      ¬Fin15AnchoredAtom2133 chi ∧
      ¬Fin15AnchoredAtom2159 chi ∧
      ¬Fin15AnchoredAtom2160 chi ∧
      ¬Fin15AnchoredAtom2161 chi ∧
      ¬Fin15AnchoredAtom2212 chi ∧
      ¬Fin15AnchoredAtom2213 chi ∧
      ¬Fin15AnchoredAtom2214 chi ∧
      ¬Fin15AnchoredAtom2240 chi ∧
      ¬Fin15AnchoredAtom2241 chi ∧
      ¬Fin15AnchoredAtom2242 chi ∧
      ¬Fin15AnchoredAtom2268 chi ∧
      ¬Fin15AnchoredAtom2269 chi ∧
      ¬Fin15AnchoredAtom2270 chi ∧
      ¬Fin15AnchoredAtom2326 chi ∧
      ¬Fin15AnchoredAtom2377 chi ∧
      ¬Fin15AnchoredAtom2378 chi ∧
      ¬Fin15AnchoredAtom2379 chi ∧
      ¬Fin15AnchoredAtom2405 chi ∧
      ¬Fin15AnchoredAtom2406 chi ∧
      ¬Fin15AnchoredAtom2407 chi ∧
      ¬Fin15AnchoredAtom2433 chi ∧
      ¬Fin15AnchoredAtom2434 chi ∧
      ¬Fin15AnchoredAtom2435 chi ∧
      ¬Fin15AnchoredAtom2491 chi ∧
      ¬Fin15AnchoredAtom2637 chi ∧
      ¬Fin15AnchoredAtom2638 chi ∧
      ¬Fin15AnchoredAtom2639 chi ∧
      ¬Fin15AnchoredAtom2695 chi ∧
      ¬Fin15AnchoredAtom2751 chi ∧
      ¬Fin15AnchoredAtom3587 chi ∧
      ¬Fin15AnchoredAtom3588 chi ∧
      ¬Fin15AnchoredAtom3589 chi ∧
      ¬Fin15AnchoredAtom3615 chi ∧
      ¬Fin15AnchoredAtom3616 chi ∧
      ¬Fin15AnchoredAtom3617 chi ∧
      ¬Fin15AnchoredAtom3643 chi ∧
      ¬Fin15AnchoredAtom3644 chi ∧
      ¬Fin15AnchoredAtom3645 chi ∧
      ¬Fin15AnchoredAtom3701 chi ∧
      ¬Fin15AnchoredAtom3847 chi ∧
      ¬Fin15AnchoredAtom3848 chi ∧
      ¬Fin15AnchoredAtom3849 chi ∧
      ¬Fin15AnchoredAtom3905 chi ∧
      ¬Fin15AnchoredAtom3961 chi ∧
      ¬Fin15AnchoredAtom4177 chi ∧
      ¬Fin15AnchoredAtom4178 chi ∧
      ¬Fin15AnchoredAtom4179 chi ∧
      ¬Fin15AnchoredAtom4235 chi ∧
      ¬Fin15AnchoredAtom4291 chi ∧
      ¬Fin15AnchoredAtom4627 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 5, 6, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask28781
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2117 Fin15AnchoredAtom2123 Fin15AnchoredAtom2124
    Fin15AnchoredAtom2125 Fin15AnchoredAtom2131 Fin15AnchoredAtom2132 Fin15AnchoredAtom2133
    Fin15AnchoredAtom2159 Fin15AnchoredAtom2160 Fin15AnchoredAtom2161 Fin15AnchoredAtom2212
    Fin15AnchoredAtom2213 Fin15AnchoredAtom2214 Fin15AnchoredAtom2240 Fin15AnchoredAtom2241
    Fin15AnchoredAtom2242 Fin15AnchoredAtom2268 Fin15AnchoredAtom2269 Fin15AnchoredAtom2270
    Fin15AnchoredAtom2326 Fin15AnchoredAtom2377 Fin15AnchoredAtom2378 Fin15AnchoredAtom2379
    Fin15AnchoredAtom2405 Fin15AnchoredAtom2406 Fin15AnchoredAtom2407 Fin15AnchoredAtom2433
    Fin15AnchoredAtom2434 Fin15AnchoredAtom2435 Fin15AnchoredAtom2491 Fin15AnchoredAtom2637
    Fin15AnchoredAtom2638 Fin15AnchoredAtom2639 Fin15AnchoredAtom2695 Fin15AnchoredAtom2751
    Fin15AnchoredAtom3587 Fin15AnchoredAtom3588 Fin15AnchoredAtom3589 Fin15AnchoredAtom3615
    Fin15AnchoredAtom3616 Fin15AnchoredAtom3617 Fin15AnchoredAtom3643 Fin15AnchoredAtom3644
    Fin15AnchoredAtom3645 Fin15AnchoredAtom3701 Fin15AnchoredAtom3847 Fin15AnchoredAtom3848
    Fin15AnchoredAtom3849 Fin15AnchoredAtom3905 Fin15AnchoredAtom3961 Fin15AnchoredAtom4177
    Fin15AnchoredAtom4178 Fin15AnchoredAtom4179 Fin15AnchoredAtom4235 Fin15AnchoredAtom4291
    Fin15AnchoredAtom4627 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31215 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom2119 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom2134 chi ∧
      ¬Fin15AnchoredAtom2136 chi ∧
      ¬Fin15AnchoredAtom2139 chi ∧
      ¬Fin15AnchoredAtom2142 chi ∧
      ¬Fin15AnchoredAtom2145 chi ∧
      ¬Fin15AnchoredAtom2154 chi ∧
      ¬Fin15AnchoredAtom2215 chi ∧
      ¬Fin15AnchoredAtom2217 chi ∧
      ¬Fin15AnchoredAtom2220 chi ∧
      ¬Fin15AnchoredAtom2223 chi ∧
      ¬Fin15AnchoredAtom2226 chi ∧
      ¬Fin15AnchoredAtom2235 chi ∧
      ¬Fin15AnchoredAtom2272 chi ∧
      ¬Fin15AnchoredAtom2275 chi ∧
      ¬Fin15AnchoredAtom2284 chi ∧
      ¬Fin15AnchoredAtom2299 chi ∧
      ¬Fin15AnchoredAtom2380 chi ∧
      ¬Fin15AnchoredAtom2382 chi ∧
      ¬Fin15AnchoredAtom2385 chi ∧
      ¬Fin15AnchoredAtom2388 chi ∧
      ¬Fin15AnchoredAtom2391 chi ∧
      ¬Fin15AnchoredAtom2400 chi ∧
      ¬Fin15AnchoredAtom2437 chi ∧
      ¬Fin15AnchoredAtom2440 chi ∧
      ¬Fin15AnchoredAtom2449 chi ∧
      ¬Fin15AnchoredAtom2464 chi ∧
      ¬Fin15AnchoredAtom2641 chi ∧
      ¬Fin15AnchoredAtom2644 chi ∧
      ¬Fin15AnchoredAtom2653 chi ∧
      ¬Fin15AnchoredAtom2668 chi ∧
      ¬Fin15AnchoredAtom2759 chi ∧
      ¬Fin15AnchoredAtom3590 chi ∧
      ¬Fin15AnchoredAtom3592 chi ∧
      ¬Fin15AnchoredAtom3595 chi ∧
      ¬Fin15AnchoredAtom3598 chi ∧
      ¬Fin15AnchoredAtom3601 chi ∧
      ¬Fin15AnchoredAtom3610 chi ∧
      ¬Fin15AnchoredAtom3647 chi ∧
      ¬Fin15AnchoredAtom3650 chi ∧
      ¬Fin15AnchoredAtom3659 chi ∧
      ¬Fin15AnchoredAtom3674 chi ∧
      ¬Fin15AnchoredAtom3851 chi ∧
      ¬Fin15AnchoredAtom3854 chi ∧
      ¬Fin15AnchoredAtom3863 chi ∧
      ¬Fin15AnchoredAtom3878 chi ∧
      ¬Fin15AnchoredAtom3969 chi ∧
      ¬Fin15AnchoredAtom4181 chi ∧
      ¬Fin15AnchoredAtom4184 chi ∧
      ¬Fin15AnchoredAtom4193 chi ∧
      ¬Fin15AnchoredAtom4208 chi ∧
      ¬Fin15AnchoredAtom4299 chi ∧
      ¬Fin15AnchoredAtom4635 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 5, 7, 8, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09645
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2118 Fin15AnchoredAtom2119 Fin15AnchoredAtom2121
    Fin15AnchoredAtom2124 Fin15AnchoredAtom2134 Fin15AnchoredAtom2136 Fin15AnchoredAtom2139
    Fin15AnchoredAtom2142 Fin15AnchoredAtom2145 Fin15AnchoredAtom2154 Fin15AnchoredAtom2215
    Fin15AnchoredAtom2217 Fin15AnchoredAtom2220 Fin15AnchoredAtom2223 Fin15AnchoredAtom2226
    Fin15AnchoredAtom2235 Fin15AnchoredAtom2272 Fin15AnchoredAtom2275 Fin15AnchoredAtom2284
    Fin15AnchoredAtom2299 Fin15AnchoredAtom2380 Fin15AnchoredAtom2382 Fin15AnchoredAtom2385
    Fin15AnchoredAtom2388 Fin15AnchoredAtom2391 Fin15AnchoredAtom2400 Fin15AnchoredAtom2437
    Fin15AnchoredAtom2440 Fin15AnchoredAtom2449 Fin15AnchoredAtom2464 Fin15AnchoredAtom2641
    Fin15AnchoredAtom2644 Fin15AnchoredAtom2653 Fin15AnchoredAtom2668 Fin15AnchoredAtom2759
    Fin15AnchoredAtom3590 Fin15AnchoredAtom3592 Fin15AnchoredAtom3595 Fin15AnchoredAtom3598
    Fin15AnchoredAtom3601 Fin15AnchoredAtom3610 Fin15AnchoredAtom3647 Fin15AnchoredAtom3650
    Fin15AnchoredAtom3659 Fin15AnchoredAtom3674 Fin15AnchoredAtom3851 Fin15AnchoredAtom3854
    Fin15AnchoredAtom3863 Fin15AnchoredAtom3878 Fin15AnchoredAtom3969 Fin15AnchoredAtom4181
    Fin15AnchoredAtom4184 Fin15AnchoredAtom4193 Fin15AnchoredAtom4208 Fin15AnchoredAtom4299
    Fin15AnchoredAtom4635 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31216 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom2135 chi ∧
      ¬Fin15AnchoredAtom2136 chi ∧
      ¬Fin15AnchoredAtom2138 chi ∧
      ¬Fin15AnchoredAtom2147 chi ∧
      ¬Fin15AnchoredAtom2149 chi ∧
      ¬Fin15AnchoredAtom2153 chi ∧
      ¬Fin15AnchoredAtom2216 chi ∧
      ¬Fin15AnchoredAtom2217 chi ∧
      ¬Fin15AnchoredAtom2219 chi ∧
      ¬Fin15AnchoredAtom2228 chi ∧
      ¬Fin15AnchoredAtom2230 chi ∧
      ¬Fin15AnchoredAtom2234 chi ∧
      ¬Fin15AnchoredAtom2277 chi ∧
      ¬Fin15AnchoredAtom2279 chi ∧
      ¬Fin15AnchoredAtom2283 chi ∧
      ¬Fin15AnchoredAtom2308 chi ∧
      ¬Fin15AnchoredAtom2381 chi ∧
      ¬Fin15AnchoredAtom2382 chi ∧
      ¬Fin15AnchoredAtom2384 chi ∧
      ¬Fin15AnchoredAtom2393 chi ∧
      ¬Fin15AnchoredAtom2395 chi ∧
      ¬Fin15AnchoredAtom2399 chi ∧
      ¬Fin15AnchoredAtom2442 chi ∧
      ¬Fin15AnchoredAtom2444 chi ∧
      ¬Fin15AnchoredAtom2448 chi ∧
      ¬Fin15AnchoredAtom2473 chi ∧
      ¬Fin15AnchoredAtom2646 chi ∧
      ¬Fin15AnchoredAtom2648 chi ∧
      ¬Fin15AnchoredAtom2652 chi ∧
      ¬Fin15AnchoredAtom2677 chi ∧
      ¬Fin15AnchoredAtom2768 chi ∧
      ¬Fin15AnchoredAtom3591 chi ∧
      ¬Fin15AnchoredAtom3592 chi ∧
      ¬Fin15AnchoredAtom3594 chi ∧
      ¬Fin15AnchoredAtom3603 chi ∧
      ¬Fin15AnchoredAtom3605 chi ∧
      ¬Fin15AnchoredAtom3609 chi ∧
      ¬Fin15AnchoredAtom3652 chi ∧
      ¬Fin15AnchoredAtom3654 chi ∧
      ¬Fin15AnchoredAtom3658 chi ∧
      ¬Fin15AnchoredAtom3683 chi ∧
      ¬Fin15AnchoredAtom3856 chi ∧
      ¬Fin15AnchoredAtom3858 chi ∧
      ¬Fin15AnchoredAtom3862 chi ∧
      ¬Fin15AnchoredAtom3887 chi ∧
      ¬Fin15AnchoredAtom3978 chi ∧
      ¬Fin15AnchoredAtom4186 chi ∧
      ¬Fin15AnchoredAtom4188 chi ∧
      ¬Fin15AnchoredAtom4192 chi ∧
      ¬Fin15AnchoredAtom4217 chi ∧
      ¬Fin15AnchoredAtom4308 chi ∧
      ¬Fin15AnchoredAtom4644 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 5, 7, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05805
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2118 Fin15AnchoredAtom2120 Fin15AnchoredAtom2121
    Fin15AnchoredAtom2123 Fin15AnchoredAtom2135 Fin15AnchoredAtom2136 Fin15AnchoredAtom2138
    Fin15AnchoredAtom2147 Fin15AnchoredAtom2149 Fin15AnchoredAtom2153 Fin15AnchoredAtom2216
    Fin15AnchoredAtom2217 Fin15AnchoredAtom2219 Fin15AnchoredAtom2228 Fin15AnchoredAtom2230
    Fin15AnchoredAtom2234 Fin15AnchoredAtom2277 Fin15AnchoredAtom2279 Fin15AnchoredAtom2283
    Fin15AnchoredAtom2308 Fin15AnchoredAtom2381 Fin15AnchoredAtom2382 Fin15AnchoredAtom2384
    Fin15AnchoredAtom2393 Fin15AnchoredAtom2395 Fin15AnchoredAtom2399 Fin15AnchoredAtom2442
    Fin15AnchoredAtom2444 Fin15AnchoredAtom2448 Fin15AnchoredAtom2473 Fin15AnchoredAtom2646
    Fin15AnchoredAtom2648 Fin15AnchoredAtom2652 Fin15AnchoredAtom2677 Fin15AnchoredAtom2768
    Fin15AnchoredAtom3591 Fin15AnchoredAtom3592 Fin15AnchoredAtom3594 Fin15AnchoredAtom3603
    Fin15AnchoredAtom3605 Fin15AnchoredAtom3609 Fin15AnchoredAtom3652 Fin15AnchoredAtom3654
    Fin15AnchoredAtom3658 Fin15AnchoredAtom3683 Fin15AnchoredAtom3856 Fin15AnchoredAtom3858
    Fin15AnchoredAtom3862 Fin15AnchoredAtom3887 Fin15AnchoredAtom3978 Fin15AnchoredAtom4186
    Fin15AnchoredAtom4188 Fin15AnchoredAtom4192 Fin15AnchoredAtom4217 Fin15AnchoredAtom4308
    Fin15AnchoredAtom4644 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31217 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom2135 chi ∧
      ¬Fin15AnchoredAtom2136 chi ∧
      ¬Fin15AnchoredAtom2139 chi ∧
      ¬Fin15AnchoredAtom2147 chi ∧
      ¬Fin15AnchoredAtom2150 chi ∧
      ¬Fin15AnchoredAtom2154 chi ∧
      ¬Fin15AnchoredAtom2216 chi ∧
      ¬Fin15AnchoredAtom2217 chi ∧
      ¬Fin15AnchoredAtom2220 chi ∧
      ¬Fin15AnchoredAtom2228 chi ∧
      ¬Fin15AnchoredAtom2231 chi ∧
      ¬Fin15AnchoredAtom2235 chi ∧
      ¬Fin15AnchoredAtom2277 chi ∧
      ¬Fin15AnchoredAtom2280 chi ∧
      ¬Fin15AnchoredAtom2284 chi ∧
      ¬Fin15AnchoredAtom2309 chi ∧
      ¬Fin15AnchoredAtom2381 chi ∧
      ¬Fin15AnchoredAtom2382 chi ∧
      ¬Fin15AnchoredAtom2385 chi ∧
      ¬Fin15AnchoredAtom2393 chi ∧
      ¬Fin15AnchoredAtom2396 chi ∧
      ¬Fin15AnchoredAtom2400 chi ∧
      ¬Fin15AnchoredAtom2442 chi ∧
      ¬Fin15AnchoredAtom2445 chi ∧
      ¬Fin15AnchoredAtom2449 chi ∧
      ¬Fin15AnchoredAtom2474 chi ∧
      ¬Fin15AnchoredAtom2646 chi ∧
      ¬Fin15AnchoredAtom2649 chi ∧
      ¬Fin15AnchoredAtom2653 chi ∧
      ¬Fin15AnchoredAtom2678 chi ∧
      ¬Fin15AnchoredAtom2769 chi ∧
      ¬Fin15AnchoredAtom3591 chi ∧
      ¬Fin15AnchoredAtom3592 chi ∧
      ¬Fin15AnchoredAtom3595 chi ∧
      ¬Fin15AnchoredAtom3603 chi ∧
      ¬Fin15AnchoredAtom3606 chi ∧
      ¬Fin15AnchoredAtom3610 chi ∧
      ¬Fin15AnchoredAtom3652 chi ∧
      ¬Fin15AnchoredAtom3655 chi ∧
      ¬Fin15AnchoredAtom3659 chi ∧
      ¬Fin15AnchoredAtom3684 chi ∧
      ¬Fin15AnchoredAtom3856 chi ∧
      ¬Fin15AnchoredAtom3859 chi ∧
      ¬Fin15AnchoredAtom3863 chi ∧
      ¬Fin15AnchoredAtom3888 chi ∧
      ¬Fin15AnchoredAtom3979 chi ∧
      ¬Fin15AnchoredAtom4186 chi ∧
      ¬Fin15AnchoredAtom4189 chi ∧
      ¬Fin15AnchoredAtom4193 chi ∧
      ¬Fin15AnchoredAtom4218 chi ∧
      ¬Fin15AnchoredAtom4309 chi ∧
      ¬Fin15AnchoredAtom4645 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 5, 7, 9, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09901
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2118 Fin15AnchoredAtom2120 Fin15AnchoredAtom2121
    Fin15AnchoredAtom2124 Fin15AnchoredAtom2135 Fin15AnchoredAtom2136 Fin15AnchoredAtom2139
    Fin15AnchoredAtom2147 Fin15AnchoredAtom2150 Fin15AnchoredAtom2154 Fin15AnchoredAtom2216
    Fin15AnchoredAtom2217 Fin15AnchoredAtom2220 Fin15AnchoredAtom2228 Fin15AnchoredAtom2231
    Fin15AnchoredAtom2235 Fin15AnchoredAtom2277 Fin15AnchoredAtom2280 Fin15AnchoredAtom2284
    Fin15AnchoredAtom2309 Fin15AnchoredAtom2381 Fin15AnchoredAtom2382 Fin15AnchoredAtom2385
    Fin15AnchoredAtom2393 Fin15AnchoredAtom2396 Fin15AnchoredAtom2400 Fin15AnchoredAtom2442
    Fin15AnchoredAtom2445 Fin15AnchoredAtom2449 Fin15AnchoredAtom2474 Fin15AnchoredAtom2646
    Fin15AnchoredAtom2649 Fin15AnchoredAtom2653 Fin15AnchoredAtom2678 Fin15AnchoredAtom2769
    Fin15AnchoredAtom3591 Fin15AnchoredAtom3592 Fin15AnchoredAtom3595 Fin15AnchoredAtom3603
    Fin15AnchoredAtom3606 Fin15AnchoredAtom3610 Fin15AnchoredAtom3652 Fin15AnchoredAtom3655
    Fin15AnchoredAtom3659 Fin15AnchoredAtom3684 Fin15AnchoredAtom3856 Fin15AnchoredAtom3859
    Fin15AnchoredAtom3863 Fin15AnchoredAtom3888 Fin15AnchoredAtom3979 Fin15AnchoredAtom4186
    Fin15AnchoredAtom4189 Fin15AnchoredAtom4193 Fin15AnchoredAtom4218 Fin15AnchoredAtom4309
    Fin15AnchoredAtom4645 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31218 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom2135 chi ∧
      ¬Fin15AnchoredAtom2136 chi ∧
      ¬Fin15AnchoredAtom2140 chi ∧
      ¬Fin15AnchoredAtom2147 chi ∧
      ¬Fin15AnchoredAtom2151 chi ∧
      ¬Fin15AnchoredAtom2155 chi ∧
      ¬Fin15AnchoredAtom2216 chi ∧
      ¬Fin15AnchoredAtom2217 chi ∧
      ¬Fin15AnchoredAtom2221 chi ∧
      ¬Fin15AnchoredAtom2228 chi ∧
      ¬Fin15AnchoredAtom2232 chi ∧
      ¬Fin15AnchoredAtom2236 chi ∧
      ¬Fin15AnchoredAtom2277 chi ∧
      ¬Fin15AnchoredAtom2281 chi ∧
      ¬Fin15AnchoredAtom2285 chi ∧
      ¬Fin15AnchoredAtom2310 chi ∧
      ¬Fin15AnchoredAtom2381 chi ∧
      ¬Fin15AnchoredAtom2382 chi ∧
      ¬Fin15AnchoredAtom2386 chi ∧
      ¬Fin15AnchoredAtom2393 chi ∧
      ¬Fin15AnchoredAtom2397 chi ∧
      ¬Fin15AnchoredAtom2401 chi ∧
      ¬Fin15AnchoredAtom2442 chi ∧
      ¬Fin15AnchoredAtom2446 chi ∧
      ¬Fin15AnchoredAtom2450 chi ∧
      ¬Fin15AnchoredAtom2475 chi ∧
      ¬Fin15AnchoredAtom2646 chi ∧
      ¬Fin15AnchoredAtom2650 chi ∧
      ¬Fin15AnchoredAtom2654 chi ∧
      ¬Fin15AnchoredAtom2679 chi ∧
      ¬Fin15AnchoredAtom2770 chi ∧
      ¬Fin15AnchoredAtom3591 chi ∧
      ¬Fin15AnchoredAtom3592 chi ∧
      ¬Fin15AnchoredAtom3596 chi ∧
      ¬Fin15AnchoredAtom3603 chi ∧
      ¬Fin15AnchoredAtom3607 chi ∧
      ¬Fin15AnchoredAtom3611 chi ∧
      ¬Fin15AnchoredAtom3652 chi ∧
      ¬Fin15AnchoredAtom3656 chi ∧
      ¬Fin15AnchoredAtom3660 chi ∧
      ¬Fin15AnchoredAtom3685 chi ∧
      ¬Fin15AnchoredAtom3856 chi ∧
      ¬Fin15AnchoredAtom3860 chi ∧
      ¬Fin15AnchoredAtom3864 chi ∧
      ¬Fin15AnchoredAtom3889 chi ∧
      ¬Fin15AnchoredAtom3980 chi ∧
      ¬Fin15AnchoredAtom4186 chi ∧
      ¬Fin15AnchoredAtom4190 chi ∧
      ¬Fin15AnchoredAtom4194 chi ∧
      ¬Fin15AnchoredAtom4219 chi ∧
      ¬Fin15AnchoredAtom4310 chi ∧
      ¬Fin15AnchoredAtom4646 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 5, 7, 9, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask18093
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2118 Fin15AnchoredAtom2120 Fin15AnchoredAtom2121
    Fin15AnchoredAtom2125 Fin15AnchoredAtom2135 Fin15AnchoredAtom2136 Fin15AnchoredAtom2140
    Fin15AnchoredAtom2147 Fin15AnchoredAtom2151 Fin15AnchoredAtom2155 Fin15AnchoredAtom2216
    Fin15AnchoredAtom2217 Fin15AnchoredAtom2221 Fin15AnchoredAtom2228 Fin15AnchoredAtom2232
    Fin15AnchoredAtom2236 Fin15AnchoredAtom2277 Fin15AnchoredAtom2281 Fin15AnchoredAtom2285
    Fin15AnchoredAtom2310 Fin15AnchoredAtom2381 Fin15AnchoredAtom2382 Fin15AnchoredAtom2386
    Fin15AnchoredAtom2393 Fin15AnchoredAtom2397 Fin15AnchoredAtom2401 Fin15AnchoredAtom2442
    Fin15AnchoredAtom2446 Fin15AnchoredAtom2450 Fin15AnchoredAtom2475 Fin15AnchoredAtom2646
    Fin15AnchoredAtom2650 Fin15AnchoredAtom2654 Fin15AnchoredAtom2679 Fin15AnchoredAtom2770
    Fin15AnchoredAtom3591 Fin15AnchoredAtom3592 Fin15AnchoredAtom3596 Fin15AnchoredAtom3603
    Fin15AnchoredAtom3607 Fin15AnchoredAtom3611 Fin15AnchoredAtom3652 Fin15AnchoredAtom3656
    Fin15AnchoredAtom3660 Fin15AnchoredAtom3685 Fin15AnchoredAtom3856 Fin15AnchoredAtom3860
    Fin15AnchoredAtom3864 Fin15AnchoredAtom3889 Fin15AnchoredAtom3980 Fin15AnchoredAtom4186
    Fin15AnchoredAtom4190 Fin15AnchoredAtom4194 Fin15AnchoredAtom4219 Fin15AnchoredAtom4310
    Fin15AnchoredAtom4646 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31219 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom2135 chi ∧
      ¬Fin15AnchoredAtom2138 chi ∧
      ¬Fin15AnchoredAtom2139 chi ∧
      ¬Fin15AnchoredAtom2149 chi ∧
      ¬Fin15AnchoredAtom2150 chi ∧
      ¬Fin15AnchoredAtom2159 chi ∧
      ¬Fin15AnchoredAtom2216 chi ∧
      ¬Fin15AnchoredAtom2219 chi ∧
      ¬Fin15AnchoredAtom2220 chi ∧
      ¬Fin15AnchoredAtom2230 chi ∧
      ¬Fin15AnchoredAtom2231 chi ∧
      ¬Fin15AnchoredAtom2240 chi ∧
      ¬Fin15AnchoredAtom2279 chi ∧
      ¬Fin15AnchoredAtom2280 chi ∧
      ¬Fin15AnchoredAtom2289 chi ∧
      ¬Fin15AnchoredAtom2314 chi ∧
      ¬Fin15AnchoredAtom2381 chi ∧
      ¬Fin15AnchoredAtom2384 chi ∧
      ¬Fin15AnchoredAtom2385 chi ∧
      ¬Fin15AnchoredAtom2395 chi ∧
      ¬Fin15AnchoredAtom2396 chi ∧
      ¬Fin15AnchoredAtom2405 chi ∧
      ¬Fin15AnchoredAtom2444 chi ∧
      ¬Fin15AnchoredAtom2445 chi ∧
      ¬Fin15AnchoredAtom2454 chi ∧
      ¬Fin15AnchoredAtom2479 chi ∧
      ¬Fin15AnchoredAtom2648 chi ∧
      ¬Fin15AnchoredAtom2649 chi ∧
      ¬Fin15AnchoredAtom2658 chi ∧
      ¬Fin15AnchoredAtom2683 chi ∧
      ¬Fin15AnchoredAtom2774 chi ∧
      ¬Fin15AnchoredAtom3591 chi ∧
      ¬Fin15AnchoredAtom3594 chi ∧
      ¬Fin15AnchoredAtom3595 chi ∧
      ¬Fin15AnchoredAtom3605 chi ∧
      ¬Fin15AnchoredAtom3606 chi ∧
      ¬Fin15AnchoredAtom3615 chi ∧
      ¬Fin15AnchoredAtom3654 chi ∧
      ¬Fin15AnchoredAtom3655 chi ∧
      ¬Fin15AnchoredAtom3664 chi ∧
      ¬Fin15AnchoredAtom3689 chi ∧
      ¬Fin15AnchoredAtom3858 chi ∧
      ¬Fin15AnchoredAtom3859 chi ∧
      ¬Fin15AnchoredAtom3868 chi ∧
      ¬Fin15AnchoredAtom3893 chi ∧
      ¬Fin15AnchoredAtom3984 chi ∧
      ¬Fin15AnchoredAtom4188 chi ∧
      ¬Fin15AnchoredAtom4189 chi ∧
      ¬Fin15AnchoredAtom4198 chi ∧
      ¬Fin15AnchoredAtom4223 chi ∧
      ¬Fin15AnchoredAtom4314 chi ∧
      ¬Fin15AnchoredAtom4650 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 5, 7, 9, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask12973
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2118 Fin15AnchoredAtom2120 Fin15AnchoredAtom2123
    Fin15AnchoredAtom2124 Fin15AnchoredAtom2135 Fin15AnchoredAtom2138 Fin15AnchoredAtom2139
    Fin15AnchoredAtom2149 Fin15AnchoredAtom2150 Fin15AnchoredAtom2159 Fin15AnchoredAtom2216
    Fin15AnchoredAtom2219 Fin15AnchoredAtom2220 Fin15AnchoredAtom2230 Fin15AnchoredAtom2231
    Fin15AnchoredAtom2240 Fin15AnchoredAtom2279 Fin15AnchoredAtom2280 Fin15AnchoredAtom2289
    Fin15AnchoredAtom2314 Fin15AnchoredAtom2381 Fin15AnchoredAtom2384 Fin15AnchoredAtom2385
    Fin15AnchoredAtom2395 Fin15AnchoredAtom2396 Fin15AnchoredAtom2405 Fin15AnchoredAtom2444
    Fin15AnchoredAtom2445 Fin15AnchoredAtom2454 Fin15AnchoredAtom2479 Fin15AnchoredAtom2648
    Fin15AnchoredAtom2649 Fin15AnchoredAtom2658 Fin15AnchoredAtom2683 Fin15AnchoredAtom2774
    Fin15AnchoredAtom3591 Fin15AnchoredAtom3594 Fin15AnchoredAtom3595 Fin15AnchoredAtom3605
    Fin15AnchoredAtom3606 Fin15AnchoredAtom3615 Fin15AnchoredAtom3654 Fin15AnchoredAtom3655
    Fin15AnchoredAtom3664 Fin15AnchoredAtom3689 Fin15AnchoredAtom3858 Fin15AnchoredAtom3859
    Fin15AnchoredAtom3868 Fin15AnchoredAtom3893 Fin15AnchoredAtom3984 Fin15AnchoredAtom4188
    Fin15AnchoredAtom4189 Fin15AnchoredAtom4198 Fin15AnchoredAtom4223 Fin15AnchoredAtom4314
    Fin15AnchoredAtom4650 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31220 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom2135 chi ∧
      ¬Fin15AnchoredAtom2138 chi ∧
      ¬Fin15AnchoredAtom2140 chi ∧
      ¬Fin15AnchoredAtom2149 chi ∧
      ¬Fin15AnchoredAtom2151 chi ∧
      ¬Fin15AnchoredAtom2160 chi ∧
      ¬Fin15AnchoredAtom2216 chi ∧
      ¬Fin15AnchoredAtom2219 chi ∧
      ¬Fin15AnchoredAtom2221 chi ∧
      ¬Fin15AnchoredAtom2230 chi ∧
      ¬Fin15AnchoredAtom2232 chi ∧
      ¬Fin15AnchoredAtom2241 chi ∧
      ¬Fin15AnchoredAtom2279 chi ∧
      ¬Fin15AnchoredAtom2281 chi ∧
      ¬Fin15AnchoredAtom2290 chi ∧
      ¬Fin15AnchoredAtom2315 chi ∧
      ¬Fin15AnchoredAtom2381 chi ∧
      ¬Fin15AnchoredAtom2384 chi ∧
      ¬Fin15AnchoredAtom2386 chi ∧
      ¬Fin15AnchoredAtom2395 chi ∧
      ¬Fin15AnchoredAtom2397 chi ∧
      ¬Fin15AnchoredAtom2406 chi ∧
      ¬Fin15AnchoredAtom2444 chi ∧
      ¬Fin15AnchoredAtom2446 chi ∧
      ¬Fin15AnchoredAtom2455 chi ∧
      ¬Fin15AnchoredAtom2480 chi ∧
      ¬Fin15AnchoredAtom2648 chi ∧
      ¬Fin15AnchoredAtom2650 chi ∧
      ¬Fin15AnchoredAtom2659 chi ∧
      ¬Fin15AnchoredAtom2684 chi ∧
      ¬Fin15AnchoredAtom2775 chi ∧
      ¬Fin15AnchoredAtom3591 chi ∧
      ¬Fin15AnchoredAtom3594 chi ∧
      ¬Fin15AnchoredAtom3596 chi ∧
      ¬Fin15AnchoredAtom3605 chi ∧
      ¬Fin15AnchoredAtom3607 chi ∧
      ¬Fin15AnchoredAtom3616 chi ∧
      ¬Fin15AnchoredAtom3654 chi ∧
      ¬Fin15AnchoredAtom3656 chi ∧
      ¬Fin15AnchoredAtom3665 chi ∧
      ¬Fin15AnchoredAtom3690 chi ∧
      ¬Fin15AnchoredAtom3858 chi ∧
      ¬Fin15AnchoredAtom3860 chi ∧
      ¬Fin15AnchoredAtom3869 chi ∧
      ¬Fin15AnchoredAtom3894 chi ∧
      ¬Fin15AnchoredAtom3985 chi ∧
      ¬Fin15AnchoredAtom4188 chi ∧
      ¬Fin15AnchoredAtom4190 chi ∧
      ¬Fin15AnchoredAtom4199 chi ∧
      ¬Fin15AnchoredAtom4224 chi ∧
      ¬Fin15AnchoredAtom4315 chi ∧
      ¬Fin15AnchoredAtom4651 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 5, 7, 9, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21165
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2118 Fin15AnchoredAtom2120 Fin15AnchoredAtom2123
    Fin15AnchoredAtom2125 Fin15AnchoredAtom2135 Fin15AnchoredAtom2138 Fin15AnchoredAtom2140
    Fin15AnchoredAtom2149 Fin15AnchoredAtom2151 Fin15AnchoredAtom2160 Fin15AnchoredAtom2216
    Fin15AnchoredAtom2219 Fin15AnchoredAtom2221 Fin15AnchoredAtom2230 Fin15AnchoredAtom2232
    Fin15AnchoredAtom2241 Fin15AnchoredAtom2279 Fin15AnchoredAtom2281 Fin15AnchoredAtom2290
    Fin15AnchoredAtom2315 Fin15AnchoredAtom2381 Fin15AnchoredAtom2384 Fin15AnchoredAtom2386
    Fin15AnchoredAtom2395 Fin15AnchoredAtom2397 Fin15AnchoredAtom2406 Fin15AnchoredAtom2444
    Fin15AnchoredAtom2446 Fin15AnchoredAtom2455 Fin15AnchoredAtom2480 Fin15AnchoredAtom2648
    Fin15AnchoredAtom2650 Fin15AnchoredAtom2659 Fin15AnchoredAtom2684 Fin15AnchoredAtom2775
    Fin15AnchoredAtom3591 Fin15AnchoredAtom3594 Fin15AnchoredAtom3596 Fin15AnchoredAtom3605
    Fin15AnchoredAtom3607 Fin15AnchoredAtom3616 Fin15AnchoredAtom3654 Fin15AnchoredAtom3656
    Fin15AnchoredAtom3665 Fin15AnchoredAtom3690 Fin15AnchoredAtom3858 Fin15AnchoredAtom3860
    Fin15AnchoredAtom3869 Fin15AnchoredAtom3894 Fin15AnchoredAtom3985 Fin15AnchoredAtom4188
    Fin15AnchoredAtom4190 Fin15AnchoredAtom4199 Fin15AnchoredAtom4224 Fin15AnchoredAtom4315
    Fin15AnchoredAtom4651 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31221 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom2135 chi ∧
      ¬Fin15AnchoredAtom2139 chi ∧
      ¬Fin15AnchoredAtom2140 chi ∧
      ¬Fin15AnchoredAtom2150 chi ∧
      ¬Fin15AnchoredAtom2151 chi ∧
      ¬Fin15AnchoredAtom2161 chi ∧
      ¬Fin15AnchoredAtom2216 chi ∧
      ¬Fin15AnchoredAtom2220 chi ∧
      ¬Fin15AnchoredAtom2221 chi ∧
      ¬Fin15AnchoredAtom2231 chi ∧
      ¬Fin15AnchoredAtom2232 chi ∧
      ¬Fin15AnchoredAtom2242 chi ∧
      ¬Fin15AnchoredAtom2280 chi ∧
      ¬Fin15AnchoredAtom2281 chi ∧
      ¬Fin15AnchoredAtom2291 chi ∧
      ¬Fin15AnchoredAtom2316 chi ∧
      ¬Fin15AnchoredAtom2381 chi ∧
      ¬Fin15AnchoredAtom2385 chi ∧
      ¬Fin15AnchoredAtom2386 chi ∧
      ¬Fin15AnchoredAtom2396 chi ∧
      ¬Fin15AnchoredAtom2397 chi ∧
      ¬Fin15AnchoredAtom2407 chi ∧
      ¬Fin15AnchoredAtom2445 chi ∧
      ¬Fin15AnchoredAtom2446 chi ∧
      ¬Fin15AnchoredAtom2456 chi ∧
      ¬Fin15AnchoredAtom2481 chi ∧
      ¬Fin15AnchoredAtom2649 chi ∧
      ¬Fin15AnchoredAtom2650 chi ∧
      ¬Fin15AnchoredAtom2660 chi ∧
      ¬Fin15AnchoredAtom2685 chi ∧
      ¬Fin15AnchoredAtom2776 chi ∧
      ¬Fin15AnchoredAtom3591 chi ∧
      ¬Fin15AnchoredAtom3595 chi ∧
      ¬Fin15AnchoredAtom3596 chi ∧
      ¬Fin15AnchoredAtom3606 chi ∧
      ¬Fin15AnchoredAtom3607 chi ∧
      ¬Fin15AnchoredAtom3617 chi ∧
      ¬Fin15AnchoredAtom3655 chi ∧
      ¬Fin15AnchoredAtom3656 chi ∧
      ¬Fin15AnchoredAtom3666 chi ∧
      ¬Fin15AnchoredAtom3691 chi ∧
      ¬Fin15AnchoredAtom3859 chi ∧
      ¬Fin15AnchoredAtom3860 chi ∧
      ¬Fin15AnchoredAtom3870 chi ∧
      ¬Fin15AnchoredAtom3895 chi ∧
      ¬Fin15AnchoredAtom3986 chi ∧
      ¬Fin15AnchoredAtom4189 chi ∧
      ¬Fin15AnchoredAtom4190 chi ∧
      ¬Fin15AnchoredAtom4200 chi ∧
      ¬Fin15AnchoredAtom4225 chi ∧
      ¬Fin15AnchoredAtom4316 chi ∧
      ¬Fin15AnchoredAtom4652 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 5, 7, 9, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25261
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2118 Fin15AnchoredAtom2120 Fin15AnchoredAtom2124
    Fin15AnchoredAtom2125 Fin15AnchoredAtom2135 Fin15AnchoredAtom2139 Fin15AnchoredAtom2140
    Fin15AnchoredAtom2150 Fin15AnchoredAtom2151 Fin15AnchoredAtom2161 Fin15AnchoredAtom2216
    Fin15AnchoredAtom2220 Fin15AnchoredAtom2221 Fin15AnchoredAtom2231 Fin15AnchoredAtom2232
    Fin15AnchoredAtom2242 Fin15AnchoredAtom2280 Fin15AnchoredAtom2281 Fin15AnchoredAtom2291
    Fin15AnchoredAtom2316 Fin15AnchoredAtom2381 Fin15AnchoredAtom2385 Fin15AnchoredAtom2386
    Fin15AnchoredAtom2396 Fin15AnchoredAtom2397 Fin15AnchoredAtom2407 Fin15AnchoredAtom2445
    Fin15AnchoredAtom2446 Fin15AnchoredAtom2456 Fin15AnchoredAtom2481 Fin15AnchoredAtom2649
    Fin15AnchoredAtom2650 Fin15AnchoredAtom2660 Fin15AnchoredAtom2685 Fin15AnchoredAtom2776
    Fin15AnchoredAtom3591 Fin15AnchoredAtom3595 Fin15AnchoredAtom3596 Fin15AnchoredAtom3606
    Fin15AnchoredAtom3607 Fin15AnchoredAtom3617 Fin15AnchoredAtom3655 Fin15AnchoredAtom3656
    Fin15AnchoredAtom3666 Fin15AnchoredAtom3691 Fin15AnchoredAtom3859 Fin15AnchoredAtom3860
    Fin15AnchoredAtom3870 Fin15AnchoredAtom3895 Fin15AnchoredAtom3986 Fin15AnchoredAtom4189
    Fin15AnchoredAtom4190 Fin15AnchoredAtom4200 Fin15AnchoredAtom4225 Fin15AnchoredAtom4316
    Fin15AnchoredAtom4652 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31222 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom2136 chi ∧
      ¬Fin15AnchoredAtom2138 chi ∧
      ¬Fin15AnchoredAtom2139 chi ∧
      ¬Fin15AnchoredAtom2153 chi ∧
      ¬Fin15AnchoredAtom2154 chi ∧
      ¬Fin15AnchoredAtom2159 chi ∧
      ¬Fin15AnchoredAtom2217 chi ∧
      ¬Fin15AnchoredAtom2219 chi ∧
      ¬Fin15AnchoredAtom2220 chi ∧
      ¬Fin15AnchoredAtom2234 chi ∧
      ¬Fin15AnchoredAtom2235 chi ∧
      ¬Fin15AnchoredAtom2240 chi ∧
      ¬Fin15AnchoredAtom2283 chi ∧
      ¬Fin15AnchoredAtom2284 chi ∧
      ¬Fin15AnchoredAtom2289 chi ∧
      ¬Fin15AnchoredAtom2320 chi ∧
      ¬Fin15AnchoredAtom2382 chi ∧
      ¬Fin15AnchoredAtom2384 chi ∧
      ¬Fin15AnchoredAtom2385 chi ∧
      ¬Fin15AnchoredAtom2399 chi ∧
      ¬Fin15AnchoredAtom2400 chi ∧
      ¬Fin15AnchoredAtom2405 chi ∧
      ¬Fin15AnchoredAtom2448 chi ∧
      ¬Fin15AnchoredAtom2449 chi ∧
      ¬Fin15AnchoredAtom2454 chi ∧
      ¬Fin15AnchoredAtom2485 chi ∧
      ¬Fin15AnchoredAtom2652 chi ∧
      ¬Fin15AnchoredAtom2653 chi ∧
      ¬Fin15AnchoredAtom2658 chi ∧
      ¬Fin15AnchoredAtom2689 chi ∧
      ¬Fin15AnchoredAtom2780 chi ∧
      ¬Fin15AnchoredAtom3592 chi ∧
      ¬Fin15AnchoredAtom3594 chi ∧
      ¬Fin15AnchoredAtom3595 chi ∧
      ¬Fin15AnchoredAtom3609 chi ∧
      ¬Fin15AnchoredAtom3610 chi ∧
      ¬Fin15AnchoredAtom3615 chi ∧
      ¬Fin15AnchoredAtom3658 chi ∧
      ¬Fin15AnchoredAtom3659 chi ∧
      ¬Fin15AnchoredAtom3664 chi ∧
      ¬Fin15AnchoredAtom3695 chi ∧
      ¬Fin15AnchoredAtom3862 chi ∧
      ¬Fin15AnchoredAtom3863 chi ∧
      ¬Fin15AnchoredAtom3868 chi ∧
      ¬Fin15AnchoredAtom3899 chi ∧
      ¬Fin15AnchoredAtom3990 chi ∧
      ¬Fin15AnchoredAtom4192 chi ∧
      ¬Fin15AnchoredAtom4193 chi ∧
      ¬Fin15AnchoredAtom4198 chi ∧
      ¬Fin15AnchoredAtom4229 chi ∧
      ¬Fin15AnchoredAtom4320 chi ∧
      ¬Fin15AnchoredAtom4656 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 5, 7, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13485
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2118 Fin15AnchoredAtom2121 Fin15AnchoredAtom2123
    Fin15AnchoredAtom2124 Fin15AnchoredAtom2136 Fin15AnchoredAtom2138 Fin15AnchoredAtom2139
    Fin15AnchoredAtom2153 Fin15AnchoredAtom2154 Fin15AnchoredAtom2159 Fin15AnchoredAtom2217
    Fin15AnchoredAtom2219 Fin15AnchoredAtom2220 Fin15AnchoredAtom2234 Fin15AnchoredAtom2235
    Fin15AnchoredAtom2240 Fin15AnchoredAtom2283 Fin15AnchoredAtom2284 Fin15AnchoredAtom2289
    Fin15AnchoredAtom2320 Fin15AnchoredAtom2382 Fin15AnchoredAtom2384 Fin15AnchoredAtom2385
    Fin15AnchoredAtom2399 Fin15AnchoredAtom2400 Fin15AnchoredAtom2405 Fin15AnchoredAtom2448
    Fin15AnchoredAtom2449 Fin15AnchoredAtom2454 Fin15AnchoredAtom2485 Fin15AnchoredAtom2652
    Fin15AnchoredAtom2653 Fin15AnchoredAtom2658 Fin15AnchoredAtom2689 Fin15AnchoredAtom2780
    Fin15AnchoredAtom3592 Fin15AnchoredAtom3594 Fin15AnchoredAtom3595 Fin15AnchoredAtom3609
    Fin15AnchoredAtom3610 Fin15AnchoredAtom3615 Fin15AnchoredAtom3658 Fin15AnchoredAtom3659
    Fin15AnchoredAtom3664 Fin15AnchoredAtom3695 Fin15AnchoredAtom3862 Fin15AnchoredAtom3863
    Fin15AnchoredAtom3868 Fin15AnchoredAtom3899 Fin15AnchoredAtom3990 Fin15AnchoredAtom4192
    Fin15AnchoredAtom4193 Fin15AnchoredAtom4198 Fin15AnchoredAtom4229 Fin15AnchoredAtom4320
    Fin15AnchoredAtom4656 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31223 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom2136 chi ∧
      ¬Fin15AnchoredAtom2138 chi ∧
      ¬Fin15AnchoredAtom2140 chi ∧
      ¬Fin15AnchoredAtom2153 chi ∧
      ¬Fin15AnchoredAtom2155 chi ∧
      ¬Fin15AnchoredAtom2160 chi ∧
      ¬Fin15AnchoredAtom2217 chi ∧
      ¬Fin15AnchoredAtom2219 chi ∧
      ¬Fin15AnchoredAtom2221 chi ∧
      ¬Fin15AnchoredAtom2234 chi ∧
      ¬Fin15AnchoredAtom2236 chi ∧
      ¬Fin15AnchoredAtom2241 chi ∧
      ¬Fin15AnchoredAtom2283 chi ∧
      ¬Fin15AnchoredAtom2285 chi ∧
      ¬Fin15AnchoredAtom2290 chi ∧
      ¬Fin15AnchoredAtom2321 chi ∧
      ¬Fin15AnchoredAtom2382 chi ∧
      ¬Fin15AnchoredAtom2384 chi ∧
      ¬Fin15AnchoredAtom2386 chi ∧
      ¬Fin15AnchoredAtom2399 chi ∧
      ¬Fin15AnchoredAtom2401 chi ∧
      ¬Fin15AnchoredAtom2406 chi ∧
      ¬Fin15AnchoredAtom2448 chi ∧
      ¬Fin15AnchoredAtom2450 chi ∧
      ¬Fin15AnchoredAtom2455 chi ∧
      ¬Fin15AnchoredAtom2486 chi ∧
      ¬Fin15AnchoredAtom2652 chi ∧
      ¬Fin15AnchoredAtom2654 chi ∧
      ¬Fin15AnchoredAtom2659 chi ∧
      ¬Fin15AnchoredAtom2690 chi ∧
      ¬Fin15AnchoredAtom2781 chi ∧
      ¬Fin15AnchoredAtom3592 chi ∧
      ¬Fin15AnchoredAtom3594 chi ∧
      ¬Fin15AnchoredAtom3596 chi ∧
      ¬Fin15AnchoredAtom3609 chi ∧
      ¬Fin15AnchoredAtom3611 chi ∧
      ¬Fin15AnchoredAtom3616 chi ∧
      ¬Fin15AnchoredAtom3658 chi ∧
      ¬Fin15AnchoredAtom3660 chi ∧
      ¬Fin15AnchoredAtom3665 chi ∧
      ¬Fin15AnchoredAtom3696 chi ∧
      ¬Fin15AnchoredAtom3862 chi ∧
      ¬Fin15AnchoredAtom3864 chi ∧
      ¬Fin15AnchoredAtom3869 chi ∧
      ¬Fin15AnchoredAtom3900 chi ∧
      ¬Fin15AnchoredAtom3991 chi ∧
      ¬Fin15AnchoredAtom4192 chi ∧
      ¬Fin15AnchoredAtom4194 chi ∧
      ¬Fin15AnchoredAtom4199 chi ∧
      ¬Fin15AnchoredAtom4230 chi ∧
      ¬Fin15AnchoredAtom4321 chi ∧
      ¬Fin15AnchoredAtom4657 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 5, 7, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21677
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2118 Fin15AnchoredAtom2121 Fin15AnchoredAtom2123
    Fin15AnchoredAtom2125 Fin15AnchoredAtom2136 Fin15AnchoredAtom2138 Fin15AnchoredAtom2140
    Fin15AnchoredAtom2153 Fin15AnchoredAtom2155 Fin15AnchoredAtom2160 Fin15AnchoredAtom2217
    Fin15AnchoredAtom2219 Fin15AnchoredAtom2221 Fin15AnchoredAtom2234 Fin15AnchoredAtom2236
    Fin15AnchoredAtom2241 Fin15AnchoredAtom2283 Fin15AnchoredAtom2285 Fin15AnchoredAtom2290
    Fin15AnchoredAtom2321 Fin15AnchoredAtom2382 Fin15AnchoredAtom2384 Fin15AnchoredAtom2386
    Fin15AnchoredAtom2399 Fin15AnchoredAtom2401 Fin15AnchoredAtom2406 Fin15AnchoredAtom2448
    Fin15AnchoredAtom2450 Fin15AnchoredAtom2455 Fin15AnchoredAtom2486 Fin15AnchoredAtom2652
    Fin15AnchoredAtom2654 Fin15AnchoredAtom2659 Fin15AnchoredAtom2690 Fin15AnchoredAtom2781
    Fin15AnchoredAtom3592 Fin15AnchoredAtom3594 Fin15AnchoredAtom3596 Fin15AnchoredAtom3609
    Fin15AnchoredAtom3611 Fin15AnchoredAtom3616 Fin15AnchoredAtom3658 Fin15AnchoredAtom3660
    Fin15AnchoredAtom3665 Fin15AnchoredAtom3696 Fin15AnchoredAtom3862 Fin15AnchoredAtom3864
    Fin15AnchoredAtom3869 Fin15AnchoredAtom3900 Fin15AnchoredAtom3991 Fin15AnchoredAtom4192
    Fin15AnchoredAtom4194 Fin15AnchoredAtom4199 Fin15AnchoredAtom4230 Fin15AnchoredAtom4321
    Fin15AnchoredAtom4657 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31224 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom2136 chi ∧
      ¬Fin15AnchoredAtom2139 chi ∧
      ¬Fin15AnchoredAtom2140 chi ∧
      ¬Fin15AnchoredAtom2154 chi ∧
      ¬Fin15AnchoredAtom2155 chi ∧
      ¬Fin15AnchoredAtom2161 chi ∧
      ¬Fin15AnchoredAtom2217 chi ∧
      ¬Fin15AnchoredAtom2220 chi ∧
      ¬Fin15AnchoredAtom2221 chi ∧
      ¬Fin15AnchoredAtom2235 chi ∧
      ¬Fin15AnchoredAtom2236 chi ∧
      ¬Fin15AnchoredAtom2242 chi ∧
      ¬Fin15AnchoredAtom2284 chi ∧
      ¬Fin15AnchoredAtom2285 chi ∧
      ¬Fin15AnchoredAtom2291 chi ∧
      ¬Fin15AnchoredAtom2322 chi ∧
      ¬Fin15AnchoredAtom2382 chi ∧
      ¬Fin15AnchoredAtom2385 chi ∧
      ¬Fin15AnchoredAtom2386 chi ∧
      ¬Fin15AnchoredAtom2400 chi ∧
      ¬Fin15AnchoredAtom2401 chi ∧
      ¬Fin15AnchoredAtom2407 chi ∧
      ¬Fin15AnchoredAtom2449 chi ∧
      ¬Fin15AnchoredAtom2450 chi ∧
      ¬Fin15AnchoredAtom2456 chi ∧
      ¬Fin15AnchoredAtom2487 chi ∧
      ¬Fin15AnchoredAtom2653 chi ∧
      ¬Fin15AnchoredAtom2654 chi ∧
      ¬Fin15AnchoredAtom2660 chi ∧
      ¬Fin15AnchoredAtom2691 chi ∧
      ¬Fin15AnchoredAtom2782 chi ∧
      ¬Fin15AnchoredAtom3592 chi ∧
      ¬Fin15AnchoredAtom3595 chi ∧
      ¬Fin15AnchoredAtom3596 chi ∧
      ¬Fin15AnchoredAtom3610 chi ∧
      ¬Fin15AnchoredAtom3611 chi ∧
      ¬Fin15AnchoredAtom3617 chi ∧
      ¬Fin15AnchoredAtom3659 chi ∧
      ¬Fin15AnchoredAtom3660 chi ∧
      ¬Fin15AnchoredAtom3666 chi ∧
      ¬Fin15AnchoredAtom3697 chi ∧
      ¬Fin15AnchoredAtom3863 chi ∧
      ¬Fin15AnchoredAtom3864 chi ∧
      ¬Fin15AnchoredAtom3870 chi ∧
      ¬Fin15AnchoredAtom3901 chi ∧
      ¬Fin15AnchoredAtom3992 chi ∧
      ¬Fin15AnchoredAtom4193 chi ∧
      ¬Fin15AnchoredAtom4194 chi ∧
      ¬Fin15AnchoredAtom4200 chi ∧
      ¬Fin15AnchoredAtom4231 chi ∧
      ¬Fin15AnchoredAtom4322 chi ∧
      ¬Fin15AnchoredAtom4658 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 5, 7, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25773
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2118 Fin15AnchoredAtom2121 Fin15AnchoredAtom2124
    Fin15AnchoredAtom2125 Fin15AnchoredAtom2136 Fin15AnchoredAtom2139 Fin15AnchoredAtom2140
    Fin15AnchoredAtom2154 Fin15AnchoredAtom2155 Fin15AnchoredAtom2161 Fin15AnchoredAtom2217
    Fin15AnchoredAtom2220 Fin15AnchoredAtom2221 Fin15AnchoredAtom2235 Fin15AnchoredAtom2236
    Fin15AnchoredAtom2242 Fin15AnchoredAtom2284 Fin15AnchoredAtom2285 Fin15AnchoredAtom2291
    Fin15AnchoredAtom2322 Fin15AnchoredAtom2382 Fin15AnchoredAtom2385 Fin15AnchoredAtom2386
    Fin15AnchoredAtom2400 Fin15AnchoredAtom2401 Fin15AnchoredAtom2407 Fin15AnchoredAtom2449
    Fin15AnchoredAtom2450 Fin15AnchoredAtom2456 Fin15AnchoredAtom2487 Fin15AnchoredAtom2653
    Fin15AnchoredAtom2654 Fin15AnchoredAtom2660 Fin15AnchoredAtom2691 Fin15AnchoredAtom2782
    Fin15AnchoredAtom3592 Fin15AnchoredAtom3595 Fin15AnchoredAtom3596 Fin15AnchoredAtom3610
    Fin15AnchoredAtom3611 Fin15AnchoredAtom3617 Fin15AnchoredAtom3659 Fin15AnchoredAtom3660
    Fin15AnchoredAtom3666 Fin15AnchoredAtom3697 Fin15AnchoredAtom3863 Fin15AnchoredAtom3864
    Fin15AnchoredAtom3870 Fin15AnchoredAtom3901 Fin15AnchoredAtom3992 Fin15AnchoredAtom4193
    Fin15AnchoredAtom4194 Fin15AnchoredAtom4200 Fin15AnchoredAtom4231 Fin15AnchoredAtom4322
    Fin15AnchoredAtom4658 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31225 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom2138 chi ∧
      ¬Fin15AnchoredAtom2139 chi ∧
      ¬Fin15AnchoredAtom2140 chi ∧
      ¬Fin15AnchoredAtom2159 chi ∧
      ¬Fin15AnchoredAtom2160 chi ∧
      ¬Fin15AnchoredAtom2161 chi ∧
      ¬Fin15AnchoredAtom2219 chi ∧
      ¬Fin15AnchoredAtom2220 chi ∧
      ¬Fin15AnchoredAtom2221 chi ∧
      ¬Fin15AnchoredAtom2240 chi ∧
      ¬Fin15AnchoredAtom2241 chi ∧
      ¬Fin15AnchoredAtom2242 chi ∧
      ¬Fin15AnchoredAtom2289 chi ∧
      ¬Fin15AnchoredAtom2290 chi ∧
      ¬Fin15AnchoredAtom2291 chi ∧
      ¬Fin15AnchoredAtom2326 chi ∧
      ¬Fin15AnchoredAtom2384 chi ∧
      ¬Fin15AnchoredAtom2385 chi ∧
      ¬Fin15AnchoredAtom2386 chi ∧
      ¬Fin15AnchoredAtom2405 chi ∧
      ¬Fin15AnchoredAtom2406 chi ∧
      ¬Fin15AnchoredAtom2407 chi ∧
      ¬Fin15AnchoredAtom2454 chi ∧
      ¬Fin15AnchoredAtom2455 chi ∧
      ¬Fin15AnchoredAtom2456 chi ∧
      ¬Fin15AnchoredAtom2491 chi ∧
      ¬Fin15AnchoredAtom2658 chi ∧
      ¬Fin15AnchoredAtom2659 chi ∧
      ¬Fin15AnchoredAtom2660 chi ∧
      ¬Fin15AnchoredAtom2695 chi ∧
      ¬Fin15AnchoredAtom2786 chi ∧
      ¬Fin15AnchoredAtom3594 chi ∧
      ¬Fin15AnchoredAtom3595 chi ∧
      ¬Fin15AnchoredAtom3596 chi ∧
      ¬Fin15AnchoredAtom3615 chi ∧
      ¬Fin15AnchoredAtom3616 chi ∧
      ¬Fin15AnchoredAtom3617 chi ∧
      ¬Fin15AnchoredAtom3664 chi ∧
      ¬Fin15AnchoredAtom3665 chi ∧
      ¬Fin15AnchoredAtom3666 chi ∧
      ¬Fin15AnchoredAtom3701 chi ∧
      ¬Fin15AnchoredAtom3868 chi ∧
      ¬Fin15AnchoredAtom3869 chi ∧
      ¬Fin15AnchoredAtom3870 chi ∧
      ¬Fin15AnchoredAtom3905 chi ∧
      ¬Fin15AnchoredAtom3996 chi ∧
      ¬Fin15AnchoredAtom4198 chi ∧
      ¬Fin15AnchoredAtom4199 chi ∧
      ¬Fin15AnchoredAtom4200 chi ∧
      ¬Fin15AnchoredAtom4235 chi ∧
      ¬Fin15AnchoredAtom4326 chi ∧
      ¬Fin15AnchoredAtom4662 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 5, 7, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask28845
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2118 Fin15AnchoredAtom2123 Fin15AnchoredAtom2124
    Fin15AnchoredAtom2125 Fin15AnchoredAtom2138 Fin15AnchoredAtom2139 Fin15AnchoredAtom2140
    Fin15AnchoredAtom2159 Fin15AnchoredAtom2160 Fin15AnchoredAtom2161 Fin15AnchoredAtom2219
    Fin15AnchoredAtom2220 Fin15AnchoredAtom2221 Fin15AnchoredAtom2240 Fin15AnchoredAtom2241
    Fin15AnchoredAtom2242 Fin15AnchoredAtom2289 Fin15AnchoredAtom2290 Fin15AnchoredAtom2291
    Fin15AnchoredAtom2326 Fin15AnchoredAtom2384 Fin15AnchoredAtom2385 Fin15AnchoredAtom2386
    Fin15AnchoredAtom2405 Fin15AnchoredAtom2406 Fin15AnchoredAtom2407 Fin15AnchoredAtom2454
    Fin15AnchoredAtom2455 Fin15AnchoredAtom2456 Fin15AnchoredAtom2491 Fin15AnchoredAtom2658
    Fin15AnchoredAtom2659 Fin15AnchoredAtom2660 Fin15AnchoredAtom2695 Fin15AnchoredAtom2786
    Fin15AnchoredAtom3594 Fin15AnchoredAtom3595 Fin15AnchoredAtom3596 Fin15AnchoredAtom3615
    Fin15AnchoredAtom3616 Fin15AnchoredAtom3617 Fin15AnchoredAtom3664 Fin15AnchoredAtom3665
    Fin15AnchoredAtom3666 Fin15AnchoredAtom3701 Fin15AnchoredAtom3868 Fin15AnchoredAtom3869
    Fin15AnchoredAtom3870 Fin15AnchoredAtom3905 Fin15AnchoredAtom3996 Fin15AnchoredAtom4198
    Fin15AnchoredAtom4199 Fin15AnchoredAtom4200 Fin15AnchoredAtom4235 Fin15AnchoredAtom4326
    Fin15AnchoredAtom4662 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31226 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2119 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom2142 chi ∧
      ¬Fin15AnchoredAtom2144 chi ∧
      ¬Fin15AnchoredAtom2145 chi ∧
      ¬Fin15AnchoredAtom2153 chi ∧
      ¬Fin15AnchoredAtom2154 chi ∧
      ¬Fin15AnchoredAtom2159 chi ∧
      ¬Fin15AnchoredAtom2223 chi ∧
      ¬Fin15AnchoredAtom2225 chi ∧
      ¬Fin15AnchoredAtom2226 chi ∧
      ¬Fin15AnchoredAtom2234 chi ∧
      ¬Fin15AnchoredAtom2235 chi ∧
      ¬Fin15AnchoredAtom2240 chi ∧
      ¬Fin15AnchoredAtom2298 chi ∧
      ¬Fin15AnchoredAtom2299 chi ∧
      ¬Fin15AnchoredAtom2304 chi ∧
      ¬Fin15AnchoredAtom2320 chi ∧
      ¬Fin15AnchoredAtom2388 chi ∧
      ¬Fin15AnchoredAtom2390 chi ∧
      ¬Fin15AnchoredAtom2391 chi ∧
      ¬Fin15AnchoredAtom2399 chi ∧
      ¬Fin15AnchoredAtom2400 chi ∧
      ¬Fin15AnchoredAtom2405 chi ∧
      ¬Fin15AnchoredAtom2463 chi ∧
      ¬Fin15AnchoredAtom2464 chi ∧
      ¬Fin15AnchoredAtom2469 chi ∧
      ¬Fin15AnchoredAtom2485 chi ∧
      ¬Fin15AnchoredAtom2667 chi ∧
      ¬Fin15AnchoredAtom2668 chi ∧
      ¬Fin15AnchoredAtom2673 chi ∧
      ¬Fin15AnchoredAtom2689 chi ∧
      ¬Fin15AnchoredAtom2800 chi ∧
      ¬Fin15AnchoredAtom3598 chi ∧
      ¬Fin15AnchoredAtom3600 chi ∧
      ¬Fin15AnchoredAtom3601 chi ∧
      ¬Fin15AnchoredAtom3609 chi ∧
      ¬Fin15AnchoredAtom3610 chi ∧
      ¬Fin15AnchoredAtom3615 chi ∧
      ¬Fin15AnchoredAtom3673 chi ∧
      ¬Fin15AnchoredAtom3674 chi ∧
      ¬Fin15AnchoredAtom3679 chi ∧
      ¬Fin15AnchoredAtom3695 chi ∧
      ¬Fin15AnchoredAtom3877 chi ∧
      ¬Fin15AnchoredAtom3878 chi ∧
      ¬Fin15AnchoredAtom3883 chi ∧
      ¬Fin15AnchoredAtom3899 chi ∧
      ¬Fin15AnchoredAtom4010 chi ∧
      ¬Fin15AnchoredAtom4207 chi ∧
      ¬Fin15AnchoredAtom4208 chi ∧
      ¬Fin15AnchoredAtom4213 chi ∧
      ¬Fin15AnchoredAtom4229 chi ∧
      ¬Fin15AnchoredAtom4340 chi ∧
      ¬Fin15AnchoredAtom4676 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 5, 8, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13613
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2119 Fin15AnchoredAtom2121 Fin15AnchoredAtom2123
    Fin15AnchoredAtom2124 Fin15AnchoredAtom2142 Fin15AnchoredAtom2144 Fin15AnchoredAtom2145
    Fin15AnchoredAtom2153 Fin15AnchoredAtom2154 Fin15AnchoredAtom2159 Fin15AnchoredAtom2223
    Fin15AnchoredAtom2225 Fin15AnchoredAtom2226 Fin15AnchoredAtom2234 Fin15AnchoredAtom2235
    Fin15AnchoredAtom2240 Fin15AnchoredAtom2298 Fin15AnchoredAtom2299 Fin15AnchoredAtom2304
    Fin15AnchoredAtom2320 Fin15AnchoredAtom2388 Fin15AnchoredAtom2390 Fin15AnchoredAtom2391
    Fin15AnchoredAtom2399 Fin15AnchoredAtom2400 Fin15AnchoredAtom2405 Fin15AnchoredAtom2463
    Fin15AnchoredAtom2464 Fin15AnchoredAtom2469 Fin15AnchoredAtom2485 Fin15AnchoredAtom2667
    Fin15AnchoredAtom2668 Fin15AnchoredAtom2673 Fin15AnchoredAtom2689 Fin15AnchoredAtom2800
    Fin15AnchoredAtom3598 Fin15AnchoredAtom3600 Fin15AnchoredAtom3601 Fin15AnchoredAtom3609
    Fin15AnchoredAtom3610 Fin15AnchoredAtom3615 Fin15AnchoredAtom3673 Fin15AnchoredAtom3674
    Fin15AnchoredAtom3679 Fin15AnchoredAtom3695 Fin15AnchoredAtom3877 Fin15AnchoredAtom3878
    Fin15AnchoredAtom3883 Fin15AnchoredAtom3899 Fin15AnchoredAtom4010 Fin15AnchoredAtom4207
    Fin15AnchoredAtom4208 Fin15AnchoredAtom4213 Fin15AnchoredAtom4229 Fin15AnchoredAtom4340
    Fin15AnchoredAtom4676 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31227 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2122 chi ∧
      ¬Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom2147 chi ∧
      ¬Fin15AnchoredAtom2148 chi ∧
      ¬Fin15AnchoredAtom2149 chi ∧
      ¬Fin15AnchoredAtom2152 chi ∧
      ¬Fin15AnchoredAtom2153 chi ∧
      ¬Fin15AnchoredAtom2156 chi ∧
      ¬Fin15AnchoredAtom2228 chi ∧
      ¬Fin15AnchoredAtom2229 chi ∧
      ¬Fin15AnchoredAtom2230 chi ∧
      ¬Fin15AnchoredAtom2233 chi ∧
      ¬Fin15AnchoredAtom2234 chi ∧
      ¬Fin15AnchoredAtom2237 chi ∧
      ¬Fin15AnchoredAtom2307 chi ∧
      ¬Fin15AnchoredAtom2308 chi ∧
      ¬Fin15AnchoredAtom2311 chi ∧
      ¬Fin15AnchoredAtom2317 chi ∧
      ¬Fin15AnchoredAtom2393 chi ∧
      ¬Fin15AnchoredAtom2394 chi ∧
      ¬Fin15AnchoredAtom2395 chi ∧
      ¬Fin15AnchoredAtom2398 chi ∧
      ¬Fin15AnchoredAtom2399 chi ∧
      ¬Fin15AnchoredAtom2402 chi ∧
      ¬Fin15AnchoredAtom2472 chi ∧
      ¬Fin15AnchoredAtom2473 chi ∧
      ¬Fin15AnchoredAtom2476 chi ∧
      ¬Fin15AnchoredAtom2482 chi ∧
      ¬Fin15AnchoredAtom2676 chi ∧
      ¬Fin15AnchoredAtom2677 chi ∧
      ¬Fin15AnchoredAtom2680 chi ∧
      ¬Fin15AnchoredAtom2686 chi ∧
      ¬Fin15AnchoredAtom2807 chi ∧
      ¬Fin15AnchoredAtom3603 chi ∧
      ¬Fin15AnchoredAtom3604 chi ∧
      ¬Fin15AnchoredAtom3605 chi ∧
      ¬Fin15AnchoredAtom3608 chi ∧
      ¬Fin15AnchoredAtom3609 chi ∧
      ¬Fin15AnchoredAtom3612 chi ∧
      ¬Fin15AnchoredAtom3682 chi ∧
      ¬Fin15AnchoredAtom3683 chi ∧
      ¬Fin15AnchoredAtom3686 chi ∧
      ¬Fin15AnchoredAtom3692 chi ∧
      ¬Fin15AnchoredAtom3886 chi ∧
      ¬Fin15AnchoredAtom3887 chi ∧
      ¬Fin15AnchoredAtom3890 chi ∧
      ¬Fin15AnchoredAtom3896 chi ∧
      ¬Fin15AnchoredAtom4017 chi ∧
      ¬Fin15AnchoredAtom4216 chi ∧
      ¬Fin15AnchoredAtom4217 chi ∧
      ¬Fin15AnchoredAtom4220 chi ∧
      ¬Fin15AnchoredAtom4226 chi ∧
      ¬Fin15AnchoredAtom4347 chi ∧
      ¬Fin15AnchoredAtom4683 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 5, 9, 10, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask07725
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2120 Fin15AnchoredAtom2121 Fin15AnchoredAtom2122
    Fin15AnchoredAtom2123 Fin15AnchoredAtom2147 Fin15AnchoredAtom2148 Fin15AnchoredAtom2149
    Fin15AnchoredAtom2152 Fin15AnchoredAtom2153 Fin15AnchoredAtom2156 Fin15AnchoredAtom2228
    Fin15AnchoredAtom2229 Fin15AnchoredAtom2230 Fin15AnchoredAtom2233 Fin15AnchoredAtom2234
    Fin15AnchoredAtom2237 Fin15AnchoredAtom2307 Fin15AnchoredAtom2308 Fin15AnchoredAtom2311
    Fin15AnchoredAtom2317 Fin15AnchoredAtom2393 Fin15AnchoredAtom2394 Fin15AnchoredAtom2395
    Fin15AnchoredAtom2398 Fin15AnchoredAtom2399 Fin15AnchoredAtom2402 Fin15AnchoredAtom2472
    Fin15AnchoredAtom2473 Fin15AnchoredAtom2476 Fin15AnchoredAtom2482 Fin15AnchoredAtom2676
    Fin15AnchoredAtom2677 Fin15AnchoredAtom2680 Fin15AnchoredAtom2686 Fin15AnchoredAtom2807
    Fin15AnchoredAtom3603 Fin15AnchoredAtom3604 Fin15AnchoredAtom3605 Fin15AnchoredAtom3608
    Fin15AnchoredAtom3609 Fin15AnchoredAtom3612 Fin15AnchoredAtom3682 Fin15AnchoredAtom3683
    Fin15AnchoredAtom3686 Fin15AnchoredAtom3692 Fin15AnchoredAtom3886 Fin15AnchoredAtom3887
    Fin15AnchoredAtom3890 Fin15AnchoredAtom3896 Fin15AnchoredAtom4017 Fin15AnchoredAtom4216
    Fin15AnchoredAtom4217 Fin15AnchoredAtom4220 Fin15AnchoredAtom4226 Fin15AnchoredAtom4347
    Fin15AnchoredAtom4683 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31228 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2122 chi ∧
      ¬Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom2147 chi ∧
      ¬Fin15AnchoredAtom2148 chi ∧
      ¬Fin15AnchoredAtom2150 chi ∧
      ¬Fin15AnchoredAtom2152 chi ∧
      ¬Fin15AnchoredAtom2154 chi ∧
      ¬Fin15AnchoredAtom2157 chi ∧
      ¬Fin15AnchoredAtom2228 chi ∧
      ¬Fin15AnchoredAtom2229 chi ∧
      ¬Fin15AnchoredAtom2231 chi ∧
      ¬Fin15AnchoredAtom2233 chi ∧
      ¬Fin15AnchoredAtom2235 chi ∧
      ¬Fin15AnchoredAtom2238 chi ∧
      ¬Fin15AnchoredAtom2307 chi ∧
      ¬Fin15AnchoredAtom2309 chi ∧
      ¬Fin15AnchoredAtom2312 chi ∧
      ¬Fin15AnchoredAtom2318 chi ∧
      ¬Fin15AnchoredAtom2393 chi ∧
      ¬Fin15AnchoredAtom2394 chi ∧
      ¬Fin15AnchoredAtom2396 chi ∧
      ¬Fin15AnchoredAtom2398 chi ∧
      ¬Fin15AnchoredAtom2400 chi ∧
      ¬Fin15AnchoredAtom2403 chi ∧
      ¬Fin15AnchoredAtom2472 chi ∧
      ¬Fin15AnchoredAtom2474 chi ∧
      ¬Fin15AnchoredAtom2477 chi ∧
      ¬Fin15AnchoredAtom2483 chi ∧
      ¬Fin15AnchoredAtom2676 chi ∧
      ¬Fin15AnchoredAtom2678 chi ∧
      ¬Fin15AnchoredAtom2681 chi ∧
      ¬Fin15AnchoredAtom2687 chi ∧
      ¬Fin15AnchoredAtom2808 chi ∧
      ¬Fin15AnchoredAtom3603 chi ∧
      ¬Fin15AnchoredAtom3604 chi ∧
      ¬Fin15AnchoredAtom3606 chi ∧
      ¬Fin15AnchoredAtom3608 chi ∧
      ¬Fin15AnchoredAtom3610 chi ∧
      ¬Fin15AnchoredAtom3613 chi ∧
      ¬Fin15AnchoredAtom3682 chi ∧
      ¬Fin15AnchoredAtom3684 chi ∧
      ¬Fin15AnchoredAtom3687 chi ∧
      ¬Fin15AnchoredAtom3693 chi ∧
      ¬Fin15AnchoredAtom3886 chi ∧
      ¬Fin15AnchoredAtom3888 chi ∧
      ¬Fin15AnchoredAtom3891 chi ∧
      ¬Fin15AnchoredAtom3897 chi ∧
      ¬Fin15AnchoredAtom4018 chi ∧
      ¬Fin15AnchoredAtom4216 chi ∧
      ¬Fin15AnchoredAtom4218 chi ∧
      ¬Fin15AnchoredAtom4221 chi ∧
      ¬Fin15AnchoredAtom4227 chi ∧
      ¬Fin15AnchoredAtom4348 chi ∧
      ¬Fin15AnchoredAtom4684 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 5, 9, 10, 11, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask11821
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2120 Fin15AnchoredAtom2121 Fin15AnchoredAtom2122
    Fin15AnchoredAtom2124 Fin15AnchoredAtom2147 Fin15AnchoredAtom2148 Fin15AnchoredAtom2150
    Fin15AnchoredAtom2152 Fin15AnchoredAtom2154 Fin15AnchoredAtom2157 Fin15AnchoredAtom2228
    Fin15AnchoredAtom2229 Fin15AnchoredAtom2231 Fin15AnchoredAtom2233 Fin15AnchoredAtom2235
    Fin15AnchoredAtom2238 Fin15AnchoredAtom2307 Fin15AnchoredAtom2309 Fin15AnchoredAtom2312
    Fin15AnchoredAtom2318 Fin15AnchoredAtom2393 Fin15AnchoredAtom2394 Fin15AnchoredAtom2396
    Fin15AnchoredAtom2398 Fin15AnchoredAtom2400 Fin15AnchoredAtom2403 Fin15AnchoredAtom2472
    Fin15AnchoredAtom2474 Fin15AnchoredAtom2477 Fin15AnchoredAtom2483 Fin15AnchoredAtom2676
    Fin15AnchoredAtom2678 Fin15AnchoredAtom2681 Fin15AnchoredAtom2687 Fin15AnchoredAtom2808
    Fin15AnchoredAtom3603 Fin15AnchoredAtom3604 Fin15AnchoredAtom3606 Fin15AnchoredAtom3608
    Fin15AnchoredAtom3610 Fin15AnchoredAtom3613 Fin15AnchoredAtom3682 Fin15AnchoredAtom3684
    Fin15AnchoredAtom3687 Fin15AnchoredAtom3693 Fin15AnchoredAtom3886 Fin15AnchoredAtom3888
    Fin15AnchoredAtom3891 Fin15AnchoredAtom3897 Fin15AnchoredAtom4018 Fin15AnchoredAtom4216
    Fin15AnchoredAtom4218 Fin15AnchoredAtom4221 Fin15AnchoredAtom4227 Fin15AnchoredAtom4348
    Fin15AnchoredAtom4684 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31229 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom2147 chi ∧
      ¬Fin15AnchoredAtom2149 chi ∧
      ¬Fin15AnchoredAtom2150 chi ∧
      ¬Fin15AnchoredAtom2153 chi ∧
      ¬Fin15AnchoredAtom2154 chi ∧
      ¬Fin15AnchoredAtom2159 chi ∧
      ¬Fin15AnchoredAtom2228 chi ∧
      ¬Fin15AnchoredAtom2230 chi ∧
      ¬Fin15AnchoredAtom2231 chi ∧
      ¬Fin15AnchoredAtom2234 chi ∧
      ¬Fin15AnchoredAtom2235 chi ∧
      ¬Fin15AnchoredAtom2240 chi ∧
      ¬Fin15AnchoredAtom2308 chi ∧
      ¬Fin15AnchoredAtom2309 chi ∧
      ¬Fin15AnchoredAtom2314 chi ∧
      ¬Fin15AnchoredAtom2320 chi ∧
      ¬Fin15AnchoredAtom2393 chi ∧
      ¬Fin15AnchoredAtom2395 chi ∧
      ¬Fin15AnchoredAtom2396 chi ∧
      ¬Fin15AnchoredAtom2399 chi ∧
      ¬Fin15AnchoredAtom2400 chi ∧
      ¬Fin15AnchoredAtom2405 chi ∧
      ¬Fin15AnchoredAtom2473 chi ∧
      ¬Fin15AnchoredAtom2474 chi ∧
      ¬Fin15AnchoredAtom2479 chi ∧
      ¬Fin15AnchoredAtom2485 chi ∧
      ¬Fin15AnchoredAtom2677 chi ∧
      ¬Fin15AnchoredAtom2678 chi ∧
      ¬Fin15AnchoredAtom2683 chi ∧
      ¬Fin15AnchoredAtom2689 chi ∧
      ¬Fin15AnchoredAtom2810 chi ∧
      ¬Fin15AnchoredAtom3603 chi ∧
      ¬Fin15AnchoredAtom3605 chi ∧
      ¬Fin15AnchoredAtom3606 chi ∧
      ¬Fin15AnchoredAtom3609 chi ∧
      ¬Fin15AnchoredAtom3610 chi ∧
      ¬Fin15AnchoredAtom3615 chi ∧
      ¬Fin15AnchoredAtom3683 chi ∧
      ¬Fin15AnchoredAtom3684 chi ∧
      ¬Fin15AnchoredAtom3689 chi ∧
      ¬Fin15AnchoredAtom3695 chi ∧
      ¬Fin15AnchoredAtom3887 chi ∧
      ¬Fin15AnchoredAtom3888 chi ∧
      ¬Fin15AnchoredAtom3893 chi ∧
      ¬Fin15AnchoredAtom3899 chi ∧
      ¬Fin15AnchoredAtom4020 chi ∧
      ¬Fin15AnchoredAtom4217 chi ∧
      ¬Fin15AnchoredAtom4218 chi ∧
      ¬Fin15AnchoredAtom4223 chi ∧
      ¬Fin15AnchoredAtom4229 chi ∧
      ¬Fin15AnchoredAtom4350 chi ∧
      ¬Fin15AnchoredAtom4686 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 5, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13869
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2120 Fin15AnchoredAtom2121 Fin15AnchoredAtom2123
    Fin15AnchoredAtom2124 Fin15AnchoredAtom2147 Fin15AnchoredAtom2149 Fin15AnchoredAtom2150
    Fin15AnchoredAtom2153 Fin15AnchoredAtom2154 Fin15AnchoredAtom2159 Fin15AnchoredAtom2228
    Fin15AnchoredAtom2230 Fin15AnchoredAtom2231 Fin15AnchoredAtom2234 Fin15AnchoredAtom2235
    Fin15AnchoredAtom2240 Fin15AnchoredAtom2308 Fin15AnchoredAtom2309 Fin15AnchoredAtom2314
    Fin15AnchoredAtom2320 Fin15AnchoredAtom2393 Fin15AnchoredAtom2395 Fin15AnchoredAtom2396
    Fin15AnchoredAtom2399 Fin15AnchoredAtom2400 Fin15AnchoredAtom2405 Fin15AnchoredAtom2473
    Fin15AnchoredAtom2474 Fin15AnchoredAtom2479 Fin15AnchoredAtom2485 Fin15AnchoredAtom2677
    Fin15AnchoredAtom2678 Fin15AnchoredAtom2683 Fin15AnchoredAtom2689 Fin15AnchoredAtom2810
    Fin15AnchoredAtom3603 Fin15AnchoredAtom3605 Fin15AnchoredAtom3606 Fin15AnchoredAtom3609
    Fin15AnchoredAtom3610 Fin15AnchoredAtom3615 Fin15AnchoredAtom3683 Fin15AnchoredAtom3684
    Fin15AnchoredAtom3689 Fin15AnchoredAtom3695 Fin15AnchoredAtom3887 Fin15AnchoredAtom3888
    Fin15AnchoredAtom3893 Fin15AnchoredAtom3899 Fin15AnchoredAtom4020 Fin15AnchoredAtom4217
    Fin15AnchoredAtom4218 Fin15AnchoredAtom4223 Fin15AnchoredAtom4229 Fin15AnchoredAtom4350
    Fin15AnchoredAtom4686 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31230 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom2147 chi ∧
      ¬Fin15AnchoredAtom2149 chi ∧
      ¬Fin15AnchoredAtom2151 chi ∧
      ¬Fin15AnchoredAtom2153 chi ∧
      ¬Fin15AnchoredAtom2155 chi ∧
      ¬Fin15AnchoredAtom2160 chi ∧
      ¬Fin15AnchoredAtom2228 chi ∧
      ¬Fin15AnchoredAtom2230 chi ∧
      ¬Fin15AnchoredAtom2232 chi ∧
      ¬Fin15AnchoredAtom2234 chi ∧
      ¬Fin15AnchoredAtom2236 chi ∧
      ¬Fin15AnchoredAtom2241 chi ∧
      ¬Fin15AnchoredAtom2308 chi ∧
      ¬Fin15AnchoredAtom2310 chi ∧
      ¬Fin15AnchoredAtom2315 chi ∧
      ¬Fin15AnchoredAtom2321 chi ∧
      ¬Fin15AnchoredAtom2393 chi ∧
      ¬Fin15AnchoredAtom2395 chi ∧
      ¬Fin15AnchoredAtom2397 chi ∧
      ¬Fin15AnchoredAtom2399 chi ∧
      ¬Fin15AnchoredAtom2401 chi ∧
      ¬Fin15AnchoredAtom2406 chi ∧
      ¬Fin15AnchoredAtom2473 chi ∧
      ¬Fin15AnchoredAtom2475 chi ∧
      ¬Fin15AnchoredAtom2480 chi ∧
      ¬Fin15AnchoredAtom2486 chi ∧
      ¬Fin15AnchoredAtom2677 chi ∧
      ¬Fin15AnchoredAtom2679 chi ∧
      ¬Fin15AnchoredAtom2684 chi ∧
      ¬Fin15AnchoredAtom2690 chi ∧
      ¬Fin15AnchoredAtom2811 chi ∧
      ¬Fin15AnchoredAtom3603 chi ∧
      ¬Fin15AnchoredAtom3605 chi ∧
      ¬Fin15AnchoredAtom3607 chi ∧
      ¬Fin15AnchoredAtom3609 chi ∧
      ¬Fin15AnchoredAtom3611 chi ∧
      ¬Fin15AnchoredAtom3616 chi ∧
      ¬Fin15AnchoredAtom3683 chi ∧
      ¬Fin15AnchoredAtom3685 chi ∧
      ¬Fin15AnchoredAtom3690 chi ∧
      ¬Fin15AnchoredAtom3696 chi ∧
      ¬Fin15AnchoredAtom3887 chi ∧
      ¬Fin15AnchoredAtom3889 chi ∧
      ¬Fin15AnchoredAtom3894 chi ∧
      ¬Fin15AnchoredAtom3900 chi ∧
      ¬Fin15AnchoredAtom4021 chi ∧
      ¬Fin15AnchoredAtom4217 chi ∧
      ¬Fin15AnchoredAtom4219 chi ∧
      ¬Fin15AnchoredAtom4224 chi ∧
      ¬Fin15AnchoredAtom4230 chi ∧
      ¬Fin15AnchoredAtom4351 chi ∧
      ¬Fin15AnchoredAtom4687 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 5, 9, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22061
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2120 Fin15AnchoredAtom2121 Fin15AnchoredAtom2123
    Fin15AnchoredAtom2125 Fin15AnchoredAtom2147 Fin15AnchoredAtom2149 Fin15AnchoredAtom2151
    Fin15AnchoredAtom2153 Fin15AnchoredAtom2155 Fin15AnchoredAtom2160 Fin15AnchoredAtom2228
    Fin15AnchoredAtom2230 Fin15AnchoredAtom2232 Fin15AnchoredAtom2234 Fin15AnchoredAtom2236
    Fin15AnchoredAtom2241 Fin15AnchoredAtom2308 Fin15AnchoredAtom2310 Fin15AnchoredAtom2315
    Fin15AnchoredAtom2321 Fin15AnchoredAtom2393 Fin15AnchoredAtom2395 Fin15AnchoredAtom2397
    Fin15AnchoredAtom2399 Fin15AnchoredAtom2401 Fin15AnchoredAtom2406 Fin15AnchoredAtom2473
    Fin15AnchoredAtom2475 Fin15AnchoredAtom2480 Fin15AnchoredAtom2486 Fin15AnchoredAtom2677
    Fin15AnchoredAtom2679 Fin15AnchoredAtom2684 Fin15AnchoredAtom2690 Fin15AnchoredAtom2811
    Fin15AnchoredAtom3603 Fin15AnchoredAtom3605 Fin15AnchoredAtom3607 Fin15AnchoredAtom3609
    Fin15AnchoredAtom3611 Fin15AnchoredAtom3616 Fin15AnchoredAtom3683 Fin15AnchoredAtom3685
    Fin15AnchoredAtom3690 Fin15AnchoredAtom3696 Fin15AnchoredAtom3887 Fin15AnchoredAtom3889
    Fin15AnchoredAtom3894 Fin15AnchoredAtom3900 Fin15AnchoredAtom4021 Fin15AnchoredAtom4217
    Fin15AnchoredAtom4219 Fin15AnchoredAtom4224 Fin15AnchoredAtom4230 Fin15AnchoredAtom4351
    Fin15AnchoredAtom4687 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31231 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom2147 chi ∧
      ¬Fin15AnchoredAtom2150 chi ∧
      ¬Fin15AnchoredAtom2151 chi ∧
      ¬Fin15AnchoredAtom2154 chi ∧
      ¬Fin15AnchoredAtom2155 chi ∧
      ¬Fin15AnchoredAtom2161 chi ∧
      ¬Fin15AnchoredAtom2228 chi ∧
      ¬Fin15AnchoredAtom2231 chi ∧
      ¬Fin15AnchoredAtom2232 chi ∧
      ¬Fin15AnchoredAtom2235 chi ∧
      ¬Fin15AnchoredAtom2236 chi ∧
      ¬Fin15AnchoredAtom2242 chi ∧
      ¬Fin15AnchoredAtom2309 chi ∧
      ¬Fin15AnchoredAtom2310 chi ∧
      ¬Fin15AnchoredAtom2316 chi ∧
      ¬Fin15AnchoredAtom2322 chi ∧
      ¬Fin15AnchoredAtom2393 chi ∧
      ¬Fin15AnchoredAtom2396 chi ∧
      ¬Fin15AnchoredAtom2397 chi ∧
      ¬Fin15AnchoredAtom2400 chi ∧
      ¬Fin15AnchoredAtom2401 chi ∧
      ¬Fin15AnchoredAtom2407 chi ∧
      ¬Fin15AnchoredAtom2474 chi ∧
      ¬Fin15AnchoredAtom2475 chi ∧
      ¬Fin15AnchoredAtom2481 chi ∧
      ¬Fin15AnchoredAtom2487 chi ∧
      ¬Fin15AnchoredAtom2678 chi ∧
      ¬Fin15AnchoredAtom2679 chi ∧
      ¬Fin15AnchoredAtom2685 chi ∧
      ¬Fin15AnchoredAtom2691 chi ∧
      ¬Fin15AnchoredAtom2812 chi ∧
      ¬Fin15AnchoredAtom3603 chi ∧
      ¬Fin15AnchoredAtom3606 chi ∧
      ¬Fin15AnchoredAtom3607 chi ∧
      ¬Fin15AnchoredAtom3610 chi ∧
      ¬Fin15AnchoredAtom3611 chi ∧
      ¬Fin15AnchoredAtom3617 chi ∧
      ¬Fin15AnchoredAtom3684 chi ∧
      ¬Fin15AnchoredAtom3685 chi ∧
      ¬Fin15AnchoredAtom3691 chi ∧
      ¬Fin15AnchoredAtom3697 chi ∧
      ¬Fin15AnchoredAtom3888 chi ∧
      ¬Fin15AnchoredAtom3889 chi ∧
      ¬Fin15AnchoredAtom3895 chi ∧
      ¬Fin15AnchoredAtom3901 chi ∧
      ¬Fin15AnchoredAtom4022 chi ∧
      ¬Fin15AnchoredAtom4218 chi ∧
      ¬Fin15AnchoredAtom4219 chi ∧
      ¬Fin15AnchoredAtom4225 chi ∧
      ¬Fin15AnchoredAtom4231 chi ∧
      ¬Fin15AnchoredAtom4352 chi ∧
      ¬Fin15AnchoredAtom4688 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 5, 9, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26157
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2120 Fin15AnchoredAtom2121 Fin15AnchoredAtom2124
    Fin15AnchoredAtom2125 Fin15AnchoredAtom2147 Fin15AnchoredAtom2150 Fin15AnchoredAtom2151
    Fin15AnchoredAtom2154 Fin15AnchoredAtom2155 Fin15AnchoredAtom2161 Fin15AnchoredAtom2228
    Fin15AnchoredAtom2231 Fin15AnchoredAtom2232 Fin15AnchoredAtom2235 Fin15AnchoredAtom2236
    Fin15AnchoredAtom2242 Fin15AnchoredAtom2309 Fin15AnchoredAtom2310 Fin15AnchoredAtom2316
    Fin15AnchoredAtom2322 Fin15AnchoredAtom2393 Fin15AnchoredAtom2396 Fin15AnchoredAtom2397
    Fin15AnchoredAtom2400 Fin15AnchoredAtom2401 Fin15AnchoredAtom2407 Fin15AnchoredAtom2474
    Fin15AnchoredAtom2475 Fin15AnchoredAtom2481 Fin15AnchoredAtom2487 Fin15AnchoredAtom2678
    Fin15AnchoredAtom2679 Fin15AnchoredAtom2685 Fin15AnchoredAtom2691 Fin15AnchoredAtom2812
    Fin15AnchoredAtom3603 Fin15AnchoredAtom3606 Fin15AnchoredAtom3607 Fin15AnchoredAtom3610
    Fin15AnchoredAtom3611 Fin15AnchoredAtom3617 Fin15AnchoredAtom3684 Fin15AnchoredAtom3685
    Fin15AnchoredAtom3691 Fin15AnchoredAtom3697 Fin15AnchoredAtom3888 Fin15AnchoredAtom3889
    Fin15AnchoredAtom3895 Fin15AnchoredAtom3901 Fin15AnchoredAtom4022 Fin15AnchoredAtom4218
    Fin15AnchoredAtom4219 Fin15AnchoredAtom4225 Fin15AnchoredAtom4231 Fin15AnchoredAtom4352
    Fin15AnchoredAtom4688 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

end ErdosSzekeres

end
