module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 239. -/

theorem fin15Anchored_clause30592 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom1935 chi ∧
      ¬Fin15AnchoredAtom1940 chi ∧
      ¬Fin15AnchoredAtom2014 chi ∧
      ¬Fin15AnchoredAtom2016 chi ∧
      ¬Fin15AnchoredAtom2021 chi ∧
      ¬Fin15AnchoredAtom2101 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom2153 chi ∧
      ¬Fin15AnchoredAtom2155 chi ∧
      ¬Fin15AnchoredAtom2160 chi ∧
      ¬Fin15AnchoredAtom2234 chi ∧
      ¬Fin15AnchoredAtom2236 chi ∧
      ¬Fin15AnchoredAtom2241 chi ∧
      ¬Fin15AnchoredAtom2321 chi ∧
      ¬Fin15AnchoredAtom2399 chi ∧
      ¬Fin15AnchoredAtom2401 chi ∧
      ¬Fin15AnchoredAtom2406 chi ∧
      ¬Fin15AnchoredAtom2486 chi ∧
      ¬Fin15AnchoredAtom2690 chi ∧
      ¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom2868 chi ∧
      ¬Fin15AnchoredAtom2870 chi ∧
      ¬Fin15AnchoredAtom2875 chi ∧
      ¬Fin15AnchoredAtom2949 chi ∧
      ¬Fin15AnchoredAtom2951 chi ∧
      ¬Fin15AnchoredAtom2956 chi ∧
      ¬Fin15AnchoredAtom3036 chi ∧
      ¬Fin15AnchoredAtom3114 chi ∧
      ¬Fin15AnchoredAtom3116 chi ∧
      ¬Fin15AnchoredAtom3121 chi ∧
      ¬Fin15AnchoredAtom3201 chi ∧
      ¬Fin15AnchoredAtom3405 chi ∧
      ¬Fin15AnchoredAtom3609 chi ∧
      ¬Fin15AnchoredAtom3611 chi ∧
      ¬Fin15AnchoredAtom3616 chi ∧
      ¬Fin15AnchoredAtom3696 chi ∧
      ¬Fin15AnchoredAtom3900 chi ∧
      ¬Fin15AnchoredAtom4230 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 5, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21551
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1822 Fin15AnchoredAtom1827 Fin15AnchoredAtom1829
    Fin15AnchoredAtom1831 Fin15AnchoredAtom1846 Fin15AnchoredAtom1848 Fin15AnchoredAtom1850
    Fin15AnchoredAtom1878 Fin15AnchoredAtom1880 Fin15AnchoredAtom1885 Fin15AnchoredAtom1901
    Fin15AnchoredAtom1903 Fin15AnchoredAtom1905 Fin15AnchoredAtom1933 Fin15AnchoredAtom1935
    Fin15AnchoredAtom1940 Fin15AnchoredAtom2014 Fin15AnchoredAtom2016 Fin15AnchoredAtom2021
    Fin15AnchoredAtom2101 Fin15AnchoredAtom2121 Fin15AnchoredAtom2123 Fin15AnchoredAtom2125
    Fin15AnchoredAtom2153 Fin15AnchoredAtom2155 Fin15AnchoredAtom2160 Fin15AnchoredAtom2234
    Fin15AnchoredAtom2236 Fin15AnchoredAtom2241 Fin15AnchoredAtom2321 Fin15AnchoredAtom2399
    Fin15AnchoredAtom2401 Fin15AnchoredAtom2406 Fin15AnchoredAtom2486 Fin15AnchoredAtom2690
    Fin15AnchoredAtom2836 Fin15AnchoredAtom2838 Fin15AnchoredAtom2840 Fin15AnchoredAtom2868
    Fin15AnchoredAtom2870 Fin15AnchoredAtom2875 Fin15AnchoredAtom2949 Fin15AnchoredAtom2951
    Fin15AnchoredAtom2956 Fin15AnchoredAtom3036 Fin15AnchoredAtom3114 Fin15AnchoredAtom3116
    Fin15AnchoredAtom3121 Fin15AnchoredAtom3201 Fin15AnchoredAtom3405 Fin15AnchoredAtom3609
    Fin15AnchoredAtom3611 Fin15AnchoredAtom3616 Fin15AnchoredAtom3696 Fin15AnchoredAtom3900
    Fin15AnchoredAtom4230 at hbad
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

theorem fin15Anchored_clause30593 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom1886 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom1935 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
      ¬Fin15AnchoredAtom2015 chi ∧
      ¬Fin15AnchoredAtom2016 chi ∧
      ¬Fin15AnchoredAtom2022 chi ∧
      ¬Fin15AnchoredAtom2102 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom2154 chi ∧
      ¬Fin15AnchoredAtom2155 chi ∧
      ¬Fin15AnchoredAtom2161 chi ∧
      ¬Fin15AnchoredAtom2235 chi ∧
      ¬Fin15AnchoredAtom2236 chi ∧
      ¬Fin15AnchoredAtom2242 chi ∧
      ¬Fin15AnchoredAtom2322 chi ∧
      ¬Fin15AnchoredAtom2400 chi ∧
      ¬Fin15AnchoredAtom2401 chi ∧
      ¬Fin15AnchoredAtom2407 chi ∧
      ¬Fin15AnchoredAtom2487 chi ∧
      ¬Fin15AnchoredAtom2691 chi ∧
      ¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom2869 chi ∧
      ¬Fin15AnchoredAtom2870 chi ∧
      ¬Fin15AnchoredAtom2876 chi ∧
      ¬Fin15AnchoredAtom2950 chi ∧
      ¬Fin15AnchoredAtom2951 chi ∧
      ¬Fin15AnchoredAtom2957 chi ∧
      ¬Fin15AnchoredAtom3037 chi ∧
      ¬Fin15AnchoredAtom3115 chi ∧
      ¬Fin15AnchoredAtom3116 chi ∧
      ¬Fin15AnchoredAtom3122 chi ∧
      ¬Fin15AnchoredAtom3202 chi ∧
      ¬Fin15AnchoredAtom3406 chi ∧
      ¬Fin15AnchoredAtom3610 chi ∧
      ¬Fin15AnchoredAtom3611 chi ∧
      ¬Fin15AnchoredAtom3617 chi ∧
      ¬Fin15AnchoredAtom3697 chi ∧
      ¬Fin15AnchoredAtom3901 chi ∧
      ¬Fin15AnchoredAtom4231 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 5, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25647
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1822 Fin15AnchoredAtom1827 Fin15AnchoredAtom1830
    Fin15AnchoredAtom1831 Fin15AnchoredAtom1846 Fin15AnchoredAtom1849 Fin15AnchoredAtom1850
    Fin15AnchoredAtom1879 Fin15AnchoredAtom1880 Fin15AnchoredAtom1886 Fin15AnchoredAtom1901
    Fin15AnchoredAtom1904 Fin15AnchoredAtom1905 Fin15AnchoredAtom1934 Fin15AnchoredAtom1935
    Fin15AnchoredAtom1941 Fin15AnchoredAtom2015 Fin15AnchoredAtom2016 Fin15AnchoredAtom2022
    Fin15AnchoredAtom2102 Fin15AnchoredAtom2121 Fin15AnchoredAtom2124 Fin15AnchoredAtom2125
    Fin15AnchoredAtom2154 Fin15AnchoredAtom2155 Fin15AnchoredAtom2161 Fin15AnchoredAtom2235
    Fin15AnchoredAtom2236 Fin15AnchoredAtom2242 Fin15AnchoredAtom2322 Fin15AnchoredAtom2400
    Fin15AnchoredAtom2401 Fin15AnchoredAtom2407 Fin15AnchoredAtom2487 Fin15AnchoredAtom2691
    Fin15AnchoredAtom2836 Fin15AnchoredAtom2839 Fin15AnchoredAtom2840 Fin15AnchoredAtom2869
    Fin15AnchoredAtom2870 Fin15AnchoredAtom2876 Fin15AnchoredAtom2950 Fin15AnchoredAtom2951
    Fin15AnchoredAtom2957 Fin15AnchoredAtom3037 Fin15AnchoredAtom3115 Fin15AnchoredAtom3116
    Fin15AnchoredAtom3122 Fin15AnchoredAtom3202 Fin15AnchoredAtom3406 Fin15AnchoredAtom3610
    Fin15AnchoredAtom3611 Fin15AnchoredAtom3617 Fin15AnchoredAtom3697 Fin15AnchoredAtom3901
    Fin15AnchoredAtom4231 at hbad
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

theorem fin15Anchored_clause30594 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom1886 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1939 chi ∧
      ¬Fin15AnchoredAtom1940 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
      ¬Fin15AnchoredAtom2020 chi ∧
      ¬Fin15AnchoredAtom2021 chi ∧
      ¬Fin15AnchoredAtom2022 chi ∧
      ¬Fin15AnchoredAtom2106 chi ∧
      ¬Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom2159 chi ∧
      ¬Fin15AnchoredAtom2160 chi ∧
      ¬Fin15AnchoredAtom2161 chi ∧
      ¬Fin15AnchoredAtom2240 chi ∧
      ¬Fin15AnchoredAtom2241 chi ∧
      ¬Fin15AnchoredAtom2242 chi ∧
      ¬Fin15AnchoredAtom2326 chi ∧
      ¬Fin15AnchoredAtom2405 chi ∧
      ¬Fin15AnchoredAtom2406 chi ∧
      ¬Fin15AnchoredAtom2407 chi ∧
      ¬Fin15AnchoredAtom2491 chi ∧
      ¬Fin15AnchoredAtom2695 chi ∧
      ¬Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom2874 chi ∧
      ¬Fin15AnchoredAtom2875 chi ∧
      ¬Fin15AnchoredAtom2876 chi ∧
      ¬Fin15AnchoredAtom2955 chi ∧
      ¬Fin15AnchoredAtom2956 chi ∧
      ¬Fin15AnchoredAtom2957 chi ∧
      ¬Fin15AnchoredAtom3041 chi ∧
      ¬Fin15AnchoredAtom3120 chi ∧
      ¬Fin15AnchoredAtom3121 chi ∧
      ¬Fin15AnchoredAtom3122 chi ∧
      ¬Fin15AnchoredAtom3206 chi ∧
      ¬Fin15AnchoredAtom3410 chi ∧
      ¬Fin15AnchoredAtom3615 chi ∧
      ¬Fin15AnchoredAtom3616 chi ∧
      ¬Fin15AnchoredAtom3617 chi ∧
      ¬Fin15AnchoredAtom3701 chi ∧
      ¬Fin15AnchoredAtom3905 chi ∧
      ¬Fin15AnchoredAtom4235 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 5, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask28719
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1822 Fin15AnchoredAtom1829 Fin15AnchoredAtom1830
    Fin15AnchoredAtom1831 Fin15AnchoredAtom1848 Fin15AnchoredAtom1849 Fin15AnchoredAtom1850
    Fin15AnchoredAtom1884 Fin15AnchoredAtom1885 Fin15AnchoredAtom1886 Fin15AnchoredAtom1903
    Fin15AnchoredAtom1904 Fin15AnchoredAtom1905 Fin15AnchoredAtom1939 Fin15AnchoredAtom1940
    Fin15AnchoredAtom1941 Fin15AnchoredAtom2020 Fin15AnchoredAtom2021 Fin15AnchoredAtom2022
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2123 Fin15AnchoredAtom2124 Fin15AnchoredAtom2125
    Fin15AnchoredAtom2159 Fin15AnchoredAtom2160 Fin15AnchoredAtom2161 Fin15AnchoredAtom2240
    Fin15AnchoredAtom2241 Fin15AnchoredAtom2242 Fin15AnchoredAtom2326 Fin15AnchoredAtom2405
    Fin15AnchoredAtom2406 Fin15AnchoredAtom2407 Fin15AnchoredAtom2491 Fin15AnchoredAtom2695
    Fin15AnchoredAtom2838 Fin15AnchoredAtom2839 Fin15AnchoredAtom2840 Fin15AnchoredAtom2874
    Fin15AnchoredAtom2875 Fin15AnchoredAtom2876 Fin15AnchoredAtom2955 Fin15AnchoredAtom2956
    Fin15AnchoredAtom2957 Fin15AnchoredAtom3041 Fin15AnchoredAtom3120 Fin15AnchoredAtom3121
    Fin15AnchoredAtom3122 Fin15AnchoredAtom3206 Fin15AnchoredAtom3410 Fin15AnchoredAtom3615
    Fin15AnchoredAtom3616 Fin15AnchoredAtom3617 Fin15AnchoredAtom3701 Fin15AnchoredAtom3905
    Fin15AnchoredAtom4235 at hbad
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

theorem fin15Anchored_clause30595 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom2024 chi ∧
      ¬Fin15AnchoredAtom2025 chi ∧
      ¬Fin15AnchoredAtom2036 chi ∧
      ¬Fin15AnchoredAtom2057 chi ∧
      ¬Fin15AnchoredAtom2126 chi ∧
      ¬Fin15AnchoredAtom2128 chi ∧
      ¬Fin15AnchoredAtom2129 chi ∧
      ¬Fin15AnchoredAtom2135 chi ∧
      ¬Fin15AnchoredAtom2136 chi ∧
      ¬Fin15AnchoredAtom2147 chi ∧
      ¬Fin15AnchoredAtom2244 chi ∧
      ¬Fin15AnchoredAtom2245 chi ∧
      ¬Fin15AnchoredAtom2256 chi ∧
      ¬Fin15AnchoredAtom2277 chi ∧
      ¬Fin15AnchoredAtom2409 chi ∧
      ¬Fin15AnchoredAtom2410 chi ∧
      ¬Fin15AnchoredAtom2421 chi ∧
      ¬Fin15AnchoredAtom2442 chi ∧
      ¬Fin15AnchoredAtom2702 chi ∧
      ¬Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom2959 chi ∧
      ¬Fin15AnchoredAtom2960 chi ∧
      ¬Fin15AnchoredAtom2971 chi ∧
      ¬Fin15AnchoredAtom2992 chi ∧
      ¬Fin15AnchoredAtom3124 chi ∧
      ¬Fin15AnchoredAtom3125 chi ∧
      ¬Fin15AnchoredAtom3136 chi ∧
      ¬Fin15AnchoredAtom3157 chi ∧
      ¬Fin15AnchoredAtom3417 chi ∧
      ¬Fin15AnchoredAtom3619 chi ∧
      ¬Fin15AnchoredAtom3620 chi ∧
      ¬Fin15AnchoredAtom3631 chi ∧
      ¬Fin15AnchoredAtom3652 chi ∧
      ¬Fin15AnchoredAtom3912 chi ∧
      ¬Fin15AnchoredAtom4242 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 6, 7, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask01743
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1823 Fin15AnchoredAtom1824 Fin15AnchoredAtom1826
    Fin15AnchoredAtom1827 Fin15AnchoredAtom1851 Fin15AnchoredAtom1853 Fin15AnchoredAtom1854
    Fin15AnchoredAtom1860 Fin15AnchoredAtom1861 Fin15AnchoredAtom1872 Fin15AnchoredAtom1906
    Fin15AnchoredAtom1908 Fin15AnchoredAtom1909 Fin15AnchoredAtom1915 Fin15AnchoredAtom1916
    Fin15AnchoredAtom1927 Fin15AnchoredAtom2024 Fin15AnchoredAtom2025 Fin15AnchoredAtom2036
    Fin15AnchoredAtom2057 Fin15AnchoredAtom2126 Fin15AnchoredAtom2128 Fin15AnchoredAtom2129
    Fin15AnchoredAtom2135 Fin15AnchoredAtom2136 Fin15AnchoredAtom2147 Fin15AnchoredAtom2244
    Fin15AnchoredAtom2245 Fin15AnchoredAtom2256 Fin15AnchoredAtom2277 Fin15AnchoredAtom2409
    Fin15AnchoredAtom2410 Fin15AnchoredAtom2421 Fin15AnchoredAtom2442 Fin15AnchoredAtom2702
    Fin15AnchoredAtom2841 Fin15AnchoredAtom2843 Fin15AnchoredAtom2844 Fin15AnchoredAtom2850
    Fin15AnchoredAtom2851 Fin15AnchoredAtom2862 Fin15AnchoredAtom2959 Fin15AnchoredAtom2960
    Fin15AnchoredAtom2971 Fin15AnchoredAtom2992 Fin15AnchoredAtom3124 Fin15AnchoredAtom3125
    Fin15AnchoredAtom3136 Fin15AnchoredAtom3157 Fin15AnchoredAtom3417 Fin15AnchoredAtom3619
    Fin15AnchoredAtom3620 Fin15AnchoredAtom3631 Fin15AnchoredAtom3652 Fin15AnchoredAtom3912
    Fin15AnchoredAtom4242 at hbad
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

theorem fin15Anchored_clause30596 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1828 chi ∧
      ¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1855 chi ∧
      ¬Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom1862 chi ∧
      ¬Fin15AnchoredAtom1873 chi ∧
      ¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1910 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1917 chi ∧
      ¬Fin15AnchoredAtom1928 chi ∧
      ¬Fin15AnchoredAtom2024 chi ∧
      ¬Fin15AnchoredAtom2026 chi ∧
      ¬Fin15AnchoredAtom2037 chi ∧
      ¬Fin15AnchoredAtom2058 chi ∧
      ¬Fin15AnchoredAtom2126 chi ∧
      ¬Fin15AnchoredAtom2128 chi ∧
      ¬Fin15AnchoredAtom2130 chi ∧
      ¬Fin15AnchoredAtom2135 chi ∧
      ¬Fin15AnchoredAtom2137 chi ∧
      ¬Fin15AnchoredAtom2148 chi ∧
      ¬Fin15AnchoredAtom2244 chi ∧
      ¬Fin15AnchoredAtom2246 chi ∧
      ¬Fin15AnchoredAtom2257 chi ∧
      ¬Fin15AnchoredAtom2278 chi ∧
      ¬Fin15AnchoredAtom2409 chi ∧
      ¬Fin15AnchoredAtom2411 chi ∧
      ¬Fin15AnchoredAtom2422 chi ∧
      ¬Fin15AnchoredAtom2443 chi ∧
      ¬Fin15AnchoredAtom2703 chi ∧
      ¬Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom2845 chi ∧
      ¬Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom2852 chi ∧
      ¬Fin15AnchoredAtom2863 chi ∧
      ¬Fin15AnchoredAtom2959 chi ∧
      ¬Fin15AnchoredAtom2961 chi ∧
      ¬Fin15AnchoredAtom2972 chi ∧
      ¬Fin15AnchoredAtom2993 chi ∧
      ¬Fin15AnchoredAtom3124 chi ∧
      ¬Fin15AnchoredAtom3126 chi ∧
      ¬Fin15AnchoredAtom3137 chi ∧
      ¬Fin15AnchoredAtom3158 chi ∧
      ¬Fin15AnchoredAtom3418 chi ∧
      ¬Fin15AnchoredAtom3619 chi ∧
      ¬Fin15AnchoredAtom3621 chi ∧
      ¬Fin15AnchoredAtom3632 chi ∧
      ¬Fin15AnchoredAtom3653 chi ∧
      ¬Fin15AnchoredAtom3913 chi ∧
      ¬Fin15AnchoredAtom4243 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 6, 7, 9, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask02767
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1823 Fin15AnchoredAtom1824 Fin15AnchoredAtom1826
    Fin15AnchoredAtom1828 Fin15AnchoredAtom1851 Fin15AnchoredAtom1853 Fin15AnchoredAtom1855
    Fin15AnchoredAtom1860 Fin15AnchoredAtom1862 Fin15AnchoredAtom1873 Fin15AnchoredAtom1906
    Fin15AnchoredAtom1908 Fin15AnchoredAtom1910 Fin15AnchoredAtom1915 Fin15AnchoredAtom1917
    Fin15AnchoredAtom1928 Fin15AnchoredAtom2024 Fin15AnchoredAtom2026 Fin15AnchoredAtom2037
    Fin15AnchoredAtom2058 Fin15AnchoredAtom2126 Fin15AnchoredAtom2128 Fin15AnchoredAtom2130
    Fin15AnchoredAtom2135 Fin15AnchoredAtom2137 Fin15AnchoredAtom2148 Fin15AnchoredAtom2244
    Fin15AnchoredAtom2246 Fin15AnchoredAtom2257 Fin15AnchoredAtom2278 Fin15AnchoredAtom2409
    Fin15AnchoredAtom2411 Fin15AnchoredAtom2422 Fin15AnchoredAtom2443 Fin15AnchoredAtom2703
    Fin15AnchoredAtom2841 Fin15AnchoredAtom2843 Fin15AnchoredAtom2845 Fin15AnchoredAtom2850
    Fin15AnchoredAtom2852 Fin15AnchoredAtom2863 Fin15AnchoredAtom2959 Fin15AnchoredAtom2961
    Fin15AnchoredAtom2972 Fin15AnchoredAtom2993 Fin15AnchoredAtom3124 Fin15AnchoredAtom3126
    Fin15AnchoredAtom3137 Fin15AnchoredAtom3158 Fin15AnchoredAtom3418 Fin15AnchoredAtom3619
    Fin15AnchoredAtom3621 Fin15AnchoredAtom3632 Fin15AnchoredAtom3653 Fin15AnchoredAtom3913
    Fin15AnchoredAtom4243 at hbad
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

theorem fin15Anchored_clause30597 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom2024 chi ∧
      ¬Fin15AnchoredAtom2027 chi ∧
      ¬Fin15AnchoredAtom2038 chi ∧
      ¬Fin15AnchoredAtom2059 chi ∧
      ¬Fin15AnchoredAtom2126 chi ∧
      ¬Fin15AnchoredAtom2128 chi ∧
      ¬Fin15AnchoredAtom2131 chi ∧
      ¬Fin15AnchoredAtom2135 chi ∧
      ¬Fin15AnchoredAtom2138 chi ∧
      ¬Fin15AnchoredAtom2149 chi ∧
      ¬Fin15AnchoredAtom2244 chi ∧
      ¬Fin15AnchoredAtom2247 chi ∧
      ¬Fin15AnchoredAtom2258 chi ∧
      ¬Fin15AnchoredAtom2279 chi ∧
      ¬Fin15AnchoredAtom2409 chi ∧
      ¬Fin15AnchoredAtom2412 chi ∧
      ¬Fin15AnchoredAtom2423 chi ∧
      ¬Fin15AnchoredAtom2444 chi ∧
      ¬Fin15AnchoredAtom2704 chi ∧
      ¬Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom2864 chi ∧
      ¬Fin15AnchoredAtom2959 chi ∧
      ¬Fin15AnchoredAtom2962 chi ∧
      ¬Fin15AnchoredAtom2973 chi ∧
      ¬Fin15AnchoredAtom2994 chi ∧
      ¬Fin15AnchoredAtom3124 chi ∧
      ¬Fin15AnchoredAtom3127 chi ∧
      ¬Fin15AnchoredAtom3138 chi ∧
      ¬Fin15AnchoredAtom3159 chi ∧
      ¬Fin15AnchoredAtom3419 chi ∧
      ¬Fin15AnchoredAtom3619 chi ∧
      ¬Fin15AnchoredAtom3622 chi ∧
      ¬Fin15AnchoredAtom3633 chi ∧
      ¬Fin15AnchoredAtom3654 chi ∧
      ¬Fin15AnchoredAtom3914 chi ∧
      ¬Fin15AnchoredAtom4244 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 6, 7, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask04815
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1823 Fin15AnchoredAtom1824 Fin15AnchoredAtom1826
    Fin15AnchoredAtom1829 Fin15AnchoredAtom1851 Fin15AnchoredAtom1853 Fin15AnchoredAtom1856
    Fin15AnchoredAtom1860 Fin15AnchoredAtom1863 Fin15AnchoredAtom1874 Fin15AnchoredAtom1906
    Fin15AnchoredAtom1908 Fin15AnchoredAtom1911 Fin15AnchoredAtom1915 Fin15AnchoredAtom1918
    Fin15AnchoredAtom1929 Fin15AnchoredAtom2024 Fin15AnchoredAtom2027 Fin15AnchoredAtom2038
    Fin15AnchoredAtom2059 Fin15AnchoredAtom2126 Fin15AnchoredAtom2128 Fin15AnchoredAtom2131
    Fin15AnchoredAtom2135 Fin15AnchoredAtom2138 Fin15AnchoredAtom2149 Fin15AnchoredAtom2244
    Fin15AnchoredAtom2247 Fin15AnchoredAtom2258 Fin15AnchoredAtom2279 Fin15AnchoredAtom2409
    Fin15AnchoredAtom2412 Fin15AnchoredAtom2423 Fin15AnchoredAtom2444 Fin15AnchoredAtom2704
    Fin15AnchoredAtom2841 Fin15AnchoredAtom2843 Fin15AnchoredAtom2846 Fin15AnchoredAtom2850
    Fin15AnchoredAtom2853 Fin15AnchoredAtom2864 Fin15AnchoredAtom2959 Fin15AnchoredAtom2962
    Fin15AnchoredAtom2973 Fin15AnchoredAtom2994 Fin15AnchoredAtom3124 Fin15AnchoredAtom3127
    Fin15AnchoredAtom3138 Fin15AnchoredAtom3159 Fin15AnchoredAtom3419 Fin15AnchoredAtom3619
    Fin15AnchoredAtom3622 Fin15AnchoredAtom3633 Fin15AnchoredAtom3654 Fin15AnchoredAtom3914
    Fin15AnchoredAtom4244 at hbad
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

theorem fin15Anchored_clause30598 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom2024 chi ∧
      ¬Fin15AnchoredAtom2028 chi ∧
      ¬Fin15AnchoredAtom2039 chi ∧
      ¬Fin15AnchoredAtom2060 chi ∧
      ¬Fin15AnchoredAtom2126 chi ∧
      ¬Fin15AnchoredAtom2128 chi ∧
      ¬Fin15AnchoredAtom2132 chi ∧
      ¬Fin15AnchoredAtom2135 chi ∧
      ¬Fin15AnchoredAtom2139 chi ∧
      ¬Fin15AnchoredAtom2150 chi ∧
      ¬Fin15AnchoredAtom2244 chi ∧
      ¬Fin15AnchoredAtom2248 chi ∧
      ¬Fin15AnchoredAtom2259 chi ∧
      ¬Fin15AnchoredAtom2280 chi ∧
      ¬Fin15AnchoredAtom2409 chi ∧
      ¬Fin15AnchoredAtom2413 chi ∧
      ¬Fin15AnchoredAtom2424 chi ∧
      ¬Fin15AnchoredAtom2445 chi ∧
      ¬Fin15AnchoredAtom2705 chi ∧
      ¬Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom2865 chi ∧
      ¬Fin15AnchoredAtom2959 chi ∧
      ¬Fin15AnchoredAtom2963 chi ∧
      ¬Fin15AnchoredAtom2974 chi ∧
      ¬Fin15AnchoredAtom2995 chi ∧
      ¬Fin15AnchoredAtom3124 chi ∧
      ¬Fin15AnchoredAtom3128 chi ∧
      ¬Fin15AnchoredAtom3139 chi ∧
      ¬Fin15AnchoredAtom3160 chi ∧
      ¬Fin15AnchoredAtom3420 chi ∧
      ¬Fin15AnchoredAtom3619 chi ∧
      ¬Fin15AnchoredAtom3623 chi ∧
      ¬Fin15AnchoredAtom3634 chi ∧
      ¬Fin15AnchoredAtom3655 chi ∧
      ¬Fin15AnchoredAtom3915 chi ∧
      ¬Fin15AnchoredAtom4245 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 6, 7, 9, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask08911
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1823 Fin15AnchoredAtom1824 Fin15AnchoredAtom1826
    Fin15AnchoredAtom1830 Fin15AnchoredAtom1851 Fin15AnchoredAtom1853 Fin15AnchoredAtom1857
    Fin15AnchoredAtom1860 Fin15AnchoredAtom1864 Fin15AnchoredAtom1875 Fin15AnchoredAtom1906
    Fin15AnchoredAtom1908 Fin15AnchoredAtom1912 Fin15AnchoredAtom1915 Fin15AnchoredAtom1919
    Fin15AnchoredAtom1930 Fin15AnchoredAtom2024 Fin15AnchoredAtom2028 Fin15AnchoredAtom2039
    Fin15AnchoredAtom2060 Fin15AnchoredAtom2126 Fin15AnchoredAtom2128 Fin15AnchoredAtom2132
    Fin15AnchoredAtom2135 Fin15AnchoredAtom2139 Fin15AnchoredAtom2150 Fin15AnchoredAtom2244
    Fin15AnchoredAtom2248 Fin15AnchoredAtom2259 Fin15AnchoredAtom2280 Fin15AnchoredAtom2409
    Fin15AnchoredAtom2413 Fin15AnchoredAtom2424 Fin15AnchoredAtom2445 Fin15AnchoredAtom2705
    Fin15AnchoredAtom2841 Fin15AnchoredAtom2843 Fin15AnchoredAtom2847 Fin15AnchoredAtom2850
    Fin15AnchoredAtom2854 Fin15AnchoredAtom2865 Fin15AnchoredAtom2959 Fin15AnchoredAtom2963
    Fin15AnchoredAtom2974 Fin15AnchoredAtom2995 Fin15AnchoredAtom3124 Fin15AnchoredAtom3128
    Fin15AnchoredAtom3139 Fin15AnchoredAtom3160 Fin15AnchoredAtom3420 Fin15AnchoredAtom3619
    Fin15AnchoredAtom3623 Fin15AnchoredAtom3634 Fin15AnchoredAtom3655 Fin15AnchoredAtom3915
    Fin15AnchoredAtom4245 at hbad
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

theorem fin15Anchored_clause30599 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom2024 chi ∧
      ¬Fin15AnchoredAtom2029 chi ∧
      ¬Fin15AnchoredAtom2040 chi ∧
      ¬Fin15AnchoredAtom2061 chi ∧
      ¬Fin15AnchoredAtom2126 chi ∧
      ¬Fin15AnchoredAtom2128 chi ∧
      ¬Fin15AnchoredAtom2133 chi ∧
      ¬Fin15AnchoredAtom2135 chi ∧
      ¬Fin15AnchoredAtom2140 chi ∧
      ¬Fin15AnchoredAtom2151 chi ∧
      ¬Fin15AnchoredAtom2244 chi ∧
      ¬Fin15AnchoredAtom2249 chi ∧
      ¬Fin15AnchoredAtom2260 chi ∧
      ¬Fin15AnchoredAtom2281 chi ∧
      ¬Fin15AnchoredAtom2409 chi ∧
      ¬Fin15AnchoredAtom2414 chi ∧
      ¬Fin15AnchoredAtom2425 chi ∧
      ¬Fin15AnchoredAtom2446 chi ∧
      ¬Fin15AnchoredAtom2706 chi ∧
      ¬Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom2866 chi ∧
      ¬Fin15AnchoredAtom2959 chi ∧
      ¬Fin15AnchoredAtom2964 chi ∧
      ¬Fin15AnchoredAtom2975 chi ∧
      ¬Fin15AnchoredAtom2996 chi ∧
      ¬Fin15AnchoredAtom3124 chi ∧
      ¬Fin15AnchoredAtom3129 chi ∧
      ¬Fin15AnchoredAtom3140 chi ∧
      ¬Fin15AnchoredAtom3161 chi ∧
      ¬Fin15AnchoredAtom3421 chi ∧
      ¬Fin15AnchoredAtom3619 chi ∧
      ¬Fin15AnchoredAtom3624 chi ∧
      ¬Fin15AnchoredAtom3635 chi ∧
      ¬Fin15AnchoredAtom3656 chi ∧
      ¬Fin15AnchoredAtom3916 chi ∧
      ¬Fin15AnchoredAtom4246 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 6, 7, 9, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17103
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1823 Fin15AnchoredAtom1824 Fin15AnchoredAtom1826
    Fin15AnchoredAtom1831 Fin15AnchoredAtom1851 Fin15AnchoredAtom1853 Fin15AnchoredAtom1858
    Fin15AnchoredAtom1860 Fin15AnchoredAtom1865 Fin15AnchoredAtom1876 Fin15AnchoredAtom1906
    Fin15AnchoredAtom1908 Fin15AnchoredAtom1913 Fin15AnchoredAtom1915 Fin15AnchoredAtom1920
    Fin15AnchoredAtom1931 Fin15AnchoredAtom2024 Fin15AnchoredAtom2029 Fin15AnchoredAtom2040
    Fin15AnchoredAtom2061 Fin15AnchoredAtom2126 Fin15AnchoredAtom2128 Fin15AnchoredAtom2133
    Fin15AnchoredAtom2135 Fin15AnchoredAtom2140 Fin15AnchoredAtom2151 Fin15AnchoredAtom2244
    Fin15AnchoredAtom2249 Fin15AnchoredAtom2260 Fin15AnchoredAtom2281 Fin15AnchoredAtom2409
    Fin15AnchoredAtom2414 Fin15AnchoredAtom2425 Fin15AnchoredAtom2446 Fin15AnchoredAtom2706
    Fin15AnchoredAtom2841 Fin15AnchoredAtom2843 Fin15AnchoredAtom2848 Fin15AnchoredAtom2850
    Fin15AnchoredAtom2855 Fin15AnchoredAtom2866 Fin15AnchoredAtom2959 Fin15AnchoredAtom2964
    Fin15AnchoredAtom2975 Fin15AnchoredAtom2996 Fin15AnchoredAtom3124 Fin15AnchoredAtom3129
    Fin15AnchoredAtom3140 Fin15AnchoredAtom3161 Fin15AnchoredAtom3421 Fin15AnchoredAtom3619
    Fin15AnchoredAtom3624 Fin15AnchoredAtom3635 Fin15AnchoredAtom3656 Fin15AnchoredAtom3916
    Fin15AnchoredAtom4246 at hbad
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

theorem fin15Anchored_clause30600 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom2025 chi ∧
      ¬Fin15AnchoredAtom2027 chi ∧
      ¬Fin15AnchoredAtom2042 chi ∧
      ¬Fin15AnchoredAtom2063 chi ∧
      ¬Fin15AnchoredAtom2126 chi ∧
      ¬Fin15AnchoredAtom2129 chi ∧
      ¬Fin15AnchoredAtom2131 chi ∧
      ¬Fin15AnchoredAtom2136 chi ∧
      ¬Fin15AnchoredAtom2138 chi ∧
      ¬Fin15AnchoredAtom2153 chi ∧
      ¬Fin15AnchoredAtom2245 chi ∧
      ¬Fin15AnchoredAtom2247 chi ∧
      ¬Fin15AnchoredAtom2262 chi ∧
      ¬Fin15AnchoredAtom2283 chi ∧
      ¬Fin15AnchoredAtom2410 chi ∧
      ¬Fin15AnchoredAtom2412 chi ∧
      ¬Fin15AnchoredAtom2427 chi ∧
      ¬Fin15AnchoredAtom2448 chi ∧
      ¬Fin15AnchoredAtom2708 chi ∧
      ¬Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom2868 chi ∧
      ¬Fin15AnchoredAtom2960 chi ∧
      ¬Fin15AnchoredAtom2962 chi ∧
      ¬Fin15AnchoredAtom2977 chi ∧
      ¬Fin15AnchoredAtom2998 chi ∧
      ¬Fin15AnchoredAtom3125 chi ∧
      ¬Fin15AnchoredAtom3127 chi ∧
      ¬Fin15AnchoredAtom3142 chi ∧
      ¬Fin15AnchoredAtom3163 chi ∧
      ¬Fin15AnchoredAtom3423 chi ∧
      ¬Fin15AnchoredAtom3620 chi ∧
      ¬Fin15AnchoredAtom3622 chi ∧
      ¬Fin15AnchoredAtom3637 chi ∧
      ¬Fin15AnchoredAtom3658 chi ∧
      ¬Fin15AnchoredAtom3918 chi ∧
      ¬Fin15AnchoredAtom4248 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 6, 7, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05327
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1823 Fin15AnchoredAtom1824 Fin15AnchoredAtom1827
    Fin15AnchoredAtom1829 Fin15AnchoredAtom1851 Fin15AnchoredAtom1854 Fin15AnchoredAtom1856
    Fin15AnchoredAtom1861 Fin15AnchoredAtom1863 Fin15AnchoredAtom1878 Fin15AnchoredAtom1906
    Fin15AnchoredAtom1909 Fin15AnchoredAtom1911 Fin15AnchoredAtom1916 Fin15AnchoredAtom1918
    Fin15AnchoredAtom1933 Fin15AnchoredAtom2025 Fin15AnchoredAtom2027 Fin15AnchoredAtom2042
    Fin15AnchoredAtom2063 Fin15AnchoredAtom2126 Fin15AnchoredAtom2129 Fin15AnchoredAtom2131
    Fin15AnchoredAtom2136 Fin15AnchoredAtom2138 Fin15AnchoredAtom2153 Fin15AnchoredAtom2245
    Fin15AnchoredAtom2247 Fin15AnchoredAtom2262 Fin15AnchoredAtom2283 Fin15AnchoredAtom2410
    Fin15AnchoredAtom2412 Fin15AnchoredAtom2427 Fin15AnchoredAtom2448 Fin15AnchoredAtom2708
    Fin15AnchoredAtom2841 Fin15AnchoredAtom2844 Fin15AnchoredAtom2846 Fin15AnchoredAtom2851
    Fin15AnchoredAtom2853 Fin15AnchoredAtom2868 Fin15AnchoredAtom2960 Fin15AnchoredAtom2962
    Fin15AnchoredAtom2977 Fin15AnchoredAtom2998 Fin15AnchoredAtom3125 Fin15AnchoredAtom3127
    Fin15AnchoredAtom3142 Fin15AnchoredAtom3163 Fin15AnchoredAtom3423 Fin15AnchoredAtom3620
    Fin15AnchoredAtom3622 Fin15AnchoredAtom3637 Fin15AnchoredAtom3658 Fin15AnchoredAtom3918
    Fin15AnchoredAtom4248 at hbad
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

theorem fin15Anchored_clause30601 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom2025 chi ∧
      ¬Fin15AnchoredAtom2028 chi ∧
      ¬Fin15AnchoredAtom2043 chi ∧
      ¬Fin15AnchoredAtom2064 chi ∧
      ¬Fin15AnchoredAtom2126 chi ∧
      ¬Fin15AnchoredAtom2129 chi ∧
      ¬Fin15AnchoredAtom2132 chi ∧
      ¬Fin15AnchoredAtom2136 chi ∧
      ¬Fin15AnchoredAtom2139 chi ∧
      ¬Fin15AnchoredAtom2154 chi ∧
      ¬Fin15AnchoredAtom2245 chi ∧
      ¬Fin15AnchoredAtom2248 chi ∧
      ¬Fin15AnchoredAtom2263 chi ∧
      ¬Fin15AnchoredAtom2284 chi ∧
      ¬Fin15AnchoredAtom2410 chi ∧
      ¬Fin15AnchoredAtom2413 chi ∧
      ¬Fin15AnchoredAtom2428 chi ∧
      ¬Fin15AnchoredAtom2449 chi ∧
      ¬Fin15AnchoredAtom2709 chi ∧
      ¬Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom2869 chi ∧
      ¬Fin15AnchoredAtom2960 chi ∧
      ¬Fin15AnchoredAtom2963 chi ∧
      ¬Fin15AnchoredAtom2978 chi ∧
      ¬Fin15AnchoredAtom2999 chi ∧
      ¬Fin15AnchoredAtom3125 chi ∧
      ¬Fin15AnchoredAtom3128 chi ∧
      ¬Fin15AnchoredAtom3143 chi ∧
      ¬Fin15AnchoredAtom3164 chi ∧
      ¬Fin15AnchoredAtom3424 chi ∧
      ¬Fin15AnchoredAtom3620 chi ∧
      ¬Fin15AnchoredAtom3623 chi ∧
      ¬Fin15AnchoredAtom3638 chi ∧
      ¬Fin15AnchoredAtom3659 chi ∧
      ¬Fin15AnchoredAtom3919 chi ∧
      ¬Fin15AnchoredAtom4249 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 6, 7, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09423
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1823 Fin15AnchoredAtom1824 Fin15AnchoredAtom1827
    Fin15AnchoredAtom1830 Fin15AnchoredAtom1851 Fin15AnchoredAtom1854 Fin15AnchoredAtom1857
    Fin15AnchoredAtom1861 Fin15AnchoredAtom1864 Fin15AnchoredAtom1879 Fin15AnchoredAtom1906
    Fin15AnchoredAtom1909 Fin15AnchoredAtom1912 Fin15AnchoredAtom1916 Fin15AnchoredAtom1919
    Fin15AnchoredAtom1934 Fin15AnchoredAtom2025 Fin15AnchoredAtom2028 Fin15AnchoredAtom2043
    Fin15AnchoredAtom2064 Fin15AnchoredAtom2126 Fin15AnchoredAtom2129 Fin15AnchoredAtom2132
    Fin15AnchoredAtom2136 Fin15AnchoredAtom2139 Fin15AnchoredAtom2154 Fin15AnchoredAtom2245
    Fin15AnchoredAtom2248 Fin15AnchoredAtom2263 Fin15AnchoredAtom2284 Fin15AnchoredAtom2410
    Fin15AnchoredAtom2413 Fin15AnchoredAtom2428 Fin15AnchoredAtom2449 Fin15AnchoredAtom2709
    Fin15AnchoredAtom2841 Fin15AnchoredAtom2844 Fin15AnchoredAtom2847 Fin15AnchoredAtom2851
    Fin15AnchoredAtom2854 Fin15AnchoredAtom2869 Fin15AnchoredAtom2960 Fin15AnchoredAtom2963
    Fin15AnchoredAtom2978 Fin15AnchoredAtom2999 Fin15AnchoredAtom3125 Fin15AnchoredAtom3128
    Fin15AnchoredAtom3143 Fin15AnchoredAtom3164 Fin15AnchoredAtom3424 Fin15AnchoredAtom3620
    Fin15AnchoredAtom3623 Fin15AnchoredAtom3638 Fin15AnchoredAtom3659 Fin15AnchoredAtom3919
    Fin15AnchoredAtom4249 at hbad
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

theorem fin15Anchored_clause30602 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1935 chi ∧
      ¬Fin15AnchoredAtom2025 chi ∧
      ¬Fin15AnchoredAtom2029 chi ∧
      ¬Fin15AnchoredAtom2044 chi ∧
      ¬Fin15AnchoredAtom2065 chi ∧
      ¬Fin15AnchoredAtom2126 chi ∧
      ¬Fin15AnchoredAtom2129 chi ∧
      ¬Fin15AnchoredAtom2133 chi ∧
      ¬Fin15AnchoredAtom2136 chi ∧
      ¬Fin15AnchoredAtom2140 chi ∧
      ¬Fin15AnchoredAtom2155 chi ∧
      ¬Fin15AnchoredAtom2245 chi ∧
      ¬Fin15AnchoredAtom2249 chi ∧
      ¬Fin15AnchoredAtom2264 chi ∧
      ¬Fin15AnchoredAtom2285 chi ∧
      ¬Fin15AnchoredAtom2410 chi ∧
      ¬Fin15AnchoredAtom2414 chi ∧
      ¬Fin15AnchoredAtom2429 chi ∧
      ¬Fin15AnchoredAtom2450 chi ∧
      ¬Fin15AnchoredAtom2710 chi ∧
      ¬Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom2870 chi ∧
      ¬Fin15AnchoredAtom2960 chi ∧
      ¬Fin15AnchoredAtom2964 chi ∧
      ¬Fin15AnchoredAtom2979 chi ∧
      ¬Fin15AnchoredAtom3000 chi ∧
      ¬Fin15AnchoredAtom3125 chi ∧
      ¬Fin15AnchoredAtom3129 chi ∧
      ¬Fin15AnchoredAtom3144 chi ∧
      ¬Fin15AnchoredAtom3165 chi ∧
      ¬Fin15AnchoredAtom3425 chi ∧
      ¬Fin15AnchoredAtom3620 chi ∧
      ¬Fin15AnchoredAtom3624 chi ∧
      ¬Fin15AnchoredAtom3639 chi ∧
      ¬Fin15AnchoredAtom3660 chi ∧
      ¬Fin15AnchoredAtom3920 chi ∧
      ¬Fin15AnchoredAtom4250 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 6, 7, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17615
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1823 Fin15AnchoredAtom1824 Fin15AnchoredAtom1827
    Fin15AnchoredAtom1831 Fin15AnchoredAtom1851 Fin15AnchoredAtom1854 Fin15AnchoredAtom1858
    Fin15AnchoredAtom1861 Fin15AnchoredAtom1865 Fin15AnchoredAtom1880 Fin15AnchoredAtom1906
    Fin15AnchoredAtom1909 Fin15AnchoredAtom1913 Fin15AnchoredAtom1916 Fin15AnchoredAtom1920
    Fin15AnchoredAtom1935 Fin15AnchoredAtom2025 Fin15AnchoredAtom2029 Fin15AnchoredAtom2044
    Fin15AnchoredAtom2065 Fin15AnchoredAtom2126 Fin15AnchoredAtom2129 Fin15AnchoredAtom2133
    Fin15AnchoredAtom2136 Fin15AnchoredAtom2140 Fin15AnchoredAtom2155 Fin15AnchoredAtom2245
    Fin15AnchoredAtom2249 Fin15AnchoredAtom2264 Fin15AnchoredAtom2285 Fin15AnchoredAtom2410
    Fin15AnchoredAtom2414 Fin15AnchoredAtom2429 Fin15AnchoredAtom2450 Fin15AnchoredAtom2710
    Fin15AnchoredAtom2841 Fin15AnchoredAtom2844 Fin15AnchoredAtom2848 Fin15AnchoredAtom2851
    Fin15AnchoredAtom2855 Fin15AnchoredAtom2870 Fin15AnchoredAtom2960 Fin15AnchoredAtom2964
    Fin15AnchoredAtom2979 Fin15AnchoredAtom3000 Fin15AnchoredAtom3125 Fin15AnchoredAtom3129
    Fin15AnchoredAtom3144 Fin15AnchoredAtom3165 Fin15AnchoredAtom3425 Fin15AnchoredAtom3620
    Fin15AnchoredAtom3624 Fin15AnchoredAtom3639 Fin15AnchoredAtom3660 Fin15AnchoredAtom3920
    Fin15AnchoredAtom4250 at hbad
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

theorem fin15Anchored_clause30603 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1939 chi ∧
      ¬Fin15AnchoredAtom2027 chi ∧
      ¬Fin15AnchoredAtom2028 chi ∧
      ¬Fin15AnchoredAtom2048 chi ∧
      ¬Fin15AnchoredAtom2069 chi ∧
      ¬Fin15AnchoredAtom2126 chi ∧
      ¬Fin15AnchoredAtom2131 chi ∧
      ¬Fin15AnchoredAtom2132 chi ∧
      ¬Fin15AnchoredAtom2138 chi ∧
      ¬Fin15AnchoredAtom2139 chi ∧
      ¬Fin15AnchoredAtom2159 chi ∧
      ¬Fin15AnchoredAtom2247 chi ∧
      ¬Fin15AnchoredAtom2248 chi ∧
      ¬Fin15AnchoredAtom2268 chi ∧
      ¬Fin15AnchoredAtom2289 chi ∧
      ¬Fin15AnchoredAtom2412 chi ∧
      ¬Fin15AnchoredAtom2413 chi ∧
      ¬Fin15AnchoredAtom2433 chi ∧
      ¬Fin15AnchoredAtom2454 chi ∧
      ¬Fin15AnchoredAtom2714 chi ∧
      ¬Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom2874 chi ∧
      ¬Fin15AnchoredAtom2962 chi ∧
      ¬Fin15AnchoredAtom2963 chi ∧
      ¬Fin15AnchoredAtom2983 chi ∧
      ¬Fin15AnchoredAtom3004 chi ∧
      ¬Fin15AnchoredAtom3127 chi ∧
      ¬Fin15AnchoredAtom3128 chi ∧
      ¬Fin15AnchoredAtom3148 chi ∧
      ¬Fin15AnchoredAtom3169 chi ∧
      ¬Fin15AnchoredAtom3429 chi ∧
      ¬Fin15AnchoredAtom3622 chi ∧
      ¬Fin15AnchoredAtom3623 chi ∧
      ¬Fin15AnchoredAtom3643 chi ∧
      ¬Fin15AnchoredAtom3664 chi ∧
      ¬Fin15AnchoredAtom3924 chi ∧
      ¬Fin15AnchoredAtom4254 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 6, 7, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask12495
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1823 Fin15AnchoredAtom1824 Fin15AnchoredAtom1829
    Fin15AnchoredAtom1830 Fin15AnchoredAtom1851 Fin15AnchoredAtom1856 Fin15AnchoredAtom1857
    Fin15AnchoredAtom1863 Fin15AnchoredAtom1864 Fin15AnchoredAtom1884 Fin15AnchoredAtom1906
    Fin15AnchoredAtom1911 Fin15AnchoredAtom1912 Fin15AnchoredAtom1918 Fin15AnchoredAtom1919
    Fin15AnchoredAtom1939 Fin15AnchoredAtom2027 Fin15AnchoredAtom2028 Fin15AnchoredAtom2048
    Fin15AnchoredAtom2069 Fin15AnchoredAtom2126 Fin15AnchoredAtom2131 Fin15AnchoredAtom2132
    Fin15AnchoredAtom2138 Fin15AnchoredAtom2139 Fin15AnchoredAtom2159 Fin15AnchoredAtom2247
    Fin15AnchoredAtom2248 Fin15AnchoredAtom2268 Fin15AnchoredAtom2289 Fin15AnchoredAtom2412
    Fin15AnchoredAtom2413 Fin15AnchoredAtom2433 Fin15AnchoredAtom2454 Fin15AnchoredAtom2714
    Fin15AnchoredAtom2841 Fin15AnchoredAtom2846 Fin15AnchoredAtom2847 Fin15AnchoredAtom2853
    Fin15AnchoredAtom2854 Fin15AnchoredAtom2874 Fin15AnchoredAtom2962 Fin15AnchoredAtom2963
    Fin15AnchoredAtom2983 Fin15AnchoredAtom3004 Fin15AnchoredAtom3127 Fin15AnchoredAtom3128
    Fin15AnchoredAtom3148 Fin15AnchoredAtom3169 Fin15AnchoredAtom3429 Fin15AnchoredAtom3622
    Fin15AnchoredAtom3623 Fin15AnchoredAtom3643 Fin15AnchoredAtom3664 Fin15AnchoredAtom3924
    Fin15AnchoredAtom4254 at hbad
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

theorem fin15Anchored_clause30604 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1940 chi ∧
      ¬Fin15AnchoredAtom2027 chi ∧
      ¬Fin15AnchoredAtom2029 chi ∧
      ¬Fin15AnchoredAtom2049 chi ∧
      ¬Fin15AnchoredAtom2070 chi ∧
      ¬Fin15AnchoredAtom2126 chi ∧
      ¬Fin15AnchoredAtom2131 chi ∧
      ¬Fin15AnchoredAtom2133 chi ∧
      ¬Fin15AnchoredAtom2138 chi ∧
      ¬Fin15AnchoredAtom2140 chi ∧
      ¬Fin15AnchoredAtom2160 chi ∧
      ¬Fin15AnchoredAtom2247 chi ∧
      ¬Fin15AnchoredAtom2249 chi ∧
      ¬Fin15AnchoredAtom2269 chi ∧
      ¬Fin15AnchoredAtom2290 chi ∧
      ¬Fin15AnchoredAtom2412 chi ∧
      ¬Fin15AnchoredAtom2414 chi ∧
      ¬Fin15AnchoredAtom2434 chi ∧
      ¬Fin15AnchoredAtom2455 chi ∧
      ¬Fin15AnchoredAtom2715 chi ∧
      ¬Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom2875 chi ∧
      ¬Fin15AnchoredAtom2962 chi ∧
      ¬Fin15AnchoredAtom2964 chi ∧
      ¬Fin15AnchoredAtom2984 chi ∧
      ¬Fin15AnchoredAtom3005 chi ∧
      ¬Fin15AnchoredAtom3127 chi ∧
      ¬Fin15AnchoredAtom3129 chi ∧
      ¬Fin15AnchoredAtom3149 chi ∧
      ¬Fin15AnchoredAtom3170 chi ∧
      ¬Fin15AnchoredAtom3430 chi ∧
      ¬Fin15AnchoredAtom3622 chi ∧
      ¬Fin15AnchoredAtom3624 chi ∧
      ¬Fin15AnchoredAtom3644 chi ∧
      ¬Fin15AnchoredAtom3665 chi ∧
      ¬Fin15AnchoredAtom3925 chi ∧
      ¬Fin15AnchoredAtom4255 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 6, 7, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask20687
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1823 Fin15AnchoredAtom1824 Fin15AnchoredAtom1829
    Fin15AnchoredAtom1831 Fin15AnchoredAtom1851 Fin15AnchoredAtom1856 Fin15AnchoredAtom1858
    Fin15AnchoredAtom1863 Fin15AnchoredAtom1865 Fin15AnchoredAtom1885 Fin15AnchoredAtom1906
    Fin15AnchoredAtom1911 Fin15AnchoredAtom1913 Fin15AnchoredAtom1918 Fin15AnchoredAtom1920
    Fin15AnchoredAtom1940 Fin15AnchoredAtom2027 Fin15AnchoredAtom2029 Fin15AnchoredAtom2049
    Fin15AnchoredAtom2070 Fin15AnchoredAtom2126 Fin15AnchoredAtom2131 Fin15AnchoredAtom2133
    Fin15AnchoredAtom2138 Fin15AnchoredAtom2140 Fin15AnchoredAtom2160 Fin15AnchoredAtom2247
    Fin15AnchoredAtom2249 Fin15AnchoredAtom2269 Fin15AnchoredAtom2290 Fin15AnchoredAtom2412
    Fin15AnchoredAtom2414 Fin15AnchoredAtom2434 Fin15AnchoredAtom2455 Fin15AnchoredAtom2715
    Fin15AnchoredAtom2841 Fin15AnchoredAtom2846 Fin15AnchoredAtom2848 Fin15AnchoredAtom2853
    Fin15AnchoredAtom2855 Fin15AnchoredAtom2875 Fin15AnchoredAtom2962 Fin15AnchoredAtom2964
    Fin15AnchoredAtom2984 Fin15AnchoredAtom3005 Fin15AnchoredAtom3127 Fin15AnchoredAtom3129
    Fin15AnchoredAtom3149 Fin15AnchoredAtom3170 Fin15AnchoredAtom3430 Fin15AnchoredAtom3622
    Fin15AnchoredAtom3624 Fin15AnchoredAtom3644 Fin15AnchoredAtom3665 Fin15AnchoredAtom3925
    Fin15AnchoredAtom4255 at hbad
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

theorem fin15Anchored_clause30605 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom1886 chi ∧
      ¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
      ¬Fin15AnchoredAtom2028 chi ∧
      ¬Fin15AnchoredAtom2029 chi ∧
      ¬Fin15AnchoredAtom2050 chi ∧
      ¬Fin15AnchoredAtom2071 chi ∧
      ¬Fin15AnchoredAtom2126 chi ∧
      ¬Fin15AnchoredAtom2132 chi ∧
      ¬Fin15AnchoredAtom2133 chi ∧
      ¬Fin15AnchoredAtom2139 chi ∧
      ¬Fin15AnchoredAtom2140 chi ∧
      ¬Fin15AnchoredAtom2161 chi ∧
      ¬Fin15AnchoredAtom2248 chi ∧
      ¬Fin15AnchoredAtom2249 chi ∧
      ¬Fin15AnchoredAtom2270 chi ∧
      ¬Fin15AnchoredAtom2291 chi ∧
      ¬Fin15AnchoredAtom2413 chi ∧
      ¬Fin15AnchoredAtom2414 chi ∧
      ¬Fin15AnchoredAtom2435 chi ∧
      ¬Fin15AnchoredAtom2456 chi ∧
      ¬Fin15AnchoredAtom2716 chi ∧
      ¬Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom2876 chi ∧
      ¬Fin15AnchoredAtom2963 chi ∧
      ¬Fin15AnchoredAtom2964 chi ∧
      ¬Fin15AnchoredAtom2985 chi ∧
      ¬Fin15AnchoredAtom3006 chi ∧
      ¬Fin15AnchoredAtom3128 chi ∧
      ¬Fin15AnchoredAtom3129 chi ∧
      ¬Fin15AnchoredAtom3150 chi ∧
      ¬Fin15AnchoredAtom3171 chi ∧
      ¬Fin15AnchoredAtom3431 chi ∧
      ¬Fin15AnchoredAtom3623 chi ∧
      ¬Fin15AnchoredAtom3624 chi ∧
      ¬Fin15AnchoredAtom3645 chi ∧
      ¬Fin15AnchoredAtom3666 chi ∧
      ¬Fin15AnchoredAtom3926 chi ∧
      ¬Fin15AnchoredAtom4256 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 6, 7, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask24783
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1823 Fin15AnchoredAtom1824 Fin15AnchoredAtom1830
    Fin15AnchoredAtom1831 Fin15AnchoredAtom1851 Fin15AnchoredAtom1857 Fin15AnchoredAtom1858
    Fin15AnchoredAtom1864 Fin15AnchoredAtom1865 Fin15AnchoredAtom1886 Fin15AnchoredAtom1906
    Fin15AnchoredAtom1912 Fin15AnchoredAtom1913 Fin15AnchoredAtom1919 Fin15AnchoredAtom1920
    Fin15AnchoredAtom1941 Fin15AnchoredAtom2028 Fin15AnchoredAtom2029 Fin15AnchoredAtom2050
    Fin15AnchoredAtom2071 Fin15AnchoredAtom2126 Fin15AnchoredAtom2132 Fin15AnchoredAtom2133
    Fin15AnchoredAtom2139 Fin15AnchoredAtom2140 Fin15AnchoredAtom2161 Fin15AnchoredAtom2248
    Fin15AnchoredAtom2249 Fin15AnchoredAtom2270 Fin15AnchoredAtom2291 Fin15AnchoredAtom2413
    Fin15AnchoredAtom2414 Fin15AnchoredAtom2435 Fin15AnchoredAtom2456 Fin15AnchoredAtom2716
    Fin15AnchoredAtom2841 Fin15AnchoredAtom2847 Fin15AnchoredAtom2848 Fin15AnchoredAtom2854
    Fin15AnchoredAtom2855 Fin15AnchoredAtom2876 Fin15AnchoredAtom2963 Fin15AnchoredAtom2964
    Fin15AnchoredAtom2985 Fin15AnchoredAtom3006 Fin15AnchoredAtom3128 Fin15AnchoredAtom3129
    Fin15AnchoredAtom3150 Fin15AnchoredAtom3171 Fin15AnchoredAtom3431 Fin15AnchoredAtom3623
    Fin15AnchoredAtom3624 Fin15AnchoredAtom3645 Fin15AnchoredAtom3666 Fin15AnchoredAtom3926
    Fin15AnchoredAtom4256 at hbad
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

theorem fin15Anchored_clause30606 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom2036 chi ∧
      ¬Fin15AnchoredAtom2038 chi ∧
      ¬Fin15AnchoredAtom2042 chi ∧
      ¬Fin15AnchoredAtom2088 chi ∧
      ¬Fin15AnchoredAtom2128 chi ∧
      ¬Fin15AnchoredAtom2129 chi ∧
      ¬Fin15AnchoredAtom2131 chi ∧
      ¬Fin15AnchoredAtom2147 chi ∧
      ¬Fin15AnchoredAtom2149 chi ∧
      ¬Fin15AnchoredAtom2153 chi ∧
      ¬Fin15AnchoredAtom2256 chi ∧
      ¬Fin15AnchoredAtom2258 chi ∧
      ¬Fin15AnchoredAtom2262 chi ∧
      ¬Fin15AnchoredAtom2308 chi ∧
      ¬Fin15AnchoredAtom2421 chi ∧
      ¬Fin15AnchoredAtom2423 chi ∧
      ¬Fin15AnchoredAtom2427 chi ∧
      ¬Fin15AnchoredAtom2473 chi ∧
      ¬Fin15AnchoredAtom2733 chi ∧
      ¬Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom2864 chi ∧
      ¬Fin15AnchoredAtom2868 chi ∧
      ¬Fin15AnchoredAtom2971 chi ∧
      ¬Fin15AnchoredAtom2973 chi ∧
      ¬Fin15AnchoredAtom2977 chi ∧
      ¬Fin15AnchoredAtom3023 chi ∧
      ¬Fin15AnchoredAtom3136 chi ∧
      ¬Fin15AnchoredAtom3138 chi ∧
      ¬Fin15AnchoredAtom3142 chi ∧
      ¬Fin15AnchoredAtom3188 chi ∧
      ¬Fin15AnchoredAtom3448 chi ∧
      ¬Fin15AnchoredAtom3631 chi ∧
      ¬Fin15AnchoredAtom3633 chi ∧
      ¬Fin15AnchoredAtom3637 chi ∧
      ¬Fin15AnchoredAtom3683 chi ∧
      ¬Fin15AnchoredAtom3943 chi ∧
      ¬Fin15AnchoredAtom4273 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 6, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05711
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1823 Fin15AnchoredAtom1826 Fin15AnchoredAtom1827
    Fin15AnchoredAtom1829 Fin15AnchoredAtom1853 Fin15AnchoredAtom1854 Fin15AnchoredAtom1856
    Fin15AnchoredAtom1872 Fin15AnchoredAtom1874 Fin15AnchoredAtom1878 Fin15AnchoredAtom1908
    Fin15AnchoredAtom1909 Fin15AnchoredAtom1911 Fin15AnchoredAtom1927 Fin15AnchoredAtom1929
    Fin15AnchoredAtom1933 Fin15AnchoredAtom2036 Fin15AnchoredAtom2038 Fin15AnchoredAtom2042
    Fin15AnchoredAtom2088 Fin15AnchoredAtom2128 Fin15AnchoredAtom2129 Fin15AnchoredAtom2131
    Fin15AnchoredAtom2147 Fin15AnchoredAtom2149 Fin15AnchoredAtom2153 Fin15AnchoredAtom2256
    Fin15AnchoredAtom2258 Fin15AnchoredAtom2262 Fin15AnchoredAtom2308 Fin15AnchoredAtom2421
    Fin15AnchoredAtom2423 Fin15AnchoredAtom2427 Fin15AnchoredAtom2473 Fin15AnchoredAtom2733
    Fin15AnchoredAtom2843 Fin15AnchoredAtom2844 Fin15AnchoredAtom2846 Fin15AnchoredAtom2862
    Fin15AnchoredAtom2864 Fin15AnchoredAtom2868 Fin15AnchoredAtom2971 Fin15AnchoredAtom2973
    Fin15AnchoredAtom2977 Fin15AnchoredAtom3023 Fin15AnchoredAtom3136 Fin15AnchoredAtom3138
    Fin15AnchoredAtom3142 Fin15AnchoredAtom3188 Fin15AnchoredAtom3448 Fin15AnchoredAtom3631
    Fin15AnchoredAtom3633 Fin15AnchoredAtom3637 Fin15AnchoredAtom3683 Fin15AnchoredAtom3943
    Fin15AnchoredAtom4273 at hbad
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

theorem fin15Anchored_clause30607 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom2036 chi ∧
      ¬Fin15AnchoredAtom2039 chi ∧
      ¬Fin15AnchoredAtom2043 chi ∧
      ¬Fin15AnchoredAtom2089 chi ∧
      ¬Fin15AnchoredAtom2128 chi ∧
      ¬Fin15AnchoredAtom2129 chi ∧
      ¬Fin15AnchoredAtom2132 chi ∧
      ¬Fin15AnchoredAtom2147 chi ∧
      ¬Fin15AnchoredAtom2150 chi ∧
      ¬Fin15AnchoredAtom2154 chi ∧
      ¬Fin15AnchoredAtom2256 chi ∧
      ¬Fin15AnchoredAtom2259 chi ∧
      ¬Fin15AnchoredAtom2263 chi ∧
      ¬Fin15AnchoredAtom2309 chi ∧
      ¬Fin15AnchoredAtom2421 chi ∧
      ¬Fin15AnchoredAtom2424 chi ∧
      ¬Fin15AnchoredAtom2428 chi ∧
      ¬Fin15AnchoredAtom2474 chi ∧
      ¬Fin15AnchoredAtom2734 chi ∧
      ¬Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom2865 chi ∧
      ¬Fin15AnchoredAtom2869 chi ∧
      ¬Fin15AnchoredAtom2971 chi ∧
      ¬Fin15AnchoredAtom2974 chi ∧
      ¬Fin15AnchoredAtom2978 chi ∧
      ¬Fin15AnchoredAtom3024 chi ∧
      ¬Fin15AnchoredAtom3136 chi ∧
      ¬Fin15AnchoredAtom3139 chi ∧
      ¬Fin15AnchoredAtom3143 chi ∧
      ¬Fin15AnchoredAtom3189 chi ∧
      ¬Fin15AnchoredAtom3449 chi ∧
      ¬Fin15AnchoredAtom3631 chi ∧
      ¬Fin15AnchoredAtom3634 chi ∧
      ¬Fin15AnchoredAtom3638 chi ∧
      ¬Fin15AnchoredAtom3684 chi ∧
      ¬Fin15AnchoredAtom3944 chi ∧
      ¬Fin15AnchoredAtom4274 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 6, 9, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09807
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1823 Fin15AnchoredAtom1826 Fin15AnchoredAtom1827
    Fin15AnchoredAtom1830 Fin15AnchoredAtom1853 Fin15AnchoredAtom1854 Fin15AnchoredAtom1857
    Fin15AnchoredAtom1872 Fin15AnchoredAtom1875 Fin15AnchoredAtom1879 Fin15AnchoredAtom1908
    Fin15AnchoredAtom1909 Fin15AnchoredAtom1912 Fin15AnchoredAtom1927 Fin15AnchoredAtom1930
    Fin15AnchoredAtom1934 Fin15AnchoredAtom2036 Fin15AnchoredAtom2039 Fin15AnchoredAtom2043
    Fin15AnchoredAtom2089 Fin15AnchoredAtom2128 Fin15AnchoredAtom2129 Fin15AnchoredAtom2132
    Fin15AnchoredAtom2147 Fin15AnchoredAtom2150 Fin15AnchoredAtom2154 Fin15AnchoredAtom2256
    Fin15AnchoredAtom2259 Fin15AnchoredAtom2263 Fin15AnchoredAtom2309 Fin15AnchoredAtom2421
    Fin15AnchoredAtom2424 Fin15AnchoredAtom2428 Fin15AnchoredAtom2474 Fin15AnchoredAtom2734
    Fin15AnchoredAtom2843 Fin15AnchoredAtom2844 Fin15AnchoredAtom2847 Fin15AnchoredAtom2862
    Fin15AnchoredAtom2865 Fin15AnchoredAtom2869 Fin15AnchoredAtom2971 Fin15AnchoredAtom2974
    Fin15AnchoredAtom2978 Fin15AnchoredAtom3024 Fin15AnchoredAtom3136 Fin15AnchoredAtom3139
    Fin15AnchoredAtom3143 Fin15AnchoredAtom3189 Fin15AnchoredAtom3449 Fin15AnchoredAtom3631
    Fin15AnchoredAtom3634 Fin15AnchoredAtom3638 Fin15AnchoredAtom3684 Fin15AnchoredAtom3944
    Fin15AnchoredAtom4274 at hbad
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

theorem fin15Anchored_clause30608 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom1935 chi ∧
      ¬Fin15AnchoredAtom2036 chi ∧
      ¬Fin15AnchoredAtom2040 chi ∧
      ¬Fin15AnchoredAtom2044 chi ∧
      ¬Fin15AnchoredAtom2090 chi ∧
      ¬Fin15AnchoredAtom2128 chi ∧
      ¬Fin15AnchoredAtom2129 chi ∧
      ¬Fin15AnchoredAtom2133 chi ∧
      ¬Fin15AnchoredAtom2147 chi ∧
      ¬Fin15AnchoredAtom2151 chi ∧
      ¬Fin15AnchoredAtom2155 chi ∧
      ¬Fin15AnchoredAtom2256 chi ∧
      ¬Fin15AnchoredAtom2260 chi ∧
      ¬Fin15AnchoredAtom2264 chi ∧
      ¬Fin15AnchoredAtom2310 chi ∧
      ¬Fin15AnchoredAtom2421 chi ∧
      ¬Fin15AnchoredAtom2425 chi ∧
      ¬Fin15AnchoredAtom2429 chi ∧
      ¬Fin15AnchoredAtom2475 chi ∧
      ¬Fin15AnchoredAtom2735 chi ∧
      ¬Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom2866 chi ∧
      ¬Fin15AnchoredAtom2870 chi ∧
      ¬Fin15AnchoredAtom2971 chi ∧
      ¬Fin15AnchoredAtom2975 chi ∧
      ¬Fin15AnchoredAtom2979 chi ∧
      ¬Fin15AnchoredAtom3025 chi ∧
      ¬Fin15AnchoredAtom3136 chi ∧
      ¬Fin15AnchoredAtom3140 chi ∧
      ¬Fin15AnchoredAtom3144 chi ∧
      ¬Fin15AnchoredAtom3190 chi ∧
      ¬Fin15AnchoredAtom3450 chi ∧
      ¬Fin15AnchoredAtom3631 chi ∧
      ¬Fin15AnchoredAtom3635 chi ∧
      ¬Fin15AnchoredAtom3639 chi ∧
      ¬Fin15AnchoredAtom3685 chi ∧
      ¬Fin15AnchoredAtom3945 chi ∧
      ¬Fin15AnchoredAtom4275 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 6, 9, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17999
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1823 Fin15AnchoredAtom1826 Fin15AnchoredAtom1827
    Fin15AnchoredAtom1831 Fin15AnchoredAtom1853 Fin15AnchoredAtom1854 Fin15AnchoredAtom1858
    Fin15AnchoredAtom1872 Fin15AnchoredAtom1876 Fin15AnchoredAtom1880 Fin15AnchoredAtom1908
    Fin15AnchoredAtom1909 Fin15AnchoredAtom1913 Fin15AnchoredAtom1927 Fin15AnchoredAtom1931
    Fin15AnchoredAtom1935 Fin15AnchoredAtom2036 Fin15AnchoredAtom2040 Fin15AnchoredAtom2044
    Fin15AnchoredAtom2090 Fin15AnchoredAtom2128 Fin15AnchoredAtom2129 Fin15AnchoredAtom2133
    Fin15AnchoredAtom2147 Fin15AnchoredAtom2151 Fin15AnchoredAtom2155 Fin15AnchoredAtom2256
    Fin15AnchoredAtom2260 Fin15AnchoredAtom2264 Fin15AnchoredAtom2310 Fin15AnchoredAtom2421
    Fin15AnchoredAtom2425 Fin15AnchoredAtom2429 Fin15AnchoredAtom2475 Fin15AnchoredAtom2735
    Fin15AnchoredAtom2843 Fin15AnchoredAtom2844 Fin15AnchoredAtom2848 Fin15AnchoredAtom2862
    Fin15AnchoredAtom2866 Fin15AnchoredAtom2870 Fin15AnchoredAtom2971 Fin15AnchoredAtom2975
    Fin15AnchoredAtom2979 Fin15AnchoredAtom3025 Fin15AnchoredAtom3136 Fin15AnchoredAtom3140
    Fin15AnchoredAtom3144 Fin15AnchoredAtom3190 Fin15AnchoredAtom3450 Fin15AnchoredAtom3631
    Fin15AnchoredAtom3635 Fin15AnchoredAtom3639 Fin15AnchoredAtom3685 Fin15AnchoredAtom3945
    Fin15AnchoredAtom4275 at hbad
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

theorem fin15Anchored_clause30609 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1939 chi ∧
      ¬Fin15AnchoredAtom2038 chi ∧
      ¬Fin15AnchoredAtom2039 chi ∧
      ¬Fin15AnchoredAtom2048 chi ∧
      ¬Fin15AnchoredAtom2094 chi ∧
      ¬Fin15AnchoredAtom2128 chi ∧
      ¬Fin15AnchoredAtom2131 chi ∧
      ¬Fin15AnchoredAtom2132 chi ∧
      ¬Fin15AnchoredAtom2149 chi ∧
      ¬Fin15AnchoredAtom2150 chi ∧
      ¬Fin15AnchoredAtom2159 chi ∧
      ¬Fin15AnchoredAtom2258 chi ∧
      ¬Fin15AnchoredAtom2259 chi ∧
      ¬Fin15AnchoredAtom2268 chi ∧
      ¬Fin15AnchoredAtom2314 chi ∧
      ¬Fin15AnchoredAtom2423 chi ∧
      ¬Fin15AnchoredAtom2424 chi ∧
      ¬Fin15AnchoredAtom2433 chi ∧
      ¬Fin15AnchoredAtom2479 chi ∧
      ¬Fin15AnchoredAtom2739 chi ∧
      ¬Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom2864 chi ∧
      ¬Fin15AnchoredAtom2865 chi ∧
      ¬Fin15AnchoredAtom2874 chi ∧
      ¬Fin15AnchoredAtom2973 chi ∧
      ¬Fin15AnchoredAtom2974 chi ∧
      ¬Fin15AnchoredAtom2983 chi ∧
      ¬Fin15AnchoredAtom3029 chi ∧
      ¬Fin15AnchoredAtom3138 chi ∧
      ¬Fin15AnchoredAtom3139 chi ∧
      ¬Fin15AnchoredAtom3148 chi ∧
      ¬Fin15AnchoredAtom3194 chi ∧
      ¬Fin15AnchoredAtom3454 chi ∧
      ¬Fin15AnchoredAtom3633 chi ∧
      ¬Fin15AnchoredAtom3634 chi ∧
      ¬Fin15AnchoredAtom3643 chi ∧
      ¬Fin15AnchoredAtom3689 chi ∧
      ¬Fin15AnchoredAtom3949 chi ∧
      ¬Fin15AnchoredAtom4279 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 6, 9, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask12879
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1823 Fin15AnchoredAtom1826 Fin15AnchoredAtom1829
    Fin15AnchoredAtom1830 Fin15AnchoredAtom1853 Fin15AnchoredAtom1856 Fin15AnchoredAtom1857
    Fin15AnchoredAtom1874 Fin15AnchoredAtom1875 Fin15AnchoredAtom1884 Fin15AnchoredAtom1908
    Fin15AnchoredAtom1911 Fin15AnchoredAtom1912 Fin15AnchoredAtom1929 Fin15AnchoredAtom1930
    Fin15AnchoredAtom1939 Fin15AnchoredAtom2038 Fin15AnchoredAtom2039 Fin15AnchoredAtom2048
    Fin15AnchoredAtom2094 Fin15AnchoredAtom2128 Fin15AnchoredAtom2131 Fin15AnchoredAtom2132
    Fin15AnchoredAtom2149 Fin15AnchoredAtom2150 Fin15AnchoredAtom2159 Fin15AnchoredAtom2258
    Fin15AnchoredAtom2259 Fin15AnchoredAtom2268 Fin15AnchoredAtom2314 Fin15AnchoredAtom2423
    Fin15AnchoredAtom2424 Fin15AnchoredAtom2433 Fin15AnchoredAtom2479 Fin15AnchoredAtom2739
    Fin15AnchoredAtom2843 Fin15AnchoredAtom2846 Fin15AnchoredAtom2847 Fin15AnchoredAtom2864
    Fin15AnchoredAtom2865 Fin15AnchoredAtom2874 Fin15AnchoredAtom2973 Fin15AnchoredAtom2974
    Fin15AnchoredAtom2983 Fin15AnchoredAtom3029 Fin15AnchoredAtom3138 Fin15AnchoredAtom3139
    Fin15AnchoredAtom3148 Fin15AnchoredAtom3194 Fin15AnchoredAtom3454 Fin15AnchoredAtom3633
    Fin15AnchoredAtom3634 Fin15AnchoredAtom3643 Fin15AnchoredAtom3689 Fin15AnchoredAtom3949
    Fin15AnchoredAtom4279 at hbad
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

theorem fin15Anchored_clause30610 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom1940 chi ∧
      ¬Fin15AnchoredAtom2038 chi ∧
      ¬Fin15AnchoredAtom2040 chi ∧
      ¬Fin15AnchoredAtom2049 chi ∧
      ¬Fin15AnchoredAtom2095 chi ∧
      ¬Fin15AnchoredAtom2128 chi ∧
      ¬Fin15AnchoredAtom2131 chi ∧
      ¬Fin15AnchoredAtom2133 chi ∧
      ¬Fin15AnchoredAtom2149 chi ∧
      ¬Fin15AnchoredAtom2151 chi ∧
      ¬Fin15AnchoredAtom2160 chi ∧
      ¬Fin15AnchoredAtom2258 chi ∧
      ¬Fin15AnchoredAtom2260 chi ∧
      ¬Fin15AnchoredAtom2269 chi ∧
      ¬Fin15AnchoredAtom2315 chi ∧
      ¬Fin15AnchoredAtom2423 chi ∧
      ¬Fin15AnchoredAtom2425 chi ∧
      ¬Fin15AnchoredAtom2434 chi ∧
      ¬Fin15AnchoredAtom2480 chi ∧
      ¬Fin15AnchoredAtom2740 chi ∧
      ¬Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom2864 chi ∧
      ¬Fin15AnchoredAtom2866 chi ∧
      ¬Fin15AnchoredAtom2875 chi ∧
      ¬Fin15AnchoredAtom2973 chi ∧
      ¬Fin15AnchoredAtom2975 chi ∧
      ¬Fin15AnchoredAtom2984 chi ∧
      ¬Fin15AnchoredAtom3030 chi ∧
      ¬Fin15AnchoredAtom3138 chi ∧
      ¬Fin15AnchoredAtom3140 chi ∧
      ¬Fin15AnchoredAtom3149 chi ∧
      ¬Fin15AnchoredAtom3195 chi ∧
      ¬Fin15AnchoredAtom3455 chi ∧
      ¬Fin15AnchoredAtom3633 chi ∧
      ¬Fin15AnchoredAtom3635 chi ∧
      ¬Fin15AnchoredAtom3644 chi ∧
      ¬Fin15AnchoredAtom3690 chi ∧
      ¬Fin15AnchoredAtom3950 chi ∧
      ¬Fin15AnchoredAtom4280 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 6, 9, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21071
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1823 Fin15AnchoredAtom1826 Fin15AnchoredAtom1829
    Fin15AnchoredAtom1831 Fin15AnchoredAtom1853 Fin15AnchoredAtom1856 Fin15AnchoredAtom1858
    Fin15AnchoredAtom1874 Fin15AnchoredAtom1876 Fin15AnchoredAtom1885 Fin15AnchoredAtom1908
    Fin15AnchoredAtom1911 Fin15AnchoredAtom1913 Fin15AnchoredAtom1929 Fin15AnchoredAtom1931
    Fin15AnchoredAtom1940 Fin15AnchoredAtom2038 Fin15AnchoredAtom2040 Fin15AnchoredAtom2049
    Fin15AnchoredAtom2095 Fin15AnchoredAtom2128 Fin15AnchoredAtom2131 Fin15AnchoredAtom2133
    Fin15AnchoredAtom2149 Fin15AnchoredAtom2151 Fin15AnchoredAtom2160 Fin15AnchoredAtom2258
    Fin15AnchoredAtom2260 Fin15AnchoredAtom2269 Fin15AnchoredAtom2315 Fin15AnchoredAtom2423
    Fin15AnchoredAtom2425 Fin15AnchoredAtom2434 Fin15AnchoredAtom2480 Fin15AnchoredAtom2740
    Fin15AnchoredAtom2843 Fin15AnchoredAtom2846 Fin15AnchoredAtom2848 Fin15AnchoredAtom2864
    Fin15AnchoredAtom2866 Fin15AnchoredAtom2875 Fin15AnchoredAtom2973 Fin15AnchoredAtom2975
    Fin15AnchoredAtom2984 Fin15AnchoredAtom3030 Fin15AnchoredAtom3138 Fin15AnchoredAtom3140
    Fin15AnchoredAtom3149 Fin15AnchoredAtom3195 Fin15AnchoredAtom3455 Fin15AnchoredAtom3633
    Fin15AnchoredAtom3635 Fin15AnchoredAtom3644 Fin15AnchoredAtom3690 Fin15AnchoredAtom3950
    Fin15AnchoredAtom4280 at hbad
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

theorem fin15Anchored_clause30611 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom1886 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
      ¬Fin15AnchoredAtom2039 chi ∧
      ¬Fin15AnchoredAtom2040 chi ∧
      ¬Fin15AnchoredAtom2050 chi ∧
      ¬Fin15AnchoredAtom2096 chi ∧
      ¬Fin15AnchoredAtom2128 chi ∧
      ¬Fin15AnchoredAtom2132 chi ∧
      ¬Fin15AnchoredAtom2133 chi ∧
      ¬Fin15AnchoredAtom2150 chi ∧
      ¬Fin15AnchoredAtom2151 chi ∧
      ¬Fin15AnchoredAtom2161 chi ∧
      ¬Fin15AnchoredAtom2259 chi ∧
      ¬Fin15AnchoredAtom2260 chi ∧
      ¬Fin15AnchoredAtom2270 chi ∧
      ¬Fin15AnchoredAtom2316 chi ∧
      ¬Fin15AnchoredAtom2424 chi ∧
      ¬Fin15AnchoredAtom2425 chi ∧
      ¬Fin15AnchoredAtom2435 chi ∧
      ¬Fin15AnchoredAtom2481 chi ∧
      ¬Fin15AnchoredAtom2741 chi ∧
      ¬Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom2865 chi ∧
      ¬Fin15AnchoredAtom2866 chi ∧
      ¬Fin15AnchoredAtom2876 chi ∧
      ¬Fin15AnchoredAtom2974 chi ∧
      ¬Fin15AnchoredAtom2975 chi ∧
      ¬Fin15AnchoredAtom2985 chi ∧
      ¬Fin15AnchoredAtom3031 chi ∧
      ¬Fin15AnchoredAtom3139 chi ∧
      ¬Fin15AnchoredAtom3140 chi ∧
      ¬Fin15AnchoredAtom3150 chi ∧
      ¬Fin15AnchoredAtom3196 chi ∧
      ¬Fin15AnchoredAtom3456 chi ∧
      ¬Fin15AnchoredAtom3634 chi ∧
      ¬Fin15AnchoredAtom3635 chi ∧
      ¬Fin15AnchoredAtom3645 chi ∧
      ¬Fin15AnchoredAtom3691 chi ∧
      ¬Fin15AnchoredAtom3951 chi ∧
      ¬Fin15AnchoredAtom4281 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 6, 9, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25167
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1823 Fin15AnchoredAtom1826 Fin15AnchoredAtom1830
    Fin15AnchoredAtom1831 Fin15AnchoredAtom1853 Fin15AnchoredAtom1857 Fin15AnchoredAtom1858
    Fin15AnchoredAtom1875 Fin15AnchoredAtom1876 Fin15AnchoredAtom1886 Fin15AnchoredAtom1908
    Fin15AnchoredAtom1912 Fin15AnchoredAtom1913 Fin15AnchoredAtom1930 Fin15AnchoredAtom1931
    Fin15AnchoredAtom1941 Fin15AnchoredAtom2039 Fin15AnchoredAtom2040 Fin15AnchoredAtom2050
    Fin15AnchoredAtom2096 Fin15AnchoredAtom2128 Fin15AnchoredAtom2132 Fin15AnchoredAtom2133
    Fin15AnchoredAtom2150 Fin15AnchoredAtom2151 Fin15AnchoredAtom2161 Fin15AnchoredAtom2259
    Fin15AnchoredAtom2260 Fin15AnchoredAtom2270 Fin15AnchoredAtom2316 Fin15AnchoredAtom2424
    Fin15AnchoredAtom2425 Fin15AnchoredAtom2435 Fin15AnchoredAtom2481 Fin15AnchoredAtom2741
    Fin15AnchoredAtom2843 Fin15AnchoredAtom2847 Fin15AnchoredAtom2848 Fin15AnchoredAtom2865
    Fin15AnchoredAtom2866 Fin15AnchoredAtom2876 Fin15AnchoredAtom2974 Fin15AnchoredAtom2975
    Fin15AnchoredAtom2985 Fin15AnchoredAtom3031 Fin15AnchoredAtom3139 Fin15AnchoredAtom3140
    Fin15AnchoredAtom3150 Fin15AnchoredAtom3196 Fin15AnchoredAtom3456 Fin15AnchoredAtom3634
    Fin15AnchoredAtom3635 Fin15AnchoredAtom3645 Fin15AnchoredAtom3691 Fin15AnchoredAtom3951
    Fin15AnchoredAtom4281 at hbad
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

theorem fin15Anchored_clause30612 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom1939 chi ∧
      ¬Fin15AnchoredAtom2042 chi ∧
      ¬Fin15AnchoredAtom2043 chi ∧
      ¬Fin15AnchoredAtom2048 chi ∧
      ¬Fin15AnchoredAtom2100 chi ∧
      ¬Fin15AnchoredAtom2129 chi ∧
      ¬Fin15AnchoredAtom2131 chi ∧
      ¬Fin15AnchoredAtom2132 chi ∧
      ¬Fin15AnchoredAtom2153 chi ∧
      ¬Fin15AnchoredAtom2154 chi ∧
      ¬Fin15AnchoredAtom2159 chi ∧
      ¬Fin15AnchoredAtom2262 chi ∧
      ¬Fin15AnchoredAtom2263 chi ∧
      ¬Fin15AnchoredAtom2268 chi ∧
      ¬Fin15AnchoredAtom2320 chi ∧
      ¬Fin15AnchoredAtom2427 chi ∧
      ¬Fin15AnchoredAtom2428 chi ∧
      ¬Fin15AnchoredAtom2433 chi ∧
      ¬Fin15AnchoredAtom2485 chi ∧
      ¬Fin15AnchoredAtom2745 chi ∧
      ¬Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom2868 chi ∧
      ¬Fin15AnchoredAtom2869 chi ∧
      ¬Fin15AnchoredAtom2874 chi ∧
      ¬Fin15AnchoredAtom2977 chi ∧
      ¬Fin15AnchoredAtom2978 chi ∧
      ¬Fin15AnchoredAtom2983 chi ∧
      ¬Fin15AnchoredAtom3035 chi ∧
      ¬Fin15AnchoredAtom3142 chi ∧
      ¬Fin15AnchoredAtom3143 chi ∧
      ¬Fin15AnchoredAtom3148 chi ∧
      ¬Fin15AnchoredAtom3200 chi ∧
      ¬Fin15AnchoredAtom3460 chi ∧
      ¬Fin15AnchoredAtom3637 chi ∧
      ¬Fin15AnchoredAtom3638 chi ∧
      ¬Fin15AnchoredAtom3643 chi ∧
      ¬Fin15AnchoredAtom3695 chi ∧
      ¬Fin15AnchoredAtom3955 chi ∧
      ¬Fin15AnchoredAtom4285 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 6, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13391
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1823 Fin15AnchoredAtom1827 Fin15AnchoredAtom1829
    Fin15AnchoredAtom1830 Fin15AnchoredAtom1854 Fin15AnchoredAtom1856 Fin15AnchoredAtom1857
    Fin15AnchoredAtom1878 Fin15AnchoredAtom1879 Fin15AnchoredAtom1884 Fin15AnchoredAtom1909
    Fin15AnchoredAtom1911 Fin15AnchoredAtom1912 Fin15AnchoredAtom1933 Fin15AnchoredAtom1934
    Fin15AnchoredAtom1939 Fin15AnchoredAtom2042 Fin15AnchoredAtom2043 Fin15AnchoredAtom2048
    Fin15AnchoredAtom2100 Fin15AnchoredAtom2129 Fin15AnchoredAtom2131 Fin15AnchoredAtom2132
    Fin15AnchoredAtom2153 Fin15AnchoredAtom2154 Fin15AnchoredAtom2159 Fin15AnchoredAtom2262
    Fin15AnchoredAtom2263 Fin15AnchoredAtom2268 Fin15AnchoredAtom2320 Fin15AnchoredAtom2427
    Fin15AnchoredAtom2428 Fin15AnchoredAtom2433 Fin15AnchoredAtom2485 Fin15AnchoredAtom2745
    Fin15AnchoredAtom2844 Fin15AnchoredAtom2846 Fin15AnchoredAtom2847 Fin15AnchoredAtom2868
    Fin15AnchoredAtom2869 Fin15AnchoredAtom2874 Fin15AnchoredAtom2977 Fin15AnchoredAtom2978
    Fin15AnchoredAtom2983 Fin15AnchoredAtom3035 Fin15AnchoredAtom3142 Fin15AnchoredAtom3143
    Fin15AnchoredAtom3148 Fin15AnchoredAtom3200 Fin15AnchoredAtom3460 Fin15AnchoredAtom3637
    Fin15AnchoredAtom3638 Fin15AnchoredAtom3643 Fin15AnchoredAtom3695 Fin15AnchoredAtom3955
    Fin15AnchoredAtom4285 at hbad
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

theorem fin15Anchored_clause30613 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom1935 chi ∧
      ¬Fin15AnchoredAtom1940 chi ∧
      ¬Fin15AnchoredAtom2042 chi ∧
      ¬Fin15AnchoredAtom2044 chi ∧
      ¬Fin15AnchoredAtom2049 chi ∧
      ¬Fin15AnchoredAtom2101 chi ∧
      ¬Fin15AnchoredAtom2129 chi ∧
      ¬Fin15AnchoredAtom2131 chi ∧
      ¬Fin15AnchoredAtom2133 chi ∧
      ¬Fin15AnchoredAtom2153 chi ∧
      ¬Fin15AnchoredAtom2155 chi ∧
      ¬Fin15AnchoredAtom2160 chi ∧
      ¬Fin15AnchoredAtom2262 chi ∧
      ¬Fin15AnchoredAtom2264 chi ∧
      ¬Fin15AnchoredAtom2269 chi ∧
      ¬Fin15AnchoredAtom2321 chi ∧
      ¬Fin15AnchoredAtom2427 chi ∧
      ¬Fin15AnchoredAtom2429 chi ∧
      ¬Fin15AnchoredAtom2434 chi ∧
      ¬Fin15AnchoredAtom2486 chi ∧
      ¬Fin15AnchoredAtom2746 chi ∧
      ¬Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom2868 chi ∧
      ¬Fin15AnchoredAtom2870 chi ∧
      ¬Fin15AnchoredAtom2875 chi ∧
      ¬Fin15AnchoredAtom2977 chi ∧
      ¬Fin15AnchoredAtom2979 chi ∧
      ¬Fin15AnchoredAtom2984 chi ∧
      ¬Fin15AnchoredAtom3036 chi ∧
      ¬Fin15AnchoredAtom3142 chi ∧
      ¬Fin15AnchoredAtom3144 chi ∧
      ¬Fin15AnchoredAtom3149 chi ∧
      ¬Fin15AnchoredAtom3201 chi ∧
      ¬Fin15AnchoredAtom3461 chi ∧
      ¬Fin15AnchoredAtom3637 chi ∧
      ¬Fin15AnchoredAtom3639 chi ∧
      ¬Fin15AnchoredAtom3644 chi ∧
      ¬Fin15AnchoredAtom3696 chi ∧
      ¬Fin15AnchoredAtom3956 chi ∧
      ¬Fin15AnchoredAtom4286 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 6, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21583
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1823 Fin15AnchoredAtom1827 Fin15AnchoredAtom1829
    Fin15AnchoredAtom1831 Fin15AnchoredAtom1854 Fin15AnchoredAtom1856 Fin15AnchoredAtom1858
    Fin15AnchoredAtom1878 Fin15AnchoredAtom1880 Fin15AnchoredAtom1885 Fin15AnchoredAtom1909
    Fin15AnchoredAtom1911 Fin15AnchoredAtom1913 Fin15AnchoredAtom1933 Fin15AnchoredAtom1935
    Fin15AnchoredAtom1940 Fin15AnchoredAtom2042 Fin15AnchoredAtom2044 Fin15AnchoredAtom2049
    Fin15AnchoredAtom2101 Fin15AnchoredAtom2129 Fin15AnchoredAtom2131 Fin15AnchoredAtom2133
    Fin15AnchoredAtom2153 Fin15AnchoredAtom2155 Fin15AnchoredAtom2160 Fin15AnchoredAtom2262
    Fin15AnchoredAtom2264 Fin15AnchoredAtom2269 Fin15AnchoredAtom2321 Fin15AnchoredAtom2427
    Fin15AnchoredAtom2429 Fin15AnchoredAtom2434 Fin15AnchoredAtom2486 Fin15AnchoredAtom2746
    Fin15AnchoredAtom2844 Fin15AnchoredAtom2846 Fin15AnchoredAtom2848 Fin15AnchoredAtom2868
    Fin15AnchoredAtom2870 Fin15AnchoredAtom2875 Fin15AnchoredAtom2977 Fin15AnchoredAtom2979
    Fin15AnchoredAtom2984 Fin15AnchoredAtom3036 Fin15AnchoredAtom3142 Fin15AnchoredAtom3144
    Fin15AnchoredAtom3149 Fin15AnchoredAtom3201 Fin15AnchoredAtom3461 Fin15AnchoredAtom3637
    Fin15AnchoredAtom3639 Fin15AnchoredAtom3644 Fin15AnchoredAtom3696 Fin15AnchoredAtom3956
    Fin15AnchoredAtom4286 at hbad
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

theorem fin15Anchored_clause30614 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom1886 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom1935 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
      ¬Fin15AnchoredAtom2043 chi ∧
      ¬Fin15AnchoredAtom2044 chi ∧
      ¬Fin15AnchoredAtom2050 chi ∧
      ¬Fin15AnchoredAtom2102 chi ∧
      ¬Fin15AnchoredAtom2129 chi ∧
      ¬Fin15AnchoredAtom2132 chi ∧
      ¬Fin15AnchoredAtom2133 chi ∧
      ¬Fin15AnchoredAtom2154 chi ∧
      ¬Fin15AnchoredAtom2155 chi ∧
      ¬Fin15AnchoredAtom2161 chi ∧
      ¬Fin15AnchoredAtom2263 chi ∧
      ¬Fin15AnchoredAtom2264 chi ∧
      ¬Fin15AnchoredAtom2270 chi ∧
      ¬Fin15AnchoredAtom2322 chi ∧
      ¬Fin15AnchoredAtom2428 chi ∧
      ¬Fin15AnchoredAtom2429 chi ∧
      ¬Fin15AnchoredAtom2435 chi ∧
      ¬Fin15AnchoredAtom2487 chi ∧
      ¬Fin15AnchoredAtom2747 chi ∧
      ¬Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom2869 chi ∧
      ¬Fin15AnchoredAtom2870 chi ∧
      ¬Fin15AnchoredAtom2876 chi ∧
      ¬Fin15AnchoredAtom2978 chi ∧
      ¬Fin15AnchoredAtom2979 chi ∧
      ¬Fin15AnchoredAtom2985 chi ∧
      ¬Fin15AnchoredAtom3037 chi ∧
      ¬Fin15AnchoredAtom3143 chi ∧
      ¬Fin15AnchoredAtom3144 chi ∧
      ¬Fin15AnchoredAtom3150 chi ∧
      ¬Fin15AnchoredAtom3202 chi ∧
      ¬Fin15AnchoredAtom3462 chi ∧
      ¬Fin15AnchoredAtom3638 chi ∧
      ¬Fin15AnchoredAtom3639 chi ∧
      ¬Fin15AnchoredAtom3645 chi ∧
      ¬Fin15AnchoredAtom3697 chi ∧
      ¬Fin15AnchoredAtom3957 chi ∧
      ¬Fin15AnchoredAtom4287 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 6, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25679
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1823 Fin15AnchoredAtom1827 Fin15AnchoredAtom1830
    Fin15AnchoredAtom1831 Fin15AnchoredAtom1854 Fin15AnchoredAtom1857 Fin15AnchoredAtom1858
    Fin15AnchoredAtom1879 Fin15AnchoredAtom1880 Fin15AnchoredAtom1886 Fin15AnchoredAtom1909
    Fin15AnchoredAtom1912 Fin15AnchoredAtom1913 Fin15AnchoredAtom1934 Fin15AnchoredAtom1935
    Fin15AnchoredAtom1941 Fin15AnchoredAtom2043 Fin15AnchoredAtom2044 Fin15AnchoredAtom2050
    Fin15AnchoredAtom2102 Fin15AnchoredAtom2129 Fin15AnchoredAtom2132 Fin15AnchoredAtom2133
    Fin15AnchoredAtom2154 Fin15AnchoredAtom2155 Fin15AnchoredAtom2161 Fin15AnchoredAtom2263
    Fin15AnchoredAtom2264 Fin15AnchoredAtom2270 Fin15AnchoredAtom2322 Fin15AnchoredAtom2428
    Fin15AnchoredAtom2429 Fin15AnchoredAtom2435 Fin15AnchoredAtom2487 Fin15AnchoredAtom2747
    Fin15AnchoredAtom2844 Fin15AnchoredAtom2847 Fin15AnchoredAtom2848 Fin15AnchoredAtom2869
    Fin15AnchoredAtom2870 Fin15AnchoredAtom2876 Fin15AnchoredAtom2978 Fin15AnchoredAtom2979
    Fin15AnchoredAtom2985 Fin15AnchoredAtom3037 Fin15AnchoredAtom3143 Fin15AnchoredAtom3144
    Fin15AnchoredAtom3150 Fin15AnchoredAtom3202 Fin15AnchoredAtom3462 Fin15AnchoredAtom3638
    Fin15AnchoredAtom3639 Fin15AnchoredAtom3645 Fin15AnchoredAtom3697 Fin15AnchoredAtom3957
    Fin15AnchoredAtom4287 at hbad
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

theorem fin15Anchored_clause30615 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom1886 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1939 chi ∧
      ¬Fin15AnchoredAtom1940 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
      ¬Fin15AnchoredAtom2048 chi ∧
      ¬Fin15AnchoredAtom2049 chi ∧
      ¬Fin15AnchoredAtom2050 chi ∧
      ¬Fin15AnchoredAtom2106 chi ∧
      ¬Fin15AnchoredAtom2131 chi ∧
      ¬Fin15AnchoredAtom2132 chi ∧
      ¬Fin15AnchoredAtom2133 chi ∧
      ¬Fin15AnchoredAtom2159 chi ∧
      ¬Fin15AnchoredAtom2160 chi ∧
      ¬Fin15AnchoredAtom2161 chi ∧
      ¬Fin15AnchoredAtom2268 chi ∧
      ¬Fin15AnchoredAtom2269 chi ∧
      ¬Fin15AnchoredAtom2270 chi ∧
      ¬Fin15AnchoredAtom2326 chi ∧
      ¬Fin15AnchoredAtom2433 chi ∧
      ¬Fin15AnchoredAtom2434 chi ∧
      ¬Fin15AnchoredAtom2435 chi ∧
      ¬Fin15AnchoredAtom2491 chi ∧
      ¬Fin15AnchoredAtom2751 chi ∧
      ¬Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom2874 chi ∧
      ¬Fin15AnchoredAtom2875 chi ∧
      ¬Fin15AnchoredAtom2876 chi ∧
      ¬Fin15AnchoredAtom2983 chi ∧
      ¬Fin15AnchoredAtom2984 chi ∧
      ¬Fin15AnchoredAtom2985 chi ∧
      ¬Fin15AnchoredAtom3041 chi ∧
      ¬Fin15AnchoredAtom3148 chi ∧
      ¬Fin15AnchoredAtom3149 chi ∧
      ¬Fin15AnchoredAtom3150 chi ∧
      ¬Fin15AnchoredAtom3206 chi ∧
      ¬Fin15AnchoredAtom3466 chi ∧
      ¬Fin15AnchoredAtom3643 chi ∧
      ¬Fin15AnchoredAtom3644 chi ∧
      ¬Fin15AnchoredAtom3645 chi ∧
      ¬Fin15AnchoredAtom3701 chi ∧
      ¬Fin15AnchoredAtom3961 chi ∧
      ¬Fin15AnchoredAtom4291 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 6, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask28751
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1823 Fin15AnchoredAtom1829 Fin15AnchoredAtom1830
    Fin15AnchoredAtom1831 Fin15AnchoredAtom1856 Fin15AnchoredAtom1857 Fin15AnchoredAtom1858
    Fin15AnchoredAtom1884 Fin15AnchoredAtom1885 Fin15AnchoredAtom1886 Fin15AnchoredAtom1911
    Fin15AnchoredAtom1912 Fin15AnchoredAtom1913 Fin15AnchoredAtom1939 Fin15AnchoredAtom1940
    Fin15AnchoredAtom1941 Fin15AnchoredAtom2048 Fin15AnchoredAtom2049 Fin15AnchoredAtom2050
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2131 Fin15AnchoredAtom2132 Fin15AnchoredAtom2133
    Fin15AnchoredAtom2159 Fin15AnchoredAtom2160 Fin15AnchoredAtom2161 Fin15AnchoredAtom2268
    Fin15AnchoredAtom2269 Fin15AnchoredAtom2270 Fin15AnchoredAtom2326 Fin15AnchoredAtom2433
    Fin15AnchoredAtom2434 Fin15AnchoredAtom2435 Fin15AnchoredAtom2491 Fin15AnchoredAtom2751
    Fin15AnchoredAtom2846 Fin15AnchoredAtom2847 Fin15AnchoredAtom2848 Fin15AnchoredAtom2874
    Fin15AnchoredAtom2875 Fin15AnchoredAtom2876 Fin15AnchoredAtom2983 Fin15AnchoredAtom2984
    Fin15AnchoredAtom2985 Fin15AnchoredAtom3041 Fin15AnchoredAtom3148 Fin15AnchoredAtom3149
    Fin15AnchoredAtom3150 Fin15AnchoredAtom3206 Fin15AnchoredAtom3466 Fin15AnchoredAtom3643
    Fin15AnchoredAtom3644 Fin15AnchoredAtom3645 Fin15AnchoredAtom3701 Fin15AnchoredAtom3961
    Fin15AnchoredAtom4291 at hbad
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

theorem fin15Anchored_clause30616 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom2057 chi ∧
      ¬Fin15AnchoredAtom2059 chi ∧
      ¬Fin15AnchoredAtom2063 chi ∧
      ¬Fin15AnchoredAtom2088 chi ∧
      ¬Fin15AnchoredAtom2135 chi ∧
      ¬Fin15AnchoredAtom2136 chi ∧
      ¬Fin15AnchoredAtom2138 chi ∧
      ¬Fin15AnchoredAtom2147 chi ∧
      ¬Fin15AnchoredAtom2149 chi ∧
      ¬Fin15AnchoredAtom2153 chi ∧
      ¬Fin15AnchoredAtom2277 chi ∧
      ¬Fin15AnchoredAtom2279 chi ∧
      ¬Fin15AnchoredAtom2283 chi ∧
      ¬Fin15AnchoredAtom2308 chi ∧
      ¬Fin15AnchoredAtom2442 chi ∧
      ¬Fin15AnchoredAtom2444 chi ∧
      ¬Fin15AnchoredAtom2448 chi ∧
      ¬Fin15AnchoredAtom2473 chi ∧
      ¬Fin15AnchoredAtom2768 chi ∧
      ¬Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom2864 chi ∧
      ¬Fin15AnchoredAtom2868 chi ∧
      ¬Fin15AnchoredAtom2992 chi ∧
      ¬Fin15AnchoredAtom2994 chi ∧
      ¬Fin15AnchoredAtom2998 chi ∧
      ¬Fin15AnchoredAtom3023 chi ∧
      ¬Fin15AnchoredAtom3157 chi ∧
      ¬Fin15AnchoredAtom3159 chi ∧
      ¬Fin15AnchoredAtom3163 chi ∧
      ¬Fin15AnchoredAtom3188 chi ∧
      ¬Fin15AnchoredAtom3483 chi ∧
      ¬Fin15AnchoredAtom3652 chi ∧
      ¬Fin15AnchoredAtom3654 chi ∧
      ¬Fin15AnchoredAtom3658 chi ∧
      ¬Fin15AnchoredAtom3683 chi ∧
      ¬Fin15AnchoredAtom3978 chi ∧
      ¬Fin15AnchoredAtom4308 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 7, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05775
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1824 Fin15AnchoredAtom1826 Fin15AnchoredAtom1827
    Fin15AnchoredAtom1829 Fin15AnchoredAtom1860 Fin15AnchoredAtom1861 Fin15AnchoredAtom1863
    Fin15AnchoredAtom1872 Fin15AnchoredAtom1874 Fin15AnchoredAtom1878 Fin15AnchoredAtom1915
    Fin15AnchoredAtom1916 Fin15AnchoredAtom1918 Fin15AnchoredAtom1927 Fin15AnchoredAtom1929
    Fin15AnchoredAtom1933 Fin15AnchoredAtom2057 Fin15AnchoredAtom2059 Fin15AnchoredAtom2063
    Fin15AnchoredAtom2088 Fin15AnchoredAtom2135 Fin15AnchoredAtom2136 Fin15AnchoredAtom2138
    Fin15AnchoredAtom2147 Fin15AnchoredAtom2149 Fin15AnchoredAtom2153 Fin15AnchoredAtom2277
    Fin15AnchoredAtom2279 Fin15AnchoredAtom2283 Fin15AnchoredAtom2308 Fin15AnchoredAtom2442
    Fin15AnchoredAtom2444 Fin15AnchoredAtom2448 Fin15AnchoredAtom2473 Fin15AnchoredAtom2768
    Fin15AnchoredAtom2850 Fin15AnchoredAtom2851 Fin15AnchoredAtom2853 Fin15AnchoredAtom2862
    Fin15AnchoredAtom2864 Fin15AnchoredAtom2868 Fin15AnchoredAtom2992 Fin15AnchoredAtom2994
    Fin15AnchoredAtom2998 Fin15AnchoredAtom3023 Fin15AnchoredAtom3157 Fin15AnchoredAtom3159
    Fin15AnchoredAtom3163 Fin15AnchoredAtom3188 Fin15AnchoredAtom3483 Fin15AnchoredAtom3652
    Fin15AnchoredAtom3654 Fin15AnchoredAtom3658 Fin15AnchoredAtom3683 Fin15AnchoredAtom3978
    Fin15AnchoredAtom4308 at hbad
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

theorem fin15Anchored_clause30617 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom2057 chi ∧
      ¬Fin15AnchoredAtom2060 chi ∧
      ¬Fin15AnchoredAtom2064 chi ∧
      ¬Fin15AnchoredAtom2089 chi ∧
      ¬Fin15AnchoredAtom2135 chi ∧
      ¬Fin15AnchoredAtom2136 chi ∧
      ¬Fin15AnchoredAtom2139 chi ∧
      ¬Fin15AnchoredAtom2147 chi ∧
      ¬Fin15AnchoredAtom2150 chi ∧
      ¬Fin15AnchoredAtom2154 chi ∧
      ¬Fin15AnchoredAtom2277 chi ∧
      ¬Fin15AnchoredAtom2280 chi ∧
      ¬Fin15AnchoredAtom2284 chi ∧
      ¬Fin15AnchoredAtom2309 chi ∧
      ¬Fin15AnchoredAtom2442 chi ∧
      ¬Fin15AnchoredAtom2445 chi ∧
      ¬Fin15AnchoredAtom2449 chi ∧
      ¬Fin15AnchoredAtom2474 chi ∧
      ¬Fin15AnchoredAtom2769 chi ∧
      ¬Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom2865 chi ∧
      ¬Fin15AnchoredAtom2869 chi ∧
      ¬Fin15AnchoredAtom2992 chi ∧
      ¬Fin15AnchoredAtom2995 chi ∧
      ¬Fin15AnchoredAtom2999 chi ∧
      ¬Fin15AnchoredAtom3024 chi ∧
      ¬Fin15AnchoredAtom3157 chi ∧
      ¬Fin15AnchoredAtom3160 chi ∧
      ¬Fin15AnchoredAtom3164 chi ∧
      ¬Fin15AnchoredAtom3189 chi ∧
      ¬Fin15AnchoredAtom3484 chi ∧
      ¬Fin15AnchoredAtom3652 chi ∧
      ¬Fin15AnchoredAtom3655 chi ∧
      ¬Fin15AnchoredAtom3659 chi ∧
      ¬Fin15AnchoredAtom3684 chi ∧
      ¬Fin15AnchoredAtom3979 chi ∧
      ¬Fin15AnchoredAtom4309 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 7, 9, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09871
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1824 Fin15AnchoredAtom1826 Fin15AnchoredAtom1827
    Fin15AnchoredAtom1830 Fin15AnchoredAtom1860 Fin15AnchoredAtom1861 Fin15AnchoredAtom1864
    Fin15AnchoredAtom1872 Fin15AnchoredAtom1875 Fin15AnchoredAtom1879 Fin15AnchoredAtom1915
    Fin15AnchoredAtom1916 Fin15AnchoredAtom1919 Fin15AnchoredAtom1927 Fin15AnchoredAtom1930
    Fin15AnchoredAtom1934 Fin15AnchoredAtom2057 Fin15AnchoredAtom2060 Fin15AnchoredAtom2064
    Fin15AnchoredAtom2089 Fin15AnchoredAtom2135 Fin15AnchoredAtom2136 Fin15AnchoredAtom2139
    Fin15AnchoredAtom2147 Fin15AnchoredAtom2150 Fin15AnchoredAtom2154 Fin15AnchoredAtom2277
    Fin15AnchoredAtom2280 Fin15AnchoredAtom2284 Fin15AnchoredAtom2309 Fin15AnchoredAtom2442
    Fin15AnchoredAtom2445 Fin15AnchoredAtom2449 Fin15AnchoredAtom2474 Fin15AnchoredAtom2769
    Fin15AnchoredAtom2850 Fin15AnchoredAtom2851 Fin15AnchoredAtom2854 Fin15AnchoredAtom2862
    Fin15AnchoredAtom2865 Fin15AnchoredAtom2869 Fin15AnchoredAtom2992 Fin15AnchoredAtom2995
    Fin15AnchoredAtom2999 Fin15AnchoredAtom3024 Fin15AnchoredAtom3157 Fin15AnchoredAtom3160
    Fin15AnchoredAtom3164 Fin15AnchoredAtom3189 Fin15AnchoredAtom3484 Fin15AnchoredAtom3652
    Fin15AnchoredAtom3655 Fin15AnchoredAtom3659 Fin15AnchoredAtom3684 Fin15AnchoredAtom3979
    Fin15AnchoredAtom4309 at hbad
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

theorem fin15Anchored_clause30618 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom1935 chi ∧
      ¬Fin15AnchoredAtom2057 chi ∧
      ¬Fin15AnchoredAtom2061 chi ∧
      ¬Fin15AnchoredAtom2065 chi ∧
      ¬Fin15AnchoredAtom2090 chi ∧
      ¬Fin15AnchoredAtom2135 chi ∧
      ¬Fin15AnchoredAtom2136 chi ∧
      ¬Fin15AnchoredAtom2140 chi ∧
      ¬Fin15AnchoredAtom2147 chi ∧
      ¬Fin15AnchoredAtom2151 chi ∧
      ¬Fin15AnchoredAtom2155 chi ∧
      ¬Fin15AnchoredAtom2277 chi ∧
      ¬Fin15AnchoredAtom2281 chi ∧
      ¬Fin15AnchoredAtom2285 chi ∧
      ¬Fin15AnchoredAtom2310 chi ∧
      ¬Fin15AnchoredAtom2442 chi ∧
      ¬Fin15AnchoredAtom2446 chi ∧
      ¬Fin15AnchoredAtom2450 chi ∧
      ¬Fin15AnchoredAtom2475 chi ∧
      ¬Fin15AnchoredAtom2770 chi ∧
      ¬Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom2866 chi ∧
      ¬Fin15AnchoredAtom2870 chi ∧
      ¬Fin15AnchoredAtom2992 chi ∧
      ¬Fin15AnchoredAtom2996 chi ∧
      ¬Fin15AnchoredAtom3000 chi ∧
      ¬Fin15AnchoredAtom3025 chi ∧
      ¬Fin15AnchoredAtom3157 chi ∧
      ¬Fin15AnchoredAtom3161 chi ∧
      ¬Fin15AnchoredAtom3165 chi ∧
      ¬Fin15AnchoredAtom3190 chi ∧
      ¬Fin15AnchoredAtom3485 chi ∧
      ¬Fin15AnchoredAtom3652 chi ∧
      ¬Fin15AnchoredAtom3656 chi ∧
      ¬Fin15AnchoredAtom3660 chi ∧
      ¬Fin15AnchoredAtom3685 chi ∧
      ¬Fin15AnchoredAtom3980 chi ∧
      ¬Fin15AnchoredAtom4310 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 7, 9, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask18063
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1824 Fin15AnchoredAtom1826 Fin15AnchoredAtom1827
    Fin15AnchoredAtom1831 Fin15AnchoredAtom1860 Fin15AnchoredAtom1861 Fin15AnchoredAtom1865
    Fin15AnchoredAtom1872 Fin15AnchoredAtom1876 Fin15AnchoredAtom1880 Fin15AnchoredAtom1915
    Fin15AnchoredAtom1916 Fin15AnchoredAtom1920 Fin15AnchoredAtom1927 Fin15AnchoredAtom1931
    Fin15AnchoredAtom1935 Fin15AnchoredAtom2057 Fin15AnchoredAtom2061 Fin15AnchoredAtom2065
    Fin15AnchoredAtom2090 Fin15AnchoredAtom2135 Fin15AnchoredAtom2136 Fin15AnchoredAtom2140
    Fin15AnchoredAtom2147 Fin15AnchoredAtom2151 Fin15AnchoredAtom2155 Fin15AnchoredAtom2277
    Fin15AnchoredAtom2281 Fin15AnchoredAtom2285 Fin15AnchoredAtom2310 Fin15AnchoredAtom2442
    Fin15AnchoredAtom2446 Fin15AnchoredAtom2450 Fin15AnchoredAtom2475 Fin15AnchoredAtom2770
    Fin15AnchoredAtom2850 Fin15AnchoredAtom2851 Fin15AnchoredAtom2855 Fin15AnchoredAtom2862
    Fin15AnchoredAtom2866 Fin15AnchoredAtom2870 Fin15AnchoredAtom2992 Fin15AnchoredAtom2996
    Fin15AnchoredAtom3000 Fin15AnchoredAtom3025 Fin15AnchoredAtom3157 Fin15AnchoredAtom3161
    Fin15AnchoredAtom3165 Fin15AnchoredAtom3190 Fin15AnchoredAtom3485 Fin15AnchoredAtom3652
    Fin15AnchoredAtom3656 Fin15AnchoredAtom3660 Fin15AnchoredAtom3685 Fin15AnchoredAtom3980
    Fin15AnchoredAtom4310 at hbad
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

theorem fin15Anchored_clause30619 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1939 chi ∧
      ¬Fin15AnchoredAtom2059 chi ∧
      ¬Fin15AnchoredAtom2060 chi ∧
      ¬Fin15AnchoredAtom2069 chi ∧
      ¬Fin15AnchoredAtom2094 chi ∧
      ¬Fin15AnchoredAtom2135 chi ∧
      ¬Fin15AnchoredAtom2138 chi ∧
      ¬Fin15AnchoredAtom2139 chi ∧
      ¬Fin15AnchoredAtom2149 chi ∧
      ¬Fin15AnchoredAtom2150 chi ∧
      ¬Fin15AnchoredAtom2159 chi ∧
      ¬Fin15AnchoredAtom2279 chi ∧
      ¬Fin15AnchoredAtom2280 chi ∧
      ¬Fin15AnchoredAtom2289 chi ∧
      ¬Fin15AnchoredAtom2314 chi ∧
      ¬Fin15AnchoredAtom2444 chi ∧
      ¬Fin15AnchoredAtom2445 chi ∧
      ¬Fin15AnchoredAtom2454 chi ∧
      ¬Fin15AnchoredAtom2479 chi ∧
      ¬Fin15AnchoredAtom2774 chi ∧
      ¬Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom2864 chi ∧
      ¬Fin15AnchoredAtom2865 chi ∧
      ¬Fin15AnchoredAtom2874 chi ∧
      ¬Fin15AnchoredAtom2994 chi ∧
      ¬Fin15AnchoredAtom2995 chi ∧
      ¬Fin15AnchoredAtom3004 chi ∧
      ¬Fin15AnchoredAtom3029 chi ∧
      ¬Fin15AnchoredAtom3159 chi ∧
      ¬Fin15AnchoredAtom3160 chi ∧
      ¬Fin15AnchoredAtom3169 chi ∧
      ¬Fin15AnchoredAtom3194 chi ∧
      ¬Fin15AnchoredAtom3489 chi ∧
      ¬Fin15AnchoredAtom3654 chi ∧
      ¬Fin15AnchoredAtom3655 chi ∧
      ¬Fin15AnchoredAtom3664 chi ∧
      ¬Fin15AnchoredAtom3689 chi ∧
      ¬Fin15AnchoredAtom3984 chi ∧
      ¬Fin15AnchoredAtom4314 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 7, 9, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask12943
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1824 Fin15AnchoredAtom1826 Fin15AnchoredAtom1829
    Fin15AnchoredAtom1830 Fin15AnchoredAtom1860 Fin15AnchoredAtom1863 Fin15AnchoredAtom1864
    Fin15AnchoredAtom1874 Fin15AnchoredAtom1875 Fin15AnchoredAtom1884 Fin15AnchoredAtom1915
    Fin15AnchoredAtom1918 Fin15AnchoredAtom1919 Fin15AnchoredAtom1929 Fin15AnchoredAtom1930
    Fin15AnchoredAtom1939 Fin15AnchoredAtom2059 Fin15AnchoredAtom2060 Fin15AnchoredAtom2069
    Fin15AnchoredAtom2094 Fin15AnchoredAtom2135 Fin15AnchoredAtom2138 Fin15AnchoredAtom2139
    Fin15AnchoredAtom2149 Fin15AnchoredAtom2150 Fin15AnchoredAtom2159 Fin15AnchoredAtom2279
    Fin15AnchoredAtom2280 Fin15AnchoredAtom2289 Fin15AnchoredAtom2314 Fin15AnchoredAtom2444
    Fin15AnchoredAtom2445 Fin15AnchoredAtom2454 Fin15AnchoredAtom2479 Fin15AnchoredAtom2774
    Fin15AnchoredAtom2850 Fin15AnchoredAtom2853 Fin15AnchoredAtom2854 Fin15AnchoredAtom2864
    Fin15AnchoredAtom2865 Fin15AnchoredAtom2874 Fin15AnchoredAtom2994 Fin15AnchoredAtom2995
    Fin15AnchoredAtom3004 Fin15AnchoredAtom3029 Fin15AnchoredAtom3159 Fin15AnchoredAtom3160
    Fin15AnchoredAtom3169 Fin15AnchoredAtom3194 Fin15AnchoredAtom3489 Fin15AnchoredAtom3654
    Fin15AnchoredAtom3655 Fin15AnchoredAtom3664 Fin15AnchoredAtom3689 Fin15AnchoredAtom3984
    Fin15AnchoredAtom4314 at hbad
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

theorem fin15Anchored_clause30620 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom1940 chi ∧
      ¬Fin15AnchoredAtom2059 chi ∧
      ¬Fin15AnchoredAtom2061 chi ∧
      ¬Fin15AnchoredAtom2070 chi ∧
      ¬Fin15AnchoredAtom2095 chi ∧
      ¬Fin15AnchoredAtom2135 chi ∧
      ¬Fin15AnchoredAtom2138 chi ∧
      ¬Fin15AnchoredAtom2140 chi ∧
      ¬Fin15AnchoredAtom2149 chi ∧
      ¬Fin15AnchoredAtom2151 chi ∧
      ¬Fin15AnchoredAtom2160 chi ∧
      ¬Fin15AnchoredAtom2279 chi ∧
      ¬Fin15AnchoredAtom2281 chi ∧
      ¬Fin15AnchoredAtom2290 chi ∧
      ¬Fin15AnchoredAtom2315 chi ∧
      ¬Fin15AnchoredAtom2444 chi ∧
      ¬Fin15AnchoredAtom2446 chi ∧
      ¬Fin15AnchoredAtom2455 chi ∧
      ¬Fin15AnchoredAtom2480 chi ∧
      ¬Fin15AnchoredAtom2775 chi ∧
      ¬Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom2864 chi ∧
      ¬Fin15AnchoredAtom2866 chi ∧
      ¬Fin15AnchoredAtom2875 chi ∧
      ¬Fin15AnchoredAtom2994 chi ∧
      ¬Fin15AnchoredAtom2996 chi ∧
      ¬Fin15AnchoredAtom3005 chi ∧
      ¬Fin15AnchoredAtom3030 chi ∧
      ¬Fin15AnchoredAtom3159 chi ∧
      ¬Fin15AnchoredAtom3161 chi ∧
      ¬Fin15AnchoredAtom3170 chi ∧
      ¬Fin15AnchoredAtom3195 chi ∧
      ¬Fin15AnchoredAtom3490 chi ∧
      ¬Fin15AnchoredAtom3654 chi ∧
      ¬Fin15AnchoredAtom3656 chi ∧
      ¬Fin15AnchoredAtom3665 chi ∧
      ¬Fin15AnchoredAtom3690 chi ∧
      ¬Fin15AnchoredAtom3985 chi ∧
      ¬Fin15AnchoredAtom4315 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 7, 9, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21135
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1824 Fin15AnchoredAtom1826 Fin15AnchoredAtom1829
    Fin15AnchoredAtom1831 Fin15AnchoredAtom1860 Fin15AnchoredAtom1863 Fin15AnchoredAtom1865
    Fin15AnchoredAtom1874 Fin15AnchoredAtom1876 Fin15AnchoredAtom1885 Fin15AnchoredAtom1915
    Fin15AnchoredAtom1918 Fin15AnchoredAtom1920 Fin15AnchoredAtom1929 Fin15AnchoredAtom1931
    Fin15AnchoredAtom1940 Fin15AnchoredAtom2059 Fin15AnchoredAtom2061 Fin15AnchoredAtom2070
    Fin15AnchoredAtom2095 Fin15AnchoredAtom2135 Fin15AnchoredAtom2138 Fin15AnchoredAtom2140
    Fin15AnchoredAtom2149 Fin15AnchoredAtom2151 Fin15AnchoredAtom2160 Fin15AnchoredAtom2279
    Fin15AnchoredAtom2281 Fin15AnchoredAtom2290 Fin15AnchoredAtom2315 Fin15AnchoredAtom2444
    Fin15AnchoredAtom2446 Fin15AnchoredAtom2455 Fin15AnchoredAtom2480 Fin15AnchoredAtom2775
    Fin15AnchoredAtom2850 Fin15AnchoredAtom2853 Fin15AnchoredAtom2855 Fin15AnchoredAtom2864
    Fin15AnchoredAtom2866 Fin15AnchoredAtom2875 Fin15AnchoredAtom2994 Fin15AnchoredAtom2996
    Fin15AnchoredAtom3005 Fin15AnchoredAtom3030 Fin15AnchoredAtom3159 Fin15AnchoredAtom3161
    Fin15AnchoredAtom3170 Fin15AnchoredAtom3195 Fin15AnchoredAtom3490 Fin15AnchoredAtom3654
    Fin15AnchoredAtom3656 Fin15AnchoredAtom3665 Fin15AnchoredAtom3690 Fin15AnchoredAtom3985
    Fin15AnchoredAtom4315 at hbad
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

theorem fin15Anchored_clause30621 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom1886 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
      ¬Fin15AnchoredAtom2060 chi ∧
      ¬Fin15AnchoredAtom2061 chi ∧
      ¬Fin15AnchoredAtom2071 chi ∧
      ¬Fin15AnchoredAtom2096 chi ∧
      ¬Fin15AnchoredAtom2135 chi ∧
      ¬Fin15AnchoredAtom2139 chi ∧
      ¬Fin15AnchoredAtom2140 chi ∧
      ¬Fin15AnchoredAtom2150 chi ∧
      ¬Fin15AnchoredAtom2151 chi ∧
      ¬Fin15AnchoredAtom2161 chi ∧
      ¬Fin15AnchoredAtom2280 chi ∧
      ¬Fin15AnchoredAtom2281 chi ∧
      ¬Fin15AnchoredAtom2291 chi ∧
      ¬Fin15AnchoredAtom2316 chi ∧
      ¬Fin15AnchoredAtom2445 chi ∧
      ¬Fin15AnchoredAtom2446 chi ∧
      ¬Fin15AnchoredAtom2456 chi ∧
      ¬Fin15AnchoredAtom2481 chi ∧
      ¬Fin15AnchoredAtom2776 chi ∧
      ¬Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom2865 chi ∧
      ¬Fin15AnchoredAtom2866 chi ∧
      ¬Fin15AnchoredAtom2876 chi ∧
      ¬Fin15AnchoredAtom2995 chi ∧
      ¬Fin15AnchoredAtom2996 chi ∧
      ¬Fin15AnchoredAtom3006 chi ∧
      ¬Fin15AnchoredAtom3031 chi ∧
      ¬Fin15AnchoredAtom3160 chi ∧
      ¬Fin15AnchoredAtom3161 chi ∧
      ¬Fin15AnchoredAtom3171 chi ∧
      ¬Fin15AnchoredAtom3196 chi ∧
      ¬Fin15AnchoredAtom3491 chi ∧
      ¬Fin15AnchoredAtom3655 chi ∧
      ¬Fin15AnchoredAtom3656 chi ∧
      ¬Fin15AnchoredAtom3666 chi ∧
      ¬Fin15AnchoredAtom3691 chi ∧
      ¬Fin15AnchoredAtom3986 chi ∧
      ¬Fin15AnchoredAtom4316 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 7, 9, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25231
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1824 Fin15AnchoredAtom1826 Fin15AnchoredAtom1830
    Fin15AnchoredAtom1831 Fin15AnchoredAtom1860 Fin15AnchoredAtom1864 Fin15AnchoredAtom1865
    Fin15AnchoredAtom1875 Fin15AnchoredAtom1876 Fin15AnchoredAtom1886 Fin15AnchoredAtom1915
    Fin15AnchoredAtom1919 Fin15AnchoredAtom1920 Fin15AnchoredAtom1930 Fin15AnchoredAtom1931
    Fin15AnchoredAtom1941 Fin15AnchoredAtom2060 Fin15AnchoredAtom2061 Fin15AnchoredAtom2071
    Fin15AnchoredAtom2096 Fin15AnchoredAtom2135 Fin15AnchoredAtom2139 Fin15AnchoredAtom2140
    Fin15AnchoredAtom2150 Fin15AnchoredAtom2151 Fin15AnchoredAtom2161 Fin15AnchoredAtom2280
    Fin15AnchoredAtom2281 Fin15AnchoredAtom2291 Fin15AnchoredAtom2316 Fin15AnchoredAtom2445
    Fin15AnchoredAtom2446 Fin15AnchoredAtom2456 Fin15AnchoredAtom2481 Fin15AnchoredAtom2776
    Fin15AnchoredAtom2850 Fin15AnchoredAtom2854 Fin15AnchoredAtom2855 Fin15AnchoredAtom2865
    Fin15AnchoredAtom2866 Fin15AnchoredAtom2876 Fin15AnchoredAtom2995 Fin15AnchoredAtom2996
    Fin15AnchoredAtom3006 Fin15AnchoredAtom3031 Fin15AnchoredAtom3160 Fin15AnchoredAtom3161
    Fin15AnchoredAtom3171 Fin15AnchoredAtom3196 Fin15AnchoredAtom3491 Fin15AnchoredAtom3655
    Fin15AnchoredAtom3656 Fin15AnchoredAtom3666 Fin15AnchoredAtom3691 Fin15AnchoredAtom3986
    Fin15AnchoredAtom4316 at hbad
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

theorem fin15Anchored_clause30622 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom1939 chi ∧
      ¬Fin15AnchoredAtom2063 chi ∧
      ¬Fin15AnchoredAtom2064 chi ∧
      ¬Fin15AnchoredAtom2069 chi ∧
      ¬Fin15AnchoredAtom2100 chi ∧
      ¬Fin15AnchoredAtom2136 chi ∧
      ¬Fin15AnchoredAtom2138 chi ∧
      ¬Fin15AnchoredAtom2139 chi ∧
      ¬Fin15AnchoredAtom2153 chi ∧
      ¬Fin15AnchoredAtom2154 chi ∧
      ¬Fin15AnchoredAtom2159 chi ∧
      ¬Fin15AnchoredAtom2283 chi ∧
      ¬Fin15AnchoredAtom2284 chi ∧
      ¬Fin15AnchoredAtom2289 chi ∧
      ¬Fin15AnchoredAtom2320 chi ∧
      ¬Fin15AnchoredAtom2448 chi ∧
      ¬Fin15AnchoredAtom2449 chi ∧
      ¬Fin15AnchoredAtom2454 chi ∧
      ¬Fin15AnchoredAtom2485 chi ∧
      ¬Fin15AnchoredAtom2780 chi ∧
      ¬Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom2868 chi ∧
      ¬Fin15AnchoredAtom2869 chi ∧
      ¬Fin15AnchoredAtom2874 chi ∧
      ¬Fin15AnchoredAtom2998 chi ∧
      ¬Fin15AnchoredAtom2999 chi ∧
      ¬Fin15AnchoredAtom3004 chi ∧
      ¬Fin15AnchoredAtom3035 chi ∧
      ¬Fin15AnchoredAtom3163 chi ∧
      ¬Fin15AnchoredAtom3164 chi ∧
      ¬Fin15AnchoredAtom3169 chi ∧
      ¬Fin15AnchoredAtom3200 chi ∧
      ¬Fin15AnchoredAtom3495 chi ∧
      ¬Fin15AnchoredAtom3658 chi ∧
      ¬Fin15AnchoredAtom3659 chi ∧
      ¬Fin15AnchoredAtom3664 chi ∧
      ¬Fin15AnchoredAtom3695 chi ∧
      ¬Fin15AnchoredAtom3990 chi ∧
      ¬Fin15AnchoredAtom4320 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 7, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13455
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1824 Fin15AnchoredAtom1827 Fin15AnchoredAtom1829
    Fin15AnchoredAtom1830 Fin15AnchoredAtom1861 Fin15AnchoredAtom1863 Fin15AnchoredAtom1864
    Fin15AnchoredAtom1878 Fin15AnchoredAtom1879 Fin15AnchoredAtom1884 Fin15AnchoredAtom1916
    Fin15AnchoredAtom1918 Fin15AnchoredAtom1919 Fin15AnchoredAtom1933 Fin15AnchoredAtom1934
    Fin15AnchoredAtom1939 Fin15AnchoredAtom2063 Fin15AnchoredAtom2064 Fin15AnchoredAtom2069
    Fin15AnchoredAtom2100 Fin15AnchoredAtom2136 Fin15AnchoredAtom2138 Fin15AnchoredAtom2139
    Fin15AnchoredAtom2153 Fin15AnchoredAtom2154 Fin15AnchoredAtom2159 Fin15AnchoredAtom2283
    Fin15AnchoredAtom2284 Fin15AnchoredAtom2289 Fin15AnchoredAtom2320 Fin15AnchoredAtom2448
    Fin15AnchoredAtom2449 Fin15AnchoredAtom2454 Fin15AnchoredAtom2485 Fin15AnchoredAtom2780
    Fin15AnchoredAtom2851 Fin15AnchoredAtom2853 Fin15AnchoredAtom2854 Fin15AnchoredAtom2868
    Fin15AnchoredAtom2869 Fin15AnchoredAtom2874 Fin15AnchoredAtom2998 Fin15AnchoredAtom2999
    Fin15AnchoredAtom3004 Fin15AnchoredAtom3035 Fin15AnchoredAtom3163 Fin15AnchoredAtom3164
    Fin15AnchoredAtom3169 Fin15AnchoredAtom3200 Fin15AnchoredAtom3495 Fin15AnchoredAtom3658
    Fin15AnchoredAtom3659 Fin15AnchoredAtom3664 Fin15AnchoredAtom3695 Fin15AnchoredAtom3990
    Fin15AnchoredAtom4320 at hbad
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

theorem fin15Anchored_clause30623 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom1935 chi ∧
      ¬Fin15AnchoredAtom1940 chi ∧
      ¬Fin15AnchoredAtom2063 chi ∧
      ¬Fin15AnchoredAtom2065 chi ∧
      ¬Fin15AnchoredAtom2070 chi ∧
      ¬Fin15AnchoredAtom2101 chi ∧
      ¬Fin15AnchoredAtom2136 chi ∧
      ¬Fin15AnchoredAtom2138 chi ∧
      ¬Fin15AnchoredAtom2140 chi ∧
      ¬Fin15AnchoredAtom2153 chi ∧
      ¬Fin15AnchoredAtom2155 chi ∧
      ¬Fin15AnchoredAtom2160 chi ∧
      ¬Fin15AnchoredAtom2283 chi ∧
      ¬Fin15AnchoredAtom2285 chi ∧
      ¬Fin15AnchoredAtom2290 chi ∧
      ¬Fin15AnchoredAtom2321 chi ∧
      ¬Fin15AnchoredAtom2448 chi ∧
      ¬Fin15AnchoredAtom2450 chi ∧
      ¬Fin15AnchoredAtom2455 chi ∧
      ¬Fin15AnchoredAtom2486 chi ∧
      ¬Fin15AnchoredAtom2781 chi ∧
      ¬Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom2868 chi ∧
      ¬Fin15AnchoredAtom2870 chi ∧
      ¬Fin15AnchoredAtom2875 chi ∧
      ¬Fin15AnchoredAtom2998 chi ∧
      ¬Fin15AnchoredAtom3000 chi ∧
      ¬Fin15AnchoredAtom3005 chi ∧
      ¬Fin15AnchoredAtom3036 chi ∧
      ¬Fin15AnchoredAtom3163 chi ∧
      ¬Fin15AnchoredAtom3165 chi ∧
      ¬Fin15AnchoredAtom3170 chi ∧
      ¬Fin15AnchoredAtom3201 chi ∧
      ¬Fin15AnchoredAtom3496 chi ∧
      ¬Fin15AnchoredAtom3658 chi ∧
      ¬Fin15AnchoredAtom3660 chi ∧
      ¬Fin15AnchoredAtom3665 chi ∧
      ¬Fin15AnchoredAtom3696 chi ∧
      ¬Fin15AnchoredAtom3991 chi ∧
      ¬Fin15AnchoredAtom4321 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 7, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21647
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1824 Fin15AnchoredAtom1827 Fin15AnchoredAtom1829
    Fin15AnchoredAtom1831 Fin15AnchoredAtom1861 Fin15AnchoredAtom1863 Fin15AnchoredAtom1865
    Fin15AnchoredAtom1878 Fin15AnchoredAtom1880 Fin15AnchoredAtom1885 Fin15AnchoredAtom1916
    Fin15AnchoredAtom1918 Fin15AnchoredAtom1920 Fin15AnchoredAtom1933 Fin15AnchoredAtom1935
    Fin15AnchoredAtom1940 Fin15AnchoredAtom2063 Fin15AnchoredAtom2065 Fin15AnchoredAtom2070
    Fin15AnchoredAtom2101 Fin15AnchoredAtom2136 Fin15AnchoredAtom2138 Fin15AnchoredAtom2140
    Fin15AnchoredAtom2153 Fin15AnchoredAtom2155 Fin15AnchoredAtom2160 Fin15AnchoredAtom2283
    Fin15AnchoredAtom2285 Fin15AnchoredAtom2290 Fin15AnchoredAtom2321 Fin15AnchoredAtom2448
    Fin15AnchoredAtom2450 Fin15AnchoredAtom2455 Fin15AnchoredAtom2486 Fin15AnchoredAtom2781
    Fin15AnchoredAtom2851 Fin15AnchoredAtom2853 Fin15AnchoredAtom2855 Fin15AnchoredAtom2868
    Fin15AnchoredAtom2870 Fin15AnchoredAtom2875 Fin15AnchoredAtom2998 Fin15AnchoredAtom3000
    Fin15AnchoredAtom3005 Fin15AnchoredAtom3036 Fin15AnchoredAtom3163 Fin15AnchoredAtom3165
    Fin15AnchoredAtom3170 Fin15AnchoredAtom3201 Fin15AnchoredAtom3496 Fin15AnchoredAtom3658
    Fin15AnchoredAtom3660 Fin15AnchoredAtom3665 Fin15AnchoredAtom3696 Fin15AnchoredAtom3991
    Fin15AnchoredAtom4321 at hbad
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

theorem fin15Anchored_clause30624 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom1886 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom1935 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
      ¬Fin15AnchoredAtom2064 chi ∧
      ¬Fin15AnchoredAtom2065 chi ∧
      ¬Fin15AnchoredAtom2071 chi ∧
      ¬Fin15AnchoredAtom2102 chi ∧
      ¬Fin15AnchoredAtom2136 chi ∧
      ¬Fin15AnchoredAtom2139 chi ∧
      ¬Fin15AnchoredAtom2140 chi ∧
      ¬Fin15AnchoredAtom2154 chi ∧
      ¬Fin15AnchoredAtom2155 chi ∧
      ¬Fin15AnchoredAtom2161 chi ∧
      ¬Fin15AnchoredAtom2284 chi ∧
      ¬Fin15AnchoredAtom2285 chi ∧
      ¬Fin15AnchoredAtom2291 chi ∧
      ¬Fin15AnchoredAtom2322 chi ∧
      ¬Fin15AnchoredAtom2449 chi ∧
      ¬Fin15AnchoredAtom2450 chi ∧
      ¬Fin15AnchoredAtom2456 chi ∧
      ¬Fin15AnchoredAtom2487 chi ∧
      ¬Fin15AnchoredAtom2782 chi ∧
      ¬Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom2869 chi ∧
      ¬Fin15AnchoredAtom2870 chi ∧
      ¬Fin15AnchoredAtom2876 chi ∧
      ¬Fin15AnchoredAtom2999 chi ∧
      ¬Fin15AnchoredAtom3000 chi ∧
      ¬Fin15AnchoredAtom3006 chi ∧
      ¬Fin15AnchoredAtom3037 chi ∧
      ¬Fin15AnchoredAtom3164 chi ∧
      ¬Fin15AnchoredAtom3165 chi ∧
      ¬Fin15AnchoredAtom3171 chi ∧
      ¬Fin15AnchoredAtom3202 chi ∧
      ¬Fin15AnchoredAtom3497 chi ∧
      ¬Fin15AnchoredAtom3659 chi ∧
      ¬Fin15AnchoredAtom3660 chi ∧
      ¬Fin15AnchoredAtom3666 chi ∧
      ¬Fin15AnchoredAtom3697 chi ∧
      ¬Fin15AnchoredAtom3992 chi ∧
      ¬Fin15AnchoredAtom4322 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 7, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25743
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1824 Fin15AnchoredAtom1827 Fin15AnchoredAtom1830
    Fin15AnchoredAtom1831 Fin15AnchoredAtom1861 Fin15AnchoredAtom1864 Fin15AnchoredAtom1865
    Fin15AnchoredAtom1879 Fin15AnchoredAtom1880 Fin15AnchoredAtom1886 Fin15AnchoredAtom1916
    Fin15AnchoredAtom1919 Fin15AnchoredAtom1920 Fin15AnchoredAtom1934 Fin15AnchoredAtom1935
    Fin15AnchoredAtom1941 Fin15AnchoredAtom2064 Fin15AnchoredAtom2065 Fin15AnchoredAtom2071
    Fin15AnchoredAtom2102 Fin15AnchoredAtom2136 Fin15AnchoredAtom2139 Fin15AnchoredAtom2140
    Fin15AnchoredAtom2154 Fin15AnchoredAtom2155 Fin15AnchoredAtom2161 Fin15AnchoredAtom2284
    Fin15AnchoredAtom2285 Fin15AnchoredAtom2291 Fin15AnchoredAtom2322 Fin15AnchoredAtom2449
    Fin15AnchoredAtom2450 Fin15AnchoredAtom2456 Fin15AnchoredAtom2487 Fin15AnchoredAtom2782
    Fin15AnchoredAtom2851 Fin15AnchoredAtom2854 Fin15AnchoredAtom2855 Fin15AnchoredAtom2869
    Fin15AnchoredAtom2870 Fin15AnchoredAtom2876 Fin15AnchoredAtom2999 Fin15AnchoredAtom3000
    Fin15AnchoredAtom3006 Fin15AnchoredAtom3037 Fin15AnchoredAtom3164 Fin15AnchoredAtom3165
    Fin15AnchoredAtom3171 Fin15AnchoredAtom3202 Fin15AnchoredAtom3497 Fin15AnchoredAtom3659
    Fin15AnchoredAtom3660 Fin15AnchoredAtom3666 Fin15AnchoredAtom3697 Fin15AnchoredAtom3992
    Fin15AnchoredAtom4322 at hbad
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

theorem fin15Anchored_clause30625 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom1886 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1939 chi ∧
      ¬Fin15AnchoredAtom1940 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
      ¬Fin15AnchoredAtom2069 chi ∧
      ¬Fin15AnchoredAtom2070 chi ∧
      ¬Fin15AnchoredAtom2071 chi ∧
      ¬Fin15AnchoredAtom2106 chi ∧
      ¬Fin15AnchoredAtom2138 chi ∧
      ¬Fin15AnchoredAtom2139 chi ∧
      ¬Fin15AnchoredAtom2140 chi ∧
      ¬Fin15AnchoredAtom2159 chi ∧
      ¬Fin15AnchoredAtom2160 chi ∧
      ¬Fin15AnchoredAtom2161 chi ∧
      ¬Fin15AnchoredAtom2289 chi ∧
      ¬Fin15AnchoredAtom2290 chi ∧
      ¬Fin15AnchoredAtom2291 chi ∧
      ¬Fin15AnchoredAtom2326 chi ∧
      ¬Fin15AnchoredAtom2454 chi ∧
      ¬Fin15AnchoredAtom2455 chi ∧
      ¬Fin15AnchoredAtom2456 chi ∧
      ¬Fin15AnchoredAtom2491 chi ∧
      ¬Fin15AnchoredAtom2786 chi ∧
      ¬Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom2874 chi ∧
      ¬Fin15AnchoredAtom2875 chi ∧
      ¬Fin15AnchoredAtom2876 chi ∧
      ¬Fin15AnchoredAtom3004 chi ∧
      ¬Fin15AnchoredAtom3005 chi ∧
      ¬Fin15AnchoredAtom3006 chi ∧
      ¬Fin15AnchoredAtom3041 chi ∧
      ¬Fin15AnchoredAtom3169 chi ∧
      ¬Fin15AnchoredAtom3170 chi ∧
      ¬Fin15AnchoredAtom3171 chi ∧
      ¬Fin15AnchoredAtom3206 chi ∧
      ¬Fin15AnchoredAtom3501 chi ∧
      ¬Fin15AnchoredAtom3664 chi ∧
      ¬Fin15AnchoredAtom3665 chi ∧
      ¬Fin15AnchoredAtom3666 chi ∧
      ¬Fin15AnchoredAtom3701 chi ∧
      ¬Fin15AnchoredAtom3996 chi ∧
      ¬Fin15AnchoredAtom4326 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 7, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask28815
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1824 Fin15AnchoredAtom1829 Fin15AnchoredAtom1830
    Fin15AnchoredAtom1831 Fin15AnchoredAtom1863 Fin15AnchoredAtom1864 Fin15AnchoredAtom1865
    Fin15AnchoredAtom1884 Fin15AnchoredAtom1885 Fin15AnchoredAtom1886 Fin15AnchoredAtom1918
    Fin15AnchoredAtom1919 Fin15AnchoredAtom1920 Fin15AnchoredAtom1939 Fin15AnchoredAtom1940
    Fin15AnchoredAtom1941 Fin15AnchoredAtom2069 Fin15AnchoredAtom2070 Fin15AnchoredAtom2071
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2138 Fin15AnchoredAtom2139 Fin15AnchoredAtom2140
    Fin15AnchoredAtom2159 Fin15AnchoredAtom2160 Fin15AnchoredAtom2161 Fin15AnchoredAtom2289
    Fin15AnchoredAtom2290 Fin15AnchoredAtom2291 Fin15AnchoredAtom2326 Fin15AnchoredAtom2454
    Fin15AnchoredAtom2455 Fin15AnchoredAtom2456 Fin15AnchoredAtom2491 Fin15AnchoredAtom2786
    Fin15AnchoredAtom2853 Fin15AnchoredAtom2854 Fin15AnchoredAtom2855 Fin15AnchoredAtom2874
    Fin15AnchoredAtom2875 Fin15AnchoredAtom2876 Fin15AnchoredAtom3004 Fin15AnchoredAtom3005
    Fin15AnchoredAtom3006 Fin15AnchoredAtom3041 Fin15AnchoredAtom3169 Fin15AnchoredAtom3170
    Fin15AnchoredAtom3171 Fin15AnchoredAtom3206 Fin15AnchoredAtom3501 Fin15AnchoredAtom3664
    Fin15AnchoredAtom3665 Fin15AnchoredAtom3666 Fin15AnchoredAtom3701 Fin15AnchoredAtom3996
    Fin15AnchoredAtom4326 at hbad
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

theorem fin15Anchored_clause30626 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom1939 chi ∧
      ¬Fin15AnchoredAtom2088 chi ∧
      ¬Fin15AnchoredAtom2089 chi ∧
      ¬Fin15AnchoredAtom2094 chi ∧
      ¬Fin15AnchoredAtom2100 chi ∧
      ¬Fin15AnchoredAtom2147 chi ∧
      ¬Fin15AnchoredAtom2149 chi ∧
      ¬Fin15AnchoredAtom2150 chi ∧
      ¬Fin15AnchoredAtom2153 chi ∧
      ¬Fin15AnchoredAtom2154 chi ∧
      ¬Fin15AnchoredAtom2159 chi ∧
      ¬Fin15AnchoredAtom2308 chi ∧
      ¬Fin15AnchoredAtom2309 chi ∧
      ¬Fin15AnchoredAtom2314 chi ∧
      ¬Fin15AnchoredAtom2320 chi ∧
      ¬Fin15AnchoredAtom2473 chi ∧
      ¬Fin15AnchoredAtom2474 chi ∧
      ¬Fin15AnchoredAtom2479 chi ∧
      ¬Fin15AnchoredAtom2485 chi ∧
      ¬Fin15AnchoredAtom2810 chi ∧
      ¬Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom2864 chi ∧
      ¬Fin15AnchoredAtom2865 chi ∧
      ¬Fin15AnchoredAtom2868 chi ∧
      ¬Fin15AnchoredAtom2869 chi ∧
      ¬Fin15AnchoredAtom2874 chi ∧
      ¬Fin15AnchoredAtom3023 chi ∧
      ¬Fin15AnchoredAtom3024 chi ∧
      ¬Fin15AnchoredAtom3029 chi ∧
      ¬Fin15AnchoredAtom3035 chi ∧
      ¬Fin15AnchoredAtom3188 chi ∧
      ¬Fin15AnchoredAtom3189 chi ∧
      ¬Fin15AnchoredAtom3194 chi ∧
      ¬Fin15AnchoredAtom3200 chi ∧
      ¬Fin15AnchoredAtom3525 chi ∧
      ¬Fin15AnchoredAtom3683 chi ∧
      ¬Fin15AnchoredAtom3684 chi ∧
      ¬Fin15AnchoredAtom3689 chi ∧
      ¬Fin15AnchoredAtom3695 chi ∧
      ¬Fin15AnchoredAtom4020 chi ∧
      ¬Fin15AnchoredAtom4350 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13839
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1826 Fin15AnchoredAtom1827 Fin15AnchoredAtom1829
    Fin15AnchoredAtom1830 Fin15AnchoredAtom1872 Fin15AnchoredAtom1874 Fin15AnchoredAtom1875
    Fin15AnchoredAtom1878 Fin15AnchoredAtom1879 Fin15AnchoredAtom1884 Fin15AnchoredAtom1927
    Fin15AnchoredAtom1929 Fin15AnchoredAtom1930 Fin15AnchoredAtom1933 Fin15AnchoredAtom1934
    Fin15AnchoredAtom1939 Fin15AnchoredAtom2088 Fin15AnchoredAtom2089 Fin15AnchoredAtom2094
    Fin15AnchoredAtom2100 Fin15AnchoredAtom2147 Fin15AnchoredAtom2149 Fin15AnchoredAtom2150
    Fin15AnchoredAtom2153 Fin15AnchoredAtom2154 Fin15AnchoredAtom2159 Fin15AnchoredAtom2308
    Fin15AnchoredAtom2309 Fin15AnchoredAtom2314 Fin15AnchoredAtom2320 Fin15AnchoredAtom2473
    Fin15AnchoredAtom2474 Fin15AnchoredAtom2479 Fin15AnchoredAtom2485 Fin15AnchoredAtom2810
    Fin15AnchoredAtom2862 Fin15AnchoredAtom2864 Fin15AnchoredAtom2865 Fin15AnchoredAtom2868
    Fin15AnchoredAtom2869 Fin15AnchoredAtom2874 Fin15AnchoredAtom3023 Fin15AnchoredAtom3024
    Fin15AnchoredAtom3029 Fin15AnchoredAtom3035 Fin15AnchoredAtom3188 Fin15AnchoredAtom3189
    Fin15AnchoredAtom3194 Fin15AnchoredAtom3200 Fin15AnchoredAtom3525 Fin15AnchoredAtom3683
    Fin15AnchoredAtom3684 Fin15AnchoredAtom3689 Fin15AnchoredAtom3695 Fin15AnchoredAtom4020
    Fin15AnchoredAtom4350 at hbad
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

theorem fin15Anchored_clause30627 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom1935 chi ∧
      ¬Fin15AnchoredAtom1940 chi ∧
      ¬Fin15AnchoredAtom2088 chi ∧
      ¬Fin15AnchoredAtom2090 chi ∧
      ¬Fin15AnchoredAtom2095 chi ∧
      ¬Fin15AnchoredAtom2101 chi ∧
      ¬Fin15AnchoredAtom2147 chi ∧
      ¬Fin15AnchoredAtom2149 chi ∧
      ¬Fin15AnchoredAtom2151 chi ∧
      ¬Fin15AnchoredAtom2153 chi ∧
      ¬Fin15AnchoredAtom2155 chi ∧
      ¬Fin15AnchoredAtom2160 chi ∧
      ¬Fin15AnchoredAtom2308 chi ∧
      ¬Fin15AnchoredAtom2310 chi ∧
      ¬Fin15AnchoredAtom2315 chi ∧
      ¬Fin15AnchoredAtom2321 chi ∧
      ¬Fin15AnchoredAtom2473 chi ∧
      ¬Fin15AnchoredAtom2475 chi ∧
      ¬Fin15AnchoredAtom2480 chi ∧
      ¬Fin15AnchoredAtom2486 chi ∧
      ¬Fin15AnchoredAtom2811 chi ∧
      ¬Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom2864 chi ∧
      ¬Fin15AnchoredAtom2866 chi ∧
      ¬Fin15AnchoredAtom2868 chi ∧
      ¬Fin15AnchoredAtom2870 chi ∧
      ¬Fin15AnchoredAtom2875 chi ∧
      ¬Fin15AnchoredAtom3023 chi ∧
      ¬Fin15AnchoredAtom3025 chi ∧
      ¬Fin15AnchoredAtom3030 chi ∧
      ¬Fin15AnchoredAtom3036 chi ∧
      ¬Fin15AnchoredAtom3188 chi ∧
      ¬Fin15AnchoredAtom3190 chi ∧
      ¬Fin15AnchoredAtom3195 chi ∧
      ¬Fin15AnchoredAtom3201 chi ∧
      ¬Fin15AnchoredAtom3526 chi ∧
      ¬Fin15AnchoredAtom3683 chi ∧
      ¬Fin15AnchoredAtom3685 chi ∧
      ¬Fin15AnchoredAtom3690 chi ∧
      ¬Fin15AnchoredAtom3696 chi ∧
      ¬Fin15AnchoredAtom4021 chi ∧
      ¬Fin15AnchoredAtom4351 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 9, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22031
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1826 Fin15AnchoredAtom1827 Fin15AnchoredAtom1829
    Fin15AnchoredAtom1831 Fin15AnchoredAtom1872 Fin15AnchoredAtom1874 Fin15AnchoredAtom1876
    Fin15AnchoredAtom1878 Fin15AnchoredAtom1880 Fin15AnchoredAtom1885 Fin15AnchoredAtom1927
    Fin15AnchoredAtom1929 Fin15AnchoredAtom1931 Fin15AnchoredAtom1933 Fin15AnchoredAtom1935
    Fin15AnchoredAtom1940 Fin15AnchoredAtom2088 Fin15AnchoredAtom2090 Fin15AnchoredAtom2095
    Fin15AnchoredAtom2101 Fin15AnchoredAtom2147 Fin15AnchoredAtom2149 Fin15AnchoredAtom2151
    Fin15AnchoredAtom2153 Fin15AnchoredAtom2155 Fin15AnchoredAtom2160 Fin15AnchoredAtom2308
    Fin15AnchoredAtom2310 Fin15AnchoredAtom2315 Fin15AnchoredAtom2321 Fin15AnchoredAtom2473
    Fin15AnchoredAtom2475 Fin15AnchoredAtom2480 Fin15AnchoredAtom2486 Fin15AnchoredAtom2811
    Fin15AnchoredAtom2862 Fin15AnchoredAtom2864 Fin15AnchoredAtom2866 Fin15AnchoredAtom2868
    Fin15AnchoredAtom2870 Fin15AnchoredAtom2875 Fin15AnchoredAtom3023 Fin15AnchoredAtom3025
    Fin15AnchoredAtom3030 Fin15AnchoredAtom3036 Fin15AnchoredAtom3188 Fin15AnchoredAtom3190
    Fin15AnchoredAtom3195 Fin15AnchoredAtom3201 Fin15AnchoredAtom3526 Fin15AnchoredAtom3683
    Fin15AnchoredAtom3685 Fin15AnchoredAtom3690 Fin15AnchoredAtom3696 Fin15AnchoredAtom4021
    Fin15AnchoredAtom4351 at hbad
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

theorem fin15Anchored_clause30628 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom1886 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom1935 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
      ¬Fin15AnchoredAtom2089 chi ∧
      ¬Fin15AnchoredAtom2090 chi ∧
      ¬Fin15AnchoredAtom2096 chi ∧
      ¬Fin15AnchoredAtom2102 chi ∧
      ¬Fin15AnchoredAtom2147 chi ∧
      ¬Fin15AnchoredAtom2150 chi ∧
      ¬Fin15AnchoredAtom2151 chi ∧
      ¬Fin15AnchoredAtom2154 chi ∧
      ¬Fin15AnchoredAtom2155 chi ∧
      ¬Fin15AnchoredAtom2161 chi ∧
      ¬Fin15AnchoredAtom2309 chi ∧
      ¬Fin15AnchoredAtom2310 chi ∧
      ¬Fin15AnchoredAtom2316 chi ∧
      ¬Fin15AnchoredAtom2322 chi ∧
      ¬Fin15AnchoredAtom2474 chi ∧
      ¬Fin15AnchoredAtom2475 chi ∧
      ¬Fin15AnchoredAtom2481 chi ∧
      ¬Fin15AnchoredAtom2487 chi ∧
      ¬Fin15AnchoredAtom2812 chi ∧
      ¬Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom2865 chi ∧
      ¬Fin15AnchoredAtom2866 chi ∧
      ¬Fin15AnchoredAtom2869 chi ∧
      ¬Fin15AnchoredAtom2870 chi ∧
      ¬Fin15AnchoredAtom2876 chi ∧
      ¬Fin15AnchoredAtom3024 chi ∧
      ¬Fin15AnchoredAtom3025 chi ∧
      ¬Fin15AnchoredAtom3031 chi ∧
      ¬Fin15AnchoredAtom3037 chi ∧
      ¬Fin15AnchoredAtom3189 chi ∧
      ¬Fin15AnchoredAtom3190 chi ∧
      ¬Fin15AnchoredAtom3196 chi ∧
      ¬Fin15AnchoredAtom3202 chi ∧
      ¬Fin15AnchoredAtom3527 chi ∧
      ¬Fin15AnchoredAtom3684 chi ∧
      ¬Fin15AnchoredAtom3685 chi ∧
      ¬Fin15AnchoredAtom3691 chi ∧
      ¬Fin15AnchoredAtom3697 chi ∧
      ¬Fin15AnchoredAtom4022 chi ∧
      ¬Fin15AnchoredAtom4352 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 9, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26127
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1826 Fin15AnchoredAtom1827 Fin15AnchoredAtom1830
    Fin15AnchoredAtom1831 Fin15AnchoredAtom1872 Fin15AnchoredAtom1875 Fin15AnchoredAtom1876
    Fin15AnchoredAtom1879 Fin15AnchoredAtom1880 Fin15AnchoredAtom1886 Fin15AnchoredAtom1927
    Fin15AnchoredAtom1930 Fin15AnchoredAtom1931 Fin15AnchoredAtom1934 Fin15AnchoredAtom1935
    Fin15AnchoredAtom1941 Fin15AnchoredAtom2089 Fin15AnchoredAtom2090 Fin15AnchoredAtom2096
    Fin15AnchoredAtom2102 Fin15AnchoredAtom2147 Fin15AnchoredAtom2150 Fin15AnchoredAtom2151
    Fin15AnchoredAtom2154 Fin15AnchoredAtom2155 Fin15AnchoredAtom2161 Fin15AnchoredAtom2309
    Fin15AnchoredAtom2310 Fin15AnchoredAtom2316 Fin15AnchoredAtom2322 Fin15AnchoredAtom2474
    Fin15AnchoredAtom2475 Fin15AnchoredAtom2481 Fin15AnchoredAtom2487 Fin15AnchoredAtom2812
    Fin15AnchoredAtom2862 Fin15AnchoredAtom2865 Fin15AnchoredAtom2866 Fin15AnchoredAtom2869
    Fin15AnchoredAtom2870 Fin15AnchoredAtom2876 Fin15AnchoredAtom3024 Fin15AnchoredAtom3025
    Fin15AnchoredAtom3031 Fin15AnchoredAtom3037 Fin15AnchoredAtom3189 Fin15AnchoredAtom3190
    Fin15AnchoredAtom3196 Fin15AnchoredAtom3202 Fin15AnchoredAtom3527 Fin15AnchoredAtom3684
    Fin15AnchoredAtom3685 Fin15AnchoredAtom3691 Fin15AnchoredAtom3697 Fin15AnchoredAtom4022
    Fin15AnchoredAtom4352 at hbad
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

theorem fin15Anchored_clause30629 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom1886 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom1939 chi ∧
      ¬Fin15AnchoredAtom1940 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
      ¬Fin15AnchoredAtom2094 chi ∧
      ¬Fin15AnchoredAtom2095 chi ∧
      ¬Fin15AnchoredAtom2096 chi ∧
      ¬Fin15AnchoredAtom2106 chi ∧
      ¬Fin15AnchoredAtom2149 chi ∧
      ¬Fin15AnchoredAtom2150 chi ∧
      ¬Fin15AnchoredAtom2151 chi ∧
      ¬Fin15AnchoredAtom2159 chi ∧
      ¬Fin15AnchoredAtom2160 chi ∧
      ¬Fin15AnchoredAtom2161 chi ∧
      ¬Fin15AnchoredAtom2314 chi ∧
      ¬Fin15AnchoredAtom2315 chi ∧
      ¬Fin15AnchoredAtom2316 chi ∧
      ¬Fin15AnchoredAtom2326 chi ∧
      ¬Fin15AnchoredAtom2479 chi ∧
      ¬Fin15AnchoredAtom2480 chi ∧
      ¬Fin15AnchoredAtom2481 chi ∧
      ¬Fin15AnchoredAtom2491 chi ∧
      ¬Fin15AnchoredAtom2816 chi ∧
      ¬Fin15AnchoredAtom2864 chi ∧
      ¬Fin15AnchoredAtom2865 chi ∧
      ¬Fin15AnchoredAtom2866 chi ∧
      ¬Fin15AnchoredAtom2874 chi ∧
      ¬Fin15AnchoredAtom2875 chi ∧
      ¬Fin15AnchoredAtom2876 chi ∧
      ¬Fin15AnchoredAtom3029 chi ∧
      ¬Fin15AnchoredAtom3030 chi ∧
      ¬Fin15AnchoredAtom3031 chi ∧
      ¬Fin15AnchoredAtom3041 chi ∧
      ¬Fin15AnchoredAtom3194 chi ∧
      ¬Fin15AnchoredAtom3195 chi ∧
      ¬Fin15AnchoredAtom3196 chi ∧
      ¬Fin15AnchoredAtom3206 chi ∧
      ¬Fin15AnchoredAtom3531 chi ∧
      ¬Fin15AnchoredAtom3689 chi ∧
      ¬Fin15AnchoredAtom3690 chi ∧
      ¬Fin15AnchoredAtom3691 chi ∧
      ¬Fin15AnchoredAtom3701 chi ∧
      ¬Fin15AnchoredAtom4026 chi ∧
      ¬Fin15AnchoredAtom4356 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 9, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29199
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1826 Fin15AnchoredAtom1829 Fin15AnchoredAtom1830
    Fin15AnchoredAtom1831 Fin15AnchoredAtom1874 Fin15AnchoredAtom1875 Fin15AnchoredAtom1876
    Fin15AnchoredAtom1884 Fin15AnchoredAtom1885 Fin15AnchoredAtom1886 Fin15AnchoredAtom1929
    Fin15AnchoredAtom1930 Fin15AnchoredAtom1931 Fin15AnchoredAtom1939 Fin15AnchoredAtom1940
    Fin15AnchoredAtom1941 Fin15AnchoredAtom2094 Fin15AnchoredAtom2095 Fin15AnchoredAtom2096
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2149 Fin15AnchoredAtom2150 Fin15AnchoredAtom2151
    Fin15AnchoredAtom2159 Fin15AnchoredAtom2160 Fin15AnchoredAtom2161 Fin15AnchoredAtom2314
    Fin15AnchoredAtom2315 Fin15AnchoredAtom2316 Fin15AnchoredAtom2326 Fin15AnchoredAtom2479
    Fin15AnchoredAtom2480 Fin15AnchoredAtom2481 Fin15AnchoredAtom2491 Fin15AnchoredAtom2816
    Fin15AnchoredAtom2864 Fin15AnchoredAtom2865 Fin15AnchoredAtom2866 Fin15AnchoredAtom2874
    Fin15AnchoredAtom2875 Fin15AnchoredAtom2876 Fin15AnchoredAtom3029 Fin15AnchoredAtom3030
    Fin15AnchoredAtom3031 Fin15AnchoredAtom3041 Fin15AnchoredAtom3194 Fin15AnchoredAtom3195
    Fin15AnchoredAtom3196 Fin15AnchoredAtom3206 Fin15AnchoredAtom3531 Fin15AnchoredAtom3689
    Fin15AnchoredAtom3690 Fin15AnchoredAtom3691 Fin15AnchoredAtom3701 Fin15AnchoredAtom4026
    Fin15AnchoredAtom4356 at hbad
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

theorem fin15Anchored_clause30630 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom1886 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom1935 chi ∧
      ¬Fin15AnchoredAtom1939 chi ∧
      ¬Fin15AnchoredAtom1940 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
      ¬Fin15AnchoredAtom2100 chi ∧
      ¬Fin15AnchoredAtom2101 chi ∧
      ¬Fin15AnchoredAtom2102 chi ∧
      ¬Fin15AnchoredAtom2106 chi ∧
      ¬Fin15AnchoredAtom2153 chi ∧
      ¬Fin15AnchoredAtom2154 chi ∧
      ¬Fin15AnchoredAtom2155 chi ∧
      ¬Fin15AnchoredAtom2159 chi ∧
      ¬Fin15AnchoredAtom2160 chi ∧
      ¬Fin15AnchoredAtom2161 chi ∧
      ¬Fin15AnchoredAtom2320 chi ∧
      ¬Fin15AnchoredAtom2321 chi ∧
      ¬Fin15AnchoredAtom2322 chi ∧
      ¬Fin15AnchoredAtom2326 chi ∧
      ¬Fin15AnchoredAtom2485 chi ∧
      ¬Fin15AnchoredAtom2486 chi ∧
      ¬Fin15AnchoredAtom2487 chi ∧
      ¬Fin15AnchoredAtom2491 chi ∧
      ¬Fin15AnchoredAtom2820 chi ∧
      ¬Fin15AnchoredAtom2868 chi ∧
      ¬Fin15AnchoredAtom2869 chi ∧
      ¬Fin15AnchoredAtom2870 chi ∧
      ¬Fin15AnchoredAtom2874 chi ∧
      ¬Fin15AnchoredAtom2875 chi ∧
      ¬Fin15AnchoredAtom2876 chi ∧
      ¬Fin15AnchoredAtom3035 chi ∧
      ¬Fin15AnchoredAtom3036 chi ∧
      ¬Fin15AnchoredAtom3037 chi ∧
      ¬Fin15AnchoredAtom3041 chi ∧
      ¬Fin15AnchoredAtom3200 chi ∧
      ¬Fin15AnchoredAtom3201 chi ∧
      ¬Fin15AnchoredAtom3202 chi ∧
      ¬Fin15AnchoredAtom3206 chi ∧
      ¬Fin15AnchoredAtom3535 chi ∧
      ¬Fin15AnchoredAtom3695 chi ∧
      ¬Fin15AnchoredAtom3696 chi ∧
      ¬Fin15AnchoredAtom3697 chi ∧
      ¬Fin15AnchoredAtom3701 chi ∧
      ¬Fin15AnchoredAtom4030 chi ∧
      ¬Fin15AnchoredAtom4360 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29711
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1827 Fin15AnchoredAtom1829 Fin15AnchoredAtom1830
    Fin15AnchoredAtom1831 Fin15AnchoredAtom1878 Fin15AnchoredAtom1879 Fin15AnchoredAtom1880
    Fin15AnchoredAtom1884 Fin15AnchoredAtom1885 Fin15AnchoredAtom1886 Fin15AnchoredAtom1933
    Fin15AnchoredAtom1934 Fin15AnchoredAtom1935 Fin15AnchoredAtom1939 Fin15AnchoredAtom1940
    Fin15AnchoredAtom1941 Fin15AnchoredAtom2100 Fin15AnchoredAtom2101 Fin15AnchoredAtom2102
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2153 Fin15AnchoredAtom2154 Fin15AnchoredAtom2155
    Fin15AnchoredAtom2159 Fin15AnchoredAtom2160 Fin15AnchoredAtom2161 Fin15AnchoredAtom2320
    Fin15AnchoredAtom2321 Fin15AnchoredAtom2322 Fin15AnchoredAtom2326 Fin15AnchoredAtom2485
    Fin15AnchoredAtom2486 Fin15AnchoredAtom2487 Fin15AnchoredAtom2491 Fin15AnchoredAtom2820
    Fin15AnchoredAtom2868 Fin15AnchoredAtom2869 Fin15AnchoredAtom2870 Fin15AnchoredAtom2874
    Fin15AnchoredAtom2875 Fin15AnchoredAtom2876 Fin15AnchoredAtom3035 Fin15AnchoredAtom3036
    Fin15AnchoredAtom3037 Fin15AnchoredAtom3041 Fin15AnchoredAtom3200 Fin15AnchoredAtom3201
    Fin15AnchoredAtom3202 Fin15AnchoredAtom3206 Fin15AnchoredAtom3535 Fin15AnchoredAtom3695
    Fin15AnchoredAtom3696 Fin15AnchoredAtom3697 Fin15AnchoredAtom3701 Fin15AnchoredAtom4030
    Fin15AnchoredAtom4360 at hbad
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

theorem fin15Anchored_clause30631 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom1942 chi ∧
      ¬Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom1987 chi ∧
      ¬Fin15AnchoredAtom1989 chi ∧
      ¬Fin15AnchoredAtom1996 chi ∧
      ¬Fin15AnchoredAtom2024 chi ∧
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
      ¬Fin15AnchoredAtom2492 chi ∧
      ¬Fin15AnchoredAtom2494 chi ∧
      ¬Fin15AnchoredAtom2501 chi ∧
      ¬Fin15AnchoredAtom2529 chi ∧
      ¬Fin15AnchoredAtom2613 chi ∧
      ¬Fin15AnchoredAtom2877 chi ∧
      ¬Fin15AnchoredAtom2878 chi ∧
      ¬Fin15AnchoredAtom2880 chi ∧
      ¬Fin15AnchoredAtom2886 chi ∧
      ¬Fin15AnchoredAtom2888 chi ∧
      ¬Fin15AnchoredAtom2895 chi ∧
      ¬Fin15AnchoredAtom2922 chi ∧
      ¬Fin15AnchoredAtom2924 chi ∧
      ¬Fin15AnchoredAtom2931 chi ∧
      ¬Fin15AnchoredAtom2959 chi ∧
      ¬Fin15AnchoredAtom3207 chi ∧
      ¬Fin15AnchoredAtom3209 chi ∧
      ¬Fin15AnchoredAtom3216 chi ∧
      ¬Fin15AnchoredAtom3244 chi ∧
      ¬Fin15AnchoredAtom3328 chi ∧
      ¬Fin15AnchoredAtom3702 chi ∧
      ¬Fin15AnchoredAtom3704 chi ∧
      ¬Fin15AnchoredAtom3711 chi ∧
      ¬Fin15AnchoredAtom3739 chi ∧
      ¬Fin15AnchoredAtom3823 chi ∧
      ¬Fin15AnchoredAtom4363 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 5, 6, 7, 9}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask00759
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1832 Fin15AnchoredAtom1833 Fin15AnchoredAtom1834
    Fin15AnchoredAtom1836 Fin15AnchoredAtom1842 Fin15AnchoredAtom1843 Fin15AnchoredAtom1845
    Fin15AnchoredAtom1851 Fin15AnchoredAtom1853 Fin15AnchoredAtom1860 Fin15AnchoredAtom1942
    Fin15AnchoredAtom1943 Fin15AnchoredAtom1945 Fin15AnchoredAtom1951 Fin15AnchoredAtom1953
    Fin15AnchoredAtom1960 Fin15AnchoredAtom1987 Fin15AnchoredAtom1989 Fin15AnchoredAtom1996
    Fin15AnchoredAtom2024 Fin15AnchoredAtom2162 Fin15AnchoredAtom2163 Fin15AnchoredAtom2165
    Fin15AnchoredAtom2171 Fin15AnchoredAtom2173 Fin15AnchoredAtom2180 Fin15AnchoredAtom2207
    Fin15AnchoredAtom2209 Fin15AnchoredAtom2216 Fin15AnchoredAtom2244 Fin15AnchoredAtom2492
    Fin15AnchoredAtom2494 Fin15AnchoredAtom2501 Fin15AnchoredAtom2529 Fin15AnchoredAtom2613
    Fin15AnchoredAtom2877 Fin15AnchoredAtom2878 Fin15AnchoredAtom2880 Fin15AnchoredAtom2886
    Fin15AnchoredAtom2888 Fin15AnchoredAtom2895 Fin15AnchoredAtom2922 Fin15AnchoredAtom2924
    Fin15AnchoredAtom2931 Fin15AnchoredAtom2959 Fin15AnchoredAtom3207 Fin15AnchoredAtom3209
    Fin15AnchoredAtom3216 Fin15AnchoredAtom3244 Fin15AnchoredAtom3328 Fin15AnchoredAtom3702
    Fin15AnchoredAtom3704 Fin15AnchoredAtom3711 Fin15AnchoredAtom3739 Fin15AnchoredAtom3823
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

theorem fin15Anchored_clause30632 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom1942 chi ∧
      ¬Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom1987 chi ∧
      ¬Fin15AnchoredAtom1990 chi ∧
      ¬Fin15AnchoredAtom1997 chi ∧
      ¬Fin15AnchoredAtom2025 chi ∧
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
      ¬Fin15AnchoredAtom2492 chi ∧
      ¬Fin15AnchoredAtom2495 chi ∧
      ¬Fin15AnchoredAtom2502 chi ∧
      ¬Fin15AnchoredAtom2530 chi ∧
      ¬Fin15AnchoredAtom2614 chi ∧
      ¬Fin15AnchoredAtom2877 chi ∧
      ¬Fin15AnchoredAtom2878 chi ∧
      ¬Fin15AnchoredAtom2881 chi ∧
      ¬Fin15AnchoredAtom2886 chi ∧
      ¬Fin15AnchoredAtom2889 chi ∧
      ¬Fin15AnchoredAtom2896 chi ∧
      ¬Fin15AnchoredAtom2922 chi ∧
      ¬Fin15AnchoredAtom2925 chi ∧
      ¬Fin15AnchoredAtom2932 chi ∧
      ¬Fin15AnchoredAtom2960 chi ∧
      ¬Fin15AnchoredAtom3207 chi ∧
      ¬Fin15AnchoredAtom3210 chi ∧
      ¬Fin15AnchoredAtom3217 chi ∧
      ¬Fin15AnchoredAtom3245 chi ∧
      ¬Fin15AnchoredAtom3329 chi ∧
      ¬Fin15AnchoredAtom3702 chi ∧
      ¬Fin15AnchoredAtom3705 chi ∧
      ¬Fin15AnchoredAtom3712 chi ∧
      ¬Fin15AnchoredAtom3740 chi ∧
      ¬Fin15AnchoredAtom3824 chi ∧
      ¬Fin15AnchoredAtom4364 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 5, 6, 7, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask01271
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1832 Fin15AnchoredAtom1833 Fin15AnchoredAtom1834
    Fin15AnchoredAtom1837 Fin15AnchoredAtom1842 Fin15AnchoredAtom1843 Fin15AnchoredAtom1846
    Fin15AnchoredAtom1851 Fin15AnchoredAtom1854 Fin15AnchoredAtom1861 Fin15AnchoredAtom1942
    Fin15AnchoredAtom1943 Fin15AnchoredAtom1946 Fin15AnchoredAtom1951 Fin15AnchoredAtom1954
    Fin15AnchoredAtom1961 Fin15AnchoredAtom1987 Fin15AnchoredAtom1990 Fin15AnchoredAtom1997
    Fin15AnchoredAtom2025 Fin15AnchoredAtom2162 Fin15AnchoredAtom2163 Fin15AnchoredAtom2166
    Fin15AnchoredAtom2171 Fin15AnchoredAtom2174 Fin15AnchoredAtom2181 Fin15AnchoredAtom2207
    Fin15AnchoredAtom2210 Fin15AnchoredAtom2217 Fin15AnchoredAtom2245 Fin15AnchoredAtom2492
    Fin15AnchoredAtom2495 Fin15AnchoredAtom2502 Fin15AnchoredAtom2530 Fin15AnchoredAtom2614
    Fin15AnchoredAtom2877 Fin15AnchoredAtom2878 Fin15AnchoredAtom2881 Fin15AnchoredAtom2886
    Fin15AnchoredAtom2889 Fin15AnchoredAtom2896 Fin15AnchoredAtom2922 Fin15AnchoredAtom2925
    Fin15AnchoredAtom2932 Fin15AnchoredAtom2960 Fin15AnchoredAtom3207 Fin15AnchoredAtom3210
    Fin15AnchoredAtom3217 Fin15AnchoredAtom3245 Fin15AnchoredAtom3329 Fin15AnchoredAtom3702
    Fin15AnchoredAtom3705 Fin15AnchoredAtom3712 Fin15AnchoredAtom3740 Fin15AnchoredAtom3824
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

theorem fin15Anchored_clause30633 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom1942 chi ∧
      ¬Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom1987 chi ∧
      ¬Fin15AnchoredAtom1992 chi ∧
      ¬Fin15AnchoredAtom1999 chi ∧
      ¬Fin15AnchoredAtom2027 chi ∧
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
      ¬Fin15AnchoredAtom2492 chi ∧
      ¬Fin15AnchoredAtom2497 chi ∧
      ¬Fin15AnchoredAtom2504 chi ∧
      ¬Fin15AnchoredAtom2532 chi ∧
      ¬Fin15AnchoredAtom2616 chi ∧
      ¬Fin15AnchoredAtom2877 chi ∧
      ¬Fin15AnchoredAtom2878 chi ∧
      ¬Fin15AnchoredAtom2883 chi ∧
      ¬Fin15AnchoredAtom2886 chi ∧
      ¬Fin15AnchoredAtom2891 chi ∧
      ¬Fin15AnchoredAtom2898 chi ∧
      ¬Fin15AnchoredAtom2922 chi ∧
      ¬Fin15AnchoredAtom2927 chi ∧
      ¬Fin15AnchoredAtom2934 chi ∧
      ¬Fin15AnchoredAtom2962 chi ∧
      ¬Fin15AnchoredAtom3207 chi ∧
      ¬Fin15AnchoredAtom3212 chi ∧
      ¬Fin15AnchoredAtom3219 chi ∧
      ¬Fin15AnchoredAtom3247 chi ∧
      ¬Fin15AnchoredAtom3331 chi ∧
      ¬Fin15AnchoredAtom3702 chi ∧
      ¬Fin15AnchoredAtom3707 chi ∧
      ¬Fin15AnchoredAtom3714 chi ∧
      ¬Fin15AnchoredAtom3742 chi ∧
      ¬Fin15AnchoredAtom3826 chi ∧
      ¬Fin15AnchoredAtom4366 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 5, 6, 7, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask04343
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1832 Fin15AnchoredAtom1833 Fin15AnchoredAtom1834
    Fin15AnchoredAtom1839 Fin15AnchoredAtom1842 Fin15AnchoredAtom1843 Fin15AnchoredAtom1848
    Fin15AnchoredAtom1851 Fin15AnchoredAtom1856 Fin15AnchoredAtom1863 Fin15AnchoredAtom1942
    Fin15AnchoredAtom1943 Fin15AnchoredAtom1948 Fin15AnchoredAtom1951 Fin15AnchoredAtom1956
    Fin15AnchoredAtom1963 Fin15AnchoredAtom1987 Fin15AnchoredAtom1992 Fin15AnchoredAtom1999
    Fin15AnchoredAtom2027 Fin15AnchoredAtom2162 Fin15AnchoredAtom2163 Fin15AnchoredAtom2168
    Fin15AnchoredAtom2171 Fin15AnchoredAtom2176 Fin15AnchoredAtom2183 Fin15AnchoredAtom2207
    Fin15AnchoredAtom2212 Fin15AnchoredAtom2219 Fin15AnchoredAtom2247 Fin15AnchoredAtom2492
    Fin15AnchoredAtom2497 Fin15AnchoredAtom2504 Fin15AnchoredAtom2532 Fin15AnchoredAtom2616
    Fin15AnchoredAtom2877 Fin15AnchoredAtom2878 Fin15AnchoredAtom2883 Fin15AnchoredAtom2886
    Fin15AnchoredAtom2891 Fin15AnchoredAtom2898 Fin15AnchoredAtom2922 Fin15AnchoredAtom2927
    Fin15AnchoredAtom2934 Fin15AnchoredAtom2962 Fin15AnchoredAtom3207 Fin15AnchoredAtom3212
    Fin15AnchoredAtom3219 Fin15AnchoredAtom3247 Fin15AnchoredAtom3331 Fin15AnchoredAtom3702
    Fin15AnchoredAtom3707 Fin15AnchoredAtom3714 Fin15AnchoredAtom3742 Fin15AnchoredAtom3826
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

theorem fin15Anchored_clause30634 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom1942 chi ∧
      ¬Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom1987 chi ∧
      ¬Fin15AnchoredAtom1993 chi ∧
      ¬Fin15AnchoredAtom2000 chi ∧
      ¬Fin15AnchoredAtom2028 chi ∧
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
      ¬Fin15AnchoredAtom2492 chi ∧
      ¬Fin15AnchoredAtom2498 chi ∧
      ¬Fin15AnchoredAtom2505 chi ∧
      ¬Fin15AnchoredAtom2533 chi ∧
      ¬Fin15AnchoredAtom2617 chi ∧
      ¬Fin15AnchoredAtom2877 chi ∧
      ¬Fin15AnchoredAtom2878 chi ∧
      ¬Fin15AnchoredAtom2884 chi ∧
      ¬Fin15AnchoredAtom2886 chi ∧
      ¬Fin15AnchoredAtom2892 chi ∧
      ¬Fin15AnchoredAtom2899 chi ∧
      ¬Fin15AnchoredAtom2922 chi ∧
      ¬Fin15AnchoredAtom2928 chi ∧
      ¬Fin15AnchoredAtom2935 chi ∧
      ¬Fin15AnchoredAtom2963 chi ∧
      ¬Fin15AnchoredAtom3207 chi ∧
      ¬Fin15AnchoredAtom3213 chi ∧
      ¬Fin15AnchoredAtom3220 chi ∧
      ¬Fin15AnchoredAtom3248 chi ∧
      ¬Fin15AnchoredAtom3332 chi ∧
      ¬Fin15AnchoredAtom3702 chi ∧
      ¬Fin15AnchoredAtom3708 chi ∧
      ¬Fin15AnchoredAtom3715 chi ∧
      ¬Fin15AnchoredAtom3743 chi ∧
      ¬Fin15AnchoredAtom3827 chi ∧
      ¬Fin15AnchoredAtom4367 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 5, 6, 7, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask08439
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1832 Fin15AnchoredAtom1833 Fin15AnchoredAtom1834
    Fin15AnchoredAtom1840 Fin15AnchoredAtom1842 Fin15AnchoredAtom1843 Fin15AnchoredAtom1849
    Fin15AnchoredAtom1851 Fin15AnchoredAtom1857 Fin15AnchoredAtom1864 Fin15AnchoredAtom1942
    Fin15AnchoredAtom1943 Fin15AnchoredAtom1949 Fin15AnchoredAtom1951 Fin15AnchoredAtom1957
    Fin15AnchoredAtom1964 Fin15AnchoredAtom1987 Fin15AnchoredAtom1993 Fin15AnchoredAtom2000
    Fin15AnchoredAtom2028 Fin15AnchoredAtom2162 Fin15AnchoredAtom2163 Fin15AnchoredAtom2169
    Fin15AnchoredAtom2171 Fin15AnchoredAtom2177 Fin15AnchoredAtom2184 Fin15AnchoredAtom2207
    Fin15AnchoredAtom2213 Fin15AnchoredAtom2220 Fin15AnchoredAtom2248 Fin15AnchoredAtom2492
    Fin15AnchoredAtom2498 Fin15AnchoredAtom2505 Fin15AnchoredAtom2533 Fin15AnchoredAtom2617
    Fin15AnchoredAtom2877 Fin15AnchoredAtom2878 Fin15AnchoredAtom2884 Fin15AnchoredAtom2886
    Fin15AnchoredAtom2892 Fin15AnchoredAtom2899 Fin15AnchoredAtom2922 Fin15AnchoredAtom2928
    Fin15AnchoredAtom2935 Fin15AnchoredAtom2963 Fin15AnchoredAtom3207 Fin15AnchoredAtom3213
    Fin15AnchoredAtom3220 Fin15AnchoredAtom3248 Fin15AnchoredAtom3332 Fin15AnchoredAtom3702
    Fin15AnchoredAtom3708 Fin15AnchoredAtom3715 Fin15AnchoredAtom3743 Fin15AnchoredAtom3827
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

theorem fin15Anchored_clause30635 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom1942 chi ∧
      ¬Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom1987 chi ∧
      ¬Fin15AnchoredAtom1994 chi ∧
      ¬Fin15AnchoredAtom2001 chi ∧
      ¬Fin15AnchoredAtom2029 chi ∧
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
      ¬Fin15AnchoredAtom2492 chi ∧
      ¬Fin15AnchoredAtom2499 chi ∧
      ¬Fin15AnchoredAtom2506 chi ∧
      ¬Fin15AnchoredAtom2534 chi ∧
      ¬Fin15AnchoredAtom2618 chi ∧
      ¬Fin15AnchoredAtom2877 chi ∧
      ¬Fin15AnchoredAtom2878 chi ∧
      ¬Fin15AnchoredAtom2885 chi ∧
      ¬Fin15AnchoredAtom2886 chi ∧
      ¬Fin15AnchoredAtom2893 chi ∧
      ¬Fin15AnchoredAtom2900 chi ∧
      ¬Fin15AnchoredAtom2922 chi ∧
      ¬Fin15AnchoredAtom2929 chi ∧
      ¬Fin15AnchoredAtom2936 chi ∧
      ¬Fin15AnchoredAtom2964 chi ∧
      ¬Fin15AnchoredAtom3207 chi ∧
      ¬Fin15AnchoredAtom3214 chi ∧
      ¬Fin15AnchoredAtom3221 chi ∧
      ¬Fin15AnchoredAtom3249 chi ∧
      ¬Fin15AnchoredAtom3333 chi ∧
      ¬Fin15AnchoredAtom3702 chi ∧
      ¬Fin15AnchoredAtom3709 chi ∧
      ¬Fin15AnchoredAtom3716 chi ∧
      ¬Fin15AnchoredAtom3744 chi ∧
      ¬Fin15AnchoredAtom3828 chi ∧
      ¬Fin15AnchoredAtom4368 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 5, 6, 7, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask16631
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1832 Fin15AnchoredAtom1833 Fin15AnchoredAtom1834
    Fin15AnchoredAtom1841 Fin15AnchoredAtom1842 Fin15AnchoredAtom1843 Fin15AnchoredAtom1850
    Fin15AnchoredAtom1851 Fin15AnchoredAtom1858 Fin15AnchoredAtom1865 Fin15AnchoredAtom1942
    Fin15AnchoredAtom1943 Fin15AnchoredAtom1950 Fin15AnchoredAtom1951 Fin15AnchoredAtom1958
    Fin15AnchoredAtom1965 Fin15AnchoredAtom1987 Fin15AnchoredAtom1994 Fin15AnchoredAtom2001
    Fin15AnchoredAtom2029 Fin15AnchoredAtom2162 Fin15AnchoredAtom2163 Fin15AnchoredAtom2170
    Fin15AnchoredAtom2171 Fin15AnchoredAtom2178 Fin15AnchoredAtom2185 Fin15AnchoredAtom2207
    Fin15AnchoredAtom2214 Fin15AnchoredAtom2221 Fin15AnchoredAtom2249 Fin15AnchoredAtom2492
    Fin15AnchoredAtom2499 Fin15AnchoredAtom2506 Fin15AnchoredAtom2534 Fin15AnchoredAtom2618
    Fin15AnchoredAtom2877 Fin15AnchoredAtom2878 Fin15AnchoredAtom2885 Fin15AnchoredAtom2886
    Fin15AnchoredAtom2893 Fin15AnchoredAtom2900 Fin15AnchoredAtom2922 Fin15AnchoredAtom2929
    Fin15AnchoredAtom2936 Fin15AnchoredAtom2964 Fin15AnchoredAtom3207 Fin15AnchoredAtom3214
    Fin15AnchoredAtom3221 Fin15AnchoredAtom3249 Fin15AnchoredAtom3333 Fin15AnchoredAtom3702
    Fin15AnchoredAtom3709 Fin15AnchoredAtom3716 Fin15AnchoredAtom3744 Fin15AnchoredAtom3828
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

theorem fin15Anchored_clause30636 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom1942 chi ∧
      ¬Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom1989 chi ∧
      ¬Fin15AnchoredAtom1990 chi ∧
      ¬Fin15AnchoredAtom2008 chi ∧
      ¬Fin15AnchoredAtom2036 chi ∧
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
      ¬Fin15AnchoredAtom2494 chi ∧
      ¬Fin15AnchoredAtom2495 chi ∧
      ¬Fin15AnchoredAtom2513 chi ∧
      ¬Fin15AnchoredAtom2541 chi ∧
      ¬Fin15AnchoredAtom2625 chi ∧
      ¬Fin15AnchoredAtom2877 chi ∧
      ¬Fin15AnchoredAtom2880 chi ∧
      ¬Fin15AnchoredAtom2881 chi ∧
      ¬Fin15AnchoredAtom2888 chi ∧
      ¬Fin15AnchoredAtom2889 chi ∧
      ¬Fin15AnchoredAtom2907 chi ∧
      ¬Fin15AnchoredAtom2924 chi ∧
      ¬Fin15AnchoredAtom2925 chi ∧
      ¬Fin15AnchoredAtom2943 chi ∧
      ¬Fin15AnchoredAtom2971 chi ∧
      ¬Fin15AnchoredAtom3209 chi ∧
      ¬Fin15AnchoredAtom3210 chi ∧
      ¬Fin15AnchoredAtom3228 chi ∧
      ¬Fin15AnchoredAtom3256 chi ∧
      ¬Fin15AnchoredAtom3340 chi ∧
      ¬Fin15AnchoredAtom3704 chi ∧
      ¬Fin15AnchoredAtom3705 chi ∧
      ¬Fin15AnchoredAtom3723 chi ∧
      ¬Fin15AnchoredAtom3751 chi ∧
      ¬Fin15AnchoredAtom3835 chi ∧
      ¬Fin15AnchoredAtom4375 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 5, 6, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask01655
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1832 Fin15AnchoredAtom1833 Fin15AnchoredAtom1836
    Fin15AnchoredAtom1837 Fin15AnchoredAtom1842 Fin15AnchoredAtom1845 Fin15AnchoredAtom1846
    Fin15AnchoredAtom1853 Fin15AnchoredAtom1854 Fin15AnchoredAtom1872 Fin15AnchoredAtom1942
    Fin15AnchoredAtom1945 Fin15AnchoredAtom1946 Fin15AnchoredAtom1953 Fin15AnchoredAtom1954
    Fin15AnchoredAtom1972 Fin15AnchoredAtom1989 Fin15AnchoredAtom1990 Fin15AnchoredAtom2008
    Fin15AnchoredAtom2036 Fin15AnchoredAtom2162 Fin15AnchoredAtom2165 Fin15AnchoredAtom2166
    Fin15AnchoredAtom2173 Fin15AnchoredAtom2174 Fin15AnchoredAtom2192 Fin15AnchoredAtom2209
    Fin15AnchoredAtom2210 Fin15AnchoredAtom2228 Fin15AnchoredAtom2256 Fin15AnchoredAtom2494
    Fin15AnchoredAtom2495 Fin15AnchoredAtom2513 Fin15AnchoredAtom2541 Fin15AnchoredAtom2625
    Fin15AnchoredAtom2877 Fin15AnchoredAtom2880 Fin15AnchoredAtom2881 Fin15AnchoredAtom2888
    Fin15AnchoredAtom2889 Fin15AnchoredAtom2907 Fin15AnchoredAtom2924 Fin15AnchoredAtom2925
    Fin15AnchoredAtom2943 Fin15AnchoredAtom2971 Fin15AnchoredAtom3209 Fin15AnchoredAtom3210
    Fin15AnchoredAtom3228 Fin15AnchoredAtom3256 Fin15AnchoredAtom3340 Fin15AnchoredAtom3704
    Fin15AnchoredAtom3705 Fin15AnchoredAtom3723 Fin15AnchoredAtom3751 Fin15AnchoredAtom3835
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

theorem fin15Anchored_clause30637 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom1942 chi ∧
      ¬Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom1989 chi ∧
      ¬Fin15AnchoredAtom1992 chi ∧
      ¬Fin15AnchoredAtom2010 chi ∧
      ¬Fin15AnchoredAtom2038 chi ∧
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
      ¬Fin15AnchoredAtom2494 chi ∧
      ¬Fin15AnchoredAtom2497 chi ∧
      ¬Fin15AnchoredAtom2515 chi ∧
      ¬Fin15AnchoredAtom2543 chi ∧
      ¬Fin15AnchoredAtom2627 chi ∧
      ¬Fin15AnchoredAtom2877 chi ∧
      ¬Fin15AnchoredAtom2880 chi ∧
      ¬Fin15AnchoredAtom2883 chi ∧
      ¬Fin15AnchoredAtom2888 chi ∧
      ¬Fin15AnchoredAtom2891 chi ∧
      ¬Fin15AnchoredAtom2909 chi ∧
      ¬Fin15AnchoredAtom2924 chi ∧
      ¬Fin15AnchoredAtom2927 chi ∧
      ¬Fin15AnchoredAtom2945 chi ∧
      ¬Fin15AnchoredAtom2973 chi ∧
      ¬Fin15AnchoredAtom3209 chi ∧
      ¬Fin15AnchoredAtom3212 chi ∧
      ¬Fin15AnchoredAtom3230 chi ∧
      ¬Fin15AnchoredAtom3258 chi ∧
      ¬Fin15AnchoredAtom3342 chi ∧
      ¬Fin15AnchoredAtom3704 chi ∧
      ¬Fin15AnchoredAtom3707 chi ∧
      ¬Fin15AnchoredAtom3725 chi ∧
      ¬Fin15AnchoredAtom3753 chi ∧
      ¬Fin15AnchoredAtom3837 chi ∧
      ¬Fin15AnchoredAtom4377 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 5, 6, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask04727
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1832 Fin15AnchoredAtom1833 Fin15AnchoredAtom1836
    Fin15AnchoredAtom1839 Fin15AnchoredAtom1842 Fin15AnchoredAtom1845 Fin15AnchoredAtom1848
    Fin15AnchoredAtom1853 Fin15AnchoredAtom1856 Fin15AnchoredAtom1874 Fin15AnchoredAtom1942
    Fin15AnchoredAtom1945 Fin15AnchoredAtom1948 Fin15AnchoredAtom1953 Fin15AnchoredAtom1956
    Fin15AnchoredAtom1974 Fin15AnchoredAtom1989 Fin15AnchoredAtom1992 Fin15AnchoredAtom2010
    Fin15AnchoredAtom2038 Fin15AnchoredAtom2162 Fin15AnchoredAtom2165 Fin15AnchoredAtom2168
    Fin15AnchoredAtom2173 Fin15AnchoredAtom2176 Fin15AnchoredAtom2194 Fin15AnchoredAtom2209
    Fin15AnchoredAtom2212 Fin15AnchoredAtom2230 Fin15AnchoredAtom2258 Fin15AnchoredAtom2494
    Fin15AnchoredAtom2497 Fin15AnchoredAtom2515 Fin15AnchoredAtom2543 Fin15AnchoredAtom2627
    Fin15AnchoredAtom2877 Fin15AnchoredAtom2880 Fin15AnchoredAtom2883 Fin15AnchoredAtom2888
    Fin15AnchoredAtom2891 Fin15AnchoredAtom2909 Fin15AnchoredAtom2924 Fin15AnchoredAtom2927
    Fin15AnchoredAtom2945 Fin15AnchoredAtom2973 Fin15AnchoredAtom3209 Fin15AnchoredAtom3212
    Fin15AnchoredAtom3230 Fin15AnchoredAtom3258 Fin15AnchoredAtom3342 Fin15AnchoredAtom3704
    Fin15AnchoredAtom3707 Fin15AnchoredAtom3725 Fin15AnchoredAtom3753 Fin15AnchoredAtom3837
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

theorem fin15Anchored_clause30638 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom1942 chi ∧
      ¬Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom1989 chi ∧
      ¬Fin15AnchoredAtom1993 chi ∧
      ¬Fin15AnchoredAtom2011 chi ∧
      ¬Fin15AnchoredAtom2039 chi ∧
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
      ¬Fin15AnchoredAtom2494 chi ∧
      ¬Fin15AnchoredAtom2498 chi ∧
      ¬Fin15AnchoredAtom2516 chi ∧
      ¬Fin15AnchoredAtom2544 chi ∧
      ¬Fin15AnchoredAtom2628 chi ∧
      ¬Fin15AnchoredAtom2877 chi ∧
      ¬Fin15AnchoredAtom2880 chi ∧
      ¬Fin15AnchoredAtom2884 chi ∧
      ¬Fin15AnchoredAtom2888 chi ∧
      ¬Fin15AnchoredAtom2892 chi ∧
      ¬Fin15AnchoredAtom2910 chi ∧
      ¬Fin15AnchoredAtom2924 chi ∧
      ¬Fin15AnchoredAtom2928 chi ∧
      ¬Fin15AnchoredAtom2946 chi ∧
      ¬Fin15AnchoredAtom2974 chi ∧
      ¬Fin15AnchoredAtom3209 chi ∧
      ¬Fin15AnchoredAtom3213 chi ∧
      ¬Fin15AnchoredAtom3231 chi ∧
      ¬Fin15AnchoredAtom3259 chi ∧
      ¬Fin15AnchoredAtom3343 chi ∧
      ¬Fin15AnchoredAtom3704 chi ∧
      ¬Fin15AnchoredAtom3708 chi ∧
      ¬Fin15AnchoredAtom3726 chi ∧
      ¬Fin15AnchoredAtom3754 chi ∧
      ¬Fin15AnchoredAtom3838 chi ∧
      ¬Fin15AnchoredAtom4378 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 5, 6, 9, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask08823
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1832 Fin15AnchoredAtom1833 Fin15AnchoredAtom1836
    Fin15AnchoredAtom1840 Fin15AnchoredAtom1842 Fin15AnchoredAtom1845 Fin15AnchoredAtom1849
    Fin15AnchoredAtom1853 Fin15AnchoredAtom1857 Fin15AnchoredAtom1875 Fin15AnchoredAtom1942
    Fin15AnchoredAtom1945 Fin15AnchoredAtom1949 Fin15AnchoredAtom1953 Fin15AnchoredAtom1957
    Fin15AnchoredAtom1975 Fin15AnchoredAtom1989 Fin15AnchoredAtom1993 Fin15AnchoredAtom2011
    Fin15AnchoredAtom2039 Fin15AnchoredAtom2162 Fin15AnchoredAtom2165 Fin15AnchoredAtom2169
    Fin15AnchoredAtom2173 Fin15AnchoredAtom2177 Fin15AnchoredAtom2195 Fin15AnchoredAtom2209
    Fin15AnchoredAtom2213 Fin15AnchoredAtom2231 Fin15AnchoredAtom2259 Fin15AnchoredAtom2494
    Fin15AnchoredAtom2498 Fin15AnchoredAtom2516 Fin15AnchoredAtom2544 Fin15AnchoredAtom2628
    Fin15AnchoredAtom2877 Fin15AnchoredAtom2880 Fin15AnchoredAtom2884 Fin15AnchoredAtom2888
    Fin15AnchoredAtom2892 Fin15AnchoredAtom2910 Fin15AnchoredAtom2924 Fin15AnchoredAtom2928
    Fin15AnchoredAtom2946 Fin15AnchoredAtom2974 Fin15AnchoredAtom3209 Fin15AnchoredAtom3213
    Fin15AnchoredAtom3231 Fin15AnchoredAtom3259 Fin15AnchoredAtom3343 Fin15AnchoredAtom3704
    Fin15AnchoredAtom3708 Fin15AnchoredAtom3726 Fin15AnchoredAtom3754 Fin15AnchoredAtom3838
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

theorem fin15Anchored_clause30639 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom1942 chi ∧
      ¬Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom1976 chi ∧
      ¬Fin15AnchoredAtom1989 chi ∧
      ¬Fin15AnchoredAtom1994 chi ∧
      ¬Fin15AnchoredAtom2012 chi ∧
      ¬Fin15AnchoredAtom2040 chi ∧
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
      ¬Fin15AnchoredAtom2494 chi ∧
      ¬Fin15AnchoredAtom2499 chi ∧
      ¬Fin15AnchoredAtom2517 chi ∧
      ¬Fin15AnchoredAtom2545 chi ∧
      ¬Fin15AnchoredAtom2629 chi ∧
      ¬Fin15AnchoredAtom2877 chi ∧
      ¬Fin15AnchoredAtom2880 chi ∧
      ¬Fin15AnchoredAtom2885 chi ∧
      ¬Fin15AnchoredAtom2888 chi ∧
      ¬Fin15AnchoredAtom2893 chi ∧
      ¬Fin15AnchoredAtom2911 chi ∧
      ¬Fin15AnchoredAtom2924 chi ∧
      ¬Fin15AnchoredAtom2929 chi ∧
      ¬Fin15AnchoredAtom2947 chi ∧
      ¬Fin15AnchoredAtom2975 chi ∧
      ¬Fin15AnchoredAtom3209 chi ∧
      ¬Fin15AnchoredAtom3214 chi ∧
      ¬Fin15AnchoredAtom3232 chi ∧
      ¬Fin15AnchoredAtom3260 chi ∧
      ¬Fin15AnchoredAtom3344 chi ∧
      ¬Fin15AnchoredAtom3704 chi ∧
      ¬Fin15AnchoredAtom3709 chi ∧
      ¬Fin15AnchoredAtom3727 chi ∧
      ¬Fin15AnchoredAtom3755 chi ∧
      ¬Fin15AnchoredAtom3839 chi ∧
      ¬Fin15AnchoredAtom4379 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 5, 6, 9, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17015
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1832 Fin15AnchoredAtom1833 Fin15AnchoredAtom1836
    Fin15AnchoredAtom1841 Fin15AnchoredAtom1842 Fin15AnchoredAtom1845 Fin15AnchoredAtom1850
    Fin15AnchoredAtom1853 Fin15AnchoredAtom1858 Fin15AnchoredAtom1876 Fin15AnchoredAtom1942
    Fin15AnchoredAtom1945 Fin15AnchoredAtom1950 Fin15AnchoredAtom1953 Fin15AnchoredAtom1958
    Fin15AnchoredAtom1976 Fin15AnchoredAtom1989 Fin15AnchoredAtom1994 Fin15AnchoredAtom2012
    Fin15AnchoredAtom2040 Fin15AnchoredAtom2162 Fin15AnchoredAtom2165 Fin15AnchoredAtom2170
    Fin15AnchoredAtom2173 Fin15AnchoredAtom2178 Fin15AnchoredAtom2196 Fin15AnchoredAtom2209
    Fin15AnchoredAtom2214 Fin15AnchoredAtom2232 Fin15AnchoredAtom2260 Fin15AnchoredAtom2494
    Fin15AnchoredAtom2499 Fin15AnchoredAtom2517 Fin15AnchoredAtom2545 Fin15AnchoredAtom2629
    Fin15AnchoredAtom2877 Fin15AnchoredAtom2880 Fin15AnchoredAtom2885 Fin15AnchoredAtom2888
    Fin15AnchoredAtom2893 Fin15AnchoredAtom2911 Fin15AnchoredAtom2924 Fin15AnchoredAtom2929
    Fin15AnchoredAtom2947 Fin15AnchoredAtom2975 Fin15AnchoredAtom3209 Fin15AnchoredAtom3214
    Fin15AnchoredAtom3232 Fin15AnchoredAtom3260 Fin15AnchoredAtom3344 Fin15AnchoredAtom3704
    Fin15AnchoredAtom3709 Fin15AnchoredAtom3727 Fin15AnchoredAtom3755 Fin15AnchoredAtom3839
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

theorem fin15Anchored_clause30640 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1838 chi ∧
      ¬Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom1847 chi ∧
      ¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1855 chi ∧
      ¬Fin15AnchoredAtom1877 chi ∧
      ¬Fin15AnchoredAtom1942 chi ∧
      ¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1947 chi ∧
      ¬Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom1955 chi ∧
      ¬Fin15AnchoredAtom1977 chi ∧
      ¬Fin15AnchoredAtom1990 chi ∧
      ¬Fin15AnchoredAtom1991 chi ∧
      ¬Fin15AnchoredAtom2013 chi ∧
      ¬Fin15AnchoredAtom2041 chi ∧
      ¬Fin15AnchoredAtom2162 chi ∧
      ¬Fin15AnchoredAtom2166 chi ∧
      ¬Fin15AnchoredAtom2167 chi ∧
      ¬Fin15AnchoredAtom2174 chi ∧
      ¬Fin15AnchoredAtom2175 chi ∧
      ¬Fin15AnchoredAtom2197 chi ∧
      ¬Fin15AnchoredAtom2210 chi ∧
      ¬Fin15AnchoredAtom2211 chi ∧
      ¬Fin15AnchoredAtom2233 chi ∧
      ¬Fin15AnchoredAtom2261 chi ∧
      ¬Fin15AnchoredAtom2495 chi ∧
      ¬Fin15AnchoredAtom2496 chi ∧
      ¬Fin15AnchoredAtom2518 chi ∧
      ¬Fin15AnchoredAtom2546 chi ∧
      ¬Fin15AnchoredAtom2630 chi ∧
      ¬Fin15AnchoredAtom2877 chi ∧
      ¬Fin15AnchoredAtom2881 chi ∧
      ¬Fin15AnchoredAtom2882 chi ∧
      ¬Fin15AnchoredAtom2889 chi ∧
      ¬Fin15AnchoredAtom2890 chi ∧
      ¬Fin15AnchoredAtom2912 chi ∧
      ¬Fin15AnchoredAtom2925 chi ∧
      ¬Fin15AnchoredAtom2926 chi ∧
      ¬Fin15AnchoredAtom2948 chi ∧
      ¬Fin15AnchoredAtom2976 chi ∧
      ¬Fin15AnchoredAtom3210 chi ∧
      ¬Fin15AnchoredAtom3211 chi ∧
      ¬Fin15AnchoredAtom3233 chi ∧
      ¬Fin15AnchoredAtom3261 chi ∧
      ¬Fin15AnchoredAtom3345 chi ∧
      ¬Fin15AnchoredAtom3705 chi ∧
      ¬Fin15AnchoredAtom3706 chi ∧
      ¬Fin15AnchoredAtom3728 chi ∧
      ¬Fin15AnchoredAtom3756 chi ∧
      ¬Fin15AnchoredAtom3840 chi ∧
      ¬Fin15AnchoredAtom4380 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 5, 6, 10, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask03191
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1832 Fin15AnchoredAtom1833 Fin15AnchoredAtom1837
    Fin15AnchoredAtom1838 Fin15AnchoredAtom1842 Fin15AnchoredAtom1846 Fin15AnchoredAtom1847
    Fin15AnchoredAtom1854 Fin15AnchoredAtom1855 Fin15AnchoredAtom1877 Fin15AnchoredAtom1942
    Fin15AnchoredAtom1946 Fin15AnchoredAtom1947 Fin15AnchoredAtom1954 Fin15AnchoredAtom1955
    Fin15AnchoredAtom1977 Fin15AnchoredAtom1990 Fin15AnchoredAtom1991 Fin15AnchoredAtom2013
    Fin15AnchoredAtom2041 Fin15AnchoredAtom2162 Fin15AnchoredAtom2166 Fin15AnchoredAtom2167
    Fin15AnchoredAtom2174 Fin15AnchoredAtom2175 Fin15AnchoredAtom2197 Fin15AnchoredAtom2210
    Fin15AnchoredAtom2211 Fin15AnchoredAtom2233 Fin15AnchoredAtom2261 Fin15AnchoredAtom2495
    Fin15AnchoredAtom2496 Fin15AnchoredAtom2518 Fin15AnchoredAtom2546 Fin15AnchoredAtom2630
    Fin15AnchoredAtom2877 Fin15AnchoredAtom2881 Fin15AnchoredAtom2882 Fin15AnchoredAtom2889
    Fin15AnchoredAtom2890 Fin15AnchoredAtom2912 Fin15AnchoredAtom2925 Fin15AnchoredAtom2926
    Fin15AnchoredAtom2948 Fin15AnchoredAtom2976 Fin15AnchoredAtom3210 Fin15AnchoredAtom3211
    Fin15AnchoredAtom3233 Fin15AnchoredAtom3261 Fin15AnchoredAtom3345 Fin15AnchoredAtom3705
    Fin15AnchoredAtom3706 Fin15AnchoredAtom3728 Fin15AnchoredAtom3756 Fin15AnchoredAtom3840
    Fin15AnchoredAtom4380 at hbad
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

theorem fin15Anchored_clause30641 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom1942 chi ∧
      ¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom1978 chi ∧
      ¬Fin15AnchoredAtom1990 chi ∧
      ¬Fin15AnchoredAtom1992 chi ∧
      ¬Fin15AnchoredAtom2014 chi ∧
      ¬Fin15AnchoredAtom2042 chi ∧
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
      ¬Fin15AnchoredAtom2495 chi ∧
      ¬Fin15AnchoredAtom2497 chi ∧
      ¬Fin15AnchoredAtom2519 chi ∧
      ¬Fin15AnchoredAtom2547 chi ∧
      ¬Fin15AnchoredAtom2631 chi ∧
      ¬Fin15AnchoredAtom2877 chi ∧
      ¬Fin15AnchoredAtom2881 chi ∧
      ¬Fin15AnchoredAtom2883 chi ∧
      ¬Fin15AnchoredAtom2889 chi ∧
      ¬Fin15AnchoredAtom2891 chi ∧
      ¬Fin15AnchoredAtom2913 chi ∧
      ¬Fin15AnchoredAtom2925 chi ∧
      ¬Fin15AnchoredAtom2927 chi ∧
      ¬Fin15AnchoredAtom2949 chi ∧
      ¬Fin15AnchoredAtom2977 chi ∧
      ¬Fin15AnchoredAtom3210 chi ∧
      ¬Fin15AnchoredAtom3212 chi ∧
      ¬Fin15AnchoredAtom3234 chi ∧
      ¬Fin15AnchoredAtom3262 chi ∧
      ¬Fin15AnchoredAtom3346 chi ∧
      ¬Fin15AnchoredAtom3705 chi ∧
      ¬Fin15AnchoredAtom3707 chi ∧
      ¬Fin15AnchoredAtom3729 chi ∧
      ¬Fin15AnchoredAtom3757 chi ∧
      ¬Fin15AnchoredAtom3841 chi ∧
      ¬Fin15AnchoredAtom4381 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 5, 6, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05239
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1832 Fin15AnchoredAtom1833 Fin15AnchoredAtom1837
    Fin15AnchoredAtom1839 Fin15AnchoredAtom1842 Fin15AnchoredAtom1846 Fin15AnchoredAtom1848
    Fin15AnchoredAtom1854 Fin15AnchoredAtom1856 Fin15AnchoredAtom1878 Fin15AnchoredAtom1942
    Fin15AnchoredAtom1946 Fin15AnchoredAtom1948 Fin15AnchoredAtom1954 Fin15AnchoredAtom1956
    Fin15AnchoredAtom1978 Fin15AnchoredAtom1990 Fin15AnchoredAtom1992 Fin15AnchoredAtom2014
    Fin15AnchoredAtom2042 Fin15AnchoredAtom2162 Fin15AnchoredAtom2166 Fin15AnchoredAtom2168
    Fin15AnchoredAtom2174 Fin15AnchoredAtom2176 Fin15AnchoredAtom2198 Fin15AnchoredAtom2210
    Fin15AnchoredAtom2212 Fin15AnchoredAtom2234 Fin15AnchoredAtom2262 Fin15AnchoredAtom2495
    Fin15AnchoredAtom2497 Fin15AnchoredAtom2519 Fin15AnchoredAtom2547 Fin15AnchoredAtom2631
    Fin15AnchoredAtom2877 Fin15AnchoredAtom2881 Fin15AnchoredAtom2883 Fin15AnchoredAtom2889
    Fin15AnchoredAtom2891 Fin15AnchoredAtom2913 Fin15AnchoredAtom2925 Fin15AnchoredAtom2927
    Fin15AnchoredAtom2949 Fin15AnchoredAtom2977 Fin15AnchoredAtom3210 Fin15AnchoredAtom3212
    Fin15AnchoredAtom3234 Fin15AnchoredAtom3262 Fin15AnchoredAtom3346 Fin15AnchoredAtom3705
    Fin15AnchoredAtom3707 Fin15AnchoredAtom3729 Fin15AnchoredAtom3757 Fin15AnchoredAtom3841
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

theorem fin15Anchored_clause30642 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom1942 chi ∧
      ¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom1979 chi ∧
      ¬Fin15AnchoredAtom1990 chi ∧
      ¬Fin15AnchoredAtom1993 chi ∧
      ¬Fin15AnchoredAtom2015 chi ∧
      ¬Fin15AnchoredAtom2043 chi ∧
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
      ¬Fin15AnchoredAtom2495 chi ∧
      ¬Fin15AnchoredAtom2498 chi ∧
      ¬Fin15AnchoredAtom2520 chi ∧
      ¬Fin15AnchoredAtom2548 chi ∧
      ¬Fin15AnchoredAtom2632 chi ∧
      ¬Fin15AnchoredAtom2877 chi ∧
      ¬Fin15AnchoredAtom2881 chi ∧
      ¬Fin15AnchoredAtom2884 chi ∧
      ¬Fin15AnchoredAtom2889 chi ∧
      ¬Fin15AnchoredAtom2892 chi ∧
      ¬Fin15AnchoredAtom2914 chi ∧
      ¬Fin15AnchoredAtom2925 chi ∧
      ¬Fin15AnchoredAtom2928 chi ∧
      ¬Fin15AnchoredAtom2950 chi ∧
      ¬Fin15AnchoredAtom2978 chi ∧
      ¬Fin15AnchoredAtom3210 chi ∧
      ¬Fin15AnchoredAtom3213 chi ∧
      ¬Fin15AnchoredAtom3235 chi ∧
      ¬Fin15AnchoredAtom3263 chi ∧
      ¬Fin15AnchoredAtom3347 chi ∧
      ¬Fin15AnchoredAtom3705 chi ∧
      ¬Fin15AnchoredAtom3708 chi ∧
      ¬Fin15AnchoredAtom3730 chi ∧
      ¬Fin15AnchoredAtom3758 chi ∧
      ¬Fin15AnchoredAtom3842 chi ∧
      ¬Fin15AnchoredAtom4382 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 5, 6, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09335
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1832 Fin15AnchoredAtom1833 Fin15AnchoredAtom1837
    Fin15AnchoredAtom1840 Fin15AnchoredAtom1842 Fin15AnchoredAtom1846 Fin15AnchoredAtom1849
    Fin15AnchoredAtom1854 Fin15AnchoredAtom1857 Fin15AnchoredAtom1879 Fin15AnchoredAtom1942
    Fin15AnchoredAtom1946 Fin15AnchoredAtom1949 Fin15AnchoredAtom1954 Fin15AnchoredAtom1957
    Fin15AnchoredAtom1979 Fin15AnchoredAtom1990 Fin15AnchoredAtom1993 Fin15AnchoredAtom2015
    Fin15AnchoredAtom2043 Fin15AnchoredAtom2162 Fin15AnchoredAtom2166 Fin15AnchoredAtom2169
    Fin15AnchoredAtom2174 Fin15AnchoredAtom2177 Fin15AnchoredAtom2199 Fin15AnchoredAtom2210
    Fin15AnchoredAtom2213 Fin15AnchoredAtom2235 Fin15AnchoredAtom2263 Fin15AnchoredAtom2495
    Fin15AnchoredAtom2498 Fin15AnchoredAtom2520 Fin15AnchoredAtom2548 Fin15AnchoredAtom2632
    Fin15AnchoredAtom2877 Fin15AnchoredAtom2881 Fin15AnchoredAtom2884 Fin15AnchoredAtom2889
    Fin15AnchoredAtom2892 Fin15AnchoredAtom2914 Fin15AnchoredAtom2925 Fin15AnchoredAtom2928
    Fin15AnchoredAtom2950 Fin15AnchoredAtom2978 Fin15AnchoredAtom3210 Fin15AnchoredAtom3213
    Fin15AnchoredAtom3235 Fin15AnchoredAtom3263 Fin15AnchoredAtom3347 Fin15AnchoredAtom3705
    Fin15AnchoredAtom3708 Fin15AnchoredAtom3730 Fin15AnchoredAtom3758 Fin15AnchoredAtom3842
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

theorem fin15Anchored_clause30643 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom1942 chi ∧
      ¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom1980 chi ∧
      ¬Fin15AnchoredAtom1990 chi ∧
      ¬Fin15AnchoredAtom1994 chi ∧
      ¬Fin15AnchoredAtom2016 chi ∧
      ¬Fin15AnchoredAtom2044 chi ∧
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
      ¬Fin15AnchoredAtom2495 chi ∧
      ¬Fin15AnchoredAtom2499 chi ∧
      ¬Fin15AnchoredAtom2521 chi ∧
      ¬Fin15AnchoredAtom2549 chi ∧
      ¬Fin15AnchoredAtom2633 chi ∧
      ¬Fin15AnchoredAtom2877 chi ∧
      ¬Fin15AnchoredAtom2881 chi ∧
      ¬Fin15AnchoredAtom2885 chi ∧
      ¬Fin15AnchoredAtom2889 chi ∧
      ¬Fin15AnchoredAtom2893 chi ∧
      ¬Fin15AnchoredAtom2915 chi ∧
      ¬Fin15AnchoredAtom2925 chi ∧
      ¬Fin15AnchoredAtom2929 chi ∧
      ¬Fin15AnchoredAtom2951 chi ∧
      ¬Fin15AnchoredAtom2979 chi ∧
      ¬Fin15AnchoredAtom3210 chi ∧
      ¬Fin15AnchoredAtom3214 chi ∧
      ¬Fin15AnchoredAtom3236 chi ∧
      ¬Fin15AnchoredAtom3264 chi ∧
      ¬Fin15AnchoredAtom3348 chi ∧
      ¬Fin15AnchoredAtom3705 chi ∧
      ¬Fin15AnchoredAtom3709 chi ∧
      ¬Fin15AnchoredAtom3731 chi ∧
      ¬Fin15AnchoredAtom3759 chi ∧
      ¬Fin15AnchoredAtom3843 chi ∧
      ¬Fin15AnchoredAtom4383 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 5, 6, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17527
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1832 Fin15AnchoredAtom1833 Fin15AnchoredAtom1837
    Fin15AnchoredAtom1841 Fin15AnchoredAtom1842 Fin15AnchoredAtom1846 Fin15AnchoredAtom1850
    Fin15AnchoredAtom1854 Fin15AnchoredAtom1858 Fin15AnchoredAtom1880 Fin15AnchoredAtom1942
    Fin15AnchoredAtom1946 Fin15AnchoredAtom1950 Fin15AnchoredAtom1954 Fin15AnchoredAtom1958
    Fin15AnchoredAtom1980 Fin15AnchoredAtom1990 Fin15AnchoredAtom1994 Fin15AnchoredAtom2016
    Fin15AnchoredAtom2044 Fin15AnchoredAtom2162 Fin15AnchoredAtom2166 Fin15AnchoredAtom2170
    Fin15AnchoredAtom2174 Fin15AnchoredAtom2178 Fin15AnchoredAtom2200 Fin15AnchoredAtom2210
    Fin15AnchoredAtom2214 Fin15AnchoredAtom2236 Fin15AnchoredAtom2264 Fin15AnchoredAtom2495
    Fin15AnchoredAtom2499 Fin15AnchoredAtom2521 Fin15AnchoredAtom2549 Fin15AnchoredAtom2633
    Fin15AnchoredAtom2877 Fin15AnchoredAtom2881 Fin15AnchoredAtom2885 Fin15AnchoredAtom2889
    Fin15AnchoredAtom2893 Fin15AnchoredAtom2915 Fin15AnchoredAtom2925 Fin15AnchoredAtom2929
    Fin15AnchoredAtom2951 Fin15AnchoredAtom2979 Fin15AnchoredAtom3210 Fin15AnchoredAtom3214
    Fin15AnchoredAtom3236 Fin15AnchoredAtom3264 Fin15AnchoredAtom3348 Fin15AnchoredAtom3705
    Fin15AnchoredAtom3709 Fin15AnchoredAtom3731 Fin15AnchoredAtom3759 Fin15AnchoredAtom3843
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

theorem fin15Anchored_clause30644 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom1942 chi ∧
      ¬Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom1984 chi ∧
      ¬Fin15AnchoredAtom1992 chi ∧
      ¬Fin15AnchoredAtom1993 chi ∧
      ¬Fin15AnchoredAtom2020 chi ∧
      ¬Fin15AnchoredAtom2048 chi ∧
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
      ¬Fin15AnchoredAtom2497 chi ∧
      ¬Fin15AnchoredAtom2498 chi ∧
      ¬Fin15AnchoredAtom2525 chi ∧
      ¬Fin15AnchoredAtom2553 chi ∧
      ¬Fin15AnchoredAtom2637 chi ∧
      ¬Fin15AnchoredAtom2877 chi ∧
      ¬Fin15AnchoredAtom2883 chi ∧
      ¬Fin15AnchoredAtom2884 chi ∧
      ¬Fin15AnchoredAtom2891 chi ∧
      ¬Fin15AnchoredAtom2892 chi ∧
      ¬Fin15AnchoredAtom2919 chi ∧
      ¬Fin15AnchoredAtom2927 chi ∧
      ¬Fin15AnchoredAtom2928 chi ∧
      ¬Fin15AnchoredAtom2955 chi ∧
      ¬Fin15AnchoredAtom2983 chi ∧
      ¬Fin15AnchoredAtom3212 chi ∧
      ¬Fin15AnchoredAtom3213 chi ∧
      ¬Fin15AnchoredAtom3240 chi ∧
      ¬Fin15AnchoredAtom3268 chi ∧
      ¬Fin15AnchoredAtom3352 chi ∧
      ¬Fin15AnchoredAtom3707 chi ∧
      ¬Fin15AnchoredAtom3708 chi ∧
      ¬Fin15AnchoredAtom3735 chi ∧
      ¬Fin15AnchoredAtom3763 chi ∧
      ¬Fin15AnchoredAtom3847 chi ∧
      ¬Fin15AnchoredAtom4387 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 5, 6, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask12407
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1832 Fin15AnchoredAtom1833 Fin15AnchoredAtom1839
    Fin15AnchoredAtom1840 Fin15AnchoredAtom1842 Fin15AnchoredAtom1848 Fin15AnchoredAtom1849
    Fin15AnchoredAtom1856 Fin15AnchoredAtom1857 Fin15AnchoredAtom1884 Fin15AnchoredAtom1942
    Fin15AnchoredAtom1948 Fin15AnchoredAtom1949 Fin15AnchoredAtom1956 Fin15AnchoredAtom1957
    Fin15AnchoredAtom1984 Fin15AnchoredAtom1992 Fin15AnchoredAtom1993 Fin15AnchoredAtom2020
    Fin15AnchoredAtom2048 Fin15AnchoredAtom2162 Fin15AnchoredAtom2168 Fin15AnchoredAtom2169
    Fin15AnchoredAtom2176 Fin15AnchoredAtom2177 Fin15AnchoredAtom2204 Fin15AnchoredAtom2212
    Fin15AnchoredAtom2213 Fin15AnchoredAtom2240 Fin15AnchoredAtom2268 Fin15AnchoredAtom2497
    Fin15AnchoredAtom2498 Fin15AnchoredAtom2525 Fin15AnchoredAtom2553 Fin15AnchoredAtom2637
    Fin15AnchoredAtom2877 Fin15AnchoredAtom2883 Fin15AnchoredAtom2884 Fin15AnchoredAtom2891
    Fin15AnchoredAtom2892 Fin15AnchoredAtom2919 Fin15AnchoredAtom2927 Fin15AnchoredAtom2928
    Fin15AnchoredAtom2955 Fin15AnchoredAtom2983 Fin15AnchoredAtom3212 Fin15AnchoredAtom3213
    Fin15AnchoredAtom3240 Fin15AnchoredAtom3268 Fin15AnchoredAtom3352 Fin15AnchoredAtom3707
    Fin15AnchoredAtom3708 Fin15AnchoredAtom3735 Fin15AnchoredAtom3763 Fin15AnchoredAtom3847
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

theorem fin15Anchored_clause30645 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom1942 chi ∧
      ¬Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom1985 chi ∧
      ¬Fin15AnchoredAtom1992 chi ∧
      ¬Fin15AnchoredAtom1994 chi ∧
      ¬Fin15AnchoredAtom2021 chi ∧
      ¬Fin15AnchoredAtom2049 chi ∧
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
      ¬Fin15AnchoredAtom2497 chi ∧
      ¬Fin15AnchoredAtom2499 chi ∧
      ¬Fin15AnchoredAtom2526 chi ∧
      ¬Fin15AnchoredAtom2554 chi ∧
      ¬Fin15AnchoredAtom2638 chi ∧
      ¬Fin15AnchoredAtom2877 chi ∧
      ¬Fin15AnchoredAtom2883 chi ∧
      ¬Fin15AnchoredAtom2885 chi ∧
      ¬Fin15AnchoredAtom2891 chi ∧
      ¬Fin15AnchoredAtom2893 chi ∧
      ¬Fin15AnchoredAtom2920 chi ∧
      ¬Fin15AnchoredAtom2927 chi ∧
      ¬Fin15AnchoredAtom2929 chi ∧
      ¬Fin15AnchoredAtom2956 chi ∧
      ¬Fin15AnchoredAtom2984 chi ∧
      ¬Fin15AnchoredAtom3212 chi ∧
      ¬Fin15AnchoredAtom3214 chi ∧
      ¬Fin15AnchoredAtom3241 chi ∧
      ¬Fin15AnchoredAtom3269 chi ∧
      ¬Fin15AnchoredAtom3353 chi ∧
      ¬Fin15AnchoredAtom3707 chi ∧
      ¬Fin15AnchoredAtom3709 chi ∧
      ¬Fin15AnchoredAtom3736 chi ∧
      ¬Fin15AnchoredAtom3764 chi ∧
      ¬Fin15AnchoredAtom3848 chi ∧
      ¬Fin15AnchoredAtom4388 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 5, 6, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask20599
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1832 Fin15AnchoredAtom1833 Fin15AnchoredAtom1839
    Fin15AnchoredAtom1841 Fin15AnchoredAtom1842 Fin15AnchoredAtom1848 Fin15AnchoredAtom1850
    Fin15AnchoredAtom1856 Fin15AnchoredAtom1858 Fin15AnchoredAtom1885 Fin15AnchoredAtom1942
    Fin15AnchoredAtom1948 Fin15AnchoredAtom1950 Fin15AnchoredAtom1956 Fin15AnchoredAtom1958
    Fin15AnchoredAtom1985 Fin15AnchoredAtom1992 Fin15AnchoredAtom1994 Fin15AnchoredAtom2021
    Fin15AnchoredAtom2049 Fin15AnchoredAtom2162 Fin15AnchoredAtom2168 Fin15AnchoredAtom2170
    Fin15AnchoredAtom2176 Fin15AnchoredAtom2178 Fin15AnchoredAtom2205 Fin15AnchoredAtom2212
    Fin15AnchoredAtom2214 Fin15AnchoredAtom2241 Fin15AnchoredAtom2269 Fin15AnchoredAtom2497
    Fin15AnchoredAtom2499 Fin15AnchoredAtom2526 Fin15AnchoredAtom2554 Fin15AnchoredAtom2638
    Fin15AnchoredAtom2877 Fin15AnchoredAtom2883 Fin15AnchoredAtom2885 Fin15AnchoredAtom2891
    Fin15AnchoredAtom2893 Fin15AnchoredAtom2920 Fin15AnchoredAtom2927 Fin15AnchoredAtom2929
    Fin15AnchoredAtom2956 Fin15AnchoredAtom2984 Fin15AnchoredAtom3212 Fin15AnchoredAtom3214
    Fin15AnchoredAtom3241 Fin15AnchoredAtom3269 Fin15AnchoredAtom3353 Fin15AnchoredAtom3707
    Fin15AnchoredAtom3709 Fin15AnchoredAtom3736 Fin15AnchoredAtom3764 Fin15AnchoredAtom3848
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

theorem fin15Anchored_clause30646 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom1886 chi ∧
      ¬Fin15AnchoredAtom1942 chi ∧
      ¬Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom1986 chi ∧
      ¬Fin15AnchoredAtom1993 chi ∧
      ¬Fin15AnchoredAtom1994 chi ∧
      ¬Fin15AnchoredAtom2022 chi ∧
      ¬Fin15AnchoredAtom2050 chi ∧
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
      ¬Fin15AnchoredAtom2498 chi ∧
      ¬Fin15AnchoredAtom2499 chi ∧
      ¬Fin15AnchoredAtom2527 chi ∧
      ¬Fin15AnchoredAtom2555 chi ∧
      ¬Fin15AnchoredAtom2639 chi ∧
      ¬Fin15AnchoredAtom2877 chi ∧
      ¬Fin15AnchoredAtom2884 chi ∧
      ¬Fin15AnchoredAtom2885 chi ∧
      ¬Fin15AnchoredAtom2892 chi ∧
      ¬Fin15AnchoredAtom2893 chi ∧
      ¬Fin15AnchoredAtom2921 chi ∧
      ¬Fin15AnchoredAtom2928 chi ∧
      ¬Fin15AnchoredAtom2929 chi ∧
      ¬Fin15AnchoredAtom2957 chi ∧
      ¬Fin15AnchoredAtom2985 chi ∧
      ¬Fin15AnchoredAtom3213 chi ∧
      ¬Fin15AnchoredAtom3214 chi ∧
      ¬Fin15AnchoredAtom3242 chi ∧
      ¬Fin15AnchoredAtom3270 chi ∧
      ¬Fin15AnchoredAtom3354 chi ∧
      ¬Fin15AnchoredAtom3708 chi ∧
      ¬Fin15AnchoredAtom3709 chi ∧
      ¬Fin15AnchoredAtom3737 chi ∧
      ¬Fin15AnchoredAtom3765 chi ∧
      ¬Fin15AnchoredAtom3849 chi ∧
      ¬Fin15AnchoredAtom4389 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 5, 6, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask24695
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1832 Fin15AnchoredAtom1833 Fin15AnchoredAtom1840
    Fin15AnchoredAtom1841 Fin15AnchoredAtom1842 Fin15AnchoredAtom1849 Fin15AnchoredAtom1850
    Fin15AnchoredAtom1857 Fin15AnchoredAtom1858 Fin15AnchoredAtom1886 Fin15AnchoredAtom1942
    Fin15AnchoredAtom1949 Fin15AnchoredAtom1950 Fin15AnchoredAtom1957 Fin15AnchoredAtom1958
    Fin15AnchoredAtom1986 Fin15AnchoredAtom1993 Fin15AnchoredAtom1994 Fin15AnchoredAtom2022
    Fin15AnchoredAtom2050 Fin15AnchoredAtom2162 Fin15AnchoredAtom2169 Fin15AnchoredAtom2170
    Fin15AnchoredAtom2177 Fin15AnchoredAtom2178 Fin15AnchoredAtom2206 Fin15AnchoredAtom2213
    Fin15AnchoredAtom2214 Fin15AnchoredAtom2242 Fin15AnchoredAtom2270 Fin15AnchoredAtom2498
    Fin15AnchoredAtom2499 Fin15AnchoredAtom2527 Fin15AnchoredAtom2555 Fin15AnchoredAtom2639
    Fin15AnchoredAtom2877 Fin15AnchoredAtom2884 Fin15AnchoredAtom2885 Fin15AnchoredAtom2892
    Fin15AnchoredAtom2893 Fin15AnchoredAtom2921 Fin15AnchoredAtom2928 Fin15AnchoredAtom2929
    Fin15AnchoredAtom2957 Fin15AnchoredAtom2985 Fin15AnchoredAtom3213 Fin15AnchoredAtom3214
    Fin15AnchoredAtom3242 Fin15AnchoredAtom3270 Fin15AnchoredAtom3354 Fin15AnchoredAtom3708
    Fin15AnchoredAtom3709 Fin15AnchoredAtom3737 Fin15AnchoredAtom3765 Fin15AnchoredAtom3849
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

theorem fin15Anchored_clause30647 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom1996 chi ∧
      ¬Fin15AnchoredAtom1997 chi ∧
      ¬Fin15AnchoredAtom2008 chi ∧
      ¬Fin15AnchoredAtom2057 chi ∧
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
      ¬Fin15AnchoredAtom2501 chi ∧
      ¬Fin15AnchoredAtom2502 chi ∧
      ¬Fin15AnchoredAtom2513 chi ∧
      ¬Fin15AnchoredAtom2562 chi ∧
      ¬Fin15AnchoredAtom2646 chi ∧
      ¬Fin15AnchoredAtom2878 chi ∧
      ¬Fin15AnchoredAtom2880 chi ∧
      ¬Fin15AnchoredAtom2881 chi ∧
      ¬Fin15AnchoredAtom2895 chi ∧
      ¬Fin15AnchoredAtom2896 chi ∧
      ¬Fin15AnchoredAtom2907 chi ∧
      ¬Fin15AnchoredAtom2931 chi ∧
      ¬Fin15AnchoredAtom2932 chi ∧
      ¬Fin15AnchoredAtom2943 chi ∧
      ¬Fin15AnchoredAtom2992 chi ∧
      ¬Fin15AnchoredAtom3216 chi ∧
      ¬Fin15AnchoredAtom3217 chi ∧
      ¬Fin15AnchoredAtom3228 chi ∧
      ¬Fin15AnchoredAtom3277 chi ∧
      ¬Fin15AnchoredAtom3361 chi ∧
      ¬Fin15AnchoredAtom3711 chi ∧
      ¬Fin15AnchoredAtom3712 chi ∧
      ¬Fin15AnchoredAtom3723 chi ∧
      ¬Fin15AnchoredAtom3772 chi ∧
      ¬Fin15AnchoredAtom3856 chi ∧
      ¬Fin15AnchoredAtom4396 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 5, 7, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask01719
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1832 Fin15AnchoredAtom1834 Fin15AnchoredAtom1836
    Fin15AnchoredAtom1837 Fin15AnchoredAtom1843 Fin15AnchoredAtom1845 Fin15AnchoredAtom1846
    Fin15AnchoredAtom1860 Fin15AnchoredAtom1861 Fin15AnchoredAtom1872 Fin15AnchoredAtom1943
    Fin15AnchoredAtom1945 Fin15AnchoredAtom1946 Fin15AnchoredAtom1960 Fin15AnchoredAtom1961
    Fin15AnchoredAtom1972 Fin15AnchoredAtom1996 Fin15AnchoredAtom1997 Fin15AnchoredAtom2008
    Fin15AnchoredAtom2057 Fin15AnchoredAtom2163 Fin15AnchoredAtom2165 Fin15AnchoredAtom2166
    Fin15AnchoredAtom2180 Fin15AnchoredAtom2181 Fin15AnchoredAtom2192 Fin15AnchoredAtom2216
    Fin15AnchoredAtom2217 Fin15AnchoredAtom2228 Fin15AnchoredAtom2277 Fin15AnchoredAtom2501
    Fin15AnchoredAtom2502 Fin15AnchoredAtom2513 Fin15AnchoredAtom2562 Fin15AnchoredAtom2646
    Fin15AnchoredAtom2878 Fin15AnchoredAtom2880 Fin15AnchoredAtom2881 Fin15AnchoredAtom2895
    Fin15AnchoredAtom2896 Fin15AnchoredAtom2907 Fin15AnchoredAtom2931 Fin15AnchoredAtom2932
    Fin15AnchoredAtom2943 Fin15AnchoredAtom2992 Fin15AnchoredAtom3216 Fin15AnchoredAtom3217
    Fin15AnchoredAtom3228 Fin15AnchoredAtom3277 Fin15AnchoredAtom3361 Fin15AnchoredAtom3711
    Fin15AnchoredAtom3712 Fin15AnchoredAtom3723 Fin15AnchoredAtom3772 Fin15AnchoredAtom3856
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

theorem fin15Anchored_clause30648 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom1996 chi ∧
      ¬Fin15AnchoredAtom1999 chi ∧
      ¬Fin15AnchoredAtom2010 chi ∧
      ¬Fin15AnchoredAtom2059 chi ∧
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
      ¬Fin15AnchoredAtom2501 chi ∧
      ¬Fin15AnchoredAtom2504 chi ∧
      ¬Fin15AnchoredAtom2515 chi ∧
      ¬Fin15AnchoredAtom2564 chi ∧
      ¬Fin15AnchoredAtom2648 chi ∧
      ¬Fin15AnchoredAtom2878 chi ∧
      ¬Fin15AnchoredAtom2880 chi ∧
      ¬Fin15AnchoredAtom2883 chi ∧
      ¬Fin15AnchoredAtom2895 chi ∧
      ¬Fin15AnchoredAtom2898 chi ∧
      ¬Fin15AnchoredAtom2909 chi ∧
      ¬Fin15AnchoredAtom2931 chi ∧
      ¬Fin15AnchoredAtom2934 chi ∧
      ¬Fin15AnchoredAtom2945 chi ∧
      ¬Fin15AnchoredAtom2994 chi ∧
      ¬Fin15AnchoredAtom3216 chi ∧
      ¬Fin15AnchoredAtom3219 chi ∧
      ¬Fin15AnchoredAtom3230 chi ∧
      ¬Fin15AnchoredAtom3279 chi ∧
      ¬Fin15AnchoredAtom3363 chi ∧
      ¬Fin15AnchoredAtom3711 chi ∧
      ¬Fin15AnchoredAtom3714 chi ∧
      ¬Fin15AnchoredAtom3725 chi ∧
      ¬Fin15AnchoredAtom3774 chi ∧
      ¬Fin15AnchoredAtom3858 chi ∧
      ¬Fin15AnchoredAtom4398 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 5, 7, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask04791
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1832 Fin15AnchoredAtom1834 Fin15AnchoredAtom1836
    Fin15AnchoredAtom1839 Fin15AnchoredAtom1843 Fin15AnchoredAtom1845 Fin15AnchoredAtom1848
    Fin15AnchoredAtom1860 Fin15AnchoredAtom1863 Fin15AnchoredAtom1874 Fin15AnchoredAtom1943
    Fin15AnchoredAtom1945 Fin15AnchoredAtom1948 Fin15AnchoredAtom1960 Fin15AnchoredAtom1963
    Fin15AnchoredAtom1974 Fin15AnchoredAtom1996 Fin15AnchoredAtom1999 Fin15AnchoredAtom2010
    Fin15AnchoredAtom2059 Fin15AnchoredAtom2163 Fin15AnchoredAtom2165 Fin15AnchoredAtom2168
    Fin15AnchoredAtom2180 Fin15AnchoredAtom2183 Fin15AnchoredAtom2194 Fin15AnchoredAtom2216
    Fin15AnchoredAtom2219 Fin15AnchoredAtom2230 Fin15AnchoredAtom2279 Fin15AnchoredAtom2501
    Fin15AnchoredAtom2504 Fin15AnchoredAtom2515 Fin15AnchoredAtom2564 Fin15AnchoredAtom2648
    Fin15AnchoredAtom2878 Fin15AnchoredAtom2880 Fin15AnchoredAtom2883 Fin15AnchoredAtom2895
    Fin15AnchoredAtom2898 Fin15AnchoredAtom2909 Fin15AnchoredAtom2931 Fin15AnchoredAtom2934
    Fin15AnchoredAtom2945 Fin15AnchoredAtom2994 Fin15AnchoredAtom3216 Fin15AnchoredAtom3219
    Fin15AnchoredAtom3230 Fin15AnchoredAtom3279 Fin15AnchoredAtom3363 Fin15AnchoredAtom3711
    Fin15AnchoredAtom3714 Fin15AnchoredAtom3725 Fin15AnchoredAtom3774 Fin15AnchoredAtom3858
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

theorem fin15Anchored_clause30649 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom1996 chi ∧
      ¬Fin15AnchoredAtom2000 chi ∧
      ¬Fin15AnchoredAtom2011 chi ∧
      ¬Fin15AnchoredAtom2060 chi ∧
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
      ¬Fin15AnchoredAtom2501 chi ∧
      ¬Fin15AnchoredAtom2505 chi ∧
      ¬Fin15AnchoredAtom2516 chi ∧
      ¬Fin15AnchoredAtom2565 chi ∧
      ¬Fin15AnchoredAtom2649 chi ∧
      ¬Fin15AnchoredAtom2878 chi ∧
      ¬Fin15AnchoredAtom2880 chi ∧
      ¬Fin15AnchoredAtom2884 chi ∧
      ¬Fin15AnchoredAtom2895 chi ∧
      ¬Fin15AnchoredAtom2899 chi ∧
      ¬Fin15AnchoredAtom2910 chi ∧
      ¬Fin15AnchoredAtom2931 chi ∧
      ¬Fin15AnchoredAtom2935 chi ∧
      ¬Fin15AnchoredAtom2946 chi ∧
      ¬Fin15AnchoredAtom2995 chi ∧
      ¬Fin15AnchoredAtom3216 chi ∧
      ¬Fin15AnchoredAtom3220 chi ∧
      ¬Fin15AnchoredAtom3231 chi ∧
      ¬Fin15AnchoredAtom3280 chi ∧
      ¬Fin15AnchoredAtom3364 chi ∧
      ¬Fin15AnchoredAtom3711 chi ∧
      ¬Fin15AnchoredAtom3715 chi ∧
      ¬Fin15AnchoredAtom3726 chi ∧
      ¬Fin15AnchoredAtom3775 chi ∧
      ¬Fin15AnchoredAtom3859 chi ∧
      ¬Fin15AnchoredAtom4399 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 5, 7, 9, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask08887
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1832 Fin15AnchoredAtom1834 Fin15AnchoredAtom1836
    Fin15AnchoredAtom1840 Fin15AnchoredAtom1843 Fin15AnchoredAtom1845 Fin15AnchoredAtom1849
    Fin15AnchoredAtom1860 Fin15AnchoredAtom1864 Fin15AnchoredAtom1875 Fin15AnchoredAtom1943
    Fin15AnchoredAtom1945 Fin15AnchoredAtom1949 Fin15AnchoredAtom1960 Fin15AnchoredAtom1964
    Fin15AnchoredAtom1975 Fin15AnchoredAtom1996 Fin15AnchoredAtom2000 Fin15AnchoredAtom2011
    Fin15AnchoredAtom2060 Fin15AnchoredAtom2163 Fin15AnchoredAtom2165 Fin15AnchoredAtom2169
    Fin15AnchoredAtom2180 Fin15AnchoredAtom2184 Fin15AnchoredAtom2195 Fin15AnchoredAtom2216
    Fin15AnchoredAtom2220 Fin15AnchoredAtom2231 Fin15AnchoredAtom2280 Fin15AnchoredAtom2501
    Fin15AnchoredAtom2505 Fin15AnchoredAtom2516 Fin15AnchoredAtom2565 Fin15AnchoredAtom2649
    Fin15AnchoredAtom2878 Fin15AnchoredAtom2880 Fin15AnchoredAtom2884 Fin15AnchoredAtom2895
    Fin15AnchoredAtom2899 Fin15AnchoredAtom2910 Fin15AnchoredAtom2931 Fin15AnchoredAtom2935
    Fin15AnchoredAtom2946 Fin15AnchoredAtom2995 Fin15AnchoredAtom3216 Fin15AnchoredAtom3220
    Fin15AnchoredAtom3231 Fin15AnchoredAtom3280 Fin15AnchoredAtom3364 Fin15AnchoredAtom3711
    Fin15AnchoredAtom3715 Fin15AnchoredAtom3726 Fin15AnchoredAtom3775 Fin15AnchoredAtom3859
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

theorem fin15Anchored_clause30650 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom1976 chi ∧
      ¬Fin15AnchoredAtom1996 chi ∧
      ¬Fin15AnchoredAtom2001 chi ∧
      ¬Fin15AnchoredAtom2012 chi ∧
      ¬Fin15AnchoredAtom2061 chi ∧
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
      ¬Fin15AnchoredAtom2501 chi ∧
      ¬Fin15AnchoredAtom2506 chi ∧
      ¬Fin15AnchoredAtom2517 chi ∧
      ¬Fin15AnchoredAtom2566 chi ∧
      ¬Fin15AnchoredAtom2650 chi ∧
      ¬Fin15AnchoredAtom2878 chi ∧
      ¬Fin15AnchoredAtom2880 chi ∧
      ¬Fin15AnchoredAtom2885 chi ∧
      ¬Fin15AnchoredAtom2895 chi ∧
      ¬Fin15AnchoredAtom2900 chi ∧
      ¬Fin15AnchoredAtom2911 chi ∧
      ¬Fin15AnchoredAtom2931 chi ∧
      ¬Fin15AnchoredAtom2936 chi ∧
      ¬Fin15AnchoredAtom2947 chi ∧
      ¬Fin15AnchoredAtom2996 chi ∧
      ¬Fin15AnchoredAtom3216 chi ∧
      ¬Fin15AnchoredAtom3221 chi ∧
      ¬Fin15AnchoredAtom3232 chi ∧
      ¬Fin15AnchoredAtom3281 chi ∧
      ¬Fin15AnchoredAtom3365 chi ∧
      ¬Fin15AnchoredAtom3711 chi ∧
      ¬Fin15AnchoredAtom3716 chi ∧
      ¬Fin15AnchoredAtom3727 chi ∧
      ¬Fin15AnchoredAtom3776 chi ∧
      ¬Fin15AnchoredAtom3860 chi ∧
      ¬Fin15AnchoredAtom4400 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 5, 7, 9, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17079
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1832 Fin15AnchoredAtom1834 Fin15AnchoredAtom1836
    Fin15AnchoredAtom1841 Fin15AnchoredAtom1843 Fin15AnchoredAtom1845 Fin15AnchoredAtom1850
    Fin15AnchoredAtom1860 Fin15AnchoredAtom1865 Fin15AnchoredAtom1876 Fin15AnchoredAtom1943
    Fin15AnchoredAtom1945 Fin15AnchoredAtom1950 Fin15AnchoredAtom1960 Fin15AnchoredAtom1965
    Fin15AnchoredAtom1976 Fin15AnchoredAtom1996 Fin15AnchoredAtom2001 Fin15AnchoredAtom2012
    Fin15AnchoredAtom2061 Fin15AnchoredAtom2163 Fin15AnchoredAtom2165 Fin15AnchoredAtom2170
    Fin15AnchoredAtom2180 Fin15AnchoredAtom2185 Fin15AnchoredAtom2196 Fin15AnchoredAtom2216
    Fin15AnchoredAtom2221 Fin15AnchoredAtom2232 Fin15AnchoredAtom2281 Fin15AnchoredAtom2501
    Fin15AnchoredAtom2506 Fin15AnchoredAtom2517 Fin15AnchoredAtom2566 Fin15AnchoredAtom2650
    Fin15AnchoredAtom2878 Fin15AnchoredAtom2880 Fin15AnchoredAtom2885 Fin15AnchoredAtom2895
    Fin15AnchoredAtom2900 Fin15AnchoredAtom2911 Fin15AnchoredAtom2931 Fin15AnchoredAtom2936
    Fin15AnchoredAtom2947 Fin15AnchoredAtom2996 Fin15AnchoredAtom3216 Fin15AnchoredAtom3221
    Fin15AnchoredAtom3232 Fin15AnchoredAtom3281 Fin15AnchoredAtom3365 Fin15AnchoredAtom3711
    Fin15AnchoredAtom3716 Fin15AnchoredAtom3727 Fin15AnchoredAtom3776 Fin15AnchoredAtom3860
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

theorem fin15Anchored_clause30651 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1838 chi ∧
      ¬Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom1847 chi ∧
      ¬Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom1862 chi ∧
      ¬Fin15AnchoredAtom1877 chi ∧
      ¬Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1947 chi ∧
      ¬Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom1962 chi ∧
      ¬Fin15AnchoredAtom1977 chi ∧
      ¬Fin15AnchoredAtom1997 chi ∧
      ¬Fin15AnchoredAtom1998 chi ∧
      ¬Fin15AnchoredAtom2013 chi ∧
      ¬Fin15AnchoredAtom2062 chi ∧
      ¬Fin15AnchoredAtom2163 chi ∧
      ¬Fin15AnchoredAtom2166 chi ∧
      ¬Fin15AnchoredAtom2167 chi ∧
      ¬Fin15AnchoredAtom2181 chi ∧
      ¬Fin15AnchoredAtom2182 chi ∧
      ¬Fin15AnchoredAtom2197 chi ∧
      ¬Fin15AnchoredAtom2217 chi ∧
      ¬Fin15AnchoredAtom2218 chi ∧
      ¬Fin15AnchoredAtom2233 chi ∧
      ¬Fin15AnchoredAtom2282 chi ∧
      ¬Fin15AnchoredAtom2502 chi ∧
      ¬Fin15AnchoredAtom2503 chi ∧
      ¬Fin15AnchoredAtom2518 chi ∧
      ¬Fin15AnchoredAtom2567 chi ∧
      ¬Fin15AnchoredAtom2651 chi ∧
      ¬Fin15AnchoredAtom2878 chi ∧
      ¬Fin15AnchoredAtom2881 chi ∧
      ¬Fin15AnchoredAtom2882 chi ∧
      ¬Fin15AnchoredAtom2896 chi ∧
      ¬Fin15AnchoredAtom2897 chi ∧
      ¬Fin15AnchoredAtom2912 chi ∧
      ¬Fin15AnchoredAtom2932 chi ∧
      ¬Fin15AnchoredAtom2933 chi ∧
      ¬Fin15AnchoredAtom2948 chi ∧
      ¬Fin15AnchoredAtom2997 chi ∧
      ¬Fin15AnchoredAtom3217 chi ∧
      ¬Fin15AnchoredAtom3218 chi ∧
      ¬Fin15AnchoredAtom3233 chi ∧
      ¬Fin15AnchoredAtom3282 chi ∧
      ¬Fin15AnchoredAtom3366 chi ∧
      ¬Fin15AnchoredAtom3712 chi ∧
      ¬Fin15AnchoredAtom3713 chi ∧
      ¬Fin15AnchoredAtom3728 chi ∧
      ¬Fin15AnchoredAtom3777 chi ∧
      ¬Fin15AnchoredAtom3861 chi ∧
      ¬Fin15AnchoredAtom4401 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 5, 7, 10, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask03255
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1832 Fin15AnchoredAtom1834 Fin15AnchoredAtom1837
    Fin15AnchoredAtom1838 Fin15AnchoredAtom1843 Fin15AnchoredAtom1846 Fin15AnchoredAtom1847
    Fin15AnchoredAtom1861 Fin15AnchoredAtom1862 Fin15AnchoredAtom1877 Fin15AnchoredAtom1943
    Fin15AnchoredAtom1946 Fin15AnchoredAtom1947 Fin15AnchoredAtom1961 Fin15AnchoredAtom1962
    Fin15AnchoredAtom1977 Fin15AnchoredAtom1997 Fin15AnchoredAtom1998 Fin15AnchoredAtom2013
    Fin15AnchoredAtom2062 Fin15AnchoredAtom2163 Fin15AnchoredAtom2166 Fin15AnchoredAtom2167
    Fin15AnchoredAtom2181 Fin15AnchoredAtom2182 Fin15AnchoredAtom2197 Fin15AnchoredAtom2217
    Fin15AnchoredAtom2218 Fin15AnchoredAtom2233 Fin15AnchoredAtom2282 Fin15AnchoredAtom2502
    Fin15AnchoredAtom2503 Fin15AnchoredAtom2518 Fin15AnchoredAtom2567 Fin15AnchoredAtom2651
    Fin15AnchoredAtom2878 Fin15AnchoredAtom2881 Fin15AnchoredAtom2882 Fin15AnchoredAtom2896
    Fin15AnchoredAtom2897 Fin15AnchoredAtom2912 Fin15AnchoredAtom2932 Fin15AnchoredAtom2933
    Fin15AnchoredAtom2948 Fin15AnchoredAtom2997 Fin15AnchoredAtom3217 Fin15AnchoredAtom3218
    Fin15AnchoredAtom3233 Fin15AnchoredAtom3282 Fin15AnchoredAtom3366 Fin15AnchoredAtom3712
    Fin15AnchoredAtom3713 Fin15AnchoredAtom3728 Fin15AnchoredAtom3777 Fin15AnchoredAtom3861
    Fin15AnchoredAtom4401 at hbad
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

theorem fin15Anchored_clause30652 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom1978 chi ∧
      ¬Fin15AnchoredAtom1997 chi ∧
      ¬Fin15AnchoredAtom1999 chi ∧
      ¬Fin15AnchoredAtom2014 chi ∧
      ¬Fin15AnchoredAtom2063 chi ∧
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
      ¬Fin15AnchoredAtom2502 chi ∧
      ¬Fin15AnchoredAtom2504 chi ∧
      ¬Fin15AnchoredAtom2519 chi ∧
      ¬Fin15AnchoredAtom2568 chi ∧
      ¬Fin15AnchoredAtom2652 chi ∧
      ¬Fin15AnchoredAtom2878 chi ∧
      ¬Fin15AnchoredAtom2881 chi ∧
      ¬Fin15AnchoredAtom2883 chi ∧
      ¬Fin15AnchoredAtom2896 chi ∧
      ¬Fin15AnchoredAtom2898 chi ∧
      ¬Fin15AnchoredAtom2913 chi ∧
      ¬Fin15AnchoredAtom2932 chi ∧
      ¬Fin15AnchoredAtom2934 chi ∧
      ¬Fin15AnchoredAtom2949 chi ∧
      ¬Fin15AnchoredAtom2998 chi ∧
      ¬Fin15AnchoredAtom3217 chi ∧
      ¬Fin15AnchoredAtom3219 chi ∧
      ¬Fin15AnchoredAtom3234 chi ∧
      ¬Fin15AnchoredAtom3283 chi ∧
      ¬Fin15AnchoredAtom3367 chi ∧
      ¬Fin15AnchoredAtom3712 chi ∧
      ¬Fin15AnchoredAtom3714 chi ∧
      ¬Fin15AnchoredAtom3729 chi ∧
      ¬Fin15AnchoredAtom3778 chi ∧
      ¬Fin15AnchoredAtom3862 chi ∧
      ¬Fin15AnchoredAtom4402 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 5, 7, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05303
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1832 Fin15AnchoredAtom1834 Fin15AnchoredAtom1837
    Fin15AnchoredAtom1839 Fin15AnchoredAtom1843 Fin15AnchoredAtom1846 Fin15AnchoredAtom1848
    Fin15AnchoredAtom1861 Fin15AnchoredAtom1863 Fin15AnchoredAtom1878 Fin15AnchoredAtom1943
    Fin15AnchoredAtom1946 Fin15AnchoredAtom1948 Fin15AnchoredAtom1961 Fin15AnchoredAtom1963
    Fin15AnchoredAtom1978 Fin15AnchoredAtom1997 Fin15AnchoredAtom1999 Fin15AnchoredAtom2014
    Fin15AnchoredAtom2063 Fin15AnchoredAtom2163 Fin15AnchoredAtom2166 Fin15AnchoredAtom2168
    Fin15AnchoredAtom2181 Fin15AnchoredAtom2183 Fin15AnchoredAtom2198 Fin15AnchoredAtom2217
    Fin15AnchoredAtom2219 Fin15AnchoredAtom2234 Fin15AnchoredAtom2283 Fin15AnchoredAtom2502
    Fin15AnchoredAtom2504 Fin15AnchoredAtom2519 Fin15AnchoredAtom2568 Fin15AnchoredAtom2652
    Fin15AnchoredAtom2878 Fin15AnchoredAtom2881 Fin15AnchoredAtom2883 Fin15AnchoredAtom2896
    Fin15AnchoredAtom2898 Fin15AnchoredAtom2913 Fin15AnchoredAtom2932 Fin15AnchoredAtom2934
    Fin15AnchoredAtom2949 Fin15AnchoredAtom2998 Fin15AnchoredAtom3217 Fin15AnchoredAtom3219
    Fin15AnchoredAtom3234 Fin15AnchoredAtom3283 Fin15AnchoredAtom3367 Fin15AnchoredAtom3712
    Fin15AnchoredAtom3714 Fin15AnchoredAtom3729 Fin15AnchoredAtom3778 Fin15AnchoredAtom3862
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

theorem fin15Anchored_clause30653 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom1979 chi ∧
      ¬Fin15AnchoredAtom1997 chi ∧
      ¬Fin15AnchoredAtom2000 chi ∧
      ¬Fin15AnchoredAtom2015 chi ∧
      ¬Fin15AnchoredAtom2064 chi ∧
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
      ¬Fin15AnchoredAtom2502 chi ∧
      ¬Fin15AnchoredAtom2505 chi ∧
      ¬Fin15AnchoredAtom2520 chi ∧
      ¬Fin15AnchoredAtom2569 chi ∧
      ¬Fin15AnchoredAtom2653 chi ∧
      ¬Fin15AnchoredAtom2878 chi ∧
      ¬Fin15AnchoredAtom2881 chi ∧
      ¬Fin15AnchoredAtom2884 chi ∧
      ¬Fin15AnchoredAtom2896 chi ∧
      ¬Fin15AnchoredAtom2899 chi ∧
      ¬Fin15AnchoredAtom2914 chi ∧
      ¬Fin15AnchoredAtom2932 chi ∧
      ¬Fin15AnchoredAtom2935 chi ∧
      ¬Fin15AnchoredAtom2950 chi ∧
      ¬Fin15AnchoredAtom2999 chi ∧
      ¬Fin15AnchoredAtom3217 chi ∧
      ¬Fin15AnchoredAtom3220 chi ∧
      ¬Fin15AnchoredAtom3235 chi ∧
      ¬Fin15AnchoredAtom3284 chi ∧
      ¬Fin15AnchoredAtom3368 chi ∧
      ¬Fin15AnchoredAtom3712 chi ∧
      ¬Fin15AnchoredAtom3715 chi ∧
      ¬Fin15AnchoredAtom3730 chi ∧
      ¬Fin15AnchoredAtom3779 chi ∧
      ¬Fin15AnchoredAtom3863 chi ∧
      ¬Fin15AnchoredAtom4403 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 5, 7, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09399
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1832 Fin15AnchoredAtom1834 Fin15AnchoredAtom1837
    Fin15AnchoredAtom1840 Fin15AnchoredAtom1843 Fin15AnchoredAtom1846 Fin15AnchoredAtom1849
    Fin15AnchoredAtom1861 Fin15AnchoredAtom1864 Fin15AnchoredAtom1879 Fin15AnchoredAtom1943
    Fin15AnchoredAtom1946 Fin15AnchoredAtom1949 Fin15AnchoredAtom1961 Fin15AnchoredAtom1964
    Fin15AnchoredAtom1979 Fin15AnchoredAtom1997 Fin15AnchoredAtom2000 Fin15AnchoredAtom2015
    Fin15AnchoredAtom2064 Fin15AnchoredAtom2163 Fin15AnchoredAtom2166 Fin15AnchoredAtom2169
    Fin15AnchoredAtom2181 Fin15AnchoredAtom2184 Fin15AnchoredAtom2199 Fin15AnchoredAtom2217
    Fin15AnchoredAtom2220 Fin15AnchoredAtom2235 Fin15AnchoredAtom2284 Fin15AnchoredAtom2502
    Fin15AnchoredAtom2505 Fin15AnchoredAtom2520 Fin15AnchoredAtom2569 Fin15AnchoredAtom2653
    Fin15AnchoredAtom2878 Fin15AnchoredAtom2881 Fin15AnchoredAtom2884 Fin15AnchoredAtom2896
    Fin15AnchoredAtom2899 Fin15AnchoredAtom2914 Fin15AnchoredAtom2932 Fin15AnchoredAtom2935
    Fin15AnchoredAtom2950 Fin15AnchoredAtom2999 Fin15AnchoredAtom3217 Fin15AnchoredAtom3220
    Fin15AnchoredAtom3235 Fin15AnchoredAtom3284 Fin15AnchoredAtom3368 Fin15AnchoredAtom3712
    Fin15AnchoredAtom3715 Fin15AnchoredAtom3730 Fin15AnchoredAtom3779 Fin15AnchoredAtom3863
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

theorem fin15Anchored_clause30654 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom1980 chi ∧
      ¬Fin15AnchoredAtom1997 chi ∧
      ¬Fin15AnchoredAtom2001 chi ∧
      ¬Fin15AnchoredAtom2016 chi ∧
      ¬Fin15AnchoredAtom2065 chi ∧
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
      ¬Fin15AnchoredAtom2502 chi ∧
      ¬Fin15AnchoredAtom2506 chi ∧
      ¬Fin15AnchoredAtom2521 chi ∧
      ¬Fin15AnchoredAtom2570 chi ∧
      ¬Fin15AnchoredAtom2654 chi ∧
      ¬Fin15AnchoredAtom2878 chi ∧
      ¬Fin15AnchoredAtom2881 chi ∧
      ¬Fin15AnchoredAtom2885 chi ∧
      ¬Fin15AnchoredAtom2896 chi ∧
      ¬Fin15AnchoredAtom2900 chi ∧
      ¬Fin15AnchoredAtom2915 chi ∧
      ¬Fin15AnchoredAtom2932 chi ∧
      ¬Fin15AnchoredAtom2936 chi ∧
      ¬Fin15AnchoredAtom2951 chi ∧
      ¬Fin15AnchoredAtom3000 chi ∧
      ¬Fin15AnchoredAtom3217 chi ∧
      ¬Fin15AnchoredAtom3221 chi ∧
      ¬Fin15AnchoredAtom3236 chi ∧
      ¬Fin15AnchoredAtom3285 chi ∧
      ¬Fin15AnchoredAtom3369 chi ∧
      ¬Fin15AnchoredAtom3712 chi ∧
      ¬Fin15AnchoredAtom3716 chi ∧
      ¬Fin15AnchoredAtom3731 chi ∧
      ¬Fin15AnchoredAtom3780 chi ∧
      ¬Fin15AnchoredAtom3864 chi ∧
      ¬Fin15AnchoredAtom4404 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 5, 7, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17591
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1832 Fin15AnchoredAtom1834 Fin15AnchoredAtom1837
    Fin15AnchoredAtom1841 Fin15AnchoredAtom1843 Fin15AnchoredAtom1846 Fin15AnchoredAtom1850
    Fin15AnchoredAtom1861 Fin15AnchoredAtom1865 Fin15AnchoredAtom1880 Fin15AnchoredAtom1943
    Fin15AnchoredAtom1946 Fin15AnchoredAtom1950 Fin15AnchoredAtom1961 Fin15AnchoredAtom1965
    Fin15AnchoredAtom1980 Fin15AnchoredAtom1997 Fin15AnchoredAtom2001 Fin15AnchoredAtom2016
    Fin15AnchoredAtom2065 Fin15AnchoredAtom2163 Fin15AnchoredAtom2166 Fin15AnchoredAtom2170
    Fin15AnchoredAtom2181 Fin15AnchoredAtom2185 Fin15AnchoredAtom2200 Fin15AnchoredAtom2217
    Fin15AnchoredAtom2221 Fin15AnchoredAtom2236 Fin15AnchoredAtom2285 Fin15AnchoredAtom2502
    Fin15AnchoredAtom2506 Fin15AnchoredAtom2521 Fin15AnchoredAtom2570 Fin15AnchoredAtom2654
    Fin15AnchoredAtom2878 Fin15AnchoredAtom2881 Fin15AnchoredAtom2885 Fin15AnchoredAtom2896
    Fin15AnchoredAtom2900 Fin15AnchoredAtom2915 Fin15AnchoredAtom2932 Fin15AnchoredAtom2936
    Fin15AnchoredAtom2951 Fin15AnchoredAtom3000 Fin15AnchoredAtom3217 Fin15AnchoredAtom3221
    Fin15AnchoredAtom3236 Fin15AnchoredAtom3285 Fin15AnchoredAtom3369 Fin15AnchoredAtom3712
    Fin15AnchoredAtom3716 Fin15AnchoredAtom3731 Fin15AnchoredAtom3780 Fin15AnchoredAtom3864
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

theorem fin15Anchored_clause30655 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom1984 chi ∧
      ¬Fin15AnchoredAtom1999 chi ∧
      ¬Fin15AnchoredAtom2000 chi ∧
      ¬Fin15AnchoredAtom2020 chi ∧
      ¬Fin15AnchoredAtom2069 chi ∧
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
      ¬Fin15AnchoredAtom2504 chi ∧
      ¬Fin15AnchoredAtom2505 chi ∧
      ¬Fin15AnchoredAtom2525 chi ∧
      ¬Fin15AnchoredAtom2574 chi ∧
      ¬Fin15AnchoredAtom2658 chi ∧
      ¬Fin15AnchoredAtom2878 chi ∧
      ¬Fin15AnchoredAtom2883 chi ∧
      ¬Fin15AnchoredAtom2884 chi ∧
      ¬Fin15AnchoredAtom2898 chi ∧
      ¬Fin15AnchoredAtom2899 chi ∧
      ¬Fin15AnchoredAtom2919 chi ∧
      ¬Fin15AnchoredAtom2934 chi ∧
      ¬Fin15AnchoredAtom2935 chi ∧
      ¬Fin15AnchoredAtom2955 chi ∧
      ¬Fin15AnchoredAtom3004 chi ∧
      ¬Fin15AnchoredAtom3219 chi ∧
      ¬Fin15AnchoredAtom3220 chi ∧
      ¬Fin15AnchoredAtom3240 chi ∧
      ¬Fin15AnchoredAtom3289 chi ∧
      ¬Fin15AnchoredAtom3373 chi ∧
      ¬Fin15AnchoredAtom3714 chi ∧
      ¬Fin15AnchoredAtom3715 chi ∧
      ¬Fin15AnchoredAtom3735 chi ∧
      ¬Fin15AnchoredAtom3784 chi ∧
      ¬Fin15AnchoredAtom3868 chi ∧
      ¬Fin15AnchoredAtom4408 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 5, 7, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask12471
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1832 Fin15AnchoredAtom1834 Fin15AnchoredAtom1839
    Fin15AnchoredAtom1840 Fin15AnchoredAtom1843 Fin15AnchoredAtom1848 Fin15AnchoredAtom1849
    Fin15AnchoredAtom1863 Fin15AnchoredAtom1864 Fin15AnchoredAtom1884 Fin15AnchoredAtom1943
    Fin15AnchoredAtom1948 Fin15AnchoredAtom1949 Fin15AnchoredAtom1963 Fin15AnchoredAtom1964
    Fin15AnchoredAtom1984 Fin15AnchoredAtom1999 Fin15AnchoredAtom2000 Fin15AnchoredAtom2020
    Fin15AnchoredAtom2069 Fin15AnchoredAtom2163 Fin15AnchoredAtom2168 Fin15AnchoredAtom2169
    Fin15AnchoredAtom2183 Fin15AnchoredAtom2184 Fin15AnchoredAtom2204 Fin15AnchoredAtom2219
    Fin15AnchoredAtom2220 Fin15AnchoredAtom2240 Fin15AnchoredAtom2289 Fin15AnchoredAtom2504
    Fin15AnchoredAtom2505 Fin15AnchoredAtom2525 Fin15AnchoredAtom2574 Fin15AnchoredAtom2658
    Fin15AnchoredAtom2878 Fin15AnchoredAtom2883 Fin15AnchoredAtom2884 Fin15AnchoredAtom2898
    Fin15AnchoredAtom2899 Fin15AnchoredAtom2919 Fin15AnchoredAtom2934 Fin15AnchoredAtom2935
    Fin15AnchoredAtom2955 Fin15AnchoredAtom3004 Fin15AnchoredAtom3219 Fin15AnchoredAtom3220
    Fin15AnchoredAtom3240 Fin15AnchoredAtom3289 Fin15AnchoredAtom3373 Fin15AnchoredAtom3714
    Fin15AnchoredAtom3715 Fin15AnchoredAtom3735 Fin15AnchoredAtom3784 Fin15AnchoredAtom3868
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

theorem fin15Anchored_clause30656 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom1985 chi ∧
      ¬Fin15AnchoredAtom1999 chi ∧
      ¬Fin15AnchoredAtom2001 chi ∧
      ¬Fin15AnchoredAtom2021 chi ∧
      ¬Fin15AnchoredAtom2070 chi ∧
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
      ¬Fin15AnchoredAtom2504 chi ∧
      ¬Fin15AnchoredAtom2506 chi ∧
      ¬Fin15AnchoredAtom2526 chi ∧
      ¬Fin15AnchoredAtom2575 chi ∧
      ¬Fin15AnchoredAtom2659 chi ∧
      ¬Fin15AnchoredAtom2878 chi ∧
      ¬Fin15AnchoredAtom2883 chi ∧
      ¬Fin15AnchoredAtom2885 chi ∧
      ¬Fin15AnchoredAtom2898 chi ∧
      ¬Fin15AnchoredAtom2900 chi ∧
      ¬Fin15AnchoredAtom2920 chi ∧
      ¬Fin15AnchoredAtom2934 chi ∧
      ¬Fin15AnchoredAtom2936 chi ∧
      ¬Fin15AnchoredAtom2956 chi ∧
      ¬Fin15AnchoredAtom3005 chi ∧
      ¬Fin15AnchoredAtom3219 chi ∧
      ¬Fin15AnchoredAtom3221 chi ∧
      ¬Fin15AnchoredAtom3241 chi ∧
      ¬Fin15AnchoredAtom3290 chi ∧
      ¬Fin15AnchoredAtom3374 chi ∧
      ¬Fin15AnchoredAtom3714 chi ∧
      ¬Fin15AnchoredAtom3716 chi ∧
      ¬Fin15AnchoredAtom3736 chi ∧
      ¬Fin15AnchoredAtom3785 chi ∧
      ¬Fin15AnchoredAtom3869 chi ∧
      ¬Fin15AnchoredAtom4409 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 5, 7, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask20663
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1832 Fin15AnchoredAtom1834 Fin15AnchoredAtom1839
    Fin15AnchoredAtom1841 Fin15AnchoredAtom1843 Fin15AnchoredAtom1848 Fin15AnchoredAtom1850
    Fin15AnchoredAtom1863 Fin15AnchoredAtom1865 Fin15AnchoredAtom1885 Fin15AnchoredAtom1943
    Fin15AnchoredAtom1948 Fin15AnchoredAtom1950 Fin15AnchoredAtom1963 Fin15AnchoredAtom1965
    Fin15AnchoredAtom1985 Fin15AnchoredAtom1999 Fin15AnchoredAtom2001 Fin15AnchoredAtom2021
    Fin15AnchoredAtom2070 Fin15AnchoredAtom2163 Fin15AnchoredAtom2168 Fin15AnchoredAtom2170
    Fin15AnchoredAtom2183 Fin15AnchoredAtom2185 Fin15AnchoredAtom2205 Fin15AnchoredAtom2219
    Fin15AnchoredAtom2221 Fin15AnchoredAtom2241 Fin15AnchoredAtom2290 Fin15AnchoredAtom2504
    Fin15AnchoredAtom2506 Fin15AnchoredAtom2526 Fin15AnchoredAtom2575 Fin15AnchoredAtom2659
    Fin15AnchoredAtom2878 Fin15AnchoredAtom2883 Fin15AnchoredAtom2885 Fin15AnchoredAtom2898
    Fin15AnchoredAtom2900 Fin15AnchoredAtom2920 Fin15AnchoredAtom2934 Fin15AnchoredAtom2936
    Fin15AnchoredAtom2956 Fin15AnchoredAtom3005 Fin15AnchoredAtom3219 Fin15AnchoredAtom3221
    Fin15AnchoredAtom3241 Fin15AnchoredAtom3290 Fin15AnchoredAtom3374 Fin15AnchoredAtom3714
    Fin15AnchoredAtom3716 Fin15AnchoredAtom3736 Fin15AnchoredAtom3785 Fin15AnchoredAtom3869
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

theorem fin15Anchored_clause30657 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom1886 chi ∧
      ¬Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom1986 chi ∧
      ¬Fin15AnchoredAtom2000 chi ∧
      ¬Fin15AnchoredAtom2001 chi ∧
      ¬Fin15AnchoredAtom2022 chi ∧
      ¬Fin15AnchoredAtom2071 chi ∧
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
      ¬Fin15AnchoredAtom2505 chi ∧
      ¬Fin15AnchoredAtom2506 chi ∧
      ¬Fin15AnchoredAtom2527 chi ∧
      ¬Fin15AnchoredAtom2576 chi ∧
      ¬Fin15AnchoredAtom2660 chi ∧
      ¬Fin15AnchoredAtom2878 chi ∧
      ¬Fin15AnchoredAtom2884 chi ∧
      ¬Fin15AnchoredAtom2885 chi ∧
      ¬Fin15AnchoredAtom2899 chi ∧
      ¬Fin15AnchoredAtom2900 chi ∧
      ¬Fin15AnchoredAtom2921 chi ∧
      ¬Fin15AnchoredAtom2935 chi ∧
      ¬Fin15AnchoredAtom2936 chi ∧
      ¬Fin15AnchoredAtom2957 chi ∧
      ¬Fin15AnchoredAtom3006 chi ∧
      ¬Fin15AnchoredAtom3220 chi ∧
      ¬Fin15AnchoredAtom3221 chi ∧
      ¬Fin15AnchoredAtom3242 chi ∧
      ¬Fin15AnchoredAtom3291 chi ∧
      ¬Fin15AnchoredAtom3375 chi ∧
      ¬Fin15AnchoredAtom3715 chi ∧
      ¬Fin15AnchoredAtom3716 chi ∧
      ¬Fin15AnchoredAtom3737 chi ∧
      ¬Fin15AnchoredAtom3786 chi ∧
      ¬Fin15AnchoredAtom3870 chi ∧
      ¬Fin15AnchoredAtom4410 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 5, 7, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask24759
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1832 Fin15AnchoredAtom1834 Fin15AnchoredAtom1840
    Fin15AnchoredAtom1841 Fin15AnchoredAtom1843 Fin15AnchoredAtom1849 Fin15AnchoredAtom1850
    Fin15AnchoredAtom1864 Fin15AnchoredAtom1865 Fin15AnchoredAtom1886 Fin15AnchoredAtom1943
    Fin15AnchoredAtom1949 Fin15AnchoredAtom1950 Fin15AnchoredAtom1964 Fin15AnchoredAtom1965
    Fin15AnchoredAtom1986 Fin15AnchoredAtom2000 Fin15AnchoredAtom2001 Fin15AnchoredAtom2022
    Fin15AnchoredAtom2071 Fin15AnchoredAtom2163 Fin15AnchoredAtom2169 Fin15AnchoredAtom2170
    Fin15AnchoredAtom2184 Fin15AnchoredAtom2185 Fin15AnchoredAtom2206 Fin15AnchoredAtom2220
    Fin15AnchoredAtom2221 Fin15AnchoredAtom2242 Fin15AnchoredAtom2291 Fin15AnchoredAtom2505
    Fin15AnchoredAtom2506 Fin15AnchoredAtom2527 Fin15AnchoredAtom2576 Fin15AnchoredAtom2660
    Fin15AnchoredAtom2878 Fin15AnchoredAtom2884 Fin15AnchoredAtom2885 Fin15AnchoredAtom2899
    Fin15AnchoredAtom2900 Fin15AnchoredAtom2921 Fin15AnchoredAtom2935 Fin15AnchoredAtom2936
    Fin15AnchoredAtom2957 Fin15AnchoredAtom3006 Fin15AnchoredAtom3220 Fin15AnchoredAtom3221
    Fin15AnchoredAtom3242 Fin15AnchoredAtom3291 Fin15AnchoredAtom3375 Fin15AnchoredAtom3715
    Fin15AnchoredAtom3716 Fin15AnchoredAtom3737 Fin15AnchoredAtom3786 Fin15AnchoredAtom3870
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

theorem fin15Anchored_clause30658 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom1978 chi ∧
      ¬Fin15AnchoredAtom2008 chi ∧
      ¬Fin15AnchoredAtom2010 chi ∧
      ¬Fin15AnchoredAtom2014 chi ∧
      ¬Fin15AnchoredAtom2088 chi ∧
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
      ¬Fin15AnchoredAtom2513 chi ∧
      ¬Fin15AnchoredAtom2515 chi ∧
      ¬Fin15AnchoredAtom2519 chi ∧
      ¬Fin15AnchoredAtom2593 chi ∧
      ¬Fin15AnchoredAtom2677 chi ∧
      ¬Fin15AnchoredAtom2880 chi ∧
      ¬Fin15AnchoredAtom2881 chi ∧
      ¬Fin15AnchoredAtom2883 chi ∧
      ¬Fin15AnchoredAtom2907 chi ∧
      ¬Fin15AnchoredAtom2909 chi ∧
      ¬Fin15AnchoredAtom2913 chi ∧
      ¬Fin15AnchoredAtom2943 chi ∧
      ¬Fin15AnchoredAtom2945 chi ∧
      ¬Fin15AnchoredAtom2949 chi ∧
      ¬Fin15AnchoredAtom3023 chi ∧
      ¬Fin15AnchoredAtom3228 chi ∧
      ¬Fin15AnchoredAtom3230 chi ∧
      ¬Fin15AnchoredAtom3234 chi ∧
      ¬Fin15AnchoredAtom3308 chi ∧
      ¬Fin15AnchoredAtom3392 chi ∧
      ¬Fin15AnchoredAtom3723 chi ∧
      ¬Fin15AnchoredAtom3725 chi ∧
      ¬Fin15AnchoredAtom3729 chi ∧
      ¬Fin15AnchoredAtom3803 chi ∧
      ¬Fin15AnchoredAtom3887 chi ∧
      ¬Fin15AnchoredAtom4427 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 5, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05687
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1832 Fin15AnchoredAtom1836 Fin15AnchoredAtom1837
    Fin15AnchoredAtom1839 Fin15AnchoredAtom1845 Fin15AnchoredAtom1846 Fin15AnchoredAtom1848
    Fin15AnchoredAtom1872 Fin15AnchoredAtom1874 Fin15AnchoredAtom1878 Fin15AnchoredAtom1945
    Fin15AnchoredAtom1946 Fin15AnchoredAtom1948 Fin15AnchoredAtom1972 Fin15AnchoredAtom1974
    Fin15AnchoredAtom1978 Fin15AnchoredAtom2008 Fin15AnchoredAtom2010 Fin15AnchoredAtom2014
    Fin15AnchoredAtom2088 Fin15AnchoredAtom2165 Fin15AnchoredAtom2166 Fin15AnchoredAtom2168
    Fin15AnchoredAtom2192 Fin15AnchoredAtom2194 Fin15AnchoredAtom2198 Fin15AnchoredAtom2228
    Fin15AnchoredAtom2230 Fin15AnchoredAtom2234 Fin15AnchoredAtom2308 Fin15AnchoredAtom2513
    Fin15AnchoredAtom2515 Fin15AnchoredAtom2519 Fin15AnchoredAtom2593 Fin15AnchoredAtom2677
    Fin15AnchoredAtom2880 Fin15AnchoredAtom2881 Fin15AnchoredAtom2883 Fin15AnchoredAtom2907
    Fin15AnchoredAtom2909 Fin15AnchoredAtom2913 Fin15AnchoredAtom2943 Fin15AnchoredAtom2945
    Fin15AnchoredAtom2949 Fin15AnchoredAtom3023 Fin15AnchoredAtom3228 Fin15AnchoredAtom3230
    Fin15AnchoredAtom3234 Fin15AnchoredAtom3308 Fin15AnchoredAtom3392 Fin15AnchoredAtom3723
    Fin15AnchoredAtom3725 Fin15AnchoredAtom3729 Fin15AnchoredAtom3803 Fin15AnchoredAtom3887
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

theorem fin15Anchored_clause30659 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom1979 chi ∧
      ¬Fin15AnchoredAtom2008 chi ∧
      ¬Fin15AnchoredAtom2011 chi ∧
      ¬Fin15AnchoredAtom2015 chi ∧
      ¬Fin15AnchoredAtom2089 chi ∧
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
      ¬Fin15AnchoredAtom2513 chi ∧
      ¬Fin15AnchoredAtom2516 chi ∧
      ¬Fin15AnchoredAtom2520 chi ∧
      ¬Fin15AnchoredAtom2594 chi ∧
      ¬Fin15AnchoredAtom2678 chi ∧
      ¬Fin15AnchoredAtom2880 chi ∧
      ¬Fin15AnchoredAtom2881 chi ∧
      ¬Fin15AnchoredAtom2884 chi ∧
      ¬Fin15AnchoredAtom2907 chi ∧
      ¬Fin15AnchoredAtom2910 chi ∧
      ¬Fin15AnchoredAtom2914 chi ∧
      ¬Fin15AnchoredAtom2943 chi ∧
      ¬Fin15AnchoredAtom2946 chi ∧
      ¬Fin15AnchoredAtom2950 chi ∧
      ¬Fin15AnchoredAtom3024 chi ∧
      ¬Fin15AnchoredAtom3228 chi ∧
      ¬Fin15AnchoredAtom3231 chi ∧
      ¬Fin15AnchoredAtom3235 chi ∧
      ¬Fin15AnchoredAtom3309 chi ∧
      ¬Fin15AnchoredAtom3393 chi ∧
      ¬Fin15AnchoredAtom3723 chi ∧
      ¬Fin15AnchoredAtom3726 chi ∧
      ¬Fin15AnchoredAtom3730 chi ∧
      ¬Fin15AnchoredAtom3804 chi ∧
      ¬Fin15AnchoredAtom3888 chi ∧
      ¬Fin15AnchoredAtom4428 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 5, 9, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09783
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1832 Fin15AnchoredAtom1836 Fin15AnchoredAtom1837
    Fin15AnchoredAtom1840 Fin15AnchoredAtom1845 Fin15AnchoredAtom1846 Fin15AnchoredAtom1849
    Fin15AnchoredAtom1872 Fin15AnchoredAtom1875 Fin15AnchoredAtom1879 Fin15AnchoredAtom1945
    Fin15AnchoredAtom1946 Fin15AnchoredAtom1949 Fin15AnchoredAtom1972 Fin15AnchoredAtom1975
    Fin15AnchoredAtom1979 Fin15AnchoredAtom2008 Fin15AnchoredAtom2011 Fin15AnchoredAtom2015
    Fin15AnchoredAtom2089 Fin15AnchoredAtom2165 Fin15AnchoredAtom2166 Fin15AnchoredAtom2169
    Fin15AnchoredAtom2192 Fin15AnchoredAtom2195 Fin15AnchoredAtom2199 Fin15AnchoredAtom2228
    Fin15AnchoredAtom2231 Fin15AnchoredAtom2235 Fin15AnchoredAtom2309 Fin15AnchoredAtom2513
    Fin15AnchoredAtom2516 Fin15AnchoredAtom2520 Fin15AnchoredAtom2594 Fin15AnchoredAtom2678
    Fin15AnchoredAtom2880 Fin15AnchoredAtom2881 Fin15AnchoredAtom2884 Fin15AnchoredAtom2907
    Fin15AnchoredAtom2910 Fin15AnchoredAtom2914 Fin15AnchoredAtom2943 Fin15AnchoredAtom2946
    Fin15AnchoredAtom2950 Fin15AnchoredAtom3024 Fin15AnchoredAtom3228 Fin15AnchoredAtom3231
    Fin15AnchoredAtom3235 Fin15AnchoredAtom3309 Fin15AnchoredAtom3393 Fin15AnchoredAtom3723
    Fin15AnchoredAtom3726 Fin15AnchoredAtom3730 Fin15AnchoredAtom3804 Fin15AnchoredAtom3888
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

theorem fin15Anchored_clause30660 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom1976 chi ∧
      ¬Fin15AnchoredAtom1980 chi ∧
      ¬Fin15AnchoredAtom2008 chi ∧
      ¬Fin15AnchoredAtom2012 chi ∧
      ¬Fin15AnchoredAtom2016 chi ∧
      ¬Fin15AnchoredAtom2090 chi ∧
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
      ¬Fin15AnchoredAtom2513 chi ∧
      ¬Fin15AnchoredAtom2517 chi ∧
      ¬Fin15AnchoredAtom2521 chi ∧
      ¬Fin15AnchoredAtom2595 chi ∧
      ¬Fin15AnchoredAtom2679 chi ∧
      ¬Fin15AnchoredAtom2880 chi ∧
      ¬Fin15AnchoredAtom2881 chi ∧
      ¬Fin15AnchoredAtom2885 chi ∧
      ¬Fin15AnchoredAtom2907 chi ∧
      ¬Fin15AnchoredAtom2911 chi ∧
      ¬Fin15AnchoredAtom2915 chi ∧
      ¬Fin15AnchoredAtom2943 chi ∧
      ¬Fin15AnchoredAtom2947 chi ∧
      ¬Fin15AnchoredAtom2951 chi ∧
      ¬Fin15AnchoredAtom3025 chi ∧
      ¬Fin15AnchoredAtom3228 chi ∧
      ¬Fin15AnchoredAtom3232 chi ∧
      ¬Fin15AnchoredAtom3236 chi ∧
      ¬Fin15AnchoredAtom3310 chi ∧
      ¬Fin15AnchoredAtom3394 chi ∧
      ¬Fin15AnchoredAtom3723 chi ∧
      ¬Fin15AnchoredAtom3727 chi ∧
      ¬Fin15AnchoredAtom3731 chi ∧
      ¬Fin15AnchoredAtom3805 chi ∧
      ¬Fin15AnchoredAtom3889 chi ∧
      ¬Fin15AnchoredAtom4429 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 5, 9, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17975
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1832 Fin15AnchoredAtom1836 Fin15AnchoredAtom1837
    Fin15AnchoredAtom1841 Fin15AnchoredAtom1845 Fin15AnchoredAtom1846 Fin15AnchoredAtom1850
    Fin15AnchoredAtom1872 Fin15AnchoredAtom1876 Fin15AnchoredAtom1880 Fin15AnchoredAtom1945
    Fin15AnchoredAtom1946 Fin15AnchoredAtom1950 Fin15AnchoredAtom1972 Fin15AnchoredAtom1976
    Fin15AnchoredAtom1980 Fin15AnchoredAtom2008 Fin15AnchoredAtom2012 Fin15AnchoredAtom2016
    Fin15AnchoredAtom2090 Fin15AnchoredAtom2165 Fin15AnchoredAtom2166 Fin15AnchoredAtom2170
    Fin15AnchoredAtom2192 Fin15AnchoredAtom2196 Fin15AnchoredAtom2200 Fin15AnchoredAtom2228
    Fin15AnchoredAtom2232 Fin15AnchoredAtom2236 Fin15AnchoredAtom2310 Fin15AnchoredAtom2513
    Fin15AnchoredAtom2517 Fin15AnchoredAtom2521 Fin15AnchoredAtom2595 Fin15AnchoredAtom2679
    Fin15AnchoredAtom2880 Fin15AnchoredAtom2881 Fin15AnchoredAtom2885 Fin15AnchoredAtom2907
    Fin15AnchoredAtom2911 Fin15AnchoredAtom2915 Fin15AnchoredAtom2943 Fin15AnchoredAtom2947
    Fin15AnchoredAtom2951 Fin15AnchoredAtom3025 Fin15AnchoredAtom3228 Fin15AnchoredAtom3232
    Fin15AnchoredAtom3236 Fin15AnchoredAtom3310 Fin15AnchoredAtom3394 Fin15AnchoredAtom3723
    Fin15AnchoredAtom3727 Fin15AnchoredAtom3731 Fin15AnchoredAtom3805 Fin15AnchoredAtom3889
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

theorem fin15Anchored_clause30661 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom1984 chi ∧
      ¬Fin15AnchoredAtom2010 chi ∧
      ¬Fin15AnchoredAtom2011 chi ∧
      ¬Fin15AnchoredAtom2020 chi ∧
      ¬Fin15AnchoredAtom2094 chi ∧
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
      ¬Fin15AnchoredAtom2515 chi ∧
      ¬Fin15AnchoredAtom2516 chi ∧
      ¬Fin15AnchoredAtom2525 chi ∧
      ¬Fin15AnchoredAtom2599 chi ∧
      ¬Fin15AnchoredAtom2683 chi ∧
      ¬Fin15AnchoredAtom2880 chi ∧
      ¬Fin15AnchoredAtom2883 chi ∧
      ¬Fin15AnchoredAtom2884 chi ∧
      ¬Fin15AnchoredAtom2909 chi ∧
      ¬Fin15AnchoredAtom2910 chi ∧
      ¬Fin15AnchoredAtom2919 chi ∧
      ¬Fin15AnchoredAtom2945 chi ∧
      ¬Fin15AnchoredAtom2946 chi ∧
      ¬Fin15AnchoredAtom2955 chi ∧
      ¬Fin15AnchoredAtom3029 chi ∧
      ¬Fin15AnchoredAtom3230 chi ∧
      ¬Fin15AnchoredAtom3231 chi ∧
      ¬Fin15AnchoredAtom3240 chi ∧
      ¬Fin15AnchoredAtom3314 chi ∧
      ¬Fin15AnchoredAtom3398 chi ∧
      ¬Fin15AnchoredAtom3725 chi ∧
      ¬Fin15AnchoredAtom3726 chi ∧
      ¬Fin15AnchoredAtom3735 chi ∧
      ¬Fin15AnchoredAtom3809 chi ∧
      ¬Fin15AnchoredAtom3893 chi ∧
      ¬Fin15AnchoredAtom4433 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 5, 9, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask12855
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1832 Fin15AnchoredAtom1836 Fin15AnchoredAtom1839
    Fin15AnchoredAtom1840 Fin15AnchoredAtom1845 Fin15AnchoredAtom1848 Fin15AnchoredAtom1849
    Fin15AnchoredAtom1874 Fin15AnchoredAtom1875 Fin15AnchoredAtom1884 Fin15AnchoredAtom1945
    Fin15AnchoredAtom1948 Fin15AnchoredAtom1949 Fin15AnchoredAtom1974 Fin15AnchoredAtom1975
    Fin15AnchoredAtom1984 Fin15AnchoredAtom2010 Fin15AnchoredAtom2011 Fin15AnchoredAtom2020
    Fin15AnchoredAtom2094 Fin15AnchoredAtom2165 Fin15AnchoredAtom2168 Fin15AnchoredAtom2169
    Fin15AnchoredAtom2194 Fin15AnchoredAtom2195 Fin15AnchoredAtom2204 Fin15AnchoredAtom2230
    Fin15AnchoredAtom2231 Fin15AnchoredAtom2240 Fin15AnchoredAtom2314 Fin15AnchoredAtom2515
    Fin15AnchoredAtom2516 Fin15AnchoredAtom2525 Fin15AnchoredAtom2599 Fin15AnchoredAtom2683
    Fin15AnchoredAtom2880 Fin15AnchoredAtom2883 Fin15AnchoredAtom2884 Fin15AnchoredAtom2909
    Fin15AnchoredAtom2910 Fin15AnchoredAtom2919 Fin15AnchoredAtom2945 Fin15AnchoredAtom2946
    Fin15AnchoredAtom2955 Fin15AnchoredAtom3029 Fin15AnchoredAtom3230 Fin15AnchoredAtom3231
    Fin15AnchoredAtom3240 Fin15AnchoredAtom3314 Fin15AnchoredAtom3398 Fin15AnchoredAtom3725
    Fin15AnchoredAtom3726 Fin15AnchoredAtom3735 Fin15AnchoredAtom3809 Fin15AnchoredAtom3893
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

theorem fin15Anchored_clause30662 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom1976 chi ∧
      ¬Fin15AnchoredAtom1985 chi ∧
      ¬Fin15AnchoredAtom2010 chi ∧
      ¬Fin15AnchoredAtom2012 chi ∧
      ¬Fin15AnchoredAtom2021 chi ∧
      ¬Fin15AnchoredAtom2095 chi ∧
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
      ¬Fin15AnchoredAtom2515 chi ∧
      ¬Fin15AnchoredAtom2517 chi ∧
      ¬Fin15AnchoredAtom2526 chi ∧
      ¬Fin15AnchoredAtom2600 chi ∧
      ¬Fin15AnchoredAtom2684 chi ∧
      ¬Fin15AnchoredAtom2880 chi ∧
      ¬Fin15AnchoredAtom2883 chi ∧
      ¬Fin15AnchoredAtom2885 chi ∧
      ¬Fin15AnchoredAtom2909 chi ∧
      ¬Fin15AnchoredAtom2911 chi ∧
      ¬Fin15AnchoredAtom2920 chi ∧
      ¬Fin15AnchoredAtom2945 chi ∧
      ¬Fin15AnchoredAtom2947 chi ∧
      ¬Fin15AnchoredAtom2956 chi ∧
      ¬Fin15AnchoredAtom3030 chi ∧
      ¬Fin15AnchoredAtom3230 chi ∧
      ¬Fin15AnchoredAtom3232 chi ∧
      ¬Fin15AnchoredAtom3241 chi ∧
      ¬Fin15AnchoredAtom3315 chi ∧
      ¬Fin15AnchoredAtom3399 chi ∧
      ¬Fin15AnchoredAtom3725 chi ∧
      ¬Fin15AnchoredAtom3727 chi ∧
      ¬Fin15AnchoredAtom3736 chi ∧
      ¬Fin15AnchoredAtom3810 chi ∧
      ¬Fin15AnchoredAtom3894 chi ∧
      ¬Fin15AnchoredAtom4434 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 5, 9, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21047
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1832 Fin15AnchoredAtom1836 Fin15AnchoredAtom1839
    Fin15AnchoredAtom1841 Fin15AnchoredAtom1845 Fin15AnchoredAtom1848 Fin15AnchoredAtom1850
    Fin15AnchoredAtom1874 Fin15AnchoredAtom1876 Fin15AnchoredAtom1885 Fin15AnchoredAtom1945
    Fin15AnchoredAtom1948 Fin15AnchoredAtom1950 Fin15AnchoredAtom1974 Fin15AnchoredAtom1976
    Fin15AnchoredAtom1985 Fin15AnchoredAtom2010 Fin15AnchoredAtom2012 Fin15AnchoredAtom2021
    Fin15AnchoredAtom2095 Fin15AnchoredAtom2165 Fin15AnchoredAtom2168 Fin15AnchoredAtom2170
    Fin15AnchoredAtom2194 Fin15AnchoredAtom2196 Fin15AnchoredAtom2205 Fin15AnchoredAtom2230
    Fin15AnchoredAtom2232 Fin15AnchoredAtom2241 Fin15AnchoredAtom2315 Fin15AnchoredAtom2515
    Fin15AnchoredAtom2517 Fin15AnchoredAtom2526 Fin15AnchoredAtom2600 Fin15AnchoredAtom2684
    Fin15AnchoredAtom2880 Fin15AnchoredAtom2883 Fin15AnchoredAtom2885 Fin15AnchoredAtom2909
    Fin15AnchoredAtom2911 Fin15AnchoredAtom2920 Fin15AnchoredAtom2945 Fin15AnchoredAtom2947
    Fin15AnchoredAtom2956 Fin15AnchoredAtom3030 Fin15AnchoredAtom3230 Fin15AnchoredAtom3232
    Fin15AnchoredAtom3241 Fin15AnchoredAtom3315 Fin15AnchoredAtom3399 Fin15AnchoredAtom3725
    Fin15AnchoredAtom3727 Fin15AnchoredAtom3736 Fin15AnchoredAtom3810 Fin15AnchoredAtom3894
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

theorem fin15Anchored_clause30663 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom1886 chi ∧
      ¬Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom1976 chi ∧
      ¬Fin15AnchoredAtom1986 chi ∧
      ¬Fin15AnchoredAtom2011 chi ∧
      ¬Fin15AnchoredAtom2012 chi ∧
      ¬Fin15AnchoredAtom2022 chi ∧
      ¬Fin15AnchoredAtom2096 chi ∧
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
      ¬Fin15AnchoredAtom2516 chi ∧
      ¬Fin15AnchoredAtom2517 chi ∧
      ¬Fin15AnchoredAtom2527 chi ∧
      ¬Fin15AnchoredAtom2601 chi ∧
      ¬Fin15AnchoredAtom2685 chi ∧
      ¬Fin15AnchoredAtom2880 chi ∧
      ¬Fin15AnchoredAtom2884 chi ∧
      ¬Fin15AnchoredAtom2885 chi ∧
      ¬Fin15AnchoredAtom2910 chi ∧
      ¬Fin15AnchoredAtom2911 chi ∧
      ¬Fin15AnchoredAtom2921 chi ∧
      ¬Fin15AnchoredAtom2946 chi ∧
      ¬Fin15AnchoredAtom2947 chi ∧
      ¬Fin15AnchoredAtom2957 chi ∧
      ¬Fin15AnchoredAtom3031 chi ∧
      ¬Fin15AnchoredAtom3231 chi ∧
      ¬Fin15AnchoredAtom3232 chi ∧
      ¬Fin15AnchoredAtom3242 chi ∧
      ¬Fin15AnchoredAtom3316 chi ∧
      ¬Fin15AnchoredAtom3400 chi ∧
      ¬Fin15AnchoredAtom3726 chi ∧
      ¬Fin15AnchoredAtom3727 chi ∧
      ¬Fin15AnchoredAtom3737 chi ∧
      ¬Fin15AnchoredAtom3811 chi ∧
      ¬Fin15AnchoredAtom3895 chi ∧
      ¬Fin15AnchoredAtom4435 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 5, 9, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25143
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1832 Fin15AnchoredAtom1836 Fin15AnchoredAtom1840
    Fin15AnchoredAtom1841 Fin15AnchoredAtom1845 Fin15AnchoredAtom1849 Fin15AnchoredAtom1850
    Fin15AnchoredAtom1875 Fin15AnchoredAtom1876 Fin15AnchoredAtom1886 Fin15AnchoredAtom1945
    Fin15AnchoredAtom1949 Fin15AnchoredAtom1950 Fin15AnchoredAtom1975 Fin15AnchoredAtom1976
    Fin15AnchoredAtom1986 Fin15AnchoredAtom2011 Fin15AnchoredAtom2012 Fin15AnchoredAtom2022
    Fin15AnchoredAtom2096 Fin15AnchoredAtom2165 Fin15AnchoredAtom2169 Fin15AnchoredAtom2170
    Fin15AnchoredAtom2195 Fin15AnchoredAtom2196 Fin15AnchoredAtom2206 Fin15AnchoredAtom2231
    Fin15AnchoredAtom2232 Fin15AnchoredAtom2242 Fin15AnchoredAtom2316 Fin15AnchoredAtom2516
    Fin15AnchoredAtom2517 Fin15AnchoredAtom2527 Fin15AnchoredAtom2601 Fin15AnchoredAtom2685
    Fin15AnchoredAtom2880 Fin15AnchoredAtom2884 Fin15AnchoredAtom2885 Fin15AnchoredAtom2910
    Fin15AnchoredAtom2911 Fin15AnchoredAtom2921 Fin15AnchoredAtom2946 Fin15AnchoredAtom2947
    Fin15AnchoredAtom2957 Fin15AnchoredAtom3031 Fin15AnchoredAtom3231 Fin15AnchoredAtom3232
    Fin15AnchoredAtom3242 Fin15AnchoredAtom3316 Fin15AnchoredAtom3400 Fin15AnchoredAtom3726
    Fin15AnchoredAtom3727 Fin15AnchoredAtom3737 Fin15AnchoredAtom3811 Fin15AnchoredAtom3895
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

theorem fin15Anchored_clause30664 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom1978 chi ∧
      ¬Fin15AnchoredAtom1979 chi ∧
      ¬Fin15AnchoredAtom1984 chi ∧
      ¬Fin15AnchoredAtom2014 chi ∧
      ¬Fin15AnchoredAtom2015 chi ∧
      ¬Fin15AnchoredAtom2020 chi ∧
      ¬Fin15AnchoredAtom2100 chi ∧
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
      ¬Fin15AnchoredAtom2519 chi ∧
      ¬Fin15AnchoredAtom2520 chi ∧
      ¬Fin15AnchoredAtom2525 chi ∧
      ¬Fin15AnchoredAtom2605 chi ∧
      ¬Fin15AnchoredAtom2689 chi ∧
      ¬Fin15AnchoredAtom2881 chi ∧
      ¬Fin15AnchoredAtom2883 chi ∧
      ¬Fin15AnchoredAtom2884 chi ∧
      ¬Fin15AnchoredAtom2913 chi ∧
      ¬Fin15AnchoredAtom2914 chi ∧
      ¬Fin15AnchoredAtom2919 chi ∧
      ¬Fin15AnchoredAtom2949 chi ∧
      ¬Fin15AnchoredAtom2950 chi ∧
      ¬Fin15AnchoredAtom2955 chi ∧
      ¬Fin15AnchoredAtom3035 chi ∧
      ¬Fin15AnchoredAtom3234 chi ∧
      ¬Fin15AnchoredAtom3235 chi ∧
      ¬Fin15AnchoredAtom3240 chi ∧
      ¬Fin15AnchoredAtom3320 chi ∧
      ¬Fin15AnchoredAtom3404 chi ∧
      ¬Fin15AnchoredAtom3729 chi ∧
      ¬Fin15AnchoredAtom3730 chi ∧
      ¬Fin15AnchoredAtom3735 chi ∧
      ¬Fin15AnchoredAtom3815 chi ∧
      ¬Fin15AnchoredAtom3899 chi ∧
      ¬Fin15AnchoredAtom4439 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 5, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13367
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1832 Fin15AnchoredAtom1837 Fin15AnchoredAtom1839
    Fin15AnchoredAtom1840 Fin15AnchoredAtom1846 Fin15AnchoredAtom1848 Fin15AnchoredAtom1849
    Fin15AnchoredAtom1878 Fin15AnchoredAtom1879 Fin15AnchoredAtom1884 Fin15AnchoredAtom1946
    Fin15AnchoredAtom1948 Fin15AnchoredAtom1949 Fin15AnchoredAtom1978 Fin15AnchoredAtom1979
    Fin15AnchoredAtom1984 Fin15AnchoredAtom2014 Fin15AnchoredAtom2015 Fin15AnchoredAtom2020
    Fin15AnchoredAtom2100 Fin15AnchoredAtom2166 Fin15AnchoredAtom2168 Fin15AnchoredAtom2169
    Fin15AnchoredAtom2198 Fin15AnchoredAtom2199 Fin15AnchoredAtom2204 Fin15AnchoredAtom2234
    Fin15AnchoredAtom2235 Fin15AnchoredAtom2240 Fin15AnchoredAtom2320 Fin15AnchoredAtom2519
    Fin15AnchoredAtom2520 Fin15AnchoredAtom2525 Fin15AnchoredAtom2605 Fin15AnchoredAtom2689
    Fin15AnchoredAtom2881 Fin15AnchoredAtom2883 Fin15AnchoredAtom2884 Fin15AnchoredAtom2913
    Fin15AnchoredAtom2914 Fin15AnchoredAtom2919 Fin15AnchoredAtom2949 Fin15AnchoredAtom2950
    Fin15AnchoredAtom2955 Fin15AnchoredAtom3035 Fin15AnchoredAtom3234 Fin15AnchoredAtom3235
    Fin15AnchoredAtom3240 Fin15AnchoredAtom3320 Fin15AnchoredAtom3404 Fin15AnchoredAtom3729
    Fin15AnchoredAtom3730 Fin15AnchoredAtom3735 Fin15AnchoredAtom3815 Fin15AnchoredAtom3899
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

theorem fin15Anchored_clause30665 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom1978 chi ∧
      ¬Fin15AnchoredAtom1980 chi ∧
      ¬Fin15AnchoredAtom1985 chi ∧
      ¬Fin15AnchoredAtom2014 chi ∧
      ¬Fin15AnchoredAtom2016 chi ∧
      ¬Fin15AnchoredAtom2021 chi ∧
      ¬Fin15AnchoredAtom2101 chi ∧
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
      ¬Fin15AnchoredAtom2519 chi ∧
      ¬Fin15AnchoredAtom2521 chi ∧
      ¬Fin15AnchoredAtom2526 chi ∧
      ¬Fin15AnchoredAtom2606 chi ∧
      ¬Fin15AnchoredAtom2690 chi ∧
      ¬Fin15AnchoredAtom2881 chi ∧
      ¬Fin15AnchoredAtom2883 chi ∧
      ¬Fin15AnchoredAtom2885 chi ∧
      ¬Fin15AnchoredAtom2913 chi ∧
      ¬Fin15AnchoredAtom2915 chi ∧
      ¬Fin15AnchoredAtom2920 chi ∧
      ¬Fin15AnchoredAtom2949 chi ∧
      ¬Fin15AnchoredAtom2951 chi ∧
      ¬Fin15AnchoredAtom2956 chi ∧
      ¬Fin15AnchoredAtom3036 chi ∧
      ¬Fin15AnchoredAtom3234 chi ∧
      ¬Fin15AnchoredAtom3236 chi ∧
      ¬Fin15AnchoredAtom3241 chi ∧
      ¬Fin15AnchoredAtom3321 chi ∧
      ¬Fin15AnchoredAtom3405 chi ∧
      ¬Fin15AnchoredAtom3729 chi ∧
      ¬Fin15AnchoredAtom3731 chi ∧
      ¬Fin15AnchoredAtom3736 chi ∧
      ¬Fin15AnchoredAtom3816 chi ∧
      ¬Fin15AnchoredAtom3900 chi ∧
      ¬Fin15AnchoredAtom4440 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 5, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21559
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1832 Fin15AnchoredAtom1837 Fin15AnchoredAtom1839
    Fin15AnchoredAtom1841 Fin15AnchoredAtom1846 Fin15AnchoredAtom1848 Fin15AnchoredAtom1850
    Fin15AnchoredAtom1878 Fin15AnchoredAtom1880 Fin15AnchoredAtom1885 Fin15AnchoredAtom1946
    Fin15AnchoredAtom1948 Fin15AnchoredAtom1950 Fin15AnchoredAtom1978 Fin15AnchoredAtom1980
    Fin15AnchoredAtom1985 Fin15AnchoredAtom2014 Fin15AnchoredAtom2016 Fin15AnchoredAtom2021
    Fin15AnchoredAtom2101 Fin15AnchoredAtom2166 Fin15AnchoredAtom2168 Fin15AnchoredAtom2170
    Fin15AnchoredAtom2198 Fin15AnchoredAtom2200 Fin15AnchoredAtom2205 Fin15AnchoredAtom2234
    Fin15AnchoredAtom2236 Fin15AnchoredAtom2241 Fin15AnchoredAtom2321 Fin15AnchoredAtom2519
    Fin15AnchoredAtom2521 Fin15AnchoredAtom2526 Fin15AnchoredAtom2606 Fin15AnchoredAtom2690
    Fin15AnchoredAtom2881 Fin15AnchoredAtom2883 Fin15AnchoredAtom2885 Fin15AnchoredAtom2913
    Fin15AnchoredAtom2915 Fin15AnchoredAtom2920 Fin15AnchoredAtom2949 Fin15AnchoredAtom2951
    Fin15AnchoredAtom2956 Fin15AnchoredAtom3036 Fin15AnchoredAtom3234 Fin15AnchoredAtom3236
    Fin15AnchoredAtom3241 Fin15AnchoredAtom3321 Fin15AnchoredAtom3405 Fin15AnchoredAtom3729
    Fin15AnchoredAtom3731 Fin15AnchoredAtom3736 Fin15AnchoredAtom3816 Fin15AnchoredAtom3900
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

theorem fin15Anchored_clause30666 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom1886 chi ∧
      ¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom1979 chi ∧
      ¬Fin15AnchoredAtom1980 chi ∧
      ¬Fin15AnchoredAtom1986 chi ∧
      ¬Fin15AnchoredAtom2015 chi ∧
      ¬Fin15AnchoredAtom2016 chi ∧
      ¬Fin15AnchoredAtom2022 chi ∧
      ¬Fin15AnchoredAtom2102 chi ∧
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
      ¬Fin15AnchoredAtom2520 chi ∧
      ¬Fin15AnchoredAtom2521 chi ∧
      ¬Fin15AnchoredAtom2527 chi ∧
      ¬Fin15AnchoredAtom2607 chi ∧
      ¬Fin15AnchoredAtom2691 chi ∧
      ¬Fin15AnchoredAtom2881 chi ∧
      ¬Fin15AnchoredAtom2884 chi ∧
      ¬Fin15AnchoredAtom2885 chi ∧
      ¬Fin15AnchoredAtom2914 chi ∧
      ¬Fin15AnchoredAtom2915 chi ∧
      ¬Fin15AnchoredAtom2921 chi ∧
      ¬Fin15AnchoredAtom2950 chi ∧
      ¬Fin15AnchoredAtom2951 chi ∧
      ¬Fin15AnchoredAtom2957 chi ∧
      ¬Fin15AnchoredAtom3037 chi ∧
      ¬Fin15AnchoredAtom3235 chi ∧
      ¬Fin15AnchoredAtom3236 chi ∧
      ¬Fin15AnchoredAtom3242 chi ∧
      ¬Fin15AnchoredAtom3322 chi ∧
      ¬Fin15AnchoredAtom3406 chi ∧
      ¬Fin15AnchoredAtom3730 chi ∧
      ¬Fin15AnchoredAtom3731 chi ∧
      ¬Fin15AnchoredAtom3737 chi ∧
      ¬Fin15AnchoredAtom3817 chi ∧
      ¬Fin15AnchoredAtom3901 chi ∧
      ¬Fin15AnchoredAtom4441 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 5, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25655
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1832 Fin15AnchoredAtom1837 Fin15AnchoredAtom1840
    Fin15AnchoredAtom1841 Fin15AnchoredAtom1846 Fin15AnchoredAtom1849 Fin15AnchoredAtom1850
    Fin15AnchoredAtom1879 Fin15AnchoredAtom1880 Fin15AnchoredAtom1886 Fin15AnchoredAtom1946
    Fin15AnchoredAtom1949 Fin15AnchoredAtom1950 Fin15AnchoredAtom1979 Fin15AnchoredAtom1980
    Fin15AnchoredAtom1986 Fin15AnchoredAtom2015 Fin15AnchoredAtom2016 Fin15AnchoredAtom2022
    Fin15AnchoredAtom2102 Fin15AnchoredAtom2166 Fin15AnchoredAtom2169 Fin15AnchoredAtom2170
    Fin15AnchoredAtom2199 Fin15AnchoredAtom2200 Fin15AnchoredAtom2206 Fin15AnchoredAtom2235
    Fin15AnchoredAtom2236 Fin15AnchoredAtom2242 Fin15AnchoredAtom2322 Fin15AnchoredAtom2520
    Fin15AnchoredAtom2521 Fin15AnchoredAtom2527 Fin15AnchoredAtom2607 Fin15AnchoredAtom2691
    Fin15AnchoredAtom2881 Fin15AnchoredAtom2884 Fin15AnchoredAtom2885 Fin15AnchoredAtom2914
    Fin15AnchoredAtom2915 Fin15AnchoredAtom2921 Fin15AnchoredAtom2950 Fin15AnchoredAtom2951
    Fin15AnchoredAtom2957 Fin15AnchoredAtom3037 Fin15AnchoredAtom3235 Fin15AnchoredAtom3236
    Fin15AnchoredAtom3242 Fin15AnchoredAtom3322 Fin15AnchoredAtom3406 Fin15AnchoredAtom3730
    Fin15AnchoredAtom3731 Fin15AnchoredAtom3737 Fin15AnchoredAtom3817 Fin15AnchoredAtom3901
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

theorem fin15Anchored_clause30667 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom1886 chi ∧
      ¬Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom1984 chi ∧
      ¬Fin15AnchoredAtom1985 chi ∧
      ¬Fin15AnchoredAtom1986 chi ∧
      ¬Fin15AnchoredAtom2020 chi ∧
      ¬Fin15AnchoredAtom2021 chi ∧
      ¬Fin15AnchoredAtom2022 chi ∧
      ¬Fin15AnchoredAtom2106 chi ∧
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
      ¬Fin15AnchoredAtom2525 chi ∧
      ¬Fin15AnchoredAtom2526 chi ∧
      ¬Fin15AnchoredAtom2527 chi ∧
      ¬Fin15AnchoredAtom2611 chi ∧
      ¬Fin15AnchoredAtom2695 chi ∧
      ¬Fin15AnchoredAtom2883 chi ∧
      ¬Fin15AnchoredAtom2884 chi ∧
      ¬Fin15AnchoredAtom2885 chi ∧
      ¬Fin15AnchoredAtom2919 chi ∧
      ¬Fin15AnchoredAtom2920 chi ∧
      ¬Fin15AnchoredAtom2921 chi ∧
      ¬Fin15AnchoredAtom2955 chi ∧
      ¬Fin15AnchoredAtom2956 chi ∧
      ¬Fin15AnchoredAtom2957 chi ∧
      ¬Fin15AnchoredAtom3041 chi ∧
      ¬Fin15AnchoredAtom3240 chi ∧
      ¬Fin15AnchoredAtom3241 chi ∧
      ¬Fin15AnchoredAtom3242 chi ∧
      ¬Fin15AnchoredAtom3326 chi ∧
      ¬Fin15AnchoredAtom3410 chi ∧
      ¬Fin15AnchoredAtom3735 chi ∧
      ¬Fin15AnchoredAtom3736 chi ∧
      ¬Fin15AnchoredAtom3737 chi ∧
      ¬Fin15AnchoredAtom3821 chi ∧
      ¬Fin15AnchoredAtom3905 chi ∧
      ¬Fin15AnchoredAtom4445 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 5, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask28727
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1832 Fin15AnchoredAtom1839 Fin15AnchoredAtom1840
    Fin15AnchoredAtom1841 Fin15AnchoredAtom1848 Fin15AnchoredAtom1849 Fin15AnchoredAtom1850
    Fin15AnchoredAtom1884 Fin15AnchoredAtom1885 Fin15AnchoredAtom1886 Fin15AnchoredAtom1948
    Fin15AnchoredAtom1949 Fin15AnchoredAtom1950 Fin15AnchoredAtom1984 Fin15AnchoredAtom1985
    Fin15AnchoredAtom1986 Fin15AnchoredAtom2020 Fin15AnchoredAtom2021 Fin15AnchoredAtom2022
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2168 Fin15AnchoredAtom2169 Fin15AnchoredAtom2170
    Fin15AnchoredAtom2204 Fin15AnchoredAtom2205 Fin15AnchoredAtom2206 Fin15AnchoredAtom2240
    Fin15AnchoredAtom2241 Fin15AnchoredAtom2242 Fin15AnchoredAtom2326 Fin15AnchoredAtom2525
    Fin15AnchoredAtom2526 Fin15AnchoredAtom2527 Fin15AnchoredAtom2611 Fin15AnchoredAtom2695
    Fin15AnchoredAtom2883 Fin15AnchoredAtom2884 Fin15AnchoredAtom2885 Fin15AnchoredAtom2919
    Fin15AnchoredAtom2920 Fin15AnchoredAtom2921 Fin15AnchoredAtom2955 Fin15AnchoredAtom2956
    Fin15AnchoredAtom2957 Fin15AnchoredAtom3041 Fin15AnchoredAtom3240 Fin15AnchoredAtom3241
    Fin15AnchoredAtom3242 Fin15AnchoredAtom3326 Fin15AnchoredAtom3410 Fin15AnchoredAtom3735
    Fin15AnchoredAtom3736 Fin15AnchoredAtom3737 Fin15AnchoredAtom3821 Fin15AnchoredAtom3905
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

theorem fin15Anchored_clause30668 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom2024 chi ∧
      ¬Fin15AnchoredAtom2025 chi ∧
      ¬Fin15AnchoredAtom2036 chi ∧
      ¬Fin15AnchoredAtom2057 chi ∧
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
      ¬Fin15AnchoredAtom2529 chi ∧
      ¬Fin15AnchoredAtom2530 chi ∧
      ¬Fin15AnchoredAtom2541 chi ∧
      ¬Fin15AnchoredAtom2562 chi ∧
      ¬Fin15AnchoredAtom2702 chi ∧
      ¬Fin15AnchoredAtom2886 chi ∧
      ¬Fin15AnchoredAtom2888 chi ∧
      ¬Fin15AnchoredAtom2889 chi ∧
      ¬Fin15AnchoredAtom2895 chi ∧
      ¬Fin15AnchoredAtom2896 chi ∧
      ¬Fin15AnchoredAtom2907 chi ∧
      ¬Fin15AnchoredAtom2959 chi ∧
      ¬Fin15AnchoredAtom2960 chi ∧
      ¬Fin15AnchoredAtom2971 chi ∧
      ¬Fin15AnchoredAtom2992 chi ∧
      ¬Fin15AnchoredAtom3244 chi ∧
      ¬Fin15AnchoredAtom3245 chi ∧
      ¬Fin15AnchoredAtom3256 chi ∧
      ¬Fin15AnchoredAtom3277 chi ∧
      ¬Fin15AnchoredAtom3417 chi ∧
      ¬Fin15AnchoredAtom3739 chi ∧
      ¬Fin15AnchoredAtom3740 chi ∧
      ¬Fin15AnchoredAtom3751 chi ∧
      ¬Fin15AnchoredAtom3772 chi ∧
      ¬Fin15AnchoredAtom3912 chi ∧
      ¬Fin15AnchoredAtom4452 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 6, 7, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask01751
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1833 Fin15AnchoredAtom1834 Fin15AnchoredAtom1836
    Fin15AnchoredAtom1837 Fin15AnchoredAtom1851 Fin15AnchoredAtom1853 Fin15AnchoredAtom1854
    Fin15AnchoredAtom1860 Fin15AnchoredAtom1861 Fin15AnchoredAtom1872 Fin15AnchoredAtom1951
    Fin15AnchoredAtom1953 Fin15AnchoredAtom1954 Fin15AnchoredAtom1960 Fin15AnchoredAtom1961
    Fin15AnchoredAtom1972 Fin15AnchoredAtom2024 Fin15AnchoredAtom2025 Fin15AnchoredAtom2036
    Fin15AnchoredAtom2057 Fin15AnchoredAtom2171 Fin15AnchoredAtom2173 Fin15AnchoredAtom2174
    Fin15AnchoredAtom2180 Fin15AnchoredAtom2181 Fin15AnchoredAtom2192 Fin15AnchoredAtom2244
    Fin15AnchoredAtom2245 Fin15AnchoredAtom2256 Fin15AnchoredAtom2277 Fin15AnchoredAtom2529
    Fin15AnchoredAtom2530 Fin15AnchoredAtom2541 Fin15AnchoredAtom2562 Fin15AnchoredAtom2702
    Fin15AnchoredAtom2886 Fin15AnchoredAtom2888 Fin15AnchoredAtom2889 Fin15AnchoredAtom2895
    Fin15AnchoredAtom2896 Fin15AnchoredAtom2907 Fin15AnchoredAtom2959 Fin15AnchoredAtom2960
    Fin15AnchoredAtom2971 Fin15AnchoredAtom2992 Fin15AnchoredAtom3244 Fin15AnchoredAtom3245
    Fin15AnchoredAtom3256 Fin15AnchoredAtom3277 Fin15AnchoredAtom3417 Fin15AnchoredAtom3739
    Fin15AnchoredAtom3740 Fin15AnchoredAtom3751 Fin15AnchoredAtom3772 Fin15AnchoredAtom3912
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

theorem fin15Anchored_clause30669 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1838 chi ∧
      ¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1855 chi ∧
      ¬Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom1862 chi ∧
      ¬Fin15AnchoredAtom1873 chi ∧
      ¬Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom1955 chi ∧
      ¬Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom1962 chi ∧
      ¬Fin15AnchoredAtom1973 chi ∧
      ¬Fin15AnchoredAtom2024 chi ∧
      ¬Fin15AnchoredAtom2026 chi ∧
      ¬Fin15AnchoredAtom2037 chi ∧
      ¬Fin15AnchoredAtom2058 chi ∧
      ¬Fin15AnchoredAtom2171 chi ∧
      ¬Fin15AnchoredAtom2173 chi ∧
      ¬Fin15AnchoredAtom2175 chi ∧
      ¬Fin15AnchoredAtom2180 chi ∧
      ¬Fin15AnchoredAtom2182 chi ∧
      ¬Fin15AnchoredAtom2193 chi ∧
      ¬Fin15AnchoredAtom2244 chi ∧
      ¬Fin15AnchoredAtom2246 chi ∧
      ¬Fin15AnchoredAtom2257 chi ∧
      ¬Fin15AnchoredAtom2278 chi ∧
      ¬Fin15AnchoredAtom2529 chi ∧
      ¬Fin15AnchoredAtom2531 chi ∧
      ¬Fin15AnchoredAtom2542 chi ∧
      ¬Fin15AnchoredAtom2563 chi ∧
      ¬Fin15AnchoredAtom2703 chi ∧
      ¬Fin15AnchoredAtom2886 chi ∧
      ¬Fin15AnchoredAtom2888 chi ∧
      ¬Fin15AnchoredAtom2890 chi ∧
      ¬Fin15AnchoredAtom2895 chi ∧
      ¬Fin15AnchoredAtom2897 chi ∧
      ¬Fin15AnchoredAtom2908 chi ∧
      ¬Fin15AnchoredAtom2959 chi ∧
      ¬Fin15AnchoredAtom2961 chi ∧
      ¬Fin15AnchoredAtom2972 chi ∧
      ¬Fin15AnchoredAtom2993 chi ∧
      ¬Fin15AnchoredAtom3244 chi ∧
      ¬Fin15AnchoredAtom3246 chi ∧
      ¬Fin15AnchoredAtom3257 chi ∧
      ¬Fin15AnchoredAtom3278 chi ∧
      ¬Fin15AnchoredAtom3418 chi ∧
      ¬Fin15AnchoredAtom3739 chi ∧
      ¬Fin15AnchoredAtom3741 chi ∧
      ¬Fin15AnchoredAtom3752 chi ∧
      ¬Fin15AnchoredAtom3773 chi ∧
      ¬Fin15AnchoredAtom3913 chi ∧
      ¬Fin15AnchoredAtom4453 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 6, 7, 9, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask02775
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1833 Fin15AnchoredAtom1834 Fin15AnchoredAtom1836
    Fin15AnchoredAtom1838 Fin15AnchoredAtom1851 Fin15AnchoredAtom1853 Fin15AnchoredAtom1855
    Fin15AnchoredAtom1860 Fin15AnchoredAtom1862 Fin15AnchoredAtom1873 Fin15AnchoredAtom1951
    Fin15AnchoredAtom1953 Fin15AnchoredAtom1955 Fin15AnchoredAtom1960 Fin15AnchoredAtom1962
    Fin15AnchoredAtom1973 Fin15AnchoredAtom2024 Fin15AnchoredAtom2026 Fin15AnchoredAtom2037
    Fin15AnchoredAtom2058 Fin15AnchoredAtom2171 Fin15AnchoredAtom2173 Fin15AnchoredAtom2175
    Fin15AnchoredAtom2180 Fin15AnchoredAtom2182 Fin15AnchoredAtom2193 Fin15AnchoredAtom2244
    Fin15AnchoredAtom2246 Fin15AnchoredAtom2257 Fin15AnchoredAtom2278 Fin15AnchoredAtom2529
    Fin15AnchoredAtom2531 Fin15AnchoredAtom2542 Fin15AnchoredAtom2563 Fin15AnchoredAtom2703
    Fin15AnchoredAtom2886 Fin15AnchoredAtom2888 Fin15AnchoredAtom2890 Fin15AnchoredAtom2895
    Fin15AnchoredAtom2897 Fin15AnchoredAtom2908 Fin15AnchoredAtom2959 Fin15AnchoredAtom2961
    Fin15AnchoredAtom2972 Fin15AnchoredAtom2993 Fin15AnchoredAtom3244 Fin15AnchoredAtom3246
    Fin15AnchoredAtom3257 Fin15AnchoredAtom3278 Fin15AnchoredAtom3418 Fin15AnchoredAtom3739
    Fin15AnchoredAtom3741 Fin15AnchoredAtom3752 Fin15AnchoredAtom3773 Fin15AnchoredAtom3913
    Fin15AnchoredAtom4453 at hbad
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

theorem fin15Anchored_clause30670 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom2024 chi ∧
      ¬Fin15AnchoredAtom2027 chi ∧
      ¬Fin15AnchoredAtom2038 chi ∧
      ¬Fin15AnchoredAtom2059 chi ∧
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
      ¬Fin15AnchoredAtom2529 chi ∧
      ¬Fin15AnchoredAtom2532 chi ∧
      ¬Fin15AnchoredAtom2543 chi ∧
      ¬Fin15AnchoredAtom2564 chi ∧
      ¬Fin15AnchoredAtom2704 chi ∧
      ¬Fin15AnchoredAtom2886 chi ∧
      ¬Fin15AnchoredAtom2888 chi ∧
      ¬Fin15AnchoredAtom2891 chi ∧
      ¬Fin15AnchoredAtom2895 chi ∧
      ¬Fin15AnchoredAtom2898 chi ∧
      ¬Fin15AnchoredAtom2909 chi ∧
      ¬Fin15AnchoredAtom2959 chi ∧
      ¬Fin15AnchoredAtom2962 chi ∧
      ¬Fin15AnchoredAtom2973 chi ∧
      ¬Fin15AnchoredAtom2994 chi ∧
      ¬Fin15AnchoredAtom3244 chi ∧
      ¬Fin15AnchoredAtom3247 chi ∧
      ¬Fin15AnchoredAtom3258 chi ∧
      ¬Fin15AnchoredAtom3279 chi ∧
      ¬Fin15AnchoredAtom3419 chi ∧
      ¬Fin15AnchoredAtom3739 chi ∧
      ¬Fin15AnchoredAtom3742 chi ∧
      ¬Fin15AnchoredAtom3753 chi ∧
      ¬Fin15AnchoredAtom3774 chi ∧
      ¬Fin15AnchoredAtom3914 chi ∧
      ¬Fin15AnchoredAtom4454 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 6, 7, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask04823
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1833 Fin15AnchoredAtom1834 Fin15AnchoredAtom1836
    Fin15AnchoredAtom1839 Fin15AnchoredAtom1851 Fin15AnchoredAtom1853 Fin15AnchoredAtom1856
    Fin15AnchoredAtom1860 Fin15AnchoredAtom1863 Fin15AnchoredAtom1874 Fin15AnchoredAtom1951
    Fin15AnchoredAtom1953 Fin15AnchoredAtom1956 Fin15AnchoredAtom1960 Fin15AnchoredAtom1963
    Fin15AnchoredAtom1974 Fin15AnchoredAtom2024 Fin15AnchoredAtom2027 Fin15AnchoredAtom2038
    Fin15AnchoredAtom2059 Fin15AnchoredAtom2171 Fin15AnchoredAtom2173 Fin15AnchoredAtom2176
    Fin15AnchoredAtom2180 Fin15AnchoredAtom2183 Fin15AnchoredAtom2194 Fin15AnchoredAtom2244
    Fin15AnchoredAtom2247 Fin15AnchoredAtom2258 Fin15AnchoredAtom2279 Fin15AnchoredAtom2529
    Fin15AnchoredAtom2532 Fin15AnchoredAtom2543 Fin15AnchoredAtom2564 Fin15AnchoredAtom2704
    Fin15AnchoredAtom2886 Fin15AnchoredAtom2888 Fin15AnchoredAtom2891 Fin15AnchoredAtom2895
    Fin15AnchoredAtom2898 Fin15AnchoredAtom2909 Fin15AnchoredAtom2959 Fin15AnchoredAtom2962
    Fin15AnchoredAtom2973 Fin15AnchoredAtom2994 Fin15AnchoredAtom3244 Fin15AnchoredAtom3247
    Fin15AnchoredAtom3258 Fin15AnchoredAtom3279 Fin15AnchoredAtom3419 Fin15AnchoredAtom3739
    Fin15AnchoredAtom3742 Fin15AnchoredAtom3753 Fin15AnchoredAtom3774 Fin15AnchoredAtom3914
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

theorem fin15Anchored_clause30671 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom2024 chi ∧
      ¬Fin15AnchoredAtom2028 chi ∧
      ¬Fin15AnchoredAtom2039 chi ∧
      ¬Fin15AnchoredAtom2060 chi ∧
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
      ¬Fin15AnchoredAtom2529 chi ∧
      ¬Fin15AnchoredAtom2533 chi ∧
      ¬Fin15AnchoredAtom2544 chi ∧
      ¬Fin15AnchoredAtom2565 chi ∧
      ¬Fin15AnchoredAtom2705 chi ∧
      ¬Fin15AnchoredAtom2886 chi ∧
      ¬Fin15AnchoredAtom2888 chi ∧
      ¬Fin15AnchoredAtom2892 chi ∧
      ¬Fin15AnchoredAtom2895 chi ∧
      ¬Fin15AnchoredAtom2899 chi ∧
      ¬Fin15AnchoredAtom2910 chi ∧
      ¬Fin15AnchoredAtom2959 chi ∧
      ¬Fin15AnchoredAtom2963 chi ∧
      ¬Fin15AnchoredAtom2974 chi ∧
      ¬Fin15AnchoredAtom2995 chi ∧
      ¬Fin15AnchoredAtom3244 chi ∧
      ¬Fin15AnchoredAtom3248 chi ∧
      ¬Fin15AnchoredAtom3259 chi ∧
      ¬Fin15AnchoredAtom3280 chi ∧
      ¬Fin15AnchoredAtom3420 chi ∧
      ¬Fin15AnchoredAtom3739 chi ∧
      ¬Fin15AnchoredAtom3743 chi ∧
      ¬Fin15AnchoredAtom3754 chi ∧
      ¬Fin15AnchoredAtom3775 chi ∧
      ¬Fin15AnchoredAtom3915 chi ∧
      ¬Fin15AnchoredAtom4455 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 6, 7, 9, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask08919
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1833 Fin15AnchoredAtom1834 Fin15AnchoredAtom1836
    Fin15AnchoredAtom1840 Fin15AnchoredAtom1851 Fin15AnchoredAtom1853 Fin15AnchoredAtom1857
    Fin15AnchoredAtom1860 Fin15AnchoredAtom1864 Fin15AnchoredAtom1875 Fin15AnchoredAtom1951
    Fin15AnchoredAtom1953 Fin15AnchoredAtom1957 Fin15AnchoredAtom1960 Fin15AnchoredAtom1964
    Fin15AnchoredAtom1975 Fin15AnchoredAtom2024 Fin15AnchoredAtom2028 Fin15AnchoredAtom2039
    Fin15AnchoredAtom2060 Fin15AnchoredAtom2171 Fin15AnchoredAtom2173 Fin15AnchoredAtom2177
    Fin15AnchoredAtom2180 Fin15AnchoredAtom2184 Fin15AnchoredAtom2195 Fin15AnchoredAtom2244
    Fin15AnchoredAtom2248 Fin15AnchoredAtom2259 Fin15AnchoredAtom2280 Fin15AnchoredAtom2529
    Fin15AnchoredAtom2533 Fin15AnchoredAtom2544 Fin15AnchoredAtom2565 Fin15AnchoredAtom2705
    Fin15AnchoredAtom2886 Fin15AnchoredAtom2888 Fin15AnchoredAtom2892 Fin15AnchoredAtom2895
    Fin15AnchoredAtom2899 Fin15AnchoredAtom2910 Fin15AnchoredAtom2959 Fin15AnchoredAtom2963
    Fin15AnchoredAtom2974 Fin15AnchoredAtom2995 Fin15AnchoredAtom3244 Fin15AnchoredAtom3248
    Fin15AnchoredAtom3259 Fin15AnchoredAtom3280 Fin15AnchoredAtom3420 Fin15AnchoredAtom3739
    Fin15AnchoredAtom3743 Fin15AnchoredAtom3754 Fin15AnchoredAtom3775 Fin15AnchoredAtom3915
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

theorem fin15Anchored_clause30672 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom1976 chi ∧
      ¬Fin15AnchoredAtom2024 chi ∧
      ¬Fin15AnchoredAtom2029 chi ∧
      ¬Fin15AnchoredAtom2040 chi ∧
      ¬Fin15AnchoredAtom2061 chi ∧
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
      ¬Fin15AnchoredAtom2529 chi ∧
      ¬Fin15AnchoredAtom2534 chi ∧
      ¬Fin15AnchoredAtom2545 chi ∧
      ¬Fin15AnchoredAtom2566 chi ∧
      ¬Fin15AnchoredAtom2706 chi ∧
      ¬Fin15AnchoredAtom2886 chi ∧
      ¬Fin15AnchoredAtom2888 chi ∧
      ¬Fin15AnchoredAtom2893 chi ∧
      ¬Fin15AnchoredAtom2895 chi ∧
      ¬Fin15AnchoredAtom2900 chi ∧
      ¬Fin15AnchoredAtom2911 chi ∧
      ¬Fin15AnchoredAtom2959 chi ∧
      ¬Fin15AnchoredAtom2964 chi ∧
      ¬Fin15AnchoredAtom2975 chi ∧
      ¬Fin15AnchoredAtom2996 chi ∧
      ¬Fin15AnchoredAtom3244 chi ∧
      ¬Fin15AnchoredAtom3249 chi ∧
      ¬Fin15AnchoredAtom3260 chi ∧
      ¬Fin15AnchoredAtom3281 chi ∧
      ¬Fin15AnchoredAtom3421 chi ∧
      ¬Fin15AnchoredAtom3739 chi ∧
      ¬Fin15AnchoredAtom3744 chi ∧
      ¬Fin15AnchoredAtom3755 chi ∧
      ¬Fin15AnchoredAtom3776 chi ∧
      ¬Fin15AnchoredAtom3916 chi ∧
      ¬Fin15AnchoredAtom4456 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 6, 7, 9, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17111
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1833 Fin15AnchoredAtom1834 Fin15AnchoredAtom1836
    Fin15AnchoredAtom1841 Fin15AnchoredAtom1851 Fin15AnchoredAtom1853 Fin15AnchoredAtom1858
    Fin15AnchoredAtom1860 Fin15AnchoredAtom1865 Fin15AnchoredAtom1876 Fin15AnchoredAtom1951
    Fin15AnchoredAtom1953 Fin15AnchoredAtom1958 Fin15AnchoredAtom1960 Fin15AnchoredAtom1965
    Fin15AnchoredAtom1976 Fin15AnchoredAtom2024 Fin15AnchoredAtom2029 Fin15AnchoredAtom2040
    Fin15AnchoredAtom2061 Fin15AnchoredAtom2171 Fin15AnchoredAtom2173 Fin15AnchoredAtom2178
    Fin15AnchoredAtom2180 Fin15AnchoredAtom2185 Fin15AnchoredAtom2196 Fin15AnchoredAtom2244
    Fin15AnchoredAtom2249 Fin15AnchoredAtom2260 Fin15AnchoredAtom2281 Fin15AnchoredAtom2529
    Fin15AnchoredAtom2534 Fin15AnchoredAtom2545 Fin15AnchoredAtom2566 Fin15AnchoredAtom2706
    Fin15AnchoredAtom2886 Fin15AnchoredAtom2888 Fin15AnchoredAtom2893 Fin15AnchoredAtom2895
    Fin15AnchoredAtom2900 Fin15AnchoredAtom2911 Fin15AnchoredAtom2959 Fin15AnchoredAtom2964
    Fin15AnchoredAtom2975 Fin15AnchoredAtom2996 Fin15AnchoredAtom3244 Fin15AnchoredAtom3249
    Fin15AnchoredAtom3260 Fin15AnchoredAtom3281 Fin15AnchoredAtom3421 Fin15AnchoredAtom3739
    Fin15AnchoredAtom3744 Fin15AnchoredAtom3755 Fin15AnchoredAtom3776 Fin15AnchoredAtom3916
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

theorem fin15Anchored_clause30673 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom1978 chi ∧
      ¬Fin15AnchoredAtom2025 chi ∧
      ¬Fin15AnchoredAtom2027 chi ∧
      ¬Fin15AnchoredAtom2042 chi ∧
      ¬Fin15AnchoredAtom2063 chi ∧
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
      ¬Fin15AnchoredAtom2530 chi ∧
      ¬Fin15AnchoredAtom2532 chi ∧
      ¬Fin15AnchoredAtom2547 chi ∧
      ¬Fin15AnchoredAtom2568 chi ∧
      ¬Fin15AnchoredAtom2708 chi ∧
      ¬Fin15AnchoredAtom2886 chi ∧
      ¬Fin15AnchoredAtom2889 chi ∧
      ¬Fin15AnchoredAtom2891 chi ∧
      ¬Fin15AnchoredAtom2896 chi ∧
      ¬Fin15AnchoredAtom2898 chi ∧
      ¬Fin15AnchoredAtom2913 chi ∧
      ¬Fin15AnchoredAtom2960 chi ∧
      ¬Fin15AnchoredAtom2962 chi ∧
      ¬Fin15AnchoredAtom2977 chi ∧
      ¬Fin15AnchoredAtom2998 chi ∧
      ¬Fin15AnchoredAtom3245 chi ∧
      ¬Fin15AnchoredAtom3247 chi ∧
      ¬Fin15AnchoredAtom3262 chi ∧
      ¬Fin15AnchoredAtom3283 chi ∧
      ¬Fin15AnchoredAtom3423 chi ∧
      ¬Fin15AnchoredAtom3740 chi ∧
      ¬Fin15AnchoredAtom3742 chi ∧
      ¬Fin15AnchoredAtom3757 chi ∧
      ¬Fin15AnchoredAtom3778 chi ∧
      ¬Fin15AnchoredAtom3918 chi ∧
      ¬Fin15AnchoredAtom4458 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 6, 7, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05335
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1833 Fin15AnchoredAtom1834 Fin15AnchoredAtom1837
    Fin15AnchoredAtom1839 Fin15AnchoredAtom1851 Fin15AnchoredAtom1854 Fin15AnchoredAtom1856
    Fin15AnchoredAtom1861 Fin15AnchoredAtom1863 Fin15AnchoredAtom1878 Fin15AnchoredAtom1951
    Fin15AnchoredAtom1954 Fin15AnchoredAtom1956 Fin15AnchoredAtom1961 Fin15AnchoredAtom1963
    Fin15AnchoredAtom1978 Fin15AnchoredAtom2025 Fin15AnchoredAtom2027 Fin15AnchoredAtom2042
    Fin15AnchoredAtom2063 Fin15AnchoredAtom2171 Fin15AnchoredAtom2174 Fin15AnchoredAtom2176
    Fin15AnchoredAtom2181 Fin15AnchoredAtom2183 Fin15AnchoredAtom2198 Fin15AnchoredAtom2245
    Fin15AnchoredAtom2247 Fin15AnchoredAtom2262 Fin15AnchoredAtom2283 Fin15AnchoredAtom2530
    Fin15AnchoredAtom2532 Fin15AnchoredAtom2547 Fin15AnchoredAtom2568 Fin15AnchoredAtom2708
    Fin15AnchoredAtom2886 Fin15AnchoredAtom2889 Fin15AnchoredAtom2891 Fin15AnchoredAtom2896
    Fin15AnchoredAtom2898 Fin15AnchoredAtom2913 Fin15AnchoredAtom2960 Fin15AnchoredAtom2962
    Fin15AnchoredAtom2977 Fin15AnchoredAtom2998 Fin15AnchoredAtom3245 Fin15AnchoredAtom3247
    Fin15AnchoredAtom3262 Fin15AnchoredAtom3283 Fin15AnchoredAtom3423 Fin15AnchoredAtom3740
    Fin15AnchoredAtom3742 Fin15AnchoredAtom3757 Fin15AnchoredAtom3778 Fin15AnchoredAtom3918
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

theorem fin15Anchored_clause30674 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom1979 chi ∧
      ¬Fin15AnchoredAtom2025 chi ∧
      ¬Fin15AnchoredAtom2028 chi ∧
      ¬Fin15AnchoredAtom2043 chi ∧
      ¬Fin15AnchoredAtom2064 chi ∧
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
      ¬Fin15AnchoredAtom2530 chi ∧
      ¬Fin15AnchoredAtom2533 chi ∧
      ¬Fin15AnchoredAtom2548 chi ∧
      ¬Fin15AnchoredAtom2569 chi ∧
      ¬Fin15AnchoredAtom2709 chi ∧
      ¬Fin15AnchoredAtom2886 chi ∧
      ¬Fin15AnchoredAtom2889 chi ∧
      ¬Fin15AnchoredAtom2892 chi ∧
      ¬Fin15AnchoredAtom2896 chi ∧
      ¬Fin15AnchoredAtom2899 chi ∧
      ¬Fin15AnchoredAtom2914 chi ∧
      ¬Fin15AnchoredAtom2960 chi ∧
      ¬Fin15AnchoredAtom2963 chi ∧
      ¬Fin15AnchoredAtom2978 chi ∧
      ¬Fin15AnchoredAtom2999 chi ∧
      ¬Fin15AnchoredAtom3245 chi ∧
      ¬Fin15AnchoredAtom3248 chi ∧
      ¬Fin15AnchoredAtom3263 chi ∧
      ¬Fin15AnchoredAtom3284 chi ∧
      ¬Fin15AnchoredAtom3424 chi ∧
      ¬Fin15AnchoredAtom3740 chi ∧
      ¬Fin15AnchoredAtom3743 chi ∧
      ¬Fin15AnchoredAtom3758 chi ∧
      ¬Fin15AnchoredAtom3779 chi ∧
      ¬Fin15AnchoredAtom3919 chi ∧
      ¬Fin15AnchoredAtom4459 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 6, 7, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09431
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1833 Fin15AnchoredAtom1834 Fin15AnchoredAtom1837
    Fin15AnchoredAtom1840 Fin15AnchoredAtom1851 Fin15AnchoredAtom1854 Fin15AnchoredAtom1857
    Fin15AnchoredAtom1861 Fin15AnchoredAtom1864 Fin15AnchoredAtom1879 Fin15AnchoredAtom1951
    Fin15AnchoredAtom1954 Fin15AnchoredAtom1957 Fin15AnchoredAtom1961 Fin15AnchoredAtom1964
    Fin15AnchoredAtom1979 Fin15AnchoredAtom2025 Fin15AnchoredAtom2028 Fin15AnchoredAtom2043
    Fin15AnchoredAtom2064 Fin15AnchoredAtom2171 Fin15AnchoredAtom2174 Fin15AnchoredAtom2177
    Fin15AnchoredAtom2181 Fin15AnchoredAtom2184 Fin15AnchoredAtom2199 Fin15AnchoredAtom2245
    Fin15AnchoredAtom2248 Fin15AnchoredAtom2263 Fin15AnchoredAtom2284 Fin15AnchoredAtom2530
    Fin15AnchoredAtom2533 Fin15AnchoredAtom2548 Fin15AnchoredAtom2569 Fin15AnchoredAtom2709
    Fin15AnchoredAtom2886 Fin15AnchoredAtom2889 Fin15AnchoredAtom2892 Fin15AnchoredAtom2896
    Fin15AnchoredAtom2899 Fin15AnchoredAtom2914 Fin15AnchoredAtom2960 Fin15AnchoredAtom2963
    Fin15AnchoredAtom2978 Fin15AnchoredAtom2999 Fin15AnchoredAtom3245 Fin15AnchoredAtom3248
    Fin15AnchoredAtom3263 Fin15AnchoredAtom3284 Fin15AnchoredAtom3424 Fin15AnchoredAtom3740
    Fin15AnchoredAtom3743 Fin15AnchoredAtom3758 Fin15AnchoredAtom3779 Fin15AnchoredAtom3919
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

theorem fin15Anchored_clause30675 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom1980 chi ∧
      ¬Fin15AnchoredAtom2025 chi ∧
      ¬Fin15AnchoredAtom2029 chi ∧
      ¬Fin15AnchoredAtom2044 chi ∧
      ¬Fin15AnchoredAtom2065 chi ∧
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
      ¬Fin15AnchoredAtom2530 chi ∧
      ¬Fin15AnchoredAtom2534 chi ∧
      ¬Fin15AnchoredAtom2549 chi ∧
      ¬Fin15AnchoredAtom2570 chi ∧
      ¬Fin15AnchoredAtom2710 chi ∧
      ¬Fin15AnchoredAtom2886 chi ∧
      ¬Fin15AnchoredAtom2889 chi ∧
      ¬Fin15AnchoredAtom2893 chi ∧
      ¬Fin15AnchoredAtom2896 chi ∧
      ¬Fin15AnchoredAtom2900 chi ∧
      ¬Fin15AnchoredAtom2915 chi ∧
      ¬Fin15AnchoredAtom2960 chi ∧
      ¬Fin15AnchoredAtom2964 chi ∧
      ¬Fin15AnchoredAtom2979 chi ∧
      ¬Fin15AnchoredAtom3000 chi ∧
      ¬Fin15AnchoredAtom3245 chi ∧
      ¬Fin15AnchoredAtom3249 chi ∧
      ¬Fin15AnchoredAtom3264 chi ∧
      ¬Fin15AnchoredAtom3285 chi ∧
      ¬Fin15AnchoredAtom3425 chi ∧
      ¬Fin15AnchoredAtom3740 chi ∧
      ¬Fin15AnchoredAtom3744 chi ∧
      ¬Fin15AnchoredAtom3759 chi ∧
      ¬Fin15AnchoredAtom3780 chi ∧
      ¬Fin15AnchoredAtom3920 chi ∧
      ¬Fin15AnchoredAtom4460 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 6, 7, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17623
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1833 Fin15AnchoredAtom1834 Fin15AnchoredAtom1837
    Fin15AnchoredAtom1841 Fin15AnchoredAtom1851 Fin15AnchoredAtom1854 Fin15AnchoredAtom1858
    Fin15AnchoredAtom1861 Fin15AnchoredAtom1865 Fin15AnchoredAtom1880 Fin15AnchoredAtom1951
    Fin15AnchoredAtom1954 Fin15AnchoredAtom1958 Fin15AnchoredAtom1961 Fin15AnchoredAtom1965
    Fin15AnchoredAtom1980 Fin15AnchoredAtom2025 Fin15AnchoredAtom2029 Fin15AnchoredAtom2044
    Fin15AnchoredAtom2065 Fin15AnchoredAtom2171 Fin15AnchoredAtom2174 Fin15AnchoredAtom2178
    Fin15AnchoredAtom2181 Fin15AnchoredAtom2185 Fin15AnchoredAtom2200 Fin15AnchoredAtom2245
    Fin15AnchoredAtom2249 Fin15AnchoredAtom2264 Fin15AnchoredAtom2285 Fin15AnchoredAtom2530
    Fin15AnchoredAtom2534 Fin15AnchoredAtom2549 Fin15AnchoredAtom2570 Fin15AnchoredAtom2710
    Fin15AnchoredAtom2886 Fin15AnchoredAtom2889 Fin15AnchoredAtom2893 Fin15AnchoredAtom2896
    Fin15AnchoredAtom2900 Fin15AnchoredAtom2915 Fin15AnchoredAtom2960 Fin15AnchoredAtom2964
    Fin15AnchoredAtom2979 Fin15AnchoredAtom3000 Fin15AnchoredAtom3245 Fin15AnchoredAtom3249
    Fin15AnchoredAtom3264 Fin15AnchoredAtom3285 Fin15AnchoredAtom3425 Fin15AnchoredAtom3740
    Fin15AnchoredAtom3744 Fin15AnchoredAtom3759 Fin15AnchoredAtom3780 Fin15AnchoredAtom3920
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

theorem fin15Anchored_clause30676 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1838 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1855 chi ∧
      ¬Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom1862 chi ∧
      ¬Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom1881 chi ∧
      ¬Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom1955 chi ∧
      ¬Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom1962 chi ∧
      ¬Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom1981 chi ∧
      ¬Fin15AnchoredAtom2026 chi ∧
      ¬Fin15AnchoredAtom2027 chi ∧
      ¬Fin15AnchoredAtom2045 chi ∧
      ¬Fin15AnchoredAtom2066 chi ∧
      ¬Fin15AnchoredAtom2171 chi ∧
      ¬Fin15AnchoredAtom2175 chi ∧
      ¬Fin15AnchoredAtom2176 chi ∧
      ¬Fin15AnchoredAtom2182 chi ∧
      ¬Fin15AnchoredAtom2183 chi ∧
      ¬Fin15AnchoredAtom2201 chi ∧
      ¬Fin15AnchoredAtom2246 chi ∧
      ¬Fin15AnchoredAtom2247 chi ∧
      ¬Fin15AnchoredAtom2265 chi ∧
      ¬Fin15AnchoredAtom2286 chi ∧
      ¬Fin15AnchoredAtom2531 chi ∧
      ¬Fin15AnchoredAtom2532 chi ∧
      ¬Fin15AnchoredAtom2550 chi ∧
      ¬Fin15AnchoredAtom2571 chi ∧
      ¬Fin15AnchoredAtom2711 chi ∧
      ¬Fin15AnchoredAtom2886 chi ∧
      ¬Fin15AnchoredAtom2890 chi ∧
      ¬Fin15AnchoredAtom2891 chi ∧
      ¬Fin15AnchoredAtom2897 chi ∧
      ¬Fin15AnchoredAtom2898 chi ∧
      ¬Fin15AnchoredAtom2916 chi ∧
      ¬Fin15AnchoredAtom2961 chi ∧
      ¬Fin15AnchoredAtom2962 chi ∧
      ¬Fin15AnchoredAtom2980 chi ∧
      ¬Fin15AnchoredAtom3001 chi ∧
      ¬Fin15AnchoredAtom3246 chi ∧
      ¬Fin15AnchoredAtom3247 chi ∧
      ¬Fin15AnchoredAtom3265 chi ∧
      ¬Fin15AnchoredAtom3286 chi ∧
      ¬Fin15AnchoredAtom3426 chi ∧
      ¬Fin15AnchoredAtom3741 chi ∧
      ¬Fin15AnchoredAtom3742 chi ∧
      ¬Fin15AnchoredAtom3760 chi ∧
      ¬Fin15AnchoredAtom3781 chi ∧
      ¬Fin15AnchoredAtom3921 chi ∧
      ¬Fin15AnchoredAtom4461 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 6, 7, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask06359
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1833 Fin15AnchoredAtom1834 Fin15AnchoredAtom1838
    Fin15AnchoredAtom1839 Fin15AnchoredAtom1851 Fin15AnchoredAtom1855 Fin15AnchoredAtom1856
    Fin15AnchoredAtom1862 Fin15AnchoredAtom1863 Fin15AnchoredAtom1881 Fin15AnchoredAtom1951
    Fin15AnchoredAtom1955 Fin15AnchoredAtom1956 Fin15AnchoredAtom1962 Fin15AnchoredAtom1963
    Fin15AnchoredAtom1981 Fin15AnchoredAtom2026 Fin15AnchoredAtom2027 Fin15AnchoredAtom2045
    Fin15AnchoredAtom2066 Fin15AnchoredAtom2171 Fin15AnchoredAtom2175 Fin15AnchoredAtom2176
    Fin15AnchoredAtom2182 Fin15AnchoredAtom2183 Fin15AnchoredAtom2201 Fin15AnchoredAtom2246
    Fin15AnchoredAtom2247 Fin15AnchoredAtom2265 Fin15AnchoredAtom2286 Fin15AnchoredAtom2531
    Fin15AnchoredAtom2532 Fin15AnchoredAtom2550 Fin15AnchoredAtom2571 Fin15AnchoredAtom2711
    Fin15AnchoredAtom2886 Fin15AnchoredAtom2890 Fin15AnchoredAtom2891 Fin15AnchoredAtom2897
    Fin15AnchoredAtom2898 Fin15AnchoredAtom2916 Fin15AnchoredAtom2961 Fin15AnchoredAtom2962
    Fin15AnchoredAtom2980 Fin15AnchoredAtom3001 Fin15AnchoredAtom3246 Fin15AnchoredAtom3247
    Fin15AnchoredAtom3265 Fin15AnchoredAtom3286 Fin15AnchoredAtom3426 Fin15AnchoredAtom3741
    Fin15AnchoredAtom3742 Fin15AnchoredAtom3760 Fin15AnchoredAtom3781 Fin15AnchoredAtom3921
    Fin15AnchoredAtom4461 at hbad
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

theorem fin15Anchored_clause30677 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom1984 chi ∧
      ¬Fin15AnchoredAtom2027 chi ∧
      ¬Fin15AnchoredAtom2028 chi ∧
      ¬Fin15AnchoredAtom2048 chi ∧
      ¬Fin15AnchoredAtom2069 chi ∧
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
      ¬Fin15AnchoredAtom2532 chi ∧
      ¬Fin15AnchoredAtom2533 chi ∧
      ¬Fin15AnchoredAtom2553 chi ∧
      ¬Fin15AnchoredAtom2574 chi ∧
      ¬Fin15AnchoredAtom2714 chi ∧
      ¬Fin15AnchoredAtom2886 chi ∧
      ¬Fin15AnchoredAtom2891 chi ∧
      ¬Fin15AnchoredAtom2892 chi ∧
      ¬Fin15AnchoredAtom2898 chi ∧
      ¬Fin15AnchoredAtom2899 chi ∧
      ¬Fin15AnchoredAtom2919 chi ∧
      ¬Fin15AnchoredAtom2962 chi ∧
      ¬Fin15AnchoredAtom2963 chi ∧
      ¬Fin15AnchoredAtom2983 chi ∧
      ¬Fin15AnchoredAtom3004 chi ∧
      ¬Fin15AnchoredAtom3247 chi ∧
      ¬Fin15AnchoredAtom3248 chi ∧
      ¬Fin15AnchoredAtom3268 chi ∧
      ¬Fin15AnchoredAtom3289 chi ∧
      ¬Fin15AnchoredAtom3429 chi ∧
      ¬Fin15AnchoredAtom3742 chi ∧
      ¬Fin15AnchoredAtom3743 chi ∧
      ¬Fin15AnchoredAtom3763 chi ∧
      ¬Fin15AnchoredAtom3784 chi ∧
      ¬Fin15AnchoredAtom3924 chi ∧
      ¬Fin15AnchoredAtom4464 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 6, 7, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask12503
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1833 Fin15AnchoredAtom1834 Fin15AnchoredAtom1839
    Fin15AnchoredAtom1840 Fin15AnchoredAtom1851 Fin15AnchoredAtom1856 Fin15AnchoredAtom1857
    Fin15AnchoredAtom1863 Fin15AnchoredAtom1864 Fin15AnchoredAtom1884 Fin15AnchoredAtom1951
    Fin15AnchoredAtom1956 Fin15AnchoredAtom1957 Fin15AnchoredAtom1963 Fin15AnchoredAtom1964
    Fin15AnchoredAtom1984 Fin15AnchoredAtom2027 Fin15AnchoredAtom2028 Fin15AnchoredAtom2048
    Fin15AnchoredAtom2069 Fin15AnchoredAtom2171 Fin15AnchoredAtom2176 Fin15AnchoredAtom2177
    Fin15AnchoredAtom2183 Fin15AnchoredAtom2184 Fin15AnchoredAtom2204 Fin15AnchoredAtom2247
    Fin15AnchoredAtom2248 Fin15AnchoredAtom2268 Fin15AnchoredAtom2289 Fin15AnchoredAtom2532
    Fin15AnchoredAtom2533 Fin15AnchoredAtom2553 Fin15AnchoredAtom2574 Fin15AnchoredAtom2714
    Fin15AnchoredAtom2886 Fin15AnchoredAtom2891 Fin15AnchoredAtom2892 Fin15AnchoredAtom2898
    Fin15AnchoredAtom2899 Fin15AnchoredAtom2919 Fin15AnchoredAtom2962 Fin15AnchoredAtom2963
    Fin15AnchoredAtom2983 Fin15AnchoredAtom3004 Fin15AnchoredAtom3247 Fin15AnchoredAtom3248
    Fin15AnchoredAtom3268 Fin15AnchoredAtom3289 Fin15AnchoredAtom3429 Fin15AnchoredAtom3742
    Fin15AnchoredAtom3743 Fin15AnchoredAtom3763 Fin15AnchoredAtom3784 Fin15AnchoredAtom3924
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

theorem fin15Anchored_clause30678 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom1985 chi ∧
      ¬Fin15AnchoredAtom2027 chi ∧
      ¬Fin15AnchoredAtom2029 chi ∧
      ¬Fin15AnchoredAtom2049 chi ∧
      ¬Fin15AnchoredAtom2070 chi ∧
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
      ¬Fin15AnchoredAtom2532 chi ∧
      ¬Fin15AnchoredAtom2534 chi ∧
      ¬Fin15AnchoredAtom2554 chi ∧
      ¬Fin15AnchoredAtom2575 chi ∧
      ¬Fin15AnchoredAtom2715 chi ∧
      ¬Fin15AnchoredAtom2886 chi ∧
      ¬Fin15AnchoredAtom2891 chi ∧
      ¬Fin15AnchoredAtom2893 chi ∧
      ¬Fin15AnchoredAtom2898 chi ∧
      ¬Fin15AnchoredAtom2900 chi ∧
      ¬Fin15AnchoredAtom2920 chi ∧
      ¬Fin15AnchoredAtom2962 chi ∧
      ¬Fin15AnchoredAtom2964 chi ∧
      ¬Fin15AnchoredAtom2984 chi ∧
      ¬Fin15AnchoredAtom3005 chi ∧
      ¬Fin15AnchoredAtom3247 chi ∧
      ¬Fin15AnchoredAtom3249 chi ∧
      ¬Fin15AnchoredAtom3269 chi ∧
      ¬Fin15AnchoredAtom3290 chi ∧
      ¬Fin15AnchoredAtom3430 chi ∧
      ¬Fin15AnchoredAtom3742 chi ∧
      ¬Fin15AnchoredAtom3744 chi ∧
      ¬Fin15AnchoredAtom3764 chi ∧
      ¬Fin15AnchoredAtom3785 chi ∧
      ¬Fin15AnchoredAtom3925 chi ∧
      ¬Fin15AnchoredAtom4465 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 6, 7, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask20695
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1833 Fin15AnchoredAtom1834 Fin15AnchoredAtom1839
    Fin15AnchoredAtom1841 Fin15AnchoredAtom1851 Fin15AnchoredAtom1856 Fin15AnchoredAtom1858
    Fin15AnchoredAtom1863 Fin15AnchoredAtom1865 Fin15AnchoredAtom1885 Fin15AnchoredAtom1951
    Fin15AnchoredAtom1956 Fin15AnchoredAtom1958 Fin15AnchoredAtom1963 Fin15AnchoredAtom1965
    Fin15AnchoredAtom1985 Fin15AnchoredAtom2027 Fin15AnchoredAtom2029 Fin15AnchoredAtom2049
    Fin15AnchoredAtom2070 Fin15AnchoredAtom2171 Fin15AnchoredAtom2176 Fin15AnchoredAtom2178
    Fin15AnchoredAtom2183 Fin15AnchoredAtom2185 Fin15AnchoredAtom2205 Fin15AnchoredAtom2247
    Fin15AnchoredAtom2249 Fin15AnchoredAtom2269 Fin15AnchoredAtom2290 Fin15AnchoredAtom2532
    Fin15AnchoredAtom2534 Fin15AnchoredAtom2554 Fin15AnchoredAtom2575 Fin15AnchoredAtom2715
    Fin15AnchoredAtom2886 Fin15AnchoredAtom2891 Fin15AnchoredAtom2893 Fin15AnchoredAtom2898
    Fin15AnchoredAtom2900 Fin15AnchoredAtom2920 Fin15AnchoredAtom2962 Fin15AnchoredAtom2964
    Fin15AnchoredAtom2984 Fin15AnchoredAtom3005 Fin15AnchoredAtom3247 Fin15AnchoredAtom3249
    Fin15AnchoredAtom3269 Fin15AnchoredAtom3290 Fin15AnchoredAtom3430 Fin15AnchoredAtom3742
    Fin15AnchoredAtom3744 Fin15AnchoredAtom3764 Fin15AnchoredAtom3785 Fin15AnchoredAtom3925
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

theorem fin15Anchored_clause30679 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom1886 chi ∧
      ¬Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom1986 chi ∧
      ¬Fin15AnchoredAtom2028 chi ∧
      ¬Fin15AnchoredAtom2029 chi ∧
      ¬Fin15AnchoredAtom2050 chi ∧
      ¬Fin15AnchoredAtom2071 chi ∧
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
      ¬Fin15AnchoredAtom2533 chi ∧
      ¬Fin15AnchoredAtom2534 chi ∧
      ¬Fin15AnchoredAtom2555 chi ∧
      ¬Fin15AnchoredAtom2576 chi ∧
      ¬Fin15AnchoredAtom2716 chi ∧
      ¬Fin15AnchoredAtom2886 chi ∧
      ¬Fin15AnchoredAtom2892 chi ∧
      ¬Fin15AnchoredAtom2893 chi ∧
      ¬Fin15AnchoredAtom2899 chi ∧
      ¬Fin15AnchoredAtom2900 chi ∧
      ¬Fin15AnchoredAtom2921 chi ∧
      ¬Fin15AnchoredAtom2963 chi ∧
      ¬Fin15AnchoredAtom2964 chi ∧
      ¬Fin15AnchoredAtom2985 chi ∧
      ¬Fin15AnchoredAtom3006 chi ∧
      ¬Fin15AnchoredAtom3248 chi ∧
      ¬Fin15AnchoredAtom3249 chi ∧
      ¬Fin15AnchoredAtom3270 chi ∧
      ¬Fin15AnchoredAtom3291 chi ∧
      ¬Fin15AnchoredAtom3431 chi ∧
      ¬Fin15AnchoredAtom3743 chi ∧
      ¬Fin15AnchoredAtom3744 chi ∧
      ¬Fin15AnchoredAtom3765 chi ∧
      ¬Fin15AnchoredAtom3786 chi ∧
      ¬Fin15AnchoredAtom3926 chi ∧
      ¬Fin15AnchoredAtom4466 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 6, 7, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask24791
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1833 Fin15AnchoredAtom1834 Fin15AnchoredAtom1840
    Fin15AnchoredAtom1841 Fin15AnchoredAtom1851 Fin15AnchoredAtom1857 Fin15AnchoredAtom1858
    Fin15AnchoredAtom1864 Fin15AnchoredAtom1865 Fin15AnchoredAtom1886 Fin15AnchoredAtom1951
    Fin15AnchoredAtom1957 Fin15AnchoredAtom1958 Fin15AnchoredAtom1964 Fin15AnchoredAtom1965
    Fin15AnchoredAtom1986 Fin15AnchoredAtom2028 Fin15AnchoredAtom2029 Fin15AnchoredAtom2050
    Fin15AnchoredAtom2071 Fin15AnchoredAtom2171 Fin15AnchoredAtom2177 Fin15AnchoredAtom2178
    Fin15AnchoredAtom2184 Fin15AnchoredAtom2185 Fin15AnchoredAtom2206 Fin15AnchoredAtom2248
    Fin15AnchoredAtom2249 Fin15AnchoredAtom2270 Fin15AnchoredAtom2291 Fin15AnchoredAtom2533
    Fin15AnchoredAtom2534 Fin15AnchoredAtom2555 Fin15AnchoredAtom2576 Fin15AnchoredAtom2716
    Fin15AnchoredAtom2886 Fin15AnchoredAtom2892 Fin15AnchoredAtom2893 Fin15AnchoredAtom2899
    Fin15AnchoredAtom2900 Fin15AnchoredAtom2921 Fin15AnchoredAtom2963 Fin15AnchoredAtom2964
    Fin15AnchoredAtom2985 Fin15AnchoredAtom3006 Fin15AnchoredAtom3248 Fin15AnchoredAtom3249
    Fin15AnchoredAtom3270 Fin15AnchoredAtom3291 Fin15AnchoredAtom3431 Fin15AnchoredAtom3743
    Fin15AnchoredAtom3744 Fin15AnchoredAtom3765 Fin15AnchoredAtom3786 Fin15AnchoredAtom3926
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

theorem fin15Anchored_clause30680 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom1978 chi ∧
      ¬Fin15AnchoredAtom2036 chi ∧
      ¬Fin15AnchoredAtom2038 chi ∧
      ¬Fin15AnchoredAtom2042 chi ∧
      ¬Fin15AnchoredAtom2088 chi ∧
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
      ¬Fin15AnchoredAtom2541 chi ∧
      ¬Fin15AnchoredAtom2543 chi ∧
      ¬Fin15AnchoredAtom2547 chi ∧
      ¬Fin15AnchoredAtom2593 chi ∧
      ¬Fin15AnchoredAtom2733 chi ∧
      ¬Fin15AnchoredAtom2888 chi ∧
      ¬Fin15AnchoredAtom2889 chi ∧
      ¬Fin15AnchoredAtom2891 chi ∧
      ¬Fin15AnchoredAtom2907 chi ∧
      ¬Fin15AnchoredAtom2909 chi ∧
      ¬Fin15AnchoredAtom2913 chi ∧
      ¬Fin15AnchoredAtom2971 chi ∧
      ¬Fin15AnchoredAtom2973 chi ∧
      ¬Fin15AnchoredAtom2977 chi ∧
      ¬Fin15AnchoredAtom3023 chi ∧
      ¬Fin15AnchoredAtom3256 chi ∧
      ¬Fin15AnchoredAtom3258 chi ∧
      ¬Fin15AnchoredAtom3262 chi ∧
      ¬Fin15AnchoredAtom3308 chi ∧
      ¬Fin15AnchoredAtom3448 chi ∧
      ¬Fin15AnchoredAtom3751 chi ∧
      ¬Fin15AnchoredAtom3753 chi ∧
      ¬Fin15AnchoredAtom3757 chi ∧
      ¬Fin15AnchoredAtom3803 chi ∧
      ¬Fin15AnchoredAtom3943 chi ∧
      ¬Fin15AnchoredAtom4483 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 6, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05719
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1833 Fin15AnchoredAtom1836 Fin15AnchoredAtom1837
    Fin15AnchoredAtom1839 Fin15AnchoredAtom1853 Fin15AnchoredAtom1854 Fin15AnchoredAtom1856
    Fin15AnchoredAtom1872 Fin15AnchoredAtom1874 Fin15AnchoredAtom1878 Fin15AnchoredAtom1953
    Fin15AnchoredAtom1954 Fin15AnchoredAtom1956 Fin15AnchoredAtom1972 Fin15AnchoredAtom1974
    Fin15AnchoredAtom1978 Fin15AnchoredAtom2036 Fin15AnchoredAtom2038 Fin15AnchoredAtom2042
    Fin15AnchoredAtom2088 Fin15AnchoredAtom2173 Fin15AnchoredAtom2174 Fin15AnchoredAtom2176
    Fin15AnchoredAtom2192 Fin15AnchoredAtom2194 Fin15AnchoredAtom2198 Fin15AnchoredAtom2256
    Fin15AnchoredAtom2258 Fin15AnchoredAtom2262 Fin15AnchoredAtom2308 Fin15AnchoredAtom2541
    Fin15AnchoredAtom2543 Fin15AnchoredAtom2547 Fin15AnchoredAtom2593 Fin15AnchoredAtom2733
    Fin15AnchoredAtom2888 Fin15AnchoredAtom2889 Fin15AnchoredAtom2891 Fin15AnchoredAtom2907
    Fin15AnchoredAtom2909 Fin15AnchoredAtom2913 Fin15AnchoredAtom2971 Fin15AnchoredAtom2973
    Fin15AnchoredAtom2977 Fin15AnchoredAtom3023 Fin15AnchoredAtom3256 Fin15AnchoredAtom3258
    Fin15AnchoredAtom3262 Fin15AnchoredAtom3308 Fin15AnchoredAtom3448 Fin15AnchoredAtom3751
    Fin15AnchoredAtom3753 Fin15AnchoredAtom3757 Fin15AnchoredAtom3803 Fin15AnchoredAtom3943
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

theorem fin15Anchored_clause30681 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom1979 chi ∧
      ¬Fin15AnchoredAtom2036 chi ∧
      ¬Fin15AnchoredAtom2039 chi ∧
      ¬Fin15AnchoredAtom2043 chi ∧
      ¬Fin15AnchoredAtom2089 chi ∧
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
      ¬Fin15AnchoredAtom2541 chi ∧
      ¬Fin15AnchoredAtom2544 chi ∧
      ¬Fin15AnchoredAtom2548 chi ∧
      ¬Fin15AnchoredAtom2594 chi ∧
      ¬Fin15AnchoredAtom2734 chi ∧
      ¬Fin15AnchoredAtom2888 chi ∧
      ¬Fin15AnchoredAtom2889 chi ∧
      ¬Fin15AnchoredAtom2892 chi ∧
      ¬Fin15AnchoredAtom2907 chi ∧
      ¬Fin15AnchoredAtom2910 chi ∧
      ¬Fin15AnchoredAtom2914 chi ∧
      ¬Fin15AnchoredAtom2971 chi ∧
      ¬Fin15AnchoredAtom2974 chi ∧
      ¬Fin15AnchoredAtom2978 chi ∧
      ¬Fin15AnchoredAtom3024 chi ∧
      ¬Fin15AnchoredAtom3256 chi ∧
      ¬Fin15AnchoredAtom3259 chi ∧
      ¬Fin15AnchoredAtom3263 chi ∧
      ¬Fin15AnchoredAtom3309 chi ∧
      ¬Fin15AnchoredAtom3449 chi ∧
      ¬Fin15AnchoredAtom3751 chi ∧
      ¬Fin15AnchoredAtom3754 chi ∧
      ¬Fin15AnchoredAtom3758 chi ∧
      ¬Fin15AnchoredAtom3804 chi ∧
      ¬Fin15AnchoredAtom3944 chi ∧
      ¬Fin15AnchoredAtom4484 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 6, 9, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09815
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1833 Fin15AnchoredAtom1836 Fin15AnchoredAtom1837
    Fin15AnchoredAtom1840 Fin15AnchoredAtom1853 Fin15AnchoredAtom1854 Fin15AnchoredAtom1857
    Fin15AnchoredAtom1872 Fin15AnchoredAtom1875 Fin15AnchoredAtom1879 Fin15AnchoredAtom1953
    Fin15AnchoredAtom1954 Fin15AnchoredAtom1957 Fin15AnchoredAtom1972 Fin15AnchoredAtom1975
    Fin15AnchoredAtom1979 Fin15AnchoredAtom2036 Fin15AnchoredAtom2039 Fin15AnchoredAtom2043
    Fin15AnchoredAtom2089 Fin15AnchoredAtom2173 Fin15AnchoredAtom2174 Fin15AnchoredAtom2177
    Fin15AnchoredAtom2192 Fin15AnchoredAtom2195 Fin15AnchoredAtom2199 Fin15AnchoredAtom2256
    Fin15AnchoredAtom2259 Fin15AnchoredAtom2263 Fin15AnchoredAtom2309 Fin15AnchoredAtom2541
    Fin15AnchoredAtom2544 Fin15AnchoredAtom2548 Fin15AnchoredAtom2594 Fin15AnchoredAtom2734
    Fin15AnchoredAtom2888 Fin15AnchoredAtom2889 Fin15AnchoredAtom2892 Fin15AnchoredAtom2907
    Fin15AnchoredAtom2910 Fin15AnchoredAtom2914 Fin15AnchoredAtom2971 Fin15AnchoredAtom2974
    Fin15AnchoredAtom2978 Fin15AnchoredAtom3024 Fin15AnchoredAtom3256 Fin15AnchoredAtom3259
    Fin15AnchoredAtom3263 Fin15AnchoredAtom3309 Fin15AnchoredAtom3449 Fin15AnchoredAtom3751
    Fin15AnchoredAtom3754 Fin15AnchoredAtom3758 Fin15AnchoredAtom3804 Fin15AnchoredAtom3944
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

theorem fin15Anchored_clause30682 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom1976 chi ∧
      ¬Fin15AnchoredAtom1980 chi ∧
      ¬Fin15AnchoredAtom2036 chi ∧
      ¬Fin15AnchoredAtom2040 chi ∧
      ¬Fin15AnchoredAtom2044 chi ∧
      ¬Fin15AnchoredAtom2090 chi ∧
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
      ¬Fin15AnchoredAtom2541 chi ∧
      ¬Fin15AnchoredAtom2545 chi ∧
      ¬Fin15AnchoredAtom2549 chi ∧
      ¬Fin15AnchoredAtom2595 chi ∧
      ¬Fin15AnchoredAtom2735 chi ∧
      ¬Fin15AnchoredAtom2888 chi ∧
      ¬Fin15AnchoredAtom2889 chi ∧
      ¬Fin15AnchoredAtom2893 chi ∧
      ¬Fin15AnchoredAtom2907 chi ∧
      ¬Fin15AnchoredAtom2911 chi ∧
      ¬Fin15AnchoredAtom2915 chi ∧
      ¬Fin15AnchoredAtom2971 chi ∧
      ¬Fin15AnchoredAtom2975 chi ∧
      ¬Fin15AnchoredAtom2979 chi ∧
      ¬Fin15AnchoredAtom3025 chi ∧
      ¬Fin15AnchoredAtom3256 chi ∧
      ¬Fin15AnchoredAtom3260 chi ∧
      ¬Fin15AnchoredAtom3264 chi ∧
      ¬Fin15AnchoredAtom3310 chi ∧
      ¬Fin15AnchoredAtom3450 chi ∧
      ¬Fin15AnchoredAtom3751 chi ∧
      ¬Fin15AnchoredAtom3755 chi ∧
      ¬Fin15AnchoredAtom3759 chi ∧
      ¬Fin15AnchoredAtom3805 chi ∧
      ¬Fin15AnchoredAtom3945 chi ∧
      ¬Fin15AnchoredAtom4485 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 6, 9, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask18007
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1833 Fin15AnchoredAtom1836 Fin15AnchoredAtom1837
    Fin15AnchoredAtom1841 Fin15AnchoredAtom1853 Fin15AnchoredAtom1854 Fin15AnchoredAtom1858
    Fin15AnchoredAtom1872 Fin15AnchoredAtom1876 Fin15AnchoredAtom1880 Fin15AnchoredAtom1953
    Fin15AnchoredAtom1954 Fin15AnchoredAtom1958 Fin15AnchoredAtom1972 Fin15AnchoredAtom1976
    Fin15AnchoredAtom1980 Fin15AnchoredAtom2036 Fin15AnchoredAtom2040 Fin15AnchoredAtom2044
    Fin15AnchoredAtom2090 Fin15AnchoredAtom2173 Fin15AnchoredAtom2174 Fin15AnchoredAtom2178
    Fin15AnchoredAtom2192 Fin15AnchoredAtom2196 Fin15AnchoredAtom2200 Fin15AnchoredAtom2256
    Fin15AnchoredAtom2260 Fin15AnchoredAtom2264 Fin15AnchoredAtom2310 Fin15AnchoredAtom2541
    Fin15AnchoredAtom2545 Fin15AnchoredAtom2549 Fin15AnchoredAtom2595 Fin15AnchoredAtom2735
    Fin15AnchoredAtom2888 Fin15AnchoredAtom2889 Fin15AnchoredAtom2893 Fin15AnchoredAtom2907
    Fin15AnchoredAtom2911 Fin15AnchoredAtom2915 Fin15AnchoredAtom2971 Fin15AnchoredAtom2975
    Fin15AnchoredAtom2979 Fin15AnchoredAtom3025 Fin15AnchoredAtom3256 Fin15AnchoredAtom3260
    Fin15AnchoredAtom3264 Fin15AnchoredAtom3310 Fin15AnchoredAtom3450 Fin15AnchoredAtom3751
    Fin15AnchoredAtom3755 Fin15AnchoredAtom3759 Fin15AnchoredAtom3805 Fin15AnchoredAtom3945
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

theorem fin15Anchored_clause30683 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom1984 chi ∧
      ¬Fin15AnchoredAtom2038 chi ∧
      ¬Fin15AnchoredAtom2039 chi ∧
      ¬Fin15AnchoredAtom2048 chi ∧
      ¬Fin15AnchoredAtom2094 chi ∧
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
      ¬Fin15AnchoredAtom2543 chi ∧
      ¬Fin15AnchoredAtom2544 chi ∧
      ¬Fin15AnchoredAtom2553 chi ∧
      ¬Fin15AnchoredAtom2599 chi ∧
      ¬Fin15AnchoredAtom2739 chi ∧
      ¬Fin15AnchoredAtom2888 chi ∧
      ¬Fin15AnchoredAtom2891 chi ∧
      ¬Fin15AnchoredAtom2892 chi ∧
      ¬Fin15AnchoredAtom2909 chi ∧
      ¬Fin15AnchoredAtom2910 chi ∧
      ¬Fin15AnchoredAtom2919 chi ∧
      ¬Fin15AnchoredAtom2973 chi ∧
      ¬Fin15AnchoredAtom2974 chi ∧
      ¬Fin15AnchoredAtom2983 chi ∧
      ¬Fin15AnchoredAtom3029 chi ∧
      ¬Fin15AnchoredAtom3258 chi ∧
      ¬Fin15AnchoredAtom3259 chi ∧
      ¬Fin15AnchoredAtom3268 chi ∧
      ¬Fin15AnchoredAtom3314 chi ∧
      ¬Fin15AnchoredAtom3454 chi ∧
      ¬Fin15AnchoredAtom3753 chi ∧
      ¬Fin15AnchoredAtom3754 chi ∧
      ¬Fin15AnchoredAtom3763 chi ∧
      ¬Fin15AnchoredAtom3809 chi ∧
      ¬Fin15AnchoredAtom3949 chi ∧
      ¬Fin15AnchoredAtom4489 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 6, 9, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask12887
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1833 Fin15AnchoredAtom1836 Fin15AnchoredAtom1839
    Fin15AnchoredAtom1840 Fin15AnchoredAtom1853 Fin15AnchoredAtom1856 Fin15AnchoredAtom1857
    Fin15AnchoredAtom1874 Fin15AnchoredAtom1875 Fin15AnchoredAtom1884 Fin15AnchoredAtom1953
    Fin15AnchoredAtom1956 Fin15AnchoredAtom1957 Fin15AnchoredAtom1974 Fin15AnchoredAtom1975
    Fin15AnchoredAtom1984 Fin15AnchoredAtom2038 Fin15AnchoredAtom2039 Fin15AnchoredAtom2048
    Fin15AnchoredAtom2094 Fin15AnchoredAtom2173 Fin15AnchoredAtom2176 Fin15AnchoredAtom2177
    Fin15AnchoredAtom2194 Fin15AnchoredAtom2195 Fin15AnchoredAtom2204 Fin15AnchoredAtom2258
    Fin15AnchoredAtom2259 Fin15AnchoredAtom2268 Fin15AnchoredAtom2314 Fin15AnchoredAtom2543
    Fin15AnchoredAtom2544 Fin15AnchoredAtom2553 Fin15AnchoredAtom2599 Fin15AnchoredAtom2739
    Fin15AnchoredAtom2888 Fin15AnchoredAtom2891 Fin15AnchoredAtom2892 Fin15AnchoredAtom2909
    Fin15AnchoredAtom2910 Fin15AnchoredAtom2919 Fin15AnchoredAtom2973 Fin15AnchoredAtom2974
    Fin15AnchoredAtom2983 Fin15AnchoredAtom3029 Fin15AnchoredAtom3258 Fin15AnchoredAtom3259
    Fin15AnchoredAtom3268 Fin15AnchoredAtom3314 Fin15AnchoredAtom3454 Fin15AnchoredAtom3753
    Fin15AnchoredAtom3754 Fin15AnchoredAtom3763 Fin15AnchoredAtom3809 Fin15AnchoredAtom3949
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

theorem fin15Anchored_clause30684 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom1976 chi ∧
      ¬Fin15AnchoredAtom1985 chi ∧
      ¬Fin15AnchoredAtom2038 chi ∧
      ¬Fin15AnchoredAtom2040 chi ∧
      ¬Fin15AnchoredAtom2049 chi ∧
      ¬Fin15AnchoredAtom2095 chi ∧
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
      ¬Fin15AnchoredAtom2543 chi ∧
      ¬Fin15AnchoredAtom2545 chi ∧
      ¬Fin15AnchoredAtom2554 chi ∧
      ¬Fin15AnchoredAtom2600 chi ∧
      ¬Fin15AnchoredAtom2740 chi ∧
      ¬Fin15AnchoredAtom2888 chi ∧
      ¬Fin15AnchoredAtom2891 chi ∧
      ¬Fin15AnchoredAtom2893 chi ∧
      ¬Fin15AnchoredAtom2909 chi ∧
      ¬Fin15AnchoredAtom2911 chi ∧
      ¬Fin15AnchoredAtom2920 chi ∧
      ¬Fin15AnchoredAtom2973 chi ∧
      ¬Fin15AnchoredAtom2975 chi ∧
      ¬Fin15AnchoredAtom2984 chi ∧
      ¬Fin15AnchoredAtom3030 chi ∧
      ¬Fin15AnchoredAtom3258 chi ∧
      ¬Fin15AnchoredAtom3260 chi ∧
      ¬Fin15AnchoredAtom3269 chi ∧
      ¬Fin15AnchoredAtom3315 chi ∧
      ¬Fin15AnchoredAtom3455 chi ∧
      ¬Fin15AnchoredAtom3753 chi ∧
      ¬Fin15AnchoredAtom3755 chi ∧
      ¬Fin15AnchoredAtom3764 chi ∧
      ¬Fin15AnchoredAtom3810 chi ∧
      ¬Fin15AnchoredAtom3950 chi ∧
      ¬Fin15AnchoredAtom4490 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 6, 9, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21079
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1833 Fin15AnchoredAtom1836 Fin15AnchoredAtom1839
    Fin15AnchoredAtom1841 Fin15AnchoredAtom1853 Fin15AnchoredAtom1856 Fin15AnchoredAtom1858
    Fin15AnchoredAtom1874 Fin15AnchoredAtom1876 Fin15AnchoredAtom1885 Fin15AnchoredAtom1953
    Fin15AnchoredAtom1956 Fin15AnchoredAtom1958 Fin15AnchoredAtom1974 Fin15AnchoredAtom1976
    Fin15AnchoredAtom1985 Fin15AnchoredAtom2038 Fin15AnchoredAtom2040 Fin15AnchoredAtom2049
    Fin15AnchoredAtom2095 Fin15AnchoredAtom2173 Fin15AnchoredAtom2176 Fin15AnchoredAtom2178
    Fin15AnchoredAtom2194 Fin15AnchoredAtom2196 Fin15AnchoredAtom2205 Fin15AnchoredAtom2258
    Fin15AnchoredAtom2260 Fin15AnchoredAtom2269 Fin15AnchoredAtom2315 Fin15AnchoredAtom2543
    Fin15AnchoredAtom2545 Fin15AnchoredAtom2554 Fin15AnchoredAtom2600 Fin15AnchoredAtom2740
    Fin15AnchoredAtom2888 Fin15AnchoredAtom2891 Fin15AnchoredAtom2893 Fin15AnchoredAtom2909
    Fin15AnchoredAtom2911 Fin15AnchoredAtom2920 Fin15AnchoredAtom2973 Fin15AnchoredAtom2975
    Fin15AnchoredAtom2984 Fin15AnchoredAtom3030 Fin15AnchoredAtom3258 Fin15AnchoredAtom3260
    Fin15AnchoredAtom3269 Fin15AnchoredAtom3315 Fin15AnchoredAtom3455 Fin15AnchoredAtom3753
    Fin15AnchoredAtom3755 Fin15AnchoredAtom3764 Fin15AnchoredAtom3810 Fin15AnchoredAtom3950
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

theorem fin15Anchored_clause30685 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom1886 chi ∧
      ¬Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom1976 chi ∧
      ¬Fin15AnchoredAtom1986 chi ∧
      ¬Fin15AnchoredAtom2039 chi ∧
      ¬Fin15AnchoredAtom2040 chi ∧
      ¬Fin15AnchoredAtom2050 chi ∧
      ¬Fin15AnchoredAtom2096 chi ∧
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
      ¬Fin15AnchoredAtom2544 chi ∧
      ¬Fin15AnchoredAtom2545 chi ∧
      ¬Fin15AnchoredAtom2555 chi ∧
      ¬Fin15AnchoredAtom2601 chi ∧
      ¬Fin15AnchoredAtom2741 chi ∧
      ¬Fin15AnchoredAtom2888 chi ∧
      ¬Fin15AnchoredAtom2892 chi ∧
      ¬Fin15AnchoredAtom2893 chi ∧
      ¬Fin15AnchoredAtom2910 chi ∧
      ¬Fin15AnchoredAtom2911 chi ∧
      ¬Fin15AnchoredAtom2921 chi ∧
      ¬Fin15AnchoredAtom2974 chi ∧
      ¬Fin15AnchoredAtom2975 chi ∧
      ¬Fin15AnchoredAtom2985 chi ∧
      ¬Fin15AnchoredAtom3031 chi ∧
      ¬Fin15AnchoredAtom3259 chi ∧
      ¬Fin15AnchoredAtom3260 chi ∧
      ¬Fin15AnchoredAtom3270 chi ∧
      ¬Fin15AnchoredAtom3316 chi ∧
      ¬Fin15AnchoredAtom3456 chi ∧
      ¬Fin15AnchoredAtom3754 chi ∧
      ¬Fin15AnchoredAtom3755 chi ∧
      ¬Fin15AnchoredAtom3765 chi ∧
      ¬Fin15AnchoredAtom3811 chi ∧
      ¬Fin15AnchoredAtom3951 chi ∧
      ¬Fin15AnchoredAtom4491 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 6, 9, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25175
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1833 Fin15AnchoredAtom1836 Fin15AnchoredAtom1840
    Fin15AnchoredAtom1841 Fin15AnchoredAtom1853 Fin15AnchoredAtom1857 Fin15AnchoredAtom1858
    Fin15AnchoredAtom1875 Fin15AnchoredAtom1876 Fin15AnchoredAtom1886 Fin15AnchoredAtom1953
    Fin15AnchoredAtom1957 Fin15AnchoredAtom1958 Fin15AnchoredAtom1975 Fin15AnchoredAtom1976
    Fin15AnchoredAtom1986 Fin15AnchoredAtom2039 Fin15AnchoredAtom2040 Fin15AnchoredAtom2050
    Fin15AnchoredAtom2096 Fin15AnchoredAtom2173 Fin15AnchoredAtom2177 Fin15AnchoredAtom2178
    Fin15AnchoredAtom2195 Fin15AnchoredAtom2196 Fin15AnchoredAtom2206 Fin15AnchoredAtom2259
    Fin15AnchoredAtom2260 Fin15AnchoredAtom2270 Fin15AnchoredAtom2316 Fin15AnchoredAtom2544
    Fin15AnchoredAtom2545 Fin15AnchoredAtom2555 Fin15AnchoredAtom2601 Fin15AnchoredAtom2741
    Fin15AnchoredAtom2888 Fin15AnchoredAtom2892 Fin15AnchoredAtom2893 Fin15AnchoredAtom2910
    Fin15AnchoredAtom2911 Fin15AnchoredAtom2921 Fin15AnchoredAtom2974 Fin15AnchoredAtom2975
    Fin15AnchoredAtom2985 Fin15AnchoredAtom3031 Fin15AnchoredAtom3259 Fin15AnchoredAtom3260
    Fin15AnchoredAtom3270 Fin15AnchoredAtom3316 Fin15AnchoredAtom3456 Fin15AnchoredAtom3754
    Fin15AnchoredAtom3755 Fin15AnchoredAtom3765 Fin15AnchoredAtom3811 Fin15AnchoredAtom3951
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

theorem fin15Anchored_clause30686 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom1978 chi ∧
      ¬Fin15AnchoredAtom1979 chi ∧
      ¬Fin15AnchoredAtom1984 chi ∧
      ¬Fin15AnchoredAtom2042 chi ∧
      ¬Fin15AnchoredAtom2043 chi ∧
      ¬Fin15AnchoredAtom2048 chi ∧
      ¬Fin15AnchoredAtom2100 chi ∧
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
      ¬Fin15AnchoredAtom2547 chi ∧
      ¬Fin15AnchoredAtom2548 chi ∧
      ¬Fin15AnchoredAtom2553 chi ∧
      ¬Fin15AnchoredAtom2605 chi ∧
      ¬Fin15AnchoredAtom2745 chi ∧
      ¬Fin15AnchoredAtom2889 chi ∧
      ¬Fin15AnchoredAtom2891 chi ∧
      ¬Fin15AnchoredAtom2892 chi ∧
      ¬Fin15AnchoredAtom2913 chi ∧
      ¬Fin15AnchoredAtom2914 chi ∧
      ¬Fin15AnchoredAtom2919 chi ∧
      ¬Fin15AnchoredAtom2977 chi ∧
      ¬Fin15AnchoredAtom2978 chi ∧
      ¬Fin15AnchoredAtom2983 chi ∧
      ¬Fin15AnchoredAtom3035 chi ∧
      ¬Fin15AnchoredAtom3262 chi ∧
      ¬Fin15AnchoredAtom3263 chi ∧
      ¬Fin15AnchoredAtom3268 chi ∧
      ¬Fin15AnchoredAtom3320 chi ∧
      ¬Fin15AnchoredAtom3460 chi ∧
      ¬Fin15AnchoredAtom3757 chi ∧
      ¬Fin15AnchoredAtom3758 chi ∧
      ¬Fin15AnchoredAtom3763 chi ∧
      ¬Fin15AnchoredAtom3815 chi ∧
      ¬Fin15AnchoredAtom3955 chi ∧
      ¬Fin15AnchoredAtom4495 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 6, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13399
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1833 Fin15AnchoredAtom1837 Fin15AnchoredAtom1839
    Fin15AnchoredAtom1840 Fin15AnchoredAtom1854 Fin15AnchoredAtom1856 Fin15AnchoredAtom1857
    Fin15AnchoredAtom1878 Fin15AnchoredAtom1879 Fin15AnchoredAtom1884 Fin15AnchoredAtom1954
    Fin15AnchoredAtom1956 Fin15AnchoredAtom1957 Fin15AnchoredAtom1978 Fin15AnchoredAtom1979
    Fin15AnchoredAtom1984 Fin15AnchoredAtom2042 Fin15AnchoredAtom2043 Fin15AnchoredAtom2048
    Fin15AnchoredAtom2100 Fin15AnchoredAtom2174 Fin15AnchoredAtom2176 Fin15AnchoredAtom2177
    Fin15AnchoredAtom2198 Fin15AnchoredAtom2199 Fin15AnchoredAtom2204 Fin15AnchoredAtom2262
    Fin15AnchoredAtom2263 Fin15AnchoredAtom2268 Fin15AnchoredAtom2320 Fin15AnchoredAtom2547
    Fin15AnchoredAtom2548 Fin15AnchoredAtom2553 Fin15AnchoredAtom2605 Fin15AnchoredAtom2745
    Fin15AnchoredAtom2889 Fin15AnchoredAtom2891 Fin15AnchoredAtom2892 Fin15AnchoredAtom2913
    Fin15AnchoredAtom2914 Fin15AnchoredAtom2919 Fin15AnchoredAtom2977 Fin15AnchoredAtom2978
    Fin15AnchoredAtom2983 Fin15AnchoredAtom3035 Fin15AnchoredAtom3262 Fin15AnchoredAtom3263
    Fin15AnchoredAtom3268 Fin15AnchoredAtom3320 Fin15AnchoredAtom3460 Fin15AnchoredAtom3757
    Fin15AnchoredAtom3758 Fin15AnchoredAtom3763 Fin15AnchoredAtom3815 Fin15AnchoredAtom3955
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

theorem fin15Anchored_clause30687 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom1978 chi ∧
      ¬Fin15AnchoredAtom1980 chi ∧
      ¬Fin15AnchoredAtom1985 chi ∧
      ¬Fin15AnchoredAtom2042 chi ∧
      ¬Fin15AnchoredAtom2044 chi ∧
      ¬Fin15AnchoredAtom2049 chi ∧
      ¬Fin15AnchoredAtom2101 chi ∧
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
      ¬Fin15AnchoredAtom2547 chi ∧
      ¬Fin15AnchoredAtom2549 chi ∧
      ¬Fin15AnchoredAtom2554 chi ∧
      ¬Fin15AnchoredAtom2606 chi ∧
      ¬Fin15AnchoredAtom2746 chi ∧
      ¬Fin15AnchoredAtom2889 chi ∧
      ¬Fin15AnchoredAtom2891 chi ∧
      ¬Fin15AnchoredAtom2893 chi ∧
      ¬Fin15AnchoredAtom2913 chi ∧
      ¬Fin15AnchoredAtom2915 chi ∧
      ¬Fin15AnchoredAtom2920 chi ∧
      ¬Fin15AnchoredAtom2977 chi ∧
      ¬Fin15AnchoredAtom2979 chi ∧
      ¬Fin15AnchoredAtom2984 chi ∧
      ¬Fin15AnchoredAtom3036 chi ∧
      ¬Fin15AnchoredAtom3262 chi ∧
      ¬Fin15AnchoredAtom3264 chi ∧
      ¬Fin15AnchoredAtom3269 chi ∧
      ¬Fin15AnchoredAtom3321 chi ∧
      ¬Fin15AnchoredAtom3461 chi ∧
      ¬Fin15AnchoredAtom3757 chi ∧
      ¬Fin15AnchoredAtom3759 chi ∧
      ¬Fin15AnchoredAtom3764 chi ∧
      ¬Fin15AnchoredAtom3816 chi ∧
      ¬Fin15AnchoredAtom3956 chi ∧
      ¬Fin15AnchoredAtom4496 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 6, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21591
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1833 Fin15AnchoredAtom1837 Fin15AnchoredAtom1839
    Fin15AnchoredAtom1841 Fin15AnchoredAtom1854 Fin15AnchoredAtom1856 Fin15AnchoredAtom1858
    Fin15AnchoredAtom1878 Fin15AnchoredAtom1880 Fin15AnchoredAtom1885 Fin15AnchoredAtom1954
    Fin15AnchoredAtom1956 Fin15AnchoredAtom1958 Fin15AnchoredAtom1978 Fin15AnchoredAtom1980
    Fin15AnchoredAtom1985 Fin15AnchoredAtom2042 Fin15AnchoredAtom2044 Fin15AnchoredAtom2049
    Fin15AnchoredAtom2101 Fin15AnchoredAtom2174 Fin15AnchoredAtom2176 Fin15AnchoredAtom2178
    Fin15AnchoredAtom2198 Fin15AnchoredAtom2200 Fin15AnchoredAtom2205 Fin15AnchoredAtom2262
    Fin15AnchoredAtom2264 Fin15AnchoredAtom2269 Fin15AnchoredAtom2321 Fin15AnchoredAtom2547
    Fin15AnchoredAtom2549 Fin15AnchoredAtom2554 Fin15AnchoredAtom2606 Fin15AnchoredAtom2746
    Fin15AnchoredAtom2889 Fin15AnchoredAtom2891 Fin15AnchoredAtom2893 Fin15AnchoredAtom2913
    Fin15AnchoredAtom2915 Fin15AnchoredAtom2920 Fin15AnchoredAtom2977 Fin15AnchoredAtom2979
    Fin15AnchoredAtom2984 Fin15AnchoredAtom3036 Fin15AnchoredAtom3262 Fin15AnchoredAtom3264
    Fin15AnchoredAtom3269 Fin15AnchoredAtom3321 Fin15AnchoredAtom3461 Fin15AnchoredAtom3757
    Fin15AnchoredAtom3759 Fin15AnchoredAtom3764 Fin15AnchoredAtom3816 Fin15AnchoredAtom3956
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

theorem fin15Anchored_clause30688 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom1886 chi ∧
      ¬Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom1979 chi ∧
      ¬Fin15AnchoredAtom1980 chi ∧
      ¬Fin15AnchoredAtom1986 chi ∧
      ¬Fin15AnchoredAtom2043 chi ∧
      ¬Fin15AnchoredAtom2044 chi ∧
      ¬Fin15AnchoredAtom2050 chi ∧
      ¬Fin15AnchoredAtom2102 chi ∧
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
      ¬Fin15AnchoredAtom2548 chi ∧
      ¬Fin15AnchoredAtom2549 chi ∧
      ¬Fin15AnchoredAtom2555 chi ∧
      ¬Fin15AnchoredAtom2607 chi ∧
      ¬Fin15AnchoredAtom2747 chi ∧
      ¬Fin15AnchoredAtom2889 chi ∧
      ¬Fin15AnchoredAtom2892 chi ∧
      ¬Fin15AnchoredAtom2893 chi ∧
      ¬Fin15AnchoredAtom2914 chi ∧
      ¬Fin15AnchoredAtom2915 chi ∧
      ¬Fin15AnchoredAtom2921 chi ∧
      ¬Fin15AnchoredAtom2978 chi ∧
      ¬Fin15AnchoredAtom2979 chi ∧
      ¬Fin15AnchoredAtom2985 chi ∧
      ¬Fin15AnchoredAtom3037 chi ∧
      ¬Fin15AnchoredAtom3263 chi ∧
      ¬Fin15AnchoredAtom3264 chi ∧
      ¬Fin15AnchoredAtom3270 chi ∧
      ¬Fin15AnchoredAtom3322 chi ∧
      ¬Fin15AnchoredAtom3462 chi ∧
      ¬Fin15AnchoredAtom3758 chi ∧
      ¬Fin15AnchoredAtom3759 chi ∧
      ¬Fin15AnchoredAtom3765 chi ∧
      ¬Fin15AnchoredAtom3817 chi ∧
      ¬Fin15AnchoredAtom3957 chi ∧
      ¬Fin15AnchoredAtom4497 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 6, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25687
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1833 Fin15AnchoredAtom1837 Fin15AnchoredAtom1840
    Fin15AnchoredAtom1841 Fin15AnchoredAtom1854 Fin15AnchoredAtom1857 Fin15AnchoredAtom1858
    Fin15AnchoredAtom1879 Fin15AnchoredAtom1880 Fin15AnchoredAtom1886 Fin15AnchoredAtom1954
    Fin15AnchoredAtom1957 Fin15AnchoredAtom1958 Fin15AnchoredAtom1979 Fin15AnchoredAtom1980
    Fin15AnchoredAtom1986 Fin15AnchoredAtom2043 Fin15AnchoredAtom2044 Fin15AnchoredAtom2050
    Fin15AnchoredAtom2102 Fin15AnchoredAtom2174 Fin15AnchoredAtom2177 Fin15AnchoredAtom2178
    Fin15AnchoredAtom2199 Fin15AnchoredAtom2200 Fin15AnchoredAtom2206 Fin15AnchoredAtom2263
    Fin15AnchoredAtom2264 Fin15AnchoredAtom2270 Fin15AnchoredAtom2322 Fin15AnchoredAtom2548
    Fin15AnchoredAtom2549 Fin15AnchoredAtom2555 Fin15AnchoredAtom2607 Fin15AnchoredAtom2747
    Fin15AnchoredAtom2889 Fin15AnchoredAtom2892 Fin15AnchoredAtom2893 Fin15AnchoredAtom2914
    Fin15AnchoredAtom2915 Fin15AnchoredAtom2921 Fin15AnchoredAtom2978 Fin15AnchoredAtom2979
    Fin15AnchoredAtom2985 Fin15AnchoredAtom3037 Fin15AnchoredAtom3263 Fin15AnchoredAtom3264
    Fin15AnchoredAtom3270 Fin15AnchoredAtom3322 Fin15AnchoredAtom3462 Fin15AnchoredAtom3758
    Fin15AnchoredAtom3759 Fin15AnchoredAtom3765 Fin15AnchoredAtom3817 Fin15AnchoredAtom3957
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

theorem fin15Anchored_clause30689 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom1886 chi ∧
      ¬Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom1984 chi ∧
      ¬Fin15AnchoredAtom1985 chi ∧
      ¬Fin15AnchoredAtom1986 chi ∧
      ¬Fin15AnchoredAtom2048 chi ∧
      ¬Fin15AnchoredAtom2049 chi ∧
      ¬Fin15AnchoredAtom2050 chi ∧
      ¬Fin15AnchoredAtom2106 chi ∧
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
      ¬Fin15AnchoredAtom2553 chi ∧
      ¬Fin15AnchoredAtom2554 chi ∧
      ¬Fin15AnchoredAtom2555 chi ∧
      ¬Fin15AnchoredAtom2611 chi ∧
      ¬Fin15AnchoredAtom2751 chi ∧
      ¬Fin15AnchoredAtom2891 chi ∧
      ¬Fin15AnchoredAtom2892 chi ∧
      ¬Fin15AnchoredAtom2893 chi ∧
      ¬Fin15AnchoredAtom2919 chi ∧
      ¬Fin15AnchoredAtom2920 chi ∧
      ¬Fin15AnchoredAtom2921 chi ∧
      ¬Fin15AnchoredAtom2983 chi ∧
      ¬Fin15AnchoredAtom2984 chi ∧
      ¬Fin15AnchoredAtom2985 chi ∧
      ¬Fin15AnchoredAtom3041 chi ∧
      ¬Fin15AnchoredAtom3268 chi ∧
      ¬Fin15AnchoredAtom3269 chi ∧
      ¬Fin15AnchoredAtom3270 chi ∧
      ¬Fin15AnchoredAtom3326 chi ∧
      ¬Fin15AnchoredAtom3466 chi ∧
      ¬Fin15AnchoredAtom3763 chi ∧
      ¬Fin15AnchoredAtom3764 chi ∧
      ¬Fin15AnchoredAtom3765 chi ∧
      ¬Fin15AnchoredAtom3821 chi ∧
      ¬Fin15AnchoredAtom3961 chi ∧
      ¬Fin15AnchoredAtom4501 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 6, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask28759
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1833 Fin15AnchoredAtom1839 Fin15AnchoredAtom1840
    Fin15AnchoredAtom1841 Fin15AnchoredAtom1856 Fin15AnchoredAtom1857 Fin15AnchoredAtom1858
    Fin15AnchoredAtom1884 Fin15AnchoredAtom1885 Fin15AnchoredAtom1886 Fin15AnchoredAtom1956
    Fin15AnchoredAtom1957 Fin15AnchoredAtom1958 Fin15AnchoredAtom1984 Fin15AnchoredAtom1985
    Fin15AnchoredAtom1986 Fin15AnchoredAtom2048 Fin15AnchoredAtom2049 Fin15AnchoredAtom2050
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2176 Fin15AnchoredAtom2177 Fin15AnchoredAtom2178
    Fin15AnchoredAtom2204 Fin15AnchoredAtom2205 Fin15AnchoredAtom2206 Fin15AnchoredAtom2268
    Fin15AnchoredAtom2269 Fin15AnchoredAtom2270 Fin15AnchoredAtom2326 Fin15AnchoredAtom2553
    Fin15AnchoredAtom2554 Fin15AnchoredAtom2555 Fin15AnchoredAtom2611 Fin15AnchoredAtom2751
    Fin15AnchoredAtom2891 Fin15AnchoredAtom2892 Fin15AnchoredAtom2893 Fin15AnchoredAtom2919
    Fin15AnchoredAtom2920 Fin15AnchoredAtom2921 Fin15AnchoredAtom2983 Fin15AnchoredAtom2984
    Fin15AnchoredAtom2985 Fin15AnchoredAtom3041 Fin15AnchoredAtom3268 Fin15AnchoredAtom3269
    Fin15AnchoredAtom3270 Fin15AnchoredAtom3326 Fin15AnchoredAtom3466 Fin15AnchoredAtom3763
    Fin15AnchoredAtom3764 Fin15AnchoredAtom3765 Fin15AnchoredAtom3821 Fin15AnchoredAtom3961
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

theorem fin15Anchored_clause30690 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom1978 chi ∧
      ¬Fin15AnchoredAtom2057 chi ∧
      ¬Fin15AnchoredAtom2059 chi ∧
      ¬Fin15AnchoredAtom2063 chi ∧
      ¬Fin15AnchoredAtom2088 chi ∧
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
      ¬Fin15AnchoredAtom2562 chi ∧
      ¬Fin15AnchoredAtom2564 chi ∧
      ¬Fin15AnchoredAtom2568 chi ∧
      ¬Fin15AnchoredAtom2593 chi ∧
      ¬Fin15AnchoredAtom2768 chi ∧
      ¬Fin15AnchoredAtom2895 chi ∧
      ¬Fin15AnchoredAtom2896 chi ∧
      ¬Fin15AnchoredAtom2898 chi ∧
      ¬Fin15AnchoredAtom2907 chi ∧
      ¬Fin15AnchoredAtom2909 chi ∧
      ¬Fin15AnchoredAtom2913 chi ∧
      ¬Fin15AnchoredAtom2992 chi ∧
      ¬Fin15AnchoredAtom2994 chi ∧
      ¬Fin15AnchoredAtom2998 chi ∧
      ¬Fin15AnchoredAtom3023 chi ∧
      ¬Fin15AnchoredAtom3277 chi ∧
      ¬Fin15AnchoredAtom3279 chi ∧
      ¬Fin15AnchoredAtom3283 chi ∧
      ¬Fin15AnchoredAtom3308 chi ∧
      ¬Fin15AnchoredAtom3483 chi ∧
      ¬Fin15AnchoredAtom3772 chi ∧
      ¬Fin15AnchoredAtom3774 chi ∧
      ¬Fin15AnchoredAtom3778 chi ∧
      ¬Fin15AnchoredAtom3803 chi ∧
      ¬Fin15AnchoredAtom3978 chi ∧
      ¬Fin15AnchoredAtom4518 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 7, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05783
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1834 Fin15AnchoredAtom1836 Fin15AnchoredAtom1837
    Fin15AnchoredAtom1839 Fin15AnchoredAtom1860 Fin15AnchoredAtom1861 Fin15AnchoredAtom1863
    Fin15AnchoredAtom1872 Fin15AnchoredAtom1874 Fin15AnchoredAtom1878 Fin15AnchoredAtom1960
    Fin15AnchoredAtom1961 Fin15AnchoredAtom1963 Fin15AnchoredAtom1972 Fin15AnchoredAtom1974
    Fin15AnchoredAtom1978 Fin15AnchoredAtom2057 Fin15AnchoredAtom2059 Fin15AnchoredAtom2063
    Fin15AnchoredAtom2088 Fin15AnchoredAtom2180 Fin15AnchoredAtom2181 Fin15AnchoredAtom2183
    Fin15AnchoredAtom2192 Fin15AnchoredAtom2194 Fin15AnchoredAtom2198 Fin15AnchoredAtom2277
    Fin15AnchoredAtom2279 Fin15AnchoredAtom2283 Fin15AnchoredAtom2308 Fin15AnchoredAtom2562
    Fin15AnchoredAtom2564 Fin15AnchoredAtom2568 Fin15AnchoredAtom2593 Fin15AnchoredAtom2768
    Fin15AnchoredAtom2895 Fin15AnchoredAtom2896 Fin15AnchoredAtom2898 Fin15AnchoredAtom2907
    Fin15AnchoredAtom2909 Fin15AnchoredAtom2913 Fin15AnchoredAtom2992 Fin15AnchoredAtom2994
    Fin15AnchoredAtom2998 Fin15AnchoredAtom3023 Fin15AnchoredAtom3277 Fin15AnchoredAtom3279
    Fin15AnchoredAtom3283 Fin15AnchoredAtom3308 Fin15AnchoredAtom3483 Fin15AnchoredAtom3772
    Fin15AnchoredAtom3774 Fin15AnchoredAtom3778 Fin15AnchoredAtom3803 Fin15AnchoredAtom3978
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

theorem fin15Anchored_clause30691 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom1979 chi ∧
      ¬Fin15AnchoredAtom2057 chi ∧
      ¬Fin15AnchoredAtom2060 chi ∧
      ¬Fin15AnchoredAtom2064 chi ∧
      ¬Fin15AnchoredAtom2089 chi ∧
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
      ¬Fin15AnchoredAtom2562 chi ∧
      ¬Fin15AnchoredAtom2565 chi ∧
      ¬Fin15AnchoredAtom2569 chi ∧
      ¬Fin15AnchoredAtom2594 chi ∧
      ¬Fin15AnchoredAtom2769 chi ∧
      ¬Fin15AnchoredAtom2895 chi ∧
      ¬Fin15AnchoredAtom2896 chi ∧
      ¬Fin15AnchoredAtom2899 chi ∧
      ¬Fin15AnchoredAtom2907 chi ∧
      ¬Fin15AnchoredAtom2910 chi ∧
      ¬Fin15AnchoredAtom2914 chi ∧
      ¬Fin15AnchoredAtom2992 chi ∧
      ¬Fin15AnchoredAtom2995 chi ∧
      ¬Fin15AnchoredAtom2999 chi ∧
      ¬Fin15AnchoredAtom3024 chi ∧
      ¬Fin15AnchoredAtom3277 chi ∧
      ¬Fin15AnchoredAtom3280 chi ∧
      ¬Fin15AnchoredAtom3284 chi ∧
      ¬Fin15AnchoredAtom3309 chi ∧
      ¬Fin15AnchoredAtom3484 chi ∧
      ¬Fin15AnchoredAtom3772 chi ∧
      ¬Fin15AnchoredAtom3775 chi ∧
      ¬Fin15AnchoredAtom3779 chi ∧
      ¬Fin15AnchoredAtom3804 chi ∧
      ¬Fin15AnchoredAtom3979 chi ∧
      ¬Fin15AnchoredAtom4519 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 7, 9, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09879
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1834 Fin15AnchoredAtom1836 Fin15AnchoredAtom1837
    Fin15AnchoredAtom1840 Fin15AnchoredAtom1860 Fin15AnchoredAtom1861 Fin15AnchoredAtom1864
    Fin15AnchoredAtom1872 Fin15AnchoredAtom1875 Fin15AnchoredAtom1879 Fin15AnchoredAtom1960
    Fin15AnchoredAtom1961 Fin15AnchoredAtom1964 Fin15AnchoredAtom1972 Fin15AnchoredAtom1975
    Fin15AnchoredAtom1979 Fin15AnchoredAtom2057 Fin15AnchoredAtom2060 Fin15AnchoredAtom2064
    Fin15AnchoredAtom2089 Fin15AnchoredAtom2180 Fin15AnchoredAtom2181 Fin15AnchoredAtom2184
    Fin15AnchoredAtom2192 Fin15AnchoredAtom2195 Fin15AnchoredAtom2199 Fin15AnchoredAtom2277
    Fin15AnchoredAtom2280 Fin15AnchoredAtom2284 Fin15AnchoredAtom2309 Fin15AnchoredAtom2562
    Fin15AnchoredAtom2565 Fin15AnchoredAtom2569 Fin15AnchoredAtom2594 Fin15AnchoredAtom2769
    Fin15AnchoredAtom2895 Fin15AnchoredAtom2896 Fin15AnchoredAtom2899 Fin15AnchoredAtom2907
    Fin15AnchoredAtom2910 Fin15AnchoredAtom2914 Fin15AnchoredAtom2992 Fin15AnchoredAtom2995
    Fin15AnchoredAtom2999 Fin15AnchoredAtom3024 Fin15AnchoredAtom3277 Fin15AnchoredAtom3280
    Fin15AnchoredAtom3284 Fin15AnchoredAtom3309 Fin15AnchoredAtom3484 Fin15AnchoredAtom3772
    Fin15AnchoredAtom3775 Fin15AnchoredAtom3779 Fin15AnchoredAtom3804 Fin15AnchoredAtom3979
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

theorem fin15Anchored_clause30692 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom1976 chi ∧
      ¬Fin15AnchoredAtom1980 chi ∧
      ¬Fin15AnchoredAtom2057 chi ∧
      ¬Fin15AnchoredAtom2061 chi ∧
      ¬Fin15AnchoredAtom2065 chi ∧
      ¬Fin15AnchoredAtom2090 chi ∧
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
      ¬Fin15AnchoredAtom2562 chi ∧
      ¬Fin15AnchoredAtom2566 chi ∧
      ¬Fin15AnchoredAtom2570 chi ∧
      ¬Fin15AnchoredAtom2595 chi ∧
      ¬Fin15AnchoredAtom2770 chi ∧
      ¬Fin15AnchoredAtom2895 chi ∧
      ¬Fin15AnchoredAtom2896 chi ∧
      ¬Fin15AnchoredAtom2900 chi ∧
      ¬Fin15AnchoredAtom2907 chi ∧
      ¬Fin15AnchoredAtom2911 chi ∧
      ¬Fin15AnchoredAtom2915 chi ∧
      ¬Fin15AnchoredAtom2992 chi ∧
      ¬Fin15AnchoredAtom2996 chi ∧
      ¬Fin15AnchoredAtom3000 chi ∧
      ¬Fin15AnchoredAtom3025 chi ∧
      ¬Fin15AnchoredAtom3277 chi ∧
      ¬Fin15AnchoredAtom3281 chi ∧
      ¬Fin15AnchoredAtom3285 chi ∧
      ¬Fin15AnchoredAtom3310 chi ∧
      ¬Fin15AnchoredAtom3485 chi ∧
      ¬Fin15AnchoredAtom3772 chi ∧
      ¬Fin15AnchoredAtom3776 chi ∧
      ¬Fin15AnchoredAtom3780 chi ∧
      ¬Fin15AnchoredAtom3805 chi ∧
      ¬Fin15AnchoredAtom3980 chi ∧
      ¬Fin15AnchoredAtom4520 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 7, 9, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask18071
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1834 Fin15AnchoredAtom1836 Fin15AnchoredAtom1837
    Fin15AnchoredAtom1841 Fin15AnchoredAtom1860 Fin15AnchoredAtom1861 Fin15AnchoredAtom1865
    Fin15AnchoredAtom1872 Fin15AnchoredAtom1876 Fin15AnchoredAtom1880 Fin15AnchoredAtom1960
    Fin15AnchoredAtom1961 Fin15AnchoredAtom1965 Fin15AnchoredAtom1972 Fin15AnchoredAtom1976
    Fin15AnchoredAtom1980 Fin15AnchoredAtom2057 Fin15AnchoredAtom2061 Fin15AnchoredAtom2065
    Fin15AnchoredAtom2090 Fin15AnchoredAtom2180 Fin15AnchoredAtom2181 Fin15AnchoredAtom2185
    Fin15AnchoredAtom2192 Fin15AnchoredAtom2196 Fin15AnchoredAtom2200 Fin15AnchoredAtom2277
    Fin15AnchoredAtom2281 Fin15AnchoredAtom2285 Fin15AnchoredAtom2310 Fin15AnchoredAtom2562
    Fin15AnchoredAtom2566 Fin15AnchoredAtom2570 Fin15AnchoredAtom2595 Fin15AnchoredAtom2770
    Fin15AnchoredAtom2895 Fin15AnchoredAtom2896 Fin15AnchoredAtom2900 Fin15AnchoredAtom2907
    Fin15AnchoredAtom2911 Fin15AnchoredAtom2915 Fin15AnchoredAtom2992 Fin15AnchoredAtom2996
    Fin15AnchoredAtom3000 Fin15AnchoredAtom3025 Fin15AnchoredAtom3277 Fin15AnchoredAtom3281
    Fin15AnchoredAtom3285 Fin15AnchoredAtom3310 Fin15AnchoredAtom3485 Fin15AnchoredAtom3772
    Fin15AnchoredAtom3776 Fin15AnchoredAtom3780 Fin15AnchoredAtom3805 Fin15AnchoredAtom3980
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

theorem fin15Anchored_clause30693 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom1984 chi ∧
      ¬Fin15AnchoredAtom2059 chi ∧
      ¬Fin15AnchoredAtom2060 chi ∧
      ¬Fin15AnchoredAtom2069 chi ∧
      ¬Fin15AnchoredAtom2094 chi ∧
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
      ¬Fin15AnchoredAtom2564 chi ∧
      ¬Fin15AnchoredAtom2565 chi ∧
      ¬Fin15AnchoredAtom2574 chi ∧
      ¬Fin15AnchoredAtom2599 chi ∧
      ¬Fin15AnchoredAtom2774 chi ∧
      ¬Fin15AnchoredAtom2895 chi ∧
      ¬Fin15AnchoredAtom2898 chi ∧
      ¬Fin15AnchoredAtom2899 chi ∧
      ¬Fin15AnchoredAtom2909 chi ∧
      ¬Fin15AnchoredAtom2910 chi ∧
      ¬Fin15AnchoredAtom2919 chi ∧
      ¬Fin15AnchoredAtom2994 chi ∧
      ¬Fin15AnchoredAtom2995 chi ∧
      ¬Fin15AnchoredAtom3004 chi ∧
      ¬Fin15AnchoredAtom3029 chi ∧
      ¬Fin15AnchoredAtom3279 chi ∧
      ¬Fin15AnchoredAtom3280 chi ∧
      ¬Fin15AnchoredAtom3289 chi ∧
      ¬Fin15AnchoredAtom3314 chi ∧
      ¬Fin15AnchoredAtom3489 chi ∧
      ¬Fin15AnchoredAtom3774 chi ∧
      ¬Fin15AnchoredAtom3775 chi ∧
      ¬Fin15AnchoredAtom3784 chi ∧
      ¬Fin15AnchoredAtom3809 chi ∧
      ¬Fin15AnchoredAtom3984 chi ∧
      ¬Fin15AnchoredAtom4524 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 7, 9, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask12951
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1834 Fin15AnchoredAtom1836 Fin15AnchoredAtom1839
    Fin15AnchoredAtom1840 Fin15AnchoredAtom1860 Fin15AnchoredAtom1863 Fin15AnchoredAtom1864
    Fin15AnchoredAtom1874 Fin15AnchoredAtom1875 Fin15AnchoredAtom1884 Fin15AnchoredAtom1960
    Fin15AnchoredAtom1963 Fin15AnchoredAtom1964 Fin15AnchoredAtom1974 Fin15AnchoredAtom1975
    Fin15AnchoredAtom1984 Fin15AnchoredAtom2059 Fin15AnchoredAtom2060 Fin15AnchoredAtom2069
    Fin15AnchoredAtom2094 Fin15AnchoredAtom2180 Fin15AnchoredAtom2183 Fin15AnchoredAtom2184
    Fin15AnchoredAtom2194 Fin15AnchoredAtom2195 Fin15AnchoredAtom2204 Fin15AnchoredAtom2279
    Fin15AnchoredAtom2280 Fin15AnchoredAtom2289 Fin15AnchoredAtom2314 Fin15AnchoredAtom2564
    Fin15AnchoredAtom2565 Fin15AnchoredAtom2574 Fin15AnchoredAtom2599 Fin15AnchoredAtom2774
    Fin15AnchoredAtom2895 Fin15AnchoredAtom2898 Fin15AnchoredAtom2899 Fin15AnchoredAtom2909
    Fin15AnchoredAtom2910 Fin15AnchoredAtom2919 Fin15AnchoredAtom2994 Fin15AnchoredAtom2995
    Fin15AnchoredAtom3004 Fin15AnchoredAtom3029 Fin15AnchoredAtom3279 Fin15AnchoredAtom3280
    Fin15AnchoredAtom3289 Fin15AnchoredAtom3314 Fin15AnchoredAtom3489 Fin15AnchoredAtom3774
    Fin15AnchoredAtom3775 Fin15AnchoredAtom3784 Fin15AnchoredAtom3809 Fin15AnchoredAtom3984
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

theorem fin15Anchored_clause30694 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom1976 chi ∧
      ¬Fin15AnchoredAtom1985 chi ∧
      ¬Fin15AnchoredAtom2059 chi ∧
      ¬Fin15AnchoredAtom2061 chi ∧
      ¬Fin15AnchoredAtom2070 chi ∧
      ¬Fin15AnchoredAtom2095 chi ∧
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
      ¬Fin15AnchoredAtom2564 chi ∧
      ¬Fin15AnchoredAtom2566 chi ∧
      ¬Fin15AnchoredAtom2575 chi ∧
      ¬Fin15AnchoredAtom2600 chi ∧
      ¬Fin15AnchoredAtom2775 chi ∧
      ¬Fin15AnchoredAtom2895 chi ∧
      ¬Fin15AnchoredAtom2898 chi ∧
      ¬Fin15AnchoredAtom2900 chi ∧
      ¬Fin15AnchoredAtom2909 chi ∧
      ¬Fin15AnchoredAtom2911 chi ∧
      ¬Fin15AnchoredAtom2920 chi ∧
      ¬Fin15AnchoredAtom2994 chi ∧
      ¬Fin15AnchoredAtom2996 chi ∧
      ¬Fin15AnchoredAtom3005 chi ∧
      ¬Fin15AnchoredAtom3030 chi ∧
      ¬Fin15AnchoredAtom3279 chi ∧
      ¬Fin15AnchoredAtom3281 chi ∧
      ¬Fin15AnchoredAtom3290 chi ∧
      ¬Fin15AnchoredAtom3315 chi ∧
      ¬Fin15AnchoredAtom3490 chi ∧
      ¬Fin15AnchoredAtom3774 chi ∧
      ¬Fin15AnchoredAtom3776 chi ∧
      ¬Fin15AnchoredAtom3785 chi ∧
      ¬Fin15AnchoredAtom3810 chi ∧
      ¬Fin15AnchoredAtom3985 chi ∧
      ¬Fin15AnchoredAtom4525 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 7, 9, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21143
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1834 Fin15AnchoredAtom1836 Fin15AnchoredAtom1839
    Fin15AnchoredAtom1841 Fin15AnchoredAtom1860 Fin15AnchoredAtom1863 Fin15AnchoredAtom1865
    Fin15AnchoredAtom1874 Fin15AnchoredAtom1876 Fin15AnchoredAtom1885 Fin15AnchoredAtom1960
    Fin15AnchoredAtom1963 Fin15AnchoredAtom1965 Fin15AnchoredAtom1974 Fin15AnchoredAtom1976
    Fin15AnchoredAtom1985 Fin15AnchoredAtom2059 Fin15AnchoredAtom2061 Fin15AnchoredAtom2070
    Fin15AnchoredAtom2095 Fin15AnchoredAtom2180 Fin15AnchoredAtom2183 Fin15AnchoredAtom2185
    Fin15AnchoredAtom2194 Fin15AnchoredAtom2196 Fin15AnchoredAtom2205 Fin15AnchoredAtom2279
    Fin15AnchoredAtom2281 Fin15AnchoredAtom2290 Fin15AnchoredAtom2315 Fin15AnchoredAtom2564
    Fin15AnchoredAtom2566 Fin15AnchoredAtom2575 Fin15AnchoredAtom2600 Fin15AnchoredAtom2775
    Fin15AnchoredAtom2895 Fin15AnchoredAtom2898 Fin15AnchoredAtom2900 Fin15AnchoredAtom2909
    Fin15AnchoredAtom2911 Fin15AnchoredAtom2920 Fin15AnchoredAtom2994 Fin15AnchoredAtom2996
    Fin15AnchoredAtom3005 Fin15AnchoredAtom3030 Fin15AnchoredAtom3279 Fin15AnchoredAtom3281
    Fin15AnchoredAtom3290 Fin15AnchoredAtom3315 Fin15AnchoredAtom3490 Fin15AnchoredAtom3774
    Fin15AnchoredAtom3776 Fin15AnchoredAtom3785 Fin15AnchoredAtom3810 Fin15AnchoredAtom3985
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

theorem fin15Anchored_clause30695 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom1886 chi ∧
      ¬Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom1976 chi ∧
      ¬Fin15AnchoredAtom1986 chi ∧
      ¬Fin15AnchoredAtom2060 chi ∧
      ¬Fin15AnchoredAtom2061 chi ∧
      ¬Fin15AnchoredAtom2071 chi ∧
      ¬Fin15AnchoredAtom2096 chi ∧
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
      ¬Fin15AnchoredAtom2565 chi ∧
      ¬Fin15AnchoredAtom2566 chi ∧
      ¬Fin15AnchoredAtom2576 chi ∧
      ¬Fin15AnchoredAtom2601 chi ∧
      ¬Fin15AnchoredAtom2776 chi ∧
      ¬Fin15AnchoredAtom2895 chi ∧
      ¬Fin15AnchoredAtom2899 chi ∧
      ¬Fin15AnchoredAtom2900 chi ∧
      ¬Fin15AnchoredAtom2910 chi ∧
      ¬Fin15AnchoredAtom2911 chi ∧
      ¬Fin15AnchoredAtom2921 chi ∧
      ¬Fin15AnchoredAtom2995 chi ∧
      ¬Fin15AnchoredAtom2996 chi ∧
      ¬Fin15AnchoredAtom3006 chi ∧
      ¬Fin15AnchoredAtom3031 chi ∧
      ¬Fin15AnchoredAtom3280 chi ∧
      ¬Fin15AnchoredAtom3281 chi ∧
      ¬Fin15AnchoredAtom3291 chi ∧
      ¬Fin15AnchoredAtom3316 chi ∧
      ¬Fin15AnchoredAtom3491 chi ∧
      ¬Fin15AnchoredAtom3775 chi ∧
      ¬Fin15AnchoredAtom3776 chi ∧
      ¬Fin15AnchoredAtom3786 chi ∧
      ¬Fin15AnchoredAtom3811 chi ∧
      ¬Fin15AnchoredAtom3986 chi ∧
      ¬Fin15AnchoredAtom4526 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 7, 9, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25239
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1834 Fin15AnchoredAtom1836 Fin15AnchoredAtom1840
    Fin15AnchoredAtom1841 Fin15AnchoredAtom1860 Fin15AnchoredAtom1864 Fin15AnchoredAtom1865
    Fin15AnchoredAtom1875 Fin15AnchoredAtom1876 Fin15AnchoredAtom1886 Fin15AnchoredAtom1960
    Fin15AnchoredAtom1964 Fin15AnchoredAtom1965 Fin15AnchoredAtom1975 Fin15AnchoredAtom1976
    Fin15AnchoredAtom1986 Fin15AnchoredAtom2060 Fin15AnchoredAtom2061 Fin15AnchoredAtom2071
    Fin15AnchoredAtom2096 Fin15AnchoredAtom2180 Fin15AnchoredAtom2184 Fin15AnchoredAtom2185
    Fin15AnchoredAtom2195 Fin15AnchoredAtom2196 Fin15AnchoredAtom2206 Fin15AnchoredAtom2280
    Fin15AnchoredAtom2281 Fin15AnchoredAtom2291 Fin15AnchoredAtom2316 Fin15AnchoredAtom2565
    Fin15AnchoredAtom2566 Fin15AnchoredAtom2576 Fin15AnchoredAtom2601 Fin15AnchoredAtom2776
    Fin15AnchoredAtom2895 Fin15AnchoredAtom2899 Fin15AnchoredAtom2900 Fin15AnchoredAtom2910
    Fin15AnchoredAtom2911 Fin15AnchoredAtom2921 Fin15AnchoredAtom2995 Fin15AnchoredAtom2996
    Fin15AnchoredAtom3006 Fin15AnchoredAtom3031 Fin15AnchoredAtom3280 Fin15AnchoredAtom3281
    Fin15AnchoredAtom3291 Fin15AnchoredAtom3316 Fin15AnchoredAtom3491 Fin15AnchoredAtom3775
    Fin15AnchoredAtom3776 Fin15AnchoredAtom3786 Fin15AnchoredAtom3811 Fin15AnchoredAtom3986
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

theorem fin15Anchored_clause30696 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom1978 chi ∧
      ¬Fin15AnchoredAtom1979 chi ∧
      ¬Fin15AnchoredAtom1984 chi ∧
      ¬Fin15AnchoredAtom2063 chi ∧
      ¬Fin15AnchoredAtom2064 chi ∧
      ¬Fin15AnchoredAtom2069 chi ∧
      ¬Fin15AnchoredAtom2100 chi ∧
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
      ¬Fin15AnchoredAtom2568 chi ∧
      ¬Fin15AnchoredAtom2569 chi ∧
      ¬Fin15AnchoredAtom2574 chi ∧
      ¬Fin15AnchoredAtom2605 chi ∧
      ¬Fin15AnchoredAtom2780 chi ∧
      ¬Fin15AnchoredAtom2896 chi ∧
      ¬Fin15AnchoredAtom2898 chi ∧
      ¬Fin15AnchoredAtom2899 chi ∧
      ¬Fin15AnchoredAtom2913 chi ∧
      ¬Fin15AnchoredAtom2914 chi ∧
      ¬Fin15AnchoredAtom2919 chi ∧
      ¬Fin15AnchoredAtom2998 chi ∧
      ¬Fin15AnchoredAtom2999 chi ∧
      ¬Fin15AnchoredAtom3004 chi ∧
      ¬Fin15AnchoredAtom3035 chi ∧
      ¬Fin15AnchoredAtom3283 chi ∧
      ¬Fin15AnchoredAtom3284 chi ∧
      ¬Fin15AnchoredAtom3289 chi ∧
      ¬Fin15AnchoredAtom3320 chi ∧
      ¬Fin15AnchoredAtom3495 chi ∧
      ¬Fin15AnchoredAtom3778 chi ∧
      ¬Fin15AnchoredAtom3779 chi ∧
      ¬Fin15AnchoredAtom3784 chi ∧
      ¬Fin15AnchoredAtom3815 chi ∧
      ¬Fin15AnchoredAtom3990 chi ∧
      ¬Fin15AnchoredAtom4530 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 7, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13463
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1834 Fin15AnchoredAtom1837 Fin15AnchoredAtom1839
    Fin15AnchoredAtom1840 Fin15AnchoredAtom1861 Fin15AnchoredAtom1863 Fin15AnchoredAtom1864
    Fin15AnchoredAtom1878 Fin15AnchoredAtom1879 Fin15AnchoredAtom1884 Fin15AnchoredAtom1961
    Fin15AnchoredAtom1963 Fin15AnchoredAtom1964 Fin15AnchoredAtom1978 Fin15AnchoredAtom1979
    Fin15AnchoredAtom1984 Fin15AnchoredAtom2063 Fin15AnchoredAtom2064 Fin15AnchoredAtom2069
    Fin15AnchoredAtom2100 Fin15AnchoredAtom2181 Fin15AnchoredAtom2183 Fin15AnchoredAtom2184
    Fin15AnchoredAtom2198 Fin15AnchoredAtom2199 Fin15AnchoredAtom2204 Fin15AnchoredAtom2283
    Fin15AnchoredAtom2284 Fin15AnchoredAtom2289 Fin15AnchoredAtom2320 Fin15AnchoredAtom2568
    Fin15AnchoredAtom2569 Fin15AnchoredAtom2574 Fin15AnchoredAtom2605 Fin15AnchoredAtom2780
    Fin15AnchoredAtom2896 Fin15AnchoredAtom2898 Fin15AnchoredAtom2899 Fin15AnchoredAtom2913
    Fin15AnchoredAtom2914 Fin15AnchoredAtom2919 Fin15AnchoredAtom2998 Fin15AnchoredAtom2999
    Fin15AnchoredAtom3004 Fin15AnchoredAtom3035 Fin15AnchoredAtom3283 Fin15AnchoredAtom3284
    Fin15AnchoredAtom3289 Fin15AnchoredAtom3320 Fin15AnchoredAtom3495 Fin15AnchoredAtom3778
    Fin15AnchoredAtom3779 Fin15AnchoredAtom3784 Fin15AnchoredAtom3815 Fin15AnchoredAtom3990
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

theorem fin15Anchored_clause30697 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom1978 chi ∧
      ¬Fin15AnchoredAtom1980 chi ∧
      ¬Fin15AnchoredAtom1985 chi ∧
      ¬Fin15AnchoredAtom2063 chi ∧
      ¬Fin15AnchoredAtom2065 chi ∧
      ¬Fin15AnchoredAtom2070 chi ∧
      ¬Fin15AnchoredAtom2101 chi ∧
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
      ¬Fin15AnchoredAtom2568 chi ∧
      ¬Fin15AnchoredAtom2570 chi ∧
      ¬Fin15AnchoredAtom2575 chi ∧
      ¬Fin15AnchoredAtom2606 chi ∧
      ¬Fin15AnchoredAtom2781 chi ∧
      ¬Fin15AnchoredAtom2896 chi ∧
      ¬Fin15AnchoredAtom2898 chi ∧
      ¬Fin15AnchoredAtom2900 chi ∧
      ¬Fin15AnchoredAtom2913 chi ∧
      ¬Fin15AnchoredAtom2915 chi ∧
      ¬Fin15AnchoredAtom2920 chi ∧
      ¬Fin15AnchoredAtom2998 chi ∧
      ¬Fin15AnchoredAtom3000 chi ∧
      ¬Fin15AnchoredAtom3005 chi ∧
      ¬Fin15AnchoredAtom3036 chi ∧
      ¬Fin15AnchoredAtom3283 chi ∧
      ¬Fin15AnchoredAtom3285 chi ∧
      ¬Fin15AnchoredAtom3290 chi ∧
      ¬Fin15AnchoredAtom3321 chi ∧
      ¬Fin15AnchoredAtom3496 chi ∧
      ¬Fin15AnchoredAtom3778 chi ∧
      ¬Fin15AnchoredAtom3780 chi ∧
      ¬Fin15AnchoredAtom3785 chi ∧
      ¬Fin15AnchoredAtom3816 chi ∧
      ¬Fin15AnchoredAtom3991 chi ∧
      ¬Fin15AnchoredAtom4531 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 7, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21655
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1834 Fin15AnchoredAtom1837 Fin15AnchoredAtom1839
    Fin15AnchoredAtom1841 Fin15AnchoredAtom1861 Fin15AnchoredAtom1863 Fin15AnchoredAtom1865
    Fin15AnchoredAtom1878 Fin15AnchoredAtom1880 Fin15AnchoredAtom1885 Fin15AnchoredAtom1961
    Fin15AnchoredAtom1963 Fin15AnchoredAtom1965 Fin15AnchoredAtom1978 Fin15AnchoredAtom1980
    Fin15AnchoredAtom1985 Fin15AnchoredAtom2063 Fin15AnchoredAtom2065 Fin15AnchoredAtom2070
    Fin15AnchoredAtom2101 Fin15AnchoredAtom2181 Fin15AnchoredAtom2183 Fin15AnchoredAtom2185
    Fin15AnchoredAtom2198 Fin15AnchoredAtom2200 Fin15AnchoredAtom2205 Fin15AnchoredAtom2283
    Fin15AnchoredAtom2285 Fin15AnchoredAtom2290 Fin15AnchoredAtom2321 Fin15AnchoredAtom2568
    Fin15AnchoredAtom2570 Fin15AnchoredAtom2575 Fin15AnchoredAtom2606 Fin15AnchoredAtom2781
    Fin15AnchoredAtom2896 Fin15AnchoredAtom2898 Fin15AnchoredAtom2900 Fin15AnchoredAtom2913
    Fin15AnchoredAtom2915 Fin15AnchoredAtom2920 Fin15AnchoredAtom2998 Fin15AnchoredAtom3000
    Fin15AnchoredAtom3005 Fin15AnchoredAtom3036 Fin15AnchoredAtom3283 Fin15AnchoredAtom3285
    Fin15AnchoredAtom3290 Fin15AnchoredAtom3321 Fin15AnchoredAtom3496 Fin15AnchoredAtom3778
    Fin15AnchoredAtom3780 Fin15AnchoredAtom3785 Fin15AnchoredAtom3816 Fin15AnchoredAtom3991
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

theorem fin15Anchored_clause30698 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom1886 chi ∧
      ¬Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom1979 chi ∧
      ¬Fin15AnchoredAtom1980 chi ∧
      ¬Fin15AnchoredAtom1986 chi ∧
      ¬Fin15AnchoredAtom2064 chi ∧
      ¬Fin15AnchoredAtom2065 chi ∧
      ¬Fin15AnchoredAtom2071 chi ∧
      ¬Fin15AnchoredAtom2102 chi ∧
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
      ¬Fin15AnchoredAtom2569 chi ∧
      ¬Fin15AnchoredAtom2570 chi ∧
      ¬Fin15AnchoredAtom2576 chi ∧
      ¬Fin15AnchoredAtom2607 chi ∧
      ¬Fin15AnchoredAtom2782 chi ∧
      ¬Fin15AnchoredAtom2896 chi ∧
      ¬Fin15AnchoredAtom2899 chi ∧
      ¬Fin15AnchoredAtom2900 chi ∧
      ¬Fin15AnchoredAtom2914 chi ∧
      ¬Fin15AnchoredAtom2915 chi ∧
      ¬Fin15AnchoredAtom2921 chi ∧
      ¬Fin15AnchoredAtom2999 chi ∧
      ¬Fin15AnchoredAtom3000 chi ∧
      ¬Fin15AnchoredAtom3006 chi ∧
      ¬Fin15AnchoredAtom3037 chi ∧
      ¬Fin15AnchoredAtom3284 chi ∧
      ¬Fin15AnchoredAtom3285 chi ∧
      ¬Fin15AnchoredAtom3291 chi ∧
      ¬Fin15AnchoredAtom3322 chi ∧
      ¬Fin15AnchoredAtom3497 chi ∧
      ¬Fin15AnchoredAtom3779 chi ∧
      ¬Fin15AnchoredAtom3780 chi ∧
      ¬Fin15AnchoredAtom3786 chi ∧
      ¬Fin15AnchoredAtom3817 chi ∧
      ¬Fin15AnchoredAtom3992 chi ∧
      ¬Fin15AnchoredAtom4532 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 7, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25751
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1834 Fin15AnchoredAtom1837 Fin15AnchoredAtom1840
    Fin15AnchoredAtom1841 Fin15AnchoredAtom1861 Fin15AnchoredAtom1864 Fin15AnchoredAtom1865
    Fin15AnchoredAtom1879 Fin15AnchoredAtom1880 Fin15AnchoredAtom1886 Fin15AnchoredAtom1961
    Fin15AnchoredAtom1964 Fin15AnchoredAtom1965 Fin15AnchoredAtom1979 Fin15AnchoredAtom1980
    Fin15AnchoredAtom1986 Fin15AnchoredAtom2064 Fin15AnchoredAtom2065 Fin15AnchoredAtom2071
    Fin15AnchoredAtom2102 Fin15AnchoredAtom2181 Fin15AnchoredAtom2184 Fin15AnchoredAtom2185
    Fin15AnchoredAtom2199 Fin15AnchoredAtom2200 Fin15AnchoredAtom2206 Fin15AnchoredAtom2284
    Fin15AnchoredAtom2285 Fin15AnchoredAtom2291 Fin15AnchoredAtom2322 Fin15AnchoredAtom2569
    Fin15AnchoredAtom2570 Fin15AnchoredAtom2576 Fin15AnchoredAtom2607 Fin15AnchoredAtom2782
    Fin15AnchoredAtom2896 Fin15AnchoredAtom2899 Fin15AnchoredAtom2900 Fin15AnchoredAtom2914
    Fin15AnchoredAtom2915 Fin15AnchoredAtom2921 Fin15AnchoredAtom2999 Fin15AnchoredAtom3000
    Fin15AnchoredAtom3006 Fin15AnchoredAtom3037 Fin15AnchoredAtom3284 Fin15AnchoredAtom3285
    Fin15AnchoredAtom3291 Fin15AnchoredAtom3322 Fin15AnchoredAtom3497 Fin15AnchoredAtom3779
    Fin15AnchoredAtom3780 Fin15AnchoredAtom3786 Fin15AnchoredAtom3817 Fin15AnchoredAtom3992
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

theorem fin15Anchored_clause30699 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom1886 chi ∧
      ¬Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom1984 chi ∧
      ¬Fin15AnchoredAtom1985 chi ∧
      ¬Fin15AnchoredAtom1986 chi ∧
      ¬Fin15AnchoredAtom2069 chi ∧
      ¬Fin15AnchoredAtom2070 chi ∧
      ¬Fin15AnchoredAtom2071 chi ∧
      ¬Fin15AnchoredAtom2106 chi ∧
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
      ¬Fin15AnchoredAtom2574 chi ∧
      ¬Fin15AnchoredAtom2575 chi ∧
      ¬Fin15AnchoredAtom2576 chi ∧
      ¬Fin15AnchoredAtom2611 chi ∧
      ¬Fin15AnchoredAtom2786 chi ∧
      ¬Fin15AnchoredAtom2898 chi ∧
      ¬Fin15AnchoredAtom2899 chi ∧
      ¬Fin15AnchoredAtom2900 chi ∧
      ¬Fin15AnchoredAtom2919 chi ∧
      ¬Fin15AnchoredAtom2920 chi ∧
      ¬Fin15AnchoredAtom2921 chi ∧
      ¬Fin15AnchoredAtom3004 chi ∧
      ¬Fin15AnchoredAtom3005 chi ∧
      ¬Fin15AnchoredAtom3006 chi ∧
      ¬Fin15AnchoredAtom3041 chi ∧
      ¬Fin15AnchoredAtom3289 chi ∧
      ¬Fin15AnchoredAtom3290 chi ∧
      ¬Fin15AnchoredAtom3291 chi ∧
      ¬Fin15AnchoredAtom3326 chi ∧
      ¬Fin15AnchoredAtom3501 chi ∧
      ¬Fin15AnchoredAtom3784 chi ∧
      ¬Fin15AnchoredAtom3785 chi ∧
      ¬Fin15AnchoredAtom3786 chi ∧
      ¬Fin15AnchoredAtom3821 chi ∧
      ¬Fin15AnchoredAtom3996 chi ∧
      ¬Fin15AnchoredAtom4536 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 7, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask28823
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1834 Fin15AnchoredAtom1839 Fin15AnchoredAtom1840
    Fin15AnchoredAtom1841 Fin15AnchoredAtom1863 Fin15AnchoredAtom1864 Fin15AnchoredAtom1865
    Fin15AnchoredAtom1884 Fin15AnchoredAtom1885 Fin15AnchoredAtom1886 Fin15AnchoredAtom1963
    Fin15AnchoredAtom1964 Fin15AnchoredAtom1965 Fin15AnchoredAtom1984 Fin15AnchoredAtom1985
    Fin15AnchoredAtom1986 Fin15AnchoredAtom2069 Fin15AnchoredAtom2070 Fin15AnchoredAtom2071
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2183 Fin15AnchoredAtom2184 Fin15AnchoredAtom2185
    Fin15AnchoredAtom2204 Fin15AnchoredAtom2205 Fin15AnchoredAtom2206 Fin15AnchoredAtom2289
    Fin15AnchoredAtom2290 Fin15AnchoredAtom2291 Fin15AnchoredAtom2326 Fin15AnchoredAtom2574
    Fin15AnchoredAtom2575 Fin15AnchoredAtom2576 Fin15AnchoredAtom2611 Fin15AnchoredAtom2786
    Fin15AnchoredAtom2898 Fin15AnchoredAtom2899 Fin15AnchoredAtom2900 Fin15AnchoredAtom2919
    Fin15AnchoredAtom2920 Fin15AnchoredAtom2921 Fin15AnchoredAtom3004 Fin15AnchoredAtom3005
    Fin15AnchoredAtom3006 Fin15AnchoredAtom3041 Fin15AnchoredAtom3289 Fin15AnchoredAtom3290
    Fin15AnchoredAtom3291 Fin15AnchoredAtom3326 Fin15AnchoredAtom3501 Fin15AnchoredAtom3784
    Fin15AnchoredAtom3785 Fin15AnchoredAtom3786 Fin15AnchoredAtom3821 Fin15AnchoredAtom3996
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

theorem fin15Anchored_clause30700 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom1978 chi ∧
      ¬Fin15AnchoredAtom1979 chi ∧
      ¬Fin15AnchoredAtom1984 chi ∧
      ¬Fin15AnchoredAtom2088 chi ∧
      ¬Fin15AnchoredAtom2089 chi ∧
      ¬Fin15AnchoredAtom2094 chi ∧
      ¬Fin15AnchoredAtom2100 chi ∧
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
      ¬Fin15AnchoredAtom2593 chi ∧
      ¬Fin15AnchoredAtom2594 chi ∧
      ¬Fin15AnchoredAtom2599 chi ∧
      ¬Fin15AnchoredAtom2605 chi ∧
      ¬Fin15AnchoredAtom2810 chi ∧
      ¬Fin15AnchoredAtom2907 chi ∧
      ¬Fin15AnchoredAtom2909 chi ∧
      ¬Fin15AnchoredAtom2910 chi ∧
      ¬Fin15AnchoredAtom2913 chi ∧
      ¬Fin15AnchoredAtom2914 chi ∧
      ¬Fin15AnchoredAtom2919 chi ∧
      ¬Fin15AnchoredAtom3023 chi ∧
      ¬Fin15AnchoredAtom3024 chi ∧
      ¬Fin15AnchoredAtom3029 chi ∧
      ¬Fin15AnchoredAtom3035 chi ∧
      ¬Fin15AnchoredAtom3308 chi ∧
      ¬Fin15AnchoredAtom3309 chi ∧
      ¬Fin15AnchoredAtom3314 chi ∧
      ¬Fin15AnchoredAtom3320 chi ∧
      ¬Fin15AnchoredAtom3525 chi ∧
      ¬Fin15AnchoredAtom3803 chi ∧
      ¬Fin15AnchoredAtom3804 chi ∧
      ¬Fin15AnchoredAtom3809 chi ∧
      ¬Fin15AnchoredAtom3815 chi ∧
      ¬Fin15AnchoredAtom4020 chi ∧
      ¬Fin15AnchoredAtom4560 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13847
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1836 Fin15AnchoredAtom1837 Fin15AnchoredAtom1839
    Fin15AnchoredAtom1840 Fin15AnchoredAtom1872 Fin15AnchoredAtom1874 Fin15AnchoredAtom1875
    Fin15AnchoredAtom1878 Fin15AnchoredAtom1879 Fin15AnchoredAtom1884 Fin15AnchoredAtom1972
    Fin15AnchoredAtom1974 Fin15AnchoredAtom1975 Fin15AnchoredAtom1978 Fin15AnchoredAtom1979
    Fin15AnchoredAtom1984 Fin15AnchoredAtom2088 Fin15AnchoredAtom2089 Fin15AnchoredAtom2094
    Fin15AnchoredAtom2100 Fin15AnchoredAtom2192 Fin15AnchoredAtom2194 Fin15AnchoredAtom2195
    Fin15AnchoredAtom2198 Fin15AnchoredAtom2199 Fin15AnchoredAtom2204 Fin15AnchoredAtom2308
    Fin15AnchoredAtom2309 Fin15AnchoredAtom2314 Fin15AnchoredAtom2320 Fin15AnchoredAtom2593
    Fin15AnchoredAtom2594 Fin15AnchoredAtom2599 Fin15AnchoredAtom2605 Fin15AnchoredAtom2810
    Fin15AnchoredAtom2907 Fin15AnchoredAtom2909 Fin15AnchoredAtom2910 Fin15AnchoredAtom2913
    Fin15AnchoredAtom2914 Fin15AnchoredAtom2919 Fin15AnchoredAtom3023 Fin15AnchoredAtom3024
    Fin15AnchoredAtom3029 Fin15AnchoredAtom3035 Fin15AnchoredAtom3308 Fin15AnchoredAtom3309
    Fin15AnchoredAtom3314 Fin15AnchoredAtom3320 Fin15AnchoredAtom3525 Fin15AnchoredAtom3803
    Fin15AnchoredAtom3804 Fin15AnchoredAtom3809 Fin15AnchoredAtom3815 Fin15AnchoredAtom4020
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

theorem fin15Anchored_clause30701 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom1976 chi ∧
      ¬Fin15AnchoredAtom1978 chi ∧
      ¬Fin15AnchoredAtom1980 chi ∧
      ¬Fin15AnchoredAtom1985 chi ∧
      ¬Fin15AnchoredAtom2088 chi ∧
      ¬Fin15AnchoredAtom2090 chi ∧
      ¬Fin15AnchoredAtom2095 chi ∧
      ¬Fin15AnchoredAtom2101 chi ∧
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
      ¬Fin15AnchoredAtom2593 chi ∧
      ¬Fin15AnchoredAtom2595 chi ∧
      ¬Fin15AnchoredAtom2600 chi ∧
      ¬Fin15AnchoredAtom2606 chi ∧
      ¬Fin15AnchoredAtom2811 chi ∧
      ¬Fin15AnchoredAtom2907 chi ∧
      ¬Fin15AnchoredAtom2909 chi ∧
      ¬Fin15AnchoredAtom2911 chi ∧
      ¬Fin15AnchoredAtom2913 chi ∧
      ¬Fin15AnchoredAtom2915 chi ∧
      ¬Fin15AnchoredAtom2920 chi ∧
      ¬Fin15AnchoredAtom3023 chi ∧
      ¬Fin15AnchoredAtom3025 chi ∧
      ¬Fin15AnchoredAtom3030 chi ∧
      ¬Fin15AnchoredAtom3036 chi ∧
      ¬Fin15AnchoredAtom3308 chi ∧
      ¬Fin15AnchoredAtom3310 chi ∧
      ¬Fin15AnchoredAtom3315 chi ∧
      ¬Fin15AnchoredAtom3321 chi ∧
      ¬Fin15AnchoredAtom3526 chi ∧
      ¬Fin15AnchoredAtom3803 chi ∧
      ¬Fin15AnchoredAtom3805 chi ∧
      ¬Fin15AnchoredAtom3810 chi ∧
      ¬Fin15AnchoredAtom3816 chi ∧
      ¬Fin15AnchoredAtom4021 chi ∧
      ¬Fin15AnchoredAtom4561 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 9, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22039
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1836 Fin15AnchoredAtom1837 Fin15AnchoredAtom1839
    Fin15AnchoredAtom1841 Fin15AnchoredAtom1872 Fin15AnchoredAtom1874 Fin15AnchoredAtom1876
    Fin15AnchoredAtom1878 Fin15AnchoredAtom1880 Fin15AnchoredAtom1885 Fin15AnchoredAtom1972
    Fin15AnchoredAtom1974 Fin15AnchoredAtom1976 Fin15AnchoredAtom1978 Fin15AnchoredAtom1980
    Fin15AnchoredAtom1985 Fin15AnchoredAtom2088 Fin15AnchoredAtom2090 Fin15AnchoredAtom2095
    Fin15AnchoredAtom2101 Fin15AnchoredAtom2192 Fin15AnchoredAtom2194 Fin15AnchoredAtom2196
    Fin15AnchoredAtom2198 Fin15AnchoredAtom2200 Fin15AnchoredAtom2205 Fin15AnchoredAtom2308
    Fin15AnchoredAtom2310 Fin15AnchoredAtom2315 Fin15AnchoredAtom2321 Fin15AnchoredAtom2593
    Fin15AnchoredAtom2595 Fin15AnchoredAtom2600 Fin15AnchoredAtom2606 Fin15AnchoredAtom2811
    Fin15AnchoredAtom2907 Fin15AnchoredAtom2909 Fin15AnchoredAtom2911 Fin15AnchoredAtom2913
    Fin15AnchoredAtom2915 Fin15AnchoredAtom2920 Fin15AnchoredAtom3023 Fin15AnchoredAtom3025
    Fin15AnchoredAtom3030 Fin15AnchoredAtom3036 Fin15AnchoredAtom3308 Fin15AnchoredAtom3310
    Fin15AnchoredAtom3315 Fin15AnchoredAtom3321 Fin15AnchoredAtom3526 Fin15AnchoredAtom3803
    Fin15AnchoredAtom3805 Fin15AnchoredAtom3810 Fin15AnchoredAtom3816 Fin15AnchoredAtom4021
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

theorem fin15Anchored_clause30702 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom1886 chi ∧
      ¬Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom1976 chi ∧
      ¬Fin15AnchoredAtom1979 chi ∧
      ¬Fin15AnchoredAtom1980 chi ∧
      ¬Fin15AnchoredAtom1986 chi ∧
      ¬Fin15AnchoredAtom2089 chi ∧
      ¬Fin15AnchoredAtom2090 chi ∧
      ¬Fin15AnchoredAtom2096 chi ∧
      ¬Fin15AnchoredAtom2102 chi ∧
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
      ¬Fin15AnchoredAtom2594 chi ∧
      ¬Fin15AnchoredAtom2595 chi ∧
      ¬Fin15AnchoredAtom2601 chi ∧
      ¬Fin15AnchoredAtom2607 chi ∧
      ¬Fin15AnchoredAtom2812 chi ∧
      ¬Fin15AnchoredAtom2907 chi ∧
      ¬Fin15AnchoredAtom2910 chi ∧
      ¬Fin15AnchoredAtom2911 chi ∧
      ¬Fin15AnchoredAtom2914 chi ∧
      ¬Fin15AnchoredAtom2915 chi ∧
      ¬Fin15AnchoredAtom2921 chi ∧
      ¬Fin15AnchoredAtom3024 chi ∧
      ¬Fin15AnchoredAtom3025 chi ∧
      ¬Fin15AnchoredAtom3031 chi ∧
      ¬Fin15AnchoredAtom3037 chi ∧
      ¬Fin15AnchoredAtom3309 chi ∧
      ¬Fin15AnchoredAtom3310 chi ∧
      ¬Fin15AnchoredAtom3316 chi ∧
      ¬Fin15AnchoredAtom3322 chi ∧
      ¬Fin15AnchoredAtom3527 chi ∧
      ¬Fin15AnchoredAtom3804 chi ∧
      ¬Fin15AnchoredAtom3805 chi ∧
      ¬Fin15AnchoredAtom3811 chi ∧
      ¬Fin15AnchoredAtom3817 chi ∧
      ¬Fin15AnchoredAtom4022 chi ∧
      ¬Fin15AnchoredAtom4562 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 9, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26135
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1836 Fin15AnchoredAtom1837 Fin15AnchoredAtom1840
    Fin15AnchoredAtom1841 Fin15AnchoredAtom1872 Fin15AnchoredAtom1875 Fin15AnchoredAtom1876
    Fin15AnchoredAtom1879 Fin15AnchoredAtom1880 Fin15AnchoredAtom1886 Fin15AnchoredAtom1972
    Fin15AnchoredAtom1975 Fin15AnchoredAtom1976 Fin15AnchoredAtom1979 Fin15AnchoredAtom1980
    Fin15AnchoredAtom1986 Fin15AnchoredAtom2089 Fin15AnchoredAtom2090 Fin15AnchoredAtom2096
    Fin15AnchoredAtom2102 Fin15AnchoredAtom2192 Fin15AnchoredAtom2195 Fin15AnchoredAtom2196
    Fin15AnchoredAtom2199 Fin15AnchoredAtom2200 Fin15AnchoredAtom2206 Fin15AnchoredAtom2309
    Fin15AnchoredAtom2310 Fin15AnchoredAtom2316 Fin15AnchoredAtom2322 Fin15AnchoredAtom2594
    Fin15AnchoredAtom2595 Fin15AnchoredAtom2601 Fin15AnchoredAtom2607 Fin15AnchoredAtom2812
    Fin15AnchoredAtom2907 Fin15AnchoredAtom2910 Fin15AnchoredAtom2911 Fin15AnchoredAtom2914
    Fin15AnchoredAtom2915 Fin15AnchoredAtom2921 Fin15AnchoredAtom3024 Fin15AnchoredAtom3025
    Fin15AnchoredAtom3031 Fin15AnchoredAtom3037 Fin15AnchoredAtom3309 Fin15AnchoredAtom3310
    Fin15AnchoredAtom3316 Fin15AnchoredAtom3322 Fin15AnchoredAtom3527 Fin15AnchoredAtom3804
    Fin15AnchoredAtom3805 Fin15AnchoredAtom3811 Fin15AnchoredAtom3817 Fin15AnchoredAtom4022
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

theorem fin15Anchored_clause30703 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom1886 chi ∧
      ¬Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom1976 chi ∧
      ¬Fin15AnchoredAtom1984 chi ∧
      ¬Fin15AnchoredAtom1985 chi ∧
      ¬Fin15AnchoredAtom1986 chi ∧
      ¬Fin15AnchoredAtom2094 chi ∧
      ¬Fin15AnchoredAtom2095 chi ∧
      ¬Fin15AnchoredAtom2096 chi ∧
      ¬Fin15AnchoredAtom2106 chi ∧
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
      ¬Fin15AnchoredAtom2599 chi ∧
      ¬Fin15AnchoredAtom2600 chi ∧
      ¬Fin15AnchoredAtom2601 chi ∧
      ¬Fin15AnchoredAtom2611 chi ∧
      ¬Fin15AnchoredAtom2816 chi ∧
      ¬Fin15AnchoredAtom2909 chi ∧
      ¬Fin15AnchoredAtom2910 chi ∧
      ¬Fin15AnchoredAtom2911 chi ∧
      ¬Fin15AnchoredAtom2919 chi ∧
      ¬Fin15AnchoredAtom2920 chi ∧
      ¬Fin15AnchoredAtom2921 chi ∧
      ¬Fin15AnchoredAtom3029 chi ∧
      ¬Fin15AnchoredAtom3030 chi ∧
      ¬Fin15AnchoredAtom3031 chi ∧
      ¬Fin15AnchoredAtom3041 chi ∧
      ¬Fin15AnchoredAtom3314 chi ∧
      ¬Fin15AnchoredAtom3315 chi ∧
      ¬Fin15AnchoredAtom3316 chi ∧
      ¬Fin15AnchoredAtom3326 chi ∧
      ¬Fin15AnchoredAtom3531 chi ∧
      ¬Fin15AnchoredAtom3809 chi ∧
      ¬Fin15AnchoredAtom3810 chi ∧
      ¬Fin15AnchoredAtom3811 chi ∧
      ¬Fin15AnchoredAtom3821 chi ∧
      ¬Fin15AnchoredAtom4026 chi ∧
      ¬Fin15AnchoredAtom4566 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 9, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29207
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1836 Fin15AnchoredAtom1839 Fin15AnchoredAtom1840
    Fin15AnchoredAtom1841 Fin15AnchoredAtom1874 Fin15AnchoredAtom1875 Fin15AnchoredAtom1876
    Fin15AnchoredAtom1884 Fin15AnchoredAtom1885 Fin15AnchoredAtom1886 Fin15AnchoredAtom1974
    Fin15AnchoredAtom1975 Fin15AnchoredAtom1976 Fin15AnchoredAtom1984 Fin15AnchoredAtom1985
    Fin15AnchoredAtom1986 Fin15AnchoredAtom2094 Fin15AnchoredAtom2095 Fin15AnchoredAtom2096
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2194 Fin15AnchoredAtom2195 Fin15AnchoredAtom2196
    Fin15AnchoredAtom2204 Fin15AnchoredAtom2205 Fin15AnchoredAtom2206 Fin15AnchoredAtom2314
    Fin15AnchoredAtom2315 Fin15AnchoredAtom2316 Fin15AnchoredAtom2326 Fin15AnchoredAtom2599
    Fin15AnchoredAtom2600 Fin15AnchoredAtom2601 Fin15AnchoredAtom2611 Fin15AnchoredAtom2816
    Fin15AnchoredAtom2909 Fin15AnchoredAtom2910 Fin15AnchoredAtom2911 Fin15AnchoredAtom2919
    Fin15AnchoredAtom2920 Fin15AnchoredAtom2921 Fin15AnchoredAtom3029 Fin15AnchoredAtom3030
    Fin15AnchoredAtom3031 Fin15AnchoredAtom3041 Fin15AnchoredAtom3314 Fin15AnchoredAtom3315
    Fin15AnchoredAtom3316 Fin15AnchoredAtom3326 Fin15AnchoredAtom3531 Fin15AnchoredAtom3809
    Fin15AnchoredAtom3810 Fin15AnchoredAtom3811 Fin15AnchoredAtom3821 Fin15AnchoredAtom4026
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

theorem fin15Anchored_clause30704 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom1886 chi ∧
      ¬Fin15AnchoredAtom1978 chi ∧
      ¬Fin15AnchoredAtom1979 chi ∧
      ¬Fin15AnchoredAtom1980 chi ∧
      ¬Fin15AnchoredAtom1984 chi ∧
      ¬Fin15AnchoredAtom1985 chi ∧
      ¬Fin15AnchoredAtom1986 chi ∧
      ¬Fin15AnchoredAtom2100 chi ∧
      ¬Fin15AnchoredAtom2101 chi ∧
      ¬Fin15AnchoredAtom2102 chi ∧
      ¬Fin15AnchoredAtom2106 chi ∧
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
      ¬Fin15AnchoredAtom2605 chi ∧
      ¬Fin15AnchoredAtom2606 chi ∧
      ¬Fin15AnchoredAtom2607 chi ∧
      ¬Fin15AnchoredAtom2611 chi ∧
      ¬Fin15AnchoredAtom2820 chi ∧
      ¬Fin15AnchoredAtom2913 chi ∧
      ¬Fin15AnchoredAtom2914 chi ∧
      ¬Fin15AnchoredAtom2915 chi ∧
      ¬Fin15AnchoredAtom2919 chi ∧
      ¬Fin15AnchoredAtom2920 chi ∧
      ¬Fin15AnchoredAtom2921 chi ∧
      ¬Fin15AnchoredAtom3035 chi ∧
      ¬Fin15AnchoredAtom3036 chi ∧
      ¬Fin15AnchoredAtom3037 chi ∧
      ¬Fin15AnchoredAtom3041 chi ∧
      ¬Fin15AnchoredAtom3320 chi ∧
      ¬Fin15AnchoredAtom3321 chi ∧
      ¬Fin15AnchoredAtom3322 chi ∧
      ¬Fin15AnchoredAtom3326 chi ∧
      ¬Fin15AnchoredAtom3535 chi ∧
      ¬Fin15AnchoredAtom3815 chi ∧
      ¬Fin15AnchoredAtom3816 chi ∧
      ¬Fin15AnchoredAtom3817 chi ∧
      ¬Fin15AnchoredAtom3821 chi ∧
      ¬Fin15AnchoredAtom4030 chi ∧
      ¬Fin15AnchoredAtom4570 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 4, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29719
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1837 Fin15AnchoredAtom1839 Fin15AnchoredAtom1840
    Fin15AnchoredAtom1841 Fin15AnchoredAtom1878 Fin15AnchoredAtom1879 Fin15AnchoredAtom1880
    Fin15AnchoredAtom1884 Fin15AnchoredAtom1885 Fin15AnchoredAtom1886 Fin15AnchoredAtom1978
    Fin15AnchoredAtom1979 Fin15AnchoredAtom1980 Fin15AnchoredAtom1984 Fin15AnchoredAtom1985
    Fin15AnchoredAtom1986 Fin15AnchoredAtom2100 Fin15AnchoredAtom2101 Fin15AnchoredAtom2102
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2198 Fin15AnchoredAtom2199 Fin15AnchoredAtom2200
    Fin15AnchoredAtom2204 Fin15AnchoredAtom2205 Fin15AnchoredAtom2206 Fin15AnchoredAtom2320
    Fin15AnchoredAtom2321 Fin15AnchoredAtom2322 Fin15AnchoredAtom2326 Fin15AnchoredAtom2605
    Fin15AnchoredAtom2606 Fin15AnchoredAtom2607 Fin15AnchoredAtom2611 Fin15AnchoredAtom2820
    Fin15AnchoredAtom2913 Fin15AnchoredAtom2914 Fin15AnchoredAtom2915 Fin15AnchoredAtom2919
    Fin15AnchoredAtom2920 Fin15AnchoredAtom2921 Fin15AnchoredAtom3035 Fin15AnchoredAtom3036
    Fin15AnchoredAtom3037 Fin15AnchoredAtom3041 Fin15AnchoredAtom3320 Fin15AnchoredAtom3321
    Fin15AnchoredAtom3322 Fin15AnchoredAtom3326 Fin15AnchoredAtom3535 Fin15AnchoredAtom3815
    Fin15AnchoredAtom3816 Fin15AnchoredAtom3817 Fin15AnchoredAtom3821 Fin15AnchoredAtom4030
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

theorem fin15Anchored_clause30705 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom1987 chi ∧
      ¬Fin15AnchoredAtom1989 chi ∧
      ¬Fin15AnchoredAtom1990 chi ∧
      ¬Fin15AnchoredAtom1996 chi ∧
      ¬Fin15AnchoredAtom1997 chi ∧
      ¬Fin15AnchoredAtom2008 chi ∧
      ¬Fin15AnchoredAtom2024 chi ∧
      ¬Fin15AnchoredAtom2025 chi ∧
      ¬Fin15AnchoredAtom2036 chi ∧
      ¬Fin15AnchoredAtom2057 chi ∧
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
      ¬Fin15AnchoredAtom2613 chi ∧
      ¬Fin15AnchoredAtom2614 chi ∧
      ¬Fin15AnchoredAtom2625 chi ∧
      ¬Fin15AnchoredAtom2646 chi ∧
      ¬Fin15AnchoredAtom2702 chi ∧
      ¬Fin15AnchoredAtom2922 chi ∧
      ¬Fin15AnchoredAtom2924 chi ∧
      ¬Fin15AnchoredAtom2925 chi ∧
      ¬Fin15AnchoredAtom2931 chi ∧
      ¬Fin15AnchoredAtom2932 chi ∧
      ¬Fin15AnchoredAtom2943 chi ∧
      ¬Fin15AnchoredAtom2959 chi ∧
      ¬Fin15AnchoredAtom2960 chi ∧
      ¬Fin15AnchoredAtom2971 chi ∧
      ¬Fin15AnchoredAtom2992 chi ∧
      ¬Fin15AnchoredAtom3328 chi ∧
      ¬Fin15AnchoredAtom3329 chi ∧
      ¬Fin15AnchoredAtom3340 chi ∧
      ¬Fin15AnchoredAtom3361 chi ∧
      ¬Fin15AnchoredAtom3417 chi ∧
      ¬Fin15AnchoredAtom3823 chi ∧
      ¬Fin15AnchoredAtom3824 chi ∧
      ¬Fin15AnchoredAtom3835 chi ∧
      ¬Fin15AnchoredAtom3856 chi ∧
      ¬Fin15AnchoredAtom3912 chi ∧
      ¬Fin15AnchoredAtom4578 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 5, 6, 7, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask01767
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1842 Fin15AnchoredAtom1843 Fin15AnchoredAtom1845
    Fin15AnchoredAtom1846 Fin15AnchoredAtom1851 Fin15AnchoredAtom1853 Fin15AnchoredAtom1854
    Fin15AnchoredAtom1860 Fin15AnchoredAtom1861 Fin15AnchoredAtom1872 Fin15AnchoredAtom1987
    Fin15AnchoredAtom1989 Fin15AnchoredAtom1990 Fin15AnchoredAtom1996 Fin15AnchoredAtom1997
    Fin15AnchoredAtom2008 Fin15AnchoredAtom2024 Fin15AnchoredAtom2025 Fin15AnchoredAtom2036
    Fin15AnchoredAtom2057 Fin15AnchoredAtom2207 Fin15AnchoredAtom2209 Fin15AnchoredAtom2210
    Fin15AnchoredAtom2216 Fin15AnchoredAtom2217 Fin15AnchoredAtom2228 Fin15AnchoredAtom2244
    Fin15AnchoredAtom2245 Fin15AnchoredAtom2256 Fin15AnchoredAtom2277 Fin15AnchoredAtom2613
    Fin15AnchoredAtom2614 Fin15AnchoredAtom2625 Fin15AnchoredAtom2646 Fin15AnchoredAtom2702
    Fin15AnchoredAtom2922 Fin15AnchoredAtom2924 Fin15AnchoredAtom2925 Fin15AnchoredAtom2931
    Fin15AnchoredAtom2932 Fin15AnchoredAtom2943 Fin15AnchoredAtom2959 Fin15AnchoredAtom2960
    Fin15AnchoredAtom2971 Fin15AnchoredAtom2992 Fin15AnchoredAtom3328 Fin15AnchoredAtom3329
    Fin15AnchoredAtom3340 Fin15AnchoredAtom3361 Fin15AnchoredAtom3417 Fin15AnchoredAtom3823
    Fin15AnchoredAtom3824 Fin15AnchoredAtom3835 Fin15AnchoredAtom3856 Fin15AnchoredAtom3912
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

theorem fin15Anchored_clause30706 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom1987 chi ∧
      ¬Fin15AnchoredAtom1989 chi ∧
      ¬Fin15AnchoredAtom1992 chi ∧
      ¬Fin15AnchoredAtom1996 chi ∧
      ¬Fin15AnchoredAtom1999 chi ∧
      ¬Fin15AnchoredAtom2010 chi ∧
      ¬Fin15AnchoredAtom2024 chi ∧
      ¬Fin15AnchoredAtom2027 chi ∧
      ¬Fin15AnchoredAtom2038 chi ∧
      ¬Fin15AnchoredAtom2059 chi ∧
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
      ¬Fin15AnchoredAtom2613 chi ∧
      ¬Fin15AnchoredAtom2616 chi ∧
      ¬Fin15AnchoredAtom2627 chi ∧
      ¬Fin15AnchoredAtom2648 chi ∧
      ¬Fin15AnchoredAtom2704 chi ∧
      ¬Fin15AnchoredAtom2922 chi ∧
      ¬Fin15AnchoredAtom2924 chi ∧
      ¬Fin15AnchoredAtom2927 chi ∧
      ¬Fin15AnchoredAtom2931 chi ∧
      ¬Fin15AnchoredAtom2934 chi ∧
      ¬Fin15AnchoredAtom2945 chi ∧
      ¬Fin15AnchoredAtom2959 chi ∧
      ¬Fin15AnchoredAtom2962 chi ∧
      ¬Fin15AnchoredAtom2973 chi ∧
      ¬Fin15AnchoredAtom2994 chi ∧
      ¬Fin15AnchoredAtom3328 chi ∧
      ¬Fin15AnchoredAtom3331 chi ∧
      ¬Fin15AnchoredAtom3342 chi ∧
      ¬Fin15AnchoredAtom3363 chi ∧
      ¬Fin15AnchoredAtom3419 chi ∧
      ¬Fin15AnchoredAtom3823 chi ∧
      ¬Fin15AnchoredAtom3826 chi ∧
      ¬Fin15AnchoredAtom3837 chi ∧
      ¬Fin15AnchoredAtom3858 chi ∧
      ¬Fin15AnchoredAtom3914 chi ∧
      ¬Fin15AnchoredAtom4580 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 5, 6, 7, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask04839
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1842 Fin15AnchoredAtom1843 Fin15AnchoredAtom1845
    Fin15AnchoredAtom1848 Fin15AnchoredAtom1851 Fin15AnchoredAtom1853 Fin15AnchoredAtom1856
    Fin15AnchoredAtom1860 Fin15AnchoredAtom1863 Fin15AnchoredAtom1874 Fin15AnchoredAtom1987
    Fin15AnchoredAtom1989 Fin15AnchoredAtom1992 Fin15AnchoredAtom1996 Fin15AnchoredAtom1999
    Fin15AnchoredAtom2010 Fin15AnchoredAtom2024 Fin15AnchoredAtom2027 Fin15AnchoredAtom2038
    Fin15AnchoredAtom2059 Fin15AnchoredAtom2207 Fin15AnchoredAtom2209 Fin15AnchoredAtom2212
    Fin15AnchoredAtom2216 Fin15AnchoredAtom2219 Fin15AnchoredAtom2230 Fin15AnchoredAtom2244
    Fin15AnchoredAtom2247 Fin15AnchoredAtom2258 Fin15AnchoredAtom2279 Fin15AnchoredAtom2613
    Fin15AnchoredAtom2616 Fin15AnchoredAtom2627 Fin15AnchoredAtom2648 Fin15AnchoredAtom2704
    Fin15AnchoredAtom2922 Fin15AnchoredAtom2924 Fin15AnchoredAtom2927 Fin15AnchoredAtom2931
    Fin15AnchoredAtom2934 Fin15AnchoredAtom2945 Fin15AnchoredAtom2959 Fin15AnchoredAtom2962
    Fin15AnchoredAtom2973 Fin15AnchoredAtom2994 Fin15AnchoredAtom3328 Fin15AnchoredAtom3331
    Fin15AnchoredAtom3342 Fin15AnchoredAtom3363 Fin15AnchoredAtom3419 Fin15AnchoredAtom3823
    Fin15AnchoredAtom3826 Fin15AnchoredAtom3837 Fin15AnchoredAtom3858 Fin15AnchoredAtom3914
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

theorem fin15Anchored_clause30707 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom1987 chi ∧
      ¬Fin15AnchoredAtom1989 chi ∧
      ¬Fin15AnchoredAtom1993 chi ∧
      ¬Fin15AnchoredAtom1996 chi ∧
      ¬Fin15AnchoredAtom2000 chi ∧
      ¬Fin15AnchoredAtom2011 chi ∧
      ¬Fin15AnchoredAtom2024 chi ∧
      ¬Fin15AnchoredAtom2028 chi ∧
      ¬Fin15AnchoredAtom2039 chi ∧
      ¬Fin15AnchoredAtom2060 chi ∧
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
      ¬Fin15AnchoredAtom2613 chi ∧
      ¬Fin15AnchoredAtom2617 chi ∧
      ¬Fin15AnchoredAtom2628 chi ∧
      ¬Fin15AnchoredAtom2649 chi ∧
      ¬Fin15AnchoredAtom2705 chi ∧
      ¬Fin15AnchoredAtom2922 chi ∧
      ¬Fin15AnchoredAtom2924 chi ∧
      ¬Fin15AnchoredAtom2928 chi ∧
      ¬Fin15AnchoredAtom2931 chi ∧
      ¬Fin15AnchoredAtom2935 chi ∧
      ¬Fin15AnchoredAtom2946 chi ∧
      ¬Fin15AnchoredAtom2959 chi ∧
      ¬Fin15AnchoredAtom2963 chi ∧
      ¬Fin15AnchoredAtom2974 chi ∧
      ¬Fin15AnchoredAtom2995 chi ∧
      ¬Fin15AnchoredAtom3328 chi ∧
      ¬Fin15AnchoredAtom3332 chi ∧
      ¬Fin15AnchoredAtom3343 chi ∧
      ¬Fin15AnchoredAtom3364 chi ∧
      ¬Fin15AnchoredAtom3420 chi ∧
      ¬Fin15AnchoredAtom3823 chi ∧
      ¬Fin15AnchoredAtom3827 chi ∧
      ¬Fin15AnchoredAtom3838 chi ∧
      ¬Fin15AnchoredAtom3859 chi ∧
      ¬Fin15AnchoredAtom3915 chi ∧
      ¬Fin15AnchoredAtom4581 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 5, 6, 7, 9, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask08935
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1842 Fin15AnchoredAtom1843 Fin15AnchoredAtom1845
    Fin15AnchoredAtom1849 Fin15AnchoredAtom1851 Fin15AnchoredAtom1853 Fin15AnchoredAtom1857
    Fin15AnchoredAtom1860 Fin15AnchoredAtom1864 Fin15AnchoredAtom1875 Fin15AnchoredAtom1987
    Fin15AnchoredAtom1989 Fin15AnchoredAtom1993 Fin15AnchoredAtom1996 Fin15AnchoredAtom2000
    Fin15AnchoredAtom2011 Fin15AnchoredAtom2024 Fin15AnchoredAtom2028 Fin15AnchoredAtom2039
    Fin15AnchoredAtom2060 Fin15AnchoredAtom2207 Fin15AnchoredAtom2209 Fin15AnchoredAtom2213
    Fin15AnchoredAtom2216 Fin15AnchoredAtom2220 Fin15AnchoredAtom2231 Fin15AnchoredAtom2244
    Fin15AnchoredAtom2248 Fin15AnchoredAtom2259 Fin15AnchoredAtom2280 Fin15AnchoredAtom2613
    Fin15AnchoredAtom2617 Fin15AnchoredAtom2628 Fin15AnchoredAtom2649 Fin15AnchoredAtom2705
    Fin15AnchoredAtom2922 Fin15AnchoredAtom2924 Fin15AnchoredAtom2928 Fin15AnchoredAtom2931
    Fin15AnchoredAtom2935 Fin15AnchoredAtom2946 Fin15AnchoredAtom2959 Fin15AnchoredAtom2963
    Fin15AnchoredAtom2974 Fin15AnchoredAtom2995 Fin15AnchoredAtom3328 Fin15AnchoredAtom3332
    Fin15AnchoredAtom3343 Fin15AnchoredAtom3364 Fin15AnchoredAtom3420 Fin15AnchoredAtom3823
    Fin15AnchoredAtom3827 Fin15AnchoredAtom3838 Fin15AnchoredAtom3859 Fin15AnchoredAtom3915
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

theorem fin15Anchored_clause30708 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom1987 chi ∧
      ¬Fin15AnchoredAtom1989 chi ∧
      ¬Fin15AnchoredAtom1994 chi ∧
      ¬Fin15AnchoredAtom1996 chi ∧
      ¬Fin15AnchoredAtom2001 chi ∧
      ¬Fin15AnchoredAtom2012 chi ∧
      ¬Fin15AnchoredAtom2024 chi ∧
      ¬Fin15AnchoredAtom2029 chi ∧
      ¬Fin15AnchoredAtom2040 chi ∧
      ¬Fin15AnchoredAtom2061 chi ∧
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
      ¬Fin15AnchoredAtom2613 chi ∧
      ¬Fin15AnchoredAtom2618 chi ∧
      ¬Fin15AnchoredAtom2629 chi ∧
      ¬Fin15AnchoredAtom2650 chi ∧
      ¬Fin15AnchoredAtom2706 chi ∧
      ¬Fin15AnchoredAtom2922 chi ∧
      ¬Fin15AnchoredAtom2924 chi ∧
      ¬Fin15AnchoredAtom2929 chi ∧
      ¬Fin15AnchoredAtom2931 chi ∧
      ¬Fin15AnchoredAtom2936 chi ∧
      ¬Fin15AnchoredAtom2947 chi ∧
      ¬Fin15AnchoredAtom2959 chi ∧
      ¬Fin15AnchoredAtom2964 chi ∧
      ¬Fin15AnchoredAtom2975 chi ∧
      ¬Fin15AnchoredAtom2996 chi ∧
      ¬Fin15AnchoredAtom3328 chi ∧
      ¬Fin15AnchoredAtom3333 chi ∧
      ¬Fin15AnchoredAtom3344 chi ∧
      ¬Fin15AnchoredAtom3365 chi ∧
      ¬Fin15AnchoredAtom3421 chi ∧
      ¬Fin15AnchoredAtom3823 chi ∧
      ¬Fin15AnchoredAtom3828 chi ∧
      ¬Fin15AnchoredAtom3839 chi ∧
      ¬Fin15AnchoredAtom3860 chi ∧
      ¬Fin15AnchoredAtom3916 chi ∧
      ¬Fin15AnchoredAtom4582 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 5, 6, 7, 9, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17127
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1842 Fin15AnchoredAtom1843 Fin15AnchoredAtom1845
    Fin15AnchoredAtom1850 Fin15AnchoredAtom1851 Fin15AnchoredAtom1853 Fin15AnchoredAtom1858
    Fin15AnchoredAtom1860 Fin15AnchoredAtom1865 Fin15AnchoredAtom1876 Fin15AnchoredAtom1987
    Fin15AnchoredAtom1989 Fin15AnchoredAtom1994 Fin15AnchoredAtom1996 Fin15AnchoredAtom2001
    Fin15AnchoredAtom2012 Fin15AnchoredAtom2024 Fin15AnchoredAtom2029 Fin15AnchoredAtom2040
    Fin15AnchoredAtom2061 Fin15AnchoredAtom2207 Fin15AnchoredAtom2209 Fin15AnchoredAtom2214
    Fin15AnchoredAtom2216 Fin15AnchoredAtom2221 Fin15AnchoredAtom2232 Fin15AnchoredAtom2244
    Fin15AnchoredAtom2249 Fin15AnchoredAtom2260 Fin15AnchoredAtom2281 Fin15AnchoredAtom2613
    Fin15AnchoredAtom2618 Fin15AnchoredAtom2629 Fin15AnchoredAtom2650 Fin15AnchoredAtom2706
    Fin15AnchoredAtom2922 Fin15AnchoredAtom2924 Fin15AnchoredAtom2929 Fin15AnchoredAtom2931
    Fin15AnchoredAtom2936 Fin15AnchoredAtom2947 Fin15AnchoredAtom2959 Fin15AnchoredAtom2964
    Fin15AnchoredAtom2975 Fin15AnchoredAtom2996 Fin15AnchoredAtom3328 Fin15AnchoredAtom3333
    Fin15AnchoredAtom3344 Fin15AnchoredAtom3365 Fin15AnchoredAtom3421 Fin15AnchoredAtom3823
    Fin15AnchoredAtom3828 Fin15AnchoredAtom3839 Fin15AnchoredAtom3860 Fin15AnchoredAtom3916
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

theorem fin15Anchored_clause30709 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom1987 chi ∧
      ¬Fin15AnchoredAtom1990 chi ∧
      ¬Fin15AnchoredAtom1992 chi ∧
      ¬Fin15AnchoredAtom1997 chi ∧
      ¬Fin15AnchoredAtom1999 chi ∧
      ¬Fin15AnchoredAtom2014 chi ∧
      ¬Fin15AnchoredAtom2025 chi ∧
      ¬Fin15AnchoredAtom2027 chi ∧
      ¬Fin15AnchoredAtom2042 chi ∧
      ¬Fin15AnchoredAtom2063 chi ∧
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
      ¬Fin15AnchoredAtom2614 chi ∧
      ¬Fin15AnchoredAtom2616 chi ∧
      ¬Fin15AnchoredAtom2631 chi ∧
      ¬Fin15AnchoredAtom2652 chi ∧
      ¬Fin15AnchoredAtom2708 chi ∧
      ¬Fin15AnchoredAtom2922 chi ∧
      ¬Fin15AnchoredAtom2925 chi ∧
      ¬Fin15AnchoredAtom2927 chi ∧
      ¬Fin15AnchoredAtom2932 chi ∧
      ¬Fin15AnchoredAtom2934 chi ∧
      ¬Fin15AnchoredAtom2949 chi ∧
      ¬Fin15AnchoredAtom2960 chi ∧
      ¬Fin15AnchoredAtom2962 chi ∧
      ¬Fin15AnchoredAtom2977 chi ∧
      ¬Fin15AnchoredAtom2998 chi ∧
      ¬Fin15AnchoredAtom3329 chi ∧
      ¬Fin15AnchoredAtom3331 chi ∧
      ¬Fin15AnchoredAtom3346 chi ∧
      ¬Fin15AnchoredAtom3367 chi ∧
      ¬Fin15AnchoredAtom3423 chi ∧
      ¬Fin15AnchoredAtom3824 chi ∧
      ¬Fin15AnchoredAtom3826 chi ∧
      ¬Fin15AnchoredAtom3841 chi ∧
      ¬Fin15AnchoredAtom3862 chi ∧
      ¬Fin15AnchoredAtom3918 chi ∧
      ¬Fin15AnchoredAtom4584 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 5, 6, 7, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05351
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1842 Fin15AnchoredAtom1843 Fin15AnchoredAtom1846
    Fin15AnchoredAtom1848 Fin15AnchoredAtom1851 Fin15AnchoredAtom1854 Fin15AnchoredAtom1856
    Fin15AnchoredAtom1861 Fin15AnchoredAtom1863 Fin15AnchoredAtom1878 Fin15AnchoredAtom1987
    Fin15AnchoredAtom1990 Fin15AnchoredAtom1992 Fin15AnchoredAtom1997 Fin15AnchoredAtom1999
    Fin15AnchoredAtom2014 Fin15AnchoredAtom2025 Fin15AnchoredAtom2027 Fin15AnchoredAtom2042
    Fin15AnchoredAtom2063 Fin15AnchoredAtom2207 Fin15AnchoredAtom2210 Fin15AnchoredAtom2212
    Fin15AnchoredAtom2217 Fin15AnchoredAtom2219 Fin15AnchoredAtom2234 Fin15AnchoredAtom2245
    Fin15AnchoredAtom2247 Fin15AnchoredAtom2262 Fin15AnchoredAtom2283 Fin15AnchoredAtom2614
    Fin15AnchoredAtom2616 Fin15AnchoredAtom2631 Fin15AnchoredAtom2652 Fin15AnchoredAtom2708
    Fin15AnchoredAtom2922 Fin15AnchoredAtom2925 Fin15AnchoredAtom2927 Fin15AnchoredAtom2932
    Fin15AnchoredAtom2934 Fin15AnchoredAtom2949 Fin15AnchoredAtom2960 Fin15AnchoredAtom2962
    Fin15AnchoredAtom2977 Fin15AnchoredAtom2998 Fin15AnchoredAtom3329 Fin15AnchoredAtom3331
    Fin15AnchoredAtom3346 Fin15AnchoredAtom3367 Fin15AnchoredAtom3423 Fin15AnchoredAtom3824
    Fin15AnchoredAtom3826 Fin15AnchoredAtom3841 Fin15AnchoredAtom3862 Fin15AnchoredAtom3918
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

theorem fin15Anchored_clause30710 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom1987 chi ∧
      ¬Fin15AnchoredAtom1990 chi ∧
      ¬Fin15AnchoredAtom1993 chi ∧
      ¬Fin15AnchoredAtom1997 chi ∧
      ¬Fin15AnchoredAtom2000 chi ∧
      ¬Fin15AnchoredAtom2015 chi ∧
      ¬Fin15AnchoredAtom2025 chi ∧
      ¬Fin15AnchoredAtom2028 chi ∧
      ¬Fin15AnchoredAtom2043 chi ∧
      ¬Fin15AnchoredAtom2064 chi ∧
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
      ¬Fin15AnchoredAtom2614 chi ∧
      ¬Fin15AnchoredAtom2617 chi ∧
      ¬Fin15AnchoredAtom2632 chi ∧
      ¬Fin15AnchoredAtom2653 chi ∧
      ¬Fin15AnchoredAtom2709 chi ∧
      ¬Fin15AnchoredAtom2922 chi ∧
      ¬Fin15AnchoredAtom2925 chi ∧
      ¬Fin15AnchoredAtom2928 chi ∧
      ¬Fin15AnchoredAtom2932 chi ∧
      ¬Fin15AnchoredAtom2935 chi ∧
      ¬Fin15AnchoredAtom2950 chi ∧
      ¬Fin15AnchoredAtom2960 chi ∧
      ¬Fin15AnchoredAtom2963 chi ∧
      ¬Fin15AnchoredAtom2978 chi ∧
      ¬Fin15AnchoredAtom2999 chi ∧
      ¬Fin15AnchoredAtom3329 chi ∧
      ¬Fin15AnchoredAtom3332 chi ∧
      ¬Fin15AnchoredAtom3347 chi ∧
      ¬Fin15AnchoredAtom3368 chi ∧
      ¬Fin15AnchoredAtom3424 chi ∧
      ¬Fin15AnchoredAtom3824 chi ∧
      ¬Fin15AnchoredAtom3827 chi ∧
      ¬Fin15AnchoredAtom3842 chi ∧
      ¬Fin15AnchoredAtom3863 chi ∧
      ¬Fin15AnchoredAtom3919 chi ∧
      ¬Fin15AnchoredAtom4585 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 5, 6, 7, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09447
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1842 Fin15AnchoredAtom1843 Fin15AnchoredAtom1846
    Fin15AnchoredAtom1849 Fin15AnchoredAtom1851 Fin15AnchoredAtom1854 Fin15AnchoredAtom1857
    Fin15AnchoredAtom1861 Fin15AnchoredAtom1864 Fin15AnchoredAtom1879 Fin15AnchoredAtom1987
    Fin15AnchoredAtom1990 Fin15AnchoredAtom1993 Fin15AnchoredAtom1997 Fin15AnchoredAtom2000
    Fin15AnchoredAtom2015 Fin15AnchoredAtom2025 Fin15AnchoredAtom2028 Fin15AnchoredAtom2043
    Fin15AnchoredAtom2064 Fin15AnchoredAtom2207 Fin15AnchoredAtom2210 Fin15AnchoredAtom2213
    Fin15AnchoredAtom2217 Fin15AnchoredAtom2220 Fin15AnchoredAtom2235 Fin15AnchoredAtom2245
    Fin15AnchoredAtom2248 Fin15AnchoredAtom2263 Fin15AnchoredAtom2284 Fin15AnchoredAtom2614
    Fin15AnchoredAtom2617 Fin15AnchoredAtom2632 Fin15AnchoredAtom2653 Fin15AnchoredAtom2709
    Fin15AnchoredAtom2922 Fin15AnchoredAtom2925 Fin15AnchoredAtom2928 Fin15AnchoredAtom2932
    Fin15AnchoredAtom2935 Fin15AnchoredAtom2950 Fin15AnchoredAtom2960 Fin15AnchoredAtom2963
    Fin15AnchoredAtom2978 Fin15AnchoredAtom2999 Fin15AnchoredAtom3329 Fin15AnchoredAtom3332
    Fin15AnchoredAtom3347 Fin15AnchoredAtom3368 Fin15AnchoredAtom3424 Fin15AnchoredAtom3824
    Fin15AnchoredAtom3827 Fin15AnchoredAtom3842 Fin15AnchoredAtom3863 Fin15AnchoredAtom3919
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

theorem fin15Anchored_clause30711 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom1987 chi ∧
      ¬Fin15AnchoredAtom1990 chi ∧
      ¬Fin15AnchoredAtom1994 chi ∧
      ¬Fin15AnchoredAtom1997 chi ∧
      ¬Fin15AnchoredAtom2001 chi ∧
      ¬Fin15AnchoredAtom2016 chi ∧
      ¬Fin15AnchoredAtom2025 chi ∧
      ¬Fin15AnchoredAtom2029 chi ∧
      ¬Fin15AnchoredAtom2044 chi ∧
      ¬Fin15AnchoredAtom2065 chi ∧
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
      ¬Fin15AnchoredAtom2614 chi ∧
      ¬Fin15AnchoredAtom2618 chi ∧
      ¬Fin15AnchoredAtom2633 chi ∧
      ¬Fin15AnchoredAtom2654 chi ∧
      ¬Fin15AnchoredAtom2710 chi ∧
      ¬Fin15AnchoredAtom2922 chi ∧
      ¬Fin15AnchoredAtom2925 chi ∧
      ¬Fin15AnchoredAtom2929 chi ∧
      ¬Fin15AnchoredAtom2932 chi ∧
      ¬Fin15AnchoredAtom2936 chi ∧
      ¬Fin15AnchoredAtom2951 chi ∧
      ¬Fin15AnchoredAtom2960 chi ∧
      ¬Fin15AnchoredAtom2964 chi ∧
      ¬Fin15AnchoredAtom2979 chi ∧
      ¬Fin15AnchoredAtom3000 chi ∧
      ¬Fin15AnchoredAtom3329 chi ∧
      ¬Fin15AnchoredAtom3333 chi ∧
      ¬Fin15AnchoredAtom3348 chi ∧
      ¬Fin15AnchoredAtom3369 chi ∧
      ¬Fin15AnchoredAtom3425 chi ∧
      ¬Fin15AnchoredAtom3824 chi ∧
      ¬Fin15AnchoredAtom3828 chi ∧
      ¬Fin15AnchoredAtom3843 chi ∧
      ¬Fin15AnchoredAtom3864 chi ∧
      ¬Fin15AnchoredAtom3920 chi ∧
      ¬Fin15AnchoredAtom4586 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 5, 6, 7, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17639
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1842 Fin15AnchoredAtom1843 Fin15AnchoredAtom1846
    Fin15AnchoredAtom1850 Fin15AnchoredAtom1851 Fin15AnchoredAtom1854 Fin15AnchoredAtom1858
    Fin15AnchoredAtom1861 Fin15AnchoredAtom1865 Fin15AnchoredAtom1880 Fin15AnchoredAtom1987
    Fin15AnchoredAtom1990 Fin15AnchoredAtom1994 Fin15AnchoredAtom1997 Fin15AnchoredAtom2001
    Fin15AnchoredAtom2016 Fin15AnchoredAtom2025 Fin15AnchoredAtom2029 Fin15AnchoredAtom2044
    Fin15AnchoredAtom2065 Fin15AnchoredAtom2207 Fin15AnchoredAtom2210 Fin15AnchoredAtom2214
    Fin15AnchoredAtom2217 Fin15AnchoredAtom2221 Fin15AnchoredAtom2236 Fin15AnchoredAtom2245
    Fin15AnchoredAtom2249 Fin15AnchoredAtom2264 Fin15AnchoredAtom2285 Fin15AnchoredAtom2614
    Fin15AnchoredAtom2618 Fin15AnchoredAtom2633 Fin15AnchoredAtom2654 Fin15AnchoredAtom2710
    Fin15AnchoredAtom2922 Fin15AnchoredAtom2925 Fin15AnchoredAtom2929 Fin15AnchoredAtom2932
    Fin15AnchoredAtom2936 Fin15AnchoredAtom2951 Fin15AnchoredAtom2960 Fin15AnchoredAtom2964
    Fin15AnchoredAtom2979 Fin15AnchoredAtom3000 Fin15AnchoredAtom3329 Fin15AnchoredAtom3333
    Fin15AnchoredAtom3348 Fin15AnchoredAtom3369 Fin15AnchoredAtom3425 Fin15AnchoredAtom3824
    Fin15AnchoredAtom3828 Fin15AnchoredAtom3843 Fin15AnchoredAtom3864 Fin15AnchoredAtom3920
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

theorem fin15Anchored_clause30712 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom1987 chi ∧
      ¬Fin15AnchoredAtom1992 chi ∧
      ¬Fin15AnchoredAtom1993 chi ∧
      ¬Fin15AnchoredAtom1999 chi ∧
      ¬Fin15AnchoredAtom2000 chi ∧
      ¬Fin15AnchoredAtom2020 chi ∧
      ¬Fin15AnchoredAtom2027 chi ∧
      ¬Fin15AnchoredAtom2028 chi ∧
      ¬Fin15AnchoredAtom2048 chi ∧
      ¬Fin15AnchoredAtom2069 chi ∧
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
      ¬Fin15AnchoredAtom2616 chi ∧
      ¬Fin15AnchoredAtom2617 chi ∧
      ¬Fin15AnchoredAtom2637 chi ∧
      ¬Fin15AnchoredAtom2658 chi ∧
      ¬Fin15AnchoredAtom2714 chi ∧
      ¬Fin15AnchoredAtom2922 chi ∧
      ¬Fin15AnchoredAtom2927 chi ∧
      ¬Fin15AnchoredAtom2928 chi ∧
      ¬Fin15AnchoredAtom2934 chi ∧
      ¬Fin15AnchoredAtom2935 chi ∧
      ¬Fin15AnchoredAtom2955 chi ∧
      ¬Fin15AnchoredAtom2962 chi ∧
      ¬Fin15AnchoredAtom2963 chi ∧
      ¬Fin15AnchoredAtom2983 chi ∧
      ¬Fin15AnchoredAtom3004 chi ∧
      ¬Fin15AnchoredAtom3331 chi ∧
      ¬Fin15AnchoredAtom3332 chi ∧
      ¬Fin15AnchoredAtom3352 chi ∧
      ¬Fin15AnchoredAtom3373 chi ∧
      ¬Fin15AnchoredAtom3429 chi ∧
      ¬Fin15AnchoredAtom3826 chi ∧
      ¬Fin15AnchoredAtom3827 chi ∧
      ¬Fin15AnchoredAtom3847 chi ∧
      ¬Fin15AnchoredAtom3868 chi ∧
      ¬Fin15AnchoredAtom3924 chi ∧
      ¬Fin15AnchoredAtom4590 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 5, 6, 7, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask12519
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1842 Fin15AnchoredAtom1843 Fin15AnchoredAtom1848
    Fin15AnchoredAtom1849 Fin15AnchoredAtom1851 Fin15AnchoredAtom1856 Fin15AnchoredAtom1857
    Fin15AnchoredAtom1863 Fin15AnchoredAtom1864 Fin15AnchoredAtom1884 Fin15AnchoredAtom1987
    Fin15AnchoredAtom1992 Fin15AnchoredAtom1993 Fin15AnchoredAtom1999 Fin15AnchoredAtom2000
    Fin15AnchoredAtom2020 Fin15AnchoredAtom2027 Fin15AnchoredAtom2028 Fin15AnchoredAtom2048
    Fin15AnchoredAtom2069 Fin15AnchoredAtom2207 Fin15AnchoredAtom2212 Fin15AnchoredAtom2213
    Fin15AnchoredAtom2219 Fin15AnchoredAtom2220 Fin15AnchoredAtom2240 Fin15AnchoredAtom2247
    Fin15AnchoredAtom2248 Fin15AnchoredAtom2268 Fin15AnchoredAtom2289 Fin15AnchoredAtom2616
    Fin15AnchoredAtom2617 Fin15AnchoredAtom2637 Fin15AnchoredAtom2658 Fin15AnchoredAtom2714
    Fin15AnchoredAtom2922 Fin15AnchoredAtom2927 Fin15AnchoredAtom2928 Fin15AnchoredAtom2934
    Fin15AnchoredAtom2935 Fin15AnchoredAtom2955 Fin15AnchoredAtom2962 Fin15AnchoredAtom2963
    Fin15AnchoredAtom2983 Fin15AnchoredAtom3004 Fin15AnchoredAtom3331 Fin15AnchoredAtom3332
    Fin15AnchoredAtom3352 Fin15AnchoredAtom3373 Fin15AnchoredAtom3429 Fin15AnchoredAtom3826
    Fin15AnchoredAtom3827 Fin15AnchoredAtom3847 Fin15AnchoredAtom3868 Fin15AnchoredAtom3924
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

theorem fin15Anchored_clause30713 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom1987 chi ∧
      ¬Fin15AnchoredAtom1992 chi ∧
      ¬Fin15AnchoredAtom1994 chi ∧
      ¬Fin15AnchoredAtom1999 chi ∧
      ¬Fin15AnchoredAtom2001 chi ∧
      ¬Fin15AnchoredAtom2021 chi ∧
      ¬Fin15AnchoredAtom2027 chi ∧
      ¬Fin15AnchoredAtom2029 chi ∧
      ¬Fin15AnchoredAtom2049 chi ∧
      ¬Fin15AnchoredAtom2070 chi ∧
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
      ¬Fin15AnchoredAtom2616 chi ∧
      ¬Fin15AnchoredAtom2618 chi ∧
      ¬Fin15AnchoredAtom2638 chi ∧
      ¬Fin15AnchoredAtom2659 chi ∧
      ¬Fin15AnchoredAtom2715 chi ∧
      ¬Fin15AnchoredAtom2922 chi ∧
      ¬Fin15AnchoredAtom2927 chi ∧
      ¬Fin15AnchoredAtom2929 chi ∧
      ¬Fin15AnchoredAtom2934 chi ∧
      ¬Fin15AnchoredAtom2936 chi ∧
      ¬Fin15AnchoredAtom2956 chi ∧
      ¬Fin15AnchoredAtom2962 chi ∧
      ¬Fin15AnchoredAtom2964 chi ∧
      ¬Fin15AnchoredAtom2984 chi ∧
      ¬Fin15AnchoredAtom3005 chi ∧
      ¬Fin15AnchoredAtom3331 chi ∧
      ¬Fin15AnchoredAtom3333 chi ∧
      ¬Fin15AnchoredAtom3353 chi ∧
      ¬Fin15AnchoredAtom3374 chi ∧
      ¬Fin15AnchoredAtom3430 chi ∧
      ¬Fin15AnchoredAtom3826 chi ∧
      ¬Fin15AnchoredAtom3828 chi ∧
      ¬Fin15AnchoredAtom3848 chi ∧
      ¬Fin15AnchoredAtom3869 chi ∧
      ¬Fin15AnchoredAtom3925 chi ∧
      ¬Fin15AnchoredAtom4591 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 5, 6, 7, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask20711
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1842 Fin15AnchoredAtom1843 Fin15AnchoredAtom1848
    Fin15AnchoredAtom1850 Fin15AnchoredAtom1851 Fin15AnchoredAtom1856 Fin15AnchoredAtom1858
    Fin15AnchoredAtom1863 Fin15AnchoredAtom1865 Fin15AnchoredAtom1885 Fin15AnchoredAtom1987
    Fin15AnchoredAtom1992 Fin15AnchoredAtom1994 Fin15AnchoredAtom1999 Fin15AnchoredAtom2001
    Fin15AnchoredAtom2021 Fin15AnchoredAtom2027 Fin15AnchoredAtom2029 Fin15AnchoredAtom2049
    Fin15AnchoredAtom2070 Fin15AnchoredAtom2207 Fin15AnchoredAtom2212 Fin15AnchoredAtom2214
    Fin15AnchoredAtom2219 Fin15AnchoredAtom2221 Fin15AnchoredAtom2241 Fin15AnchoredAtom2247
    Fin15AnchoredAtom2249 Fin15AnchoredAtom2269 Fin15AnchoredAtom2290 Fin15AnchoredAtom2616
    Fin15AnchoredAtom2618 Fin15AnchoredAtom2638 Fin15AnchoredAtom2659 Fin15AnchoredAtom2715
    Fin15AnchoredAtom2922 Fin15AnchoredAtom2927 Fin15AnchoredAtom2929 Fin15AnchoredAtom2934
    Fin15AnchoredAtom2936 Fin15AnchoredAtom2956 Fin15AnchoredAtom2962 Fin15AnchoredAtom2964
    Fin15AnchoredAtom2984 Fin15AnchoredAtom3005 Fin15AnchoredAtom3331 Fin15AnchoredAtom3333
    Fin15AnchoredAtom3353 Fin15AnchoredAtom3374 Fin15AnchoredAtom3430 Fin15AnchoredAtom3826
    Fin15AnchoredAtom3828 Fin15AnchoredAtom3848 Fin15AnchoredAtom3869 Fin15AnchoredAtom3925
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

theorem fin15Anchored_clause30714 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom1886 chi ∧
      ¬Fin15AnchoredAtom1987 chi ∧
      ¬Fin15AnchoredAtom1993 chi ∧
      ¬Fin15AnchoredAtom1994 chi ∧
      ¬Fin15AnchoredAtom2000 chi ∧
      ¬Fin15AnchoredAtom2001 chi ∧
      ¬Fin15AnchoredAtom2022 chi ∧
      ¬Fin15AnchoredAtom2028 chi ∧
      ¬Fin15AnchoredAtom2029 chi ∧
      ¬Fin15AnchoredAtom2050 chi ∧
      ¬Fin15AnchoredAtom2071 chi ∧
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
      ¬Fin15AnchoredAtom2617 chi ∧
      ¬Fin15AnchoredAtom2618 chi ∧
      ¬Fin15AnchoredAtom2639 chi ∧
      ¬Fin15AnchoredAtom2660 chi ∧
      ¬Fin15AnchoredAtom2716 chi ∧
      ¬Fin15AnchoredAtom2922 chi ∧
      ¬Fin15AnchoredAtom2928 chi ∧
      ¬Fin15AnchoredAtom2929 chi ∧
      ¬Fin15AnchoredAtom2935 chi ∧
      ¬Fin15AnchoredAtom2936 chi ∧
      ¬Fin15AnchoredAtom2957 chi ∧
      ¬Fin15AnchoredAtom2963 chi ∧
      ¬Fin15AnchoredAtom2964 chi ∧
      ¬Fin15AnchoredAtom2985 chi ∧
      ¬Fin15AnchoredAtom3006 chi ∧
      ¬Fin15AnchoredAtom3332 chi ∧
      ¬Fin15AnchoredAtom3333 chi ∧
      ¬Fin15AnchoredAtom3354 chi ∧
      ¬Fin15AnchoredAtom3375 chi ∧
      ¬Fin15AnchoredAtom3431 chi ∧
      ¬Fin15AnchoredAtom3827 chi ∧
      ¬Fin15AnchoredAtom3828 chi ∧
      ¬Fin15AnchoredAtom3849 chi ∧
      ¬Fin15AnchoredAtom3870 chi ∧
      ¬Fin15AnchoredAtom3926 chi ∧
      ¬Fin15AnchoredAtom4592 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 5, 6, 7, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask24807
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1842 Fin15AnchoredAtom1843 Fin15AnchoredAtom1849
    Fin15AnchoredAtom1850 Fin15AnchoredAtom1851 Fin15AnchoredAtom1857 Fin15AnchoredAtom1858
    Fin15AnchoredAtom1864 Fin15AnchoredAtom1865 Fin15AnchoredAtom1886 Fin15AnchoredAtom1987
    Fin15AnchoredAtom1993 Fin15AnchoredAtom1994 Fin15AnchoredAtom2000 Fin15AnchoredAtom2001
    Fin15AnchoredAtom2022 Fin15AnchoredAtom2028 Fin15AnchoredAtom2029 Fin15AnchoredAtom2050
    Fin15AnchoredAtom2071 Fin15AnchoredAtom2207 Fin15AnchoredAtom2213 Fin15AnchoredAtom2214
    Fin15AnchoredAtom2220 Fin15AnchoredAtom2221 Fin15AnchoredAtom2242 Fin15AnchoredAtom2248
    Fin15AnchoredAtom2249 Fin15AnchoredAtom2270 Fin15AnchoredAtom2291 Fin15AnchoredAtom2617
    Fin15AnchoredAtom2618 Fin15AnchoredAtom2639 Fin15AnchoredAtom2660 Fin15AnchoredAtom2716
    Fin15AnchoredAtom2922 Fin15AnchoredAtom2928 Fin15AnchoredAtom2929 Fin15AnchoredAtom2935
    Fin15AnchoredAtom2936 Fin15AnchoredAtom2957 Fin15AnchoredAtom2963 Fin15AnchoredAtom2964
    Fin15AnchoredAtom2985 Fin15AnchoredAtom3006 Fin15AnchoredAtom3332 Fin15AnchoredAtom3333
    Fin15AnchoredAtom3354 Fin15AnchoredAtom3375 Fin15AnchoredAtom3431 Fin15AnchoredAtom3827
    Fin15AnchoredAtom3828 Fin15AnchoredAtom3849 Fin15AnchoredAtom3870 Fin15AnchoredAtom3926
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

theorem fin15Anchored_clause30715 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom1989 chi ∧
      ¬Fin15AnchoredAtom1990 chi ∧
      ¬Fin15AnchoredAtom1992 chi ∧
      ¬Fin15AnchoredAtom2008 chi ∧
      ¬Fin15AnchoredAtom2010 chi ∧
      ¬Fin15AnchoredAtom2014 chi ∧
      ¬Fin15AnchoredAtom2036 chi ∧
      ¬Fin15AnchoredAtom2038 chi ∧
      ¬Fin15AnchoredAtom2042 chi ∧
      ¬Fin15AnchoredAtom2088 chi ∧
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
      ¬Fin15AnchoredAtom2625 chi ∧
      ¬Fin15AnchoredAtom2627 chi ∧
      ¬Fin15AnchoredAtom2631 chi ∧
      ¬Fin15AnchoredAtom2677 chi ∧
      ¬Fin15AnchoredAtom2733 chi ∧
      ¬Fin15AnchoredAtom2924 chi ∧
      ¬Fin15AnchoredAtom2925 chi ∧
      ¬Fin15AnchoredAtom2927 chi ∧
      ¬Fin15AnchoredAtom2943 chi ∧
      ¬Fin15AnchoredAtom2945 chi ∧
      ¬Fin15AnchoredAtom2949 chi ∧
      ¬Fin15AnchoredAtom2971 chi ∧
      ¬Fin15AnchoredAtom2973 chi ∧
      ¬Fin15AnchoredAtom2977 chi ∧
      ¬Fin15AnchoredAtom3023 chi ∧
      ¬Fin15AnchoredAtom3340 chi ∧
      ¬Fin15AnchoredAtom3342 chi ∧
      ¬Fin15AnchoredAtom3346 chi ∧
      ¬Fin15AnchoredAtom3392 chi ∧
      ¬Fin15AnchoredAtom3448 chi ∧
      ¬Fin15AnchoredAtom3835 chi ∧
      ¬Fin15AnchoredAtom3837 chi ∧
      ¬Fin15AnchoredAtom3841 chi ∧
      ¬Fin15AnchoredAtom3887 chi ∧
      ¬Fin15AnchoredAtom3943 chi ∧
      ¬Fin15AnchoredAtom4609 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 5, 6, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05735
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1842 Fin15AnchoredAtom1845 Fin15AnchoredAtom1846
    Fin15AnchoredAtom1848 Fin15AnchoredAtom1853 Fin15AnchoredAtom1854 Fin15AnchoredAtom1856
    Fin15AnchoredAtom1872 Fin15AnchoredAtom1874 Fin15AnchoredAtom1878 Fin15AnchoredAtom1989
    Fin15AnchoredAtom1990 Fin15AnchoredAtom1992 Fin15AnchoredAtom2008 Fin15AnchoredAtom2010
    Fin15AnchoredAtom2014 Fin15AnchoredAtom2036 Fin15AnchoredAtom2038 Fin15AnchoredAtom2042
    Fin15AnchoredAtom2088 Fin15AnchoredAtom2209 Fin15AnchoredAtom2210 Fin15AnchoredAtom2212
    Fin15AnchoredAtom2228 Fin15AnchoredAtom2230 Fin15AnchoredAtom2234 Fin15AnchoredAtom2256
    Fin15AnchoredAtom2258 Fin15AnchoredAtom2262 Fin15AnchoredAtom2308 Fin15AnchoredAtom2625
    Fin15AnchoredAtom2627 Fin15AnchoredAtom2631 Fin15AnchoredAtom2677 Fin15AnchoredAtom2733
    Fin15AnchoredAtom2924 Fin15AnchoredAtom2925 Fin15AnchoredAtom2927 Fin15AnchoredAtom2943
    Fin15AnchoredAtom2945 Fin15AnchoredAtom2949 Fin15AnchoredAtom2971 Fin15AnchoredAtom2973
    Fin15AnchoredAtom2977 Fin15AnchoredAtom3023 Fin15AnchoredAtom3340 Fin15AnchoredAtom3342
    Fin15AnchoredAtom3346 Fin15AnchoredAtom3392 Fin15AnchoredAtom3448 Fin15AnchoredAtom3835
    Fin15AnchoredAtom3837 Fin15AnchoredAtom3841 Fin15AnchoredAtom3887 Fin15AnchoredAtom3943
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

theorem fin15Anchored_clause30716 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom1989 chi ∧
      ¬Fin15AnchoredAtom1990 chi ∧
      ¬Fin15AnchoredAtom1993 chi ∧
      ¬Fin15AnchoredAtom2008 chi ∧
      ¬Fin15AnchoredAtom2011 chi ∧
      ¬Fin15AnchoredAtom2015 chi ∧
      ¬Fin15AnchoredAtom2036 chi ∧
      ¬Fin15AnchoredAtom2039 chi ∧
      ¬Fin15AnchoredAtom2043 chi ∧
      ¬Fin15AnchoredAtom2089 chi ∧
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
      ¬Fin15AnchoredAtom2625 chi ∧
      ¬Fin15AnchoredAtom2628 chi ∧
      ¬Fin15AnchoredAtom2632 chi ∧
      ¬Fin15AnchoredAtom2678 chi ∧
      ¬Fin15AnchoredAtom2734 chi ∧
      ¬Fin15AnchoredAtom2924 chi ∧
      ¬Fin15AnchoredAtom2925 chi ∧
      ¬Fin15AnchoredAtom2928 chi ∧
      ¬Fin15AnchoredAtom2943 chi ∧
      ¬Fin15AnchoredAtom2946 chi ∧
      ¬Fin15AnchoredAtom2950 chi ∧
      ¬Fin15AnchoredAtom2971 chi ∧
      ¬Fin15AnchoredAtom2974 chi ∧
      ¬Fin15AnchoredAtom2978 chi ∧
      ¬Fin15AnchoredAtom3024 chi ∧
      ¬Fin15AnchoredAtom3340 chi ∧
      ¬Fin15AnchoredAtom3343 chi ∧
      ¬Fin15AnchoredAtom3347 chi ∧
      ¬Fin15AnchoredAtom3393 chi ∧
      ¬Fin15AnchoredAtom3449 chi ∧
      ¬Fin15AnchoredAtom3835 chi ∧
      ¬Fin15AnchoredAtom3838 chi ∧
      ¬Fin15AnchoredAtom3842 chi ∧
      ¬Fin15AnchoredAtom3888 chi ∧
      ¬Fin15AnchoredAtom3944 chi ∧
      ¬Fin15AnchoredAtom4610 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 5, 6, 9, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09831
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1842 Fin15AnchoredAtom1845 Fin15AnchoredAtom1846
    Fin15AnchoredAtom1849 Fin15AnchoredAtom1853 Fin15AnchoredAtom1854 Fin15AnchoredAtom1857
    Fin15AnchoredAtom1872 Fin15AnchoredAtom1875 Fin15AnchoredAtom1879 Fin15AnchoredAtom1989
    Fin15AnchoredAtom1990 Fin15AnchoredAtom1993 Fin15AnchoredAtom2008 Fin15AnchoredAtom2011
    Fin15AnchoredAtom2015 Fin15AnchoredAtom2036 Fin15AnchoredAtom2039 Fin15AnchoredAtom2043
    Fin15AnchoredAtom2089 Fin15AnchoredAtom2209 Fin15AnchoredAtom2210 Fin15AnchoredAtom2213
    Fin15AnchoredAtom2228 Fin15AnchoredAtom2231 Fin15AnchoredAtom2235 Fin15AnchoredAtom2256
    Fin15AnchoredAtom2259 Fin15AnchoredAtom2263 Fin15AnchoredAtom2309 Fin15AnchoredAtom2625
    Fin15AnchoredAtom2628 Fin15AnchoredAtom2632 Fin15AnchoredAtom2678 Fin15AnchoredAtom2734
    Fin15AnchoredAtom2924 Fin15AnchoredAtom2925 Fin15AnchoredAtom2928 Fin15AnchoredAtom2943
    Fin15AnchoredAtom2946 Fin15AnchoredAtom2950 Fin15AnchoredAtom2971 Fin15AnchoredAtom2974
    Fin15AnchoredAtom2978 Fin15AnchoredAtom3024 Fin15AnchoredAtom3340 Fin15AnchoredAtom3343
    Fin15AnchoredAtom3347 Fin15AnchoredAtom3393 Fin15AnchoredAtom3449 Fin15AnchoredAtom3835
    Fin15AnchoredAtom3838 Fin15AnchoredAtom3842 Fin15AnchoredAtom3888 Fin15AnchoredAtom3944
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

theorem fin15Anchored_clause30717 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom1989 chi ∧
      ¬Fin15AnchoredAtom1990 chi ∧
      ¬Fin15AnchoredAtom1994 chi ∧
      ¬Fin15AnchoredAtom2008 chi ∧
      ¬Fin15AnchoredAtom2012 chi ∧
      ¬Fin15AnchoredAtom2016 chi ∧
      ¬Fin15AnchoredAtom2036 chi ∧
      ¬Fin15AnchoredAtom2040 chi ∧
      ¬Fin15AnchoredAtom2044 chi ∧
      ¬Fin15AnchoredAtom2090 chi ∧
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
      ¬Fin15AnchoredAtom2625 chi ∧
      ¬Fin15AnchoredAtom2629 chi ∧
      ¬Fin15AnchoredAtom2633 chi ∧
      ¬Fin15AnchoredAtom2679 chi ∧
      ¬Fin15AnchoredAtom2735 chi ∧
      ¬Fin15AnchoredAtom2924 chi ∧
      ¬Fin15AnchoredAtom2925 chi ∧
      ¬Fin15AnchoredAtom2929 chi ∧
      ¬Fin15AnchoredAtom2943 chi ∧
      ¬Fin15AnchoredAtom2947 chi ∧
      ¬Fin15AnchoredAtom2951 chi ∧
      ¬Fin15AnchoredAtom2971 chi ∧
      ¬Fin15AnchoredAtom2975 chi ∧
      ¬Fin15AnchoredAtom2979 chi ∧
      ¬Fin15AnchoredAtom3025 chi ∧
      ¬Fin15AnchoredAtom3340 chi ∧
      ¬Fin15AnchoredAtom3344 chi ∧
      ¬Fin15AnchoredAtom3348 chi ∧
      ¬Fin15AnchoredAtom3394 chi ∧
      ¬Fin15AnchoredAtom3450 chi ∧
      ¬Fin15AnchoredAtom3835 chi ∧
      ¬Fin15AnchoredAtom3839 chi ∧
      ¬Fin15AnchoredAtom3843 chi ∧
      ¬Fin15AnchoredAtom3889 chi ∧
      ¬Fin15AnchoredAtom3945 chi ∧
      ¬Fin15AnchoredAtom4611 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 5, 6, 9, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask18023
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1842 Fin15AnchoredAtom1845 Fin15AnchoredAtom1846
    Fin15AnchoredAtom1850 Fin15AnchoredAtom1853 Fin15AnchoredAtom1854 Fin15AnchoredAtom1858
    Fin15AnchoredAtom1872 Fin15AnchoredAtom1876 Fin15AnchoredAtom1880 Fin15AnchoredAtom1989
    Fin15AnchoredAtom1990 Fin15AnchoredAtom1994 Fin15AnchoredAtom2008 Fin15AnchoredAtom2012
    Fin15AnchoredAtom2016 Fin15AnchoredAtom2036 Fin15AnchoredAtom2040 Fin15AnchoredAtom2044
    Fin15AnchoredAtom2090 Fin15AnchoredAtom2209 Fin15AnchoredAtom2210 Fin15AnchoredAtom2214
    Fin15AnchoredAtom2228 Fin15AnchoredAtom2232 Fin15AnchoredAtom2236 Fin15AnchoredAtom2256
    Fin15AnchoredAtom2260 Fin15AnchoredAtom2264 Fin15AnchoredAtom2310 Fin15AnchoredAtom2625
    Fin15AnchoredAtom2629 Fin15AnchoredAtom2633 Fin15AnchoredAtom2679 Fin15AnchoredAtom2735
    Fin15AnchoredAtom2924 Fin15AnchoredAtom2925 Fin15AnchoredAtom2929 Fin15AnchoredAtom2943
    Fin15AnchoredAtom2947 Fin15AnchoredAtom2951 Fin15AnchoredAtom2971 Fin15AnchoredAtom2975
    Fin15AnchoredAtom2979 Fin15AnchoredAtom3025 Fin15AnchoredAtom3340 Fin15AnchoredAtom3344
    Fin15AnchoredAtom3348 Fin15AnchoredAtom3394 Fin15AnchoredAtom3450 Fin15AnchoredAtom3835
    Fin15AnchoredAtom3839 Fin15AnchoredAtom3843 Fin15AnchoredAtom3889 Fin15AnchoredAtom3945
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

theorem fin15Anchored_clause30718 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom1989 chi ∧
      ¬Fin15AnchoredAtom1992 chi ∧
      ¬Fin15AnchoredAtom1993 chi ∧
      ¬Fin15AnchoredAtom2010 chi ∧
      ¬Fin15AnchoredAtom2011 chi ∧
      ¬Fin15AnchoredAtom2020 chi ∧
      ¬Fin15AnchoredAtom2038 chi ∧
      ¬Fin15AnchoredAtom2039 chi ∧
      ¬Fin15AnchoredAtom2048 chi ∧
      ¬Fin15AnchoredAtom2094 chi ∧
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
      ¬Fin15AnchoredAtom2627 chi ∧
      ¬Fin15AnchoredAtom2628 chi ∧
      ¬Fin15AnchoredAtom2637 chi ∧
      ¬Fin15AnchoredAtom2683 chi ∧
      ¬Fin15AnchoredAtom2739 chi ∧
      ¬Fin15AnchoredAtom2924 chi ∧
      ¬Fin15AnchoredAtom2927 chi ∧
      ¬Fin15AnchoredAtom2928 chi ∧
      ¬Fin15AnchoredAtom2945 chi ∧
      ¬Fin15AnchoredAtom2946 chi ∧
      ¬Fin15AnchoredAtom2955 chi ∧
      ¬Fin15AnchoredAtom2973 chi ∧
      ¬Fin15AnchoredAtom2974 chi ∧
      ¬Fin15AnchoredAtom2983 chi ∧
      ¬Fin15AnchoredAtom3029 chi ∧
      ¬Fin15AnchoredAtom3342 chi ∧
      ¬Fin15AnchoredAtom3343 chi ∧
      ¬Fin15AnchoredAtom3352 chi ∧
      ¬Fin15AnchoredAtom3398 chi ∧
      ¬Fin15AnchoredAtom3454 chi ∧
      ¬Fin15AnchoredAtom3837 chi ∧
      ¬Fin15AnchoredAtom3838 chi ∧
      ¬Fin15AnchoredAtom3847 chi ∧
      ¬Fin15AnchoredAtom3893 chi ∧
      ¬Fin15AnchoredAtom3949 chi ∧
      ¬Fin15AnchoredAtom4615 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 5, 6, 9, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask12903
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1842 Fin15AnchoredAtom1845 Fin15AnchoredAtom1848
    Fin15AnchoredAtom1849 Fin15AnchoredAtom1853 Fin15AnchoredAtom1856 Fin15AnchoredAtom1857
    Fin15AnchoredAtom1874 Fin15AnchoredAtom1875 Fin15AnchoredAtom1884 Fin15AnchoredAtom1989
    Fin15AnchoredAtom1992 Fin15AnchoredAtom1993 Fin15AnchoredAtom2010 Fin15AnchoredAtom2011
    Fin15AnchoredAtom2020 Fin15AnchoredAtom2038 Fin15AnchoredAtom2039 Fin15AnchoredAtom2048
    Fin15AnchoredAtom2094 Fin15AnchoredAtom2209 Fin15AnchoredAtom2212 Fin15AnchoredAtom2213
    Fin15AnchoredAtom2230 Fin15AnchoredAtom2231 Fin15AnchoredAtom2240 Fin15AnchoredAtom2258
    Fin15AnchoredAtom2259 Fin15AnchoredAtom2268 Fin15AnchoredAtom2314 Fin15AnchoredAtom2627
    Fin15AnchoredAtom2628 Fin15AnchoredAtom2637 Fin15AnchoredAtom2683 Fin15AnchoredAtom2739
    Fin15AnchoredAtom2924 Fin15AnchoredAtom2927 Fin15AnchoredAtom2928 Fin15AnchoredAtom2945
    Fin15AnchoredAtom2946 Fin15AnchoredAtom2955 Fin15AnchoredAtom2973 Fin15AnchoredAtom2974
    Fin15AnchoredAtom2983 Fin15AnchoredAtom3029 Fin15AnchoredAtom3342 Fin15AnchoredAtom3343
    Fin15AnchoredAtom3352 Fin15AnchoredAtom3398 Fin15AnchoredAtom3454 Fin15AnchoredAtom3837
    Fin15AnchoredAtom3838 Fin15AnchoredAtom3847 Fin15AnchoredAtom3893 Fin15AnchoredAtom3949
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

theorem fin15Anchored_clause30719 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom1989 chi ∧
      ¬Fin15AnchoredAtom1992 chi ∧
      ¬Fin15AnchoredAtom1994 chi ∧
      ¬Fin15AnchoredAtom2010 chi ∧
      ¬Fin15AnchoredAtom2012 chi ∧
      ¬Fin15AnchoredAtom2021 chi ∧
      ¬Fin15AnchoredAtom2038 chi ∧
      ¬Fin15AnchoredAtom2040 chi ∧
      ¬Fin15AnchoredAtom2049 chi ∧
      ¬Fin15AnchoredAtom2095 chi ∧
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
      ¬Fin15AnchoredAtom2627 chi ∧
      ¬Fin15AnchoredAtom2629 chi ∧
      ¬Fin15AnchoredAtom2638 chi ∧
      ¬Fin15AnchoredAtom2684 chi ∧
      ¬Fin15AnchoredAtom2740 chi ∧
      ¬Fin15AnchoredAtom2924 chi ∧
      ¬Fin15AnchoredAtom2927 chi ∧
      ¬Fin15AnchoredAtom2929 chi ∧
      ¬Fin15AnchoredAtom2945 chi ∧
      ¬Fin15AnchoredAtom2947 chi ∧
      ¬Fin15AnchoredAtom2956 chi ∧
      ¬Fin15AnchoredAtom2973 chi ∧
      ¬Fin15AnchoredAtom2975 chi ∧
      ¬Fin15AnchoredAtom2984 chi ∧
      ¬Fin15AnchoredAtom3030 chi ∧
      ¬Fin15AnchoredAtom3342 chi ∧
      ¬Fin15AnchoredAtom3344 chi ∧
      ¬Fin15AnchoredAtom3353 chi ∧
      ¬Fin15AnchoredAtom3399 chi ∧
      ¬Fin15AnchoredAtom3455 chi ∧
      ¬Fin15AnchoredAtom3837 chi ∧
      ¬Fin15AnchoredAtom3839 chi ∧
      ¬Fin15AnchoredAtom3848 chi ∧
      ¬Fin15AnchoredAtom3894 chi ∧
      ¬Fin15AnchoredAtom3950 chi ∧
      ¬Fin15AnchoredAtom4616 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 5, 6, 9, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21095
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1842 Fin15AnchoredAtom1845 Fin15AnchoredAtom1848
    Fin15AnchoredAtom1850 Fin15AnchoredAtom1853 Fin15AnchoredAtom1856 Fin15AnchoredAtom1858
    Fin15AnchoredAtom1874 Fin15AnchoredAtom1876 Fin15AnchoredAtom1885 Fin15AnchoredAtom1989
    Fin15AnchoredAtom1992 Fin15AnchoredAtom1994 Fin15AnchoredAtom2010 Fin15AnchoredAtom2012
    Fin15AnchoredAtom2021 Fin15AnchoredAtom2038 Fin15AnchoredAtom2040 Fin15AnchoredAtom2049
    Fin15AnchoredAtom2095 Fin15AnchoredAtom2209 Fin15AnchoredAtom2212 Fin15AnchoredAtom2214
    Fin15AnchoredAtom2230 Fin15AnchoredAtom2232 Fin15AnchoredAtom2241 Fin15AnchoredAtom2258
    Fin15AnchoredAtom2260 Fin15AnchoredAtom2269 Fin15AnchoredAtom2315 Fin15AnchoredAtom2627
    Fin15AnchoredAtom2629 Fin15AnchoredAtom2638 Fin15AnchoredAtom2684 Fin15AnchoredAtom2740
    Fin15AnchoredAtom2924 Fin15AnchoredAtom2927 Fin15AnchoredAtom2929 Fin15AnchoredAtom2945
    Fin15AnchoredAtom2947 Fin15AnchoredAtom2956 Fin15AnchoredAtom2973 Fin15AnchoredAtom2975
    Fin15AnchoredAtom2984 Fin15AnchoredAtom3030 Fin15AnchoredAtom3342 Fin15AnchoredAtom3344
    Fin15AnchoredAtom3353 Fin15AnchoredAtom3399 Fin15AnchoredAtom3455 Fin15AnchoredAtom3837
    Fin15AnchoredAtom3839 Fin15AnchoredAtom3848 Fin15AnchoredAtom3894 Fin15AnchoredAtom3950
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

end ErdosSzekeres

end
