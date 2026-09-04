module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 240. -/

theorem fin15Anchored_clause30720 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom1886 chi ∧
      ¬Fin15AnchoredAtom1989 chi ∧
      ¬Fin15AnchoredAtom1993 chi ∧
      ¬Fin15AnchoredAtom1994 chi ∧
      ¬Fin15AnchoredAtom2011 chi ∧
      ¬Fin15AnchoredAtom2012 chi ∧
      ¬Fin15AnchoredAtom2022 chi ∧
      ¬Fin15AnchoredAtom2039 chi ∧
      ¬Fin15AnchoredAtom2040 chi ∧
      ¬Fin15AnchoredAtom2050 chi ∧
      ¬Fin15AnchoredAtom2096 chi ∧
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
      ¬Fin15AnchoredAtom2628 chi ∧
      ¬Fin15AnchoredAtom2629 chi ∧
      ¬Fin15AnchoredAtom2639 chi ∧
      ¬Fin15AnchoredAtom2685 chi ∧
      ¬Fin15AnchoredAtom2741 chi ∧
      ¬Fin15AnchoredAtom2924 chi ∧
      ¬Fin15AnchoredAtom2928 chi ∧
      ¬Fin15AnchoredAtom2929 chi ∧
      ¬Fin15AnchoredAtom2946 chi ∧
      ¬Fin15AnchoredAtom2947 chi ∧
      ¬Fin15AnchoredAtom2957 chi ∧
      ¬Fin15AnchoredAtom2974 chi ∧
      ¬Fin15AnchoredAtom2975 chi ∧
      ¬Fin15AnchoredAtom2985 chi ∧
      ¬Fin15AnchoredAtom3031 chi ∧
      ¬Fin15AnchoredAtom3343 chi ∧
      ¬Fin15AnchoredAtom3344 chi ∧
      ¬Fin15AnchoredAtom3354 chi ∧
      ¬Fin15AnchoredAtom3400 chi ∧
      ¬Fin15AnchoredAtom3456 chi ∧
      ¬Fin15AnchoredAtom3838 chi ∧
      ¬Fin15AnchoredAtom3839 chi ∧
      ¬Fin15AnchoredAtom3849 chi ∧
      ¬Fin15AnchoredAtom3895 chi ∧
      ¬Fin15AnchoredAtom3951 chi ∧
      ¬Fin15AnchoredAtom4617 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 5, 6, 9, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25191
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1842 Fin15AnchoredAtom1845 Fin15AnchoredAtom1849
    Fin15AnchoredAtom1850 Fin15AnchoredAtom1853 Fin15AnchoredAtom1857 Fin15AnchoredAtom1858
    Fin15AnchoredAtom1875 Fin15AnchoredAtom1876 Fin15AnchoredAtom1886 Fin15AnchoredAtom1989
    Fin15AnchoredAtom1993 Fin15AnchoredAtom1994 Fin15AnchoredAtom2011 Fin15AnchoredAtom2012
    Fin15AnchoredAtom2022 Fin15AnchoredAtom2039 Fin15AnchoredAtom2040 Fin15AnchoredAtom2050
    Fin15AnchoredAtom2096 Fin15AnchoredAtom2209 Fin15AnchoredAtom2213 Fin15AnchoredAtom2214
    Fin15AnchoredAtom2231 Fin15AnchoredAtom2232 Fin15AnchoredAtom2242 Fin15AnchoredAtom2259
    Fin15AnchoredAtom2260 Fin15AnchoredAtom2270 Fin15AnchoredAtom2316 Fin15AnchoredAtom2628
    Fin15AnchoredAtom2629 Fin15AnchoredAtom2639 Fin15AnchoredAtom2685 Fin15AnchoredAtom2741
    Fin15AnchoredAtom2924 Fin15AnchoredAtom2928 Fin15AnchoredAtom2929 Fin15AnchoredAtom2946
    Fin15AnchoredAtom2947 Fin15AnchoredAtom2957 Fin15AnchoredAtom2974 Fin15AnchoredAtom2975
    Fin15AnchoredAtom2985 Fin15AnchoredAtom3031 Fin15AnchoredAtom3343 Fin15AnchoredAtom3344
    Fin15AnchoredAtom3354 Fin15AnchoredAtom3400 Fin15AnchoredAtom3456 Fin15AnchoredAtom3838
    Fin15AnchoredAtom3839 Fin15AnchoredAtom3849 Fin15AnchoredAtom3895 Fin15AnchoredAtom3951
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

theorem fin15Anchored_clause30721 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom1990 chi ∧
      ¬Fin15AnchoredAtom1992 chi ∧
      ¬Fin15AnchoredAtom1993 chi ∧
      ¬Fin15AnchoredAtom2014 chi ∧
      ¬Fin15AnchoredAtom2015 chi ∧
      ¬Fin15AnchoredAtom2020 chi ∧
      ¬Fin15AnchoredAtom2042 chi ∧
      ¬Fin15AnchoredAtom2043 chi ∧
      ¬Fin15AnchoredAtom2048 chi ∧
      ¬Fin15AnchoredAtom2100 chi ∧
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
      ¬Fin15AnchoredAtom2631 chi ∧
      ¬Fin15AnchoredAtom2632 chi ∧
      ¬Fin15AnchoredAtom2637 chi ∧
      ¬Fin15AnchoredAtom2689 chi ∧
      ¬Fin15AnchoredAtom2745 chi ∧
      ¬Fin15AnchoredAtom2925 chi ∧
      ¬Fin15AnchoredAtom2927 chi ∧
      ¬Fin15AnchoredAtom2928 chi ∧
      ¬Fin15AnchoredAtom2949 chi ∧
      ¬Fin15AnchoredAtom2950 chi ∧
      ¬Fin15AnchoredAtom2955 chi ∧
      ¬Fin15AnchoredAtom2977 chi ∧
      ¬Fin15AnchoredAtom2978 chi ∧
      ¬Fin15AnchoredAtom2983 chi ∧
      ¬Fin15AnchoredAtom3035 chi ∧
      ¬Fin15AnchoredAtom3346 chi ∧
      ¬Fin15AnchoredAtom3347 chi ∧
      ¬Fin15AnchoredAtom3352 chi ∧
      ¬Fin15AnchoredAtom3404 chi ∧
      ¬Fin15AnchoredAtom3460 chi ∧
      ¬Fin15AnchoredAtom3841 chi ∧
      ¬Fin15AnchoredAtom3842 chi ∧
      ¬Fin15AnchoredAtom3847 chi ∧
      ¬Fin15AnchoredAtom3899 chi ∧
      ¬Fin15AnchoredAtom3955 chi ∧
      ¬Fin15AnchoredAtom4621 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 5, 6, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13415
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1842 Fin15AnchoredAtom1846 Fin15AnchoredAtom1848
    Fin15AnchoredAtom1849 Fin15AnchoredAtom1854 Fin15AnchoredAtom1856 Fin15AnchoredAtom1857
    Fin15AnchoredAtom1878 Fin15AnchoredAtom1879 Fin15AnchoredAtom1884 Fin15AnchoredAtom1990
    Fin15AnchoredAtom1992 Fin15AnchoredAtom1993 Fin15AnchoredAtom2014 Fin15AnchoredAtom2015
    Fin15AnchoredAtom2020 Fin15AnchoredAtom2042 Fin15AnchoredAtom2043 Fin15AnchoredAtom2048
    Fin15AnchoredAtom2100 Fin15AnchoredAtom2210 Fin15AnchoredAtom2212 Fin15AnchoredAtom2213
    Fin15AnchoredAtom2234 Fin15AnchoredAtom2235 Fin15AnchoredAtom2240 Fin15AnchoredAtom2262
    Fin15AnchoredAtom2263 Fin15AnchoredAtom2268 Fin15AnchoredAtom2320 Fin15AnchoredAtom2631
    Fin15AnchoredAtom2632 Fin15AnchoredAtom2637 Fin15AnchoredAtom2689 Fin15AnchoredAtom2745
    Fin15AnchoredAtom2925 Fin15AnchoredAtom2927 Fin15AnchoredAtom2928 Fin15AnchoredAtom2949
    Fin15AnchoredAtom2950 Fin15AnchoredAtom2955 Fin15AnchoredAtom2977 Fin15AnchoredAtom2978
    Fin15AnchoredAtom2983 Fin15AnchoredAtom3035 Fin15AnchoredAtom3346 Fin15AnchoredAtom3347
    Fin15AnchoredAtom3352 Fin15AnchoredAtom3404 Fin15AnchoredAtom3460 Fin15AnchoredAtom3841
    Fin15AnchoredAtom3842 Fin15AnchoredAtom3847 Fin15AnchoredAtom3899 Fin15AnchoredAtom3955
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

theorem fin15Anchored_clause30722 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom1990 chi ∧
      ¬Fin15AnchoredAtom1992 chi ∧
      ¬Fin15AnchoredAtom1994 chi ∧
      ¬Fin15AnchoredAtom2014 chi ∧
      ¬Fin15AnchoredAtom2016 chi ∧
      ¬Fin15AnchoredAtom2021 chi ∧
      ¬Fin15AnchoredAtom2042 chi ∧
      ¬Fin15AnchoredAtom2044 chi ∧
      ¬Fin15AnchoredAtom2049 chi ∧
      ¬Fin15AnchoredAtom2101 chi ∧
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
      ¬Fin15AnchoredAtom2631 chi ∧
      ¬Fin15AnchoredAtom2633 chi ∧
      ¬Fin15AnchoredAtom2638 chi ∧
      ¬Fin15AnchoredAtom2690 chi ∧
      ¬Fin15AnchoredAtom2746 chi ∧
      ¬Fin15AnchoredAtom2925 chi ∧
      ¬Fin15AnchoredAtom2927 chi ∧
      ¬Fin15AnchoredAtom2929 chi ∧
      ¬Fin15AnchoredAtom2949 chi ∧
      ¬Fin15AnchoredAtom2951 chi ∧
      ¬Fin15AnchoredAtom2956 chi ∧
      ¬Fin15AnchoredAtom2977 chi ∧
      ¬Fin15AnchoredAtom2979 chi ∧
      ¬Fin15AnchoredAtom2984 chi ∧
      ¬Fin15AnchoredAtom3036 chi ∧
      ¬Fin15AnchoredAtom3346 chi ∧
      ¬Fin15AnchoredAtom3348 chi ∧
      ¬Fin15AnchoredAtom3353 chi ∧
      ¬Fin15AnchoredAtom3405 chi ∧
      ¬Fin15AnchoredAtom3461 chi ∧
      ¬Fin15AnchoredAtom3841 chi ∧
      ¬Fin15AnchoredAtom3843 chi ∧
      ¬Fin15AnchoredAtom3848 chi ∧
      ¬Fin15AnchoredAtom3900 chi ∧
      ¬Fin15AnchoredAtom3956 chi ∧
      ¬Fin15AnchoredAtom4622 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 5, 6, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21607
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1842 Fin15AnchoredAtom1846 Fin15AnchoredAtom1848
    Fin15AnchoredAtom1850 Fin15AnchoredAtom1854 Fin15AnchoredAtom1856 Fin15AnchoredAtom1858
    Fin15AnchoredAtom1878 Fin15AnchoredAtom1880 Fin15AnchoredAtom1885 Fin15AnchoredAtom1990
    Fin15AnchoredAtom1992 Fin15AnchoredAtom1994 Fin15AnchoredAtom2014 Fin15AnchoredAtom2016
    Fin15AnchoredAtom2021 Fin15AnchoredAtom2042 Fin15AnchoredAtom2044 Fin15AnchoredAtom2049
    Fin15AnchoredAtom2101 Fin15AnchoredAtom2210 Fin15AnchoredAtom2212 Fin15AnchoredAtom2214
    Fin15AnchoredAtom2234 Fin15AnchoredAtom2236 Fin15AnchoredAtom2241 Fin15AnchoredAtom2262
    Fin15AnchoredAtom2264 Fin15AnchoredAtom2269 Fin15AnchoredAtom2321 Fin15AnchoredAtom2631
    Fin15AnchoredAtom2633 Fin15AnchoredAtom2638 Fin15AnchoredAtom2690 Fin15AnchoredAtom2746
    Fin15AnchoredAtom2925 Fin15AnchoredAtom2927 Fin15AnchoredAtom2929 Fin15AnchoredAtom2949
    Fin15AnchoredAtom2951 Fin15AnchoredAtom2956 Fin15AnchoredAtom2977 Fin15AnchoredAtom2979
    Fin15AnchoredAtom2984 Fin15AnchoredAtom3036 Fin15AnchoredAtom3346 Fin15AnchoredAtom3348
    Fin15AnchoredAtom3353 Fin15AnchoredAtom3405 Fin15AnchoredAtom3461 Fin15AnchoredAtom3841
    Fin15AnchoredAtom3843 Fin15AnchoredAtom3848 Fin15AnchoredAtom3900 Fin15AnchoredAtom3956
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

theorem fin15Anchored_clause30723 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom1886 chi ∧
      ¬Fin15AnchoredAtom1990 chi ∧
      ¬Fin15AnchoredAtom1993 chi ∧
      ¬Fin15AnchoredAtom1994 chi ∧
      ¬Fin15AnchoredAtom2015 chi ∧
      ¬Fin15AnchoredAtom2016 chi ∧
      ¬Fin15AnchoredAtom2022 chi ∧
      ¬Fin15AnchoredAtom2043 chi ∧
      ¬Fin15AnchoredAtom2044 chi ∧
      ¬Fin15AnchoredAtom2050 chi ∧
      ¬Fin15AnchoredAtom2102 chi ∧
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
      ¬Fin15AnchoredAtom2632 chi ∧
      ¬Fin15AnchoredAtom2633 chi ∧
      ¬Fin15AnchoredAtom2639 chi ∧
      ¬Fin15AnchoredAtom2691 chi ∧
      ¬Fin15AnchoredAtom2747 chi ∧
      ¬Fin15AnchoredAtom2925 chi ∧
      ¬Fin15AnchoredAtom2928 chi ∧
      ¬Fin15AnchoredAtom2929 chi ∧
      ¬Fin15AnchoredAtom2950 chi ∧
      ¬Fin15AnchoredAtom2951 chi ∧
      ¬Fin15AnchoredAtom2957 chi ∧
      ¬Fin15AnchoredAtom2978 chi ∧
      ¬Fin15AnchoredAtom2979 chi ∧
      ¬Fin15AnchoredAtom2985 chi ∧
      ¬Fin15AnchoredAtom3037 chi ∧
      ¬Fin15AnchoredAtom3347 chi ∧
      ¬Fin15AnchoredAtom3348 chi ∧
      ¬Fin15AnchoredAtom3354 chi ∧
      ¬Fin15AnchoredAtom3406 chi ∧
      ¬Fin15AnchoredAtom3462 chi ∧
      ¬Fin15AnchoredAtom3842 chi ∧
      ¬Fin15AnchoredAtom3843 chi ∧
      ¬Fin15AnchoredAtom3849 chi ∧
      ¬Fin15AnchoredAtom3901 chi ∧
      ¬Fin15AnchoredAtom3957 chi ∧
      ¬Fin15AnchoredAtom4623 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 5, 6, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25703
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1842 Fin15AnchoredAtom1846 Fin15AnchoredAtom1849
    Fin15AnchoredAtom1850 Fin15AnchoredAtom1854 Fin15AnchoredAtom1857 Fin15AnchoredAtom1858
    Fin15AnchoredAtom1879 Fin15AnchoredAtom1880 Fin15AnchoredAtom1886 Fin15AnchoredAtom1990
    Fin15AnchoredAtom1993 Fin15AnchoredAtom1994 Fin15AnchoredAtom2015 Fin15AnchoredAtom2016
    Fin15AnchoredAtom2022 Fin15AnchoredAtom2043 Fin15AnchoredAtom2044 Fin15AnchoredAtom2050
    Fin15AnchoredAtom2102 Fin15AnchoredAtom2210 Fin15AnchoredAtom2213 Fin15AnchoredAtom2214
    Fin15AnchoredAtom2235 Fin15AnchoredAtom2236 Fin15AnchoredAtom2242 Fin15AnchoredAtom2263
    Fin15AnchoredAtom2264 Fin15AnchoredAtom2270 Fin15AnchoredAtom2322 Fin15AnchoredAtom2632
    Fin15AnchoredAtom2633 Fin15AnchoredAtom2639 Fin15AnchoredAtom2691 Fin15AnchoredAtom2747
    Fin15AnchoredAtom2925 Fin15AnchoredAtom2928 Fin15AnchoredAtom2929 Fin15AnchoredAtom2950
    Fin15AnchoredAtom2951 Fin15AnchoredAtom2957 Fin15AnchoredAtom2978 Fin15AnchoredAtom2979
    Fin15AnchoredAtom2985 Fin15AnchoredAtom3037 Fin15AnchoredAtom3347 Fin15AnchoredAtom3348
    Fin15AnchoredAtom3354 Fin15AnchoredAtom3406 Fin15AnchoredAtom3462 Fin15AnchoredAtom3842
    Fin15AnchoredAtom3843 Fin15AnchoredAtom3849 Fin15AnchoredAtom3901 Fin15AnchoredAtom3957
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

theorem fin15Anchored_clause30724 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom1886 chi ∧
      ¬Fin15AnchoredAtom1992 chi ∧
      ¬Fin15AnchoredAtom1993 chi ∧
      ¬Fin15AnchoredAtom1994 chi ∧
      ¬Fin15AnchoredAtom2020 chi ∧
      ¬Fin15AnchoredAtom2021 chi ∧
      ¬Fin15AnchoredAtom2022 chi ∧
      ¬Fin15AnchoredAtom2048 chi ∧
      ¬Fin15AnchoredAtom2049 chi ∧
      ¬Fin15AnchoredAtom2050 chi ∧
      ¬Fin15AnchoredAtom2106 chi ∧
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
      ¬Fin15AnchoredAtom2637 chi ∧
      ¬Fin15AnchoredAtom2638 chi ∧
      ¬Fin15AnchoredAtom2639 chi ∧
      ¬Fin15AnchoredAtom2695 chi ∧
      ¬Fin15AnchoredAtom2751 chi ∧
      ¬Fin15AnchoredAtom2927 chi ∧
      ¬Fin15AnchoredAtom2928 chi ∧
      ¬Fin15AnchoredAtom2929 chi ∧
      ¬Fin15AnchoredAtom2955 chi ∧
      ¬Fin15AnchoredAtom2956 chi ∧
      ¬Fin15AnchoredAtom2957 chi ∧
      ¬Fin15AnchoredAtom2983 chi ∧
      ¬Fin15AnchoredAtom2984 chi ∧
      ¬Fin15AnchoredAtom2985 chi ∧
      ¬Fin15AnchoredAtom3041 chi ∧
      ¬Fin15AnchoredAtom3352 chi ∧
      ¬Fin15AnchoredAtom3353 chi ∧
      ¬Fin15AnchoredAtom3354 chi ∧
      ¬Fin15AnchoredAtom3410 chi ∧
      ¬Fin15AnchoredAtom3466 chi ∧
      ¬Fin15AnchoredAtom3847 chi ∧
      ¬Fin15AnchoredAtom3848 chi ∧
      ¬Fin15AnchoredAtom3849 chi ∧
      ¬Fin15AnchoredAtom3905 chi ∧
      ¬Fin15AnchoredAtom3961 chi ∧
      ¬Fin15AnchoredAtom4627 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 5, 6, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask28775
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1842 Fin15AnchoredAtom1848 Fin15AnchoredAtom1849
    Fin15AnchoredAtom1850 Fin15AnchoredAtom1856 Fin15AnchoredAtom1857 Fin15AnchoredAtom1858
    Fin15AnchoredAtom1884 Fin15AnchoredAtom1885 Fin15AnchoredAtom1886 Fin15AnchoredAtom1992
    Fin15AnchoredAtom1993 Fin15AnchoredAtom1994 Fin15AnchoredAtom2020 Fin15AnchoredAtom2021
    Fin15AnchoredAtom2022 Fin15AnchoredAtom2048 Fin15AnchoredAtom2049 Fin15AnchoredAtom2050
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2212 Fin15AnchoredAtom2213 Fin15AnchoredAtom2214
    Fin15AnchoredAtom2240 Fin15AnchoredAtom2241 Fin15AnchoredAtom2242 Fin15AnchoredAtom2268
    Fin15AnchoredAtom2269 Fin15AnchoredAtom2270 Fin15AnchoredAtom2326 Fin15AnchoredAtom2637
    Fin15AnchoredAtom2638 Fin15AnchoredAtom2639 Fin15AnchoredAtom2695 Fin15AnchoredAtom2751
    Fin15AnchoredAtom2927 Fin15AnchoredAtom2928 Fin15AnchoredAtom2929 Fin15AnchoredAtom2955
    Fin15AnchoredAtom2956 Fin15AnchoredAtom2957 Fin15AnchoredAtom2983 Fin15AnchoredAtom2984
    Fin15AnchoredAtom2985 Fin15AnchoredAtom3041 Fin15AnchoredAtom3352 Fin15AnchoredAtom3353
    Fin15AnchoredAtom3354 Fin15AnchoredAtom3410 Fin15AnchoredAtom3466 Fin15AnchoredAtom3847
    Fin15AnchoredAtom3848 Fin15AnchoredAtom3849 Fin15AnchoredAtom3905 Fin15AnchoredAtom3961
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

theorem fin15Anchored_clause30725 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom1996 chi ∧
      ¬Fin15AnchoredAtom1997 chi ∧
      ¬Fin15AnchoredAtom1999 chi ∧
      ¬Fin15AnchoredAtom2008 chi ∧
      ¬Fin15AnchoredAtom2010 chi ∧
      ¬Fin15AnchoredAtom2014 chi ∧
      ¬Fin15AnchoredAtom2057 chi ∧
      ¬Fin15AnchoredAtom2059 chi ∧
      ¬Fin15AnchoredAtom2063 chi ∧
      ¬Fin15AnchoredAtom2088 chi ∧
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
      ¬Fin15AnchoredAtom2646 chi ∧
      ¬Fin15AnchoredAtom2648 chi ∧
      ¬Fin15AnchoredAtom2652 chi ∧
      ¬Fin15AnchoredAtom2677 chi ∧
      ¬Fin15AnchoredAtom2768 chi ∧
      ¬Fin15AnchoredAtom2931 chi ∧
      ¬Fin15AnchoredAtom2932 chi ∧
      ¬Fin15AnchoredAtom2934 chi ∧
      ¬Fin15AnchoredAtom2943 chi ∧
      ¬Fin15AnchoredAtom2945 chi ∧
      ¬Fin15AnchoredAtom2949 chi ∧
      ¬Fin15AnchoredAtom2992 chi ∧
      ¬Fin15AnchoredAtom2994 chi ∧
      ¬Fin15AnchoredAtom2998 chi ∧
      ¬Fin15AnchoredAtom3023 chi ∧
      ¬Fin15AnchoredAtom3361 chi ∧
      ¬Fin15AnchoredAtom3363 chi ∧
      ¬Fin15AnchoredAtom3367 chi ∧
      ¬Fin15AnchoredAtom3392 chi ∧
      ¬Fin15AnchoredAtom3483 chi ∧
      ¬Fin15AnchoredAtom3856 chi ∧
      ¬Fin15AnchoredAtom3858 chi ∧
      ¬Fin15AnchoredAtom3862 chi ∧
      ¬Fin15AnchoredAtom3887 chi ∧
      ¬Fin15AnchoredAtom3978 chi ∧
      ¬Fin15AnchoredAtom4644 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 5, 7, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05799
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1843 Fin15AnchoredAtom1845 Fin15AnchoredAtom1846
    Fin15AnchoredAtom1848 Fin15AnchoredAtom1860 Fin15AnchoredAtom1861 Fin15AnchoredAtom1863
    Fin15AnchoredAtom1872 Fin15AnchoredAtom1874 Fin15AnchoredAtom1878 Fin15AnchoredAtom1996
    Fin15AnchoredAtom1997 Fin15AnchoredAtom1999 Fin15AnchoredAtom2008 Fin15AnchoredAtom2010
    Fin15AnchoredAtom2014 Fin15AnchoredAtom2057 Fin15AnchoredAtom2059 Fin15AnchoredAtom2063
    Fin15AnchoredAtom2088 Fin15AnchoredAtom2216 Fin15AnchoredAtom2217 Fin15AnchoredAtom2219
    Fin15AnchoredAtom2228 Fin15AnchoredAtom2230 Fin15AnchoredAtom2234 Fin15AnchoredAtom2277
    Fin15AnchoredAtom2279 Fin15AnchoredAtom2283 Fin15AnchoredAtom2308 Fin15AnchoredAtom2646
    Fin15AnchoredAtom2648 Fin15AnchoredAtom2652 Fin15AnchoredAtom2677 Fin15AnchoredAtom2768
    Fin15AnchoredAtom2931 Fin15AnchoredAtom2932 Fin15AnchoredAtom2934 Fin15AnchoredAtom2943
    Fin15AnchoredAtom2945 Fin15AnchoredAtom2949 Fin15AnchoredAtom2992 Fin15AnchoredAtom2994
    Fin15AnchoredAtom2998 Fin15AnchoredAtom3023 Fin15AnchoredAtom3361 Fin15AnchoredAtom3363
    Fin15AnchoredAtom3367 Fin15AnchoredAtom3392 Fin15AnchoredAtom3483 Fin15AnchoredAtom3856
    Fin15AnchoredAtom3858 Fin15AnchoredAtom3862 Fin15AnchoredAtom3887 Fin15AnchoredAtom3978
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

theorem fin15Anchored_clause30726 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom1996 chi ∧
      ¬Fin15AnchoredAtom1997 chi ∧
      ¬Fin15AnchoredAtom2000 chi ∧
      ¬Fin15AnchoredAtom2008 chi ∧
      ¬Fin15AnchoredAtom2011 chi ∧
      ¬Fin15AnchoredAtom2015 chi ∧
      ¬Fin15AnchoredAtom2057 chi ∧
      ¬Fin15AnchoredAtom2060 chi ∧
      ¬Fin15AnchoredAtom2064 chi ∧
      ¬Fin15AnchoredAtom2089 chi ∧
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
      ¬Fin15AnchoredAtom2646 chi ∧
      ¬Fin15AnchoredAtom2649 chi ∧
      ¬Fin15AnchoredAtom2653 chi ∧
      ¬Fin15AnchoredAtom2678 chi ∧
      ¬Fin15AnchoredAtom2769 chi ∧
      ¬Fin15AnchoredAtom2931 chi ∧
      ¬Fin15AnchoredAtom2932 chi ∧
      ¬Fin15AnchoredAtom2935 chi ∧
      ¬Fin15AnchoredAtom2943 chi ∧
      ¬Fin15AnchoredAtom2946 chi ∧
      ¬Fin15AnchoredAtom2950 chi ∧
      ¬Fin15AnchoredAtom2992 chi ∧
      ¬Fin15AnchoredAtom2995 chi ∧
      ¬Fin15AnchoredAtom2999 chi ∧
      ¬Fin15AnchoredAtom3024 chi ∧
      ¬Fin15AnchoredAtom3361 chi ∧
      ¬Fin15AnchoredAtom3364 chi ∧
      ¬Fin15AnchoredAtom3368 chi ∧
      ¬Fin15AnchoredAtom3393 chi ∧
      ¬Fin15AnchoredAtom3484 chi ∧
      ¬Fin15AnchoredAtom3856 chi ∧
      ¬Fin15AnchoredAtom3859 chi ∧
      ¬Fin15AnchoredAtom3863 chi ∧
      ¬Fin15AnchoredAtom3888 chi ∧
      ¬Fin15AnchoredAtom3979 chi ∧
      ¬Fin15AnchoredAtom4645 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 5, 7, 9, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09895
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1843 Fin15AnchoredAtom1845 Fin15AnchoredAtom1846
    Fin15AnchoredAtom1849 Fin15AnchoredAtom1860 Fin15AnchoredAtom1861 Fin15AnchoredAtom1864
    Fin15AnchoredAtom1872 Fin15AnchoredAtom1875 Fin15AnchoredAtom1879 Fin15AnchoredAtom1996
    Fin15AnchoredAtom1997 Fin15AnchoredAtom2000 Fin15AnchoredAtom2008 Fin15AnchoredAtom2011
    Fin15AnchoredAtom2015 Fin15AnchoredAtom2057 Fin15AnchoredAtom2060 Fin15AnchoredAtom2064
    Fin15AnchoredAtom2089 Fin15AnchoredAtom2216 Fin15AnchoredAtom2217 Fin15AnchoredAtom2220
    Fin15AnchoredAtom2228 Fin15AnchoredAtom2231 Fin15AnchoredAtom2235 Fin15AnchoredAtom2277
    Fin15AnchoredAtom2280 Fin15AnchoredAtom2284 Fin15AnchoredAtom2309 Fin15AnchoredAtom2646
    Fin15AnchoredAtom2649 Fin15AnchoredAtom2653 Fin15AnchoredAtom2678 Fin15AnchoredAtom2769
    Fin15AnchoredAtom2931 Fin15AnchoredAtom2932 Fin15AnchoredAtom2935 Fin15AnchoredAtom2943
    Fin15AnchoredAtom2946 Fin15AnchoredAtom2950 Fin15AnchoredAtom2992 Fin15AnchoredAtom2995
    Fin15AnchoredAtom2999 Fin15AnchoredAtom3024 Fin15AnchoredAtom3361 Fin15AnchoredAtom3364
    Fin15AnchoredAtom3368 Fin15AnchoredAtom3393 Fin15AnchoredAtom3484 Fin15AnchoredAtom3856
    Fin15AnchoredAtom3859 Fin15AnchoredAtom3863 Fin15AnchoredAtom3888 Fin15AnchoredAtom3979
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

theorem fin15Anchored_clause30727 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom1996 chi ∧
      ¬Fin15AnchoredAtom1997 chi ∧
      ¬Fin15AnchoredAtom2001 chi ∧
      ¬Fin15AnchoredAtom2008 chi ∧
      ¬Fin15AnchoredAtom2012 chi ∧
      ¬Fin15AnchoredAtom2016 chi ∧
      ¬Fin15AnchoredAtom2057 chi ∧
      ¬Fin15AnchoredAtom2061 chi ∧
      ¬Fin15AnchoredAtom2065 chi ∧
      ¬Fin15AnchoredAtom2090 chi ∧
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
      ¬Fin15AnchoredAtom2646 chi ∧
      ¬Fin15AnchoredAtom2650 chi ∧
      ¬Fin15AnchoredAtom2654 chi ∧
      ¬Fin15AnchoredAtom2679 chi ∧
      ¬Fin15AnchoredAtom2770 chi ∧
      ¬Fin15AnchoredAtom2931 chi ∧
      ¬Fin15AnchoredAtom2932 chi ∧
      ¬Fin15AnchoredAtom2936 chi ∧
      ¬Fin15AnchoredAtom2943 chi ∧
      ¬Fin15AnchoredAtom2947 chi ∧
      ¬Fin15AnchoredAtom2951 chi ∧
      ¬Fin15AnchoredAtom2992 chi ∧
      ¬Fin15AnchoredAtom2996 chi ∧
      ¬Fin15AnchoredAtom3000 chi ∧
      ¬Fin15AnchoredAtom3025 chi ∧
      ¬Fin15AnchoredAtom3361 chi ∧
      ¬Fin15AnchoredAtom3365 chi ∧
      ¬Fin15AnchoredAtom3369 chi ∧
      ¬Fin15AnchoredAtom3394 chi ∧
      ¬Fin15AnchoredAtom3485 chi ∧
      ¬Fin15AnchoredAtom3856 chi ∧
      ¬Fin15AnchoredAtom3860 chi ∧
      ¬Fin15AnchoredAtom3864 chi ∧
      ¬Fin15AnchoredAtom3889 chi ∧
      ¬Fin15AnchoredAtom3980 chi ∧
      ¬Fin15AnchoredAtom4646 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 5, 7, 9, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask18087
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1843 Fin15AnchoredAtom1845 Fin15AnchoredAtom1846
    Fin15AnchoredAtom1850 Fin15AnchoredAtom1860 Fin15AnchoredAtom1861 Fin15AnchoredAtom1865
    Fin15AnchoredAtom1872 Fin15AnchoredAtom1876 Fin15AnchoredAtom1880 Fin15AnchoredAtom1996
    Fin15AnchoredAtom1997 Fin15AnchoredAtom2001 Fin15AnchoredAtom2008 Fin15AnchoredAtom2012
    Fin15AnchoredAtom2016 Fin15AnchoredAtom2057 Fin15AnchoredAtom2061 Fin15AnchoredAtom2065
    Fin15AnchoredAtom2090 Fin15AnchoredAtom2216 Fin15AnchoredAtom2217 Fin15AnchoredAtom2221
    Fin15AnchoredAtom2228 Fin15AnchoredAtom2232 Fin15AnchoredAtom2236 Fin15AnchoredAtom2277
    Fin15AnchoredAtom2281 Fin15AnchoredAtom2285 Fin15AnchoredAtom2310 Fin15AnchoredAtom2646
    Fin15AnchoredAtom2650 Fin15AnchoredAtom2654 Fin15AnchoredAtom2679 Fin15AnchoredAtom2770
    Fin15AnchoredAtom2931 Fin15AnchoredAtom2932 Fin15AnchoredAtom2936 Fin15AnchoredAtom2943
    Fin15AnchoredAtom2947 Fin15AnchoredAtom2951 Fin15AnchoredAtom2992 Fin15AnchoredAtom2996
    Fin15AnchoredAtom3000 Fin15AnchoredAtom3025 Fin15AnchoredAtom3361 Fin15AnchoredAtom3365
    Fin15AnchoredAtom3369 Fin15AnchoredAtom3394 Fin15AnchoredAtom3485 Fin15AnchoredAtom3856
    Fin15AnchoredAtom3860 Fin15AnchoredAtom3864 Fin15AnchoredAtom3889 Fin15AnchoredAtom3980
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

theorem fin15Anchored_clause30728 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom1996 chi ∧
      ¬Fin15AnchoredAtom1999 chi ∧
      ¬Fin15AnchoredAtom2000 chi ∧
      ¬Fin15AnchoredAtom2010 chi ∧
      ¬Fin15AnchoredAtom2011 chi ∧
      ¬Fin15AnchoredAtom2020 chi ∧
      ¬Fin15AnchoredAtom2059 chi ∧
      ¬Fin15AnchoredAtom2060 chi ∧
      ¬Fin15AnchoredAtom2069 chi ∧
      ¬Fin15AnchoredAtom2094 chi ∧
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
      ¬Fin15AnchoredAtom2648 chi ∧
      ¬Fin15AnchoredAtom2649 chi ∧
      ¬Fin15AnchoredAtom2658 chi ∧
      ¬Fin15AnchoredAtom2683 chi ∧
      ¬Fin15AnchoredAtom2774 chi ∧
      ¬Fin15AnchoredAtom2931 chi ∧
      ¬Fin15AnchoredAtom2934 chi ∧
      ¬Fin15AnchoredAtom2935 chi ∧
      ¬Fin15AnchoredAtom2945 chi ∧
      ¬Fin15AnchoredAtom2946 chi ∧
      ¬Fin15AnchoredAtom2955 chi ∧
      ¬Fin15AnchoredAtom2994 chi ∧
      ¬Fin15AnchoredAtom2995 chi ∧
      ¬Fin15AnchoredAtom3004 chi ∧
      ¬Fin15AnchoredAtom3029 chi ∧
      ¬Fin15AnchoredAtom3363 chi ∧
      ¬Fin15AnchoredAtom3364 chi ∧
      ¬Fin15AnchoredAtom3373 chi ∧
      ¬Fin15AnchoredAtom3398 chi ∧
      ¬Fin15AnchoredAtom3489 chi ∧
      ¬Fin15AnchoredAtom3858 chi ∧
      ¬Fin15AnchoredAtom3859 chi ∧
      ¬Fin15AnchoredAtom3868 chi ∧
      ¬Fin15AnchoredAtom3893 chi ∧
      ¬Fin15AnchoredAtom3984 chi ∧
      ¬Fin15AnchoredAtom4650 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 5, 7, 9, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask12967
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1843 Fin15AnchoredAtom1845 Fin15AnchoredAtom1848
    Fin15AnchoredAtom1849 Fin15AnchoredAtom1860 Fin15AnchoredAtom1863 Fin15AnchoredAtom1864
    Fin15AnchoredAtom1874 Fin15AnchoredAtom1875 Fin15AnchoredAtom1884 Fin15AnchoredAtom1996
    Fin15AnchoredAtom1999 Fin15AnchoredAtom2000 Fin15AnchoredAtom2010 Fin15AnchoredAtom2011
    Fin15AnchoredAtom2020 Fin15AnchoredAtom2059 Fin15AnchoredAtom2060 Fin15AnchoredAtom2069
    Fin15AnchoredAtom2094 Fin15AnchoredAtom2216 Fin15AnchoredAtom2219 Fin15AnchoredAtom2220
    Fin15AnchoredAtom2230 Fin15AnchoredAtom2231 Fin15AnchoredAtom2240 Fin15AnchoredAtom2279
    Fin15AnchoredAtom2280 Fin15AnchoredAtom2289 Fin15AnchoredAtom2314 Fin15AnchoredAtom2648
    Fin15AnchoredAtom2649 Fin15AnchoredAtom2658 Fin15AnchoredAtom2683 Fin15AnchoredAtom2774
    Fin15AnchoredAtom2931 Fin15AnchoredAtom2934 Fin15AnchoredAtom2935 Fin15AnchoredAtom2945
    Fin15AnchoredAtom2946 Fin15AnchoredAtom2955 Fin15AnchoredAtom2994 Fin15AnchoredAtom2995
    Fin15AnchoredAtom3004 Fin15AnchoredAtom3029 Fin15AnchoredAtom3363 Fin15AnchoredAtom3364
    Fin15AnchoredAtom3373 Fin15AnchoredAtom3398 Fin15AnchoredAtom3489 Fin15AnchoredAtom3858
    Fin15AnchoredAtom3859 Fin15AnchoredAtom3868 Fin15AnchoredAtom3893 Fin15AnchoredAtom3984
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

theorem fin15Anchored_clause30729 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom1996 chi ∧
      ¬Fin15AnchoredAtom1999 chi ∧
      ¬Fin15AnchoredAtom2001 chi ∧
      ¬Fin15AnchoredAtom2010 chi ∧
      ¬Fin15AnchoredAtom2012 chi ∧
      ¬Fin15AnchoredAtom2021 chi ∧
      ¬Fin15AnchoredAtom2059 chi ∧
      ¬Fin15AnchoredAtom2061 chi ∧
      ¬Fin15AnchoredAtom2070 chi ∧
      ¬Fin15AnchoredAtom2095 chi ∧
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
      ¬Fin15AnchoredAtom2648 chi ∧
      ¬Fin15AnchoredAtom2650 chi ∧
      ¬Fin15AnchoredAtom2659 chi ∧
      ¬Fin15AnchoredAtom2684 chi ∧
      ¬Fin15AnchoredAtom2775 chi ∧
      ¬Fin15AnchoredAtom2931 chi ∧
      ¬Fin15AnchoredAtom2934 chi ∧
      ¬Fin15AnchoredAtom2936 chi ∧
      ¬Fin15AnchoredAtom2945 chi ∧
      ¬Fin15AnchoredAtom2947 chi ∧
      ¬Fin15AnchoredAtom2956 chi ∧
      ¬Fin15AnchoredAtom2994 chi ∧
      ¬Fin15AnchoredAtom2996 chi ∧
      ¬Fin15AnchoredAtom3005 chi ∧
      ¬Fin15AnchoredAtom3030 chi ∧
      ¬Fin15AnchoredAtom3363 chi ∧
      ¬Fin15AnchoredAtom3365 chi ∧
      ¬Fin15AnchoredAtom3374 chi ∧
      ¬Fin15AnchoredAtom3399 chi ∧
      ¬Fin15AnchoredAtom3490 chi ∧
      ¬Fin15AnchoredAtom3858 chi ∧
      ¬Fin15AnchoredAtom3860 chi ∧
      ¬Fin15AnchoredAtom3869 chi ∧
      ¬Fin15AnchoredAtom3894 chi ∧
      ¬Fin15AnchoredAtom3985 chi ∧
      ¬Fin15AnchoredAtom4651 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 5, 7, 9, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21159
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1843 Fin15AnchoredAtom1845 Fin15AnchoredAtom1848
    Fin15AnchoredAtom1850 Fin15AnchoredAtom1860 Fin15AnchoredAtom1863 Fin15AnchoredAtom1865
    Fin15AnchoredAtom1874 Fin15AnchoredAtom1876 Fin15AnchoredAtom1885 Fin15AnchoredAtom1996
    Fin15AnchoredAtom1999 Fin15AnchoredAtom2001 Fin15AnchoredAtom2010 Fin15AnchoredAtom2012
    Fin15AnchoredAtom2021 Fin15AnchoredAtom2059 Fin15AnchoredAtom2061 Fin15AnchoredAtom2070
    Fin15AnchoredAtom2095 Fin15AnchoredAtom2216 Fin15AnchoredAtom2219 Fin15AnchoredAtom2221
    Fin15AnchoredAtom2230 Fin15AnchoredAtom2232 Fin15AnchoredAtom2241 Fin15AnchoredAtom2279
    Fin15AnchoredAtom2281 Fin15AnchoredAtom2290 Fin15AnchoredAtom2315 Fin15AnchoredAtom2648
    Fin15AnchoredAtom2650 Fin15AnchoredAtom2659 Fin15AnchoredAtom2684 Fin15AnchoredAtom2775
    Fin15AnchoredAtom2931 Fin15AnchoredAtom2934 Fin15AnchoredAtom2936 Fin15AnchoredAtom2945
    Fin15AnchoredAtom2947 Fin15AnchoredAtom2956 Fin15AnchoredAtom2994 Fin15AnchoredAtom2996
    Fin15AnchoredAtom3005 Fin15AnchoredAtom3030 Fin15AnchoredAtom3363 Fin15AnchoredAtom3365
    Fin15AnchoredAtom3374 Fin15AnchoredAtom3399 Fin15AnchoredAtom3490 Fin15AnchoredAtom3858
    Fin15AnchoredAtom3860 Fin15AnchoredAtom3869 Fin15AnchoredAtom3894 Fin15AnchoredAtom3985
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

theorem fin15Anchored_clause30730 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom1886 chi ∧
      ¬Fin15AnchoredAtom1996 chi ∧
      ¬Fin15AnchoredAtom2000 chi ∧
      ¬Fin15AnchoredAtom2001 chi ∧
      ¬Fin15AnchoredAtom2011 chi ∧
      ¬Fin15AnchoredAtom2012 chi ∧
      ¬Fin15AnchoredAtom2022 chi ∧
      ¬Fin15AnchoredAtom2060 chi ∧
      ¬Fin15AnchoredAtom2061 chi ∧
      ¬Fin15AnchoredAtom2071 chi ∧
      ¬Fin15AnchoredAtom2096 chi ∧
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
      ¬Fin15AnchoredAtom2649 chi ∧
      ¬Fin15AnchoredAtom2650 chi ∧
      ¬Fin15AnchoredAtom2660 chi ∧
      ¬Fin15AnchoredAtom2685 chi ∧
      ¬Fin15AnchoredAtom2776 chi ∧
      ¬Fin15AnchoredAtom2931 chi ∧
      ¬Fin15AnchoredAtom2935 chi ∧
      ¬Fin15AnchoredAtom2936 chi ∧
      ¬Fin15AnchoredAtom2946 chi ∧
      ¬Fin15AnchoredAtom2947 chi ∧
      ¬Fin15AnchoredAtom2957 chi ∧
      ¬Fin15AnchoredAtom2995 chi ∧
      ¬Fin15AnchoredAtom2996 chi ∧
      ¬Fin15AnchoredAtom3006 chi ∧
      ¬Fin15AnchoredAtom3031 chi ∧
      ¬Fin15AnchoredAtom3364 chi ∧
      ¬Fin15AnchoredAtom3365 chi ∧
      ¬Fin15AnchoredAtom3375 chi ∧
      ¬Fin15AnchoredAtom3400 chi ∧
      ¬Fin15AnchoredAtom3491 chi ∧
      ¬Fin15AnchoredAtom3859 chi ∧
      ¬Fin15AnchoredAtom3860 chi ∧
      ¬Fin15AnchoredAtom3870 chi ∧
      ¬Fin15AnchoredAtom3895 chi ∧
      ¬Fin15AnchoredAtom3986 chi ∧
      ¬Fin15AnchoredAtom4652 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 5, 7, 9, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25255
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1843 Fin15AnchoredAtom1845 Fin15AnchoredAtom1849
    Fin15AnchoredAtom1850 Fin15AnchoredAtom1860 Fin15AnchoredAtom1864 Fin15AnchoredAtom1865
    Fin15AnchoredAtom1875 Fin15AnchoredAtom1876 Fin15AnchoredAtom1886 Fin15AnchoredAtom1996
    Fin15AnchoredAtom2000 Fin15AnchoredAtom2001 Fin15AnchoredAtom2011 Fin15AnchoredAtom2012
    Fin15AnchoredAtom2022 Fin15AnchoredAtom2060 Fin15AnchoredAtom2061 Fin15AnchoredAtom2071
    Fin15AnchoredAtom2096 Fin15AnchoredAtom2216 Fin15AnchoredAtom2220 Fin15AnchoredAtom2221
    Fin15AnchoredAtom2231 Fin15AnchoredAtom2232 Fin15AnchoredAtom2242 Fin15AnchoredAtom2280
    Fin15AnchoredAtom2281 Fin15AnchoredAtom2291 Fin15AnchoredAtom2316 Fin15AnchoredAtom2649
    Fin15AnchoredAtom2650 Fin15AnchoredAtom2660 Fin15AnchoredAtom2685 Fin15AnchoredAtom2776
    Fin15AnchoredAtom2931 Fin15AnchoredAtom2935 Fin15AnchoredAtom2936 Fin15AnchoredAtom2946
    Fin15AnchoredAtom2947 Fin15AnchoredAtom2957 Fin15AnchoredAtom2995 Fin15AnchoredAtom2996
    Fin15AnchoredAtom3006 Fin15AnchoredAtom3031 Fin15AnchoredAtom3364 Fin15AnchoredAtom3365
    Fin15AnchoredAtom3375 Fin15AnchoredAtom3400 Fin15AnchoredAtom3491 Fin15AnchoredAtom3859
    Fin15AnchoredAtom3860 Fin15AnchoredAtom3870 Fin15AnchoredAtom3895 Fin15AnchoredAtom3986
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

theorem fin15Anchored_clause30731 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom1997 chi ∧
      ¬Fin15AnchoredAtom1999 chi ∧
      ¬Fin15AnchoredAtom2000 chi ∧
      ¬Fin15AnchoredAtom2014 chi ∧
      ¬Fin15AnchoredAtom2015 chi ∧
      ¬Fin15AnchoredAtom2020 chi ∧
      ¬Fin15AnchoredAtom2063 chi ∧
      ¬Fin15AnchoredAtom2064 chi ∧
      ¬Fin15AnchoredAtom2069 chi ∧
      ¬Fin15AnchoredAtom2100 chi ∧
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
      ¬Fin15AnchoredAtom2652 chi ∧
      ¬Fin15AnchoredAtom2653 chi ∧
      ¬Fin15AnchoredAtom2658 chi ∧
      ¬Fin15AnchoredAtom2689 chi ∧
      ¬Fin15AnchoredAtom2780 chi ∧
      ¬Fin15AnchoredAtom2932 chi ∧
      ¬Fin15AnchoredAtom2934 chi ∧
      ¬Fin15AnchoredAtom2935 chi ∧
      ¬Fin15AnchoredAtom2949 chi ∧
      ¬Fin15AnchoredAtom2950 chi ∧
      ¬Fin15AnchoredAtom2955 chi ∧
      ¬Fin15AnchoredAtom2998 chi ∧
      ¬Fin15AnchoredAtom2999 chi ∧
      ¬Fin15AnchoredAtom3004 chi ∧
      ¬Fin15AnchoredAtom3035 chi ∧
      ¬Fin15AnchoredAtom3367 chi ∧
      ¬Fin15AnchoredAtom3368 chi ∧
      ¬Fin15AnchoredAtom3373 chi ∧
      ¬Fin15AnchoredAtom3404 chi ∧
      ¬Fin15AnchoredAtom3495 chi ∧
      ¬Fin15AnchoredAtom3862 chi ∧
      ¬Fin15AnchoredAtom3863 chi ∧
      ¬Fin15AnchoredAtom3868 chi ∧
      ¬Fin15AnchoredAtom3899 chi ∧
      ¬Fin15AnchoredAtom3990 chi ∧
      ¬Fin15AnchoredAtom4656 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 5, 7, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13479
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1843 Fin15AnchoredAtom1846 Fin15AnchoredAtom1848
    Fin15AnchoredAtom1849 Fin15AnchoredAtom1861 Fin15AnchoredAtom1863 Fin15AnchoredAtom1864
    Fin15AnchoredAtom1878 Fin15AnchoredAtom1879 Fin15AnchoredAtom1884 Fin15AnchoredAtom1997
    Fin15AnchoredAtom1999 Fin15AnchoredAtom2000 Fin15AnchoredAtom2014 Fin15AnchoredAtom2015
    Fin15AnchoredAtom2020 Fin15AnchoredAtom2063 Fin15AnchoredAtom2064 Fin15AnchoredAtom2069
    Fin15AnchoredAtom2100 Fin15AnchoredAtom2217 Fin15AnchoredAtom2219 Fin15AnchoredAtom2220
    Fin15AnchoredAtom2234 Fin15AnchoredAtom2235 Fin15AnchoredAtom2240 Fin15AnchoredAtom2283
    Fin15AnchoredAtom2284 Fin15AnchoredAtom2289 Fin15AnchoredAtom2320 Fin15AnchoredAtom2652
    Fin15AnchoredAtom2653 Fin15AnchoredAtom2658 Fin15AnchoredAtom2689 Fin15AnchoredAtom2780
    Fin15AnchoredAtom2932 Fin15AnchoredAtom2934 Fin15AnchoredAtom2935 Fin15AnchoredAtom2949
    Fin15AnchoredAtom2950 Fin15AnchoredAtom2955 Fin15AnchoredAtom2998 Fin15AnchoredAtom2999
    Fin15AnchoredAtom3004 Fin15AnchoredAtom3035 Fin15AnchoredAtom3367 Fin15AnchoredAtom3368
    Fin15AnchoredAtom3373 Fin15AnchoredAtom3404 Fin15AnchoredAtom3495 Fin15AnchoredAtom3862
    Fin15AnchoredAtom3863 Fin15AnchoredAtom3868 Fin15AnchoredAtom3899 Fin15AnchoredAtom3990
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

theorem fin15Anchored_clause30732 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom1997 chi ∧
      ¬Fin15AnchoredAtom1999 chi ∧
      ¬Fin15AnchoredAtom2001 chi ∧
      ¬Fin15AnchoredAtom2014 chi ∧
      ¬Fin15AnchoredAtom2016 chi ∧
      ¬Fin15AnchoredAtom2021 chi ∧
      ¬Fin15AnchoredAtom2063 chi ∧
      ¬Fin15AnchoredAtom2065 chi ∧
      ¬Fin15AnchoredAtom2070 chi ∧
      ¬Fin15AnchoredAtom2101 chi ∧
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
      ¬Fin15AnchoredAtom2652 chi ∧
      ¬Fin15AnchoredAtom2654 chi ∧
      ¬Fin15AnchoredAtom2659 chi ∧
      ¬Fin15AnchoredAtom2690 chi ∧
      ¬Fin15AnchoredAtom2781 chi ∧
      ¬Fin15AnchoredAtom2932 chi ∧
      ¬Fin15AnchoredAtom2934 chi ∧
      ¬Fin15AnchoredAtom2936 chi ∧
      ¬Fin15AnchoredAtom2949 chi ∧
      ¬Fin15AnchoredAtom2951 chi ∧
      ¬Fin15AnchoredAtom2956 chi ∧
      ¬Fin15AnchoredAtom2998 chi ∧
      ¬Fin15AnchoredAtom3000 chi ∧
      ¬Fin15AnchoredAtom3005 chi ∧
      ¬Fin15AnchoredAtom3036 chi ∧
      ¬Fin15AnchoredAtom3367 chi ∧
      ¬Fin15AnchoredAtom3369 chi ∧
      ¬Fin15AnchoredAtom3374 chi ∧
      ¬Fin15AnchoredAtom3405 chi ∧
      ¬Fin15AnchoredAtom3496 chi ∧
      ¬Fin15AnchoredAtom3862 chi ∧
      ¬Fin15AnchoredAtom3864 chi ∧
      ¬Fin15AnchoredAtom3869 chi ∧
      ¬Fin15AnchoredAtom3900 chi ∧
      ¬Fin15AnchoredAtom3991 chi ∧
      ¬Fin15AnchoredAtom4657 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 5, 7, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21671
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1843 Fin15AnchoredAtom1846 Fin15AnchoredAtom1848
    Fin15AnchoredAtom1850 Fin15AnchoredAtom1861 Fin15AnchoredAtom1863 Fin15AnchoredAtom1865
    Fin15AnchoredAtom1878 Fin15AnchoredAtom1880 Fin15AnchoredAtom1885 Fin15AnchoredAtom1997
    Fin15AnchoredAtom1999 Fin15AnchoredAtom2001 Fin15AnchoredAtom2014 Fin15AnchoredAtom2016
    Fin15AnchoredAtom2021 Fin15AnchoredAtom2063 Fin15AnchoredAtom2065 Fin15AnchoredAtom2070
    Fin15AnchoredAtom2101 Fin15AnchoredAtom2217 Fin15AnchoredAtom2219 Fin15AnchoredAtom2221
    Fin15AnchoredAtom2234 Fin15AnchoredAtom2236 Fin15AnchoredAtom2241 Fin15AnchoredAtom2283
    Fin15AnchoredAtom2285 Fin15AnchoredAtom2290 Fin15AnchoredAtom2321 Fin15AnchoredAtom2652
    Fin15AnchoredAtom2654 Fin15AnchoredAtom2659 Fin15AnchoredAtom2690 Fin15AnchoredAtom2781
    Fin15AnchoredAtom2932 Fin15AnchoredAtom2934 Fin15AnchoredAtom2936 Fin15AnchoredAtom2949
    Fin15AnchoredAtom2951 Fin15AnchoredAtom2956 Fin15AnchoredAtom2998 Fin15AnchoredAtom3000
    Fin15AnchoredAtom3005 Fin15AnchoredAtom3036 Fin15AnchoredAtom3367 Fin15AnchoredAtom3369
    Fin15AnchoredAtom3374 Fin15AnchoredAtom3405 Fin15AnchoredAtom3496 Fin15AnchoredAtom3862
    Fin15AnchoredAtom3864 Fin15AnchoredAtom3869 Fin15AnchoredAtom3900 Fin15AnchoredAtom3991
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

theorem fin15Anchored_clause30733 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom1886 chi ∧
      ¬Fin15AnchoredAtom1997 chi ∧
      ¬Fin15AnchoredAtom2000 chi ∧
      ¬Fin15AnchoredAtom2001 chi ∧
      ¬Fin15AnchoredAtom2015 chi ∧
      ¬Fin15AnchoredAtom2016 chi ∧
      ¬Fin15AnchoredAtom2022 chi ∧
      ¬Fin15AnchoredAtom2064 chi ∧
      ¬Fin15AnchoredAtom2065 chi ∧
      ¬Fin15AnchoredAtom2071 chi ∧
      ¬Fin15AnchoredAtom2102 chi ∧
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
      ¬Fin15AnchoredAtom2653 chi ∧
      ¬Fin15AnchoredAtom2654 chi ∧
      ¬Fin15AnchoredAtom2660 chi ∧
      ¬Fin15AnchoredAtom2691 chi ∧
      ¬Fin15AnchoredAtom2782 chi ∧
      ¬Fin15AnchoredAtom2932 chi ∧
      ¬Fin15AnchoredAtom2935 chi ∧
      ¬Fin15AnchoredAtom2936 chi ∧
      ¬Fin15AnchoredAtom2950 chi ∧
      ¬Fin15AnchoredAtom2951 chi ∧
      ¬Fin15AnchoredAtom2957 chi ∧
      ¬Fin15AnchoredAtom2999 chi ∧
      ¬Fin15AnchoredAtom3000 chi ∧
      ¬Fin15AnchoredAtom3006 chi ∧
      ¬Fin15AnchoredAtom3037 chi ∧
      ¬Fin15AnchoredAtom3368 chi ∧
      ¬Fin15AnchoredAtom3369 chi ∧
      ¬Fin15AnchoredAtom3375 chi ∧
      ¬Fin15AnchoredAtom3406 chi ∧
      ¬Fin15AnchoredAtom3497 chi ∧
      ¬Fin15AnchoredAtom3863 chi ∧
      ¬Fin15AnchoredAtom3864 chi ∧
      ¬Fin15AnchoredAtom3870 chi ∧
      ¬Fin15AnchoredAtom3901 chi ∧
      ¬Fin15AnchoredAtom3992 chi ∧
      ¬Fin15AnchoredAtom4658 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 5, 7, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25767
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1843 Fin15AnchoredAtom1846 Fin15AnchoredAtom1849
    Fin15AnchoredAtom1850 Fin15AnchoredAtom1861 Fin15AnchoredAtom1864 Fin15AnchoredAtom1865
    Fin15AnchoredAtom1879 Fin15AnchoredAtom1880 Fin15AnchoredAtom1886 Fin15AnchoredAtom1997
    Fin15AnchoredAtom2000 Fin15AnchoredAtom2001 Fin15AnchoredAtom2015 Fin15AnchoredAtom2016
    Fin15AnchoredAtom2022 Fin15AnchoredAtom2064 Fin15AnchoredAtom2065 Fin15AnchoredAtom2071
    Fin15AnchoredAtom2102 Fin15AnchoredAtom2217 Fin15AnchoredAtom2220 Fin15AnchoredAtom2221
    Fin15AnchoredAtom2235 Fin15AnchoredAtom2236 Fin15AnchoredAtom2242 Fin15AnchoredAtom2284
    Fin15AnchoredAtom2285 Fin15AnchoredAtom2291 Fin15AnchoredAtom2322 Fin15AnchoredAtom2653
    Fin15AnchoredAtom2654 Fin15AnchoredAtom2660 Fin15AnchoredAtom2691 Fin15AnchoredAtom2782
    Fin15AnchoredAtom2932 Fin15AnchoredAtom2935 Fin15AnchoredAtom2936 Fin15AnchoredAtom2950
    Fin15AnchoredAtom2951 Fin15AnchoredAtom2957 Fin15AnchoredAtom2999 Fin15AnchoredAtom3000
    Fin15AnchoredAtom3006 Fin15AnchoredAtom3037 Fin15AnchoredAtom3368 Fin15AnchoredAtom3369
    Fin15AnchoredAtom3375 Fin15AnchoredAtom3406 Fin15AnchoredAtom3497 Fin15AnchoredAtom3863
    Fin15AnchoredAtom3864 Fin15AnchoredAtom3870 Fin15AnchoredAtom3901 Fin15AnchoredAtom3992
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

theorem fin15Anchored_clause30734 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom1886 chi ∧
      ¬Fin15AnchoredAtom1999 chi ∧
      ¬Fin15AnchoredAtom2000 chi ∧
      ¬Fin15AnchoredAtom2001 chi ∧
      ¬Fin15AnchoredAtom2020 chi ∧
      ¬Fin15AnchoredAtom2021 chi ∧
      ¬Fin15AnchoredAtom2022 chi ∧
      ¬Fin15AnchoredAtom2069 chi ∧
      ¬Fin15AnchoredAtom2070 chi ∧
      ¬Fin15AnchoredAtom2071 chi ∧
      ¬Fin15AnchoredAtom2106 chi ∧
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
      ¬Fin15AnchoredAtom2658 chi ∧
      ¬Fin15AnchoredAtom2659 chi ∧
      ¬Fin15AnchoredAtom2660 chi ∧
      ¬Fin15AnchoredAtom2695 chi ∧
      ¬Fin15AnchoredAtom2786 chi ∧
      ¬Fin15AnchoredAtom2934 chi ∧
      ¬Fin15AnchoredAtom2935 chi ∧
      ¬Fin15AnchoredAtom2936 chi ∧
      ¬Fin15AnchoredAtom2955 chi ∧
      ¬Fin15AnchoredAtom2956 chi ∧
      ¬Fin15AnchoredAtom2957 chi ∧
      ¬Fin15AnchoredAtom3004 chi ∧
      ¬Fin15AnchoredAtom3005 chi ∧
      ¬Fin15AnchoredAtom3006 chi ∧
      ¬Fin15AnchoredAtom3041 chi ∧
      ¬Fin15AnchoredAtom3373 chi ∧
      ¬Fin15AnchoredAtom3374 chi ∧
      ¬Fin15AnchoredAtom3375 chi ∧
      ¬Fin15AnchoredAtom3410 chi ∧
      ¬Fin15AnchoredAtom3501 chi ∧
      ¬Fin15AnchoredAtom3868 chi ∧
      ¬Fin15AnchoredAtom3869 chi ∧
      ¬Fin15AnchoredAtom3870 chi ∧
      ¬Fin15AnchoredAtom3905 chi ∧
      ¬Fin15AnchoredAtom3996 chi ∧
      ¬Fin15AnchoredAtom4662 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 5, 7, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask28839
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1843 Fin15AnchoredAtom1848 Fin15AnchoredAtom1849
    Fin15AnchoredAtom1850 Fin15AnchoredAtom1863 Fin15AnchoredAtom1864 Fin15AnchoredAtom1865
    Fin15AnchoredAtom1884 Fin15AnchoredAtom1885 Fin15AnchoredAtom1886 Fin15AnchoredAtom1999
    Fin15AnchoredAtom2000 Fin15AnchoredAtom2001 Fin15AnchoredAtom2020 Fin15AnchoredAtom2021
    Fin15AnchoredAtom2022 Fin15AnchoredAtom2069 Fin15AnchoredAtom2070 Fin15AnchoredAtom2071
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2219 Fin15AnchoredAtom2220 Fin15AnchoredAtom2221
    Fin15AnchoredAtom2240 Fin15AnchoredAtom2241 Fin15AnchoredAtom2242 Fin15AnchoredAtom2289
    Fin15AnchoredAtom2290 Fin15AnchoredAtom2291 Fin15AnchoredAtom2326 Fin15AnchoredAtom2658
    Fin15AnchoredAtom2659 Fin15AnchoredAtom2660 Fin15AnchoredAtom2695 Fin15AnchoredAtom2786
    Fin15AnchoredAtom2934 Fin15AnchoredAtom2935 Fin15AnchoredAtom2936 Fin15AnchoredAtom2955
    Fin15AnchoredAtom2956 Fin15AnchoredAtom2957 Fin15AnchoredAtom3004 Fin15AnchoredAtom3005
    Fin15AnchoredAtom3006 Fin15AnchoredAtom3041 Fin15AnchoredAtom3373 Fin15AnchoredAtom3374
    Fin15AnchoredAtom3375 Fin15AnchoredAtom3410 Fin15AnchoredAtom3501 Fin15AnchoredAtom3868
    Fin15AnchoredAtom3869 Fin15AnchoredAtom3870 Fin15AnchoredAtom3905 Fin15AnchoredAtom3996
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

theorem fin15Anchored_clause30735 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom2008 chi ∧
      ¬Fin15AnchoredAtom2010 chi ∧
      ¬Fin15AnchoredAtom2011 chi ∧
      ¬Fin15AnchoredAtom2014 chi ∧
      ¬Fin15AnchoredAtom2015 chi ∧
      ¬Fin15AnchoredAtom2020 chi ∧
      ¬Fin15AnchoredAtom2088 chi ∧
      ¬Fin15AnchoredAtom2089 chi ∧
      ¬Fin15AnchoredAtom2094 chi ∧
      ¬Fin15AnchoredAtom2100 chi ∧
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
      ¬Fin15AnchoredAtom2677 chi ∧
      ¬Fin15AnchoredAtom2678 chi ∧
      ¬Fin15AnchoredAtom2683 chi ∧
      ¬Fin15AnchoredAtom2689 chi ∧
      ¬Fin15AnchoredAtom2810 chi ∧
      ¬Fin15AnchoredAtom2943 chi ∧
      ¬Fin15AnchoredAtom2945 chi ∧
      ¬Fin15AnchoredAtom2946 chi ∧
      ¬Fin15AnchoredAtom2949 chi ∧
      ¬Fin15AnchoredAtom2950 chi ∧
      ¬Fin15AnchoredAtom2955 chi ∧
      ¬Fin15AnchoredAtom3023 chi ∧
      ¬Fin15AnchoredAtom3024 chi ∧
      ¬Fin15AnchoredAtom3029 chi ∧
      ¬Fin15AnchoredAtom3035 chi ∧
      ¬Fin15AnchoredAtom3392 chi ∧
      ¬Fin15AnchoredAtom3393 chi ∧
      ¬Fin15AnchoredAtom3398 chi ∧
      ¬Fin15AnchoredAtom3404 chi ∧
      ¬Fin15AnchoredAtom3525 chi ∧
      ¬Fin15AnchoredAtom3887 chi ∧
      ¬Fin15AnchoredAtom3888 chi ∧
      ¬Fin15AnchoredAtom3893 chi ∧
      ¬Fin15AnchoredAtom3899 chi ∧
      ¬Fin15AnchoredAtom4020 chi ∧
      ¬Fin15AnchoredAtom4686 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 5, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13863
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1845 Fin15AnchoredAtom1846 Fin15AnchoredAtom1848
    Fin15AnchoredAtom1849 Fin15AnchoredAtom1872 Fin15AnchoredAtom1874 Fin15AnchoredAtom1875
    Fin15AnchoredAtom1878 Fin15AnchoredAtom1879 Fin15AnchoredAtom1884 Fin15AnchoredAtom2008
    Fin15AnchoredAtom2010 Fin15AnchoredAtom2011 Fin15AnchoredAtom2014 Fin15AnchoredAtom2015
    Fin15AnchoredAtom2020 Fin15AnchoredAtom2088 Fin15AnchoredAtom2089 Fin15AnchoredAtom2094
    Fin15AnchoredAtom2100 Fin15AnchoredAtom2228 Fin15AnchoredAtom2230 Fin15AnchoredAtom2231
    Fin15AnchoredAtom2234 Fin15AnchoredAtom2235 Fin15AnchoredAtom2240 Fin15AnchoredAtom2308
    Fin15AnchoredAtom2309 Fin15AnchoredAtom2314 Fin15AnchoredAtom2320 Fin15AnchoredAtom2677
    Fin15AnchoredAtom2678 Fin15AnchoredAtom2683 Fin15AnchoredAtom2689 Fin15AnchoredAtom2810
    Fin15AnchoredAtom2943 Fin15AnchoredAtom2945 Fin15AnchoredAtom2946 Fin15AnchoredAtom2949
    Fin15AnchoredAtom2950 Fin15AnchoredAtom2955 Fin15AnchoredAtom3023 Fin15AnchoredAtom3024
    Fin15AnchoredAtom3029 Fin15AnchoredAtom3035 Fin15AnchoredAtom3392 Fin15AnchoredAtom3393
    Fin15AnchoredAtom3398 Fin15AnchoredAtom3404 Fin15AnchoredAtom3525 Fin15AnchoredAtom3887
    Fin15AnchoredAtom3888 Fin15AnchoredAtom3893 Fin15AnchoredAtom3899 Fin15AnchoredAtom4020
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

theorem fin15Anchored_clause30736 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom2008 chi ∧
      ¬Fin15AnchoredAtom2010 chi ∧
      ¬Fin15AnchoredAtom2012 chi ∧
      ¬Fin15AnchoredAtom2014 chi ∧
      ¬Fin15AnchoredAtom2016 chi ∧
      ¬Fin15AnchoredAtom2021 chi ∧
      ¬Fin15AnchoredAtom2088 chi ∧
      ¬Fin15AnchoredAtom2090 chi ∧
      ¬Fin15AnchoredAtom2095 chi ∧
      ¬Fin15AnchoredAtom2101 chi ∧
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
      ¬Fin15AnchoredAtom2677 chi ∧
      ¬Fin15AnchoredAtom2679 chi ∧
      ¬Fin15AnchoredAtom2684 chi ∧
      ¬Fin15AnchoredAtom2690 chi ∧
      ¬Fin15AnchoredAtom2811 chi ∧
      ¬Fin15AnchoredAtom2943 chi ∧
      ¬Fin15AnchoredAtom2945 chi ∧
      ¬Fin15AnchoredAtom2947 chi ∧
      ¬Fin15AnchoredAtom2949 chi ∧
      ¬Fin15AnchoredAtom2951 chi ∧
      ¬Fin15AnchoredAtom2956 chi ∧
      ¬Fin15AnchoredAtom3023 chi ∧
      ¬Fin15AnchoredAtom3025 chi ∧
      ¬Fin15AnchoredAtom3030 chi ∧
      ¬Fin15AnchoredAtom3036 chi ∧
      ¬Fin15AnchoredAtom3392 chi ∧
      ¬Fin15AnchoredAtom3394 chi ∧
      ¬Fin15AnchoredAtom3399 chi ∧
      ¬Fin15AnchoredAtom3405 chi ∧
      ¬Fin15AnchoredAtom3526 chi ∧
      ¬Fin15AnchoredAtom3887 chi ∧
      ¬Fin15AnchoredAtom3889 chi ∧
      ¬Fin15AnchoredAtom3894 chi ∧
      ¬Fin15AnchoredAtom3900 chi ∧
      ¬Fin15AnchoredAtom4021 chi ∧
      ¬Fin15AnchoredAtom4687 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 5, 9, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22055
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1845 Fin15AnchoredAtom1846 Fin15AnchoredAtom1848
    Fin15AnchoredAtom1850 Fin15AnchoredAtom1872 Fin15AnchoredAtom1874 Fin15AnchoredAtom1876
    Fin15AnchoredAtom1878 Fin15AnchoredAtom1880 Fin15AnchoredAtom1885 Fin15AnchoredAtom2008
    Fin15AnchoredAtom2010 Fin15AnchoredAtom2012 Fin15AnchoredAtom2014 Fin15AnchoredAtom2016
    Fin15AnchoredAtom2021 Fin15AnchoredAtom2088 Fin15AnchoredAtom2090 Fin15AnchoredAtom2095
    Fin15AnchoredAtom2101 Fin15AnchoredAtom2228 Fin15AnchoredAtom2230 Fin15AnchoredAtom2232
    Fin15AnchoredAtom2234 Fin15AnchoredAtom2236 Fin15AnchoredAtom2241 Fin15AnchoredAtom2308
    Fin15AnchoredAtom2310 Fin15AnchoredAtom2315 Fin15AnchoredAtom2321 Fin15AnchoredAtom2677
    Fin15AnchoredAtom2679 Fin15AnchoredAtom2684 Fin15AnchoredAtom2690 Fin15AnchoredAtom2811
    Fin15AnchoredAtom2943 Fin15AnchoredAtom2945 Fin15AnchoredAtom2947 Fin15AnchoredAtom2949
    Fin15AnchoredAtom2951 Fin15AnchoredAtom2956 Fin15AnchoredAtom3023 Fin15AnchoredAtom3025
    Fin15AnchoredAtom3030 Fin15AnchoredAtom3036 Fin15AnchoredAtom3392 Fin15AnchoredAtom3394
    Fin15AnchoredAtom3399 Fin15AnchoredAtom3405 Fin15AnchoredAtom3526 Fin15AnchoredAtom3887
    Fin15AnchoredAtom3889 Fin15AnchoredAtom3894 Fin15AnchoredAtom3900 Fin15AnchoredAtom4021
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

theorem fin15Anchored_clause30737 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom1886 chi ∧
      ¬Fin15AnchoredAtom2008 chi ∧
      ¬Fin15AnchoredAtom2011 chi ∧
      ¬Fin15AnchoredAtom2012 chi ∧
      ¬Fin15AnchoredAtom2015 chi ∧
      ¬Fin15AnchoredAtom2016 chi ∧
      ¬Fin15AnchoredAtom2022 chi ∧
      ¬Fin15AnchoredAtom2089 chi ∧
      ¬Fin15AnchoredAtom2090 chi ∧
      ¬Fin15AnchoredAtom2096 chi ∧
      ¬Fin15AnchoredAtom2102 chi ∧
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
      ¬Fin15AnchoredAtom2678 chi ∧
      ¬Fin15AnchoredAtom2679 chi ∧
      ¬Fin15AnchoredAtom2685 chi ∧
      ¬Fin15AnchoredAtom2691 chi ∧
      ¬Fin15AnchoredAtom2812 chi ∧
      ¬Fin15AnchoredAtom2943 chi ∧
      ¬Fin15AnchoredAtom2946 chi ∧
      ¬Fin15AnchoredAtom2947 chi ∧
      ¬Fin15AnchoredAtom2950 chi ∧
      ¬Fin15AnchoredAtom2951 chi ∧
      ¬Fin15AnchoredAtom2957 chi ∧
      ¬Fin15AnchoredAtom3024 chi ∧
      ¬Fin15AnchoredAtom3025 chi ∧
      ¬Fin15AnchoredAtom3031 chi ∧
      ¬Fin15AnchoredAtom3037 chi ∧
      ¬Fin15AnchoredAtom3393 chi ∧
      ¬Fin15AnchoredAtom3394 chi ∧
      ¬Fin15AnchoredAtom3400 chi ∧
      ¬Fin15AnchoredAtom3406 chi ∧
      ¬Fin15AnchoredAtom3527 chi ∧
      ¬Fin15AnchoredAtom3888 chi ∧
      ¬Fin15AnchoredAtom3889 chi ∧
      ¬Fin15AnchoredAtom3895 chi ∧
      ¬Fin15AnchoredAtom3901 chi ∧
      ¬Fin15AnchoredAtom4022 chi ∧
      ¬Fin15AnchoredAtom4688 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 5, 9, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26151
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1845 Fin15AnchoredAtom1846 Fin15AnchoredAtom1849
    Fin15AnchoredAtom1850 Fin15AnchoredAtom1872 Fin15AnchoredAtom1875 Fin15AnchoredAtom1876
    Fin15AnchoredAtom1879 Fin15AnchoredAtom1880 Fin15AnchoredAtom1886 Fin15AnchoredAtom2008
    Fin15AnchoredAtom2011 Fin15AnchoredAtom2012 Fin15AnchoredAtom2015 Fin15AnchoredAtom2016
    Fin15AnchoredAtom2022 Fin15AnchoredAtom2089 Fin15AnchoredAtom2090 Fin15AnchoredAtom2096
    Fin15AnchoredAtom2102 Fin15AnchoredAtom2228 Fin15AnchoredAtom2231 Fin15AnchoredAtom2232
    Fin15AnchoredAtom2235 Fin15AnchoredAtom2236 Fin15AnchoredAtom2242 Fin15AnchoredAtom2309
    Fin15AnchoredAtom2310 Fin15AnchoredAtom2316 Fin15AnchoredAtom2322 Fin15AnchoredAtom2678
    Fin15AnchoredAtom2679 Fin15AnchoredAtom2685 Fin15AnchoredAtom2691 Fin15AnchoredAtom2812
    Fin15AnchoredAtom2943 Fin15AnchoredAtom2946 Fin15AnchoredAtom2947 Fin15AnchoredAtom2950
    Fin15AnchoredAtom2951 Fin15AnchoredAtom2957 Fin15AnchoredAtom3024 Fin15AnchoredAtom3025
    Fin15AnchoredAtom3031 Fin15AnchoredAtom3037 Fin15AnchoredAtom3393 Fin15AnchoredAtom3394
    Fin15AnchoredAtom3400 Fin15AnchoredAtom3406 Fin15AnchoredAtom3527 Fin15AnchoredAtom3888
    Fin15AnchoredAtom3889 Fin15AnchoredAtom3895 Fin15AnchoredAtom3901 Fin15AnchoredAtom4022
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

theorem fin15Anchored_clause30738 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom1886 chi ∧
      ¬Fin15AnchoredAtom2010 chi ∧
      ¬Fin15AnchoredAtom2011 chi ∧
      ¬Fin15AnchoredAtom2012 chi ∧
      ¬Fin15AnchoredAtom2020 chi ∧
      ¬Fin15AnchoredAtom2021 chi ∧
      ¬Fin15AnchoredAtom2022 chi ∧
      ¬Fin15AnchoredAtom2094 chi ∧
      ¬Fin15AnchoredAtom2095 chi ∧
      ¬Fin15AnchoredAtom2096 chi ∧
      ¬Fin15AnchoredAtom2106 chi ∧
      ¬Fin15AnchoredAtom2230 chi ∧
      ¬Fin15AnchoredAtom2231 chi ∧
      ¬Fin15AnchoredAtom2232 chi ∧
      ¬Fin15AnchoredAtom2240 chi ∧
      ¬Fin15AnchoredAtom2241 chi ∧
      ¬Fin15AnchoredAtom2242 chi ∧
      ¬Fin15AnchoredAtom2314 chi ∧
      ¬Fin15AnchoredAtom2315 chi ∧
      ¬Fin15AnchoredAtom2316 chi ∧
      ¬Fin15AnchoredAtom2326 chi ∧
      ¬Fin15AnchoredAtom2683 chi ∧
      ¬Fin15AnchoredAtom2684 chi ∧
      ¬Fin15AnchoredAtom2685 chi ∧
      ¬Fin15AnchoredAtom2695 chi ∧
      ¬Fin15AnchoredAtom2816 chi ∧
      ¬Fin15AnchoredAtom2945 chi ∧
      ¬Fin15AnchoredAtom2946 chi ∧
      ¬Fin15AnchoredAtom2947 chi ∧
      ¬Fin15AnchoredAtom2955 chi ∧
      ¬Fin15AnchoredAtom2956 chi ∧
      ¬Fin15AnchoredAtom2957 chi ∧
      ¬Fin15AnchoredAtom3029 chi ∧
      ¬Fin15AnchoredAtom3030 chi ∧
      ¬Fin15AnchoredAtom3031 chi ∧
      ¬Fin15AnchoredAtom3041 chi ∧
      ¬Fin15AnchoredAtom3398 chi ∧
      ¬Fin15AnchoredAtom3399 chi ∧
      ¬Fin15AnchoredAtom3400 chi ∧
      ¬Fin15AnchoredAtom3410 chi ∧
      ¬Fin15AnchoredAtom3531 chi ∧
      ¬Fin15AnchoredAtom3893 chi ∧
      ¬Fin15AnchoredAtom3894 chi ∧
      ¬Fin15AnchoredAtom3895 chi ∧
      ¬Fin15AnchoredAtom3905 chi ∧
      ¬Fin15AnchoredAtom4026 chi ∧
      ¬Fin15AnchoredAtom4692 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 5, 9, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29223
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1845 Fin15AnchoredAtom1848 Fin15AnchoredAtom1849
    Fin15AnchoredAtom1850 Fin15AnchoredAtom1874 Fin15AnchoredAtom1875 Fin15AnchoredAtom1876
    Fin15AnchoredAtom1884 Fin15AnchoredAtom1885 Fin15AnchoredAtom1886 Fin15AnchoredAtom2010
    Fin15AnchoredAtom2011 Fin15AnchoredAtom2012 Fin15AnchoredAtom2020 Fin15AnchoredAtom2021
    Fin15AnchoredAtom2022 Fin15AnchoredAtom2094 Fin15AnchoredAtom2095 Fin15AnchoredAtom2096
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2230 Fin15AnchoredAtom2231 Fin15AnchoredAtom2232
    Fin15AnchoredAtom2240 Fin15AnchoredAtom2241 Fin15AnchoredAtom2242 Fin15AnchoredAtom2314
    Fin15AnchoredAtom2315 Fin15AnchoredAtom2316 Fin15AnchoredAtom2326 Fin15AnchoredAtom2683
    Fin15AnchoredAtom2684 Fin15AnchoredAtom2685 Fin15AnchoredAtom2695 Fin15AnchoredAtom2816
    Fin15AnchoredAtom2945 Fin15AnchoredAtom2946 Fin15AnchoredAtom2947 Fin15AnchoredAtom2955
    Fin15AnchoredAtom2956 Fin15AnchoredAtom2957 Fin15AnchoredAtom3029 Fin15AnchoredAtom3030
    Fin15AnchoredAtom3031 Fin15AnchoredAtom3041 Fin15AnchoredAtom3398 Fin15AnchoredAtom3399
    Fin15AnchoredAtom3400 Fin15AnchoredAtom3410 Fin15AnchoredAtom3531 Fin15AnchoredAtom3893
    Fin15AnchoredAtom3894 Fin15AnchoredAtom3895 Fin15AnchoredAtom3905 Fin15AnchoredAtom4026
    Fin15AnchoredAtom4692 at hbad
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

theorem fin15Anchored_clause30739 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom1886 chi ∧
      ¬Fin15AnchoredAtom2014 chi ∧
      ¬Fin15AnchoredAtom2015 chi ∧
      ¬Fin15AnchoredAtom2016 chi ∧
      ¬Fin15AnchoredAtom2020 chi ∧
      ¬Fin15AnchoredAtom2021 chi ∧
      ¬Fin15AnchoredAtom2022 chi ∧
      ¬Fin15AnchoredAtom2100 chi ∧
      ¬Fin15AnchoredAtom2101 chi ∧
      ¬Fin15AnchoredAtom2102 chi ∧
      ¬Fin15AnchoredAtom2106 chi ∧
      ¬Fin15AnchoredAtom2234 chi ∧
      ¬Fin15AnchoredAtom2235 chi ∧
      ¬Fin15AnchoredAtom2236 chi ∧
      ¬Fin15AnchoredAtom2240 chi ∧
      ¬Fin15AnchoredAtom2241 chi ∧
      ¬Fin15AnchoredAtom2242 chi ∧
      ¬Fin15AnchoredAtom2320 chi ∧
      ¬Fin15AnchoredAtom2321 chi ∧
      ¬Fin15AnchoredAtom2322 chi ∧
      ¬Fin15AnchoredAtom2326 chi ∧
      ¬Fin15AnchoredAtom2689 chi ∧
      ¬Fin15AnchoredAtom2690 chi ∧
      ¬Fin15AnchoredAtom2691 chi ∧
      ¬Fin15AnchoredAtom2695 chi ∧
      ¬Fin15AnchoredAtom2820 chi ∧
      ¬Fin15AnchoredAtom2949 chi ∧
      ¬Fin15AnchoredAtom2950 chi ∧
      ¬Fin15AnchoredAtom2951 chi ∧
      ¬Fin15AnchoredAtom2955 chi ∧
      ¬Fin15AnchoredAtom2956 chi ∧
      ¬Fin15AnchoredAtom2957 chi ∧
      ¬Fin15AnchoredAtom3035 chi ∧
      ¬Fin15AnchoredAtom3036 chi ∧
      ¬Fin15AnchoredAtom3037 chi ∧
      ¬Fin15AnchoredAtom3041 chi ∧
      ¬Fin15AnchoredAtom3404 chi ∧
      ¬Fin15AnchoredAtom3405 chi ∧
      ¬Fin15AnchoredAtom3406 chi ∧
      ¬Fin15AnchoredAtom3410 chi ∧
      ¬Fin15AnchoredAtom3535 chi ∧
      ¬Fin15AnchoredAtom3899 chi ∧
      ¬Fin15AnchoredAtom3900 chi ∧
      ¬Fin15AnchoredAtom3901 chi ∧
      ¬Fin15AnchoredAtom3905 chi ∧
      ¬Fin15AnchoredAtom4030 chi ∧
      ¬Fin15AnchoredAtom4696 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 5, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29735
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1846 Fin15AnchoredAtom1848 Fin15AnchoredAtom1849
    Fin15AnchoredAtom1850 Fin15AnchoredAtom1878 Fin15AnchoredAtom1879 Fin15AnchoredAtom1880
    Fin15AnchoredAtom1884 Fin15AnchoredAtom1885 Fin15AnchoredAtom1886 Fin15AnchoredAtom2014
    Fin15AnchoredAtom2015 Fin15AnchoredAtom2016 Fin15AnchoredAtom2020 Fin15AnchoredAtom2021
    Fin15AnchoredAtom2022 Fin15AnchoredAtom2100 Fin15AnchoredAtom2101 Fin15AnchoredAtom2102
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2234 Fin15AnchoredAtom2235 Fin15AnchoredAtom2236
    Fin15AnchoredAtom2240 Fin15AnchoredAtom2241 Fin15AnchoredAtom2242 Fin15AnchoredAtom2320
    Fin15AnchoredAtom2321 Fin15AnchoredAtom2322 Fin15AnchoredAtom2326 Fin15AnchoredAtom2689
    Fin15AnchoredAtom2690 Fin15AnchoredAtom2691 Fin15AnchoredAtom2695 Fin15AnchoredAtom2820
    Fin15AnchoredAtom2949 Fin15AnchoredAtom2950 Fin15AnchoredAtom2951 Fin15AnchoredAtom2955
    Fin15AnchoredAtom2956 Fin15AnchoredAtom2957 Fin15AnchoredAtom3035 Fin15AnchoredAtom3036
    Fin15AnchoredAtom3037 Fin15AnchoredAtom3041 Fin15AnchoredAtom3404 Fin15AnchoredAtom3405
    Fin15AnchoredAtom3406 Fin15AnchoredAtom3410 Fin15AnchoredAtom3535 Fin15AnchoredAtom3899
    Fin15AnchoredAtom3900 Fin15AnchoredAtom3901 Fin15AnchoredAtom3905 Fin15AnchoredAtom4030
    Fin15AnchoredAtom4696 at hbad
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

theorem fin15Anchored_clause30740 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1852 chi ∧
      ¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1859 chi ∧
      ¬Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom1866 chi ∧
      ¬Fin15AnchoredAtom1867 chi ∧
      ¬Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom2023 chi ∧
      ¬Fin15AnchoredAtom2024 chi ∧
      ¬Fin15AnchoredAtom2025 chi ∧
      ¬Fin15AnchoredAtom2030 chi ∧
      ¬Fin15AnchoredAtom2031 chi ∧
      ¬Fin15AnchoredAtom2036 chi ∧
      ¬Fin15AnchoredAtom2051 chi ∧
      ¬Fin15AnchoredAtom2052 chi ∧
      ¬Fin15AnchoredAtom2057 chi ∧
      ¬Fin15AnchoredAtom2072 chi ∧
      ¬Fin15AnchoredAtom2243 chi ∧
      ¬Fin15AnchoredAtom2244 chi ∧
      ¬Fin15AnchoredAtom2245 chi ∧
      ¬Fin15AnchoredAtom2250 chi ∧
      ¬Fin15AnchoredAtom2251 chi ∧
      ¬Fin15AnchoredAtom2256 chi ∧
      ¬Fin15AnchoredAtom2271 chi ∧
      ¬Fin15AnchoredAtom2272 chi ∧
      ¬Fin15AnchoredAtom2277 chi ∧
      ¬Fin15AnchoredAtom2292 chi ∧
      ¬Fin15AnchoredAtom2696 chi ∧
      ¬Fin15AnchoredAtom2697 chi ∧
      ¬Fin15AnchoredAtom2702 chi ∧
      ¬Fin15AnchoredAtom2717 chi ∧
      ¬Fin15AnchoredAtom2752 chi ∧
      ¬Fin15AnchoredAtom2958 chi ∧
      ¬Fin15AnchoredAtom2959 chi ∧
      ¬Fin15AnchoredAtom2960 chi ∧
      ¬Fin15AnchoredAtom2965 chi ∧
      ¬Fin15AnchoredAtom2966 chi ∧
      ¬Fin15AnchoredAtom2971 chi ∧
      ¬Fin15AnchoredAtom2986 chi ∧
      ¬Fin15AnchoredAtom2987 chi ∧
      ¬Fin15AnchoredAtom2992 chi ∧
      ¬Fin15AnchoredAtom3007 chi ∧
      ¬Fin15AnchoredAtom3411 chi ∧
      ¬Fin15AnchoredAtom3412 chi ∧
      ¬Fin15AnchoredAtom3417 chi ∧
      ¬Fin15AnchoredAtom3432 chi ∧
      ¬Fin15AnchoredAtom3467 chi ∧
      ¬Fin15AnchoredAtom3906 chi ∧
      ¬Fin15AnchoredAtom3907 chi ∧
      ¬Fin15AnchoredAtom3912 chi ∧
      ¬Fin15AnchoredAtom3927 chi ∧
      ¬Fin15AnchoredAtom3962 chi ∧
      ¬Fin15AnchoredAtom4698 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 6, 7, 8, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask01991
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1851 Fin15AnchoredAtom1852 Fin15AnchoredAtom1853
    Fin15AnchoredAtom1854 Fin15AnchoredAtom1859 Fin15AnchoredAtom1860 Fin15AnchoredAtom1861
    Fin15AnchoredAtom1866 Fin15AnchoredAtom1867 Fin15AnchoredAtom1872 Fin15AnchoredAtom2023
    Fin15AnchoredAtom2024 Fin15AnchoredAtom2025 Fin15AnchoredAtom2030 Fin15AnchoredAtom2031
    Fin15AnchoredAtom2036 Fin15AnchoredAtom2051 Fin15AnchoredAtom2052 Fin15AnchoredAtom2057
    Fin15AnchoredAtom2072 Fin15AnchoredAtom2243 Fin15AnchoredAtom2244 Fin15AnchoredAtom2245
    Fin15AnchoredAtom2250 Fin15AnchoredAtom2251 Fin15AnchoredAtom2256 Fin15AnchoredAtom2271
    Fin15AnchoredAtom2272 Fin15AnchoredAtom2277 Fin15AnchoredAtom2292 Fin15AnchoredAtom2696
    Fin15AnchoredAtom2697 Fin15AnchoredAtom2702 Fin15AnchoredAtom2717 Fin15AnchoredAtom2752
    Fin15AnchoredAtom2958 Fin15AnchoredAtom2959 Fin15AnchoredAtom2960 Fin15AnchoredAtom2965
    Fin15AnchoredAtom2966 Fin15AnchoredAtom2971 Fin15AnchoredAtom2986 Fin15AnchoredAtom2987
    Fin15AnchoredAtom2992 Fin15AnchoredAtom3007 Fin15AnchoredAtom3411 Fin15AnchoredAtom3412
    Fin15AnchoredAtom3417 Fin15AnchoredAtom3432 Fin15AnchoredAtom3467 Fin15AnchoredAtom3906
    Fin15AnchoredAtom3907 Fin15AnchoredAtom3912 Fin15AnchoredAtom3927 Fin15AnchoredAtom3962
    Fin15AnchoredAtom4698 at hbad
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

theorem fin15Anchored_clause30741 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom2024 chi ∧
      ¬Fin15AnchoredAtom2025 chi ∧
      ¬Fin15AnchoredAtom2027 chi ∧
      ¬Fin15AnchoredAtom2036 chi ∧
      ¬Fin15AnchoredAtom2038 chi ∧
      ¬Fin15AnchoredAtom2042 chi ∧
      ¬Fin15AnchoredAtom2057 chi ∧
      ¬Fin15AnchoredAtom2059 chi ∧
      ¬Fin15AnchoredAtom2063 chi ∧
      ¬Fin15AnchoredAtom2088 chi ∧
      ¬Fin15AnchoredAtom2244 chi ∧
      ¬Fin15AnchoredAtom2245 chi ∧
      ¬Fin15AnchoredAtom2247 chi ∧
      ¬Fin15AnchoredAtom2256 chi ∧
      ¬Fin15AnchoredAtom2258 chi ∧
      ¬Fin15AnchoredAtom2262 chi ∧
      ¬Fin15AnchoredAtom2277 chi ∧
      ¬Fin15AnchoredAtom2279 chi ∧
      ¬Fin15AnchoredAtom2283 chi ∧
      ¬Fin15AnchoredAtom2308 chi ∧
      ¬Fin15AnchoredAtom2702 chi ∧
      ¬Fin15AnchoredAtom2704 chi ∧
      ¬Fin15AnchoredAtom2708 chi ∧
      ¬Fin15AnchoredAtom2733 chi ∧
      ¬Fin15AnchoredAtom2768 chi ∧
      ¬Fin15AnchoredAtom2959 chi ∧
      ¬Fin15AnchoredAtom2960 chi ∧
      ¬Fin15AnchoredAtom2962 chi ∧
      ¬Fin15AnchoredAtom2971 chi ∧
      ¬Fin15AnchoredAtom2973 chi ∧
      ¬Fin15AnchoredAtom2977 chi ∧
      ¬Fin15AnchoredAtom2992 chi ∧
      ¬Fin15AnchoredAtom2994 chi ∧
      ¬Fin15AnchoredAtom2998 chi ∧
      ¬Fin15AnchoredAtom3023 chi ∧
      ¬Fin15AnchoredAtom3417 chi ∧
      ¬Fin15AnchoredAtom3419 chi ∧
      ¬Fin15AnchoredAtom3423 chi ∧
      ¬Fin15AnchoredAtom3448 chi ∧
      ¬Fin15AnchoredAtom3483 chi ∧
      ¬Fin15AnchoredAtom3912 chi ∧
      ¬Fin15AnchoredAtom3914 chi ∧
      ¬Fin15AnchoredAtom3918 chi ∧
      ¬Fin15AnchoredAtom3943 chi ∧
      ¬Fin15AnchoredAtom3978 chi ∧
      ¬Fin15AnchoredAtom4714 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 6, 7, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05831
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1851 Fin15AnchoredAtom1853 Fin15AnchoredAtom1854
    Fin15AnchoredAtom1856 Fin15AnchoredAtom1860 Fin15AnchoredAtom1861 Fin15AnchoredAtom1863
    Fin15AnchoredAtom1872 Fin15AnchoredAtom1874 Fin15AnchoredAtom1878 Fin15AnchoredAtom2024
    Fin15AnchoredAtom2025 Fin15AnchoredAtom2027 Fin15AnchoredAtom2036 Fin15AnchoredAtom2038
    Fin15AnchoredAtom2042 Fin15AnchoredAtom2057 Fin15AnchoredAtom2059 Fin15AnchoredAtom2063
    Fin15AnchoredAtom2088 Fin15AnchoredAtom2244 Fin15AnchoredAtom2245 Fin15AnchoredAtom2247
    Fin15AnchoredAtom2256 Fin15AnchoredAtom2258 Fin15AnchoredAtom2262 Fin15AnchoredAtom2277
    Fin15AnchoredAtom2279 Fin15AnchoredAtom2283 Fin15AnchoredAtom2308 Fin15AnchoredAtom2702
    Fin15AnchoredAtom2704 Fin15AnchoredAtom2708 Fin15AnchoredAtom2733 Fin15AnchoredAtom2768
    Fin15AnchoredAtom2959 Fin15AnchoredAtom2960 Fin15AnchoredAtom2962 Fin15AnchoredAtom2971
    Fin15AnchoredAtom2973 Fin15AnchoredAtom2977 Fin15AnchoredAtom2992 Fin15AnchoredAtom2994
    Fin15AnchoredAtom2998 Fin15AnchoredAtom3023 Fin15AnchoredAtom3417 Fin15AnchoredAtom3419
    Fin15AnchoredAtom3423 Fin15AnchoredAtom3448 Fin15AnchoredAtom3483 Fin15AnchoredAtom3912
    Fin15AnchoredAtom3914 Fin15AnchoredAtom3918 Fin15AnchoredAtom3943 Fin15AnchoredAtom3978
    Fin15AnchoredAtom4714 at hbad
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

theorem fin15Anchored_clause30742 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom2024 chi ∧
      ¬Fin15AnchoredAtom2025 chi ∧
      ¬Fin15AnchoredAtom2028 chi ∧
      ¬Fin15AnchoredAtom2036 chi ∧
      ¬Fin15AnchoredAtom2039 chi ∧
      ¬Fin15AnchoredAtom2043 chi ∧
      ¬Fin15AnchoredAtom2057 chi ∧
      ¬Fin15AnchoredAtom2060 chi ∧
      ¬Fin15AnchoredAtom2064 chi ∧
      ¬Fin15AnchoredAtom2089 chi ∧
      ¬Fin15AnchoredAtom2244 chi ∧
      ¬Fin15AnchoredAtom2245 chi ∧
      ¬Fin15AnchoredAtom2248 chi ∧
      ¬Fin15AnchoredAtom2256 chi ∧
      ¬Fin15AnchoredAtom2259 chi ∧
      ¬Fin15AnchoredAtom2263 chi ∧
      ¬Fin15AnchoredAtom2277 chi ∧
      ¬Fin15AnchoredAtom2280 chi ∧
      ¬Fin15AnchoredAtom2284 chi ∧
      ¬Fin15AnchoredAtom2309 chi ∧
      ¬Fin15AnchoredAtom2702 chi ∧
      ¬Fin15AnchoredAtom2705 chi ∧
      ¬Fin15AnchoredAtom2709 chi ∧
      ¬Fin15AnchoredAtom2734 chi ∧
      ¬Fin15AnchoredAtom2769 chi ∧
      ¬Fin15AnchoredAtom2959 chi ∧
      ¬Fin15AnchoredAtom2960 chi ∧
      ¬Fin15AnchoredAtom2963 chi ∧
      ¬Fin15AnchoredAtom2971 chi ∧
      ¬Fin15AnchoredAtom2974 chi ∧
      ¬Fin15AnchoredAtom2978 chi ∧
      ¬Fin15AnchoredAtom2992 chi ∧
      ¬Fin15AnchoredAtom2995 chi ∧
      ¬Fin15AnchoredAtom2999 chi ∧
      ¬Fin15AnchoredAtom3024 chi ∧
      ¬Fin15AnchoredAtom3417 chi ∧
      ¬Fin15AnchoredAtom3420 chi ∧
      ¬Fin15AnchoredAtom3424 chi ∧
      ¬Fin15AnchoredAtom3449 chi ∧
      ¬Fin15AnchoredAtom3484 chi ∧
      ¬Fin15AnchoredAtom3912 chi ∧
      ¬Fin15AnchoredAtom3915 chi ∧
      ¬Fin15AnchoredAtom3919 chi ∧
      ¬Fin15AnchoredAtom3944 chi ∧
      ¬Fin15AnchoredAtom3979 chi ∧
      ¬Fin15AnchoredAtom4715 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 6, 7, 9, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09927
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1851 Fin15AnchoredAtom1853 Fin15AnchoredAtom1854
    Fin15AnchoredAtom1857 Fin15AnchoredAtom1860 Fin15AnchoredAtom1861 Fin15AnchoredAtom1864
    Fin15AnchoredAtom1872 Fin15AnchoredAtom1875 Fin15AnchoredAtom1879 Fin15AnchoredAtom2024
    Fin15AnchoredAtom2025 Fin15AnchoredAtom2028 Fin15AnchoredAtom2036 Fin15AnchoredAtom2039
    Fin15AnchoredAtom2043 Fin15AnchoredAtom2057 Fin15AnchoredAtom2060 Fin15AnchoredAtom2064
    Fin15AnchoredAtom2089 Fin15AnchoredAtom2244 Fin15AnchoredAtom2245 Fin15AnchoredAtom2248
    Fin15AnchoredAtom2256 Fin15AnchoredAtom2259 Fin15AnchoredAtom2263 Fin15AnchoredAtom2277
    Fin15AnchoredAtom2280 Fin15AnchoredAtom2284 Fin15AnchoredAtom2309 Fin15AnchoredAtom2702
    Fin15AnchoredAtom2705 Fin15AnchoredAtom2709 Fin15AnchoredAtom2734 Fin15AnchoredAtom2769
    Fin15AnchoredAtom2959 Fin15AnchoredAtom2960 Fin15AnchoredAtom2963 Fin15AnchoredAtom2971
    Fin15AnchoredAtom2974 Fin15AnchoredAtom2978 Fin15AnchoredAtom2992 Fin15AnchoredAtom2995
    Fin15AnchoredAtom2999 Fin15AnchoredAtom3024 Fin15AnchoredAtom3417 Fin15AnchoredAtom3420
    Fin15AnchoredAtom3424 Fin15AnchoredAtom3449 Fin15AnchoredAtom3484 Fin15AnchoredAtom3912
    Fin15AnchoredAtom3915 Fin15AnchoredAtom3919 Fin15AnchoredAtom3944 Fin15AnchoredAtom3979
    Fin15AnchoredAtom4715 at hbad
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

theorem fin15Anchored_clause30743 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom2024 chi ∧
      ¬Fin15AnchoredAtom2025 chi ∧
      ¬Fin15AnchoredAtom2029 chi ∧
      ¬Fin15AnchoredAtom2036 chi ∧
      ¬Fin15AnchoredAtom2040 chi ∧
      ¬Fin15AnchoredAtom2044 chi ∧
      ¬Fin15AnchoredAtom2057 chi ∧
      ¬Fin15AnchoredAtom2061 chi ∧
      ¬Fin15AnchoredAtom2065 chi ∧
      ¬Fin15AnchoredAtom2090 chi ∧
      ¬Fin15AnchoredAtom2244 chi ∧
      ¬Fin15AnchoredAtom2245 chi ∧
      ¬Fin15AnchoredAtom2249 chi ∧
      ¬Fin15AnchoredAtom2256 chi ∧
      ¬Fin15AnchoredAtom2260 chi ∧
      ¬Fin15AnchoredAtom2264 chi ∧
      ¬Fin15AnchoredAtom2277 chi ∧
      ¬Fin15AnchoredAtom2281 chi ∧
      ¬Fin15AnchoredAtom2285 chi ∧
      ¬Fin15AnchoredAtom2310 chi ∧
      ¬Fin15AnchoredAtom2702 chi ∧
      ¬Fin15AnchoredAtom2706 chi ∧
      ¬Fin15AnchoredAtom2710 chi ∧
      ¬Fin15AnchoredAtom2735 chi ∧
      ¬Fin15AnchoredAtom2770 chi ∧
      ¬Fin15AnchoredAtom2959 chi ∧
      ¬Fin15AnchoredAtom2960 chi ∧
      ¬Fin15AnchoredAtom2964 chi ∧
      ¬Fin15AnchoredAtom2971 chi ∧
      ¬Fin15AnchoredAtom2975 chi ∧
      ¬Fin15AnchoredAtom2979 chi ∧
      ¬Fin15AnchoredAtom2992 chi ∧
      ¬Fin15AnchoredAtom2996 chi ∧
      ¬Fin15AnchoredAtom3000 chi ∧
      ¬Fin15AnchoredAtom3025 chi ∧
      ¬Fin15AnchoredAtom3417 chi ∧
      ¬Fin15AnchoredAtom3421 chi ∧
      ¬Fin15AnchoredAtom3425 chi ∧
      ¬Fin15AnchoredAtom3450 chi ∧
      ¬Fin15AnchoredAtom3485 chi ∧
      ¬Fin15AnchoredAtom3912 chi ∧
      ¬Fin15AnchoredAtom3916 chi ∧
      ¬Fin15AnchoredAtom3920 chi ∧
      ¬Fin15AnchoredAtom3945 chi ∧
      ¬Fin15AnchoredAtom3980 chi ∧
      ¬Fin15AnchoredAtom4716 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 6, 7, 9, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask18119
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1851 Fin15AnchoredAtom1853 Fin15AnchoredAtom1854
    Fin15AnchoredAtom1858 Fin15AnchoredAtom1860 Fin15AnchoredAtom1861 Fin15AnchoredAtom1865
    Fin15AnchoredAtom1872 Fin15AnchoredAtom1876 Fin15AnchoredAtom1880 Fin15AnchoredAtom2024
    Fin15AnchoredAtom2025 Fin15AnchoredAtom2029 Fin15AnchoredAtom2036 Fin15AnchoredAtom2040
    Fin15AnchoredAtom2044 Fin15AnchoredAtom2057 Fin15AnchoredAtom2061 Fin15AnchoredAtom2065
    Fin15AnchoredAtom2090 Fin15AnchoredAtom2244 Fin15AnchoredAtom2245 Fin15AnchoredAtom2249
    Fin15AnchoredAtom2256 Fin15AnchoredAtom2260 Fin15AnchoredAtom2264 Fin15AnchoredAtom2277
    Fin15AnchoredAtom2281 Fin15AnchoredAtom2285 Fin15AnchoredAtom2310 Fin15AnchoredAtom2702
    Fin15AnchoredAtom2706 Fin15AnchoredAtom2710 Fin15AnchoredAtom2735 Fin15AnchoredAtom2770
    Fin15AnchoredAtom2959 Fin15AnchoredAtom2960 Fin15AnchoredAtom2964 Fin15AnchoredAtom2971
    Fin15AnchoredAtom2975 Fin15AnchoredAtom2979 Fin15AnchoredAtom2992 Fin15AnchoredAtom2996
    Fin15AnchoredAtom3000 Fin15AnchoredAtom3025 Fin15AnchoredAtom3417 Fin15AnchoredAtom3421
    Fin15AnchoredAtom3425 Fin15AnchoredAtom3450 Fin15AnchoredAtom3485 Fin15AnchoredAtom3912
    Fin15AnchoredAtom3916 Fin15AnchoredAtom3920 Fin15AnchoredAtom3945 Fin15AnchoredAtom3980
    Fin15AnchoredAtom4716 at hbad
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

theorem fin15Anchored_clause30744 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom2024 chi ∧
      ¬Fin15AnchoredAtom2027 chi ∧
      ¬Fin15AnchoredAtom2028 chi ∧
      ¬Fin15AnchoredAtom2038 chi ∧
      ¬Fin15AnchoredAtom2039 chi ∧
      ¬Fin15AnchoredAtom2048 chi ∧
      ¬Fin15AnchoredAtom2059 chi ∧
      ¬Fin15AnchoredAtom2060 chi ∧
      ¬Fin15AnchoredAtom2069 chi ∧
      ¬Fin15AnchoredAtom2094 chi ∧
      ¬Fin15AnchoredAtom2244 chi ∧
      ¬Fin15AnchoredAtom2247 chi ∧
      ¬Fin15AnchoredAtom2248 chi ∧
      ¬Fin15AnchoredAtom2258 chi ∧
      ¬Fin15AnchoredAtom2259 chi ∧
      ¬Fin15AnchoredAtom2268 chi ∧
      ¬Fin15AnchoredAtom2279 chi ∧
      ¬Fin15AnchoredAtom2280 chi ∧
      ¬Fin15AnchoredAtom2289 chi ∧
      ¬Fin15AnchoredAtom2314 chi ∧
      ¬Fin15AnchoredAtom2704 chi ∧
      ¬Fin15AnchoredAtom2705 chi ∧
      ¬Fin15AnchoredAtom2714 chi ∧
      ¬Fin15AnchoredAtom2739 chi ∧
      ¬Fin15AnchoredAtom2774 chi ∧
      ¬Fin15AnchoredAtom2959 chi ∧
      ¬Fin15AnchoredAtom2962 chi ∧
      ¬Fin15AnchoredAtom2963 chi ∧
      ¬Fin15AnchoredAtom2973 chi ∧
      ¬Fin15AnchoredAtom2974 chi ∧
      ¬Fin15AnchoredAtom2983 chi ∧
      ¬Fin15AnchoredAtom2994 chi ∧
      ¬Fin15AnchoredAtom2995 chi ∧
      ¬Fin15AnchoredAtom3004 chi ∧
      ¬Fin15AnchoredAtom3029 chi ∧
      ¬Fin15AnchoredAtom3419 chi ∧
      ¬Fin15AnchoredAtom3420 chi ∧
      ¬Fin15AnchoredAtom3429 chi ∧
      ¬Fin15AnchoredAtom3454 chi ∧
      ¬Fin15AnchoredAtom3489 chi ∧
      ¬Fin15AnchoredAtom3914 chi ∧
      ¬Fin15AnchoredAtom3915 chi ∧
      ¬Fin15AnchoredAtom3924 chi ∧
      ¬Fin15AnchoredAtom3949 chi ∧
      ¬Fin15AnchoredAtom3984 chi ∧
      ¬Fin15AnchoredAtom4720 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 6, 7, 9, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask12999
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1851 Fin15AnchoredAtom1853 Fin15AnchoredAtom1856
    Fin15AnchoredAtom1857 Fin15AnchoredAtom1860 Fin15AnchoredAtom1863 Fin15AnchoredAtom1864
    Fin15AnchoredAtom1874 Fin15AnchoredAtom1875 Fin15AnchoredAtom1884 Fin15AnchoredAtom2024
    Fin15AnchoredAtom2027 Fin15AnchoredAtom2028 Fin15AnchoredAtom2038 Fin15AnchoredAtom2039
    Fin15AnchoredAtom2048 Fin15AnchoredAtom2059 Fin15AnchoredAtom2060 Fin15AnchoredAtom2069
    Fin15AnchoredAtom2094 Fin15AnchoredAtom2244 Fin15AnchoredAtom2247 Fin15AnchoredAtom2248
    Fin15AnchoredAtom2258 Fin15AnchoredAtom2259 Fin15AnchoredAtom2268 Fin15AnchoredAtom2279
    Fin15AnchoredAtom2280 Fin15AnchoredAtom2289 Fin15AnchoredAtom2314 Fin15AnchoredAtom2704
    Fin15AnchoredAtom2705 Fin15AnchoredAtom2714 Fin15AnchoredAtom2739 Fin15AnchoredAtom2774
    Fin15AnchoredAtom2959 Fin15AnchoredAtom2962 Fin15AnchoredAtom2963 Fin15AnchoredAtom2973
    Fin15AnchoredAtom2974 Fin15AnchoredAtom2983 Fin15AnchoredAtom2994 Fin15AnchoredAtom2995
    Fin15AnchoredAtom3004 Fin15AnchoredAtom3029 Fin15AnchoredAtom3419 Fin15AnchoredAtom3420
    Fin15AnchoredAtom3429 Fin15AnchoredAtom3454 Fin15AnchoredAtom3489 Fin15AnchoredAtom3914
    Fin15AnchoredAtom3915 Fin15AnchoredAtom3924 Fin15AnchoredAtom3949 Fin15AnchoredAtom3984
    Fin15AnchoredAtom4720 at hbad
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

theorem fin15Anchored_clause30745 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom2024 chi ∧
      ¬Fin15AnchoredAtom2027 chi ∧
      ¬Fin15AnchoredAtom2029 chi ∧
      ¬Fin15AnchoredAtom2038 chi ∧
      ¬Fin15AnchoredAtom2040 chi ∧
      ¬Fin15AnchoredAtom2049 chi ∧
      ¬Fin15AnchoredAtom2059 chi ∧
      ¬Fin15AnchoredAtom2061 chi ∧
      ¬Fin15AnchoredAtom2070 chi ∧
      ¬Fin15AnchoredAtom2095 chi ∧
      ¬Fin15AnchoredAtom2244 chi ∧
      ¬Fin15AnchoredAtom2247 chi ∧
      ¬Fin15AnchoredAtom2249 chi ∧
      ¬Fin15AnchoredAtom2258 chi ∧
      ¬Fin15AnchoredAtom2260 chi ∧
      ¬Fin15AnchoredAtom2269 chi ∧
      ¬Fin15AnchoredAtom2279 chi ∧
      ¬Fin15AnchoredAtom2281 chi ∧
      ¬Fin15AnchoredAtom2290 chi ∧
      ¬Fin15AnchoredAtom2315 chi ∧
      ¬Fin15AnchoredAtom2704 chi ∧
      ¬Fin15AnchoredAtom2706 chi ∧
      ¬Fin15AnchoredAtom2715 chi ∧
      ¬Fin15AnchoredAtom2740 chi ∧
      ¬Fin15AnchoredAtom2775 chi ∧
      ¬Fin15AnchoredAtom2959 chi ∧
      ¬Fin15AnchoredAtom2962 chi ∧
      ¬Fin15AnchoredAtom2964 chi ∧
      ¬Fin15AnchoredAtom2973 chi ∧
      ¬Fin15AnchoredAtom2975 chi ∧
      ¬Fin15AnchoredAtom2984 chi ∧
      ¬Fin15AnchoredAtom2994 chi ∧
      ¬Fin15AnchoredAtom2996 chi ∧
      ¬Fin15AnchoredAtom3005 chi ∧
      ¬Fin15AnchoredAtom3030 chi ∧
      ¬Fin15AnchoredAtom3419 chi ∧
      ¬Fin15AnchoredAtom3421 chi ∧
      ¬Fin15AnchoredAtom3430 chi ∧
      ¬Fin15AnchoredAtom3455 chi ∧
      ¬Fin15AnchoredAtom3490 chi ∧
      ¬Fin15AnchoredAtom3914 chi ∧
      ¬Fin15AnchoredAtom3916 chi ∧
      ¬Fin15AnchoredAtom3925 chi ∧
      ¬Fin15AnchoredAtom3950 chi ∧
      ¬Fin15AnchoredAtom3985 chi ∧
      ¬Fin15AnchoredAtom4721 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 6, 7, 9, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21191
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1851 Fin15AnchoredAtom1853 Fin15AnchoredAtom1856
    Fin15AnchoredAtom1858 Fin15AnchoredAtom1860 Fin15AnchoredAtom1863 Fin15AnchoredAtom1865
    Fin15AnchoredAtom1874 Fin15AnchoredAtom1876 Fin15AnchoredAtom1885 Fin15AnchoredAtom2024
    Fin15AnchoredAtom2027 Fin15AnchoredAtom2029 Fin15AnchoredAtom2038 Fin15AnchoredAtom2040
    Fin15AnchoredAtom2049 Fin15AnchoredAtom2059 Fin15AnchoredAtom2061 Fin15AnchoredAtom2070
    Fin15AnchoredAtom2095 Fin15AnchoredAtom2244 Fin15AnchoredAtom2247 Fin15AnchoredAtom2249
    Fin15AnchoredAtom2258 Fin15AnchoredAtom2260 Fin15AnchoredAtom2269 Fin15AnchoredAtom2279
    Fin15AnchoredAtom2281 Fin15AnchoredAtom2290 Fin15AnchoredAtom2315 Fin15AnchoredAtom2704
    Fin15AnchoredAtom2706 Fin15AnchoredAtom2715 Fin15AnchoredAtom2740 Fin15AnchoredAtom2775
    Fin15AnchoredAtom2959 Fin15AnchoredAtom2962 Fin15AnchoredAtom2964 Fin15AnchoredAtom2973
    Fin15AnchoredAtom2975 Fin15AnchoredAtom2984 Fin15AnchoredAtom2994 Fin15AnchoredAtom2996
    Fin15AnchoredAtom3005 Fin15AnchoredAtom3030 Fin15AnchoredAtom3419 Fin15AnchoredAtom3421
    Fin15AnchoredAtom3430 Fin15AnchoredAtom3455 Fin15AnchoredAtom3490 Fin15AnchoredAtom3914
    Fin15AnchoredAtom3916 Fin15AnchoredAtom3925 Fin15AnchoredAtom3950 Fin15AnchoredAtom3985
    Fin15AnchoredAtom4721 at hbad
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

theorem fin15Anchored_clause30746 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom1886 chi ∧
      ¬Fin15AnchoredAtom2024 chi ∧
      ¬Fin15AnchoredAtom2028 chi ∧
      ¬Fin15AnchoredAtom2029 chi ∧
      ¬Fin15AnchoredAtom2039 chi ∧
      ¬Fin15AnchoredAtom2040 chi ∧
      ¬Fin15AnchoredAtom2050 chi ∧
      ¬Fin15AnchoredAtom2060 chi ∧
      ¬Fin15AnchoredAtom2061 chi ∧
      ¬Fin15AnchoredAtom2071 chi ∧
      ¬Fin15AnchoredAtom2096 chi ∧
      ¬Fin15AnchoredAtom2244 chi ∧
      ¬Fin15AnchoredAtom2248 chi ∧
      ¬Fin15AnchoredAtom2249 chi ∧
      ¬Fin15AnchoredAtom2259 chi ∧
      ¬Fin15AnchoredAtom2260 chi ∧
      ¬Fin15AnchoredAtom2270 chi ∧
      ¬Fin15AnchoredAtom2280 chi ∧
      ¬Fin15AnchoredAtom2281 chi ∧
      ¬Fin15AnchoredAtom2291 chi ∧
      ¬Fin15AnchoredAtom2316 chi ∧
      ¬Fin15AnchoredAtom2705 chi ∧
      ¬Fin15AnchoredAtom2706 chi ∧
      ¬Fin15AnchoredAtom2716 chi ∧
      ¬Fin15AnchoredAtom2741 chi ∧
      ¬Fin15AnchoredAtom2776 chi ∧
      ¬Fin15AnchoredAtom2959 chi ∧
      ¬Fin15AnchoredAtom2963 chi ∧
      ¬Fin15AnchoredAtom2964 chi ∧
      ¬Fin15AnchoredAtom2974 chi ∧
      ¬Fin15AnchoredAtom2975 chi ∧
      ¬Fin15AnchoredAtom2985 chi ∧
      ¬Fin15AnchoredAtom2995 chi ∧
      ¬Fin15AnchoredAtom2996 chi ∧
      ¬Fin15AnchoredAtom3006 chi ∧
      ¬Fin15AnchoredAtom3031 chi ∧
      ¬Fin15AnchoredAtom3420 chi ∧
      ¬Fin15AnchoredAtom3421 chi ∧
      ¬Fin15AnchoredAtom3431 chi ∧
      ¬Fin15AnchoredAtom3456 chi ∧
      ¬Fin15AnchoredAtom3491 chi ∧
      ¬Fin15AnchoredAtom3915 chi ∧
      ¬Fin15AnchoredAtom3916 chi ∧
      ¬Fin15AnchoredAtom3926 chi ∧
      ¬Fin15AnchoredAtom3951 chi ∧
      ¬Fin15AnchoredAtom3986 chi ∧
      ¬Fin15AnchoredAtom4722 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 6, 7, 9, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25287
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1851 Fin15AnchoredAtom1853 Fin15AnchoredAtom1857
    Fin15AnchoredAtom1858 Fin15AnchoredAtom1860 Fin15AnchoredAtom1864 Fin15AnchoredAtom1865
    Fin15AnchoredAtom1875 Fin15AnchoredAtom1876 Fin15AnchoredAtom1886 Fin15AnchoredAtom2024
    Fin15AnchoredAtom2028 Fin15AnchoredAtom2029 Fin15AnchoredAtom2039 Fin15AnchoredAtom2040
    Fin15AnchoredAtom2050 Fin15AnchoredAtom2060 Fin15AnchoredAtom2061 Fin15AnchoredAtom2071
    Fin15AnchoredAtom2096 Fin15AnchoredAtom2244 Fin15AnchoredAtom2248 Fin15AnchoredAtom2249
    Fin15AnchoredAtom2259 Fin15AnchoredAtom2260 Fin15AnchoredAtom2270 Fin15AnchoredAtom2280
    Fin15AnchoredAtom2281 Fin15AnchoredAtom2291 Fin15AnchoredAtom2316 Fin15AnchoredAtom2705
    Fin15AnchoredAtom2706 Fin15AnchoredAtom2716 Fin15AnchoredAtom2741 Fin15AnchoredAtom2776
    Fin15AnchoredAtom2959 Fin15AnchoredAtom2963 Fin15AnchoredAtom2964 Fin15AnchoredAtom2974
    Fin15AnchoredAtom2975 Fin15AnchoredAtom2985 Fin15AnchoredAtom2995 Fin15AnchoredAtom2996
    Fin15AnchoredAtom3006 Fin15AnchoredAtom3031 Fin15AnchoredAtom3420 Fin15AnchoredAtom3421
    Fin15AnchoredAtom3431 Fin15AnchoredAtom3456 Fin15AnchoredAtom3491 Fin15AnchoredAtom3915
    Fin15AnchoredAtom3916 Fin15AnchoredAtom3926 Fin15AnchoredAtom3951 Fin15AnchoredAtom3986
    Fin15AnchoredAtom4722 at hbad
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

theorem fin15Anchored_clause30747 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom2025 chi ∧
      ¬Fin15AnchoredAtom2027 chi ∧
      ¬Fin15AnchoredAtom2028 chi ∧
      ¬Fin15AnchoredAtom2042 chi ∧
      ¬Fin15AnchoredAtom2043 chi ∧
      ¬Fin15AnchoredAtom2048 chi ∧
      ¬Fin15AnchoredAtom2063 chi ∧
      ¬Fin15AnchoredAtom2064 chi ∧
      ¬Fin15AnchoredAtom2069 chi ∧
      ¬Fin15AnchoredAtom2100 chi ∧
      ¬Fin15AnchoredAtom2245 chi ∧
      ¬Fin15AnchoredAtom2247 chi ∧
      ¬Fin15AnchoredAtom2248 chi ∧
      ¬Fin15AnchoredAtom2262 chi ∧
      ¬Fin15AnchoredAtom2263 chi ∧
      ¬Fin15AnchoredAtom2268 chi ∧
      ¬Fin15AnchoredAtom2283 chi ∧
      ¬Fin15AnchoredAtom2284 chi ∧
      ¬Fin15AnchoredAtom2289 chi ∧
      ¬Fin15AnchoredAtom2320 chi ∧
      ¬Fin15AnchoredAtom2708 chi ∧
      ¬Fin15AnchoredAtom2709 chi ∧
      ¬Fin15AnchoredAtom2714 chi ∧
      ¬Fin15AnchoredAtom2745 chi ∧
      ¬Fin15AnchoredAtom2780 chi ∧
      ¬Fin15AnchoredAtom2960 chi ∧
      ¬Fin15AnchoredAtom2962 chi ∧
      ¬Fin15AnchoredAtom2963 chi ∧
      ¬Fin15AnchoredAtom2977 chi ∧
      ¬Fin15AnchoredAtom2978 chi ∧
      ¬Fin15AnchoredAtom2983 chi ∧
      ¬Fin15AnchoredAtom2998 chi ∧
      ¬Fin15AnchoredAtom2999 chi ∧
      ¬Fin15AnchoredAtom3004 chi ∧
      ¬Fin15AnchoredAtom3035 chi ∧
      ¬Fin15AnchoredAtom3423 chi ∧
      ¬Fin15AnchoredAtom3424 chi ∧
      ¬Fin15AnchoredAtom3429 chi ∧
      ¬Fin15AnchoredAtom3460 chi ∧
      ¬Fin15AnchoredAtom3495 chi ∧
      ¬Fin15AnchoredAtom3918 chi ∧
      ¬Fin15AnchoredAtom3919 chi ∧
      ¬Fin15AnchoredAtom3924 chi ∧
      ¬Fin15AnchoredAtom3955 chi ∧
      ¬Fin15AnchoredAtom3990 chi ∧
      ¬Fin15AnchoredAtom4726 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 6, 7, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13511
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1851 Fin15AnchoredAtom1854 Fin15AnchoredAtom1856
    Fin15AnchoredAtom1857 Fin15AnchoredAtom1861 Fin15AnchoredAtom1863 Fin15AnchoredAtom1864
    Fin15AnchoredAtom1878 Fin15AnchoredAtom1879 Fin15AnchoredAtom1884 Fin15AnchoredAtom2025
    Fin15AnchoredAtom2027 Fin15AnchoredAtom2028 Fin15AnchoredAtom2042 Fin15AnchoredAtom2043
    Fin15AnchoredAtom2048 Fin15AnchoredAtom2063 Fin15AnchoredAtom2064 Fin15AnchoredAtom2069
    Fin15AnchoredAtom2100 Fin15AnchoredAtom2245 Fin15AnchoredAtom2247 Fin15AnchoredAtom2248
    Fin15AnchoredAtom2262 Fin15AnchoredAtom2263 Fin15AnchoredAtom2268 Fin15AnchoredAtom2283
    Fin15AnchoredAtom2284 Fin15AnchoredAtom2289 Fin15AnchoredAtom2320 Fin15AnchoredAtom2708
    Fin15AnchoredAtom2709 Fin15AnchoredAtom2714 Fin15AnchoredAtom2745 Fin15AnchoredAtom2780
    Fin15AnchoredAtom2960 Fin15AnchoredAtom2962 Fin15AnchoredAtom2963 Fin15AnchoredAtom2977
    Fin15AnchoredAtom2978 Fin15AnchoredAtom2983 Fin15AnchoredAtom2998 Fin15AnchoredAtom2999
    Fin15AnchoredAtom3004 Fin15AnchoredAtom3035 Fin15AnchoredAtom3423 Fin15AnchoredAtom3424
    Fin15AnchoredAtom3429 Fin15AnchoredAtom3460 Fin15AnchoredAtom3495 Fin15AnchoredAtom3918
    Fin15AnchoredAtom3919 Fin15AnchoredAtom3924 Fin15AnchoredAtom3955 Fin15AnchoredAtom3990
    Fin15AnchoredAtom4726 at hbad
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

theorem fin15Anchored_clause30748 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom2025 chi ∧
      ¬Fin15AnchoredAtom2027 chi ∧
      ¬Fin15AnchoredAtom2029 chi ∧
      ¬Fin15AnchoredAtom2042 chi ∧
      ¬Fin15AnchoredAtom2044 chi ∧
      ¬Fin15AnchoredAtom2049 chi ∧
      ¬Fin15AnchoredAtom2063 chi ∧
      ¬Fin15AnchoredAtom2065 chi ∧
      ¬Fin15AnchoredAtom2070 chi ∧
      ¬Fin15AnchoredAtom2101 chi ∧
      ¬Fin15AnchoredAtom2245 chi ∧
      ¬Fin15AnchoredAtom2247 chi ∧
      ¬Fin15AnchoredAtom2249 chi ∧
      ¬Fin15AnchoredAtom2262 chi ∧
      ¬Fin15AnchoredAtom2264 chi ∧
      ¬Fin15AnchoredAtom2269 chi ∧
      ¬Fin15AnchoredAtom2283 chi ∧
      ¬Fin15AnchoredAtom2285 chi ∧
      ¬Fin15AnchoredAtom2290 chi ∧
      ¬Fin15AnchoredAtom2321 chi ∧
      ¬Fin15AnchoredAtom2708 chi ∧
      ¬Fin15AnchoredAtom2710 chi ∧
      ¬Fin15AnchoredAtom2715 chi ∧
      ¬Fin15AnchoredAtom2746 chi ∧
      ¬Fin15AnchoredAtom2781 chi ∧
      ¬Fin15AnchoredAtom2960 chi ∧
      ¬Fin15AnchoredAtom2962 chi ∧
      ¬Fin15AnchoredAtom2964 chi ∧
      ¬Fin15AnchoredAtom2977 chi ∧
      ¬Fin15AnchoredAtom2979 chi ∧
      ¬Fin15AnchoredAtom2984 chi ∧
      ¬Fin15AnchoredAtom2998 chi ∧
      ¬Fin15AnchoredAtom3000 chi ∧
      ¬Fin15AnchoredAtom3005 chi ∧
      ¬Fin15AnchoredAtom3036 chi ∧
      ¬Fin15AnchoredAtom3423 chi ∧
      ¬Fin15AnchoredAtom3425 chi ∧
      ¬Fin15AnchoredAtom3430 chi ∧
      ¬Fin15AnchoredAtom3461 chi ∧
      ¬Fin15AnchoredAtom3496 chi ∧
      ¬Fin15AnchoredAtom3918 chi ∧
      ¬Fin15AnchoredAtom3920 chi ∧
      ¬Fin15AnchoredAtom3925 chi ∧
      ¬Fin15AnchoredAtom3956 chi ∧
      ¬Fin15AnchoredAtom3991 chi ∧
      ¬Fin15AnchoredAtom4727 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 6, 7, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21703
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1851 Fin15AnchoredAtom1854 Fin15AnchoredAtom1856
    Fin15AnchoredAtom1858 Fin15AnchoredAtom1861 Fin15AnchoredAtom1863 Fin15AnchoredAtom1865
    Fin15AnchoredAtom1878 Fin15AnchoredAtom1880 Fin15AnchoredAtom1885 Fin15AnchoredAtom2025
    Fin15AnchoredAtom2027 Fin15AnchoredAtom2029 Fin15AnchoredAtom2042 Fin15AnchoredAtom2044
    Fin15AnchoredAtom2049 Fin15AnchoredAtom2063 Fin15AnchoredAtom2065 Fin15AnchoredAtom2070
    Fin15AnchoredAtom2101 Fin15AnchoredAtom2245 Fin15AnchoredAtom2247 Fin15AnchoredAtom2249
    Fin15AnchoredAtom2262 Fin15AnchoredAtom2264 Fin15AnchoredAtom2269 Fin15AnchoredAtom2283
    Fin15AnchoredAtom2285 Fin15AnchoredAtom2290 Fin15AnchoredAtom2321 Fin15AnchoredAtom2708
    Fin15AnchoredAtom2710 Fin15AnchoredAtom2715 Fin15AnchoredAtom2746 Fin15AnchoredAtom2781
    Fin15AnchoredAtom2960 Fin15AnchoredAtom2962 Fin15AnchoredAtom2964 Fin15AnchoredAtom2977
    Fin15AnchoredAtom2979 Fin15AnchoredAtom2984 Fin15AnchoredAtom2998 Fin15AnchoredAtom3000
    Fin15AnchoredAtom3005 Fin15AnchoredAtom3036 Fin15AnchoredAtom3423 Fin15AnchoredAtom3425
    Fin15AnchoredAtom3430 Fin15AnchoredAtom3461 Fin15AnchoredAtom3496 Fin15AnchoredAtom3918
    Fin15AnchoredAtom3920 Fin15AnchoredAtom3925 Fin15AnchoredAtom3956 Fin15AnchoredAtom3991
    Fin15AnchoredAtom4727 at hbad
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

theorem fin15Anchored_clause30749 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom1886 chi ∧
      ¬Fin15AnchoredAtom2025 chi ∧
      ¬Fin15AnchoredAtom2028 chi ∧
      ¬Fin15AnchoredAtom2029 chi ∧
      ¬Fin15AnchoredAtom2043 chi ∧
      ¬Fin15AnchoredAtom2044 chi ∧
      ¬Fin15AnchoredAtom2050 chi ∧
      ¬Fin15AnchoredAtom2064 chi ∧
      ¬Fin15AnchoredAtom2065 chi ∧
      ¬Fin15AnchoredAtom2071 chi ∧
      ¬Fin15AnchoredAtom2102 chi ∧
      ¬Fin15AnchoredAtom2245 chi ∧
      ¬Fin15AnchoredAtom2248 chi ∧
      ¬Fin15AnchoredAtom2249 chi ∧
      ¬Fin15AnchoredAtom2263 chi ∧
      ¬Fin15AnchoredAtom2264 chi ∧
      ¬Fin15AnchoredAtom2270 chi ∧
      ¬Fin15AnchoredAtom2284 chi ∧
      ¬Fin15AnchoredAtom2285 chi ∧
      ¬Fin15AnchoredAtom2291 chi ∧
      ¬Fin15AnchoredAtom2322 chi ∧
      ¬Fin15AnchoredAtom2709 chi ∧
      ¬Fin15AnchoredAtom2710 chi ∧
      ¬Fin15AnchoredAtom2716 chi ∧
      ¬Fin15AnchoredAtom2747 chi ∧
      ¬Fin15AnchoredAtom2782 chi ∧
      ¬Fin15AnchoredAtom2960 chi ∧
      ¬Fin15AnchoredAtom2963 chi ∧
      ¬Fin15AnchoredAtom2964 chi ∧
      ¬Fin15AnchoredAtom2978 chi ∧
      ¬Fin15AnchoredAtom2979 chi ∧
      ¬Fin15AnchoredAtom2985 chi ∧
      ¬Fin15AnchoredAtom2999 chi ∧
      ¬Fin15AnchoredAtom3000 chi ∧
      ¬Fin15AnchoredAtom3006 chi ∧
      ¬Fin15AnchoredAtom3037 chi ∧
      ¬Fin15AnchoredAtom3424 chi ∧
      ¬Fin15AnchoredAtom3425 chi ∧
      ¬Fin15AnchoredAtom3431 chi ∧
      ¬Fin15AnchoredAtom3462 chi ∧
      ¬Fin15AnchoredAtom3497 chi ∧
      ¬Fin15AnchoredAtom3919 chi ∧
      ¬Fin15AnchoredAtom3920 chi ∧
      ¬Fin15AnchoredAtom3926 chi ∧
      ¬Fin15AnchoredAtom3957 chi ∧
      ¬Fin15AnchoredAtom3992 chi ∧
      ¬Fin15AnchoredAtom4728 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 6, 7, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25799
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1851 Fin15AnchoredAtom1854 Fin15AnchoredAtom1857
    Fin15AnchoredAtom1858 Fin15AnchoredAtom1861 Fin15AnchoredAtom1864 Fin15AnchoredAtom1865
    Fin15AnchoredAtom1879 Fin15AnchoredAtom1880 Fin15AnchoredAtom1886 Fin15AnchoredAtom2025
    Fin15AnchoredAtom2028 Fin15AnchoredAtom2029 Fin15AnchoredAtom2043 Fin15AnchoredAtom2044
    Fin15AnchoredAtom2050 Fin15AnchoredAtom2064 Fin15AnchoredAtom2065 Fin15AnchoredAtom2071
    Fin15AnchoredAtom2102 Fin15AnchoredAtom2245 Fin15AnchoredAtom2248 Fin15AnchoredAtom2249
    Fin15AnchoredAtom2263 Fin15AnchoredAtom2264 Fin15AnchoredAtom2270 Fin15AnchoredAtom2284
    Fin15AnchoredAtom2285 Fin15AnchoredAtom2291 Fin15AnchoredAtom2322 Fin15AnchoredAtom2709
    Fin15AnchoredAtom2710 Fin15AnchoredAtom2716 Fin15AnchoredAtom2747 Fin15AnchoredAtom2782
    Fin15AnchoredAtom2960 Fin15AnchoredAtom2963 Fin15AnchoredAtom2964 Fin15AnchoredAtom2978
    Fin15AnchoredAtom2979 Fin15AnchoredAtom2985 Fin15AnchoredAtom2999 Fin15AnchoredAtom3000
    Fin15AnchoredAtom3006 Fin15AnchoredAtom3037 Fin15AnchoredAtom3424 Fin15AnchoredAtom3425
    Fin15AnchoredAtom3431 Fin15AnchoredAtom3462 Fin15AnchoredAtom3497 Fin15AnchoredAtom3919
    Fin15AnchoredAtom3920 Fin15AnchoredAtom3926 Fin15AnchoredAtom3957 Fin15AnchoredAtom3992
    Fin15AnchoredAtom4728 at hbad
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

theorem fin15Anchored_clause30750 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom1886 chi ∧
      ¬Fin15AnchoredAtom2027 chi ∧
      ¬Fin15AnchoredAtom2028 chi ∧
      ¬Fin15AnchoredAtom2029 chi ∧
      ¬Fin15AnchoredAtom2048 chi ∧
      ¬Fin15AnchoredAtom2049 chi ∧
      ¬Fin15AnchoredAtom2050 chi ∧
      ¬Fin15AnchoredAtom2069 chi ∧
      ¬Fin15AnchoredAtom2070 chi ∧
      ¬Fin15AnchoredAtom2071 chi ∧
      ¬Fin15AnchoredAtom2106 chi ∧
      ¬Fin15AnchoredAtom2247 chi ∧
      ¬Fin15AnchoredAtom2248 chi ∧
      ¬Fin15AnchoredAtom2249 chi ∧
      ¬Fin15AnchoredAtom2268 chi ∧
      ¬Fin15AnchoredAtom2269 chi ∧
      ¬Fin15AnchoredAtom2270 chi ∧
      ¬Fin15AnchoredAtom2289 chi ∧
      ¬Fin15AnchoredAtom2290 chi ∧
      ¬Fin15AnchoredAtom2291 chi ∧
      ¬Fin15AnchoredAtom2326 chi ∧
      ¬Fin15AnchoredAtom2714 chi ∧
      ¬Fin15AnchoredAtom2715 chi ∧
      ¬Fin15AnchoredAtom2716 chi ∧
      ¬Fin15AnchoredAtom2751 chi ∧
      ¬Fin15AnchoredAtom2786 chi ∧
      ¬Fin15AnchoredAtom2962 chi ∧
      ¬Fin15AnchoredAtom2963 chi ∧
      ¬Fin15AnchoredAtom2964 chi ∧
      ¬Fin15AnchoredAtom2983 chi ∧
      ¬Fin15AnchoredAtom2984 chi ∧
      ¬Fin15AnchoredAtom2985 chi ∧
      ¬Fin15AnchoredAtom3004 chi ∧
      ¬Fin15AnchoredAtom3005 chi ∧
      ¬Fin15AnchoredAtom3006 chi ∧
      ¬Fin15AnchoredAtom3041 chi ∧
      ¬Fin15AnchoredAtom3429 chi ∧
      ¬Fin15AnchoredAtom3430 chi ∧
      ¬Fin15AnchoredAtom3431 chi ∧
      ¬Fin15AnchoredAtom3466 chi ∧
      ¬Fin15AnchoredAtom3501 chi ∧
      ¬Fin15AnchoredAtom3924 chi ∧
      ¬Fin15AnchoredAtom3925 chi ∧
      ¬Fin15AnchoredAtom3926 chi ∧
      ¬Fin15AnchoredAtom3961 chi ∧
      ¬Fin15AnchoredAtom3996 chi ∧
      ¬Fin15AnchoredAtom4732 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 6, 7, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask28871
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1851 Fin15AnchoredAtom1856 Fin15AnchoredAtom1857
    Fin15AnchoredAtom1858 Fin15AnchoredAtom1863 Fin15AnchoredAtom1864 Fin15AnchoredAtom1865
    Fin15AnchoredAtom1884 Fin15AnchoredAtom1885 Fin15AnchoredAtom1886 Fin15AnchoredAtom2027
    Fin15AnchoredAtom2028 Fin15AnchoredAtom2029 Fin15AnchoredAtom2048 Fin15AnchoredAtom2049
    Fin15AnchoredAtom2050 Fin15AnchoredAtom2069 Fin15AnchoredAtom2070 Fin15AnchoredAtom2071
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2247 Fin15AnchoredAtom2248 Fin15AnchoredAtom2249
    Fin15AnchoredAtom2268 Fin15AnchoredAtom2269 Fin15AnchoredAtom2270 Fin15AnchoredAtom2289
    Fin15AnchoredAtom2290 Fin15AnchoredAtom2291 Fin15AnchoredAtom2326 Fin15AnchoredAtom2714
    Fin15AnchoredAtom2715 Fin15AnchoredAtom2716 Fin15AnchoredAtom2751 Fin15AnchoredAtom2786
    Fin15AnchoredAtom2962 Fin15AnchoredAtom2963 Fin15AnchoredAtom2964 Fin15AnchoredAtom2983
    Fin15AnchoredAtom2984 Fin15AnchoredAtom2985 Fin15AnchoredAtom3004 Fin15AnchoredAtom3005
    Fin15AnchoredAtom3006 Fin15AnchoredAtom3041 Fin15AnchoredAtom3429 Fin15AnchoredAtom3430
    Fin15AnchoredAtom3431 Fin15AnchoredAtom3466 Fin15AnchoredAtom3501 Fin15AnchoredAtom3924
    Fin15AnchoredAtom3925 Fin15AnchoredAtom3926 Fin15AnchoredAtom3961 Fin15AnchoredAtom3996
    Fin15AnchoredAtom4732 at hbad
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

theorem fin15Anchored_clause30751 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1855 chi ∧
      ¬Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom1873 chi ∧
      ¬Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom1877 chi ∧
      ¬Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom1881 chi ∧
      ¬Fin15AnchoredAtom2036 chi ∧
      ¬Fin15AnchoredAtom2037 chi ∧
      ¬Fin15AnchoredAtom2038 chi ∧
      ¬Fin15AnchoredAtom2041 chi ∧
      ¬Fin15AnchoredAtom2042 chi ∧
      ¬Fin15AnchoredAtom2045 chi ∧
      ¬Fin15AnchoredAtom2087 chi ∧
      ¬Fin15AnchoredAtom2088 chi ∧
      ¬Fin15AnchoredAtom2091 chi ∧
      ¬Fin15AnchoredAtom2097 chi ∧
      ¬Fin15AnchoredAtom2256 chi ∧
      ¬Fin15AnchoredAtom2257 chi ∧
      ¬Fin15AnchoredAtom2258 chi ∧
      ¬Fin15AnchoredAtom2261 chi ∧
      ¬Fin15AnchoredAtom2262 chi ∧
      ¬Fin15AnchoredAtom2265 chi ∧
      ¬Fin15AnchoredAtom2307 chi ∧
      ¬Fin15AnchoredAtom2308 chi ∧
      ¬Fin15AnchoredAtom2311 chi ∧
      ¬Fin15AnchoredAtom2317 chi ∧
      ¬Fin15AnchoredAtom2732 chi ∧
      ¬Fin15AnchoredAtom2733 chi ∧
      ¬Fin15AnchoredAtom2736 chi ∧
      ¬Fin15AnchoredAtom2742 chi ∧
      ¬Fin15AnchoredAtom2807 chi ∧
      ¬Fin15AnchoredAtom2971 chi ∧
      ¬Fin15AnchoredAtom2972 chi ∧
      ¬Fin15AnchoredAtom2973 chi ∧
      ¬Fin15AnchoredAtom2976 chi ∧
      ¬Fin15AnchoredAtom2977 chi ∧
      ¬Fin15AnchoredAtom2980 chi ∧
      ¬Fin15AnchoredAtom3022 chi ∧
      ¬Fin15AnchoredAtom3023 chi ∧
      ¬Fin15AnchoredAtom3026 chi ∧
      ¬Fin15AnchoredAtom3032 chi ∧
      ¬Fin15AnchoredAtom3447 chi ∧
      ¬Fin15AnchoredAtom3448 chi ∧
      ¬Fin15AnchoredAtom3451 chi ∧
      ¬Fin15AnchoredAtom3457 chi ∧
      ¬Fin15AnchoredAtom3522 chi ∧
      ¬Fin15AnchoredAtom3942 chi ∧
      ¬Fin15AnchoredAtom3943 chi ∧
      ¬Fin15AnchoredAtom3946 chi ∧
      ¬Fin15AnchoredAtom3952 chi ∧
      ¬Fin15AnchoredAtom4017 chi ∧
      ¬Fin15AnchoredAtom4753 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 6, 9, 10, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask07751
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1853 Fin15AnchoredAtom1854 Fin15AnchoredAtom1855
    Fin15AnchoredAtom1856 Fin15AnchoredAtom1872 Fin15AnchoredAtom1873 Fin15AnchoredAtom1874
    Fin15AnchoredAtom1877 Fin15AnchoredAtom1878 Fin15AnchoredAtom1881 Fin15AnchoredAtom2036
    Fin15AnchoredAtom2037 Fin15AnchoredAtom2038 Fin15AnchoredAtom2041 Fin15AnchoredAtom2042
    Fin15AnchoredAtom2045 Fin15AnchoredAtom2087 Fin15AnchoredAtom2088 Fin15AnchoredAtom2091
    Fin15AnchoredAtom2097 Fin15AnchoredAtom2256 Fin15AnchoredAtom2257 Fin15AnchoredAtom2258
    Fin15AnchoredAtom2261 Fin15AnchoredAtom2262 Fin15AnchoredAtom2265 Fin15AnchoredAtom2307
    Fin15AnchoredAtom2308 Fin15AnchoredAtom2311 Fin15AnchoredAtom2317 Fin15AnchoredAtom2732
    Fin15AnchoredAtom2733 Fin15AnchoredAtom2736 Fin15AnchoredAtom2742 Fin15AnchoredAtom2807
    Fin15AnchoredAtom2971 Fin15AnchoredAtom2972 Fin15AnchoredAtom2973 Fin15AnchoredAtom2976
    Fin15AnchoredAtom2977 Fin15AnchoredAtom2980 Fin15AnchoredAtom3022 Fin15AnchoredAtom3023
    Fin15AnchoredAtom3026 Fin15AnchoredAtom3032 Fin15AnchoredAtom3447 Fin15AnchoredAtom3448
    Fin15AnchoredAtom3451 Fin15AnchoredAtom3457 Fin15AnchoredAtom3522 Fin15AnchoredAtom3942
    Fin15AnchoredAtom3943 Fin15AnchoredAtom3946 Fin15AnchoredAtom3952 Fin15AnchoredAtom4017
    Fin15AnchoredAtom4753 at hbad
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

theorem fin15Anchored_clause30752 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom2036 chi ∧
      ¬Fin15AnchoredAtom2038 chi ∧
      ¬Fin15AnchoredAtom2039 chi ∧
      ¬Fin15AnchoredAtom2042 chi ∧
      ¬Fin15AnchoredAtom2043 chi ∧
      ¬Fin15AnchoredAtom2048 chi ∧
      ¬Fin15AnchoredAtom2088 chi ∧
      ¬Fin15AnchoredAtom2089 chi ∧
      ¬Fin15AnchoredAtom2094 chi ∧
      ¬Fin15AnchoredAtom2100 chi ∧
      ¬Fin15AnchoredAtom2256 chi ∧
      ¬Fin15AnchoredAtom2258 chi ∧
      ¬Fin15AnchoredAtom2259 chi ∧
      ¬Fin15AnchoredAtom2262 chi ∧
      ¬Fin15AnchoredAtom2263 chi ∧
      ¬Fin15AnchoredAtom2268 chi ∧
      ¬Fin15AnchoredAtom2308 chi ∧
      ¬Fin15AnchoredAtom2309 chi ∧
      ¬Fin15AnchoredAtom2314 chi ∧
      ¬Fin15AnchoredAtom2320 chi ∧
      ¬Fin15AnchoredAtom2733 chi ∧
      ¬Fin15AnchoredAtom2734 chi ∧
      ¬Fin15AnchoredAtom2739 chi ∧
      ¬Fin15AnchoredAtom2745 chi ∧
      ¬Fin15AnchoredAtom2810 chi ∧
      ¬Fin15AnchoredAtom2971 chi ∧
      ¬Fin15AnchoredAtom2973 chi ∧
      ¬Fin15AnchoredAtom2974 chi ∧
      ¬Fin15AnchoredAtom2977 chi ∧
      ¬Fin15AnchoredAtom2978 chi ∧
      ¬Fin15AnchoredAtom2983 chi ∧
      ¬Fin15AnchoredAtom3023 chi ∧
      ¬Fin15AnchoredAtom3024 chi ∧
      ¬Fin15AnchoredAtom3029 chi ∧
      ¬Fin15AnchoredAtom3035 chi ∧
      ¬Fin15AnchoredAtom3448 chi ∧
      ¬Fin15AnchoredAtom3449 chi ∧
      ¬Fin15AnchoredAtom3454 chi ∧
      ¬Fin15AnchoredAtom3460 chi ∧
      ¬Fin15AnchoredAtom3525 chi ∧
      ¬Fin15AnchoredAtom3943 chi ∧
      ¬Fin15AnchoredAtom3944 chi ∧
      ¬Fin15AnchoredAtom3949 chi ∧
      ¬Fin15AnchoredAtom3955 chi ∧
      ¬Fin15AnchoredAtom4020 chi ∧
      ¬Fin15AnchoredAtom4756 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 6, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13895
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1853 Fin15AnchoredAtom1854 Fin15AnchoredAtom1856
    Fin15AnchoredAtom1857 Fin15AnchoredAtom1872 Fin15AnchoredAtom1874 Fin15AnchoredAtom1875
    Fin15AnchoredAtom1878 Fin15AnchoredAtom1879 Fin15AnchoredAtom1884 Fin15AnchoredAtom2036
    Fin15AnchoredAtom2038 Fin15AnchoredAtom2039 Fin15AnchoredAtom2042 Fin15AnchoredAtom2043
    Fin15AnchoredAtom2048 Fin15AnchoredAtom2088 Fin15AnchoredAtom2089 Fin15AnchoredAtom2094
    Fin15AnchoredAtom2100 Fin15AnchoredAtom2256 Fin15AnchoredAtom2258 Fin15AnchoredAtom2259
    Fin15AnchoredAtom2262 Fin15AnchoredAtom2263 Fin15AnchoredAtom2268 Fin15AnchoredAtom2308
    Fin15AnchoredAtom2309 Fin15AnchoredAtom2314 Fin15AnchoredAtom2320 Fin15AnchoredAtom2733
    Fin15AnchoredAtom2734 Fin15AnchoredAtom2739 Fin15AnchoredAtom2745 Fin15AnchoredAtom2810
    Fin15AnchoredAtom2971 Fin15AnchoredAtom2973 Fin15AnchoredAtom2974 Fin15AnchoredAtom2977
    Fin15AnchoredAtom2978 Fin15AnchoredAtom2983 Fin15AnchoredAtom3023 Fin15AnchoredAtom3024
    Fin15AnchoredAtom3029 Fin15AnchoredAtom3035 Fin15AnchoredAtom3448 Fin15AnchoredAtom3449
    Fin15AnchoredAtom3454 Fin15AnchoredAtom3460 Fin15AnchoredAtom3525 Fin15AnchoredAtom3943
    Fin15AnchoredAtom3944 Fin15AnchoredAtom3949 Fin15AnchoredAtom3955 Fin15AnchoredAtom4020
    Fin15AnchoredAtom4756 at hbad
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

theorem fin15Anchored_clause30753 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom2036 chi ∧
      ¬Fin15AnchoredAtom2038 chi ∧
      ¬Fin15AnchoredAtom2040 chi ∧
      ¬Fin15AnchoredAtom2042 chi ∧
      ¬Fin15AnchoredAtom2044 chi ∧
      ¬Fin15AnchoredAtom2049 chi ∧
      ¬Fin15AnchoredAtom2088 chi ∧
      ¬Fin15AnchoredAtom2090 chi ∧
      ¬Fin15AnchoredAtom2095 chi ∧
      ¬Fin15AnchoredAtom2101 chi ∧
      ¬Fin15AnchoredAtom2256 chi ∧
      ¬Fin15AnchoredAtom2258 chi ∧
      ¬Fin15AnchoredAtom2260 chi ∧
      ¬Fin15AnchoredAtom2262 chi ∧
      ¬Fin15AnchoredAtom2264 chi ∧
      ¬Fin15AnchoredAtom2269 chi ∧
      ¬Fin15AnchoredAtom2308 chi ∧
      ¬Fin15AnchoredAtom2310 chi ∧
      ¬Fin15AnchoredAtom2315 chi ∧
      ¬Fin15AnchoredAtom2321 chi ∧
      ¬Fin15AnchoredAtom2733 chi ∧
      ¬Fin15AnchoredAtom2735 chi ∧
      ¬Fin15AnchoredAtom2740 chi ∧
      ¬Fin15AnchoredAtom2746 chi ∧
      ¬Fin15AnchoredAtom2811 chi ∧
      ¬Fin15AnchoredAtom2971 chi ∧
      ¬Fin15AnchoredAtom2973 chi ∧
      ¬Fin15AnchoredAtom2975 chi ∧
      ¬Fin15AnchoredAtom2977 chi ∧
      ¬Fin15AnchoredAtom2979 chi ∧
      ¬Fin15AnchoredAtom2984 chi ∧
      ¬Fin15AnchoredAtom3023 chi ∧
      ¬Fin15AnchoredAtom3025 chi ∧
      ¬Fin15AnchoredAtom3030 chi ∧
      ¬Fin15AnchoredAtom3036 chi ∧
      ¬Fin15AnchoredAtom3448 chi ∧
      ¬Fin15AnchoredAtom3450 chi ∧
      ¬Fin15AnchoredAtom3455 chi ∧
      ¬Fin15AnchoredAtom3461 chi ∧
      ¬Fin15AnchoredAtom3526 chi ∧
      ¬Fin15AnchoredAtom3943 chi ∧
      ¬Fin15AnchoredAtom3945 chi ∧
      ¬Fin15AnchoredAtom3950 chi ∧
      ¬Fin15AnchoredAtom3956 chi ∧
      ¬Fin15AnchoredAtom4021 chi ∧
      ¬Fin15AnchoredAtom4757 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 6, 9, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22087
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1853 Fin15AnchoredAtom1854 Fin15AnchoredAtom1856
    Fin15AnchoredAtom1858 Fin15AnchoredAtom1872 Fin15AnchoredAtom1874 Fin15AnchoredAtom1876
    Fin15AnchoredAtom1878 Fin15AnchoredAtom1880 Fin15AnchoredAtom1885 Fin15AnchoredAtom2036
    Fin15AnchoredAtom2038 Fin15AnchoredAtom2040 Fin15AnchoredAtom2042 Fin15AnchoredAtom2044
    Fin15AnchoredAtom2049 Fin15AnchoredAtom2088 Fin15AnchoredAtom2090 Fin15AnchoredAtom2095
    Fin15AnchoredAtom2101 Fin15AnchoredAtom2256 Fin15AnchoredAtom2258 Fin15AnchoredAtom2260
    Fin15AnchoredAtom2262 Fin15AnchoredAtom2264 Fin15AnchoredAtom2269 Fin15AnchoredAtom2308
    Fin15AnchoredAtom2310 Fin15AnchoredAtom2315 Fin15AnchoredAtom2321 Fin15AnchoredAtom2733
    Fin15AnchoredAtom2735 Fin15AnchoredAtom2740 Fin15AnchoredAtom2746 Fin15AnchoredAtom2811
    Fin15AnchoredAtom2971 Fin15AnchoredAtom2973 Fin15AnchoredAtom2975 Fin15AnchoredAtom2977
    Fin15AnchoredAtom2979 Fin15AnchoredAtom2984 Fin15AnchoredAtom3023 Fin15AnchoredAtom3025
    Fin15AnchoredAtom3030 Fin15AnchoredAtom3036 Fin15AnchoredAtom3448 Fin15AnchoredAtom3450
    Fin15AnchoredAtom3455 Fin15AnchoredAtom3461 Fin15AnchoredAtom3526 Fin15AnchoredAtom3943
    Fin15AnchoredAtom3945 Fin15AnchoredAtom3950 Fin15AnchoredAtom3956 Fin15AnchoredAtom4021
    Fin15AnchoredAtom4757 at hbad
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

theorem fin15Anchored_clause30754 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom1886 chi ∧
      ¬Fin15AnchoredAtom2036 chi ∧
      ¬Fin15AnchoredAtom2039 chi ∧
      ¬Fin15AnchoredAtom2040 chi ∧
      ¬Fin15AnchoredAtom2043 chi ∧
      ¬Fin15AnchoredAtom2044 chi ∧
      ¬Fin15AnchoredAtom2050 chi ∧
      ¬Fin15AnchoredAtom2089 chi ∧
      ¬Fin15AnchoredAtom2090 chi ∧
      ¬Fin15AnchoredAtom2096 chi ∧
      ¬Fin15AnchoredAtom2102 chi ∧
      ¬Fin15AnchoredAtom2256 chi ∧
      ¬Fin15AnchoredAtom2259 chi ∧
      ¬Fin15AnchoredAtom2260 chi ∧
      ¬Fin15AnchoredAtom2263 chi ∧
      ¬Fin15AnchoredAtom2264 chi ∧
      ¬Fin15AnchoredAtom2270 chi ∧
      ¬Fin15AnchoredAtom2309 chi ∧
      ¬Fin15AnchoredAtom2310 chi ∧
      ¬Fin15AnchoredAtom2316 chi ∧
      ¬Fin15AnchoredAtom2322 chi ∧
      ¬Fin15AnchoredAtom2734 chi ∧
      ¬Fin15AnchoredAtom2735 chi ∧
      ¬Fin15AnchoredAtom2741 chi ∧
      ¬Fin15AnchoredAtom2747 chi ∧
      ¬Fin15AnchoredAtom2812 chi ∧
      ¬Fin15AnchoredAtom2971 chi ∧
      ¬Fin15AnchoredAtom2974 chi ∧
      ¬Fin15AnchoredAtom2975 chi ∧
      ¬Fin15AnchoredAtom2978 chi ∧
      ¬Fin15AnchoredAtom2979 chi ∧
      ¬Fin15AnchoredAtom2985 chi ∧
      ¬Fin15AnchoredAtom3024 chi ∧
      ¬Fin15AnchoredAtom3025 chi ∧
      ¬Fin15AnchoredAtom3031 chi ∧
      ¬Fin15AnchoredAtom3037 chi ∧
      ¬Fin15AnchoredAtom3449 chi ∧
      ¬Fin15AnchoredAtom3450 chi ∧
      ¬Fin15AnchoredAtom3456 chi ∧
      ¬Fin15AnchoredAtom3462 chi ∧
      ¬Fin15AnchoredAtom3527 chi ∧
      ¬Fin15AnchoredAtom3944 chi ∧
      ¬Fin15AnchoredAtom3945 chi ∧
      ¬Fin15AnchoredAtom3951 chi ∧
      ¬Fin15AnchoredAtom3957 chi ∧
      ¬Fin15AnchoredAtom4022 chi ∧
      ¬Fin15AnchoredAtom4758 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 6, 9, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26183
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1853 Fin15AnchoredAtom1854 Fin15AnchoredAtom1857
    Fin15AnchoredAtom1858 Fin15AnchoredAtom1872 Fin15AnchoredAtom1875 Fin15AnchoredAtom1876
    Fin15AnchoredAtom1879 Fin15AnchoredAtom1880 Fin15AnchoredAtom1886 Fin15AnchoredAtom2036
    Fin15AnchoredAtom2039 Fin15AnchoredAtom2040 Fin15AnchoredAtom2043 Fin15AnchoredAtom2044
    Fin15AnchoredAtom2050 Fin15AnchoredAtom2089 Fin15AnchoredAtom2090 Fin15AnchoredAtom2096
    Fin15AnchoredAtom2102 Fin15AnchoredAtom2256 Fin15AnchoredAtom2259 Fin15AnchoredAtom2260
    Fin15AnchoredAtom2263 Fin15AnchoredAtom2264 Fin15AnchoredAtom2270 Fin15AnchoredAtom2309
    Fin15AnchoredAtom2310 Fin15AnchoredAtom2316 Fin15AnchoredAtom2322 Fin15AnchoredAtom2734
    Fin15AnchoredAtom2735 Fin15AnchoredAtom2741 Fin15AnchoredAtom2747 Fin15AnchoredAtom2812
    Fin15AnchoredAtom2971 Fin15AnchoredAtom2974 Fin15AnchoredAtom2975 Fin15AnchoredAtom2978
    Fin15AnchoredAtom2979 Fin15AnchoredAtom2985 Fin15AnchoredAtom3024 Fin15AnchoredAtom3025
    Fin15AnchoredAtom3031 Fin15AnchoredAtom3037 Fin15AnchoredAtom3449 Fin15AnchoredAtom3450
    Fin15AnchoredAtom3456 Fin15AnchoredAtom3462 Fin15AnchoredAtom3527 Fin15AnchoredAtom3944
    Fin15AnchoredAtom3945 Fin15AnchoredAtom3951 Fin15AnchoredAtom3957 Fin15AnchoredAtom4022
    Fin15AnchoredAtom4758 at hbad
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

theorem fin15Anchored_clause30755 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom1886 chi ∧
      ¬Fin15AnchoredAtom2038 chi ∧
      ¬Fin15AnchoredAtom2039 chi ∧
      ¬Fin15AnchoredAtom2040 chi ∧
      ¬Fin15AnchoredAtom2048 chi ∧
      ¬Fin15AnchoredAtom2049 chi ∧
      ¬Fin15AnchoredAtom2050 chi ∧
      ¬Fin15AnchoredAtom2094 chi ∧
      ¬Fin15AnchoredAtom2095 chi ∧
      ¬Fin15AnchoredAtom2096 chi ∧
      ¬Fin15AnchoredAtom2106 chi ∧
      ¬Fin15AnchoredAtom2258 chi ∧
      ¬Fin15AnchoredAtom2259 chi ∧
      ¬Fin15AnchoredAtom2260 chi ∧
      ¬Fin15AnchoredAtom2268 chi ∧
      ¬Fin15AnchoredAtom2269 chi ∧
      ¬Fin15AnchoredAtom2270 chi ∧
      ¬Fin15AnchoredAtom2314 chi ∧
      ¬Fin15AnchoredAtom2315 chi ∧
      ¬Fin15AnchoredAtom2316 chi ∧
      ¬Fin15AnchoredAtom2326 chi ∧
      ¬Fin15AnchoredAtom2739 chi ∧
      ¬Fin15AnchoredAtom2740 chi ∧
      ¬Fin15AnchoredAtom2741 chi ∧
      ¬Fin15AnchoredAtom2751 chi ∧
      ¬Fin15AnchoredAtom2816 chi ∧
      ¬Fin15AnchoredAtom2973 chi ∧
      ¬Fin15AnchoredAtom2974 chi ∧
      ¬Fin15AnchoredAtom2975 chi ∧
      ¬Fin15AnchoredAtom2983 chi ∧
      ¬Fin15AnchoredAtom2984 chi ∧
      ¬Fin15AnchoredAtom2985 chi ∧
      ¬Fin15AnchoredAtom3029 chi ∧
      ¬Fin15AnchoredAtom3030 chi ∧
      ¬Fin15AnchoredAtom3031 chi ∧
      ¬Fin15AnchoredAtom3041 chi ∧
      ¬Fin15AnchoredAtom3454 chi ∧
      ¬Fin15AnchoredAtom3455 chi ∧
      ¬Fin15AnchoredAtom3456 chi ∧
      ¬Fin15AnchoredAtom3466 chi ∧
      ¬Fin15AnchoredAtom3531 chi ∧
      ¬Fin15AnchoredAtom3949 chi ∧
      ¬Fin15AnchoredAtom3950 chi ∧
      ¬Fin15AnchoredAtom3951 chi ∧
      ¬Fin15AnchoredAtom3961 chi ∧
      ¬Fin15AnchoredAtom4026 chi ∧
      ¬Fin15AnchoredAtom4762 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 6, 9, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29255
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1853 Fin15AnchoredAtom1856 Fin15AnchoredAtom1857
    Fin15AnchoredAtom1858 Fin15AnchoredAtom1874 Fin15AnchoredAtom1875 Fin15AnchoredAtom1876
    Fin15AnchoredAtom1884 Fin15AnchoredAtom1885 Fin15AnchoredAtom1886 Fin15AnchoredAtom2038
    Fin15AnchoredAtom2039 Fin15AnchoredAtom2040 Fin15AnchoredAtom2048 Fin15AnchoredAtom2049
    Fin15AnchoredAtom2050 Fin15AnchoredAtom2094 Fin15AnchoredAtom2095 Fin15AnchoredAtom2096
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2258 Fin15AnchoredAtom2259 Fin15AnchoredAtom2260
    Fin15AnchoredAtom2268 Fin15AnchoredAtom2269 Fin15AnchoredAtom2270 Fin15AnchoredAtom2314
    Fin15AnchoredAtom2315 Fin15AnchoredAtom2316 Fin15AnchoredAtom2326 Fin15AnchoredAtom2739
    Fin15AnchoredAtom2740 Fin15AnchoredAtom2741 Fin15AnchoredAtom2751 Fin15AnchoredAtom2816
    Fin15AnchoredAtom2973 Fin15AnchoredAtom2974 Fin15AnchoredAtom2975 Fin15AnchoredAtom2983
    Fin15AnchoredAtom2984 Fin15AnchoredAtom2985 Fin15AnchoredAtom3029 Fin15AnchoredAtom3030
    Fin15AnchoredAtom3031 Fin15AnchoredAtom3041 Fin15AnchoredAtom3454 Fin15AnchoredAtom3455
    Fin15AnchoredAtom3456 Fin15AnchoredAtom3466 Fin15AnchoredAtom3531 Fin15AnchoredAtom3949
    Fin15AnchoredAtom3950 Fin15AnchoredAtom3951 Fin15AnchoredAtom3961 Fin15AnchoredAtom4026
    Fin15AnchoredAtom4762 at hbad
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

theorem fin15Anchored_clause30756 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom1886 chi ∧
      ¬Fin15AnchoredAtom2042 chi ∧
      ¬Fin15AnchoredAtom2043 chi ∧
      ¬Fin15AnchoredAtom2044 chi ∧
      ¬Fin15AnchoredAtom2048 chi ∧
      ¬Fin15AnchoredAtom2049 chi ∧
      ¬Fin15AnchoredAtom2050 chi ∧
      ¬Fin15AnchoredAtom2100 chi ∧
      ¬Fin15AnchoredAtom2101 chi ∧
      ¬Fin15AnchoredAtom2102 chi ∧
      ¬Fin15AnchoredAtom2106 chi ∧
      ¬Fin15AnchoredAtom2262 chi ∧
      ¬Fin15AnchoredAtom2263 chi ∧
      ¬Fin15AnchoredAtom2264 chi ∧
      ¬Fin15AnchoredAtom2268 chi ∧
      ¬Fin15AnchoredAtom2269 chi ∧
      ¬Fin15AnchoredAtom2270 chi ∧
      ¬Fin15AnchoredAtom2320 chi ∧
      ¬Fin15AnchoredAtom2321 chi ∧
      ¬Fin15AnchoredAtom2322 chi ∧
      ¬Fin15AnchoredAtom2326 chi ∧
      ¬Fin15AnchoredAtom2745 chi ∧
      ¬Fin15AnchoredAtom2746 chi ∧
      ¬Fin15AnchoredAtom2747 chi ∧
      ¬Fin15AnchoredAtom2751 chi ∧
      ¬Fin15AnchoredAtom2820 chi ∧
      ¬Fin15AnchoredAtom2977 chi ∧
      ¬Fin15AnchoredAtom2978 chi ∧
      ¬Fin15AnchoredAtom2979 chi ∧
      ¬Fin15AnchoredAtom2983 chi ∧
      ¬Fin15AnchoredAtom2984 chi ∧
      ¬Fin15AnchoredAtom2985 chi ∧
      ¬Fin15AnchoredAtom3035 chi ∧
      ¬Fin15AnchoredAtom3036 chi ∧
      ¬Fin15AnchoredAtom3037 chi ∧
      ¬Fin15AnchoredAtom3041 chi ∧
      ¬Fin15AnchoredAtom3460 chi ∧
      ¬Fin15AnchoredAtom3461 chi ∧
      ¬Fin15AnchoredAtom3462 chi ∧
      ¬Fin15AnchoredAtom3466 chi ∧
      ¬Fin15AnchoredAtom3535 chi ∧
      ¬Fin15AnchoredAtom3955 chi ∧
      ¬Fin15AnchoredAtom3956 chi ∧
      ¬Fin15AnchoredAtom3957 chi ∧
      ¬Fin15AnchoredAtom3961 chi ∧
      ¬Fin15AnchoredAtom4030 chi ∧
      ¬Fin15AnchoredAtom4766 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 6, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29767
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1854 Fin15AnchoredAtom1856 Fin15AnchoredAtom1857
    Fin15AnchoredAtom1858 Fin15AnchoredAtom1878 Fin15AnchoredAtom1879 Fin15AnchoredAtom1880
    Fin15AnchoredAtom1884 Fin15AnchoredAtom1885 Fin15AnchoredAtom1886 Fin15AnchoredAtom2042
    Fin15AnchoredAtom2043 Fin15AnchoredAtom2044 Fin15AnchoredAtom2048 Fin15AnchoredAtom2049
    Fin15AnchoredAtom2050 Fin15AnchoredAtom2100 Fin15AnchoredAtom2101 Fin15AnchoredAtom2102
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2262 Fin15AnchoredAtom2263 Fin15AnchoredAtom2264
    Fin15AnchoredAtom2268 Fin15AnchoredAtom2269 Fin15AnchoredAtom2270 Fin15AnchoredAtom2320
    Fin15AnchoredAtom2321 Fin15AnchoredAtom2322 Fin15AnchoredAtom2326 Fin15AnchoredAtom2745
    Fin15AnchoredAtom2746 Fin15AnchoredAtom2747 Fin15AnchoredAtom2751 Fin15AnchoredAtom2820
    Fin15AnchoredAtom2977 Fin15AnchoredAtom2978 Fin15AnchoredAtom2979 Fin15AnchoredAtom2983
    Fin15AnchoredAtom2984 Fin15AnchoredAtom2985 Fin15AnchoredAtom3035 Fin15AnchoredAtom3036
    Fin15AnchoredAtom3037 Fin15AnchoredAtom3041 Fin15AnchoredAtom3460 Fin15AnchoredAtom3461
    Fin15AnchoredAtom3462 Fin15AnchoredAtom3466 Fin15AnchoredAtom3535 Fin15AnchoredAtom3955
    Fin15AnchoredAtom3956 Fin15AnchoredAtom3957 Fin15AnchoredAtom3961 Fin15AnchoredAtom4030
    Fin15AnchoredAtom4766 at hbad
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

theorem fin15Anchored_clause30757 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom2057 chi ∧
      ¬Fin15AnchoredAtom2059 chi ∧
      ¬Fin15AnchoredAtom2060 chi ∧
      ¬Fin15AnchoredAtom2063 chi ∧
      ¬Fin15AnchoredAtom2064 chi ∧
      ¬Fin15AnchoredAtom2069 chi ∧
      ¬Fin15AnchoredAtom2088 chi ∧
      ¬Fin15AnchoredAtom2089 chi ∧
      ¬Fin15AnchoredAtom2094 chi ∧
      ¬Fin15AnchoredAtom2100 chi ∧
      ¬Fin15AnchoredAtom2277 chi ∧
      ¬Fin15AnchoredAtom2279 chi ∧
      ¬Fin15AnchoredAtom2280 chi ∧
      ¬Fin15AnchoredAtom2283 chi ∧
      ¬Fin15AnchoredAtom2284 chi ∧
      ¬Fin15AnchoredAtom2289 chi ∧
      ¬Fin15AnchoredAtom2308 chi ∧
      ¬Fin15AnchoredAtom2309 chi ∧
      ¬Fin15AnchoredAtom2314 chi ∧
      ¬Fin15AnchoredAtom2320 chi ∧
      ¬Fin15AnchoredAtom2768 chi ∧
      ¬Fin15AnchoredAtom2769 chi ∧
      ¬Fin15AnchoredAtom2774 chi ∧
      ¬Fin15AnchoredAtom2780 chi ∧
      ¬Fin15AnchoredAtom2810 chi ∧
      ¬Fin15AnchoredAtom2992 chi ∧
      ¬Fin15AnchoredAtom2994 chi ∧
      ¬Fin15AnchoredAtom2995 chi ∧
      ¬Fin15AnchoredAtom2998 chi ∧
      ¬Fin15AnchoredAtom2999 chi ∧
      ¬Fin15AnchoredAtom3004 chi ∧
      ¬Fin15AnchoredAtom3023 chi ∧
      ¬Fin15AnchoredAtom3024 chi ∧
      ¬Fin15AnchoredAtom3029 chi ∧
      ¬Fin15AnchoredAtom3035 chi ∧
      ¬Fin15AnchoredAtom3483 chi ∧
      ¬Fin15AnchoredAtom3484 chi ∧
      ¬Fin15AnchoredAtom3489 chi ∧
      ¬Fin15AnchoredAtom3495 chi ∧
      ¬Fin15AnchoredAtom3525 chi ∧
      ¬Fin15AnchoredAtom3978 chi ∧
      ¬Fin15AnchoredAtom3979 chi ∧
      ¬Fin15AnchoredAtom3984 chi ∧
      ¬Fin15AnchoredAtom3990 chi ∧
      ¬Fin15AnchoredAtom4020 chi ∧
      ¬Fin15AnchoredAtom4791 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 7, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13959
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1860 Fin15AnchoredAtom1861 Fin15AnchoredAtom1863
    Fin15AnchoredAtom1864 Fin15AnchoredAtom1872 Fin15AnchoredAtom1874 Fin15AnchoredAtom1875
    Fin15AnchoredAtom1878 Fin15AnchoredAtom1879 Fin15AnchoredAtom1884 Fin15AnchoredAtom2057
    Fin15AnchoredAtom2059 Fin15AnchoredAtom2060 Fin15AnchoredAtom2063 Fin15AnchoredAtom2064
    Fin15AnchoredAtom2069 Fin15AnchoredAtom2088 Fin15AnchoredAtom2089 Fin15AnchoredAtom2094
    Fin15AnchoredAtom2100 Fin15AnchoredAtom2277 Fin15AnchoredAtom2279 Fin15AnchoredAtom2280
    Fin15AnchoredAtom2283 Fin15AnchoredAtom2284 Fin15AnchoredAtom2289 Fin15AnchoredAtom2308
    Fin15AnchoredAtom2309 Fin15AnchoredAtom2314 Fin15AnchoredAtom2320 Fin15AnchoredAtom2768
    Fin15AnchoredAtom2769 Fin15AnchoredAtom2774 Fin15AnchoredAtom2780 Fin15AnchoredAtom2810
    Fin15AnchoredAtom2992 Fin15AnchoredAtom2994 Fin15AnchoredAtom2995 Fin15AnchoredAtom2998
    Fin15AnchoredAtom2999 Fin15AnchoredAtom3004 Fin15AnchoredAtom3023 Fin15AnchoredAtom3024
    Fin15AnchoredAtom3029 Fin15AnchoredAtom3035 Fin15AnchoredAtom3483 Fin15AnchoredAtom3484
    Fin15AnchoredAtom3489 Fin15AnchoredAtom3495 Fin15AnchoredAtom3525 Fin15AnchoredAtom3978
    Fin15AnchoredAtom3979 Fin15AnchoredAtom3984 Fin15AnchoredAtom3990 Fin15AnchoredAtom4020
    Fin15AnchoredAtom4791 at hbad
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

theorem fin15Anchored_clause30758 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom1885 chi ∧
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
      ¬Fin15AnchoredAtom2277 chi ∧
      ¬Fin15AnchoredAtom2279 chi ∧
      ¬Fin15AnchoredAtom2281 chi ∧
      ¬Fin15AnchoredAtom2283 chi ∧
      ¬Fin15AnchoredAtom2285 chi ∧
      ¬Fin15AnchoredAtom2290 chi ∧
      ¬Fin15AnchoredAtom2308 chi ∧
      ¬Fin15AnchoredAtom2310 chi ∧
      ¬Fin15AnchoredAtom2315 chi ∧
      ¬Fin15AnchoredAtom2321 chi ∧
      ¬Fin15AnchoredAtom2768 chi ∧
      ¬Fin15AnchoredAtom2770 chi ∧
      ¬Fin15AnchoredAtom2775 chi ∧
      ¬Fin15AnchoredAtom2781 chi ∧
      ¬Fin15AnchoredAtom2811 chi ∧
      ¬Fin15AnchoredAtom2992 chi ∧
      ¬Fin15AnchoredAtom2994 chi ∧
      ¬Fin15AnchoredAtom2996 chi ∧
      ¬Fin15AnchoredAtom2998 chi ∧
      ¬Fin15AnchoredAtom3000 chi ∧
      ¬Fin15AnchoredAtom3005 chi ∧
      ¬Fin15AnchoredAtom3023 chi ∧
      ¬Fin15AnchoredAtom3025 chi ∧
      ¬Fin15AnchoredAtom3030 chi ∧
      ¬Fin15AnchoredAtom3036 chi ∧
      ¬Fin15AnchoredAtom3483 chi ∧
      ¬Fin15AnchoredAtom3485 chi ∧
      ¬Fin15AnchoredAtom3490 chi ∧
      ¬Fin15AnchoredAtom3496 chi ∧
      ¬Fin15AnchoredAtom3526 chi ∧
      ¬Fin15AnchoredAtom3978 chi ∧
      ¬Fin15AnchoredAtom3980 chi ∧
      ¬Fin15AnchoredAtom3985 chi ∧
      ¬Fin15AnchoredAtom3991 chi ∧
      ¬Fin15AnchoredAtom4021 chi ∧
      ¬Fin15AnchoredAtom4792 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 7, 9, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22151
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1860 Fin15AnchoredAtom1861 Fin15AnchoredAtom1863
    Fin15AnchoredAtom1865 Fin15AnchoredAtom1872 Fin15AnchoredAtom1874 Fin15AnchoredAtom1876
    Fin15AnchoredAtom1878 Fin15AnchoredAtom1880 Fin15AnchoredAtom1885 Fin15AnchoredAtom2057
    Fin15AnchoredAtom2059 Fin15AnchoredAtom2061 Fin15AnchoredAtom2063 Fin15AnchoredAtom2065
    Fin15AnchoredAtom2070 Fin15AnchoredAtom2088 Fin15AnchoredAtom2090 Fin15AnchoredAtom2095
    Fin15AnchoredAtom2101 Fin15AnchoredAtom2277 Fin15AnchoredAtom2279 Fin15AnchoredAtom2281
    Fin15AnchoredAtom2283 Fin15AnchoredAtom2285 Fin15AnchoredAtom2290 Fin15AnchoredAtom2308
    Fin15AnchoredAtom2310 Fin15AnchoredAtom2315 Fin15AnchoredAtom2321 Fin15AnchoredAtom2768
    Fin15AnchoredAtom2770 Fin15AnchoredAtom2775 Fin15AnchoredAtom2781 Fin15AnchoredAtom2811
    Fin15AnchoredAtom2992 Fin15AnchoredAtom2994 Fin15AnchoredAtom2996 Fin15AnchoredAtom2998
    Fin15AnchoredAtom3000 Fin15AnchoredAtom3005 Fin15AnchoredAtom3023 Fin15AnchoredAtom3025
    Fin15AnchoredAtom3030 Fin15AnchoredAtom3036 Fin15AnchoredAtom3483 Fin15AnchoredAtom3485
    Fin15AnchoredAtom3490 Fin15AnchoredAtom3496 Fin15AnchoredAtom3526 Fin15AnchoredAtom3978
    Fin15AnchoredAtom3980 Fin15AnchoredAtom3985 Fin15AnchoredAtom3991 Fin15AnchoredAtom4021
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

theorem fin15Anchored_clause30759 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom1886 chi ∧
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
      ¬Fin15AnchoredAtom2277 chi ∧
      ¬Fin15AnchoredAtom2280 chi ∧
      ¬Fin15AnchoredAtom2281 chi ∧
      ¬Fin15AnchoredAtom2284 chi ∧
      ¬Fin15AnchoredAtom2285 chi ∧
      ¬Fin15AnchoredAtom2291 chi ∧
      ¬Fin15AnchoredAtom2309 chi ∧
      ¬Fin15AnchoredAtom2310 chi ∧
      ¬Fin15AnchoredAtom2316 chi ∧
      ¬Fin15AnchoredAtom2322 chi ∧
      ¬Fin15AnchoredAtom2769 chi ∧
      ¬Fin15AnchoredAtom2770 chi ∧
      ¬Fin15AnchoredAtom2776 chi ∧
      ¬Fin15AnchoredAtom2782 chi ∧
      ¬Fin15AnchoredAtom2812 chi ∧
      ¬Fin15AnchoredAtom2992 chi ∧
      ¬Fin15AnchoredAtom2995 chi ∧
      ¬Fin15AnchoredAtom2996 chi ∧
      ¬Fin15AnchoredAtom2999 chi ∧
      ¬Fin15AnchoredAtom3000 chi ∧
      ¬Fin15AnchoredAtom3006 chi ∧
      ¬Fin15AnchoredAtom3024 chi ∧
      ¬Fin15AnchoredAtom3025 chi ∧
      ¬Fin15AnchoredAtom3031 chi ∧
      ¬Fin15AnchoredAtom3037 chi ∧
      ¬Fin15AnchoredAtom3484 chi ∧
      ¬Fin15AnchoredAtom3485 chi ∧
      ¬Fin15AnchoredAtom3491 chi ∧
      ¬Fin15AnchoredAtom3497 chi ∧
      ¬Fin15AnchoredAtom3527 chi ∧
      ¬Fin15AnchoredAtom3979 chi ∧
      ¬Fin15AnchoredAtom3980 chi ∧
      ¬Fin15AnchoredAtom3986 chi ∧
      ¬Fin15AnchoredAtom3992 chi ∧
      ¬Fin15AnchoredAtom4022 chi ∧
      ¬Fin15AnchoredAtom4793 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 7, 9, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26247
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1860 Fin15AnchoredAtom1861 Fin15AnchoredAtom1864
    Fin15AnchoredAtom1865 Fin15AnchoredAtom1872 Fin15AnchoredAtom1875 Fin15AnchoredAtom1876
    Fin15AnchoredAtom1879 Fin15AnchoredAtom1880 Fin15AnchoredAtom1886 Fin15AnchoredAtom2057
    Fin15AnchoredAtom2060 Fin15AnchoredAtom2061 Fin15AnchoredAtom2064 Fin15AnchoredAtom2065
    Fin15AnchoredAtom2071 Fin15AnchoredAtom2089 Fin15AnchoredAtom2090 Fin15AnchoredAtom2096
    Fin15AnchoredAtom2102 Fin15AnchoredAtom2277 Fin15AnchoredAtom2280 Fin15AnchoredAtom2281
    Fin15AnchoredAtom2284 Fin15AnchoredAtom2285 Fin15AnchoredAtom2291 Fin15AnchoredAtom2309
    Fin15AnchoredAtom2310 Fin15AnchoredAtom2316 Fin15AnchoredAtom2322 Fin15AnchoredAtom2769
    Fin15AnchoredAtom2770 Fin15AnchoredAtom2776 Fin15AnchoredAtom2782 Fin15AnchoredAtom2812
    Fin15AnchoredAtom2992 Fin15AnchoredAtom2995 Fin15AnchoredAtom2996 Fin15AnchoredAtom2999
    Fin15AnchoredAtom3000 Fin15AnchoredAtom3006 Fin15AnchoredAtom3024 Fin15AnchoredAtom3025
    Fin15AnchoredAtom3031 Fin15AnchoredAtom3037 Fin15AnchoredAtom3484 Fin15AnchoredAtom3485
    Fin15AnchoredAtom3491 Fin15AnchoredAtom3497 Fin15AnchoredAtom3527 Fin15AnchoredAtom3979
    Fin15AnchoredAtom3980 Fin15AnchoredAtom3986 Fin15AnchoredAtom3992 Fin15AnchoredAtom4022
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

theorem fin15Anchored_clause30760 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom1886 chi ∧
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
      ¬Fin15AnchoredAtom2279 chi ∧
      ¬Fin15AnchoredAtom2280 chi ∧
      ¬Fin15AnchoredAtom2281 chi ∧
      ¬Fin15AnchoredAtom2289 chi ∧
      ¬Fin15AnchoredAtom2290 chi ∧
      ¬Fin15AnchoredAtom2291 chi ∧
      ¬Fin15AnchoredAtom2314 chi ∧
      ¬Fin15AnchoredAtom2315 chi ∧
      ¬Fin15AnchoredAtom2316 chi ∧
      ¬Fin15AnchoredAtom2326 chi ∧
      ¬Fin15AnchoredAtom2774 chi ∧
      ¬Fin15AnchoredAtom2775 chi ∧
      ¬Fin15AnchoredAtom2776 chi ∧
      ¬Fin15AnchoredAtom2786 chi ∧
      ¬Fin15AnchoredAtom2816 chi ∧
      ¬Fin15AnchoredAtom2994 chi ∧
      ¬Fin15AnchoredAtom2995 chi ∧
      ¬Fin15AnchoredAtom2996 chi ∧
      ¬Fin15AnchoredAtom3004 chi ∧
      ¬Fin15AnchoredAtom3005 chi ∧
      ¬Fin15AnchoredAtom3006 chi ∧
      ¬Fin15AnchoredAtom3029 chi ∧
      ¬Fin15AnchoredAtom3030 chi ∧
      ¬Fin15AnchoredAtom3031 chi ∧
      ¬Fin15AnchoredAtom3041 chi ∧
      ¬Fin15AnchoredAtom3489 chi ∧
      ¬Fin15AnchoredAtom3490 chi ∧
      ¬Fin15AnchoredAtom3491 chi ∧
      ¬Fin15AnchoredAtom3501 chi ∧
      ¬Fin15AnchoredAtom3531 chi ∧
      ¬Fin15AnchoredAtom3984 chi ∧
      ¬Fin15AnchoredAtom3985 chi ∧
      ¬Fin15AnchoredAtom3986 chi ∧
      ¬Fin15AnchoredAtom3996 chi ∧
      ¬Fin15AnchoredAtom4026 chi ∧
      ¬Fin15AnchoredAtom4797 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 7, 9, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29319
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1860 Fin15AnchoredAtom1863 Fin15AnchoredAtom1864
    Fin15AnchoredAtom1865 Fin15AnchoredAtom1874 Fin15AnchoredAtom1875 Fin15AnchoredAtom1876
    Fin15AnchoredAtom1884 Fin15AnchoredAtom1885 Fin15AnchoredAtom1886 Fin15AnchoredAtom2059
    Fin15AnchoredAtom2060 Fin15AnchoredAtom2061 Fin15AnchoredAtom2069 Fin15AnchoredAtom2070
    Fin15AnchoredAtom2071 Fin15AnchoredAtom2094 Fin15AnchoredAtom2095 Fin15AnchoredAtom2096
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2279 Fin15AnchoredAtom2280 Fin15AnchoredAtom2281
    Fin15AnchoredAtom2289 Fin15AnchoredAtom2290 Fin15AnchoredAtom2291 Fin15AnchoredAtom2314
    Fin15AnchoredAtom2315 Fin15AnchoredAtom2316 Fin15AnchoredAtom2326 Fin15AnchoredAtom2774
    Fin15AnchoredAtom2775 Fin15AnchoredAtom2776 Fin15AnchoredAtom2786 Fin15AnchoredAtom2816
    Fin15AnchoredAtom2994 Fin15AnchoredAtom2995 Fin15AnchoredAtom2996 Fin15AnchoredAtom3004
    Fin15AnchoredAtom3005 Fin15AnchoredAtom3006 Fin15AnchoredAtom3029 Fin15AnchoredAtom3030
    Fin15AnchoredAtom3031 Fin15AnchoredAtom3041 Fin15AnchoredAtom3489 Fin15AnchoredAtom3490
    Fin15AnchoredAtom3491 Fin15AnchoredAtom3501 Fin15AnchoredAtom3531 Fin15AnchoredAtom3984
    Fin15AnchoredAtom3985 Fin15AnchoredAtom3986 Fin15AnchoredAtom3996 Fin15AnchoredAtom4026
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

theorem fin15Anchored_clause30761 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom1886 chi ∧
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
      ¬Fin15AnchoredAtom2283 chi ∧
      ¬Fin15AnchoredAtom2284 chi ∧
      ¬Fin15AnchoredAtom2285 chi ∧
      ¬Fin15AnchoredAtom2289 chi ∧
      ¬Fin15AnchoredAtom2290 chi ∧
      ¬Fin15AnchoredAtom2291 chi ∧
      ¬Fin15AnchoredAtom2320 chi ∧
      ¬Fin15AnchoredAtom2321 chi ∧
      ¬Fin15AnchoredAtom2322 chi ∧
      ¬Fin15AnchoredAtom2326 chi ∧
      ¬Fin15AnchoredAtom2780 chi ∧
      ¬Fin15AnchoredAtom2781 chi ∧
      ¬Fin15AnchoredAtom2782 chi ∧
      ¬Fin15AnchoredAtom2786 chi ∧
      ¬Fin15AnchoredAtom2820 chi ∧
      ¬Fin15AnchoredAtom2998 chi ∧
      ¬Fin15AnchoredAtom2999 chi ∧
      ¬Fin15AnchoredAtom3000 chi ∧
      ¬Fin15AnchoredAtom3004 chi ∧
      ¬Fin15AnchoredAtom3005 chi ∧
      ¬Fin15AnchoredAtom3006 chi ∧
      ¬Fin15AnchoredAtom3035 chi ∧
      ¬Fin15AnchoredAtom3036 chi ∧
      ¬Fin15AnchoredAtom3037 chi ∧
      ¬Fin15AnchoredAtom3041 chi ∧
      ¬Fin15AnchoredAtom3495 chi ∧
      ¬Fin15AnchoredAtom3496 chi ∧
      ¬Fin15AnchoredAtom3497 chi ∧
      ¬Fin15AnchoredAtom3501 chi ∧
      ¬Fin15AnchoredAtom3535 chi ∧
      ¬Fin15AnchoredAtom3990 chi ∧
      ¬Fin15AnchoredAtom3991 chi ∧
      ¬Fin15AnchoredAtom3992 chi ∧
      ¬Fin15AnchoredAtom3996 chi ∧
      ¬Fin15AnchoredAtom4030 chi ∧
      ¬Fin15AnchoredAtom4801 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 7, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29831
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1861 Fin15AnchoredAtom1863 Fin15AnchoredAtom1864
    Fin15AnchoredAtom1865 Fin15AnchoredAtom1878 Fin15AnchoredAtom1879 Fin15AnchoredAtom1880
    Fin15AnchoredAtom1884 Fin15AnchoredAtom1885 Fin15AnchoredAtom1886 Fin15AnchoredAtom2063
    Fin15AnchoredAtom2064 Fin15AnchoredAtom2065 Fin15AnchoredAtom2069 Fin15AnchoredAtom2070
    Fin15AnchoredAtom2071 Fin15AnchoredAtom2100 Fin15AnchoredAtom2101 Fin15AnchoredAtom2102
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2283 Fin15AnchoredAtom2284 Fin15AnchoredAtom2285
    Fin15AnchoredAtom2289 Fin15AnchoredAtom2290 Fin15AnchoredAtom2291 Fin15AnchoredAtom2320
    Fin15AnchoredAtom2321 Fin15AnchoredAtom2322 Fin15AnchoredAtom2326 Fin15AnchoredAtom2780
    Fin15AnchoredAtom2781 Fin15AnchoredAtom2782 Fin15AnchoredAtom2786 Fin15AnchoredAtom2820
    Fin15AnchoredAtom2998 Fin15AnchoredAtom2999 Fin15AnchoredAtom3000 Fin15AnchoredAtom3004
    Fin15AnchoredAtom3005 Fin15AnchoredAtom3006 Fin15AnchoredAtom3035 Fin15AnchoredAtom3036
    Fin15AnchoredAtom3037 Fin15AnchoredAtom3041 Fin15AnchoredAtom3495 Fin15AnchoredAtom3496
    Fin15AnchoredAtom3497 Fin15AnchoredAtom3501 Fin15AnchoredAtom3535 Fin15AnchoredAtom3990
    Fin15AnchoredAtom3991 Fin15AnchoredAtom3992 Fin15AnchoredAtom3996 Fin15AnchoredAtom4030
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

theorem fin15Anchored_clause30762 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom1886 chi ∧
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
      ¬Fin15AnchoredAtom2308 chi ∧
      ¬Fin15AnchoredAtom2309 chi ∧
      ¬Fin15AnchoredAtom2310 chi ∧
      ¬Fin15AnchoredAtom2314 chi ∧
      ¬Fin15AnchoredAtom2315 chi ∧
      ¬Fin15AnchoredAtom2316 chi ∧
      ¬Fin15AnchoredAtom2320 chi ∧
      ¬Fin15AnchoredAtom2321 chi ∧
      ¬Fin15AnchoredAtom2322 chi ∧
      ¬Fin15AnchoredAtom2326 chi ∧
      ¬Fin15AnchoredAtom2810 chi ∧
      ¬Fin15AnchoredAtom2811 chi ∧
      ¬Fin15AnchoredAtom2812 chi ∧
      ¬Fin15AnchoredAtom2816 chi ∧
      ¬Fin15AnchoredAtom2820 chi ∧
      ¬Fin15AnchoredAtom3023 chi ∧
      ¬Fin15AnchoredAtom3024 chi ∧
      ¬Fin15AnchoredAtom3025 chi ∧
      ¬Fin15AnchoredAtom3029 chi ∧
      ¬Fin15AnchoredAtom3030 chi ∧
      ¬Fin15AnchoredAtom3031 chi ∧
      ¬Fin15AnchoredAtom3035 chi ∧
      ¬Fin15AnchoredAtom3036 chi ∧
      ¬Fin15AnchoredAtom3037 chi ∧
      ¬Fin15AnchoredAtom3041 chi ∧
      ¬Fin15AnchoredAtom3525 chi ∧
      ¬Fin15AnchoredAtom3526 chi ∧
      ¬Fin15AnchoredAtom3527 chi ∧
      ¬Fin15AnchoredAtom3531 chi ∧
      ¬Fin15AnchoredAtom3535 chi ∧
      ¬Fin15AnchoredAtom4020 chi ∧
      ¬Fin15AnchoredAtom4021 chi ∧
      ¬Fin15AnchoredAtom4022 chi ∧
      ¬Fin15AnchoredAtom4026 chi ∧
      ¬Fin15AnchoredAtom4030 chi ∧
      ¬Fin15AnchoredAtom4821 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 9, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask30215
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1872 Fin15AnchoredAtom1874 Fin15AnchoredAtom1875
    Fin15AnchoredAtom1876 Fin15AnchoredAtom1878 Fin15AnchoredAtom1879 Fin15AnchoredAtom1880
    Fin15AnchoredAtom1884 Fin15AnchoredAtom1885 Fin15AnchoredAtom1886 Fin15AnchoredAtom2088
    Fin15AnchoredAtom2089 Fin15AnchoredAtom2090 Fin15AnchoredAtom2094 Fin15AnchoredAtom2095
    Fin15AnchoredAtom2096 Fin15AnchoredAtom2100 Fin15AnchoredAtom2101 Fin15AnchoredAtom2102
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2308 Fin15AnchoredAtom2309 Fin15AnchoredAtom2310
    Fin15AnchoredAtom2314 Fin15AnchoredAtom2315 Fin15AnchoredAtom2316 Fin15AnchoredAtom2320
    Fin15AnchoredAtom2321 Fin15AnchoredAtom2322 Fin15AnchoredAtom2326 Fin15AnchoredAtom2810
    Fin15AnchoredAtom2811 Fin15AnchoredAtom2812 Fin15AnchoredAtom2816 Fin15AnchoredAtom2820
    Fin15AnchoredAtom3023 Fin15AnchoredAtom3024 Fin15AnchoredAtom3025 Fin15AnchoredAtom3029
    Fin15AnchoredAtom3030 Fin15AnchoredAtom3031 Fin15AnchoredAtom3035 Fin15AnchoredAtom3036
    Fin15AnchoredAtom3037 Fin15AnchoredAtom3041 Fin15AnchoredAtom3525 Fin15AnchoredAtom3526
    Fin15AnchoredAtom3527 Fin15AnchoredAtom3531 Fin15AnchoredAtom3535 Fin15AnchoredAtom4020
    Fin15AnchoredAtom4021 Fin15AnchoredAtom4022 Fin15AnchoredAtom4026 Fin15AnchoredAtom4030
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

theorem fin15Anchored_clause30763 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
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
      ¬Fin15AnchoredAtom3042 chi ∧
      ¬Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom3051 chi ∧
      ¬Fin15AnchoredAtom3053 chi ∧
      ¬Fin15AnchoredAtom3060 chi ∧
      ¬Fin15AnchoredAtom3087 chi ∧
      ¬Fin15AnchoredAtom3089 chi ∧
      ¬Fin15AnchoredAtom3096 chi ∧
      ¬Fin15AnchoredAtom3124 chi ∧
      ¬Fin15AnchoredAtom3207 chi ∧
      ¬Fin15AnchoredAtom3209 chi ∧
      ¬Fin15AnchoredAtom3216 chi ∧
      ¬Fin15AnchoredAtom3244 chi ∧
      ¬Fin15AnchoredAtom3328 chi ∧
      ¬Fin15AnchoredAtom4032 chi ∧
      ¬Fin15AnchoredAtom4034 chi ∧
      ¬Fin15AnchoredAtom4041 chi ∧
      ¬Fin15AnchoredAtom4069 chi ∧
      ¬Fin15AnchoredAtom4153 chi ∧
      ¬Fin15AnchoredAtom4363 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 5, 6, 7, 9}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask00763
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1887 Fin15AnchoredAtom1888 Fin15AnchoredAtom1889
    Fin15AnchoredAtom1891 Fin15AnchoredAtom1897 Fin15AnchoredAtom1898 Fin15AnchoredAtom1900
    Fin15AnchoredAtom1906 Fin15AnchoredAtom1908 Fin15AnchoredAtom1915 Fin15AnchoredAtom1942
    Fin15AnchoredAtom1943 Fin15AnchoredAtom1945 Fin15AnchoredAtom1951 Fin15AnchoredAtom1953
    Fin15AnchoredAtom1960 Fin15AnchoredAtom1987 Fin15AnchoredAtom1989 Fin15AnchoredAtom1996
    Fin15AnchoredAtom2024 Fin15AnchoredAtom2327 Fin15AnchoredAtom2328 Fin15AnchoredAtom2330
    Fin15AnchoredAtom2336 Fin15AnchoredAtom2338 Fin15AnchoredAtom2345 Fin15AnchoredAtom2372
    Fin15AnchoredAtom2374 Fin15AnchoredAtom2381 Fin15AnchoredAtom2409 Fin15AnchoredAtom2492
    Fin15AnchoredAtom2494 Fin15AnchoredAtom2501 Fin15AnchoredAtom2529 Fin15AnchoredAtom2613
    Fin15AnchoredAtom3042 Fin15AnchoredAtom3043 Fin15AnchoredAtom3045 Fin15AnchoredAtom3051
    Fin15AnchoredAtom3053 Fin15AnchoredAtom3060 Fin15AnchoredAtom3087 Fin15AnchoredAtom3089
    Fin15AnchoredAtom3096 Fin15AnchoredAtom3124 Fin15AnchoredAtom3207 Fin15AnchoredAtom3209
    Fin15AnchoredAtom3216 Fin15AnchoredAtom3244 Fin15AnchoredAtom3328 Fin15AnchoredAtom4032
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

theorem fin15Anchored_clause30764 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
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
      ¬Fin15AnchoredAtom3042 chi ∧
      ¬Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom3051 chi ∧
      ¬Fin15AnchoredAtom3054 chi ∧
      ¬Fin15AnchoredAtom3061 chi ∧
      ¬Fin15AnchoredAtom3087 chi ∧
      ¬Fin15AnchoredAtom3090 chi ∧
      ¬Fin15AnchoredAtom3097 chi ∧
      ¬Fin15AnchoredAtom3125 chi ∧
      ¬Fin15AnchoredAtom3207 chi ∧
      ¬Fin15AnchoredAtom3210 chi ∧
      ¬Fin15AnchoredAtom3217 chi ∧
      ¬Fin15AnchoredAtom3245 chi ∧
      ¬Fin15AnchoredAtom3329 chi ∧
      ¬Fin15AnchoredAtom4032 chi ∧
      ¬Fin15AnchoredAtom4035 chi ∧
      ¬Fin15AnchoredAtom4042 chi ∧
      ¬Fin15AnchoredAtom4070 chi ∧
      ¬Fin15AnchoredAtom4154 chi ∧
      ¬Fin15AnchoredAtom4364 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 5, 6, 7, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask01275
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1887 Fin15AnchoredAtom1888 Fin15AnchoredAtom1889
    Fin15AnchoredAtom1892 Fin15AnchoredAtom1897 Fin15AnchoredAtom1898 Fin15AnchoredAtom1901
    Fin15AnchoredAtom1906 Fin15AnchoredAtom1909 Fin15AnchoredAtom1916 Fin15AnchoredAtom1942
    Fin15AnchoredAtom1943 Fin15AnchoredAtom1946 Fin15AnchoredAtom1951 Fin15AnchoredAtom1954
    Fin15AnchoredAtom1961 Fin15AnchoredAtom1987 Fin15AnchoredAtom1990 Fin15AnchoredAtom1997
    Fin15AnchoredAtom2025 Fin15AnchoredAtom2327 Fin15AnchoredAtom2328 Fin15AnchoredAtom2331
    Fin15AnchoredAtom2336 Fin15AnchoredAtom2339 Fin15AnchoredAtom2346 Fin15AnchoredAtom2372
    Fin15AnchoredAtom2375 Fin15AnchoredAtom2382 Fin15AnchoredAtom2410 Fin15AnchoredAtom2492
    Fin15AnchoredAtom2495 Fin15AnchoredAtom2502 Fin15AnchoredAtom2530 Fin15AnchoredAtom2614
    Fin15AnchoredAtom3042 Fin15AnchoredAtom3043 Fin15AnchoredAtom3046 Fin15AnchoredAtom3051
    Fin15AnchoredAtom3054 Fin15AnchoredAtom3061 Fin15AnchoredAtom3087 Fin15AnchoredAtom3090
    Fin15AnchoredAtom3097 Fin15AnchoredAtom3125 Fin15AnchoredAtom3207 Fin15AnchoredAtom3210
    Fin15AnchoredAtom3217 Fin15AnchoredAtom3245 Fin15AnchoredAtom3329 Fin15AnchoredAtom4032
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

theorem fin15Anchored_clause30765 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
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
      ¬Fin15AnchoredAtom3042 chi ∧
      ¬Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom3048 chi ∧
      ¬Fin15AnchoredAtom3051 chi ∧
      ¬Fin15AnchoredAtom3056 chi ∧
      ¬Fin15AnchoredAtom3063 chi ∧
      ¬Fin15AnchoredAtom3087 chi ∧
      ¬Fin15AnchoredAtom3092 chi ∧
      ¬Fin15AnchoredAtom3099 chi ∧
      ¬Fin15AnchoredAtom3127 chi ∧
      ¬Fin15AnchoredAtom3207 chi ∧
      ¬Fin15AnchoredAtom3212 chi ∧
      ¬Fin15AnchoredAtom3219 chi ∧
      ¬Fin15AnchoredAtom3247 chi ∧
      ¬Fin15AnchoredAtom3331 chi ∧
      ¬Fin15AnchoredAtom4032 chi ∧
      ¬Fin15AnchoredAtom4037 chi ∧
      ¬Fin15AnchoredAtom4044 chi ∧
      ¬Fin15AnchoredAtom4072 chi ∧
      ¬Fin15AnchoredAtom4156 chi ∧
      ¬Fin15AnchoredAtom4366 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 5, 6, 7, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask04347
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1887 Fin15AnchoredAtom1888 Fin15AnchoredAtom1889
    Fin15AnchoredAtom1894 Fin15AnchoredAtom1897 Fin15AnchoredAtom1898 Fin15AnchoredAtom1903
    Fin15AnchoredAtom1906 Fin15AnchoredAtom1911 Fin15AnchoredAtom1918 Fin15AnchoredAtom1942
    Fin15AnchoredAtom1943 Fin15AnchoredAtom1948 Fin15AnchoredAtom1951 Fin15AnchoredAtom1956
    Fin15AnchoredAtom1963 Fin15AnchoredAtom1987 Fin15AnchoredAtom1992 Fin15AnchoredAtom1999
    Fin15AnchoredAtom2027 Fin15AnchoredAtom2327 Fin15AnchoredAtom2328 Fin15AnchoredAtom2333
    Fin15AnchoredAtom2336 Fin15AnchoredAtom2341 Fin15AnchoredAtom2348 Fin15AnchoredAtom2372
    Fin15AnchoredAtom2377 Fin15AnchoredAtom2384 Fin15AnchoredAtom2412 Fin15AnchoredAtom2492
    Fin15AnchoredAtom2497 Fin15AnchoredAtom2504 Fin15AnchoredAtom2532 Fin15AnchoredAtom2616
    Fin15AnchoredAtom3042 Fin15AnchoredAtom3043 Fin15AnchoredAtom3048 Fin15AnchoredAtom3051
    Fin15AnchoredAtom3056 Fin15AnchoredAtom3063 Fin15AnchoredAtom3087 Fin15AnchoredAtom3092
    Fin15AnchoredAtom3099 Fin15AnchoredAtom3127 Fin15AnchoredAtom3207 Fin15AnchoredAtom3212
    Fin15AnchoredAtom3219 Fin15AnchoredAtom3247 Fin15AnchoredAtom3331 Fin15AnchoredAtom4032
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

theorem fin15Anchored_clause30766 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
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
      ¬Fin15AnchoredAtom3042 chi ∧
      ¬Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom3051 chi ∧
      ¬Fin15AnchoredAtom3057 chi ∧
      ¬Fin15AnchoredAtom3064 chi ∧
      ¬Fin15AnchoredAtom3087 chi ∧
      ¬Fin15AnchoredAtom3093 chi ∧
      ¬Fin15AnchoredAtom3100 chi ∧
      ¬Fin15AnchoredAtom3128 chi ∧
      ¬Fin15AnchoredAtom3207 chi ∧
      ¬Fin15AnchoredAtom3213 chi ∧
      ¬Fin15AnchoredAtom3220 chi ∧
      ¬Fin15AnchoredAtom3248 chi ∧
      ¬Fin15AnchoredAtom3332 chi ∧
      ¬Fin15AnchoredAtom4032 chi ∧
      ¬Fin15AnchoredAtom4038 chi ∧
      ¬Fin15AnchoredAtom4045 chi ∧
      ¬Fin15AnchoredAtom4073 chi ∧
      ¬Fin15AnchoredAtom4157 chi ∧
      ¬Fin15AnchoredAtom4367 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 5, 6, 7, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask08443
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1887 Fin15AnchoredAtom1888 Fin15AnchoredAtom1889
    Fin15AnchoredAtom1895 Fin15AnchoredAtom1897 Fin15AnchoredAtom1898 Fin15AnchoredAtom1904
    Fin15AnchoredAtom1906 Fin15AnchoredAtom1912 Fin15AnchoredAtom1919 Fin15AnchoredAtom1942
    Fin15AnchoredAtom1943 Fin15AnchoredAtom1949 Fin15AnchoredAtom1951 Fin15AnchoredAtom1957
    Fin15AnchoredAtom1964 Fin15AnchoredAtom1987 Fin15AnchoredAtom1993 Fin15AnchoredAtom2000
    Fin15AnchoredAtom2028 Fin15AnchoredAtom2327 Fin15AnchoredAtom2328 Fin15AnchoredAtom2334
    Fin15AnchoredAtom2336 Fin15AnchoredAtom2342 Fin15AnchoredAtom2349 Fin15AnchoredAtom2372
    Fin15AnchoredAtom2378 Fin15AnchoredAtom2385 Fin15AnchoredAtom2413 Fin15AnchoredAtom2492
    Fin15AnchoredAtom2498 Fin15AnchoredAtom2505 Fin15AnchoredAtom2533 Fin15AnchoredAtom2617
    Fin15AnchoredAtom3042 Fin15AnchoredAtom3043 Fin15AnchoredAtom3049 Fin15AnchoredAtom3051
    Fin15AnchoredAtom3057 Fin15AnchoredAtom3064 Fin15AnchoredAtom3087 Fin15AnchoredAtom3093
    Fin15AnchoredAtom3100 Fin15AnchoredAtom3128 Fin15AnchoredAtom3207 Fin15AnchoredAtom3213
    Fin15AnchoredAtom3220 Fin15AnchoredAtom3248 Fin15AnchoredAtom3332 Fin15AnchoredAtom4032
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

theorem fin15Anchored_clause30767 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
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
      ¬Fin15AnchoredAtom3042 chi ∧
      ¬Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom3050 chi ∧
      ¬Fin15AnchoredAtom3051 chi ∧
      ¬Fin15AnchoredAtom3058 chi ∧
      ¬Fin15AnchoredAtom3065 chi ∧
      ¬Fin15AnchoredAtom3087 chi ∧
      ¬Fin15AnchoredAtom3094 chi ∧
      ¬Fin15AnchoredAtom3101 chi ∧
      ¬Fin15AnchoredAtom3129 chi ∧
      ¬Fin15AnchoredAtom3207 chi ∧
      ¬Fin15AnchoredAtom3214 chi ∧
      ¬Fin15AnchoredAtom3221 chi ∧
      ¬Fin15AnchoredAtom3249 chi ∧
      ¬Fin15AnchoredAtom3333 chi ∧
      ¬Fin15AnchoredAtom4032 chi ∧
      ¬Fin15AnchoredAtom4039 chi ∧
      ¬Fin15AnchoredAtom4046 chi ∧
      ¬Fin15AnchoredAtom4074 chi ∧
      ¬Fin15AnchoredAtom4158 chi ∧
      ¬Fin15AnchoredAtom4368 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 5, 6, 7, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask16635
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1887 Fin15AnchoredAtom1888 Fin15AnchoredAtom1889
    Fin15AnchoredAtom1896 Fin15AnchoredAtom1897 Fin15AnchoredAtom1898 Fin15AnchoredAtom1905
    Fin15AnchoredAtom1906 Fin15AnchoredAtom1913 Fin15AnchoredAtom1920 Fin15AnchoredAtom1942
    Fin15AnchoredAtom1943 Fin15AnchoredAtom1950 Fin15AnchoredAtom1951 Fin15AnchoredAtom1958
    Fin15AnchoredAtom1965 Fin15AnchoredAtom1987 Fin15AnchoredAtom1994 Fin15AnchoredAtom2001
    Fin15AnchoredAtom2029 Fin15AnchoredAtom2327 Fin15AnchoredAtom2328 Fin15AnchoredAtom2335
    Fin15AnchoredAtom2336 Fin15AnchoredAtom2343 Fin15AnchoredAtom2350 Fin15AnchoredAtom2372
    Fin15AnchoredAtom2379 Fin15AnchoredAtom2386 Fin15AnchoredAtom2414 Fin15AnchoredAtom2492
    Fin15AnchoredAtom2499 Fin15AnchoredAtom2506 Fin15AnchoredAtom2534 Fin15AnchoredAtom2618
    Fin15AnchoredAtom3042 Fin15AnchoredAtom3043 Fin15AnchoredAtom3050 Fin15AnchoredAtom3051
    Fin15AnchoredAtom3058 Fin15AnchoredAtom3065 Fin15AnchoredAtom3087 Fin15AnchoredAtom3094
    Fin15AnchoredAtom3101 Fin15AnchoredAtom3129 Fin15AnchoredAtom3207 Fin15AnchoredAtom3214
    Fin15AnchoredAtom3221 Fin15AnchoredAtom3249 Fin15AnchoredAtom3333 Fin15AnchoredAtom4032
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

theorem fin15Anchored_clause30768 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1890 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1899 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1907 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1922 chi ∧
      ¬Fin15AnchoredAtom1942 chi ∧
      ¬Fin15AnchoredAtom1944 chi ∧
      ¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1952 chi ∧
      ¬Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom1967 chi ∧
      ¬Fin15AnchoredAtom1988 chi ∧
      ¬Fin15AnchoredAtom1990 chi ∧
      ¬Fin15AnchoredAtom2003 chi ∧
      ¬Fin15AnchoredAtom2031 chi ∧
      ¬Fin15AnchoredAtom2327 chi ∧
      ¬Fin15AnchoredAtom2329 chi ∧
      ¬Fin15AnchoredAtom2331 chi ∧
      ¬Fin15AnchoredAtom2337 chi ∧
      ¬Fin15AnchoredAtom2339 chi ∧
      ¬Fin15AnchoredAtom2352 chi ∧
      ¬Fin15AnchoredAtom2373 chi ∧
      ¬Fin15AnchoredAtom2375 chi ∧
      ¬Fin15AnchoredAtom2388 chi ∧
      ¬Fin15AnchoredAtom2416 chi ∧
      ¬Fin15AnchoredAtom2493 chi ∧
      ¬Fin15AnchoredAtom2495 chi ∧
      ¬Fin15AnchoredAtom2508 chi ∧
      ¬Fin15AnchoredAtom2536 chi ∧
      ¬Fin15AnchoredAtom2620 chi ∧
      ¬Fin15AnchoredAtom3042 chi ∧
      ¬Fin15AnchoredAtom3044 chi ∧
      ¬Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom3052 chi ∧
      ¬Fin15AnchoredAtom3054 chi ∧
      ¬Fin15AnchoredAtom3067 chi ∧
      ¬Fin15AnchoredAtom3088 chi ∧
      ¬Fin15AnchoredAtom3090 chi ∧
      ¬Fin15AnchoredAtom3103 chi ∧
      ¬Fin15AnchoredAtom3131 chi ∧
      ¬Fin15AnchoredAtom3208 chi ∧
      ¬Fin15AnchoredAtom3210 chi ∧
      ¬Fin15AnchoredAtom3223 chi ∧
      ¬Fin15AnchoredAtom3251 chi ∧
      ¬Fin15AnchoredAtom3335 chi ∧
      ¬Fin15AnchoredAtom4033 chi ∧
      ¬Fin15AnchoredAtom4035 chi ∧
      ¬Fin15AnchoredAtom4048 chi ∧
      ¬Fin15AnchoredAtom4076 chi ∧
      ¬Fin15AnchoredAtom4160 chi ∧
      ¬Fin15AnchoredAtom4370 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 5, 6, 8, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask01403
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1887 Fin15AnchoredAtom1888 Fin15AnchoredAtom1890
    Fin15AnchoredAtom1892 Fin15AnchoredAtom1897 Fin15AnchoredAtom1899 Fin15AnchoredAtom1901
    Fin15AnchoredAtom1907 Fin15AnchoredAtom1909 Fin15AnchoredAtom1922 Fin15AnchoredAtom1942
    Fin15AnchoredAtom1944 Fin15AnchoredAtom1946 Fin15AnchoredAtom1952 Fin15AnchoredAtom1954
    Fin15AnchoredAtom1967 Fin15AnchoredAtom1988 Fin15AnchoredAtom1990 Fin15AnchoredAtom2003
    Fin15AnchoredAtom2031 Fin15AnchoredAtom2327 Fin15AnchoredAtom2329 Fin15AnchoredAtom2331
    Fin15AnchoredAtom2337 Fin15AnchoredAtom2339 Fin15AnchoredAtom2352 Fin15AnchoredAtom2373
    Fin15AnchoredAtom2375 Fin15AnchoredAtom2388 Fin15AnchoredAtom2416 Fin15AnchoredAtom2493
    Fin15AnchoredAtom2495 Fin15AnchoredAtom2508 Fin15AnchoredAtom2536 Fin15AnchoredAtom2620
    Fin15AnchoredAtom3042 Fin15AnchoredAtom3044 Fin15AnchoredAtom3046 Fin15AnchoredAtom3052
    Fin15AnchoredAtom3054 Fin15AnchoredAtom3067 Fin15AnchoredAtom3088 Fin15AnchoredAtom3090
    Fin15AnchoredAtom3103 Fin15AnchoredAtom3131 Fin15AnchoredAtom3208 Fin15AnchoredAtom3210
    Fin15AnchoredAtom3223 Fin15AnchoredAtom3251 Fin15AnchoredAtom3335 Fin15AnchoredAtom4033
    Fin15AnchoredAtom4035 Fin15AnchoredAtom4048 Fin15AnchoredAtom4076 Fin15AnchoredAtom4160
    Fin15AnchoredAtom4370 at hbad
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

theorem fin15Anchored_clause30769 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1890 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1899 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1907 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1925 chi ∧
      ¬Fin15AnchoredAtom1942 chi ∧
      ¬Fin15AnchoredAtom1944 chi ∧
      ¬Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom1952 chi ∧
      ¬Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom1970 chi ∧
      ¬Fin15AnchoredAtom1988 chi ∧
      ¬Fin15AnchoredAtom1993 chi ∧
      ¬Fin15AnchoredAtom2006 chi ∧
      ¬Fin15AnchoredAtom2034 chi ∧
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
      ¬Fin15AnchoredAtom3042 chi ∧
      ¬Fin15AnchoredAtom3044 chi ∧
      ¬Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom3052 chi ∧
      ¬Fin15AnchoredAtom3057 chi ∧
      ¬Fin15AnchoredAtom3070 chi ∧
      ¬Fin15AnchoredAtom3088 chi ∧
      ¬Fin15AnchoredAtom3093 chi ∧
      ¬Fin15AnchoredAtom3106 chi ∧
      ¬Fin15AnchoredAtom3134 chi ∧
      ¬Fin15AnchoredAtom3208 chi ∧
      ¬Fin15AnchoredAtom3213 chi ∧
      ¬Fin15AnchoredAtom3226 chi ∧
      ¬Fin15AnchoredAtom3254 chi ∧
      ¬Fin15AnchoredAtom3338 chi ∧
      ¬Fin15AnchoredAtom4033 chi ∧
      ¬Fin15AnchoredAtom4038 chi ∧
      ¬Fin15AnchoredAtom4051 chi ∧
      ¬Fin15AnchoredAtom4079 chi ∧
      ¬Fin15AnchoredAtom4163 chi ∧
      ¬Fin15AnchoredAtom4373 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 5, 6, 8, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask08571
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1887 Fin15AnchoredAtom1888 Fin15AnchoredAtom1890
    Fin15AnchoredAtom1895 Fin15AnchoredAtom1897 Fin15AnchoredAtom1899 Fin15AnchoredAtom1904
    Fin15AnchoredAtom1907 Fin15AnchoredAtom1912 Fin15AnchoredAtom1925 Fin15AnchoredAtom1942
    Fin15AnchoredAtom1944 Fin15AnchoredAtom1949 Fin15AnchoredAtom1952 Fin15AnchoredAtom1957
    Fin15AnchoredAtom1970 Fin15AnchoredAtom1988 Fin15AnchoredAtom1993 Fin15AnchoredAtom2006
    Fin15AnchoredAtom2034 Fin15AnchoredAtom2327 Fin15AnchoredAtom2329 Fin15AnchoredAtom2334
    Fin15AnchoredAtom2337 Fin15AnchoredAtom2342 Fin15AnchoredAtom2355 Fin15AnchoredAtom2373
    Fin15AnchoredAtom2378 Fin15AnchoredAtom2391 Fin15AnchoredAtom2419 Fin15AnchoredAtom2493
    Fin15AnchoredAtom2498 Fin15AnchoredAtom2511 Fin15AnchoredAtom2539 Fin15AnchoredAtom2623
    Fin15AnchoredAtom3042 Fin15AnchoredAtom3044 Fin15AnchoredAtom3049 Fin15AnchoredAtom3052
    Fin15AnchoredAtom3057 Fin15AnchoredAtom3070 Fin15AnchoredAtom3088 Fin15AnchoredAtom3093
    Fin15AnchoredAtom3106 Fin15AnchoredAtom3134 Fin15AnchoredAtom3208 Fin15AnchoredAtom3213
    Fin15AnchoredAtom3226 Fin15AnchoredAtom3254 Fin15AnchoredAtom3338 Fin15AnchoredAtom4033
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

theorem fin15Anchored_clause30770 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1890 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1899 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1907 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1926 chi ∧
      ¬Fin15AnchoredAtom1942 chi ∧
      ¬Fin15AnchoredAtom1944 chi ∧
      ¬Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom1952 chi ∧
      ¬Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom1971 chi ∧
      ¬Fin15AnchoredAtom1988 chi ∧
      ¬Fin15AnchoredAtom1994 chi ∧
      ¬Fin15AnchoredAtom2007 chi ∧
      ¬Fin15AnchoredAtom2035 chi ∧
      ¬Fin15AnchoredAtom2327 chi ∧
      ¬Fin15AnchoredAtom2329 chi ∧
      ¬Fin15AnchoredAtom2335 chi ∧
      ¬Fin15AnchoredAtom2337 chi ∧
      ¬Fin15AnchoredAtom2343 chi ∧
      ¬Fin15AnchoredAtom2356 chi ∧
      ¬Fin15AnchoredAtom2373 chi ∧
      ¬Fin15AnchoredAtom2379 chi ∧
      ¬Fin15AnchoredAtom2392 chi ∧
      ¬Fin15AnchoredAtom2420 chi ∧
      ¬Fin15AnchoredAtom2493 chi ∧
      ¬Fin15AnchoredAtom2499 chi ∧
      ¬Fin15AnchoredAtom2512 chi ∧
      ¬Fin15AnchoredAtom2540 chi ∧
      ¬Fin15AnchoredAtom2624 chi ∧
      ¬Fin15AnchoredAtom3042 chi ∧
      ¬Fin15AnchoredAtom3044 chi ∧
      ¬Fin15AnchoredAtom3050 chi ∧
      ¬Fin15AnchoredAtom3052 chi ∧
      ¬Fin15AnchoredAtom3058 chi ∧
      ¬Fin15AnchoredAtom3071 chi ∧
      ¬Fin15AnchoredAtom3088 chi ∧
      ¬Fin15AnchoredAtom3094 chi ∧
      ¬Fin15AnchoredAtom3107 chi ∧
      ¬Fin15AnchoredAtom3135 chi ∧
      ¬Fin15AnchoredAtom3208 chi ∧
      ¬Fin15AnchoredAtom3214 chi ∧
      ¬Fin15AnchoredAtom3227 chi ∧
      ¬Fin15AnchoredAtom3255 chi ∧
      ¬Fin15AnchoredAtom3339 chi ∧
      ¬Fin15AnchoredAtom4033 chi ∧
      ¬Fin15AnchoredAtom4039 chi ∧
      ¬Fin15AnchoredAtom4052 chi ∧
      ¬Fin15AnchoredAtom4080 chi ∧
      ¬Fin15AnchoredAtom4164 chi ∧
      ¬Fin15AnchoredAtom4374 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 5, 6, 8, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask16763
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1887 Fin15AnchoredAtom1888 Fin15AnchoredAtom1890
    Fin15AnchoredAtom1896 Fin15AnchoredAtom1897 Fin15AnchoredAtom1899 Fin15AnchoredAtom1905
    Fin15AnchoredAtom1907 Fin15AnchoredAtom1913 Fin15AnchoredAtom1926 Fin15AnchoredAtom1942
    Fin15AnchoredAtom1944 Fin15AnchoredAtom1950 Fin15AnchoredAtom1952 Fin15AnchoredAtom1958
    Fin15AnchoredAtom1971 Fin15AnchoredAtom1988 Fin15AnchoredAtom1994 Fin15AnchoredAtom2007
    Fin15AnchoredAtom2035 Fin15AnchoredAtom2327 Fin15AnchoredAtom2329 Fin15AnchoredAtom2335
    Fin15AnchoredAtom2337 Fin15AnchoredAtom2343 Fin15AnchoredAtom2356 Fin15AnchoredAtom2373
    Fin15AnchoredAtom2379 Fin15AnchoredAtom2392 Fin15AnchoredAtom2420 Fin15AnchoredAtom2493
    Fin15AnchoredAtom2499 Fin15AnchoredAtom2512 Fin15AnchoredAtom2540 Fin15AnchoredAtom2624
    Fin15AnchoredAtom3042 Fin15AnchoredAtom3044 Fin15AnchoredAtom3050 Fin15AnchoredAtom3052
    Fin15AnchoredAtom3058 Fin15AnchoredAtom3071 Fin15AnchoredAtom3088 Fin15AnchoredAtom3094
    Fin15AnchoredAtom3107 Fin15AnchoredAtom3135 Fin15AnchoredAtom3208 Fin15AnchoredAtom3214
    Fin15AnchoredAtom3227 Fin15AnchoredAtom3255 Fin15AnchoredAtom3339 Fin15AnchoredAtom4033
    Fin15AnchoredAtom4039 Fin15AnchoredAtom4052 Fin15AnchoredAtom4080 Fin15AnchoredAtom4164
    Fin15AnchoredAtom4374 at hbad
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

theorem fin15Anchored_clause30771 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
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
      ¬Fin15AnchoredAtom3042 chi ∧
      ¬Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom3053 chi ∧
      ¬Fin15AnchoredAtom3054 chi ∧
      ¬Fin15AnchoredAtom3072 chi ∧
      ¬Fin15AnchoredAtom3089 chi ∧
      ¬Fin15AnchoredAtom3090 chi ∧
      ¬Fin15AnchoredAtom3108 chi ∧
      ¬Fin15AnchoredAtom3136 chi ∧
      ¬Fin15AnchoredAtom3209 chi ∧
      ¬Fin15AnchoredAtom3210 chi ∧
      ¬Fin15AnchoredAtom3228 chi ∧
      ¬Fin15AnchoredAtom3256 chi ∧
      ¬Fin15AnchoredAtom3340 chi ∧
      ¬Fin15AnchoredAtom4034 chi ∧
      ¬Fin15AnchoredAtom4035 chi ∧
      ¬Fin15AnchoredAtom4053 chi ∧
      ¬Fin15AnchoredAtom4081 chi ∧
      ¬Fin15AnchoredAtom4165 chi ∧
      ¬Fin15AnchoredAtom4375 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 5, 6, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask01659
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1887 Fin15AnchoredAtom1888 Fin15AnchoredAtom1891
    Fin15AnchoredAtom1892 Fin15AnchoredAtom1897 Fin15AnchoredAtom1900 Fin15AnchoredAtom1901
    Fin15AnchoredAtom1908 Fin15AnchoredAtom1909 Fin15AnchoredAtom1927 Fin15AnchoredAtom1942
    Fin15AnchoredAtom1945 Fin15AnchoredAtom1946 Fin15AnchoredAtom1953 Fin15AnchoredAtom1954
    Fin15AnchoredAtom1972 Fin15AnchoredAtom1989 Fin15AnchoredAtom1990 Fin15AnchoredAtom2008
    Fin15AnchoredAtom2036 Fin15AnchoredAtom2327 Fin15AnchoredAtom2330 Fin15AnchoredAtom2331
    Fin15AnchoredAtom2338 Fin15AnchoredAtom2339 Fin15AnchoredAtom2357 Fin15AnchoredAtom2374
    Fin15AnchoredAtom2375 Fin15AnchoredAtom2393 Fin15AnchoredAtom2421 Fin15AnchoredAtom2494
    Fin15AnchoredAtom2495 Fin15AnchoredAtom2513 Fin15AnchoredAtom2541 Fin15AnchoredAtom2625
    Fin15AnchoredAtom3042 Fin15AnchoredAtom3045 Fin15AnchoredAtom3046 Fin15AnchoredAtom3053
    Fin15AnchoredAtom3054 Fin15AnchoredAtom3072 Fin15AnchoredAtom3089 Fin15AnchoredAtom3090
    Fin15AnchoredAtom3108 Fin15AnchoredAtom3136 Fin15AnchoredAtom3209 Fin15AnchoredAtom3210
    Fin15AnchoredAtom3228 Fin15AnchoredAtom3256 Fin15AnchoredAtom3340 Fin15AnchoredAtom4034
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

theorem fin15Anchored_clause30772 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
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
      ¬Fin15AnchoredAtom3042 chi ∧
      ¬Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom3048 chi ∧
      ¬Fin15AnchoredAtom3053 chi ∧
      ¬Fin15AnchoredAtom3056 chi ∧
      ¬Fin15AnchoredAtom3074 chi ∧
      ¬Fin15AnchoredAtom3089 chi ∧
      ¬Fin15AnchoredAtom3092 chi ∧
      ¬Fin15AnchoredAtom3110 chi ∧
      ¬Fin15AnchoredAtom3138 chi ∧
      ¬Fin15AnchoredAtom3209 chi ∧
      ¬Fin15AnchoredAtom3212 chi ∧
      ¬Fin15AnchoredAtom3230 chi ∧
      ¬Fin15AnchoredAtom3258 chi ∧
      ¬Fin15AnchoredAtom3342 chi ∧
      ¬Fin15AnchoredAtom4034 chi ∧
      ¬Fin15AnchoredAtom4037 chi ∧
      ¬Fin15AnchoredAtom4055 chi ∧
      ¬Fin15AnchoredAtom4083 chi ∧
      ¬Fin15AnchoredAtom4167 chi ∧
      ¬Fin15AnchoredAtom4377 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 5, 6, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask04731
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1887 Fin15AnchoredAtom1888 Fin15AnchoredAtom1891
    Fin15AnchoredAtom1894 Fin15AnchoredAtom1897 Fin15AnchoredAtom1900 Fin15AnchoredAtom1903
    Fin15AnchoredAtom1908 Fin15AnchoredAtom1911 Fin15AnchoredAtom1929 Fin15AnchoredAtom1942
    Fin15AnchoredAtom1945 Fin15AnchoredAtom1948 Fin15AnchoredAtom1953 Fin15AnchoredAtom1956
    Fin15AnchoredAtom1974 Fin15AnchoredAtom1989 Fin15AnchoredAtom1992 Fin15AnchoredAtom2010
    Fin15AnchoredAtom2038 Fin15AnchoredAtom2327 Fin15AnchoredAtom2330 Fin15AnchoredAtom2333
    Fin15AnchoredAtom2338 Fin15AnchoredAtom2341 Fin15AnchoredAtom2359 Fin15AnchoredAtom2374
    Fin15AnchoredAtom2377 Fin15AnchoredAtom2395 Fin15AnchoredAtom2423 Fin15AnchoredAtom2494
    Fin15AnchoredAtom2497 Fin15AnchoredAtom2515 Fin15AnchoredAtom2543 Fin15AnchoredAtom2627
    Fin15AnchoredAtom3042 Fin15AnchoredAtom3045 Fin15AnchoredAtom3048 Fin15AnchoredAtom3053
    Fin15AnchoredAtom3056 Fin15AnchoredAtom3074 Fin15AnchoredAtom3089 Fin15AnchoredAtom3092
    Fin15AnchoredAtom3110 Fin15AnchoredAtom3138 Fin15AnchoredAtom3209 Fin15AnchoredAtom3212
    Fin15AnchoredAtom3230 Fin15AnchoredAtom3258 Fin15AnchoredAtom3342 Fin15AnchoredAtom4034
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

theorem fin15Anchored_clause30773 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
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
      ¬Fin15AnchoredAtom3042 chi ∧
      ¬Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom3053 chi ∧
      ¬Fin15AnchoredAtom3057 chi ∧
      ¬Fin15AnchoredAtom3075 chi ∧
      ¬Fin15AnchoredAtom3089 chi ∧
      ¬Fin15AnchoredAtom3093 chi ∧
      ¬Fin15AnchoredAtom3111 chi ∧
      ¬Fin15AnchoredAtom3139 chi ∧
      ¬Fin15AnchoredAtom3209 chi ∧
      ¬Fin15AnchoredAtom3213 chi ∧
      ¬Fin15AnchoredAtom3231 chi ∧
      ¬Fin15AnchoredAtom3259 chi ∧
      ¬Fin15AnchoredAtom3343 chi ∧
      ¬Fin15AnchoredAtom4034 chi ∧
      ¬Fin15AnchoredAtom4038 chi ∧
      ¬Fin15AnchoredAtom4056 chi ∧
      ¬Fin15AnchoredAtom4084 chi ∧
      ¬Fin15AnchoredAtom4168 chi ∧
      ¬Fin15AnchoredAtom4378 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 5, 6, 9, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask08827
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1887 Fin15AnchoredAtom1888 Fin15AnchoredAtom1891
    Fin15AnchoredAtom1895 Fin15AnchoredAtom1897 Fin15AnchoredAtom1900 Fin15AnchoredAtom1904
    Fin15AnchoredAtom1908 Fin15AnchoredAtom1912 Fin15AnchoredAtom1930 Fin15AnchoredAtom1942
    Fin15AnchoredAtom1945 Fin15AnchoredAtom1949 Fin15AnchoredAtom1953 Fin15AnchoredAtom1957
    Fin15AnchoredAtom1975 Fin15AnchoredAtom1989 Fin15AnchoredAtom1993 Fin15AnchoredAtom2011
    Fin15AnchoredAtom2039 Fin15AnchoredAtom2327 Fin15AnchoredAtom2330 Fin15AnchoredAtom2334
    Fin15AnchoredAtom2338 Fin15AnchoredAtom2342 Fin15AnchoredAtom2360 Fin15AnchoredAtom2374
    Fin15AnchoredAtom2378 Fin15AnchoredAtom2396 Fin15AnchoredAtom2424 Fin15AnchoredAtom2494
    Fin15AnchoredAtom2498 Fin15AnchoredAtom2516 Fin15AnchoredAtom2544 Fin15AnchoredAtom2628
    Fin15AnchoredAtom3042 Fin15AnchoredAtom3045 Fin15AnchoredAtom3049 Fin15AnchoredAtom3053
    Fin15AnchoredAtom3057 Fin15AnchoredAtom3075 Fin15AnchoredAtom3089 Fin15AnchoredAtom3093
    Fin15AnchoredAtom3111 Fin15AnchoredAtom3139 Fin15AnchoredAtom3209 Fin15AnchoredAtom3213
    Fin15AnchoredAtom3231 Fin15AnchoredAtom3259 Fin15AnchoredAtom3343 Fin15AnchoredAtom4034
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

theorem fin15Anchored_clause30774 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
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
      ¬Fin15AnchoredAtom3042 chi ∧
      ¬Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom3050 chi ∧
      ¬Fin15AnchoredAtom3053 chi ∧
      ¬Fin15AnchoredAtom3058 chi ∧
      ¬Fin15AnchoredAtom3076 chi ∧
      ¬Fin15AnchoredAtom3089 chi ∧
      ¬Fin15AnchoredAtom3094 chi ∧
      ¬Fin15AnchoredAtom3112 chi ∧
      ¬Fin15AnchoredAtom3140 chi ∧
      ¬Fin15AnchoredAtom3209 chi ∧
      ¬Fin15AnchoredAtom3214 chi ∧
      ¬Fin15AnchoredAtom3232 chi ∧
      ¬Fin15AnchoredAtom3260 chi ∧
      ¬Fin15AnchoredAtom3344 chi ∧
      ¬Fin15AnchoredAtom4034 chi ∧
      ¬Fin15AnchoredAtom4039 chi ∧
      ¬Fin15AnchoredAtom4057 chi ∧
      ¬Fin15AnchoredAtom4085 chi ∧
      ¬Fin15AnchoredAtom4169 chi ∧
      ¬Fin15AnchoredAtom4379 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 5, 6, 9, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17019
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1887 Fin15AnchoredAtom1888 Fin15AnchoredAtom1891
    Fin15AnchoredAtom1896 Fin15AnchoredAtom1897 Fin15AnchoredAtom1900 Fin15AnchoredAtom1905
    Fin15AnchoredAtom1908 Fin15AnchoredAtom1913 Fin15AnchoredAtom1931 Fin15AnchoredAtom1942
    Fin15AnchoredAtom1945 Fin15AnchoredAtom1950 Fin15AnchoredAtom1953 Fin15AnchoredAtom1958
    Fin15AnchoredAtom1976 Fin15AnchoredAtom1989 Fin15AnchoredAtom1994 Fin15AnchoredAtom2012
    Fin15AnchoredAtom2040 Fin15AnchoredAtom2327 Fin15AnchoredAtom2330 Fin15AnchoredAtom2335
    Fin15AnchoredAtom2338 Fin15AnchoredAtom2343 Fin15AnchoredAtom2361 Fin15AnchoredAtom2374
    Fin15AnchoredAtom2379 Fin15AnchoredAtom2397 Fin15AnchoredAtom2425 Fin15AnchoredAtom2494
    Fin15AnchoredAtom2499 Fin15AnchoredAtom2517 Fin15AnchoredAtom2545 Fin15AnchoredAtom2629
    Fin15AnchoredAtom3042 Fin15AnchoredAtom3045 Fin15AnchoredAtom3050 Fin15AnchoredAtom3053
    Fin15AnchoredAtom3058 Fin15AnchoredAtom3076 Fin15AnchoredAtom3089 Fin15AnchoredAtom3094
    Fin15AnchoredAtom3112 Fin15AnchoredAtom3140 Fin15AnchoredAtom3209 Fin15AnchoredAtom3214
    Fin15AnchoredAtom3232 Fin15AnchoredAtom3260 Fin15AnchoredAtom3344 Fin15AnchoredAtom4034
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

theorem fin15Anchored_clause30775 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
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
      ¬Fin15AnchoredAtom3042 chi ∧
      ¬Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom3048 chi ∧
      ¬Fin15AnchoredAtom3054 chi ∧
      ¬Fin15AnchoredAtom3056 chi ∧
      ¬Fin15AnchoredAtom3078 chi ∧
      ¬Fin15AnchoredAtom3090 chi ∧
      ¬Fin15AnchoredAtom3092 chi ∧
      ¬Fin15AnchoredAtom3114 chi ∧
      ¬Fin15AnchoredAtom3142 chi ∧
      ¬Fin15AnchoredAtom3210 chi ∧
      ¬Fin15AnchoredAtom3212 chi ∧
      ¬Fin15AnchoredAtom3234 chi ∧
      ¬Fin15AnchoredAtom3262 chi ∧
      ¬Fin15AnchoredAtom3346 chi ∧
      ¬Fin15AnchoredAtom4035 chi ∧
      ¬Fin15AnchoredAtom4037 chi ∧
      ¬Fin15AnchoredAtom4059 chi ∧
      ¬Fin15AnchoredAtom4087 chi ∧
      ¬Fin15AnchoredAtom4171 chi ∧
      ¬Fin15AnchoredAtom4381 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 5, 6, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05243
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1887 Fin15AnchoredAtom1888 Fin15AnchoredAtom1892
    Fin15AnchoredAtom1894 Fin15AnchoredAtom1897 Fin15AnchoredAtom1901 Fin15AnchoredAtom1903
    Fin15AnchoredAtom1909 Fin15AnchoredAtom1911 Fin15AnchoredAtom1933 Fin15AnchoredAtom1942
    Fin15AnchoredAtom1946 Fin15AnchoredAtom1948 Fin15AnchoredAtom1954 Fin15AnchoredAtom1956
    Fin15AnchoredAtom1978 Fin15AnchoredAtom1990 Fin15AnchoredAtom1992 Fin15AnchoredAtom2014
    Fin15AnchoredAtom2042 Fin15AnchoredAtom2327 Fin15AnchoredAtom2331 Fin15AnchoredAtom2333
    Fin15AnchoredAtom2339 Fin15AnchoredAtom2341 Fin15AnchoredAtom2363 Fin15AnchoredAtom2375
    Fin15AnchoredAtom2377 Fin15AnchoredAtom2399 Fin15AnchoredAtom2427 Fin15AnchoredAtom2495
    Fin15AnchoredAtom2497 Fin15AnchoredAtom2519 Fin15AnchoredAtom2547 Fin15AnchoredAtom2631
    Fin15AnchoredAtom3042 Fin15AnchoredAtom3046 Fin15AnchoredAtom3048 Fin15AnchoredAtom3054
    Fin15AnchoredAtom3056 Fin15AnchoredAtom3078 Fin15AnchoredAtom3090 Fin15AnchoredAtom3092
    Fin15AnchoredAtom3114 Fin15AnchoredAtom3142 Fin15AnchoredAtom3210 Fin15AnchoredAtom3212
    Fin15AnchoredAtom3234 Fin15AnchoredAtom3262 Fin15AnchoredAtom3346 Fin15AnchoredAtom4035
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

theorem fin15Anchored_clause30776 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
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
      ¬Fin15AnchoredAtom3042 chi ∧
      ¬Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom3054 chi ∧
      ¬Fin15AnchoredAtom3057 chi ∧
      ¬Fin15AnchoredAtom3079 chi ∧
      ¬Fin15AnchoredAtom3090 chi ∧
      ¬Fin15AnchoredAtom3093 chi ∧
      ¬Fin15AnchoredAtom3115 chi ∧
      ¬Fin15AnchoredAtom3143 chi ∧
      ¬Fin15AnchoredAtom3210 chi ∧
      ¬Fin15AnchoredAtom3213 chi ∧
      ¬Fin15AnchoredAtom3235 chi ∧
      ¬Fin15AnchoredAtom3263 chi ∧
      ¬Fin15AnchoredAtom3347 chi ∧
      ¬Fin15AnchoredAtom4035 chi ∧
      ¬Fin15AnchoredAtom4038 chi ∧
      ¬Fin15AnchoredAtom4060 chi ∧
      ¬Fin15AnchoredAtom4088 chi ∧
      ¬Fin15AnchoredAtom4172 chi ∧
      ¬Fin15AnchoredAtom4382 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 5, 6, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09339
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1887 Fin15AnchoredAtom1888 Fin15AnchoredAtom1892
    Fin15AnchoredAtom1895 Fin15AnchoredAtom1897 Fin15AnchoredAtom1901 Fin15AnchoredAtom1904
    Fin15AnchoredAtom1909 Fin15AnchoredAtom1912 Fin15AnchoredAtom1934 Fin15AnchoredAtom1942
    Fin15AnchoredAtom1946 Fin15AnchoredAtom1949 Fin15AnchoredAtom1954 Fin15AnchoredAtom1957
    Fin15AnchoredAtom1979 Fin15AnchoredAtom1990 Fin15AnchoredAtom1993 Fin15AnchoredAtom2015
    Fin15AnchoredAtom2043 Fin15AnchoredAtom2327 Fin15AnchoredAtom2331 Fin15AnchoredAtom2334
    Fin15AnchoredAtom2339 Fin15AnchoredAtom2342 Fin15AnchoredAtom2364 Fin15AnchoredAtom2375
    Fin15AnchoredAtom2378 Fin15AnchoredAtom2400 Fin15AnchoredAtom2428 Fin15AnchoredAtom2495
    Fin15AnchoredAtom2498 Fin15AnchoredAtom2520 Fin15AnchoredAtom2548 Fin15AnchoredAtom2632
    Fin15AnchoredAtom3042 Fin15AnchoredAtom3046 Fin15AnchoredAtom3049 Fin15AnchoredAtom3054
    Fin15AnchoredAtom3057 Fin15AnchoredAtom3079 Fin15AnchoredAtom3090 Fin15AnchoredAtom3093
    Fin15AnchoredAtom3115 Fin15AnchoredAtom3143 Fin15AnchoredAtom3210 Fin15AnchoredAtom3213
    Fin15AnchoredAtom3235 Fin15AnchoredAtom3263 Fin15AnchoredAtom3347 Fin15AnchoredAtom4035
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

theorem fin15Anchored_clause30777 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1935 chi ∧
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
      ¬Fin15AnchoredAtom3042 chi ∧
      ¬Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom3050 chi ∧
      ¬Fin15AnchoredAtom3054 chi ∧
      ¬Fin15AnchoredAtom3058 chi ∧
      ¬Fin15AnchoredAtom3080 chi ∧
      ¬Fin15AnchoredAtom3090 chi ∧
      ¬Fin15AnchoredAtom3094 chi ∧
      ¬Fin15AnchoredAtom3116 chi ∧
      ¬Fin15AnchoredAtom3144 chi ∧
      ¬Fin15AnchoredAtom3210 chi ∧
      ¬Fin15AnchoredAtom3214 chi ∧
      ¬Fin15AnchoredAtom3236 chi ∧
      ¬Fin15AnchoredAtom3264 chi ∧
      ¬Fin15AnchoredAtom3348 chi ∧
      ¬Fin15AnchoredAtom4035 chi ∧
      ¬Fin15AnchoredAtom4039 chi ∧
      ¬Fin15AnchoredAtom4061 chi ∧
      ¬Fin15AnchoredAtom4089 chi ∧
      ¬Fin15AnchoredAtom4173 chi ∧
      ¬Fin15AnchoredAtom4383 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 5, 6, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17531
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1887 Fin15AnchoredAtom1888 Fin15AnchoredAtom1892
    Fin15AnchoredAtom1896 Fin15AnchoredAtom1897 Fin15AnchoredAtom1901 Fin15AnchoredAtom1905
    Fin15AnchoredAtom1909 Fin15AnchoredAtom1913 Fin15AnchoredAtom1935 Fin15AnchoredAtom1942
    Fin15AnchoredAtom1946 Fin15AnchoredAtom1950 Fin15AnchoredAtom1954 Fin15AnchoredAtom1958
    Fin15AnchoredAtom1980 Fin15AnchoredAtom1990 Fin15AnchoredAtom1994 Fin15AnchoredAtom2016
    Fin15AnchoredAtom2044 Fin15AnchoredAtom2327 Fin15AnchoredAtom2331 Fin15AnchoredAtom2335
    Fin15AnchoredAtom2339 Fin15AnchoredAtom2343 Fin15AnchoredAtom2365 Fin15AnchoredAtom2375
    Fin15AnchoredAtom2379 Fin15AnchoredAtom2401 Fin15AnchoredAtom2429 Fin15AnchoredAtom2495
    Fin15AnchoredAtom2499 Fin15AnchoredAtom2521 Fin15AnchoredAtom2549 Fin15AnchoredAtom2633
    Fin15AnchoredAtom3042 Fin15AnchoredAtom3046 Fin15AnchoredAtom3050 Fin15AnchoredAtom3054
    Fin15AnchoredAtom3058 Fin15AnchoredAtom3080 Fin15AnchoredAtom3090 Fin15AnchoredAtom3094
    Fin15AnchoredAtom3116 Fin15AnchoredAtom3144 Fin15AnchoredAtom3210 Fin15AnchoredAtom3214
    Fin15AnchoredAtom3236 Fin15AnchoredAtom3264 Fin15AnchoredAtom3348 Fin15AnchoredAtom4035
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

theorem fin15Anchored_clause30778 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1939 chi ∧
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
      ¬Fin15AnchoredAtom3042 chi ∧
      ¬Fin15AnchoredAtom3048 chi ∧
      ¬Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom3056 chi ∧
      ¬Fin15AnchoredAtom3057 chi ∧
      ¬Fin15AnchoredAtom3084 chi ∧
      ¬Fin15AnchoredAtom3092 chi ∧
      ¬Fin15AnchoredAtom3093 chi ∧
      ¬Fin15AnchoredAtom3120 chi ∧
      ¬Fin15AnchoredAtom3148 chi ∧
      ¬Fin15AnchoredAtom3212 chi ∧
      ¬Fin15AnchoredAtom3213 chi ∧
      ¬Fin15AnchoredAtom3240 chi ∧
      ¬Fin15AnchoredAtom3268 chi ∧
      ¬Fin15AnchoredAtom3352 chi ∧
      ¬Fin15AnchoredAtom4037 chi ∧
      ¬Fin15AnchoredAtom4038 chi ∧
      ¬Fin15AnchoredAtom4065 chi ∧
      ¬Fin15AnchoredAtom4093 chi ∧
      ¬Fin15AnchoredAtom4177 chi ∧
      ¬Fin15AnchoredAtom4387 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 5, 6, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask12411
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1887 Fin15AnchoredAtom1888 Fin15AnchoredAtom1894
    Fin15AnchoredAtom1895 Fin15AnchoredAtom1897 Fin15AnchoredAtom1903 Fin15AnchoredAtom1904
    Fin15AnchoredAtom1911 Fin15AnchoredAtom1912 Fin15AnchoredAtom1939 Fin15AnchoredAtom1942
    Fin15AnchoredAtom1948 Fin15AnchoredAtom1949 Fin15AnchoredAtom1956 Fin15AnchoredAtom1957
    Fin15AnchoredAtom1984 Fin15AnchoredAtom1992 Fin15AnchoredAtom1993 Fin15AnchoredAtom2020
    Fin15AnchoredAtom2048 Fin15AnchoredAtom2327 Fin15AnchoredAtom2333 Fin15AnchoredAtom2334
    Fin15AnchoredAtom2341 Fin15AnchoredAtom2342 Fin15AnchoredAtom2369 Fin15AnchoredAtom2377
    Fin15AnchoredAtom2378 Fin15AnchoredAtom2405 Fin15AnchoredAtom2433 Fin15AnchoredAtom2497
    Fin15AnchoredAtom2498 Fin15AnchoredAtom2525 Fin15AnchoredAtom2553 Fin15AnchoredAtom2637
    Fin15AnchoredAtom3042 Fin15AnchoredAtom3048 Fin15AnchoredAtom3049 Fin15AnchoredAtom3056
    Fin15AnchoredAtom3057 Fin15AnchoredAtom3084 Fin15AnchoredAtom3092 Fin15AnchoredAtom3093
    Fin15AnchoredAtom3120 Fin15AnchoredAtom3148 Fin15AnchoredAtom3212 Fin15AnchoredAtom3213
    Fin15AnchoredAtom3240 Fin15AnchoredAtom3268 Fin15AnchoredAtom3352 Fin15AnchoredAtom4037
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

theorem fin15Anchored_clause30779 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1940 chi ∧
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
      ¬Fin15AnchoredAtom3042 chi ∧
      ¬Fin15AnchoredAtom3048 chi ∧
      ¬Fin15AnchoredAtom3050 chi ∧
      ¬Fin15AnchoredAtom3056 chi ∧
      ¬Fin15AnchoredAtom3058 chi ∧
      ¬Fin15AnchoredAtom3085 chi ∧
      ¬Fin15AnchoredAtom3092 chi ∧
      ¬Fin15AnchoredAtom3094 chi ∧
      ¬Fin15AnchoredAtom3121 chi ∧
      ¬Fin15AnchoredAtom3149 chi ∧
      ¬Fin15AnchoredAtom3212 chi ∧
      ¬Fin15AnchoredAtom3214 chi ∧
      ¬Fin15AnchoredAtom3241 chi ∧
      ¬Fin15AnchoredAtom3269 chi ∧
      ¬Fin15AnchoredAtom3353 chi ∧
      ¬Fin15AnchoredAtom4037 chi ∧
      ¬Fin15AnchoredAtom4039 chi ∧
      ¬Fin15AnchoredAtom4066 chi ∧
      ¬Fin15AnchoredAtom4094 chi ∧
      ¬Fin15AnchoredAtom4178 chi ∧
      ¬Fin15AnchoredAtom4388 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 5, 6, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask20603
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1887 Fin15AnchoredAtom1888 Fin15AnchoredAtom1894
    Fin15AnchoredAtom1896 Fin15AnchoredAtom1897 Fin15AnchoredAtom1903 Fin15AnchoredAtom1905
    Fin15AnchoredAtom1911 Fin15AnchoredAtom1913 Fin15AnchoredAtom1940 Fin15AnchoredAtom1942
    Fin15AnchoredAtom1948 Fin15AnchoredAtom1950 Fin15AnchoredAtom1956 Fin15AnchoredAtom1958
    Fin15AnchoredAtom1985 Fin15AnchoredAtom1992 Fin15AnchoredAtom1994 Fin15AnchoredAtom2021
    Fin15AnchoredAtom2049 Fin15AnchoredAtom2327 Fin15AnchoredAtom2333 Fin15AnchoredAtom2335
    Fin15AnchoredAtom2341 Fin15AnchoredAtom2343 Fin15AnchoredAtom2370 Fin15AnchoredAtom2377
    Fin15AnchoredAtom2379 Fin15AnchoredAtom2406 Fin15AnchoredAtom2434 Fin15AnchoredAtom2497
    Fin15AnchoredAtom2499 Fin15AnchoredAtom2526 Fin15AnchoredAtom2554 Fin15AnchoredAtom2638
    Fin15AnchoredAtom3042 Fin15AnchoredAtom3048 Fin15AnchoredAtom3050 Fin15AnchoredAtom3056
    Fin15AnchoredAtom3058 Fin15AnchoredAtom3085 Fin15AnchoredAtom3092 Fin15AnchoredAtom3094
    Fin15AnchoredAtom3121 Fin15AnchoredAtom3149 Fin15AnchoredAtom3212 Fin15AnchoredAtom3214
    Fin15AnchoredAtom3241 Fin15AnchoredAtom3269 Fin15AnchoredAtom3353 Fin15AnchoredAtom4037
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

theorem fin15Anchored_clause30780 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
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
      ¬Fin15AnchoredAtom3042 chi ∧
      ¬Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom3050 chi ∧
      ¬Fin15AnchoredAtom3057 chi ∧
      ¬Fin15AnchoredAtom3058 chi ∧
      ¬Fin15AnchoredAtom3086 chi ∧
      ¬Fin15AnchoredAtom3093 chi ∧
      ¬Fin15AnchoredAtom3094 chi ∧
      ¬Fin15AnchoredAtom3122 chi ∧
      ¬Fin15AnchoredAtom3150 chi ∧
      ¬Fin15AnchoredAtom3213 chi ∧
      ¬Fin15AnchoredAtom3214 chi ∧
      ¬Fin15AnchoredAtom3242 chi ∧
      ¬Fin15AnchoredAtom3270 chi ∧
      ¬Fin15AnchoredAtom3354 chi ∧
      ¬Fin15AnchoredAtom4038 chi ∧
      ¬Fin15AnchoredAtom4039 chi ∧
      ¬Fin15AnchoredAtom4067 chi ∧
      ¬Fin15AnchoredAtom4095 chi ∧
      ¬Fin15AnchoredAtom4179 chi ∧
      ¬Fin15AnchoredAtom4389 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 5, 6, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask24699
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1887 Fin15AnchoredAtom1888 Fin15AnchoredAtom1895
    Fin15AnchoredAtom1896 Fin15AnchoredAtom1897 Fin15AnchoredAtom1904 Fin15AnchoredAtom1905
    Fin15AnchoredAtom1912 Fin15AnchoredAtom1913 Fin15AnchoredAtom1941 Fin15AnchoredAtom1942
    Fin15AnchoredAtom1949 Fin15AnchoredAtom1950 Fin15AnchoredAtom1957 Fin15AnchoredAtom1958
    Fin15AnchoredAtom1986 Fin15AnchoredAtom1993 Fin15AnchoredAtom1994 Fin15AnchoredAtom2022
    Fin15AnchoredAtom2050 Fin15AnchoredAtom2327 Fin15AnchoredAtom2334 Fin15AnchoredAtom2335
    Fin15AnchoredAtom2342 Fin15AnchoredAtom2343 Fin15AnchoredAtom2371 Fin15AnchoredAtom2378
    Fin15AnchoredAtom2379 Fin15AnchoredAtom2407 Fin15AnchoredAtom2435 Fin15AnchoredAtom2498
    Fin15AnchoredAtom2499 Fin15AnchoredAtom2527 Fin15AnchoredAtom2555 Fin15AnchoredAtom2639
    Fin15AnchoredAtom3042 Fin15AnchoredAtom3049 Fin15AnchoredAtom3050 Fin15AnchoredAtom3057
    Fin15AnchoredAtom3058 Fin15AnchoredAtom3086 Fin15AnchoredAtom3093 Fin15AnchoredAtom3094
    Fin15AnchoredAtom3122 Fin15AnchoredAtom3150 Fin15AnchoredAtom3213 Fin15AnchoredAtom3214
    Fin15AnchoredAtom3242 Fin15AnchoredAtom3270 Fin15AnchoredAtom3354 Fin15AnchoredAtom4038
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

theorem fin15Anchored_clause30781 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1890 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1899 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1914 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1921 chi ∧
      ¬Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom1944 chi ∧
      ¬Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom1959 chi ∧
      ¬Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom1966 chi ∧
      ¬Fin15AnchoredAtom1995 chi ∧
      ¬Fin15AnchoredAtom1996 chi ∧
      ¬Fin15AnchoredAtom2002 chi ∧
      ¬Fin15AnchoredAtom2051 chi ∧
      ¬Fin15AnchoredAtom2328 chi ∧
      ¬Fin15AnchoredAtom2329 chi ∧
      ¬Fin15AnchoredAtom2330 chi ∧
      ¬Fin15AnchoredAtom2344 chi ∧
      ¬Fin15AnchoredAtom2345 chi ∧
      ¬Fin15AnchoredAtom2351 chi ∧
      ¬Fin15AnchoredAtom2380 chi ∧
      ¬Fin15AnchoredAtom2381 chi ∧
      ¬Fin15AnchoredAtom2387 chi ∧
      ¬Fin15AnchoredAtom2436 chi ∧
      ¬Fin15AnchoredAtom2500 chi ∧
      ¬Fin15AnchoredAtom2501 chi ∧
      ¬Fin15AnchoredAtom2507 chi ∧
      ¬Fin15AnchoredAtom2556 chi ∧
      ¬Fin15AnchoredAtom2640 chi ∧
      ¬Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom3044 chi ∧
      ¬Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom3059 chi ∧
      ¬Fin15AnchoredAtom3060 chi ∧
      ¬Fin15AnchoredAtom3066 chi ∧
      ¬Fin15AnchoredAtom3095 chi ∧
      ¬Fin15AnchoredAtom3096 chi ∧
      ¬Fin15AnchoredAtom3102 chi ∧
      ¬Fin15AnchoredAtom3151 chi ∧
      ¬Fin15AnchoredAtom3215 chi ∧
      ¬Fin15AnchoredAtom3216 chi ∧
      ¬Fin15AnchoredAtom3222 chi ∧
      ¬Fin15AnchoredAtom3271 chi ∧
      ¬Fin15AnchoredAtom3355 chi ∧
      ¬Fin15AnchoredAtom4040 chi ∧
      ¬Fin15AnchoredAtom4041 chi ∧
      ¬Fin15AnchoredAtom4047 chi ∧
      ¬Fin15AnchoredAtom4096 chi ∧
      ¬Fin15AnchoredAtom4180 chi ∧
      ¬Fin15AnchoredAtom4390 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 5, 7, 8, 9}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask00955
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1887 Fin15AnchoredAtom1889 Fin15AnchoredAtom1890
    Fin15AnchoredAtom1891 Fin15AnchoredAtom1898 Fin15AnchoredAtom1899 Fin15AnchoredAtom1900
    Fin15AnchoredAtom1914 Fin15AnchoredAtom1915 Fin15AnchoredAtom1921 Fin15AnchoredAtom1943
    Fin15AnchoredAtom1944 Fin15AnchoredAtom1945 Fin15AnchoredAtom1959 Fin15AnchoredAtom1960
    Fin15AnchoredAtom1966 Fin15AnchoredAtom1995 Fin15AnchoredAtom1996 Fin15AnchoredAtom2002
    Fin15AnchoredAtom2051 Fin15AnchoredAtom2328 Fin15AnchoredAtom2329 Fin15AnchoredAtom2330
    Fin15AnchoredAtom2344 Fin15AnchoredAtom2345 Fin15AnchoredAtom2351 Fin15AnchoredAtom2380
    Fin15AnchoredAtom2381 Fin15AnchoredAtom2387 Fin15AnchoredAtom2436 Fin15AnchoredAtom2500
    Fin15AnchoredAtom2501 Fin15AnchoredAtom2507 Fin15AnchoredAtom2556 Fin15AnchoredAtom2640
    Fin15AnchoredAtom3043 Fin15AnchoredAtom3044 Fin15AnchoredAtom3045 Fin15AnchoredAtom3059
    Fin15AnchoredAtom3060 Fin15AnchoredAtom3066 Fin15AnchoredAtom3095 Fin15AnchoredAtom3096
    Fin15AnchoredAtom3102 Fin15AnchoredAtom3151 Fin15AnchoredAtom3215 Fin15AnchoredAtom3216
    Fin15AnchoredAtom3222 Fin15AnchoredAtom3271 Fin15AnchoredAtom3355 Fin15AnchoredAtom4040
    Fin15AnchoredAtom4041 Fin15AnchoredAtom4047 Fin15AnchoredAtom4096 Fin15AnchoredAtom4180
    Fin15AnchoredAtom4390 at hbad
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

theorem fin15Anchored_clause30782 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1890 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1899 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1914 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1922 chi ∧
      ¬Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom1944 chi ∧
      ¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1959 chi ∧
      ¬Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom1967 chi ∧
      ¬Fin15AnchoredAtom1995 chi ∧
      ¬Fin15AnchoredAtom1997 chi ∧
      ¬Fin15AnchoredAtom2003 chi ∧
      ¬Fin15AnchoredAtom2052 chi ∧
      ¬Fin15AnchoredAtom2328 chi ∧
      ¬Fin15AnchoredAtom2329 chi ∧
      ¬Fin15AnchoredAtom2331 chi ∧
      ¬Fin15AnchoredAtom2344 chi ∧
      ¬Fin15AnchoredAtom2346 chi ∧
      ¬Fin15AnchoredAtom2352 chi ∧
      ¬Fin15AnchoredAtom2380 chi ∧
      ¬Fin15AnchoredAtom2382 chi ∧
      ¬Fin15AnchoredAtom2388 chi ∧
      ¬Fin15AnchoredAtom2437 chi ∧
      ¬Fin15AnchoredAtom2500 chi ∧
      ¬Fin15AnchoredAtom2502 chi ∧
      ¬Fin15AnchoredAtom2508 chi ∧
      ¬Fin15AnchoredAtom2557 chi ∧
      ¬Fin15AnchoredAtom2641 chi ∧
      ¬Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom3044 chi ∧
      ¬Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom3059 chi ∧
      ¬Fin15AnchoredAtom3061 chi ∧
      ¬Fin15AnchoredAtom3067 chi ∧
      ¬Fin15AnchoredAtom3095 chi ∧
      ¬Fin15AnchoredAtom3097 chi ∧
      ¬Fin15AnchoredAtom3103 chi ∧
      ¬Fin15AnchoredAtom3152 chi ∧
      ¬Fin15AnchoredAtom3215 chi ∧
      ¬Fin15AnchoredAtom3217 chi ∧
      ¬Fin15AnchoredAtom3223 chi ∧
      ¬Fin15AnchoredAtom3272 chi ∧
      ¬Fin15AnchoredAtom3356 chi ∧
      ¬Fin15AnchoredAtom4040 chi ∧
      ¬Fin15AnchoredAtom4042 chi ∧
      ¬Fin15AnchoredAtom4048 chi ∧
      ¬Fin15AnchoredAtom4097 chi ∧
      ¬Fin15AnchoredAtom4181 chi ∧
      ¬Fin15AnchoredAtom4391 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 5, 7, 8, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask01467
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1887 Fin15AnchoredAtom1889 Fin15AnchoredAtom1890
    Fin15AnchoredAtom1892 Fin15AnchoredAtom1898 Fin15AnchoredAtom1899 Fin15AnchoredAtom1901
    Fin15AnchoredAtom1914 Fin15AnchoredAtom1916 Fin15AnchoredAtom1922 Fin15AnchoredAtom1943
    Fin15AnchoredAtom1944 Fin15AnchoredAtom1946 Fin15AnchoredAtom1959 Fin15AnchoredAtom1961
    Fin15AnchoredAtom1967 Fin15AnchoredAtom1995 Fin15AnchoredAtom1997 Fin15AnchoredAtom2003
    Fin15AnchoredAtom2052 Fin15AnchoredAtom2328 Fin15AnchoredAtom2329 Fin15AnchoredAtom2331
    Fin15AnchoredAtom2344 Fin15AnchoredAtom2346 Fin15AnchoredAtom2352 Fin15AnchoredAtom2380
    Fin15AnchoredAtom2382 Fin15AnchoredAtom2388 Fin15AnchoredAtom2437 Fin15AnchoredAtom2500
    Fin15AnchoredAtom2502 Fin15AnchoredAtom2508 Fin15AnchoredAtom2557 Fin15AnchoredAtom2641
    Fin15AnchoredAtom3043 Fin15AnchoredAtom3044 Fin15AnchoredAtom3046 Fin15AnchoredAtom3059
    Fin15AnchoredAtom3061 Fin15AnchoredAtom3067 Fin15AnchoredAtom3095 Fin15AnchoredAtom3097
    Fin15AnchoredAtom3103 Fin15AnchoredAtom3152 Fin15AnchoredAtom3215 Fin15AnchoredAtom3217
    Fin15AnchoredAtom3223 Fin15AnchoredAtom3272 Fin15AnchoredAtom3356 Fin15AnchoredAtom4040
    Fin15AnchoredAtom4042 Fin15AnchoredAtom4048 Fin15AnchoredAtom4097 Fin15AnchoredAtom4181
    Fin15AnchoredAtom4391 at hbad
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

theorem fin15Anchored_clause30783 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1890 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1899 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1914 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1924 chi ∧
      ¬Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom1944 chi ∧
      ¬Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom1959 chi ∧
      ¬Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom1969 chi ∧
      ¬Fin15AnchoredAtom1995 chi ∧
      ¬Fin15AnchoredAtom1999 chi ∧
      ¬Fin15AnchoredAtom2005 chi ∧
      ¬Fin15AnchoredAtom2054 chi ∧
      ¬Fin15AnchoredAtom2328 chi ∧
      ¬Fin15AnchoredAtom2329 chi ∧
      ¬Fin15AnchoredAtom2333 chi ∧
      ¬Fin15AnchoredAtom2344 chi ∧
      ¬Fin15AnchoredAtom2348 chi ∧
      ¬Fin15AnchoredAtom2354 chi ∧
      ¬Fin15AnchoredAtom2380 chi ∧
      ¬Fin15AnchoredAtom2384 chi ∧
      ¬Fin15AnchoredAtom2390 chi ∧
      ¬Fin15AnchoredAtom2439 chi ∧
      ¬Fin15AnchoredAtom2500 chi ∧
      ¬Fin15AnchoredAtom2504 chi ∧
      ¬Fin15AnchoredAtom2510 chi ∧
      ¬Fin15AnchoredAtom2559 chi ∧
      ¬Fin15AnchoredAtom2643 chi ∧
      ¬Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom3044 chi ∧
      ¬Fin15AnchoredAtom3048 chi ∧
      ¬Fin15AnchoredAtom3059 chi ∧
      ¬Fin15AnchoredAtom3063 chi ∧
      ¬Fin15AnchoredAtom3069 chi ∧
      ¬Fin15AnchoredAtom3095 chi ∧
      ¬Fin15AnchoredAtom3099 chi ∧
      ¬Fin15AnchoredAtom3105 chi ∧
      ¬Fin15AnchoredAtom3154 chi ∧
      ¬Fin15AnchoredAtom3215 chi ∧
      ¬Fin15AnchoredAtom3219 chi ∧
      ¬Fin15AnchoredAtom3225 chi ∧
      ¬Fin15AnchoredAtom3274 chi ∧
      ¬Fin15AnchoredAtom3358 chi ∧
      ¬Fin15AnchoredAtom4040 chi ∧
      ¬Fin15AnchoredAtom4044 chi ∧
      ¬Fin15AnchoredAtom4050 chi ∧
      ¬Fin15AnchoredAtom4099 chi ∧
      ¬Fin15AnchoredAtom4183 chi ∧
      ¬Fin15AnchoredAtom4393 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 5, 7, 8, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask04539
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1887 Fin15AnchoredAtom1889 Fin15AnchoredAtom1890
    Fin15AnchoredAtom1894 Fin15AnchoredAtom1898 Fin15AnchoredAtom1899 Fin15AnchoredAtom1903
    Fin15AnchoredAtom1914 Fin15AnchoredAtom1918 Fin15AnchoredAtom1924 Fin15AnchoredAtom1943
    Fin15AnchoredAtom1944 Fin15AnchoredAtom1948 Fin15AnchoredAtom1959 Fin15AnchoredAtom1963
    Fin15AnchoredAtom1969 Fin15AnchoredAtom1995 Fin15AnchoredAtom1999 Fin15AnchoredAtom2005
    Fin15AnchoredAtom2054 Fin15AnchoredAtom2328 Fin15AnchoredAtom2329 Fin15AnchoredAtom2333
    Fin15AnchoredAtom2344 Fin15AnchoredAtom2348 Fin15AnchoredAtom2354 Fin15AnchoredAtom2380
    Fin15AnchoredAtom2384 Fin15AnchoredAtom2390 Fin15AnchoredAtom2439 Fin15AnchoredAtom2500
    Fin15AnchoredAtom2504 Fin15AnchoredAtom2510 Fin15AnchoredAtom2559 Fin15AnchoredAtom2643
    Fin15AnchoredAtom3043 Fin15AnchoredAtom3044 Fin15AnchoredAtom3048 Fin15AnchoredAtom3059
    Fin15AnchoredAtom3063 Fin15AnchoredAtom3069 Fin15AnchoredAtom3095 Fin15AnchoredAtom3099
    Fin15AnchoredAtom3105 Fin15AnchoredAtom3154 Fin15AnchoredAtom3215 Fin15AnchoredAtom3219
    Fin15AnchoredAtom3225 Fin15AnchoredAtom3274 Fin15AnchoredAtom3358 Fin15AnchoredAtom4040
    Fin15AnchoredAtom4044 Fin15AnchoredAtom4050 Fin15AnchoredAtom4099 Fin15AnchoredAtom4183
    Fin15AnchoredAtom4393 at hbad
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

theorem fin15Anchored_clause30784 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1890 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1899 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1914 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1925 chi ∧
      ¬Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom1944 chi ∧
      ¬Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom1959 chi ∧
      ¬Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom1970 chi ∧
      ¬Fin15AnchoredAtom1995 chi ∧
      ¬Fin15AnchoredAtom2000 chi ∧
      ¬Fin15AnchoredAtom2006 chi ∧
      ¬Fin15AnchoredAtom2055 chi ∧
      ¬Fin15AnchoredAtom2328 chi ∧
      ¬Fin15AnchoredAtom2329 chi ∧
      ¬Fin15AnchoredAtom2334 chi ∧
      ¬Fin15AnchoredAtom2344 chi ∧
      ¬Fin15AnchoredAtom2349 chi ∧
      ¬Fin15AnchoredAtom2355 chi ∧
      ¬Fin15AnchoredAtom2380 chi ∧
      ¬Fin15AnchoredAtom2385 chi ∧
      ¬Fin15AnchoredAtom2391 chi ∧
      ¬Fin15AnchoredAtom2440 chi ∧
      ¬Fin15AnchoredAtom2500 chi ∧
      ¬Fin15AnchoredAtom2505 chi ∧
      ¬Fin15AnchoredAtom2511 chi ∧
      ¬Fin15AnchoredAtom2560 chi ∧
      ¬Fin15AnchoredAtom2644 chi ∧
      ¬Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom3044 chi ∧
      ¬Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom3059 chi ∧
      ¬Fin15AnchoredAtom3064 chi ∧
      ¬Fin15AnchoredAtom3070 chi ∧
      ¬Fin15AnchoredAtom3095 chi ∧
      ¬Fin15AnchoredAtom3100 chi ∧
      ¬Fin15AnchoredAtom3106 chi ∧
      ¬Fin15AnchoredAtom3155 chi ∧
      ¬Fin15AnchoredAtom3215 chi ∧
      ¬Fin15AnchoredAtom3220 chi ∧
      ¬Fin15AnchoredAtom3226 chi ∧
      ¬Fin15AnchoredAtom3275 chi ∧
      ¬Fin15AnchoredAtom3359 chi ∧
      ¬Fin15AnchoredAtom4040 chi ∧
      ¬Fin15AnchoredAtom4045 chi ∧
      ¬Fin15AnchoredAtom4051 chi ∧
      ¬Fin15AnchoredAtom4100 chi ∧
      ¬Fin15AnchoredAtom4184 chi ∧
      ¬Fin15AnchoredAtom4394 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 5, 7, 8, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask08635
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1887 Fin15AnchoredAtom1889 Fin15AnchoredAtom1890
    Fin15AnchoredAtom1895 Fin15AnchoredAtom1898 Fin15AnchoredAtom1899 Fin15AnchoredAtom1904
    Fin15AnchoredAtom1914 Fin15AnchoredAtom1919 Fin15AnchoredAtom1925 Fin15AnchoredAtom1943
    Fin15AnchoredAtom1944 Fin15AnchoredAtom1949 Fin15AnchoredAtom1959 Fin15AnchoredAtom1964
    Fin15AnchoredAtom1970 Fin15AnchoredAtom1995 Fin15AnchoredAtom2000 Fin15AnchoredAtom2006
    Fin15AnchoredAtom2055 Fin15AnchoredAtom2328 Fin15AnchoredAtom2329 Fin15AnchoredAtom2334
    Fin15AnchoredAtom2344 Fin15AnchoredAtom2349 Fin15AnchoredAtom2355 Fin15AnchoredAtom2380
    Fin15AnchoredAtom2385 Fin15AnchoredAtom2391 Fin15AnchoredAtom2440 Fin15AnchoredAtom2500
    Fin15AnchoredAtom2505 Fin15AnchoredAtom2511 Fin15AnchoredAtom2560 Fin15AnchoredAtom2644
    Fin15AnchoredAtom3043 Fin15AnchoredAtom3044 Fin15AnchoredAtom3049 Fin15AnchoredAtom3059
    Fin15AnchoredAtom3064 Fin15AnchoredAtom3070 Fin15AnchoredAtom3095 Fin15AnchoredAtom3100
    Fin15AnchoredAtom3106 Fin15AnchoredAtom3155 Fin15AnchoredAtom3215 Fin15AnchoredAtom3220
    Fin15AnchoredAtom3226 Fin15AnchoredAtom3275 Fin15AnchoredAtom3359 Fin15AnchoredAtom4040
    Fin15AnchoredAtom4045 Fin15AnchoredAtom4051 Fin15AnchoredAtom4100 Fin15AnchoredAtom4184
    Fin15AnchoredAtom4394 at hbad
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

theorem fin15Anchored_clause30785 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1890 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1899 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1914 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1926 chi ∧
      ¬Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom1944 chi ∧
      ¬Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom1959 chi ∧
      ¬Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom1971 chi ∧
      ¬Fin15AnchoredAtom1995 chi ∧
      ¬Fin15AnchoredAtom2001 chi ∧
      ¬Fin15AnchoredAtom2007 chi ∧
      ¬Fin15AnchoredAtom2056 chi ∧
      ¬Fin15AnchoredAtom2328 chi ∧
      ¬Fin15AnchoredAtom2329 chi ∧
      ¬Fin15AnchoredAtom2335 chi ∧
      ¬Fin15AnchoredAtom2344 chi ∧
      ¬Fin15AnchoredAtom2350 chi ∧
      ¬Fin15AnchoredAtom2356 chi ∧
      ¬Fin15AnchoredAtom2380 chi ∧
      ¬Fin15AnchoredAtom2386 chi ∧
      ¬Fin15AnchoredAtom2392 chi ∧
      ¬Fin15AnchoredAtom2441 chi ∧
      ¬Fin15AnchoredAtom2500 chi ∧
      ¬Fin15AnchoredAtom2506 chi ∧
      ¬Fin15AnchoredAtom2512 chi ∧
      ¬Fin15AnchoredAtom2561 chi ∧
      ¬Fin15AnchoredAtom2645 chi ∧
      ¬Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom3044 chi ∧
      ¬Fin15AnchoredAtom3050 chi ∧
      ¬Fin15AnchoredAtom3059 chi ∧
      ¬Fin15AnchoredAtom3065 chi ∧
      ¬Fin15AnchoredAtom3071 chi ∧
      ¬Fin15AnchoredAtom3095 chi ∧
      ¬Fin15AnchoredAtom3101 chi ∧
      ¬Fin15AnchoredAtom3107 chi ∧
      ¬Fin15AnchoredAtom3156 chi ∧
      ¬Fin15AnchoredAtom3215 chi ∧
      ¬Fin15AnchoredAtom3221 chi ∧
      ¬Fin15AnchoredAtom3227 chi ∧
      ¬Fin15AnchoredAtom3276 chi ∧
      ¬Fin15AnchoredAtom3360 chi ∧
      ¬Fin15AnchoredAtom4040 chi ∧
      ¬Fin15AnchoredAtom4046 chi ∧
      ¬Fin15AnchoredAtom4052 chi ∧
      ¬Fin15AnchoredAtom4101 chi ∧
      ¬Fin15AnchoredAtom4185 chi ∧
      ¬Fin15AnchoredAtom4395 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 5, 7, 8, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask16827
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1887 Fin15AnchoredAtom1889 Fin15AnchoredAtom1890
    Fin15AnchoredAtom1896 Fin15AnchoredAtom1898 Fin15AnchoredAtom1899 Fin15AnchoredAtom1905
    Fin15AnchoredAtom1914 Fin15AnchoredAtom1920 Fin15AnchoredAtom1926 Fin15AnchoredAtom1943
    Fin15AnchoredAtom1944 Fin15AnchoredAtom1950 Fin15AnchoredAtom1959 Fin15AnchoredAtom1965
    Fin15AnchoredAtom1971 Fin15AnchoredAtom1995 Fin15AnchoredAtom2001 Fin15AnchoredAtom2007
    Fin15AnchoredAtom2056 Fin15AnchoredAtom2328 Fin15AnchoredAtom2329 Fin15AnchoredAtom2335
    Fin15AnchoredAtom2344 Fin15AnchoredAtom2350 Fin15AnchoredAtom2356 Fin15AnchoredAtom2380
    Fin15AnchoredAtom2386 Fin15AnchoredAtom2392 Fin15AnchoredAtom2441 Fin15AnchoredAtom2500
    Fin15AnchoredAtom2506 Fin15AnchoredAtom2512 Fin15AnchoredAtom2561 Fin15AnchoredAtom2645
    Fin15AnchoredAtom3043 Fin15AnchoredAtom3044 Fin15AnchoredAtom3050 Fin15AnchoredAtom3059
    Fin15AnchoredAtom3065 Fin15AnchoredAtom3071 Fin15AnchoredAtom3095 Fin15AnchoredAtom3101
    Fin15AnchoredAtom3107 Fin15AnchoredAtom3156 Fin15AnchoredAtom3215 Fin15AnchoredAtom3221
    Fin15AnchoredAtom3227 Fin15AnchoredAtom3276 Fin15AnchoredAtom3360 Fin15AnchoredAtom4040
    Fin15AnchoredAtom4046 Fin15AnchoredAtom4052 Fin15AnchoredAtom4101 Fin15AnchoredAtom4185
    Fin15AnchoredAtom4395 at hbad
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

theorem fin15Anchored_clause30786 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
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
      ¬Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom3060 chi ∧
      ¬Fin15AnchoredAtom3061 chi ∧
      ¬Fin15AnchoredAtom3072 chi ∧
      ¬Fin15AnchoredAtom3096 chi ∧
      ¬Fin15AnchoredAtom3097 chi ∧
      ¬Fin15AnchoredAtom3108 chi ∧
      ¬Fin15AnchoredAtom3157 chi ∧
      ¬Fin15AnchoredAtom3216 chi ∧
      ¬Fin15AnchoredAtom3217 chi ∧
      ¬Fin15AnchoredAtom3228 chi ∧
      ¬Fin15AnchoredAtom3277 chi ∧
      ¬Fin15AnchoredAtom3361 chi ∧
      ¬Fin15AnchoredAtom4041 chi ∧
      ¬Fin15AnchoredAtom4042 chi ∧
      ¬Fin15AnchoredAtom4053 chi ∧
      ¬Fin15AnchoredAtom4102 chi ∧
      ¬Fin15AnchoredAtom4186 chi ∧
      ¬Fin15AnchoredAtom4396 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 5, 7, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask01723
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1887 Fin15AnchoredAtom1889 Fin15AnchoredAtom1891
    Fin15AnchoredAtom1892 Fin15AnchoredAtom1898 Fin15AnchoredAtom1900 Fin15AnchoredAtom1901
    Fin15AnchoredAtom1915 Fin15AnchoredAtom1916 Fin15AnchoredAtom1927 Fin15AnchoredAtom1943
    Fin15AnchoredAtom1945 Fin15AnchoredAtom1946 Fin15AnchoredAtom1960 Fin15AnchoredAtom1961
    Fin15AnchoredAtom1972 Fin15AnchoredAtom1996 Fin15AnchoredAtom1997 Fin15AnchoredAtom2008
    Fin15AnchoredAtom2057 Fin15AnchoredAtom2328 Fin15AnchoredAtom2330 Fin15AnchoredAtom2331
    Fin15AnchoredAtom2345 Fin15AnchoredAtom2346 Fin15AnchoredAtom2357 Fin15AnchoredAtom2381
    Fin15AnchoredAtom2382 Fin15AnchoredAtom2393 Fin15AnchoredAtom2442 Fin15AnchoredAtom2501
    Fin15AnchoredAtom2502 Fin15AnchoredAtom2513 Fin15AnchoredAtom2562 Fin15AnchoredAtom2646
    Fin15AnchoredAtom3043 Fin15AnchoredAtom3045 Fin15AnchoredAtom3046 Fin15AnchoredAtom3060
    Fin15AnchoredAtom3061 Fin15AnchoredAtom3072 Fin15AnchoredAtom3096 Fin15AnchoredAtom3097
    Fin15AnchoredAtom3108 Fin15AnchoredAtom3157 Fin15AnchoredAtom3216 Fin15AnchoredAtom3217
    Fin15AnchoredAtom3228 Fin15AnchoredAtom3277 Fin15AnchoredAtom3361 Fin15AnchoredAtom4041
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

theorem fin15Anchored_clause30787 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
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
      ¬Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom3048 chi ∧
      ¬Fin15AnchoredAtom3060 chi ∧
      ¬Fin15AnchoredAtom3063 chi ∧
      ¬Fin15AnchoredAtom3074 chi ∧
      ¬Fin15AnchoredAtom3096 chi ∧
      ¬Fin15AnchoredAtom3099 chi ∧
      ¬Fin15AnchoredAtom3110 chi ∧
      ¬Fin15AnchoredAtom3159 chi ∧
      ¬Fin15AnchoredAtom3216 chi ∧
      ¬Fin15AnchoredAtom3219 chi ∧
      ¬Fin15AnchoredAtom3230 chi ∧
      ¬Fin15AnchoredAtom3279 chi ∧
      ¬Fin15AnchoredAtom3363 chi ∧
      ¬Fin15AnchoredAtom4041 chi ∧
      ¬Fin15AnchoredAtom4044 chi ∧
      ¬Fin15AnchoredAtom4055 chi ∧
      ¬Fin15AnchoredAtom4104 chi ∧
      ¬Fin15AnchoredAtom4188 chi ∧
      ¬Fin15AnchoredAtom4398 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 5, 7, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask04795
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1887 Fin15AnchoredAtom1889 Fin15AnchoredAtom1891
    Fin15AnchoredAtom1894 Fin15AnchoredAtom1898 Fin15AnchoredAtom1900 Fin15AnchoredAtom1903
    Fin15AnchoredAtom1915 Fin15AnchoredAtom1918 Fin15AnchoredAtom1929 Fin15AnchoredAtom1943
    Fin15AnchoredAtom1945 Fin15AnchoredAtom1948 Fin15AnchoredAtom1960 Fin15AnchoredAtom1963
    Fin15AnchoredAtom1974 Fin15AnchoredAtom1996 Fin15AnchoredAtom1999 Fin15AnchoredAtom2010
    Fin15AnchoredAtom2059 Fin15AnchoredAtom2328 Fin15AnchoredAtom2330 Fin15AnchoredAtom2333
    Fin15AnchoredAtom2345 Fin15AnchoredAtom2348 Fin15AnchoredAtom2359 Fin15AnchoredAtom2381
    Fin15AnchoredAtom2384 Fin15AnchoredAtom2395 Fin15AnchoredAtom2444 Fin15AnchoredAtom2501
    Fin15AnchoredAtom2504 Fin15AnchoredAtom2515 Fin15AnchoredAtom2564 Fin15AnchoredAtom2648
    Fin15AnchoredAtom3043 Fin15AnchoredAtom3045 Fin15AnchoredAtom3048 Fin15AnchoredAtom3060
    Fin15AnchoredAtom3063 Fin15AnchoredAtom3074 Fin15AnchoredAtom3096 Fin15AnchoredAtom3099
    Fin15AnchoredAtom3110 Fin15AnchoredAtom3159 Fin15AnchoredAtom3216 Fin15AnchoredAtom3219
    Fin15AnchoredAtom3230 Fin15AnchoredAtom3279 Fin15AnchoredAtom3363 Fin15AnchoredAtom4041
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

theorem fin15Anchored_clause30788 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
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
      ¬Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom3060 chi ∧
      ¬Fin15AnchoredAtom3064 chi ∧
      ¬Fin15AnchoredAtom3075 chi ∧
      ¬Fin15AnchoredAtom3096 chi ∧
      ¬Fin15AnchoredAtom3100 chi ∧
      ¬Fin15AnchoredAtom3111 chi ∧
      ¬Fin15AnchoredAtom3160 chi ∧
      ¬Fin15AnchoredAtom3216 chi ∧
      ¬Fin15AnchoredAtom3220 chi ∧
      ¬Fin15AnchoredAtom3231 chi ∧
      ¬Fin15AnchoredAtom3280 chi ∧
      ¬Fin15AnchoredAtom3364 chi ∧
      ¬Fin15AnchoredAtom4041 chi ∧
      ¬Fin15AnchoredAtom4045 chi ∧
      ¬Fin15AnchoredAtom4056 chi ∧
      ¬Fin15AnchoredAtom4105 chi ∧
      ¬Fin15AnchoredAtom4189 chi ∧
      ¬Fin15AnchoredAtom4399 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 5, 7, 9, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask08891
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1887 Fin15AnchoredAtom1889 Fin15AnchoredAtom1891
    Fin15AnchoredAtom1895 Fin15AnchoredAtom1898 Fin15AnchoredAtom1900 Fin15AnchoredAtom1904
    Fin15AnchoredAtom1915 Fin15AnchoredAtom1919 Fin15AnchoredAtom1930 Fin15AnchoredAtom1943
    Fin15AnchoredAtom1945 Fin15AnchoredAtom1949 Fin15AnchoredAtom1960 Fin15AnchoredAtom1964
    Fin15AnchoredAtom1975 Fin15AnchoredAtom1996 Fin15AnchoredAtom2000 Fin15AnchoredAtom2011
    Fin15AnchoredAtom2060 Fin15AnchoredAtom2328 Fin15AnchoredAtom2330 Fin15AnchoredAtom2334
    Fin15AnchoredAtom2345 Fin15AnchoredAtom2349 Fin15AnchoredAtom2360 Fin15AnchoredAtom2381
    Fin15AnchoredAtom2385 Fin15AnchoredAtom2396 Fin15AnchoredAtom2445 Fin15AnchoredAtom2501
    Fin15AnchoredAtom2505 Fin15AnchoredAtom2516 Fin15AnchoredAtom2565 Fin15AnchoredAtom2649
    Fin15AnchoredAtom3043 Fin15AnchoredAtom3045 Fin15AnchoredAtom3049 Fin15AnchoredAtom3060
    Fin15AnchoredAtom3064 Fin15AnchoredAtom3075 Fin15AnchoredAtom3096 Fin15AnchoredAtom3100
    Fin15AnchoredAtom3111 Fin15AnchoredAtom3160 Fin15AnchoredAtom3216 Fin15AnchoredAtom3220
    Fin15AnchoredAtom3231 Fin15AnchoredAtom3280 Fin15AnchoredAtom3364 Fin15AnchoredAtom4041
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

theorem fin15Anchored_clause30789 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
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
      ¬Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom3050 chi ∧
      ¬Fin15AnchoredAtom3060 chi ∧
      ¬Fin15AnchoredAtom3065 chi ∧
      ¬Fin15AnchoredAtom3076 chi ∧
      ¬Fin15AnchoredAtom3096 chi ∧
      ¬Fin15AnchoredAtom3101 chi ∧
      ¬Fin15AnchoredAtom3112 chi ∧
      ¬Fin15AnchoredAtom3161 chi ∧
      ¬Fin15AnchoredAtom3216 chi ∧
      ¬Fin15AnchoredAtom3221 chi ∧
      ¬Fin15AnchoredAtom3232 chi ∧
      ¬Fin15AnchoredAtom3281 chi ∧
      ¬Fin15AnchoredAtom3365 chi ∧
      ¬Fin15AnchoredAtom4041 chi ∧
      ¬Fin15AnchoredAtom4046 chi ∧
      ¬Fin15AnchoredAtom4057 chi ∧
      ¬Fin15AnchoredAtom4106 chi ∧
      ¬Fin15AnchoredAtom4190 chi ∧
      ¬Fin15AnchoredAtom4400 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 5, 7, 9, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17083
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1887 Fin15AnchoredAtom1889 Fin15AnchoredAtom1891
    Fin15AnchoredAtom1896 Fin15AnchoredAtom1898 Fin15AnchoredAtom1900 Fin15AnchoredAtom1905
    Fin15AnchoredAtom1915 Fin15AnchoredAtom1920 Fin15AnchoredAtom1931 Fin15AnchoredAtom1943
    Fin15AnchoredAtom1945 Fin15AnchoredAtom1950 Fin15AnchoredAtom1960 Fin15AnchoredAtom1965
    Fin15AnchoredAtom1976 Fin15AnchoredAtom1996 Fin15AnchoredAtom2001 Fin15AnchoredAtom2012
    Fin15AnchoredAtom2061 Fin15AnchoredAtom2328 Fin15AnchoredAtom2330 Fin15AnchoredAtom2335
    Fin15AnchoredAtom2345 Fin15AnchoredAtom2350 Fin15AnchoredAtom2361 Fin15AnchoredAtom2381
    Fin15AnchoredAtom2386 Fin15AnchoredAtom2397 Fin15AnchoredAtom2446 Fin15AnchoredAtom2501
    Fin15AnchoredAtom2506 Fin15AnchoredAtom2517 Fin15AnchoredAtom2566 Fin15AnchoredAtom2650
    Fin15AnchoredAtom3043 Fin15AnchoredAtom3045 Fin15AnchoredAtom3050 Fin15AnchoredAtom3060
    Fin15AnchoredAtom3065 Fin15AnchoredAtom3076 Fin15AnchoredAtom3096 Fin15AnchoredAtom3101
    Fin15AnchoredAtom3112 Fin15AnchoredAtom3161 Fin15AnchoredAtom3216 Fin15AnchoredAtom3221
    Fin15AnchoredAtom3232 Fin15AnchoredAtom3281 Fin15AnchoredAtom3365 Fin15AnchoredAtom4041
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

theorem fin15Anchored_clause30790 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
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
      ¬Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom3048 chi ∧
      ¬Fin15AnchoredAtom3061 chi ∧
      ¬Fin15AnchoredAtom3063 chi ∧
      ¬Fin15AnchoredAtom3078 chi ∧
      ¬Fin15AnchoredAtom3097 chi ∧
      ¬Fin15AnchoredAtom3099 chi ∧
      ¬Fin15AnchoredAtom3114 chi ∧
      ¬Fin15AnchoredAtom3163 chi ∧
      ¬Fin15AnchoredAtom3217 chi ∧
      ¬Fin15AnchoredAtom3219 chi ∧
      ¬Fin15AnchoredAtom3234 chi ∧
      ¬Fin15AnchoredAtom3283 chi ∧
      ¬Fin15AnchoredAtom3367 chi ∧
      ¬Fin15AnchoredAtom4042 chi ∧
      ¬Fin15AnchoredAtom4044 chi ∧
      ¬Fin15AnchoredAtom4059 chi ∧
      ¬Fin15AnchoredAtom4108 chi ∧
      ¬Fin15AnchoredAtom4192 chi ∧
      ¬Fin15AnchoredAtom4402 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 5, 7, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05307
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1887 Fin15AnchoredAtom1889 Fin15AnchoredAtom1892
    Fin15AnchoredAtom1894 Fin15AnchoredAtom1898 Fin15AnchoredAtom1901 Fin15AnchoredAtom1903
    Fin15AnchoredAtom1916 Fin15AnchoredAtom1918 Fin15AnchoredAtom1933 Fin15AnchoredAtom1943
    Fin15AnchoredAtom1946 Fin15AnchoredAtom1948 Fin15AnchoredAtom1961 Fin15AnchoredAtom1963
    Fin15AnchoredAtom1978 Fin15AnchoredAtom1997 Fin15AnchoredAtom1999 Fin15AnchoredAtom2014
    Fin15AnchoredAtom2063 Fin15AnchoredAtom2328 Fin15AnchoredAtom2331 Fin15AnchoredAtom2333
    Fin15AnchoredAtom2346 Fin15AnchoredAtom2348 Fin15AnchoredAtom2363 Fin15AnchoredAtom2382
    Fin15AnchoredAtom2384 Fin15AnchoredAtom2399 Fin15AnchoredAtom2448 Fin15AnchoredAtom2502
    Fin15AnchoredAtom2504 Fin15AnchoredAtom2519 Fin15AnchoredAtom2568 Fin15AnchoredAtom2652
    Fin15AnchoredAtom3043 Fin15AnchoredAtom3046 Fin15AnchoredAtom3048 Fin15AnchoredAtom3061
    Fin15AnchoredAtom3063 Fin15AnchoredAtom3078 Fin15AnchoredAtom3097 Fin15AnchoredAtom3099
    Fin15AnchoredAtom3114 Fin15AnchoredAtom3163 Fin15AnchoredAtom3217 Fin15AnchoredAtom3219
    Fin15AnchoredAtom3234 Fin15AnchoredAtom3283 Fin15AnchoredAtom3367 Fin15AnchoredAtom4042
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

theorem fin15Anchored_clause30791 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
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
      ¬Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom3061 chi ∧
      ¬Fin15AnchoredAtom3064 chi ∧
      ¬Fin15AnchoredAtom3079 chi ∧
      ¬Fin15AnchoredAtom3097 chi ∧
      ¬Fin15AnchoredAtom3100 chi ∧
      ¬Fin15AnchoredAtom3115 chi ∧
      ¬Fin15AnchoredAtom3164 chi ∧
      ¬Fin15AnchoredAtom3217 chi ∧
      ¬Fin15AnchoredAtom3220 chi ∧
      ¬Fin15AnchoredAtom3235 chi ∧
      ¬Fin15AnchoredAtom3284 chi ∧
      ¬Fin15AnchoredAtom3368 chi ∧
      ¬Fin15AnchoredAtom4042 chi ∧
      ¬Fin15AnchoredAtom4045 chi ∧
      ¬Fin15AnchoredAtom4060 chi ∧
      ¬Fin15AnchoredAtom4109 chi ∧
      ¬Fin15AnchoredAtom4193 chi ∧
      ¬Fin15AnchoredAtom4403 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 5, 7, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09403
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1887 Fin15AnchoredAtom1889 Fin15AnchoredAtom1892
    Fin15AnchoredAtom1895 Fin15AnchoredAtom1898 Fin15AnchoredAtom1901 Fin15AnchoredAtom1904
    Fin15AnchoredAtom1916 Fin15AnchoredAtom1919 Fin15AnchoredAtom1934 Fin15AnchoredAtom1943
    Fin15AnchoredAtom1946 Fin15AnchoredAtom1949 Fin15AnchoredAtom1961 Fin15AnchoredAtom1964
    Fin15AnchoredAtom1979 Fin15AnchoredAtom1997 Fin15AnchoredAtom2000 Fin15AnchoredAtom2015
    Fin15AnchoredAtom2064 Fin15AnchoredAtom2328 Fin15AnchoredAtom2331 Fin15AnchoredAtom2334
    Fin15AnchoredAtom2346 Fin15AnchoredAtom2349 Fin15AnchoredAtom2364 Fin15AnchoredAtom2382
    Fin15AnchoredAtom2385 Fin15AnchoredAtom2400 Fin15AnchoredAtom2449 Fin15AnchoredAtom2502
    Fin15AnchoredAtom2505 Fin15AnchoredAtom2520 Fin15AnchoredAtom2569 Fin15AnchoredAtom2653
    Fin15AnchoredAtom3043 Fin15AnchoredAtom3046 Fin15AnchoredAtom3049 Fin15AnchoredAtom3061
    Fin15AnchoredAtom3064 Fin15AnchoredAtom3079 Fin15AnchoredAtom3097 Fin15AnchoredAtom3100
    Fin15AnchoredAtom3115 Fin15AnchoredAtom3164 Fin15AnchoredAtom3217 Fin15AnchoredAtom3220
    Fin15AnchoredAtom3235 Fin15AnchoredAtom3284 Fin15AnchoredAtom3368 Fin15AnchoredAtom4042
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

theorem fin15Anchored_clause30792 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1935 chi ∧
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
      ¬Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom3050 chi ∧
      ¬Fin15AnchoredAtom3061 chi ∧
      ¬Fin15AnchoredAtom3065 chi ∧
      ¬Fin15AnchoredAtom3080 chi ∧
      ¬Fin15AnchoredAtom3097 chi ∧
      ¬Fin15AnchoredAtom3101 chi ∧
      ¬Fin15AnchoredAtom3116 chi ∧
      ¬Fin15AnchoredAtom3165 chi ∧
      ¬Fin15AnchoredAtom3217 chi ∧
      ¬Fin15AnchoredAtom3221 chi ∧
      ¬Fin15AnchoredAtom3236 chi ∧
      ¬Fin15AnchoredAtom3285 chi ∧
      ¬Fin15AnchoredAtom3369 chi ∧
      ¬Fin15AnchoredAtom4042 chi ∧
      ¬Fin15AnchoredAtom4046 chi ∧
      ¬Fin15AnchoredAtom4061 chi ∧
      ¬Fin15AnchoredAtom4110 chi ∧
      ¬Fin15AnchoredAtom4194 chi ∧
      ¬Fin15AnchoredAtom4404 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 5, 7, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17595
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1887 Fin15AnchoredAtom1889 Fin15AnchoredAtom1892
    Fin15AnchoredAtom1896 Fin15AnchoredAtom1898 Fin15AnchoredAtom1901 Fin15AnchoredAtom1905
    Fin15AnchoredAtom1916 Fin15AnchoredAtom1920 Fin15AnchoredAtom1935 Fin15AnchoredAtom1943
    Fin15AnchoredAtom1946 Fin15AnchoredAtom1950 Fin15AnchoredAtom1961 Fin15AnchoredAtom1965
    Fin15AnchoredAtom1980 Fin15AnchoredAtom1997 Fin15AnchoredAtom2001 Fin15AnchoredAtom2016
    Fin15AnchoredAtom2065 Fin15AnchoredAtom2328 Fin15AnchoredAtom2331 Fin15AnchoredAtom2335
    Fin15AnchoredAtom2346 Fin15AnchoredAtom2350 Fin15AnchoredAtom2365 Fin15AnchoredAtom2382
    Fin15AnchoredAtom2386 Fin15AnchoredAtom2401 Fin15AnchoredAtom2450 Fin15AnchoredAtom2502
    Fin15AnchoredAtom2506 Fin15AnchoredAtom2521 Fin15AnchoredAtom2570 Fin15AnchoredAtom2654
    Fin15AnchoredAtom3043 Fin15AnchoredAtom3046 Fin15AnchoredAtom3050 Fin15AnchoredAtom3061
    Fin15AnchoredAtom3065 Fin15AnchoredAtom3080 Fin15AnchoredAtom3097 Fin15AnchoredAtom3101
    Fin15AnchoredAtom3116 Fin15AnchoredAtom3165 Fin15AnchoredAtom3217 Fin15AnchoredAtom3221
    Fin15AnchoredAtom3236 Fin15AnchoredAtom3285 Fin15AnchoredAtom3369 Fin15AnchoredAtom4042
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

theorem fin15Anchored_clause30793 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1939 chi ∧
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
      ¬Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom3048 chi ∧
      ¬Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom3063 chi ∧
      ¬Fin15AnchoredAtom3064 chi ∧
      ¬Fin15AnchoredAtom3084 chi ∧
      ¬Fin15AnchoredAtom3099 chi ∧
      ¬Fin15AnchoredAtom3100 chi ∧
      ¬Fin15AnchoredAtom3120 chi ∧
      ¬Fin15AnchoredAtom3169 chi ∧
      ¬Fin15AnchoredAtom3219 chi ∧
      ¬Fin15AnchoredAtom3220 chi ∧
      ¬Fin15AnchoredAtom3240 chi ∧
      ¬Fin15AnchoredAtom3289 chi ∧
      ¬Fin15AnchoredAtom3373 chi ∧
      ¬Fin15AnchoredAtom4044 chi ∧
      ¬Fin15AnchoredAtom4045 chi ∧
      ¬Fin15AnchoredAtom4065 chi ∧
      ¬Fin15AnchoredAtom4114 chi ∧
      ¬Fin15AnchoredAtom4198 chi ∧
      ¬Fin15AnchoredAtom4408 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 5, 7, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask12475
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1887 Fin15AnchoredAtom1889 Fin15AnchoredAtom1894
    Fin15AnchoredAtom1895 Fin15AnchoredAtom1898 Fin15AnchoredAtom1903 Fin15AnchoredAtom1904
    Fin15AnchoredAtom1918 Fin15AnchoredAtom1919 Fin15AnchoredAtom1939 Fin15AnchoredAtom1943
    Fin15AnchoredAtom1948 Fin15AnchoredAtom1949 Fin15AnchoredAtom1963 Fin15AnchoredAtom1964
    Fin15AnchoredAtom1984 Fin15AnchoredAtom1999 Fin15AnchoredAtom2000 Fin15AnchoredAtom2020
    Fin15AnchoredAtom2069 Fin15AnchoredAtom2328 Fin15AnchoredAtom2333 Fin15AnchoredAtom2334
    Fin15AnchoredAtom2348 Fin15AnchoredAtom2349 Fin15AnchoredAtom2369 Fin15AnchoredAtom2384
    Fin15AnchoredAtom2385 Fin15AnchoredAtom2405 Fin15AnchoredAtom2454 Fin15AnchoredAtom2504
    Fin15AnchoredAtom2505 Fin15AnchoredAtom2525 Fin15AnchoredAtom2574 Fin15AnchoredAtom2658
    Fin15AnchoredAtom3043 Fin15AnchoredAtom3048 Fin15AnchoredAtom3049 Fin15AnchoredAtom3063
    Fin15AnchoredAtom3064 Fin15AnchoredAtom3084 Fin15AnchoredAtom3099 Fin15AnchoredAtom3100
    Fin15AnchoredAtom3120 Fin15AnchoredAtom3169 Fin15AnchoredAtom3219 Fin15AnchoredAtom3220
    Fin15AnchoredAtom3240 Fin15AnchoredAtom3289 Fin15AnchoredAtom3373 Fin15AnchoredAtom4044
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

theorem fin15Anchored_clause30794 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1940 chi ∧
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
      ¬Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom3048 chi ∧
      ¬Fin15AnchoredAtom3050 chi ∧
      ¬Fin15AnchoredAtom3063 chi ∧
      ¬Fin15AnchoredAtom3065 chi ∧
      ¬Fin15AnchoredAtom3085 chi ∧
      ¬Fin15AnchoredAtom3099 chi ∧
      ¬Fin15AnchoredAtom3101 chi ∧
      ¬Fin15AnchoredAtom3121 chi ∧
      ¬Fin15AnchoredAtom3170 chi ∧
      ¬Fin15AnchoredAtom3219 chi ∧
      ¬Fin15AnchoredAtom3221 chi ∧
      ¬Fin15AnchoredAtom3241 chi ∧
      ¬Fin15AnchoredAtom3290 chi ∧
      ¬Fin15AnchoredAtom3374 chi ∧
      ¬Fin15AnchoredAtom4044 chi ∧
      ¬Fin15AnchoredAtom4046 chi ∧
      ¬Fin15AnchoredAtom4066 chi ∧
      ¬Fin15AnchoredAtom4115 chi ∧
      ¬Fin15AnchoredAtom4199 chi ∧
      ¬Fin15AnchoredAtom4409 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 5, 7, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask20667
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1887 Fin15AnchoredAtom1889 Fin15AnchoredAtom1894
    Fin15AnchoredAtom1896 Fin15AnchoredAtom1898 Fin15AnchoredAtom1903 Fin15AnchoredAtom1905
    Fin15AnchoredAtom1918 Fin15AnchoredAtom1920 Fin15AnchoredAtom1940 Fin15AnchoredAtom1943
    Fin15AnchoredAtom1948 Fin15AnchoredAtom1950 Fin15AnchoredAtom1963 Fin15AnchoredAtom1965
    Fin15AnchoredAtom1985 Fin15AnchoredAtom1999 Fin15AnchoredAtom2001 Fin15AnchoredAtom2021
    Fin15AnchoredAtom2070 Fin15AnchoredAtom2328 Fin15AnchoredAtom2333 Fin15AnchoredAtom2335
    Fin15AnchoredAtom2348 Fin15AnchoredAtom2350 Fin15AnchoredAtom2370 Fin15AnchoredAtom2384
    Fin15AnchoredAtom2386 Fin15AnchoredAtom2406 Fin15AnchoredAtom2455 Fin15AnchoredAtom2504
    Fin15AnchoredAtom2506 Fin15AnchoredAtom2526 Fin15AnchoredAtom2575 Fin15AnchoredAtom2659
    Fin15AnchoredAtom3043 Fin15AnchoredAtom3048 Fin15AnchoredAtom3050 Fin15AnchoredAtom3063
    Fin15AnchoredAtom3065 Fin15AnchoredAtom3085 Fin15AnchoredAtom3099 Fin15AnchoredAtom3101
    Fin15AnchoredAtom3121 Fin15AnchoredAtom3170 Fin15AnchoredAtom3219 Fin15AnchoredAtom3221
    Fin15AnchoredAtom3241 Fin15AnchoredAtom3290 Fin15AnchoredAtom3374 Fin15AnchoredAtom4044
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

theorem fin15Anchored_clause30795 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
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
      ¬Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom3050 chi ∧
      ¬Fin15AnchoredAtom3064 chi ∧
      ¬Fin15AnchoredAtom3065 chi ∧
      ¬Fin15AnchoredAtom3086 chi ∧
      ¬Fin15AnchoredAtom3100 chi ∧
      ¬Fin15AnchoredAtom3101 chi ∧
      ¬Fin15AnchoredAtom3122 chi ∧
      ¬Fin15AnchoredAtom3171 chi ∧
      ¬Fin15AnchoredAtom3220 chi ∧
      ¬Fin15AnchoredAtom3221 chi ∧
      ¬Fin15AnchoredAtom3242 chi ∧
      ¬Fin15AnchoredAtom3291 chi ∧
      ¬Fin15AnchoredAtom3375 chi ∧
      ¬Fin15AnchoredAtom4045 chi ∧
      ¬Fin15AnchoredAtom4046 chi ∧
      ¬Fin15AnchoredAtom4067 chi ∧
      ¬Fin15AnchoredAtom4116 chi ∧
      ¬Fin15AnchoredAtom4200 chi ∧
      ¬Fin15AnchoredAtom4410 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 5, 7, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask24763
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1887 Fin15AnchoredAtom1889 Fin15AnchoredAtom1895
    Fin15AnchoredAtom1896 Fin15AnchoredAtom1898 Fin15AnchoredAtom1904 Fin15AnchoredAtom1905
    Fin15AnchoredAtom1919 Fin15AnchoredAtom1920 Fin15AnchoredAtom1941 Fin15AnchoredAtom1943
    Fin15AnchoredAtom1949 Fin15AnchoredAtom1950 Fin15AnchoredAtom1964 Fin15AnchoredAtom1965
    Fin15AnchoredAtom1986 Fin15AnchoredAtom2000 Fin15AnchoredAtom2001 Fin15AnchoredAtom2022
    Fin15AnchoredAtom2071 Fin15AnchoredAtom2328 Fin15AnchoredAtom2334 Fin15AnchoredAtom2335
    Fin15AnchoredAtom2349 Fin15AnchoredAtom2350 Fin15AnchoredAtom2371 Fin15AnchoredAtom2385
    Fin15AnchoredAtom2386 Fin15AnchoredAtom2407 Fin15AnchoredAtom2456 Fin15AnchoredAtom2505
    Fin15AnchoredAtom2506 Fin15AnchoredAtom2527 Fin15AnchoredAtom2576 Fin15AnchoredAtom2660
    Fin15AnchoredAtom3043 Fin15AnchoredAtom3049 Fin15AnchoredAtom3050 Fin15AnchoredAtom3064
    Fin15AnchoredAtom3065 Fin15AnchoredAtom3086 Fin15AnchoredAtom3100 Fin15AnchoredAtom3101
    Fin15AnchoredAtom3122 Fin15AnchoredAtom3171 Fin15AnchoredAtom3220 Fin15AnchoredAtom3221
    Fin15AnchoredAtom3242 Fin15AnchoredAtom3291 Fin15AnchoredAtom3375 Fin15AnchoredAtom4045
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

theorem fin15Anchored_clause30796 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1890 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1899 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1921 chi ∧
      ¬Fin15AnchoredAtom1922 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1944 chi ∧
      ¬Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1966 chi ∧
      ¬Fin15AnchoredAtom1967 chi ∧
      ¬Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom2002 chi ∧
      ¬Fin15AnchoredAtom2003 chi ∧
      ¬Fin15AnchoredAtom2008 chi ∧
      ¬Fin15AnchoredAtom2072 chi ∧
      ¬Fin15AnchoredAtom2329 chi ∧
      ¬Fin15AnchoredAtom2330 chi ∧
      ¬Fin15AnchoredAtom2331 chi ∧
      ¬Fin15AnchoredAtom2351 chi ∧
      ¬Fin15AnchoredAtom2352 chi ∧
      ¬Fin15AnchoredAtom2357 chi ∧
      ¬Fin15AnchoredAtom2387 chi ∧
      ¬Fin15AnchoredAtom2388 chi ∧
      ¬Fin15AnchoredAtom2393 chi ∧
      ¬Fin15AnchoredAtom2457 chi ∧
      ¬Fin15AnchoredAtom2507 chi ∧
      ¬Fin15AnchoredAtom2508 chi ∧
      ¬Fin15AnchoredAtom2513 chi ∧
      ¬Fin15AnchoredAtom2577 chi ∧
      ¬Fin15AnchoredAtom2661 chi ∧
      ¬Fin15AnchoredAtom3044 chi ∧
      ¬Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom3066 chi ∧
      ¬Fin15AnchoredAtom3067 chi ∧
      ¬Fin15AnchoredAtom3072 chi ∧
      ¬Fin15AnchoredAtom3102 chi ∧
      ¬Fin15AnchoredAtom3103 chi ∧
      ¬Fin15AnchoredAtom3108 chi ∧
      ¬Fin15AnchoredAtom3172 chi ∧
      ¬Fin15AnchoredAtom3222 chi ∧
      ¬Fin15AnchoredAtom3223 chi ∧
      ¬Fin15AnchoredAtom3228 chi ∧
      ¬Fin15AnchoredAtom3292 chi ∧
      ¬Fin15AnchoredAtom3376 chi ∧
      ¬Fin15AnchoredAtom4047 chi ∧
      ¬Fin15AnchoredAtom4048 chi ∧
      ¬Fin15AnchoredAtom4053 chi ∧
      ¬Fin15AnchoredAtom4117 chi ∧
      ¬Fin15AnchoredAtom4201 chi ∧
      ¬Fin15AnchoredAtom4411 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 5, 8, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask01851
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1887 Fin15AnchoredAtom1890 Fin15AnchoredAtom1891
    Fin15AnchoredAtom1892 Fin15AnchoredAtom1899 Fin15AnchoredAtom1900 Fin15AnchoredAtom1901
    Fin15AnchoredAtom1921 Fin15AnchoredAtom1922 Fin15AnchoredAtom1927 Fin15AnchoredAtom1944
    Fin15AnchoredAtom1945 Fin15AnchoredAtom1946 Fin15AnchoredAtom1966 Fin15AnchoredAtom1967
    Fin15AnchoredAtom1972 Fin15AnchoredAtom2002 Fin15AnchoredAtom2003 Fin15AnchoredAtom2008
    Fin15AnchoredAtom2072 Fin15AnchoredAtom2329 Fin15AnchoredAtom2330 Fin15AnchoredAtom2331
    Fin15AnchoredAtom2351 Fin15AnchoredAtom2352 Fin15AnchoredAtom2357 Fin15AnchoredAtom2387
    Fin15AnchoredAtom2388 Fin15AnchoredAtom2393 Fin15AnchoredAtom2457 Fin15AnchoredAtom2507
    Fin15AnchoredAtom2508 Fin15AnchoredAtom2513 Fin15AnchoredAtom2577 Fin15AnchoredAtom2661
    Fin15AnchoredAtom3044 Fin15AnchoredAtom3045 Fin15AnchoredAtom3046 Fin15AnchoredAtom3066
    Fin15AnchoredAtom3067 Fin15AnchoredAtom3072 Fin15AnchoredAtom3102 Fin15AnchoredAtom3103
    Fin15AnchoredAtom3108 Fin15AnchoredAtom3172 Fin15AnchoredAtom3222 Fin15AnchoredAtom3223
    Fin15AnchoredAtom3228 Fin15AnchoredAtom3292 Fin15AnchoredAtom3376 Fin15AnchoredAtom4047
    Fin15AnchoredAtom4048 Fin15AnchoredAtom4053 Fin15AnchoredAtom4117 Fin15AnchoredAtom4201
    Fin15AnchoredAtom4411 at hbad
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

theorem fin15Anchored_clause30797 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1890 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1899 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1921 chi ∧
      ¬Fin15AnchoredAtom1924 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom1944 chi ∧
      ¬Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom1966 chi ∧
      ¬Fin15AnchoredAtom1969 chi ∧
      ¬Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom2002 chi ∧
      ¬Fin15AnchoredAtom2005 chi ∧
      ¬Fin15AnchoredAtom2010 chi ∧
      ¬Fin15AnchoredAtom2074 chi ∧
      ¬Fin15AnchoredAtom2329 chi ∧
      ¬Fin15AnchoredAtom2330 chi ∧
      ¬Fin15AnchoredAtom2333 chi ∧
      ¬Fin15AnchoredAtom2351 chi ∧
      ¬Fin15AnchoredAtom2354 chi ∧
      ¬Fin15AnchoredAtom2359 chi ∧
      ¬Fin15AnchoredAtom2387 chi ∧
      ¬Fin15AnchoredAtom2390 chi ∧
      ¬Fin15AnchoredAtom2395 chi ∧
      ¬Fin15AnchoredAtom2459 chi ∧
      ¬Fin15AnchoredAtom2507 chi ∧
      ¬Fin15AnchoredAtom2510 chi ∧
      ¬Fin15AnchoredAtom2515 chi ∧
      ¬Fin15AnchoredAtom2579 chi ∧
      ¬Fin15AnchoredAtom2663 chi ∧
      ¬Fin15AnchoredAtom3044 chi ∧
      ¬Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom3048 chi ∧
      ¬Fin15AnchoredAtom3066 chi ∧
      ¬Fin15AnchoredAtom3069 chi ∧
      ¬Fin15AnchoredAtom3074 chi ∧
      ¬Fin15AnchoredAtom3102 chi ∧
      ¬Fin15AnchoredAtom3105 chi ∧
      ¬Fin15AnchoredAtom3110 chi ∧
      ¬Fin15AnchoredAtom3174 chi ∧
      ¬Fin15AnchoredAtom3222 chi ∧
      ¬Fin15AnchoredAtom3225 chi ∧
      ¬Fin15AnchoredAtom3230 chi ∧
      ¬Fin15AnchoredAtom3294 chi ∧
      ¬Fin15AnchoredAtom3378 chi ∧
      ¬Fin15AnchoredAtom4047 chi ∧
      ¬Fin15AnchoredAtom4050 chi ∧
      ¬Fin15AnchoredAtom4055 chi ∧
      ¬Fin15AnchoredAtom4119 chi ∧
      ¬Fin15AnchoredAtom4203 chi ∧
      ¬Fin15AnchoredAtom4413 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 5, 8, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask04923
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1887 Fin15AnchoredAtom1890 Fin15AnchoredAtom1891
    Fin15AnchoredAtom1894 Fin15AnchoredAtom1899 Fin15AnchoredAtom1900 Fin15AnchoredAtom1903
    Fin15AnchoredAtom1921 Fin15AnchoredAtom1924 Fin15AnchoredAtom1929 Fin15AnchoredAtom1944
    Fin15AnchoredAtom1945 Fin15AnchoredAtom1948 Fin15AnchoredAtom1966 Fin15AnchoredAtom1969
    Fin15AnchoredAtom1974 Fin15AnchoredAtom2002 Fin15AnchoredAtom2005 Fin15AnchoredAtom2010
    Fin15AnchoredAtom2074 Fin15AnchoredAtom2329 Fin15AnchoredAtom2330 Fin15AnchoredAtom2333
    Fin15AnchoredAtom2351 Fin15AnchoredAtom2354 Fin15AnchoredAtom2359 Fin15AnchoredAtom2387
    Fin15AnchoredAtom2390 Fin15AnchoredAtom2395 Fin15AnchoredAtom2459 Fin15AnchoredAtom2507
    Fin15AnchoredAtom2510 Fin15AnchoredAtom2515 Fin15AnchoredAtom2579 Fin15AnchoredAtom2663
    Fin15AnchoredAtom3044 Fin15AnchoredAtom3045 Fin15AnchoredAtom3048 Fin15AnchoredAtom3066
    Fin15AnchoredAtom3069 Fin15AnchoredAtom3074 Fin15AnchoredAtom3102 Fin15AnchoredAtom3105
    Fin15AnchoredAtom3110 Fin15AnchoredAtom3174 Fin15AnchoredAtom3222 Fin15AnchoredAtom3225
    Fin15AnchoredAtom3230 Fin15AnchoredAtom3294 Fin15AnchoredAtom3378 Fin15AnchoredAtom4047
    Fin15AnchoredAtom4050 Fin15AnchoredAtom4055 Fin15AnchoredAtom4119 Fin15AnchoredAtom4203
    Fin15AnchoredAtom4413 at hbad
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

theorem fin15Anchored_clause30798 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1890 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1899 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1921 chi ∧
      ¬Fin15AnchoredAtom1925 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1944 chi ∧
      ¬Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom1966 chi ∧
      ¬Fin15AnchoredAtom1970 chi ∧
      ¬Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom2002 chi ∧
      ¬Fin15AnchoredAtom2006 chi ∧
      ¬Fin15AnchoredAtom2011 chi ∧
      ¬Fin15AnchoredAtom2075 chi ∧
      ¬Fin15AnchoredAtom2329 chi ∧
      ¬Fin15AnchoredAtom2330 chi ∧
      ¬Fin15AnchoredAtom2334 chi ∧
      ¬Fin15AnchoredAtom2351 chi ∧
      ¬Fin15AnchoredAtom2355 chi ∧
      ¬Fin15AnchoredAtom2360 chi ∧
      ¬Fin15AnchoredAtom2387 chi ∧
      ¬Fin15AnchoredAtom2391 chi ∧
      ¬Fin15AnchoredAtom2396 chi ∧
      ¬Fin15AnchoredAtom2460 chi ∧
      ¬Fin15AnchoredAtom2507 chi ∧
      ¬Fin15AnchoredAtom2511 chi ∧
      ¬Fin15AnchoredAtom2516 chi ∧
      ¬Fin15AnchoredAtom2580 chi ∧
      ¬Fin15AnchoredAtom2664 chi ∧
      ¬Fin15AnchoredAtom3044 chi ∧
      ¬Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom3066 chi ∧
      ¬Fin15AnchoredAtom3070 chi ∧
      ¬Fin15AnchoredAtom3075 chi ∧
      ¬Fin15AnchoredAtom3102 chi ∧
      ¬Fin15AnchoredAtom3106 chi ∧
      ¬Fin15AnchoredAtom3111 chi ∧
      ¬Fin15AnchoredAtom3175 chi ∧
      ¬Fin15AnchoredAtom3222 chi ∧
      ¬Fin15AnchoredAtom3226 chi ∧
      ¬Fin15AnchoredAtom3231 chi ∧
      ¬Fin15AnchoredAtom3295 chi ∧
      ¬Fin15AnchoredAtom3379 chi ∧
      ¬Fin15AnchoredAtom4047 chi ∧
      ¬Fin15AnchoredAtom4051 chi ∧
      ¬Fin15AnchoredAtom4056 chi ∧
      ¬Fin15AnchoredAtom4120 chi ∧
      ¬Fin15AnchoredAtom4204 chi ∧
      ¬Fin15AnchoredAtom4414 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 5, 8, 9, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09019
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1887 Fin15AnchoredAtom1890 Fin15AnchoredAtom1891
    Fin15AnchoredAtom1895 Fin15AnchoredAtom1899 Fin15AnchoredAtom1900 Fin15AnchoredAtom1904
    Fin15AnchoredAtom1921 Fin15AnchoredAtom1925 Fin15AnchoredAtom1930 Fin15AnchoredAtom1944
    Fin15AnchoredAtom1945 Fin15AnchoredAtom1949 Fin15AnchoredAtom1966 Fin15AnchoredAtom1970
    Fin15AnchoredAtom1975 Fin15AnchoredAtom2002 Fin15AnchoredAtom2006 Fin15AnchoredAtom2011
    Fin15AnchoredAtom2075 Fin15AnchoredAtom2329 Fin15AnchoredAtom2330 Fin15AnchoredAtom2334
    Fin15AnchoredAtom2351 Fin15AnchoredAtom2355 Fin15AnchoredAtom2360 Fin15AnchoredAtom2387
    Fin15AnchoredAtom2391 Fin15AnchoredAtom2396 Fin15AnchoredAtom2460 Fin15AnchoredAtom2507
    Fin15AnchoredAtom2511 Fin15AnchoredAtom2516 Fin15AnchoredAtom2580 Fin15AnchoredAtom2664
    Fin15AnchoredAtom3044 Fin15AnchoredAtom3045 Fin15AnchoredAtom3049 Fin15AnchoredAtom3066
    Fin15AnchoredAtom3070 Fin15AnchoredAtom3075 Fin15AnchoredAtom3102 Fin15AnchoredAtom3106
    Fin15AnchoredAtom3111 Fin15AnchoredAtom3175 Fin15AnchoredAtom3222 Fin15AnchoredAtom3226
    Fin15AnchoredAtom3231 Fin15AnchoredAtom3295 Fin15AnchoredAtom3379 Fin15AnchoredAtom4047
    Fin15AnchoredAtom4051 Fin15AnchoredAtom4056 Fin15AnchoredAtom4120 Fin15AnchoredAtom4204
    Fin15AnchoredAtom4414 at hbad
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

theorem fin15Anchored_clause30799 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1890 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1899 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1921 chi ∧
      ¬Fin15AnchoredAtom1926 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom1944 chi ∧
      ¬Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom1966 chi ∧
      ¬Fin15AnchoredAtom1971 chi ∧
      ¬Fin15AnchoredAtom1976 chi ∧
      ¬Fin15AnchoredAtom2002 chi ∧
      ¬Fin15AnchoredAtom2007 chi ∧
      ¬Fin15AnchoredAtom2012 chi ∧
      ¬Fin15AnchoredAtom2076 chi ∧
      ¬Fin15AnchoredAtom2329 chi ∧
      ¬Fin15AnchoredAtom2330 chi ∧
      ¬Fin15AnchoredAtom2335 chi ∧
      ¬Fin15AnchoredAtom2351 chi ∧
      ¬Fin15AnchoredAtom2356 chi ∧
      ¬Fin15AnchoredAtom2361 chi ∧
      ¬Fin15AnchoredAtom2387 chi ∧
      ¬Fin15AnchoredAtom2392 chi ∧
      ¬Fin15AnchoredAtom2397 chi ∧
      ¬Fin15AnchoredAtom2461 chi ∧
      ¬Fin15AnchoredAtom2507 chi ∧
      ¬Fin15AnchoredAtom2512 chi ∧
      ¬Fin15AnchoredAtom2517 chi ∧
      ¬Fin15AnchoredAtom2581 chi ∧
      ¬Fin15AnchoredAtom2665 chi ∧
      ¬Fin15AnchoredAtom3044 chi ∧
      ¬Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom3050 chi ∧
      ¬Fin15AnchoredAtom3066 chi ∧
      ¬Fin15AnchoredAtom3071 chi ∧
      ¬Fin15AnchoredAtom3076 chi ∧
      ¬Fin15AnchoredAtom3102 chi ∧
      ¬Fin15AnchoredAtom3107 chi ∧
      ¬Fin15AnchoredAtom3112 chi ∧
      ¬Fin15AnchoredAtom3176 chi ∧
      ¬Fin15AnchoredAtom3222 chi ∧
      ¬Fin15AnchoredAtom3227 chi ∧
      ¬Fin15AnchoredAtom3232 chi ∧
      ¬Fin15AnchoredAtom3296 chi ∧
      ¬Fin15AnchoredAtom3380 chi ∧
      ¬Fin15AnchoredAtom4047 chi ∧
      ¬Fin15AnchoredAtom4052 chi ∧
      ¬Fin15AnchoredAtom4057 chi ∧
      ¬Fin15AnchoredAtom4121 chi ∧
      ¬Fin15AnchoredAtom4205 chi ∧
      ¬Fin15AnchoredAtom4415 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 5, 8, 9, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17211
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1887 Fin15AnchoredAtom1890 Fin15AnchoredAtom1891
    Fin15AnchoredAtom1896 Fin15AnchoredAtom1899 Fin15AnchoredAtom1900 Fin15AnchoredAtom1905
    Fin15AnchoredAtom1921 Fin15AnchoredAtom1926 Fin15AnchoredAtom1931 Fin15AnchoredAtom1944
    Fin15AnchoredAtom1945 Fin15AnchoredAtom1950 Fin15AnchoredAtom1966 Fin15AnchoredAtom1971
    Fin15AnchoredAtom1976 Fin15AnchoredAtom2002 Fin15AnchoredAtom2007 Fin15AnchoredAtom2012
    Fin15AnchoredAtom2076 Fin15AnchoredAtom2329 Fin15AnchoredAtom2330 Fin15AnchoredAtom2335
    Fin15AnchoredAtom2351 Fin15AnchoredAtom2356 Fin15AnchoredAtom2361 Fin15AnchoredAtom2387
    Fin15AnchoredAtom2392 Fin15AnchoredAtom2397 Fin15AnchoredAtom2461 Fin15AnchoredAtom2507
    Fin15AnchoredAtom2512 Fin15AnchoredAtom2517 Fin15AnchoredAtom2581 Fin15AnchoredAtom2665
    Fin15AnchoredAtom3044 Fin15AnchoredAtom3045 Fin15AnchoredAtom3050 Fin15AnchoredAtom3066
    Fin15AnchoredAtom3071 Fin15AnchoredAtom3076 Fin15AnchoredAtom3102 Fin15AnchoredAtom3107
    Fin15AnchoredAtom3112 Fin15AnchoredAtom3176 Fin15AnchoredAtom3222 Fin15AnchoredAtom3227
    Fin15AnchoredAtom3232 Fin15AnchoredAtom3296 Fin15AnchoredAtom3380 Fin15AnchoredAtom4047
    Fin15AnchoredAtom4052 Fin15AnchoredAtom4057 Fin15AnchoredAtom4121 Fin15AnchoredAtom4205
    Fin15AnchoredAtom4415 at hbad
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

theorem fin15Anchored_clause30800 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1890 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1899 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1922 chi ∧
      ¬Fin15AnchoredAtom1924 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom1944 chi ∧
      ¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom1967 chi ∧
      ¬Fin15AnchoredAtom1969 chi ∧
      ¬Fin15AnchoredAtom1978 chi ∧
      ¬Fin15AnchoredAtom2003 chi ∧
      ¬Fin15AnchoredAtom2005 chi ∧
      ¬Fin15AnchoredAtom2014 chi ∧
      ¬Fin15AnchoredAtom2078 chi ∧
      ¬Fin15AnchoredAtom2329 chi ∧
      ¬Fin15AnchoredAtom2331 chi ∧
      ¬Fin15AnchoredAtom2333 chi ∧
      ¬Fin15AnchoredAtom2352 chi ∧
      ¬Fin15AnchoredAtom2354 chi ∧
      ¬Fin15AnchoredAtom2363 chi ∧
      ¬Fin15AnchoredAtom2388 chi ∧
      ¬Fin15AnchoredAtom2390 chi ∧
      ¬Fin15AnchoredAtom2399 chi ∧
      ¬Fin15AnchoredAtom2463 chi ∧
      ¬Fin15AnchoredAtom2508 chi ∧
      ¬Fin15AnchoredAtom2510 chi ∧
      ¬Fin15AnchoredAtom2519 chi ∧
      ¬Fin15AnchoredAtom2583 chi ∧
      ¬Fin15AnchoredAtom2667 chi ∧
      ¬Fin15AnchoredAtom3044 chi ∧
      ¬Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom3048 chi ∧
      ¬Fin15AnchoredAtom3067 chi ∧
      ¬Fin15AnchoredAtom3069 chi ∧
      ¬Fin15AnchoredAtom3078 chi ∧
      ¬Fin15AnchoredAtom3103 chi ∧
      ¬Fin15AnchoredAtom3105 chi ∧
      ¬Fin15AnchoredAtom3114 chi ∧
      ¬Fin15AnchoredAtom3178 chi ∧
      ¬Fin15AnchoredAtom3223 chi ∧
      ¬Fin15AnchoredAtom3225 chi ∧
      ¬Fin15AnchoredAtom3234 chi ∧
      ¬Fin15AnchoredAtom3298 chi ∧
      ¬Fin15AnchoredAtom3382 chi ∧
      ¬Fin15AnchoredAtom4048 chi ∧
      ¬Fin15AnchoredAtom4050 chi ∧
      ¬Fin15AnchoredAtom4059 chi ∧
      ¬Fin15AnchoredAtom4123 chi ∧
      ¬Fin15AnchoredAtom4207 chi ∧
      ¬Fin15AnchoredAtom4417 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 5, 8, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05435
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1887 Fin15AnchoredAtom1890 Fin15AnchoredAtom1892
    Fin15AnchoredAtom1894 Fin15AnchoredAtom1899 Fin15AnchoredAtom1901 Fin15AnchoredAtom1903
    Fin15AnchoredAtom1922 Fin15AnchoredAtom1924 Fin15AnchoredAtom1933 Fin15AnchoredAtom1944
    Fin15AnchoredAtom1946 Fin15AnchoredAtom1948 Fin15AnchoredAtom1967 Fin15AnchoredAtom1969
    Fin15AnchoredAtom1978 Fin15AnchoredAtom2003 Fin15AnchoredAtom2005 Fin15AnchoredAtom2014
    Fin15AnchoredAtom2078 Fin15AnchoredAtom2329 Fin15AnchoredAtom2331 Fin15AnchoredAtom2333
    Fin15AnchoredAtom2352 Fin15AnchoredAtom2354 Fin15AnchoredAtom2363 Fin15AnchoredAtom2388
    Fin15AnchoredAtom2390 Fin15AnchoredAtom2399 Fin15AnchoredAtom2463 Fin15AnchoredAtom2508
    Fin15AnchoredAtom2510 Fin15AnchoredAtom2519 Fin15AnchoredAtom2583 Fin15AnchoredAtom2667
    Fin15AnchoredAtom3044 Fin15AnchoredAtom3046 Fin15AnchoredAtom3048 Fin15AnchoredAtom3067
    Fin15AnchoredAtom3069 Fin15AnchoredAtom3078 Fin15AnchoredAtom3103 Fin15AnchoredAtom3105
    Fin15AnchoredAtom3114 Fin15AnchoredAtom3178 Fin15AnchoredAtom3223 Fin15AnchoredAtom3225
    Fin15AnchoredAtom3234 Fin15AnchoredAtom3298 Fin15AnchoredAtom3382 Fin15AnchoredAtom4048
    Fin15AnchoredAtom4050 Fin15AnchoredAtom4059 Fin15AnchoredAtom4123 Fin15AnchoredAtom4207
    Fin15AnchoredAtom4417 at hbad
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

theorem fin15Anchored_clause30801 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1890 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1899 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1922 chi ∧
      ¬Fin15AnchoredAtom1925 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom1944 chi ∧
      ¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom1967 chi ∧
      ¬Fin15AnchoredAtom1970 chi ∧
      ¬Fin15AnchoredAtom1979 chi ∧
      ¬Fin15AnchoredAtom2003 chi ∧
      ¬Fin15AnchoredAtom2006 chi ∧
      ¬Fin15AnchoredAtom2015 chi ∧
      ¬Fin15AnchoredAtom2079 chi ∧
      ¬Fin15AnchoredAtom2329 chi ∧
      ¬Fin15AnchoredAtom2331 chi ∧
      ¬Fin15AnchoredAtom2334 chi ∧
      ¬Fin15AnchoredAtom2352 chi ∧
      ¬Fin15AnchoredAtom2355 chi ∧
      ¬Fin15AnchoredAtom2364 chi ∧
      ¬Fin15AnchoredAtom2388 chi ∧
      ¬Fin15AnchoredAtom2391 chi ∧
      ¬Fin15AnchoredAtom2400 chi ∧
      ¬Fin15AnchoredAtom2464 chi ∧
      ¬Fin15AnchoredAtom2508 chi ∧
      ¬Fin15AnchoredAtom2511 chi ∧
      ¬Fin15AnchoredAtom2520 chi ∧
      ¬Fin15AnchoredAtom2584 chi ∧
      ¬Fin15AnchoredAtom2668 chi ∧
      ¬Fin15AnchoredAtom3044 chi ∧
      ¬Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom3067 chi ∧
      ¬Fin15AnchoredAtom3070 chi ∧
      ¬Fin15AnchoredAtom3079 chi ∧
      ¬Fin15AnchoredAtom3103 chi ∧
      ¬Fin15AnchoredAtom3106 chi ∧
      ¬Fin15AnchoredAtom3115 chi ∧
      ¬Fin15AnchoredAtom3179 chi ∧
      ¬Fin15AnchoredAtom3223 chi ∧
      ¬Fin15AnchoredAtom3226 chi ∧
      ¬Fin15AnchoredAtom3235 chi ∧
      ¬Fin15AnchoredAtom3299 chi ∧
      ¬Fin15AnchoredAtom3383 chi ∧
      ¬Fin15AnchoredAtom4048 chi ∧
      ¬Fin15AnchoredAtom4051 chi ∧
      ¬Fin15AnchoredAtom4060 chi ∧
      ¬Fin15AnchoredAtom4124 chi ∧
      ¬Fin15AnchoredAtom4208 chi ∧
      ¬Fin15AnchoredAtom4418 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 5, 8, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09531
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1887 Fin15AnchoredAtom1890 Fin15AnchoredAtom1892
    Fin15AnchoredAtom1895 Fin15AnchoredAtom1899 Fin15AnchoredAtom1901 Fin15AnchoredAtom1904
    Fin15AnchoredAtom1922 Fin15AnchoredAtom1925 Fin15AnchoredAtom1934 Fin15AnchoredAtom1944
    Fin15AnchoredAtom1946 Fin15AnchoredAtom1949 Fin15AnchoredAtom1967 Fin15AnchoredAtom1970
    Fin15AnchoredAtom1979 Fin15AnchoredAtom2003 Fin15AnchoredAtom2006 Fin15AnchoredAtom2015
    Fin15AnchoredAtom2079 Fin15AnchoredAtom2329 Fin15AnchoredAtom2331 Fin15AnchoredAtom2334
    Fin15AnchoredAtom2352 Fin15AnchoredAtom2355 Fin15AnchoredAtom2364 Fin15AnchoredAtom2388
    Fin15AnchoredAtom2391 Fin15AnchoredAtom2400 Fin15AnchoredAtom2464 Fin15AnchoredAtom2508
    Fin15AnchoredAtom2511 Fin15AnchoredAtom2520 Fin15AnchoredAtom2584 Fin15AnchoredAtom2668
    Fin15AnchoredAtom3044 Fin15AnchoredAtom3046 Fin15AnchoredAtom3049 Fin15AnchoredAtom3067
    Fin15AnchoredAtom3070 Fin15AnchoredAtom3079 Fin15AnchoredAtom3103 Fin15AnchoredAtom3106
    Fin15AnchoredAtom3115 Fin15AnchoredAtom3179 Fin15AnchoredAtom3223 Fin15AnchoredAtom3226
    Fin15AnchoredAtom3235 Fin15AnchoredAtom3299 Fin15AnchoredAtom3383 Fin15AnchoredAtom4048
    Fin15AnchoredAtom4051 Fin15AnchoredAtom4060 Fin15AnchoredAtom4124 Fin15AnchoredAtom4208
    Fin15AnchoredAtom4418 at hbad
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

theorem fin15Anchored_clause30802 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1890 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1899 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1922 chi ∧
      ¬Fin15AnchoredAtom1926 chi ∧
      ¬Fin15AnchoredAtom1935 chi ∧
      ¬Fin15AnchoredAtom1944 chi ∧
      ¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom1967 chi ∧
      ¬Fin15AnchoredAtom1971 chi ∧
      ¬Fin15AnchoredAtom1980 chi ∧
      ¬Fin15AnchoredAtom2003 chi ∧
      ¬Fin15AnchoredAtom2007 chi ∧
      ¬Fin15AnchoredAtom2016 chi ∧
      ¬Fin15AnchoredAtom2080 chi ∧
      ¬Fin15AnchoredAtom2329 chi ∧
      ¬Fin15AnchoredAtom2331 chi ∧
      ¬Fin15AnchoredAtom2335 chi ∧
      ¬Fin15AnchoredAtom2352 chi ∧
      ¬Fin15AnchoredAtom2356 chi ∧
      ¬Fin15AnchoredAtom2365 chi ∧
      ¬Fin15AnchoredAtom2388 chi ∧
      ¬Fin15AnchoredAtom2392 chi ∧
      ¬Fin15AnchoredAtom2401 chi ∧
      ¬Fin15AnchoredAtom2465 chi ∧
      ¬Fin15AnchoredAtom2508 chi ∧
      ¬Fin15AnchoredAtom2512 chi ∧
      ¬Fin15AnchoredAtom2521 chi ∧
      ¬Fin15AnchoredAtom2585 chi ∧
      ¬Fin15AnchoredAtom2669 chi ∧
      ¬Fin15AnchoredAtom3044 chi ∧
      ¬Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom3050 chi ∧
      ¬Fin15AnchoredAtom3067 chi ∧
      ¬Fin15AnchoredAtom3071 chi ∧
      ¬Fin15AnchoredAtom3080 chi ∧
      ¬Fin15AnchoredAtom3103 chi ∧
      ¬Fin15AnchoredAtom3107 chi ∧
      ¬Fin15AnchoredAtom3116 chi ∧
      ¬Fin15AnchoredAtom3180 chi ∧
      ¬Fin15AnchoredAtom3223 chi ∧
      ¬Fin15AnchoredAtom3227 chi ∧
      ¬Fin15AnchoredAtom3236 chi ∧
      ¬Fin15AnchoredAtom3300 chi ∧
      ¬Fin15AnchoredAtom3384 chi ∧
      ¬Fin15AnchoredAtom4048 chi ∧
      ¬Fin15AnchoredAtom4052 chi ∧
      ¬Fin15AnchoredAtom4061 chi ∧
      ¬Fin15AnchoredAtom4125 chi ∧
      ¬Fin15AnchoredAtom4209 chi ∧
      ¬Fin15AnchoredAtom4419 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 5, 8, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17723
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1887 Fin15AnchoredAtom1890 Fin15AnchoredAtom1892
    Fin15AnchoredAtom1896 Fin15AnchoredAtom1899 Fin15AnchoredAtom1901 Fin15AnchoredAtom1905
    Fin15AnchoredAtom1922 Fin15AnchoredAtom1926 Fin15AnchoredAtom1935 Fin15AnchoredAtom1944
    Fin15AnchoredAtom1946 Fin15AnchoredAtom1950 Fin15AnchoredAtom1967 Fin15AnchoredAtom1971
    Fin15AnchoredAtom1980 Fin15AnchoredAtom2003 Fin15AnchoredAtom2007 Fin15AnchoredAtom2016
    Fin15AnchoredAtom2080 Fin15AnchoredAtom2329 Fin15AnchoredAtom2331 Fin15AnchoredAtom2335
    Fin15AnchoredAtom2352 Fin15AnchoredAtom2356 Fin15AnchoredAtom2365 Fin15AnchoredAtom2388
    Fin15AnchoredAtom2392 Fin15AnchoredAtom2401 Fin15AnchoredAtom2465 Fin15AnchoredAtom2508
    Fin15AnchoredAtom2512 Fin15AnchoredAtom2521 Fin15AnchoredAtom2585 Fin15AnchoredAtom2669
    Fin15AnchoredAtom3044 Fin15AnchoredAtom3046 Fin15AnchoredAtom3050 Fin15AnchoredAtom3067
    Fin15AnchoredAtom3071 Fin15AnchoredAtom3080 Fin15AnchoredAtom3103 Fin15AnchoredAtom3107
    Fin15AnchoredAtom3116 Fin15AnchoredAtom3180 Fin15AnchoredAtom3223 Fin15AnchoredAtom3227
    Fin15AnchoredAtom3236 Fin15AnchoredAtom3300 Fin15AnchoredAtom3384 Fin15AnchoredAtom4048
    Fin15AnchoredAtom4052 Fin15AnchoredAtom4061 Fin15AnchoredAtom4125 Fin15AnchoredAtom4209
    Fin15AnchoredAtom4419 at hbad
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

theorem fin15Anchored_clause30803 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1890 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1899 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1924 chi ∧
      ¬Fin15AnchoredAtom1925 chi ∧
      ¬Fin15AnchoredAtom1939 chi ∧
      ¬Fin15AnchoredAtom1944 chi ∧
      ¬Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom1969 chi ∧
      ¬Fin15AnchoredAtom1970 chi ∧
      ¬Fin15AnchoredAtom1984 chi ∧
      ¬Fin15AnchoredAtom2005 chi ∧
      ¬Fin15AnchoredAtom2006 chi ∧
      ¬Fin15AnchoredAtom2020 chi ∧
      ¬Fin15AnchoredAtom2084 chi ∧
      ¬Fin15AnchoredAtom2329 chi ∧
      ¬Fin15AnchoredAtom2333 chi ∧
      ¬Fin15AnchoredAtom2334 chi ∧
      ¬Fin15AnchoredAtom2354 chi ∧
      ¬Fin15AnchoredAtom2355 chi ∧
      ¬Fin15AnchoredAtom2369 chi ∧
      ¬Fin15AnchoredAtom2390 chi ∧
      ¬Fin15AnchoredAtom2391 chi ∧
      ¬Fin15AnchoredAtom2405 chi ∧
      ¬Fin15AnchoredAtom2469 chi ∧
      ¬Fin15AnchoredAtom2510 chi ∧
      ¬Fin15AnchoredAtom2511 chi ∧
      ¬Fin15AnchoredAtom2525 chi ∧
      ¬Fin15AnchoredAtom2589 chi ∧
      ¬Fin15AnchoredAtom2673 chi ∧
      ¬Fin15AnchoredAtom3044 chi ∧
      ¬Fin15AnchoredAtom3048 chi ∧
      ¬Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom3069 chi ∧
      ¬Fin15AnchoredAtom3070 chi ∧
      ¬Fin15AnchoredAtom3084 chi ∧
      ¬Fin15AnchoredAtom3105 chi ∧
      ¬Fin15AnchoredAtom3106 chi ∧
      ¬Fin15AnchoredAtom3120 chi ∧
      ¬Fin15AnchoredAtom3184 chi ∧
      ¬Fin15AnchoredAtom3225 chi ∧
      ¬Fin15AnchoredAtom3226 chi ∧
      ¬Fin15AnchoredAtom3240 chi ∧
      ¬Fin15AnchoredAtom3304 chi ∧
      ¬Fin15AnchoredAtom3388 chi ∧
      ¬Fin15AnchoredAtom4050 chi ∧
      ¬Fin15AnchoredAtom4051 chi ∧
      ¬Fin15AnchoredAtom4065 chi ∧
      ¬Fin15AnchoredAtom4129 chi ∧
      ¬Fin15AnchoredAtom4213 chi ∧
      ¬Fin15AnchoredAtom4423 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 5, 8, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask12603
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1887 Fin15AnchoredAtom1890 Fin15AnchoredAtom1894
    Fin15AnchoredAtom1895 Fin15AnchoredAtom1899 Fin15AnchoredAtom1903 Fin15AnchoredAtom1904
    Fin15AnchoredAtom1924 Fin15AnchoredAtom1925 Fin15AnchoredAtom1939 Fin15AnchoredAtom1944
    Fin15AnchoredAtom1948 Fin15AnchoredAtom1949 Fin15AnchoredAtom1969 Fin15AnchoredAtom1970
    Fin15AnchoredAtom1984 Fin15AnchoredAtom2005 Fin15AnchoredAtom2006 Fin15AnchoredAtom2020
    Fin15AnchoredAtom2084 Fin15AnchoredAtom2329 Fin15AnchoredAtom2333 Fin15AnchoredAtom2334
    Fin15AnchoredAtom2354 Fin15AnchoredAtom2355 Fin15AnchoredAtom2369 Fin15AnchoredAtom2390
    Fin15AnchoredAtom2391 Fin15AnchoredAtom2405 Fin15AnchoredAtom2469 Fin15AnchoredAtom2510
    Fin15AnchoredAtom2511 Fin15AnchoredAtom2525 Fin15AnchoredAtom2589 Fin15AnchoredAtom2673
    Fin15AnchoredAtom3044 Fin15AnchoredAtom3048 Fin15AnchoredAtom3049 Fin15AnchoredAtom3069
    Fin15AnchoredAtom3070 Fin15AnchoredAtom3084 Fin15AnchoredAtom3105 Fin15AnchoredAtom3106
    Fin15AnchoredAtom3120 Fin15AnchoredAtom3184 Fin15AnchoredAtom3225 Fin15AnchoredAtom3226
    Fin15AnchoredAtom3240 Fin15AnchoredAtom3304 Fin15AnchoredAtom3388 Fin15AnchoredAtom4050
    Fin15AnchoredAtom4051 Fin15AnchoredAtom4065 Fin15AnchoredAtom4129 Fin15AnchoredAtom4213
    Fin15AnchoredAtom4423 at hbad
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

theorem fin15Anchored_clause30804 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1890 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1899 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1924 chi ∧
      ¬Fin15AnchoredAtom1926 chi ∧
      ¬Fin15AnchoredAtom1940 chi ∧
      ¬Fin15AnchoredAtom1944 chi ∧
      ¬Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom1969 chi ∧
      ¬Fin15AnchoredAtom1971 chi ∧
      ¬Fin15AnchoredAtom1985 chi ∧
      ¬Fin15AnchoredAtom2005 chi ∧
      ¬Fin15AnchoredAtom2007 chi ∧
      ¬Fin15AnchoredAtom2021 chi ∧
      ¬Fin15AnchoredAtom2085 chi ∧
      ¬Fin15AnchoredAtom2329 chi ∧
      ¬Fin15AnchoredAtom2333 chi ∧
      ¬Fin15AnchoredAtom2335 chi ∧
      ¬Fin15AnchoredAtom2354 chi ∧
      ¬Fin15AnchoredAtom2356 chi ∧
      ¬Fin15AnchoredAtom2370 chi ∧
      ¬Fin15AnchoredAtom2390 chi ∧
      ¬Fin15AnchoredAtom2392 chi ∧
      ¬Fin15AnchoredAtom2406 chi ∧
      ¬Fin15AnchoredAtom2470 chi ∧
      ¬Fin15AnchoredAtom2510 chi ∧
      ¬Fin15AnchoredAtom2512 chi ∧
      ¬Fin15AnchoredAtom2526 chi ∧
      ¬Fin15AnchoredAtom2590 chi ∧
      ¬Fin15AnchoredAtom2674 chi ∧
      ¬Fin15AnchoredAtom3044 chi ∧
      ¬Fin15AnchoredAtom3048 chi ∧
      ¬Fin15AnchoredAtom3050 chi ∧
      ¬Fin15AnchoredAtom3069 chi ∧
      ¬Fin15AnchoredAtom3071 chi ∧
      ¬Fin15AnchoredAtom3085 chi ∧
      ¬Fin15AnchoredAtom3105 chi ∧
      ¬Fin15AnchoredAtom3107 chi ∧
      ¬Fin15AnchoredAtom3121 chi ∧
      ¬Fin15AnchoredAtom3185 chi ∧
      ¬Fin15AnchoredAtom3225 chi ∧
      ¬Fin15AnchoredAtom3227 chi ∧
      ¬Fin15AnchoredAtom3241 chi ∧
      ¬Fin15AnchoredAtom3305 chi ∧
      ¬Fin15AnchoredAtom3389 chi ∧
      ¬Fin15AnchoredAtom4050 chi ∧
      ¬Fin15AnchoredAtom4052 chi ∧
      ¬Fin15AnchoredAtom4066 chi ∧
      ¬Fin15AnchoredAtom4130 chi ∧
      ¬Fin15AnchoredAtom4214 chi ∧
      ¬Fin15AnchoredAtom4424 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 5, 8, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask20795
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1887 Fin15AnchoredAtom1890 Fin15AnchoredAtom1894
    Fin15AnchoredAtom1896 Fin15AnchoredAtom1899 Fin15AnchoredAtom1903 Fin15AnchoredAtom1905
    Fin15AnchoredAtom1924 Fin15AnchoredAtom1926 Fin15AnchoredAtom1940 Fin15AnchoredAtom1944
    Fin15AnchoredAtom1948 Fin15AnchoredAtom1950 Fin15AnchoredAtom1969 Fin15AnchoredAtom1971
    Fin15AnchoredAtom1985 Fin15AnchoredAtom2005 Fin15AnchoredAtom2007 Fin15AnchoredAtom2021
    Fin15AnchoredAtom2085 Fin15AnchoredAtom2329 Fin15AnchoredAtom2333 Fin15AnchoredAtom2335
    Fin15AnchoredAtom2354 Fin15AnchoredAtom2356 Fin15AnchoredAtom2370 Fin15AnchoredAtom2390
    Fin15AnchoredAtom2392 Fin15AnchoredAtom2406 Fin15AnchoredAtom2470 Fin15AnchoredAtom2510
    Fin15AnchoredAtom2512 Fin15AnchoredAtom2526 Fin15AnchoredAtom2590 Fin15AnchoredAtom2674
    Fin15AnchoredAtom3044 Fin15AnchoredAtom3048 Fin15AnchoredAtom3050 Fin15AnchoredAtom3069
    Fin15AnchoredAtom3071 Fin15AnchoredAtom3085 Fin15AnchoredAtom3105 Fin15AnchoredAtom3107
    Fin15AnchoredAtom3121 Fin15AnchoredAtom3185 Fin15AnchoredAtom3225 Fin15AnchoredAtom3227
    Fin15AnchoredAtom3241 Fin15AnchoredAtom3305 Fin15AnchoredAtom3389 Fin15AnchoredAtom4050
    Fin15AnchoredAtom4052 Fin15AnchoredAtom4066 Fin15AnchoredAtom4130 Fin15AnchoredAtom4214
    Fin15AnchoredAtom4424 at hbad
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

theorem fin15Anchored_clause30805 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1890 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1899 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1925 chi ∧
      ¬Fin15AnchoredAtom1926 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
      ¬Fin15AnchoredAtom1944 chi ∧
      ¬Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom1970 chi ∧
      ¬Fin15AnchoredAtom1971 chi ∧
      ¬Fin15AnchoredAtom1986 chi ∧
      ¬Fin15AnchoredAtom2006 chi ∧
      ¬Fin15AnchoredAtom2007 chi ∧
      ¬Fin15AnchoredAtom2022 chi ∧
      ¬Fin15AnchoredAtom2086 chi ∧
      ¬Fin15AnchoredAtom2329 chi ∧
      ¬Fin15AnchoredAtom2334 chi ∧
      ¬Fin15AnchoredAtom2335 chi ∧
      ¬Fin15AnchoredAtom2355 chi ∧
      ¬Fin15AnchoredAtom2356 chi ∧
      ¬Fin15AnchoredAtom2371 chi ∧
      ¬Fin15AnchoredAtom2391 chi ∧
      ¬Fin15AnchoredAtom2392 chi ∧
      ¬Fin15AnchoredAtom2407 chi ∧
      ¬Fin15AnchoredAtom2471 chi ∧
      ¬Fin15AnchoredAtom2511 chi ∧
      ¬Fin15AnchoredAtom2512 chi ∧
      ¬Fin15AnchoredAtom2527 chi ∧
      ¬Fin15AnchoredAtom2591 chi ∧
      ¬Fin15AnchoredAtom2675 chi ∧
      ¬Fin15AnchoredAtom3044 chi ∧
      ¬Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom3050 chi ∧
      ¬Fin15AnchoredAtom3070 chi ∧
      ¬Fin15AnchoredAtom3071 chi ∧
      ¬Fin15AnchoredAtom3086 chi ∧
      ¬Fin15AnchoredAtom3106 chi ∧
      ¬Fin15AnchoredAtom3107 chi ∧
      ¬Fin15AnchoredAtom3122 chi ∧
      ¬Fin15AnchoredAtom3186 chi ∧
      ¬Fin15AnchoredAtom3226 chi ∧
      ¬Fin15AnchoredAtom3227 chi ∧
      ¬Fin15AnchoredAtom3242 chi ∧
      ¬Fin15AnchoredAtom3306 chi ∧
      ¬Fin15AnchoredAtom3390 chi ∧
      ¬Fin15AnchoredAtom4051 chi ∧
      ¬Fin15AnchoredAtom4052 chi ∧
      ¬Fin15AnchoredAtom4067 chi ∧
      ¬Fin15AnchoredAtom4131 chi ∧
      ¬Fin15AnchoredAtom4215 chi ∧
      ¬Fin15AnchoredAtom4425 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 5, 8, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask24891
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1887 Fin15AnchoredAtom1890 Fin15AnchoredAtom1895
    Fin15AnchoredAtom1896 Fin15AnchoredAtom1899 Fin15AnchoredAtom1904 Fin15AnchoredAtom1905
    Fin15AnchoredAtom1925 Fin15AnchoredAtom1926 Fin15AnchoredAtom1941 Fin15AnchoredAtom1944
    Fin15AnchoredAtom1949 Fin15AnchoredAtom1950 Fin15AnchoredAtom1970 Fin15AnchoredAtom1971
    Fin15AnchoredAtom1986 Fin15AnchoredAtom2006 Fin15AnchoredAtom2007 Fin15AnchoredAtom2022
    Fin15AnchoredAtom2086 Fin15AnchoredAtom2329 Fin15AnchoredAtom2334 Fin15AnchoredAtom2335
    Fin15AnchoredAtom2355 Fin15AnchoredAtom2356 Fin15AnchoredAtom2371 Fin15AnchoredAtom2391
    Fin15AnchoredAtom2392 Fin15AnchoredAtom2407 Fin15AnchoredAtom2471 Fin15AnchoredAtom2511
    Fin15AnchoredAtom2512 Fin15AnchoredAtom2527 Fin15AnchoredAtom2591 Fin15AnchoredAtom2675
    Fin15AnchoredAtom3044 Fin15AnchoredAtom3049 Fin15AnchoredAtom3050 Fin15AnchoredAtom3070
    Fin15AnchoredAtom3071 Fin15AnchoredAtom3086 Fin15AnchoredAtom3106 Fin15AnchoredAtom3107
    Fin15AnchoredAtom3122 Fin15AnchoredAtom3186 Fin15AnchoredAtom3226 Fin15AnchoredAtom3227
    Fin15AnchoredAtom3242 Fin15AnchoredAtom3306 Fin15AnchoredAtom3390 Fin15AnchoredAtom4051
    Fin15AnchoredAtom4052 Fin15AnchoredAtom4067 Fin15AnchoredAtom4131 Fin15AnchoredAtom4215
    Fin15AnchoredAtom4425 at hbad
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

theorem fin15Anchored_clause30806 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
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
      ¬Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom3048 chi ∧
      ¬Fin15AnchoredAtom3072 chi ∧
      ¬Fin15AnchoredAtom3074 chi ∧
      ¬Fin15AnchoredAtom3078 chi ∧
      ¬Fin15AnchoredAtom3108 chi ∧
      ¬Fin15AnchoredAtom3110 chi ∧
      ¬Fin15AnchoredAtom3114 chi ∧
      ¬Fin15AnchoredAtom3188 chi ∧
      ¬Fin15AnchoredAtom3228 chi ∧
      ¬Fin15AnchoredAtom3230 chi ∧
      ¬Fin15AnchoredAtom3234 chi ∧
      ¬Fin15AnchoredAtom3308 chi ∧
      ¬Fin15AnchoredAtom3392 chi ∧
      ¬Fin15AnchoredAtom4053 chi ∧
      ¬Fin15AnchoredAtom4055 chi ∧
      ¬Fin15AnchoredAtom4059 chi ∧
      ¬Fin15AnchoredAtom4133 chi ∧
      ¬Fin15AnchoredAtom4217 chi ∧
      ¬Fin15AnchoredAtom4427 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 5, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05691
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1887 Fin15AnchoredAtom1891 Fin15AnchoredAtom1892
    Fin15AnchoredAtom1894 Fin15AnchoredAtom1900 Fin15AnchoredAtom1901 Fin15AnchoredAtom1903
    Fin15AnchoredAtom1927 Fin15AnchoredAtom1929 Fin15AnchoredAtom1933 Fin15AnchoredAtom1945
    Fin15AnchoredAtom1946 Fin15AnchoredAtom1948 Fin15AnchoredAtom1972 Fin15AnchoredAtom1974
    Fin15AnchoredAtom1978 Fin15AnchoredAtom2008 Fin15AnchoredAtom2010 Fin15AnchoredAtom2014
    Fin15AnchoredAtom2088 Fin15AnchoredAtom2330 Fin15AnchoredAtom2331 Fin15AnchoredAtom2333
    Fin15AnchoredAtom2357 Fin15AnchoredAtom2359 Fin15AnchoredAtom2363 Fin15AnchoredAtom2393
    Fin15AnchoredAtom2395 Fin15AnchoredAtom2399 Fin15AnchoredAtom2473 Fin15AnchoredAtom2513
    Fin15AnchoredAtom2515 Fin15AnchoredAtom2519 Fin15AnchoredAtom2593 Fin15AnchoredAtom2677
    Fin15AnchoredAtom3045 Fin15AnchoredAtom3046 Fin15AnchoredAtom3048 Fin15AnchoredAtom3072
    Fin15AnchoredAtom3074 Fin15AnchoredAtom3078 Fin15AnchoredAtom3108 Fin15AnchoredAtom3110
    Fin15AnchoredAtom3114 Fin15AnchoredAtom3188 Fin15AnchoredAtom3228 Fin15AnchoredAtom3230
    Fin15AnchoredAtom3234 Fin15AnchoredAtom3308 Fin15AnchoredAtom3392 Fin15AnchoredAtom4053
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

theorem fin15Anchored_clause30807 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
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
      ¬Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom3072 chi ∧
      ¬Fin15AnchoredAtom3075 chi ∧
      ¬Fin15AnchoredAtom3079 chi ∧
      ¬Fin15AnchoredAtom3108 chi ∧
      ¬Fin15AnchoredAtom3111 chi ∧
      ¬Fin15AnchoredAtom3115 chi ∧
      ¬Fin15AnchoredAtom3189 chi ∧
      ¬Fin15AnchoredAtom3228 chi ∧
      ¬Fin15AnchoredAtom3231 chi ∧
      ¬Fin15AnchoredAtom3235 chi ∧
      ¬Fin15AnchoredAtom3309 chi ∧
      ¬Fin15AnchoredAtom3393 chi ∧
      ¬Fin15AnchoredAtom4053 chi ∧
      ¬Fin15AnchoredAtom4056 chi ∧
      ¬Fin15AnchoredAtom4060 chi ∧
      ¬Fin15AnchoredAtom4134 chi ∧
      ¬Fin15AnchoredAtom4218 chi ∧
      ¬Fin15AnchoredAtom4428 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 5, 9, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09787
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1887 Fin15AnchoredAtom1891 Fin15AnchoredAtom1892
    Fin15AnchoredAtom1895 Fin15AnchoredAtom1900 Fin15AnchoredAtom1901 Fin15AnchoredAtom1904
    Fin15AnchoredAtom1927 Fin15AnchoredAtom1930 Fin15AnchoredAtom1934 Fin15AnchoredAtom1945
    Fin15AnchoredAtom1946 Fin15AnchoredAtom1949 Fin15AnchoredAtom1972 Fin15AnchoredAtom1975
    Fin15AnchoredAtom1979 Fin15AnchoredAtom2008 Fin15AnchoredAtom2011 Fin15AnchoredAtom2015
    Fin15AnchoredAtom2089 Fin15AnchoredAtom2330 Fin15AnchoredAtom2331 Fin15AnchoredAtom2334
    Fin15AnchoredAtom2357 Fin15AnchoredAtom2360 Fin15AnchoredAtom2364 Fin15AnchoredAtom2393
    Fin15AnchoredAtom2396 Fin15AnchoredAtom2400 Fin15AnchoredAtom2474 Fin15AnchoredAtom2513
    Fin15AnchoredAtom2516 Fin15AnchoredAtom2520 Fin15AnchoredAtom2594 Fin15AnchoredAtom2678
    Fin15AnchoredAtom3045 Fin15AnchoredAtom3046 Fin15AnchoredAtom3049 Fin15AnchoredAtom3072
    Fin15AnchoredAtom3075 Fin15AnchoredAtom3079 Fin15AnchoredAtom3108 Fin15AnchoredAtom3111
    Fin15AnchoredAtom3115 Fin15AnchoredAtom3189 Fin15AnchoredAtom3228 Fin15AnchoredAtom3231
    Fin15AnchoredAtom3235 Fin15AnchoredAtom3309 Fin15AnchoredAtom3393 Fin15AnchoredAtom4053
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

theorem fin15Anchored_clause30808 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom1935 chi ∧
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
      ¬Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom3050 chi ∧
      ¬Fin15AnchoredAtom3072 chi ∧
      ¬Fin15AnchoredAtom3076 chi ∧
      ¬Fin15AnchoredAtom3080 chi ∧
      ¬Fin15AnchoredAtom3108 chi ∧
      ¬Fin15AnchoredAtom3112 chi ∧
      ¬Fin15AnchoredAtom3116 chi ∧
      ¬Fin15AnchoredAtom3190 chi ∧
      ¬Fin15AnchoredAtom3228 chi ∧
      ¬Fin15AnchoredAtom3232 chi ∧
      ¬Fin15AnchoredAtom3236 chi ∧
      ¬Fin15AnchoredAtom3310 chi ∧
      ¬Fin15AnchoredAtom3394 chi ∧
      ¬Fin15AnchoredAtom4053 chi ∧
      ¬Fin15AnchoredAtom4057 chi ∧
      ¬Fin15AnchoredAtom4061 chi ∧
      ¬Fin15AnchoredAtom4135 chi ∧
      ¬Fin15AnchoredAtom4219 chi ∧
      ¬Fin15AnchoredAtom4429 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 5, 9, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17979
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1887 Fin15AnchoredAtom1891 Fin15AnchoredAtom1892
    Fin15AnchoredAtom1896 Fin15AnchoredAtom1900 Fin15AnchoredAtom1901 Fin15AnchoredAtom1905
    Fin15AnchoredAtom1927 Fin15AnchoredAtom1931 Fin15AnchoredAtom1935 Fin15AnchoredAtom1945
    Fin15AnchoredAtom1946 Fin15AnchoredAtom1950 Fin15AnchoredAtom1972 Fin15AnchoredAtom1976
    Fin15AnchoredAtom1980 Fin15AnchoredAtom2008 Fin15AnchoredAtom2012 Fin15AnchoredAtom2016
    Fin15AnchoredAtom2090 Fin15AnchoredAtom2330 Fin15AnchoredAtom2331 Fin15AnchoredAtom2335
    Fin15AnchoredAtom2357 Fin15AnchoredAtom2361 Fin15AnchoredAtom2365 Fin15AnchoredAtom2393
    Fin15AnchoredAtom2397 Fin15AnchoredAtom2401 Fin15AnchoredAtom2475 Fin15AnchoredAtom2513
    Fin15AnchoredAtom2517 Fin15AnchoredAtom2521 Fin15AnchoredAtom2595 Fin15AnchoredAtom2679
    Fin15AnchoredAtom3045 Fin15AnchoredAtom3046 Fin15AnchoredAtom3050 Fin15AnchoredAtom3072
    Fin15AnchoredAtom3076 Fin15AnchoredAtom3080 Fin15AnchoredAtom3108 Fin15AnchoredAtom3112
    Fin15AnchoredAtom3116 Fin15AnchoredAtom3190 Fin15AnchoredAtom3228 Fin15AnchoredAtom3232
    Fin15AnchoredAtom3236 Fin15AnchoredAtom3310 Fin15AnchoredAtom3394 Fin15AnchoredAtom4053
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

theorem fin15Anchored_clause30809 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1939 chi ∧
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
      ¬Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom3048 chi ∧
      ¬Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom3074 chi ∧
      ¬Fin15AnchoredAtom3075 chi ∧
      ¬Fin15AnchoredAtom3084 chi ∧
      ¬Fin15AnchoredAtom3110 chi ∧
      ¬Fin15AnchoredAtom3111 chi ∧
      ¬Fin15AnchoredAtom3120 chi ∧
      ¬Fin15AnchoredAtom3194 chi ∧
      ¬Fin15AnchoredAtom3230 chi ∧
      ¬Fin15AnchoredAtom3231 chi ∧
      ¬Fin15AnchoredAtom3240 chi ∧
      ¬Fin15AnchoredAtom3314 chi ∧
      ¬Fin15AnchoredAtom3398 chi ∧
      ¬Fin15AnchoredAtom4055 chi ∧
      ¬Fin15AnchoredAtom4056 chi ∧
      ¬Fin15AnchoredAtom4065 chi ∧
      ¬Fin15AnchoredAtom4139 chi ∧
      ¬Fin15AnchoredAtom4223 chi ∧
      ¬Fin15AnchoredAtom4433 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 5, 9, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask12859
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1887 Fin15AnchoredAtom1891 Fin15AnchoredAtom1894
    Fin15AnchoredAtom1895 Fin15AnchoredAtom1900 Fin15AnchoredAtom1903 Fin15AnchoredAtom1904
    Fin15AnchoredAtom1929 Fin15AnchoredAtom1930 Fin15AnchoredAtom1939 Fin15AnchoredAtom1945
    Fin15AnchoredAtom1948 Fin15AnchoredAtom1949 Fin15AnchoredAtom1974 Fin15AnchoredAtom1975
    Fin15AnchoredAtom1984 Fin15AnchoredAtom2010 Fin15AnchoredAtom2011 Fin15AnchoredAtom2020
    Fin15AnchoredAtom2094 Fin15AnchoredAtom2330 Fin15AnchoredAtom2333 Fin15AnchoredAtom2334
    Fin15AnchoredAtom2359 Fin15AnchoredAtom2360 Fin15AnchoredAtom2369 Fin15AnchoredAtom2395
    Fin15AnchoredAtom2396 Fin15AnchoredAtom2405 Fin15AnchoredAtom2479 Fin15AnchoredAtom2515
    Fin15AnchoredAtom2516 Fin15AnchoredAtom2525 Fin15AnchoredAtom2599 Fin15AnchoredAtom2683
    Fin15AnchoredAtom3045 Fin15AnchoredAtom3048 Fin15AnchoredAtom3049 Fin15AnchoredAtom3074
    Fin15AnchoredAtom3075 Fin15AnchoredAtom3084 Fin15AnchoredAtom3110 Fin15AnchoredAtom3111
    Fin15AnchoredAtom3120 Fin15AnchoredAtom3194 Fin15AnchoredAtom3230 Fin15AnchoredAtom3231
    Fin15AnchoredAtom3240 Fin15AnchoredAtom3314 Fin15AnchoredAtom3398 Fin15AnchoredAtom4055
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

theorem fin15Anchored_clause30810 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom1940 chi ∧
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
      ¬Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom3048 chi ∧
      ¬Fin15AnchoredAtom3050 chi ∧
      ¬Fin15AnchoredAtom3074 chi ∧
      ¬Fin15AnchoredAtom3076 chi ∧
      ¬Fin15AnchoredAtom3085 chi ∧
      ¬Fin15AnchoredAtom3110 chi ∧
      ¬Fin15AnchoredAtom3112 chi ∧
      ¬Fin15AnchoredAtom3121 chi ∧
      ¬Fin15AnchoredAtom3195 chi ∧
      ¬Fin15AnchoredAtom3230 chi ∧
      ¬Fin15AnchoredAtom3232 chi ∧
      ¬Fin15AnchoredAtom3241 chi ∧
      ¬Fin15AnchoredAtom3315 chi ∧
      ¬Fin15AnchoredAtom3399 chi ∧
      ¬Fin15AnchoredAtom4055 chi ∧
      ¬Fin15AnchoredAtom4057 chi ∧
      ¬Fin15AnchoredAtom4066 chi ∧
      ¬Fin15AnchoredAtom4140 chi ∧
      ¬Fin15AnchoredAtom4224 chi ∧
      ¬Fin15AnchoredAtom4434 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 5, 9, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21051
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1887 Fin15AnchoredAtom1891 Fin15AnchoredAtom1894
    Fin15AnchoredAtom1896 Fin15AnchoredAtom1900 Fin15AnchoredAtom1903 Fin15AnchoredAtom1905
    Fin15AnchoredAtom1929 Fin15AnchoredAtom1931 Fin15AnchoredAtom1940 Fin15AnchoredAtom1945
    Fin15AnchoredAtom1948 Fin15AnchoredAtom1950 Fin15AnchoredAtom1974 Fin15AnchoredAtom1976
    Fin15AnchoredAtom1985 Fin15AnchoredAtom2010 Fin15AnchoredAtom2012 Fin15AnchoredAtom2021
    Fin15AnchoredAtom2095 Fin15AnchoredAtom2330 Fin15AnchoredAtom2333 Fin15AnchoredAtom2335
    Fin15AnchoredAtom2359 Fin15AnchoredAtom2361 Fin15AnchoredAtom2370 Fin15AnchoredAtom2395
    Fin15AnchoredAtom2397 Fin15AnchoredAtom2406 Fin15AnchoredAtom2480 Fin15AnchoredAtom2515
    Fin15AnchoredAtom2517 Fin15AnchoredAtom2526 Fin15AnchoredAtom2600 Fin15AnchoredAtom2684
    Fin15AnchoredAtom3045 Fin15AnchoredAtom3048 Fin15AnchoredAtom3050 Fin15AnchoredAtom3074
    Fin15AnchoredAtom3076 Fin15AnchoredAtom3085 Fin15AnchoredAtom3110 Fin15AnchoredAtom3112
    Fin15AnchoredAtom3121 Fin15AnchoredAtom3195 Fin15AnchoredAtom3230 Fin15AnchoredAtom3232
    Fin15AnchoredAtom3241 Fin15AnchoredAtom3315 Fin15AnchoredAtom3399 Fin15AnchoredAtom4055
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

theorem fin15Anchored_clause30811 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
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
      ¬Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom3050 chi ∧
      ¬Fin15AnchoredAtom3075 chi ∧
      ¬Fin15AnchoredAtom3076 chi ∧
      ¬Fin15AnchoredAtom3086 chi ∧
      ¬Fin15AnchoredAtom3111 chi ∧
      ¬Fin15AnchoredAtom3112 chi ∧
      ¬Fin15AnchoredAtom3122 chi ∧
      ¬Fin15AnchoredAtom3196 chi ∧
      ¬Fin15AnchoredAtom3231 chi ∧
      ¬Fin15AnchoredAtom3232 chi ∧
      ¬Fin15AnchoredAtom3242 chi ∧
      ¬Fin15AnchoredAtom3316 chi ∧
      ¬Fin15AnchoredAtom3400 chi ∧
      ¬Fin15AnchoredAtom4056 chi ∧
      ¬Fin15AnchoredAtom4057 chi ∧
      ¬Fin15AnchoredAtom4067 chi ∧
      ¬Fin15AnchoredAtom4141 chi ∧
      ¬Fin15AnchoredAtom4225 chi ∧
      ¬Fin15AnchoredAtom4435 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 5, 9, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25147
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1887 Fin15AnchoredAtom1891 Fin15AnchoredAtom1895
    Fin15AnchoredAtom1896 Fin15AnchoredAtom1900 Fin15AnchoredAtom1904 Fin15AnchoredAtom1905
    Fin15AnchoredAtom1930 Fin15AnchoredAtom1931 Fin15AnchoredAtom1941 Fin15AnchoredAtom1945
    Fin15AnchoredAtom1949 Fin15AnchoredAtom1950 Fin15AnchoredAtom1975 Fin15AnchoredAtom1976
    Fin15AnchoredAtom1986 Fin15AnchoredAtom2011 Fin15AnchoredAtom2012 Fin15AnchoredAtom2022
    Fin15AnchoredAtom2096 Fin15AnchoredAtom2330 Fin15AnchoredAtom2334 Fin15AnchoredAtom2335
    Fin15AnchoredAtom2360 Fin15AnchoredAtom2361 Fin15AnchoredAtom2371 Fin15AnchoredAtom2396
    Fin15AnchoredAtom2397 Fin15AnchoredAtom2407 Fin15AnchoredAtom2481 Fin15AnchoredAtom2516
    Fin15AnchoredAtom2517 Fin15AnchoredAtom2527 Fin15AnchoredAtom2601 Fin15AnchoredAtom2685
    Fin15AnchoredAtom3045 Fin15AnchoredAtom3049 Fin15AnchoredAtom3050 Fin15AnchoredAtom3075
    Fin15AnchoredAtom3076 Fin15AnchoredAtom3086 Fin15AnchoredAtom3111 Fin15AnchoredAtom3112
    Fin15AnchoredAtom3122 Fin15AnchoredAtom3196 Fin15AnchoredAtom3231 Fin15AnchoredAtom3232
    Fin15AnchoredAtom3242 Fin15AnchoredAtom3316 Fin15AnchoredAtom3400 Fin15AnchoredAtom4056
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

theorem fin15Anchored_clause30812 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1893 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1902 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1932 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom1936 chi ∧
      ¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1947 chi ∧
      ¬Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom1977 chi ∧
      ¬Fin15AnchoredAtom1978 chi ∧
      ¬Fin15AnchoredAtom1981 chi ∧
      ¬Fin15AnchoredAtom2013 chi ∧
      ¬Fin15AnchoredAtom2014 chi ∧
      ¬Fin15AnchoredAtom2017 chi ∧
      ¬Fin15AnchoredAtom2097 chi ∧
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
      ¬Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom3047 chi ∧
      ¬Fin15AnchoredAtom3048 chi ∧
      ¬Fin15AnchoredAtom3077 chi ∧
      ¬Fin15AnchoredAtom3078 chi ∧
      ¬Fin15AnchoredAtom3081 chi ∧
      ¬Fin15AnchoredAtom3113 chi ∧
      ¬Fin15AnchoredAtom3114 chi ∧
      ¬Fin15AnchoredAtom3117 chi ∧
      ¬Fin15AnchoredAtom3197 chi ∧
      ¬Fin15AnchoredAtom3233 chi ∧
      ¬Fin15AnchoredAtom3234 chi ∧
      ¬Fin15AnchoredAtom3237 chi ∧
      ¬Fin15AnchoredAtom3317 chi ∧
      ¬Fin15AnchoredAtom3401 chi ∧
      ¬Fin15AnchoredAtom4058 chi ∧
      ¬Fin15AnchoredAtom4059 chi ∧
      ¬Fin15AnchoredAtom4062 chi ∧
      ¬Fin15AnchoredAtom4142 chi ∧
      ¬Fin15AnchoredAtom4226 chi ∧
      ¬Fin15AnchoredAtom4436 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 5, 10, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask07227
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1887 Fin15AnchoredAtom1892 Fin15AnchoredAtom1893
    Fin15AnchoredAtom1894 Fin15AnchoredAtom1901 Fin15AnchoredAtom1902 Fin15AnchoredAtom1903
    Fin15AnchoredAtom1932 Fin15AnchoredAtom1933 Fin15AnchoredAtom1936 Fin15AnchoredAtom1946
    Fin15AnchoredAtom1947 Fin15AnchoredAtom1948 Fin15AnchoredAtom1977 Fin15AnchoredAtom1978
    Fin15AnchoredAtom1981 Fin15AnchoredAtom2013 Fin15AnchoredAtom2014 Fin15AnchoredAtom2017
    Fin15AnchoredAtom2097 Fin15AnchoredAtom2331 Fin15AnchoredAtom2332 Fin15AnchoredAtom2333
    Fin15AnchoredAtom2362 Fin15AnchoredAtom2363 Fin15AnchoredAtom2366 Fin15AnchoredAtom2398
    Fin15AnchoredAtom2399 Fin15AnchoredAtom2402 Fin15AnchoredAtom2482 Fin15AnchoredAtom2518
    Fin15AnchoredAtom2519 Fin15AnchoredAtom2522 Fin15AnchoredAtom2602 Fin15AnchoredAtom2686
    Fin15AnchoredAtom3046 Fin15AnchoredAtom3047 Fin15AnchoredAtom3048 Fin15AnchoredAtom3077
    Fin15AnchoredAtom3078 Fin15AnchoredAtom3081 Fin15AnchoredAtom3113 Fin15AnchoredAtom3114
    Fin15AnchoredAtom3117 Fin15AnchoredAtom3197 Fin15AnchoredAtom3233 Fin15AnchoredAtom3234
    Fin15AnchoredAtom3237 Fin15AnchoredAtom3317 Fin15AnchoredAtom3401 Fin15AnchoredAtom4058
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

theorem fin15Anchored_clause30813 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom1939 chi ∧
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
      ¬Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom3048 chi ∧
      ¬Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom3078 chi ∧
      ¬Fin15AnchoredAtom3079 chi ∧
      ¬Fin15AnchoredAtom3084 chi ∧
      ¬Fin15AnchoredAtom3114 chi ∧
      ¬Fin15AnchoredAtom3115 chi ∧
      ¬Fin15AnchoredAtom3120 chi ∧
      ¬Fin15AnchoredAtom3200 chi ∧
      ¬Fin15AnchoredAtom3234 chi ∧
      ¬Fin15AnchoredAtom3235 chi ∧
      ¬Fin15AnchoredAtom3240 chi ∧
      ¬Fin15AnchoredAtom3320 chi ∧
      ¬Fin15AnchoredAtom3404 chi ∧
      ¬Fin15AnchoredAtom4059 chi ∧
      ¬Fin15AnchoredAtom4060 chi ∧
      ¬Fin15AnchoredAtom4065 chi ∧
      ¬Fin15AnchoredAtom4145 chi ∧
      ¬Fin15AnchoredAtom4229 chi ∧
      ¬Fin15AnchoredAtom4439 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 5, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13371
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1887 Fin15AnchoredAtom1892 Fin15AnchoredAtom1894
    Fin15AnchoredAtom1895 Fin15AnchoredAtom1901 Fin15AnchoredAtom1903 Fin15AnchoredAtom1904
    Fin15AnchoredAtom1933 Fin15AnchoredAtom1934 Fin15AnchoredAtom1939 Fin15AnchoredAtom1946
    Fin15AnchoredAtom1948 Fin15AnchoredAtom1949 Fin15AnchoredAtom1978 Fin15AnchoredAtom1979
    Fin15AnchoredAtom1984 Fin15AnchoredAtom2014 Fin15AnchoredAtom2015 Fin15AnchoredAtom2020
    Fin15AnchoredAtom2100 Fin15AnchoredAtom2331 Fin15AnchoredAtom2333 Fin15AnchoredAtom2334
    Fin15AnchoredAtom2363 Fin15AnchoredAtom2364 Fin15AnchoredAtom2369 Fin15AnchoredAtom2399
    Fin15AnchoredAtom2400 Fin15AnchoredAtom2405 Fin15AnchoredAtom2485 Fin15AnchoredAtom2519
    Fin15AnchoredAtom2520 Fin15AnchoredAtom2525 Fin15AnchoredAtom2605 Fin15AnchoredAtom2689
    Fin15AnchoredAtom3046 Fin15AnchoredAtom3048 Fin15AnchoredAtom3049 Fin15AnchoredAtom3078
    Fin15AnchoredAtom3079 Fin15AnchoredAtom3084 Fin15AnchoredAtom3114 Fin15AnchoredAtom3115
    Fin15AnchoredAtom3120 Fin15AnchoredAtom3200 Fin15AnchoredAtom3234 Fin15AnchoredAtom3235
    Fin15AnchoredAtom3240 Fin15AnchoredAtom3320 Fin15AnchoredAtom3404 Fin15AnchoredAtom4059
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

theorem fin15Anchored_clause30814 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom1935 chi ∧
      ¬Fin15AnchoredAtom1940 chi ∧
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
      ¬Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom3048 chi ∧
      ¬Fin15AnchoredAtom3050 chi ∧
      ¬Fin15AnchoredAtom3078 chi ∧
      ¬Fin15AnchoredAtom3080 chi ∧
      ¬Fin15AnchoredAtom3085 chi ∧
      ¬Fin15AnchoredAtom3114 chi ∧
      ¬Fin15AnchoredAtom3116 chi ∧
      ¬Fin15AnchoredAtom3121 chi ∧
      ¬Fin15AnchoredAtom3201 chi ∧
      ¬Fin15AnchoredAtom3234 chi ∧
      ¬Fin15AnchoredAtom3236 chi ∧
      ¬Fin15AnchoredAtom3241 chi ∧
      ¬Fin15AnchoredAtom3321 chi ∧
      ¬Fin15AnchoredAtom3405 chi ∧
      ¬Fin15AnchoredAtom4059 chi ∧
      ¬Fin15AnchoredAtom4061 chi ∧
      ¬Fin15AnchoredAtom4066 chi ∧
      ¬Fin15AnchoredAtom4146 chi ∧
      ¬Fin15AnchoredAtom4230 chi ∧
      ¬Fin15AnchoredAtom4440 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 5, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21563
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1887 Fin15AnchoredAtom1892 Fin15AnchoredAtom1894
    Fin15AnchoredAtom1896 Fin15AnchoredAtom1901 Fin15AnchoredAtom1903 Fin15AnchoredAtom1905
    Fin15AnchoredAtom1933 Fin15AnchoredAtom1935 Fin15AnchoredAtom1940 Fin15AnchoredAtom1946
    Fin15AnchoredAtom1948 Fin15AnchoredAtom1950 Fin15AnchoredAtom1978 Fin15AnchoredAtom1980
    Fin15AnchoredAtom1985 Fin15AnchoredAtom2014 Fin15AnchoredAtom2016 Fin15AnchoredAtom2021
    Fin15AnchoredAtom2101 Fin15AnchoredAtom2331 Fin15AnchoredAtom2333 Fin15AnchoredAtom2335
    Fin15AnchoredAtom2363 Fin15AnchoredAtom2365 Fin15AnchoredAtom2370 Fin15AnchoredAtom2399
    Fin15AnchoredAtom2401 Fin15AnchoredAtom2406 Fin15AnchoredAtom2486 Fin15AnchoredAtom2519
    Fin15AnchoredAtom2521 Fin15AnchoredAtom2526 Fin15AnchoredAtom2606 Fin15AnchoredAtom2690
    Fin15AnchoredAtom3046 Fin15AnchoredAtom3048 Fin15AnchoredAtom3050 Fin15AnchoredAtom3078
    Fin15AnchoredAtom3080 Fin15AnchoredAtom3085 Fin15AnchoredAtom3114 Fin15AnchoredAtom3116
    Fin15AnchoredAtom3121 Fin15AnchoredAtom3201 Fin15AnchoredAtom3234 Fin15AnchoredAtom3236
    Fin15AnchoredAtom3241 Fin15AnchoredAtom3321 Fin15AnchoredAtom3405 Fin15AnchoredAtom4059
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

theorem fin15Anchored_clause30815 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom1935 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
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
      ¬Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom3050 chi ∧
      ¬Fin15AnchoredAtom3079 chi ∧
      ¬Fin15AnchoredAtom3080 chi ∧
      ¬Fin15AnchoredAtom3086 chi ∧
      ¬Fin15AnchoredAtom3115 chi ∧
      ¬Fin15AnchoredAtom3116 chi ∧
      ¬Fin15AnchoredAtom3122 chi ∧
      ¬Fin15AnchoredAtom3202 chi ∧
      ¬Fin15AnchoredAtom3235 chi ∧
      ¬Fin15AnchoredAtom3236 chi ∧
      ¬Fin15AnchoredAtom3242 chi ∧
      ¬Fin15AnchoredAtom3322 chi ∧
      ¬Fin15AnchoredAtom3406 chi ∧
      ¬Fin15AnchoredAtom4060 chi ∧
      ¬Fin15AnchoredAtom4061 chi ∧
      ¬Fin15AnchoredAtom4067 chi ∧
      ¬Fin15AnchoredAtom4147 chi ∧
      ¬Fin15AnchoredAtom4231 chi ∧
      ¬Fin15AnchoredAtom4441 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 5, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25659
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1887 Fin15AnchoredAtom1892 Fin15AnchoredAtom1895
    Fin15AnchoredAtom1896 Fin15AnchoredAtom1901 Fin15AnchoredAtom1904 Fin15AnchoredAtom1905
    Fin15AnchoredAtom1934 Fin15AnchoredAtom1935 Fin15AnchoredAtom1941 Fin15AnchoredAtom1946
    Fin15AnchoredAtom1949 Fin15AnchoredAtom1950 Fin15AnchoredAtom1979 Fin15AnchoredAtom1980
    Fin15AnchoredAtom1986 Fin15AnchoredAtom2015 Fin15AnchoredAtom2016 Fin15AnchoredAtom2022
    Fin15AnchoredAtom2102 Fin15AnchoredAtom2331 Fin15AnchoredAtom2334 Fin15AnchoredAtom2335
    Fin15AnchoredAtom2364 Fin15AnchoredAtom2365 Fin15AnchoredAtom2371 Fin15AnchoredAtom2400
    Fin15AnchoredAtom2401 Fin15AnchoredAtom2407 Fin15AnchoredAtom2487 Fin15AnchoredAtom2520
    Fin15AnchoredAtom2521 Fin15AnchoredAtom2527 Fin15AnchoredAtom2607 Fin15AnchoredAtom2691
    Fin15AnchoredAtom3046 Fin15AnchoredAtom3049 Fin15AnchoredAtom3050 Fin15AnchoredAtom3079
    Fin15AnchoredAtom3080 Fin15AnchoredAtom3086 Fin15AnchoredAtom3115 Fin15AnchoredAtom3116
    Fin15AnchoredAtom3122 Fin15AnchoredAtom3202 Fin15AnchoredAtom3235 Fin15AnchoredAtom3236
    Fin15AnchoredAtom3242 Fin15AnchoredAtom3322 Fin15AnchoredAtom3406 Fin15AnchoredAtom4060
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

theorem fin15Anchored_clause30816 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1939 chi ∧
      ¬Fin15AnchoredAtom1940 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
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
      ¬Fin15AnchoredAtom3048 chi ∧
      ¬Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom3050 chi ∧
      ¬Fin15AnchoredAtom3084 chi ∧
      ¬Fin15AnchoredAtom3085 chi ∧
      ¬Fin15AnchoredAtom3086 chi ∧
      ¬Fin15AnchoredAtom3120 chi ∧
      ¬Fin15AnchoredAtom3121 chi ∧
      ¬Fin15AnchoredAtom3122 chi ∧
      ¬Fin15AnchoredAtom3206 chi ∧
      ¬Fin15AnchoredAtom3240 chi ∧
      ¬Fin15AnchoredAtom3241 chi ∧
      ¬Fin15AnchoredAtom3242 chi ∧
      ¬Fin15AnchoredAtom3326 chi ∧
      ¬Fin15AnchoredAtom3410 chi ∧
      ¬Fin15AnchoredAtom4065 chi ∧
      ¬Fin15AnchoredAtom4066 chi ∧
      ¬Fin15AnchoredAtom4067 chi ∧
      ¬Fin15AnchoredAtom4151 chi ∧
      ¬Fin15AnchoredAtom4235 chi ∧
      ¬Fin15AnchoredAtom4445 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 5, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask28731
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1887 Fin15AnchoredAtom1894 Fin15AnchoredAtom1895
    Fin15AnchoredAtom1896 Fin15AnchoredAtom1903 Fin15AnchoredAtom1904 Fin15AnchoredAtom1905
    Fin15AnchoredAtom1939 Fin15AnchoredAtom1940 Fin15AnchoredAtom1941 Fin15AnchoredAtom1948
    Fin15AnchoredAtom1949 Fin15AnchoredAtom1950 Fin15AnchoredAtom1984 Fin15AnchoredAtom1985
    Fin15AnchoredAtom1986 Fin15AnchoredAtom2020 Fin15AnchoredAtom2021 Fin15AnchoredAtom2022
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2333 Fin15AnchoredAtom2334 Fin15AnchoredAtom2335
    Fin15AnchoredAtom2369 Fin15AnchoredAtom2370 Fin15AnchoredAtom2371 Fin15AnchoredAtom2405
    Fin15AnchoredAtom2406 Fin15AnchoredAtom2407 Fin15AnchoredAtom2491 Fin15AnchoredAtom2525
    Fin15AnchoredAtom2526 Fin15AnchoredAtom2527 Fin15AnchoredAtom2611 Fin15AnchoredAtom2695
    Fin15AnchoredAtom3048 Fin15AnchoredAtom3049 Fin15AnchoredAtom3050 Fin15AnchoredAtom3084
    Fin15AnchoredAtom3085 Fin15AnchoredAtom3086 Fin15AnchoredAtom3120 Fin15AnchoredAtom3121
    Fin15AnchoredAtom3122 Fin15AnchoredAtom3206 Fin15AnchoredAtom3240 Fin15AnchoredAtom3241
    Fin15AnchoredAtom3242 Fin15AnchoredAtom3326 Fin15AnchoredAtom3410 Fin15AnchoredAtom4065
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

theorem fin15Anchored_clause30817 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1890 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1907 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1914 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1921 chi ∧
      ¬Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom1952 chi ∧
      ¬Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom1959 chi ∧
      ¬Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom1966 chi ∧
      ¬Fin15AnchoredAtom2023 chi ∧
      ¬Fin15AnchoredAtom2024 chi ∧
      ¬Fin15AnchoredAtom2030 chi ∧
      ¬Fin15AnchoredAtom2051 chi ∧
      ¬Fin15AnchoredAtom2336 chi ∧
      ¬Fin15AnchoredAtom2337 chi ∧
      ¬Fin15AnchoredAtom2338 chi ∧
      ¬Fin15AnchoredAtom2344 chi ∧
      ¬Fin15AnchoredAtom2345 chi ∧
      ¬Fin15AnchoredAtom2351 chi ∧
      ¬Fin15AnchoredAtom2408 chi ∧
      ¬Fin15AnchoredAtom2409 chi ∧
      ¬Fin15AnchoredAtom2415 chi ∧
      ¬Fin15AnchoredAtom2436 chi ∧
      ¬Fin15AnchoredAtom2528 chi ∧
      ¬Fin15AnchoredAtom2529 chi ∧
      ¬Fin15AnchoredAtom2535 chi ∧
      ¬Fin15AnchoredAtom2556 chi ∧
      ¬Fin15AnchoredAtom2696 chi ∧
      ¬Fin15AnchoredAtom3051 chi ∧
      ¬Fin15AnchoredAtom3052 chi ∧
      ¬Fin15AnchoredAtom3053 chi ∧
      ¬Fin15AnchoredAtom3059 chi ∧
      ¬Fin15AnchoredAtom3060 chi ∧
      ¬Fin15AnchoredAtom3066 chi ∧
      ¬Fin15AnchoredAtom3123 chi ∧
      ¬Fin15AnchoredAtom3124 chi ∧
      ¬Fin15AnchoredAtom3130 chi ∧
      ¬Fin15AnchoredAtom3151 chi ∧
      ¬Fin15AnchoredAtom3243 chi ∧
      ¬Fin15AnchoredAtom3244 chi ∧
      ¬Fin15AnchoredAtom3250 chi ∧
      ¬Fin15AnchoredAtom3271 chi ∧
      ¬Fin15AnchoredAtom3411 chi ∧
      ¬Fin15AnchoredAtom4068 chi ∧
      ¬Fin15AnchoredAtom4069 chi ∧
      ¬Fin15AnchoredAtom4075 chi ∧
      ¬Fin15AnchoredAtom4096 chi ∧
      ¬Fin15AnchoredAtom4236 chi ∧
      ¬Fin15AnchoredAtom4446 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 6, 7, 8, 9}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask00987
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1888 Fin15AnchoredAtom1889 Fin15AnchoredAtom1890
    Fin15AnchoredAtom1891 Fin15AnchoredAtom1906 Fin15AnchoredAtom1907 Fin15AnchoredAtom1908
    Fin15AnchoredAtom1914 Fin15AnchoredAtom1915 Fin15AnchoredAtom1921 Fin15AnchoredAtom1951
    Fin15AnchoredAtom1952 Fin15AnchoredAtom1953 Fin15AnchoredAtom1959 Fin15AnchoredAtom1960
    Fin15AnchoredAtom1966 Fin15AnchoredAtom2023 Fin15AnchoredAtom2024 Fin15AnchoredAtom2030
    Fin15AnchoredAtom2051 Fin15AnchoredAtom2336 Fin15AnchoredAtom2337 Fin15AnchoredAtom2338
    Fin15AnchoredAtom2344 Fin15AnchoredAtom2345 Fin15AnchoredAtom2351 Fin15AnchoredAtom2408
    Fin15AnchoredAtom2409 Fin15AnchoredAtom2415 Fin15AnchoredAtom2436 Fin15AnchoredAtom2528
    Fin15AnchoredAtom2529 Fin15AnchoredAtom2535 Fin15AnchoredAtom2556 Fin15AnchoredAtom2696
    Fin15AnchoredAtom3051 Fin15AnchoredAtom3052 Fin15AnchoredAtom3053 Fin15AnchoredAtom3059
    Fin15AnchoredAtom3060 Fin15AnchoredAtom3066 Fin15AnchoredAtom3123 Fin15AnchoredAtom3124
    Fin15AnchoredAtom3130 Fin15AnchoredAtom3151 Fin15AnchoredAtom3243 Fin15AnchoredAtom3244
    Fin15AnchoredAtom3250 Fin15AnchoredAtom3271 Fin15AnchoredAtom3411 Fin15AnchoredAtom4068
    Fin15AnchoredAtom4069 Fin15AnchoredAtom4075 Fin15AnchoredAtom4096 Fin15AnchoredAtom4236
    Fin15AnchoredAtom4446 at hbad
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

theorem fin15Anchored_clause30818 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1890 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1907 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1914 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1925 chi ∧
      ¬Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom1952 chi ∧
      ¬Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom1959 chi ∧
      ¬Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom1970 chi ∧
      ¬Fin15AnchoredAtom2023 chi ∧
      ¬Fin15AnchoredAtom2028 chi ∧
      ¬Fin15AnchoredAtom2034 chi ∧
      ¬Fin15AnchoredAtom2055 chi ∧
      ¬Fin15AnchoredAtom2336 chi ∧
      ¬Fin15AnchoredAtom2337 chi ∧
      ¬Fin15AnchoredAtom2342 chi ∧
      ¬Fin15AnchoredAtom2344 chi ∧
      ¬Fin15AnchoredAtom2349 chi ∧
      ¬Fin15AnchoredAtom2355 chi ∧
      ¬Fin15AnchoredAtom2408 chi ∧
      ¬Fin15AnchoredAtom2413 chi ∧
      ¬Fin15AnchoredAtom2419 chi ∧
      ¬Fin15AnchoredAtom2440 chi ∧
      ¬Fin15AnchoredAtom2528 chi ∧
      ¬Fin15AnchoredAtom2533 chi ∧
      ¬Fin15AnchoredAtom2539 chi ∧
      ¬Fin15AnchoredAtom2560 chi ∧
      ¬Fin15AnchoredAtom2700 chi ∧
      ¬Fin15AnchoredAtom3051 chi ∧
      ¬Fin15AnchoredAtom3052 chi ∧
      ¬Fin15AnchoredAtom3057 chi ∧
      ¬Fin15AnchoredAtom3059 chi ∧
      ¬Fin15AnchoredAtom3064 chi ∧
      ¬Fin15AnchoredAtom3070 chi ∧
      ¬Fin15AnchoredAtom3123 chi ∧
      ¬Fin15AnchoredAtom3128 chi ∧
      ¬Fin15AnchoredAtom3134 chi ∧
      ¬Fin15AnchoredAtom3155 chi ∧
      ¬Fin15AnchoredAtom3243 chi ∧
      ¬Fin15AnchoredAtom3248 chi ∧
      ¬Fin15AnchoredAtom3254 chi ∧
      ¬Fin15AnchoredAtom3275 chi ∧
      ¬Fin15AnchoredAtom3415 chi ∧
      ¬Fin15AnchoredAtom4068 chi ∧
      ¬Fin15AnchoredAtom4073 chi ∧
      ¬Fin15AnchoredAtom4079 chi ∧
      ¬Fin15AnchoredAtom4100 chi ∧
      ¬Fin15AnchoredAtom4240 chi ∧
      ¬Fin15AnchoredAtom4450 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 6, 7, 8, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask08667
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1888 Fin15AnchoredAtom1889 Fin15AnchoredAtom1890
    Fin15AnchoredAtom1895 Fin15AnchoredAtom1906 Fin15AnchoredAtom1907 Fin15AnchoredAtom1912
    Fin15AnchoredAtom1914 Fin15AnchoredAtom1919 Fin15AnchoredAtom1925 Fin15AnchoredAtom1951
    Fin15AnchoredAtom1952 Fin15AnchoredAtom1957 Fin15AnchoredAtom1959 Fin15AnchoredAtom1964
    Fin15AnchoredAtom1970 Fin15AnchoredAtom2023 Fin15AnchoredAtom2028 Fin15AnchoredAtom2034
    Fin15AnchoredAtom2055 Fin15AnchoredAtom2336 Fin15AnchoredAtom2337 Fin15AnchoredAtom2342
    Fin15AnchoredAtom2344 Fin15AnchoredAtom2349 Fin15AnchoredAtom2355 Fin15AnchoredAtom2408
    Fin15AnchoredAtom2413 Fin15AnchoredAtom2419 Fin15AnchoredAtom2440 Fin15AnchoredAtom2528
    Fin15AnchoredAtom2533 Fin15AnchoredAtom2539 Fin15AnchoredAtom2560 Fin15AnchoredAtom2700
    Fin15AnchoredAtom3051 Fin15AnchoredAtom3052 Fin15AnchoredAtom3057 Fin15AnchoredAtom3059
    Fin15AnchoredAtom3064 Fin15AnchoredAtom3070 Fin15AnchoredAtom3123 Fin15AnchoredAtom3128
    Fin15AnchoredAtom3134 Fin15AnchoredAtom3155 Fin15AnchoredAtom3243 Fin15AnchoredAtom3248
    Fin15AnchoredAtom3254 Fin15AnchoredAtom3275 Fin15AnchoredAtom3415 Fin15AnchoredAtom4068
    Fin15AnchoredAtom4073 Fin15AnchoredAtom4079 Fin15AnchoredAtom4100 Fin15AnchoredAtom4240
    Fin15AnchoredAtom4450 at hbad
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

theorem fin15Anchored_clause30819 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1890 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1907 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1914 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1926 chi ∧
      ¬Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom1952 chi ∧
      ¬Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom1959 chi ∧
      ¬Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom1971 chi ∧
      ¬Fin15AnchoredAtom2023 chi ∧
      ¬Fin15AnchoredAtom2029 chi ∧
      ¬Fin15AnchoredAtom2035 chi ∧
      ¬Fin15AnchoredAtom2056 chi ∧
      ¬Fin15AnchoredAtom2336 chi ∧
      ¬Fin15AnchoredAtom2337 chi ∧
      ¬Fin15AnchoredAtom2343 chi ∧
      ¬Fin15AnchoredAtom2344 chi ∧
      ¬Fin15AnchoredAtom2350 chi ∧
      ¬Fin15AnchoredAtom2356 chi ∧
      ¬Fin15AnchoredAtom2408 chi ∧
      ¬Fin15AnchoredAtom2414 chi ∧
      ¬Fin15AnchoredAtom2420 chi ∧
      ¬Fin15AnchoredAtom2441 chi ∧
      ¬Fin15AnchoredAtom2528 chi ∧
      ¬Fin15AnchoredAtom2534 chi ∧
      ¬Fin15AnchoredAtom2540 chi ∧
      ¬Fin15AnchoredAtom2561 chi ∧
      ¬Fin15AnchoredAtom2701 chi ∧
      ¬Fin15AnchoredAtom3051 chi ∧
      ¬Fin15AnchoredAtom3052 chi ∧
      ¬Fin15AnchoredAtom3058 chi ∧
      ¬Fin15AnchoredAtom3059 chi ∧
      ¬Fin15AnchoredAtom3065 chi ∧
      ¬Fin15AnchoredAtom3071 chi ∧
      ¬Fin15AnchoredAtom3123 chi ∧
      ¬Fin15AnchoredAtom3129 chi ∧
      ¬Fin15AnchoredAtom3135 chi ∧
      ¬Fin15AnchoredAtom3156 chi ∧
      ¬Fin15AnchoredAtom3243 chi ∧
      ¬Fin15AnchoredAtom3249 chi ∧
      ¬Fin15AnchoredAtom3255 chi ∧
      ¬Fin15AnchoredAtom3276 chi ∧
      ¬Fin15AnchoredAtom3416 chi ∧
      ¬Fin15AnchoredAtom4068 chi ∧
      ¬Fin15AnchoredAtom4074 chi ∧
      ¬Fin15AnchoredAtom4080 chi ∧
      ¬Fin15AnchoredAtom4101 chi ∧
      ¬Fin15AnchoredAtom4241 chi ∧
      ¬Fin15AnchoredAtom4451 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 6, 7, 8, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask16859
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1888 Fin15AnchoredAtom1889 Fin15AnchoredAtom1890
    Fin15AnchoredAtom1896 Fin15AnchoredAtom1906 Fin15AnchoredAtom1907 Fin15AnchoredAtom1913
    Fin15AnchoredAtom1914 Fin15AnchoredAtom1920 Fin15AnchoredAtom1926 Fin15AnchoredAtom1951
    Fin15AnchoredAtom1952 Fin15AnchoredAtom1958 Fin15AnchoredAtom1959 Fin15AnchoredAtom1965
    Fin15AnchoredAtom1971 Fin15AnchoredAtom2023 Fin15AnchoredAtom2029 Fin15AnchoredAtom2035
    Fin15AnchoredAtom2056 Fin15AnchoredAtom2336 Fin15AnchoredAtom2337 Fin15AnchoredAtom2343
    Fin15AnchoredAtom2344 Fin15AnchoredAtom2350 Fin15AnchoredAtom2356 Fin15AnchoredAtom2408
    Fin15AnchoredAtom2414 Fin15AnchoredAtom2420 Fin15AnchoredAtom2441 Fin15AnchoredAtom2528
    Fin15AnchoredAtom2534 Fin15AnchoredAtom2540 Fin15AnchoredAtom2561 Fin15AnchoredAtom2701
    Fin15AnchoredAtom3051 Fin15AnchoredAtom3052 Fin15AnchoredAtom3058 Fin15AnchoredAtom3059
    Fin15AnchoredAtom3065 Fin15AnchoredAtom3071 Fin15AnchoredAtom3123 Fin15AnchoredAtom3129
    Fin15AnchoredAtom3135 Fin15AnchoredAtom3156 Fin15AnchoredAtom3243 Fin15AnchoredAtom3249
    Fin15AnchoredAtom3255 Fin15AnchoredAtom3276 Fin15AnchoredAtom3416 Fin15AnchoredAtom4068
    Fin15AnchoredAtom4074 Fin15AnchoredAtom4080 Fin15AnchoredAtom4101 Fin15AnchoredAtom4241
    Fin15AnchoredAtom4451 at hbad
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

theorem fin15Anchored_clause30820 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
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
      ¬Fin15AnchoredAtom3051 chi ∧
      ¬Fin15AnchoredAtom3053 chi ∧
      ¬Fin15AnchoredAtom3054 chi ∧
      ¬Fin15AnchoredAtom3060 chi ∧
      ¬Fin15AnchoredAtom3061 chi ∧
      ¬Fin15AnchoredAtom3072 chi ∧
      ¬Fin15AnchoredAtom3124 chi ∧
      ¬Fin15AnchoredAtom3125 chi ∧
      ¬Fin15AnchoredAtom3136 chi ∧
      ¬Fin15AnchoredAtom3157 chi ∧
      ¬Fin15AnchoredAtom3244 chi ∧
      ¬Fin15AnchoredAtom3245 chi ∧
      ¬Fin15AnchoredAtom3256 chi ∧
      ¬Fin15AnchoredAtom3277 chi ∧
      ¬Fin15AnchoredAtom3417 chi ∧
      ¬Fin15AnchoredAtom4069 chi ∧
      ¬Fin15AnchoredAtom4070 chi ∧
      ¬Fin15AnchoredAtom4081 chi ∧
      ¬Fin15AnchoredAtom4102 chi ∧
      ¬Fin15AnchoredAtom4242 chi ∧
      ¬Fin15AnchoredAtom4452 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 6, 7, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask01755
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1888 Fin15AnchoredAtom1889 Fin15AnchoredAtom1891
    Fin15AnchoredAtom1892 Fin15AnchoredAtom1906 Fin15AnchoredAtom1908 Fin15AnchoredAtom1909
    Fin15AnchoredAtom1915 Fin15AnchoredAtom1916 Fin15AnchoredAtom1927 Fin15AnchoredAtom1951
    Fin15AnchoredAtom1953 Fin15AnchoredAtom1954 Fin15AnchoredAtom1960 Fin15AnchoredAtom1961
    Fin15AnchoredAtom1972 Fin15AnchoredAtom2024 Fin15AnchoredAtom2025 Fin15AnchoredAtom2036
    Fin15AnchoredAtom2057 Fin15AnchoredAtom2336 Fin15AnchoredAtom2338 Fin15AnchoredAtom2339
    Fin15AnchoredAtom2345 Fin15AnchoredAtom2346 Fin15AnchoredAtom2357 Fin15AnchoredAtom2409
    Fin15AnchoredAtom2410 Fin15AnchoredAtom2421 Fin15AnchoredAtom2442 Fin15AnchoredAtom2529
    Fin15AnchoredAtom2530 Fin15AnchoredAtom2541 Fin15AnchoredAtom2562 Fin15AnchoredAtom2702
    Fin15AnchoredAtom3051 Fin15AnchoredAtom3053 Fin15AnchoredAtom3054 Fin15AnchoredAtom3060
    Fin15AnchoredAtom3061 Fin15AnchoredAtom3072 Fin15AnchoredAtom3124 Fin15AnchoredAtom3125
    Fin15AnchoredAtom3136 Fin15AnchoredAtom3157 Fin15AnchoredAtom3244 Fin15AnchoredAtom3245
    Fin15AnchoredAtom3256 Fin15AnchoredAtom3277 Fin15AnchoredAtom3417 Fin15AnchoredAtom4069
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

theorem fin15Anchored_clause30821 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
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
      ¬Fin15AnchoredAtom3051 chi ∧
      ¬Fin15AnchoredAtom3053 chi ∧
      ¬Fin15AnchoredAtom3056 chi ∧
      ¬Fin15AnchoredAtom3060 chi ∧
      ¬Fin15AnchoredAtom3063 chi ∧
      ¬Fin15AnchoredAtom3074 chi ∧
      ¬Fin15AnchoredAtom3124 chi ∧
      ¬Fin15AnchoredAtom3127 chi ∧
      ¬Fin15AnchoredAtom3138 chi ∧
      ¬Fin15AnchoredAtom3159 chi ∧
      ¬Fin15AnchoredAtom3244 chi ∧
      ¬Fin15AnchoredAtom3247 chi ∧
      ¬Fin15AnchoredAtom3258 chi ∧
      ¬Fin15AnchoredAtom3279 chi ∧
      ¬Fin15AnchoredAtom3419 chi ∧
      ¬Fin15AnchoredAtom4069 chi ∧
      ¬Fin15AnchoredAtom4072 chi ∧
      ¬Fin15AnchoredAtom4083 chi ∧
      ¬Fin15AnchoredAtom4104 chi ∧
      ¬Fin15AnchoredAtom4244 chi ∧
      ¬Fin15AnchoredAtom4454 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 6, 7, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask04827
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1888 Fin15AnchoredAtom1889 Fin15AnchoredAtom1891
    Fin15AnchoredAtom1894 Fin15AnchoredAtom1906 Fin15AnchoredAtom1908 Fin15AnchoredAtom1911
    Fin15AnchoredAtom1915 Fin15AnchoredAtom1918 Fin15AnchoredAtom1929 Fin15AnchoredAtom1951
    Fin15AnchoredAtom1953 Fin15AnchoredAtom1956 Fin15AnchoredAtom1960 Fin15AnchoredAtom1963
    Fin15AnchoredAtom1974 Fin15AnchoredAtom2024 Fin15AnchoredAtom2027 Fin15AnchoredAtom2038
    Fin15AnchoredAtom2059 Fin15AnchoredAtom2336 Fin15AnchoredAtom2338 Fin15AnchoredAtom2341
    Fin15AnchoredAtom2345 Fin15AnchoredAtom2348 Fin15AnchoredAtom2359 Fin15AnchoredAtom2409
    Fin15AnchoredAtom2412 Fin15AnchoredAtom2423 Fin15AnchoredAtom2444 Fin15AnchoredAtom2529
    Fin15AnchoredAtom2532 Fin15AnchoredAtom2543 Fin15AnchoredAtom2564 Fin15AnchoredAtom2704
    Fin15AnchoredAtom3051 Fin15AnchoredAtom3053 Fin15AnchoredAtom3056 Fin15AnchoredAtom3060
    Fin15AnchoredAtom3063 Fin15AnchoredAtom3074 Fin15AnchoredAtom3124 Fin15AnchoredAtom3127
    Fin15AnchoredAtom3138 Fin15AnchoredAtom3159 Fin15AnchoredAtom3244 Fin15AnchoredAtom3247
    Fin15AnchoredAtom3258 Fin15AnchoredAtom3279 Fin15AnchoredAtom3419 Fin15AnchoredAtom4069
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

theorem fin15Anchored_clause30822 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
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
      ¬Fin15AnchoredAtom3051 chi ∧
      ¬Fin15AnchoredAtom3053 chi ∧
      ¬Fin15AnchoredAtom3057 chi ∧
      ¬Fin15AnchoredAtom3060 chi ∧
      ¬Fin15AnchoredAtom3064 chi ∧
      ¬Fin15AnchoredAtom3075 chi ∧
      ¬Fin15AnchoredAtom3124 chi ∧
      ¬Fin15AnchoredAtom3128 chi ∧
      ¬Fin15AnchoredAtom3139 chi ∧
      ¬Fin15AnchoredAtom3160 chi ∧
      ¬Fin15AnchoredAtom3244 chi ∧
      ¬Fin15AnchoredAtom3248 chi ∧
      ¬Fin15AnchoredAtom3259 chi ∧
      ¬Fin15AnchoredAtom3280 chi ∧
      ¬Fin15AnchoredAtom3420 chi ∧
      ¬Fin15AnchoredAtom4069 chi ∧
      ¬Fin15AnchoredAtom4073 chi ∧
      ¬Fin15AnchoredAtom4084 chi ∧
      ¬Fin15AnchoredAtom4105 chi ∧
      ¬Fin15AnchoredAtom4245 chi ∧
      ¬Fin15AnchoredAtom4455 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 6, 7, 9, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask08923
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1888 Fin15AnchoredAtom1889 Fin15AnchoredAtom1891
    Fin15AnchoredAtom1895 Fin15AnchoredAtom1906 Fin15AnchoredAtom1908 Fin15AnchoredAtom1912
    Fin15AnchoredAtom1915 Fin15AnchoredAtom1919 Fin15AnchoredAtom1930 Fin15AnchoredAtom1951
    Fin15AnchoredAtom1953 Fin15AnchoredAtom1957 Fin15AnchoredAtom1960 Fin15AnchoredAtom1964
    Fin15AnchoredAtom1975 Fin15AnchoredAtom2024 Fin15AnchoredAtom2028 Fin15AnchoredAtom2039
    Fin15AnchoredAtom2060 Fin15AnchoredAtom2336 Fin15AnchoredAtom2338 Fin15AnchoredAtom2342
    Fin15AnchoredAtom2345 Fin15AnchoredAtom2349 Fin15AnchoredAtom2360 Fin15AnchoredAtom2409
    Fin15AnchoredAtom2413 Fin15AnchoredAtom2424 Fin15AnchoredAtom2445 Fin15AnchoredAtom2529
    Fin15AnchoredAtom2533 Fin15AnchoredAtom2544 Fin15AnchoredAtom2565 Fin15AnchoredAtom2705
    Fin15AnchoredAtom3051 Fin15AnchoredAtom3053 Fin15AnchoredAtom3057 Fin15AnchoredAtom3060
    Fin15AnchoredAtom3064 Fin15AnchoredAtom3075 Fin15AnchoredAtom3124 Fin15AnchoredAtom3128
    Fin15AnchoredAtom3139 Fin15AnchoredAtom3160 Fin15AnchoredAtom3244 Fin15AnchoredAtom3248
    Fin15AnchoredAtom3259 Fin15AnchoredAtom3280 Fin15AnchoredAtom3420 Fin15AnchoredAtom4069
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

theorem fin15Anchored_clause30823 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
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
      ¬Fin15AnchoredAtom3051 chi ∧
      ¬Fin15AnchoredAtom3053 chi ∧
      ¬Fin15AnchoredAtom3058 chi ∧
      ¬Fin15AnchoredAtom3060 chi ∧
      ¬Fin15AnchoredAtom3065 chi ∧
      ¬Fin15AnchoredAtom3076 chi ∧
      ¬Fin15AnchoredAtom3124 chi ∧
      ¬Fin15AnchoredAtom3129 chi ∧
      ¬Fin15AnchoredAtom3140 chi ∧
      ¬Fin15AnchoredAtom3161 chi ∧
      ¬Fin15AnchoredAtom3244 chi ∧
      ¬Fin15AnchoredAtom3249 chi ∧
      ¬Fin15AnchoredAtom3260 chi ∧
      ¬Fin15AnchoredAtom3281 chi ∧
      ¬Fin15AnchoredAtom3421 chi ∧
      ¬Fin15AnchoredAtom4069 chi ∧
      ¬Fin15AnchoredAtom4074 chi ∧
      ¬Fin15AnchoredAtom4085 chi ∧
      ¬Fin15AnchoredAtom4106 chi ∧
      ¬Fin15AnchoredAtom4246 chi ∧
      ¬Fin15AnchoredAtom4456 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 6, 7, 9, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17115
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1888 Fin15AnchoredAtom1889 Fin15AnchoredAtom1891
    Fin15AnchoredAtom1896 Fin15AnchoredAtom1906 Fin15AnchoredAtom1908 Fin15AnchoredAtom1913
    Fin15AnchoredAtom1915 Fin15AnchoredAtom1920 Fin15AnchoredAtom1931 Fin15AnchoredAtom1951
    Fin15AnchoredAtom1953 Fin15AnchoredAtom1958 Fin15AnchoredAtom1960 Fin15AnchoredAtom1965
    Fin15AnchoredAtom1976 Fin15AnchoredAtom2024 Fin15AnchoredAtom2029 Fin15AnchoredAtom2040
    Fin15AnchoredAtom2061 Fin15AnchoredAtom2336 Fin15AnchoredAtom2338 Fin15AnchoredAtom2343
    Fin15AnchoredAtom2345 Fin15AnchoredAtom2350 Fin15AnchoredAtom2361 Fin15AnchoredAtom2409
    Fin15AnchoredAtom2414 Fin15AnchoredAtom2425 Fin15AnchoredAtom2446 Fin15AnchoredAtom2529
    Fin15AnchoredAtom2534 Fin15AnchoredAtom2545 Fin15AnchoredAtom2566 Fin15AnchoredAtom2706
    Fin15AnchoredAtom3051 Fin15AnchoredAtom3053 Fin15AnchoredAtom3058 Fin15AnchoredAtom3060
    Fin15AnchoredAtom3065 Fin15AnchoredAtom3076 Fin15AnchoredAtom3124 Fin15AnchoredAtom3129
    Fin15AnchoredAtom3140 Fin15AnchoredAtom3161 Fin15AnchoredAtom3244 Fin15AnchoredAtom3249
    Fin15AnchoredAtom3260 Fin15AnchoredAtom3281 Fin15AnchoredAtom3421 Fin15AnchoredAtom4069
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

theorem fin15Anchored_clause30824 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1893 chi ∧
      ¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1910 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1917 chi ∧
      ¬Fin15AnchoredAtom1932 chi ∧
      ¬Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom1955 chi ∧
      ¬Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom1962 chi ∧
      ¬Fin15AnchoredAtom1977 chi ∧
      ¬Fin15AnchoredAtom2025 chi ∧
      ¬Fin15AnchoredAtom2026 chi ∧
      ¬Fin15AnchoredAtom2041 chi ∧
      ¬Fin15AnchoredAtom2062 chi ∧
      ¬Fin15AnchoredAtom2336 chi ∧
      ¬Fin15AnchoredAtom2339 chi ∧
      ¬Fin15AnchoredAtom2340 chi ∧
      ¬Fin15AnchoredAtom2346 chi ∧
      ¬Fin15AnchoredAtom2347 chi ∧
      ¬Fin15AnchoredAtom2362 chi ∧
      ¬Fin15AnchoredAtom2410 chi ∧
      ¬Fin15AnchoredAtom2411 chi ∧
      ¬Fin15AnchoredAtom2426 chi ∧
      ¬Fin15AnchoredAtom2447 chi ∧
      ¬Fin15AnchoredAtom2530 chi ∧
      ¬Fin15AnchoredAtom2531 chi ∧
      ¬Fin15AnchoredAtom2546 chi ∧
      ¬Fin15AnchoredAtom2567 chi ∧
      ¬Fin15AnchoredAtom2707 chi ∧
      ¬Fin15AnchoredAtom3051 chi ∧
      ¬Fin15AnchoredAtom3054 chi ∧
      ¬Fin15AnchoredAtom3055 chi ∧
      ¬Fin15AnchoredAtom3061 chi ∧
      ¬Fin15AnchoredAtom3062 chi ∧
      ¬Fin15AnchoredAtom3077 chi ∧
      ¬Fin15AnchoredAtom3125 chi ∧
      ¬Fin15AnchoredAtom3126 chi ∧
      ¬Fin15AnchoredAtom3141 chi ∧
      ¬Fin15AnchoredAtom3162 chi ∧
      ¬Fin15AnchoredAtom3245 chi ∧
      ¬Fin15AnchoredAtom3246 chi ∧
      ¬Fin15AnchoredAtom3261 chi ∧
      ¬Fin15AnchoredAtom3282 chi ∧
      ¬Fin15AnchoredAtom3422 chi ∧
      ¬Fin15AnchoredAtom4070 chi ∧
      ¬Fin15AnchoredAtom4071 chi ∧
      ¬Fin15AnchoredAtom4086 chi ∧
      ¬Fin15AnchoredAtom4107 chi ∧
      ¬Fin15AnchoredAtom4247 chi ∧
      ¬Fin15AnchoredAtom4457 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 6, 7, 10, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask03291
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1888 Fin15AnchoredAtom1889 Fin15AnchoredAtom1892
    Fin15AnchoredAtom1893 Fin15AnchoredAtom1906 Fin15AnchoredAtom1909 Fin15AnchoredAtom1910
    Fin15AnchoredAtom1916 Fin15AnchoredAtom1917 Fin15AnchoredAtom1932 Fin15AnchoredAtom1951
    Fin15AnchoredAtom1954 Fin15AnchoredAtom1955 Fin15AnchoredAtom1961 Fin15AnchoredAtom1962
    Fin15AnchoredAtom1977 Fin15AnchoredAtom2025 Fin15AnchoredAtom2026 Fin15AnchoredAtom2041
    Fin15AnchoredAtom2062 Fin15AnchoredAtom2336 Fin15AnchoredAtom2339 Fin15AnchoredAtom2340
    Fin15AnchoredAtom2346 Fin15AnchoredAtom2347 Fin15AnchoredAtom2362 Fin15AnchoredAtom2410
    Fin15AnchoredAtom2411 Fin15AnchoredAtom2426 Fin15AnchoredAtom2447 Fin15AnchoredAtom2530
    Fin15AnchoredAtom2531 Fin15AnchoredAtom2546 Fin15AnchoredAtom2567 Fin15AnchoredAtom2707
    Fin15AnchoredAtom3051 Fin15AnchoredAtom3054 Fin15AnchoredAtom3055 Fin15AnchoredAtom3061
    Fin15AnchoredAtom3062 Fin15AnchoredAtom3077 Fin15AnchoredAtom3125 Fin15AnchoredAtom3126
    Fin15AnchoredAtom3141 Fin15AnchoredAtom3162 Fin15AnchoredAtom3245 Fin15AnchoredAtom3246
    Fin15AnchoredAtom3261 Fin15AnchoredAtom3282 Fin15AnchoredAtom3422 Fin15AnchoredAtom4070
    Fin15AnchoredAtom4071 Fin15AnchoredAtom4086 Fin15AnchoredAtom4107 Fin15AnchoredAtom4247
    Fin15AnchoredAtom4457 at hbad
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

theorem fin15Anchored_clause30825 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
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
      ¬Fin15AnchoredAtom3051 chi ∧
      ¬Fin15AnchoredAtom3054 chi ∧
      ¬Fin15AnchoredAtom3056 chi ∧
      ¬Fin15AnchoredAtom3061 chi ∧
      ¬Fin15AnchoredAtom3063 chi ∧
      ¬Fin15AnchoredAtom3078 chi ∧
      ¬Fin15AnchoredAtom3125 chi ∧
      ¬Fin15AnchoredAtom3127 chi ∧
      ¬Fin15AnchoredAtom3142 chi ∧
      ¬Fin15AnchoredAtom3163 chi ∧
      ¬Fin15AnchoredAtom3245 chi ∧
      ¬Fin15AnchoredAtom3247 chi ∧
      ¬Fin15AnchoredAtom3262 chi ∧
      ¬Fin15AnchoredAtom3283 chi ∧
      ¬Fin15AnchoredAtom3423 chi ∧
      ¬Fin15AnchoredAtom4070 chi ∧
      ¬Fin15AnchoredAtom4072 chi ∧
      ¬Fin15AnchoredAtom4087 chi ∧
      ¬Fin15AnchoredAtom4108 chi ∧
      ¬Fin15AnchoredAtom4248 chi ∧
      ¬Fin15AnchoredAtom4458 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 6, 7, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05339
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1888 Fin15AnchoredAtom1889 Fin15AnchoredAtom1892
    Fin15AnchoredAtom1894 Fin15AnchoredAtom1906 Fin15AnchoredAtom1909 Fin15AnchoredAtom1911
    Fin15AnchoredAtom1916 Fin15AnchoredAtom1918 Fin15AnchoredAtom1933 Fin15AnchoredAtom1951
    Fin15AnchoredAtom1954 Fin15AnchoredAtom1956 Fin15AnchoredAtom1961 Fin15AnchoredAtom1963
    Fin15AnchoredAtom1978 Fin15AnchoredAtom2025 Fin15AnchoredAtom2027 Fin15AnchoredAtom2042
    Fin15AnchoredAtom2063 Fin15AnchoredAtom2336 Fin15AnchoredAtom2339 Fin15AnchoredAtom2341
    Fin15AnchoredAtom2346 Fin15AnchoredAtom2348 Fin15AnchoredAtom2363 Fin15AnchoredAtom2410
    Fin15AnchoredAtom2412 Fin15AnchoredAtom2427 Fin15AnchoredAtom2448 Fin15AnchoredAtom2530
    Fin15AnchoredAtom2532 Fin15AnchoredAtom2547 Fin15AnchoredAtom2568 Fin15AnchoredAtom2708
    Fin15AnchoredAtom3051 Fin15AnchoredAtom3054 Fin15AnchoredAtom3056 Fin15AnchoredAtom3061
    Fin15AnchoredAtom3063 Fin15AnchoredAtom3078 Fin15AnchoredAtom3125 Fin15AnchoredAtom3127
    Fin15AnchoredAtom3142 Fin15AnchoredAtom3163 Fin15AnchoredAtom3245 Fin15AnchoredAtom3247
    Fin15AnchoredAtom3262 Fin15AnchoredAtom3283 Fin15AnchoredAtom3423 Fin15AnchoredAtom4070
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

theorem fin15Anchored_clause30826 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
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
      ¬Fin15AnchoredAtom3051 chi ∧
      ¬Fin15AnchoredAtom3054 chi ∧
      ¬Fin15AnchoredAtom3057 chi ∧
      ¬Fin15AnchoredAtom3061 chi ∧
      ¬Fin15AnchoredAtom3064 chi ∧
      ¬Fin15AnchoredAtom3079 chi ∧
      ¬Fin15AnchoredAtom3125 chi ∧
      ¬Fin15AnchoredAtom3128 chi ∧
      ¬Fin15AnchoredAtom3143 chi ∧
      ¬Fin15AnchoredAtom3164 chi ∧
      ¬Fin15AnchoredAtom3245 chi ∧
      ¬Fin15AnchoredAtom3248 chi ∧
      ¬Fin15AnchoredAtom3263 chi ∧
      ¬Fin15AnchoredAtom3284 chi ∧
      ¬Fin15AnchoredAtom3424 chi ∧
      ¬Fin15AnchoredAtom4070 chi ∧
      ¬Fin15AnchoredAtom4073 chi ∧
      ¬Fin15AnchoredAtom4088 chi ∧
      ¬Fin15AnchoredAtom4109 chi ∧
      ¬Fin15AnchoredAtom4249 chi ∧
      ¬Fin15AnchoredAtom4459 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 6, 7, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09435
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1888 Fin15AnchoredAtom1889 Fin15AnchoredAtom1892
    Fin15AnchoredAtom1895 Fin15AnchoredAtom1906 Fin15AnchoredAtom1909 Fin15AnchoredAtom1912
    Fin15AnchoredAtom1916 Fin15AnchoredAtom1919 Fin15AnchoredAtom1934 Fin15AnchoredAtom1951
    Fin15AnchoredAtom1954 Fin15AnchoredAtom1957 Fin15AnchoredAtom1961 Fin15AnchoredAtom1964
    Fin15AnchoredAtom1979 Fin15AnchoredAtom2025 Fin15AnchoredAtom2028 Fin15AnchoredAtom2043
    Fin15AnchoredAtom2064 Fin15AnchoredAtom2336 Fin15AnchoredAtom2339 Fin15AnchoredAtom2342
    Fin15AnchoredAtom2346 Fin15AnchoredAtom2349 Fin15AnchoredAtom2364 Fin15AnchoredAtom2410
    Fin15AnchoredAtom2413 Fin15AnchoredAtom2428 Fin15AnchoredAtom2449 Fin15AnchoredAtom2530
    Fin15AnchoredAtom2533 Fin15AnchoredAtom2548 Fin15AnchoredAtom2569 Fin15AnchoredAtom2709
    Fin15AnchoredAtom3051 Fin15AnchoredAtom3054 Fin15AnchoredAtom3057 Fin15AnchoredAtom3061
    Fin15AnchoredAtom3064 Fin15AnchoredAtom3079 Fin15AnchoredAtom3125 Fin15AnchoredAtom3128
    Fin15AnchoredAtom3143 Fin15AnchoredAtom3164 Fin15AnchoredAtom3245 Fin15AnchoredAtom3248
    Fin15AnchoredAtom3263 Fin15AnchoredAtom3284 Fin15AnchoredAtom3424 Fin15AnchoredAtom4070
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

theorem fin15Anchored_clause30827 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1935 chi ∧
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
      ¬Fin15AnchoredAtom3051 chi ∧
      ¬Fin15AnchoredAtom3054 chi ∧
      ¬Fin15AnchoredAtom3058 chi ∧
      ¬Fin15AnchoredAtom3061 chi ∧
      ¬Fin15AnchoredAtom3065 chi ∧
      ¬Fin15AnchoredAtom3080 chi ∧
      ¬Fin15AnchoredAtom3125 chi ∧
      ¬Fin15AnchoredAtom3129 chi ∧
      ¬Fin15AnchoredAtom3144 chi ∧
      ¬Fin15AnchoredAtom3165 chi ∧
      ¬Fin15AnchoredAtom3245 chi ∧
      ¬Fin15AnchoredAtom3249 chi ∧
      ¬Fin15AnchoredAtom3264 chi ∧
      ¬Fin15AnchoredAtom3285 chi ∧
      ¬Fin15AnchoredAtom3425 chi ∧
      ¬Fin15AnchoredAtom4070 chi ∧
      ¬Fin15AnchoredAtom4074 chi ∧
      ¬Fin15AnchoredAtom4089 chi ∧
      ¬Fin15AnchoredAtom4110 chi ∧
      ¬Fin15AnchoredAtom4250 chi ∧
      ¬Fin15AnchoredAtom4460 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 6, 7, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17627
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1888 Fin15AnchoredAtom1889 Fin15AnchoredAtom1892
    Fin15AnchoredAtom1896 Fin15AnchoredAtom1906 Fin15AnchoredAtom1909 Fin15AnchoredAtom1913
    Fin15AnchoredAtom1916 Fin15AnchoredAtom1920 Fin15AnchoredAtom1935 Fin15AnchoredAtom1951
    Fin15AnchoredAtom1954 Fin15AnchoredAtom1958 Fin15AnchoredAtom1961 Fin15AnchoredAtom1965
    Fin15AnchoredAtom1980 Fin15AnchoredAtom2025 Fin15AnchoredAtom2029 Fin15AnchoredAtom2044
    Fin15AnchoredAtom2065 Fin15AnchoredAtom2336 Fin15AnchoredAtom2339 Fin15AnchoredAtom2343
    Fin15AnchoredAtom2346 Fin15AnchoredAtom2350 Fin15AnchoredAtom2365 Fin15AnchoredAtom2410
    Fin15AnchoredAtom2414 Fin15AnchoredAtom2429 Fin15AnchoredAtom2450 Fin15AnchoredAtom2530
    Fin15AnchoredAtom2534 Fin15AnchoredAtom2549 Fin15AnchoredAtom2570 Fin15AnchoredAtom2710
    Fin15AnchoredAtom3051 Fin15AnchoredAtom3054 Fin15AnchoredAtom3058 Fin15AnchoredAtom3061
    Fin15AnchoredAtom3065 Fin15AnchoredAtom3080 Fin15AnchoredAtom3125 Fin15AnchoredAtom3129
    Fin15AnchoredAtom3144 Fin15AnchoredAtom3165 Fin15AnchoredAtom3245 Fin15AnchoredAtom3249
    Fin15AnchoredAtom3264 Fin15AnchoredAtom3285 Fin15AnchoredAtom3425 Fin15AnchoredAtom4070
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

theorem fin15Anchored_clause30828 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1939 chi ∧
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
      ¬Fin15AnchoredAtom3051 chi ∧
      ¬Fin15AnchoredAtom3056 chi ∧
      ¬Fin15AnchoredAtom3057 chi ∧
      ¬Fin15AnchoredAtom3063 chi ∧
      ¬Fin15AnchoredAtom3064 chi ∧
      ¬Fin15AnchoredAtom3084 chi ∧
      ¬Fin15AnchoredAtom3127 chi ∧
      ¬Fin15AnchoredAtom3128 chi ∧
      ¬Fin15AnchoredAtom3148 chi ∧
      ¬Fin15AnchoredAtom3169 chi ∧
      ¬Fin15AnchoredAtom3247 chi ∧
      ¬Fin15AnchoredAtom3248 chi ∧
      ¬Fin15AnchoredAtom3268 chi ∧
      ¬Fin15AnchoredAtom3289 chi ∧
      ¬Fin15AnchoredAtom3429 chi ∧
      ¬Fin15AnchoredAtom4072 chi ∧
      ¬Fin15AnchoredAtom4073 chi ∧
      ¬Fin15AnchoredAtom4093 chi ∧
      ¬Fin15AnchoredAtom4114 chi ∧
      ¬Fin15AnchoredAtom4254 chi ∧
      ¬Fin15AnchoredAtom4464 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 6, 7, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask12507
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1888 Fin15AnchoredAtom1889 Fin15AnchoredAtom1894
    Fin15AnchoredAtom1895 Fin15AnchoredAtom1906 Fin15AnchoredAtom1911 Fin15AnchoredAtom1912
    Fin15AnchoredAtom1918 Fin15AnchoredAtom1919 Fin15AnchoredAtom1939 Fin15AnchoredAtom1951
    Fin15AnchoredAtom1956 Fin15AnchoredAtom1957 Fin15AnchoredAtom1963 Fin15AnchoredAtom1964
    Fin15AnchoredAtom1984 Fin15AnchoredAtom2027 Fin15AnchoredAtom2028 Fin15AnchoredAtom2048
    Fin15AnchoredAtom2069 Fin15AnchoredAtom2336 Fin15AnchoredAtom2341 Fin15AnchoredAtom2342
    Fin15AnchoredAtom2348 Fin15AnchoredAtom2349 Fin15AnchoredAtom2369 Fin15AnchoredAtom2412
    Fin15AnchoredAtom2413 Fin15AnchoredAtom2433 Fin15AnchoredAtom2454 Fin15AnchoredAtom2532
    Fin15AnchoredAtom2533 Fin15AnchoredAtom2553 Fin15AnchoredAtom2574 Fin15AnchoredAtom2714
    Fin15AnchoredAtom3051 Fin15AnchoredAtom3056 Fin15AnchoredAtom3057 Fin15AnchoredAtom3063
    Fin15AnchoredAtom3064 Fin15AnchoredAtom3084 Fin15AnchoredAtom3127 Fin15AnchoredAtom3128
    Fin15AnchoredAtom3148 Fin15AnchoredAtom3169 Fin15AnchoredAtom3247 Fin15AnchoredAtom3248
    Fin15AnchoredAtom3268 Fin15AnchoredAtom3289 Fin15AnchoredAtom3429 Fin15AnchoredAtom4072
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

theorem fin15Anchored_clause30829 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1940 chi ∧
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
      ¬Fin15AnchoredAtom3051 chi ∧
      ¬Fin15AnchoredAtom3056 chi ∧
      ¬Fin15AnchoredAtom3058 chi ∧
      ¬Fin15AnchoredAtom3063 chi ∧
      ¬Fin15AnchoredAtom3065 chi ∧
      ¬Fin15AnchoredAtom3085 chi ∧
      ¬Fin15AnchoredAtom3127 chi ∧
      ¬Fin15AnchoredAtom3129 chi ∧
      ¬Fin15AnchoredAtom3149 chi ∧
      ¬Fin15AnchoredAtom3170 chi ∧
      ¬Fin15AnchoredAtom3247 chi ∧
      ¬Fin15AnchoredAtom3249 chi ∧
      ¬Fin15AnchoredAtom3269 chi ∧
      ¬Fin15AnchoredAtom3290 chi ∧
      ¬Fin15AnchoredAtom3430 chi ∧
      ¬Fin15AnchoredAtom4072 chi ∧
      ¬Fin15AnchoredAtom4074 chi ∧
      ¬Fin15AnchoredAtom4094 chi ∧
      ¬Fin15AnchoredAtom4115 chi ∧
      ¬Fin15AnchoredAtom4255 chi ∧
      ¬Fin15AnchoredAtom4465 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 6, 7, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask20699
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1888 Fin15AnchoredAtom1889 Fin15AnchoredAtom1894
    Fin15AnchoredAtom1896 Fin15AnchoredAtom1906 Fin15AnchoredAtom1911 Fin15AnchoredAtom1913
    Fin15AnchoredAtom1918 Fin15AnchoredAtom1920 Fin15AnchoredAtom1940 Fin15AnchoredAtom1951
    Fin15AnchoredAtom1956 Fin15AnchoredAtom1958 Fin15AnchoredAtom1963 Fin15AnchoredAtom1965
    Fin15AnchoredAtom1985 Fin15AnchoredAtom2027 Fin15AnchoredAtom2029 Fin15AnchoredAtom2049
    Fin15AnchoredAtom2070 Fin15AnchoredAtom2336 Fin15AnchoredAtom2341 Fin15AnchoredAtom2343
    Fin15AnchoredAtom2348 Fin15AnchoredAtom2350 Fin15AnchoredAtom2370 Fin15AnchoredAtom2412
    Fin15AnchoredAtom2414 Fin15AnchoredAtom2434 Fin15AnchoredAtom2455 Fin15AnchoredAtom2532
    Fin15AnchoredAtom2534 Fin15AnchoredAtom2554 Fin15AnchoredAtom2575 Fin15AnchoredAtom2715
    Fin15AnchoredAtom3051 Fin15AnchoredAtom3056 Fin15AnchoredAtom3058 Fin15AnchoredAtom3063
    Fin15AnchoredAtom3065 Fin15AnchoredAtom3085 Fin15AnchoredAtom3127 Fin15AnchoredAtom3129
    Fin15AnchoredAtom3149 Fin15AnchoredAtom3170 Fin15AnchoredAtom3247 Fin15AnchoredAtom3249
    Fin15AnchoredAtom3269 Fin15AnchoredAtom3290 Fin15AnchoredAtom3430 Fin15AnchoredAtom4072
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

theorem fin15Anchored_clause30830 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
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
      ¬Fin15AnchoredAtom3051 chi ∧
      ¬Fin15AnchoredAtom3057 chi ∧
      ¬Fin15AnchoredAtom3058 chi ∧
      ¬Fin15AnchoredAtom3064 chi ∧
      ¬Fin15AnchoredAtom3065 chi ∧
      ¬Fin15AnchoredAtom3086 chi ∧
      ¬Fin15AnchoredAtom3128 chi ∧
      ¬Fin15AnchoredAtom3129 chi ∧
      ¬Fin15AnchoredAtom3150 chi ∧
      ¬Fin15AnchoredAtom3171 chi ∧
      ¬Fin15AnchoredAtom3248 chi ∧
      ¬Fin15AnchoredAtom3249 chi ∧
      ¬Fin15AnchoredAtom3270 chi ∧
      ¬Fin15AnchoredAtom3291 chi ∧
      ¬Fin15AnchoredAtom3431 chi ∧
      ¬Fin15AnchoredAtom4073 chi ∧
      ¬Fin15AnchoredAtom4074 chi ∧
      ¬Fin15AnchoredAtom4095 chi ∧
      ¬Fin15AnchoredAtom4116 chi ∧
      ¬Fin15AnchoredAtom4256 chi ∧
      ¬Fin15AnchoredAtom4466 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 6, 7, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask24795
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1888 Fin15AnchoredAtom1889 Fin15AnchoredAtom1895
    Fin15AnchoredAtom1896 Fin15AnchoredAtom1906 Fin15AnchoredAtom1912 Fin15AnchoredAtom1913
    Fin15AnchoredAtom1919 Fin15AnchoredAtom1920 Fin15AnchoredAtom1941 Fin15AnchoredAtom1951
    Fin15AnchoredAtom1957 Fin15AnchoredAtom1958 Fin15AnchoredAtom1964 Fin15AnchoredAtom1965
    Fin15AnchoredAtom1986 Fin15AnchoredAtom2028 Fin15AnchoredAtom2029 Fin15AnchoredAtom2050
    Fin15AnchoredAtom2071 Fin15AnchoredAtom2336 Fin15AnchoredAtom2342 Fin15AnchoredAtom2343
    Fin15AnchoredAtom2349 Fin15AnchoredAtom2350 Fin15AnchoredAtom2371 Fin15AnchoredAtom2413
    Fin15AnchoredAtom2414 Fin15AnchoredAtom2435 Fin15AnchoredAtom2456 Fin15AnchoredAtom2533
    Fin15AnchoredAtom2534 Fin15AnchoredAtom2555 Fin15AnchoredAtom2576 Fin15AnchoredAtom2716
    Fin15AnchoredAtom3051 Fin15AnchoredAtom3057 Fin15AnchoredAtom3058 Fin15AnchoredAtom3064
    Fin15AnchoredAtom3065 Fin15AnchoredAtom3086 Fin15AnchoredAtom3128 Fin15AnchoredAtom3129
    Fin15AnchoredAtom3150 Fin15AnchoredAtom3171 Fin15AnchoredAtom3248 Fin15AnchoredAtom3249
    Fin15AnchoredAtom3270 Fin15AnchoredAtom3291 Fin15AnchoredAtom3431 Fin15AnchoredAtom4073
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

theorem fin15Anchored_clause30831 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1890 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1907 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1921 chi ∧
      ¬Fin15AnchoredAtom1924 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom1952 chi ∧
      ¬Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom1966 chi ∧
      ¬Fin15AnchoredAtom1969 chi ∧
      ¬Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom2030 chi ∧
      ¬Fin15AnchoredAtom2033 chi ∧
      ¬Fin15AnchoredAtom2038 chi ∧
      ¬Fin15AnchoredAtom2074 chi ∧
      ¬Fin15AnchoredAtom2337 chi ∧
      ¬Fin15AnchoredAtom2338 chi ∧
      ¬Fin15AnchoredAtom2341 chi ∧
      ¬Fin15AnchoredAtom2351 chi ∧
      ¬Fin15AnchoredAtom2354 chi ∧
      ¬Fin15AnchoredAtom2359 chi ∧
      ¬Fin15AnchoredAtom2415 chi ∧
      ¬Fin15AnchoredAtom2418 chi ∧
      ¬Fin15AnchoredAtom2423 chi ∧
      ¬Fin15AnchoredAtom2459 chi ∧
      ¬Fin15AnchoredAtom2535 chi ∧
      ¬Fin15AnchoredAtom2538 chi ∧
      ¬Fin15AnchoredAtom2543 chi ∧
      ¬Fin15AnchoredAtom2579 chi ∧
      ¬Fin15AnchoredAtom2719 chi ∧
      ¬Fin15AnchoredAtom3052 chi ∧
      ¬Fin15AnchoredAtom3053 chi ∧
      ¬Fin15AnchoredAtom3056 chi ∧
      ¬Fin15AnchoredAtom3066 chi ∧
      ¬Fin15AnchoredAtom3069 chi ∧
      ¬Fin15AnchoredAtom3074 chi ∧
      ¬Fin15AnchoredAtom3130 chi ∧
      ¬Fin15AnchoredAtom3133 chi ∧
      ¬Fin15AnchoredAtom3138 chi ∧
      ¬Fin15AnchoredAtom3174 chi ∧
      ¬Fin15AnchoredAtom3250 chi ∧
      ¬Fin15AnchoredAtom3253 chi ∧
      ¬Fin15AnchoredAtom3258 chi ∧
      ¬Fin15AnchoredAtom3294 chi ∧
      ¬Fin15AnchoredAtom3434 chi ∧
      ¬Fin15AnchoredAtom4075 chi ∧
      ¬Fin15AnchoredAtom4078 chi ∧
      ¬Fin15AnchoredAtom4083 chi ∧
      ¬Fin15AnchoredAtom4119 chi ∧
      ¬Fin15AnchoredAtom4259 chi ∧
      ¬Fin15AnchoredAtom4469 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 6, 8, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask04955
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1888 Fin15AnchoredAtom1890 Fin15AnchoredAtom1891
    Fin15AnchoredAtom1894 Fin15AnchoredAtom1907 Fin15AnchoredAtom1908 Fin15AnchoredAtom1911
    Fin15AnchoredAtom1921 Fin15AnchoredAtom1924 Fin15AnchoredAtom1929 Fin15AnchoredAtom1952
    Fin15AnchoredAtom1953 Fin15AnchoredAtom1956 Fin15AnchoredAtom1966 Fin15AnchoredAtom1969
    Fin15AnchoredAtom1974 Fin15AnchoredAtom2030 Fin15AnchoredAtom2033 Fin15AnchoredAtom2038
    Fin15AnchoredAtom2074 Fin15AnchoredAtom2337 Fin15AnchoredAtom2338 Fin15AnchoredAtom2341
    Fin15AnchoredAtom2351 Fin15AnchoredAtom2354 Fin15AnchoredAtom2359 Fin15AnchoredAtom2415
    Fin15AnchoredAtom2418 Fin15AnchoredAtom2423 Fin15AnchoredAtom2459 Fin15AnchoredAtom2535
    Fin15AnchoredAtom2538 Fin15AnchoredAtom2543 Fin15AnchoredAtom2579 Fin15AnchoredAtom2719
    Fin15AnchoredAtom3052 Fin15AnchoredAtom3053 Fin15AnchoredAtom3056 Fin15AnchoredAtom3066
    Fin15AnchoredAtom3069 Fin15AnchoredAtom3074 Fin15AnchoredAtom3130 Fin15AnchoredAtom3133
    Fin15AnchoredAtom3138 Fin15AnchoredAtom3174 Fin15AnchoredAtom3250 Fin15AnchoredAtom3253
    Fin15AnchoredAtom3258 Fin15AnchoredAtom3294 Fin15AnchoredAtom3434 Fin15AnchoredAtom4075
    Fin15AnchoredAtom4078 Fin15AnchoredAtom4083 Fin15AnchoredAtom4119 Fin15AnchoredAtom4259
    Fin15AnchoredAtom4469 at hbad
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

theorem fin15Anchored_clause30832 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1890 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1907 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1922 chi ∧
      ¬Fin15AnchoredAtom1925 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom1952 chi ∧
      ¬Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom1967 chi ∧
      ¬Fin15AnchoredAtom1970 chi ∧
      ¬Fin15AnchoredAtom1979 chi ∧
      ¬Fin15AnchoredAtom2031 chi ∧
      ¬Fin15AnchoredAtom2034 chi ∧
      ¬Fin15AnchoredAtom2043 chi ∧
      ¬Fin15AnchoredAtom2079 chi ∧
      ¬Fin15AnchoredAtom2337 chi ∧
      ¬Fin15AnchoredAtom2339 chi ∧
      ¬Fin15AnchoredAtom2342 chi ∧
      ¬Fin15AnchoredAtom2352 chi ∧
      ¬Fin15AnchoredAtom2355 chi ∧
      ¬Fin15AnchoredAtom2364 chi ∧
      ¬Fin15AnchoredAtom2416 chi ∧
      ¬Fin15AnchoredAtom2419 chi ∧
      ¬Fin15AnchoredAtom2428 chi ∧
      ¬Fin15AnchoredAtom2464 chi ∧
      ¬Fin15AnchoredAtom2536 chi ∧
      ¬Fin15AnchoredAtom2539 chi ∧
      ¬Fin15AnchoredAtom2548 chi ∧
      ¬Fin15AnchoredAtom2584 chi ∧
      ¬Fin15AnchoredAtom2724 chi ∧
      ¬Fin15AnchoredAtom3052 chi ∧
      ¬Fin15AnchoredAtom3054 chi ∧
      ¬Fin15AnchoredAtom3057 chi ∧
      ¬Fin15AnchoredAtom3067 chi ∧
      ¬Fin15AnchoredAtom3070 chi ∧
      ¬Fin15AnchoredAtom3079 chi ∧
      ¬Fin15AnchoredAtom3131 chi ∧
      ¬Fin15AnchoredAtom3134 chi ∧
      ¬Fin15AnchoredAtom3143 chi ∧
      ¬Fin15AnchoredAtom3179 chi ∧
      ¬Fin15AnchoredAtom3251 chi ∧
      ¬Fin15AnchoredAtom3254 chi ∧
      ¬Fin15AnchoredAtom3263 chi ∧
      ¬Fin15AnchoredAtom3299 chi ∧
      ¬Fin15AnchoredAtom3439 chi ∧
      ¬Fin15AnchoredAtom4076 chi ∧
      ¬Fin15AnchoredAtom4079 chi ∧
      ¬Fin15AnchoredAtom4088 chi ∧
      ¬Fin15AnchoredAtom4124 chi ∧
      ¬Fin15AnchoredAtom4264 chi ∧
      ¬Fin15AnchoredAtom4474 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 6, 8, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09563
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1888 Fin15AnchoredAtom1890 Fin15AnchoredAtom1892
    Fin15AnchoredAtom1895 Fin15AnchoredAtom1907 Fin15AnchoredAtom1909 Fin15AnchoredAtom1912
    Fin15AnchoredAtom1922 Fin15AnchoredAtom1925 Fin15AnchoredAtom1934 Fin15AnchoredAtom1952
    Fin15AnchoredAtom1954 Fin15AnchoredAtom1957 Fin15AnchoredAtom1967 Fin15AnchoredAtom1970
    Fin15AnchoredAtom1979 Fin15AnchoredAtom2031 Fin15AnchoredAtom2034 Fin15AnchoredAtom2043
    Fin15AnchoredAtom2079 Fin15AnchoredAtom2337 Fin15AnchoredAtom2339 Fin15AnchoredAtom2342
    Fin15AnchoredAtom2352 Fin15AnchoredAtom2355 Fin15AnchoredAtom2364 Fin15AnchoredAtom2416
    Fin15AnchoredAtom2419 Fin15AnchoredAtom2428 Fin15AnchoredAtom2464 Fin15AnchoredAtom2536
    Fin15AnchoredAtom2539 Fin15AnchoredAtom2548 Fin15AnchoredAtom2584 Fin15AnchoredAtom2724
    Fin15AnchoredAtom3052 Fin15AnchoredAtom3054 Fin15AnchoredAtom3057 Fin15AnchoredAtom3067
    Fin15AnchoredAtom3070 Fin15AnchoredAtom3079 Fin15AnchoredAtom3131 Fin15AnchoredAtom3134
    Fin15AnchoredAtom3143 Fin15AnchoredAtom3179 Fin15AnchoredAtom3251 Fin15AnchoredAtom3254
    Fin15AnchoredAtom3263 Fin15AnchoredAtom3299 Fin15AnchoredAtom3439 Fin15AnchoredAtom4076
    Fin15AnchoredAtom4079 Fin15AnchoredAtom4088 Fin15AnchoredAtom4124 Fin15AnchoredAtom4264
    Fin15AnchoredAtom4474 at hbad
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

theorem fin15Anchored_clause30833 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
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
      ¬Fin15AnchoredAtom3053 chi ∧
      ¬Fin15AnchoredAtom3054 chi ∧
      ¬Fin15AnchoredAtom3056 chi ∧
      ¬Fin15AnchoredAtom3072 chi ∧
      ¬Fin15AnchoredAtom3074 chi ∧
      ¬Fin15AnchoredAtom3078 chi ∧
      ¬Fin15AnchoredAtom3136 chi ∧
      ¬Fin15AnchoredAtom3138 chi ∧
      ¬Fin15AnchoredAtom3142 chi ∧
      ¬Fin15AnchoredAtom3188 chi ∧
      ¬Fin15AnchoredAtom3256 chi ∧
      ¬Fin15AnchoredAtom3258 chi ∧
      ¬Fin15AnchoredAtom3262 chi ∧
      ¬Fin15AnchoredAtom3308 chi ∧
      ¬Fin15AnchoredAtom3448 chi ∧
      ¬Fin15AnchoredAtom4081 chi ∧
      ¬Fin15AnchoredAtom4083 chi ∧
      ¬Fin15AnchoredAtom4087 chi ∧
      ¬Fin15AnchoredAtom4133 chi ∧
      ¬Fin15AnchoredAtom4273 chi ∧
      ¬Fin15AnchoredAtom4483 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 6, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05723
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1888 Fin15AnchoredAtom1891 Fin15AnchoredAtom1892
    Fin15AnchoredAtom1894 Fin15AnchoredAtom1908 Fin15AnchoredAtom1909 Fin15AnchoredAtom1911
    Fin15AnchoredAtom1927 Fin15AnchoredAtom1929 Fin15AnchoredAtom1933 Fin15AnchoredAtom1953
    Fin15AnchoredAtom1954 Fin15AnchoredAtom1956 Fin15AnchoredAtom1972 Fin15AnchoredAtom1974
    Fin15AnchoredAtom1978 Fin15AnchoredAtom2036 Fin15AnchoredAtom2038 Fin15AnchoredAtom2042
    Fin15AnchoredAtom2088 Fin15AnchoredAtom2338 Fin15AnchoredAtom2339 Fin15AnchoredAtom2341
    Fin15AnchoredAtom2357 Fin15AnchoredAtom2359 Fin15AnchoredAtom2363 Fin15AnchoredAtom2421
    Fin15AnchoredAtom2423 Fin15AnchoredAtom2427 Fin15AnchoredAtom2473 Fin15AnchoredAtom2541
    Fin15AnchoredAtom2543 Fin15AnchoredAtom2547 Fin15AnchoredAtom2593 Fin15AnchoredAtom2733
    Fin15AnchoredAtom3053 Fin15AnchoredAtom3054 Fin15AnchoredAtom3056 Fin15AnchoredAtom3072
    Fin15AnchoredAtom3074 Fin15AnchoredAtom3078 Fin15AnchoredAtom3136 Fin15AnchoredAtom3138
    Fin15AnchoredAtom3142 Fin15AnchoredAtom3188 Fin15AnchoredAtom3256 Fin15AnchoredAtom3258
    Fin15AnchoredAtom3262 Fin15AnchoredAtom3308 Fin15AnchoredAtom3448 Fin15AnchoredAtom4081
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

theorem fin15Anchored_clause30834 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
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
      ¬Fin15AnchoredAtom3053 chi ∧
      ¬Fin15AnchoredAtom3054 chi ∧
      ¬Fin15AnchoredAtom3057 chi ∧
      ¬Fin15AnchoredAtom3072 chi ∧
      ¬Fin15AnchoredAtom3075 chi ∧
      ¬Fin15AnchoredAtom3079 chi ∧
      ¬Fin15AnchoredAtom3136 chi ∧
      ¬Fin15AnchoredAtom3139 chi ∧
      ¬Fin15AnchoredAtom3143 chi ∧
      ¬Fin15AnchoredAtom3189 chi ∧
      ¬Fin15AnchoredAtom3256 chi ∧
      ¬Fin15AnchoredAtom3259 chi ∧
      ¬Fin15AnchoredAtom3263 chi ∧
      ¬Fin15AnchoredAtom3309 chi ∧
      ¬Fin15AnchoredAtom3449 chi ∧
      ¬Fin15AnchoredAtom4081 chi ∧
      ¬Fin15AnchoredAtom4084 chi ∧
      ¬Fin15AnchoredAtom4088 chi ∧
      ¬Fin15AnchoredAtom4134 chi ∧
      ¬Fin15AnchoredAtom4274 chi ∧
      ¬Fin15AnchoredAtom4484 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 6, 9, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09819
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1888 Fin15AnchoredAtom1891 Fin15AnchoredAtom1892
    Fin15AnchoredAtom1895 Fin15AnchoredAtom1908 Fin15AnchoredAtom1909 Fin15AnchoredAtom1912
    Fin15AnchoredAtom1927 Fin15AnchoredAtom1930 Fin15AnchoredAtom1934 Fin15AnchoredAtom1953
    Fin15AnchoredAtom1954 Fin15AnchoredAtom1957 Fin15AnchoredAtom1972 Fin15AnchoredAtom1975
    Fin15AnchoredAtom1979 Fin15AnchoredAtom2036 Fin15AnchoredAtom2039 Fin15AnchoredAtom2043
    Fin15AnchoredAtom2089 Fin15AnchoredAtom2338 Fin15AnchoredAtom2339 Fin15AnchoredAtom2342
    Fin15AnchoredAtom2357 Fin15AnchoredAtom2360 Fin15AnchoredAtom2364 Fin15AnchoredAtom2421
    Fin15AnchoredAtom2424 Fin15AnchoredAtom2428 Fin15AnchoredAtom2474 Fin15AnchoredAtom2541
    Fin15AnchoredAtom2544 Fin15AnchoredAtom2548 Fin15AnchoredAtom2594 Fin15AnchoredAtom2734
    Fin15AnchoredAtom3053 Fin15AnchoredAtom3054 Fin15AnchoredAtom3057 Fin15AnchoredAtom3072
    Fin15AnchoredAtom3075 Fin15AnchoredAtom3079 Fin15AnchoredAtom3136 Fin15AnchoredAtom3139
    Fin15AnchoredAtom3143 Fin15AnchoredAtom3189 Fin15AnchoredAtom3256 Fin15AnchoredAtom3259
    Fin15AnchoredAtom3263 Fin15AnchoredAtom3309 Fin15AnchoredAtom3449 Fin15AnchoredAtom4081
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

theorem fin15Anchored_clause30835 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom1935 chi ∧
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
      ¬Fin15AnchoredAtom3053 chi ∧
      ¬Fin15AnchoredAtom3054 chi ∧
      ¬Fin15AnchoredAtom3058 chi ∧
      ¬Fin15AnchoredAtom3072 chi ∧
      ¬Fin15AnchoredAtom3076 chi ∧
      ¬Fin15AnchoredAtom3080 chi ∧
      ¬Fin15AnchoredAtom3136 chi ∧
      ¬Fin15AnchoredAtom3140 chi ∧
      ¬Fin15AnchoredAtom3144 chi ∧
      ¬Fin15AnchoredAtom3190 chi ∧
      ¬Fin15AnchoredAtom3256 chi ∧
      ¬Fin15AnchoredAtom3260 chi ∧
      ¬Fin15AnchoredAtom3264 chi ∧
      ¬Fin15AnchoredAtom3310 chi ∧
      ¬Fin15AnchoredAtom3450 chi ∧
      ¬Fin15AnchoredAtom4081 chi ∧
      ¬Fin15AnchoredAtom4085 chi ∧
      ¬Fin15AnchoredAtom4089 chi ∧
      ¬Fin15AnchoredAtom4135 chi ∧
      ¬Fin15AnchoredAtom4275 chi ∧
      ¬Fin15AnchoredAtom4485 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 6, 9, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask18011
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1888 Fin15AnchoredAtom1891 Fin15AnchoredAtom1892
    Fin15AnchoredAtom1896 Fin15AnchoredAtom1908 Fin15AnchoredAtom1909 Fin15AnchoredAtom1913
    Fin15AnchoredAtom1927 Fin15AnchoredAtom1931 Fin15AnchoredAtom1935 Fin15AnchoredAtom1953
    Fin15AnchoredAtom1954 Fin15AnchoredAtom1958 Fin15AnchoredAtom1972 Fin15AnchoredAtom1976
    Fin15AnchoredAtom1980 Fin15AnchoredAtom2036 Fin15AnchoredAtom2040 Fin15AnchoredAtom2044
    Fin15AnchoredAtom2090 Fin15AnchoredAtom2338 Fin15AnchoredAtom2339 Fin15AnchoredAtom2343
    Fin15AnchoredAtom2357 Fin15AnchoredAtom2361 Fin15AnchoredAtom2365 Fin15AnchoredAtom2421
    Fin15AnchoredAtom2425 Fin15AnchoredAtom2429 Fin15AnchoredAtom2475 Fin15AnchoredAtom2541
    Fin15AnchoredAtom2545 Fin15AnchoredAtom2549 Fin15AnchoredAtom2595 Fin15AnchoredAtom2735
    Fin15AnchoredAtom3053 Fin15AnchoredAtom3054 Fin15AnchoredAtom3058 Fin15AnchoredAtom3072
    Fin15AnchoredAtom3076 Fin15AnchoredAtom3080 Fin15AnchoredAtom3136 Fin15AnchoredAtom3140
    Fin15AnchoredAtom3144 Fin15AnchoredAtom3190 Fin15AnchoredAtom3256 Fin15AnchoredAtom3260
    Fin15AnchoredAtom3264 Fin15AnchoredAtom3310 Fin15AnchoredAtom3450 Fin15AnchoredAtom4081
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

theorem fin15Anchored_clause30836 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1939 chi ∧
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
      ¬Fin15AnchoredAtom3053 chi ∧
      ¬Fin15AnchoredAtom3056 chi ∧
      ¬Fin15AnchoredAtom3057 chi ∧
      ¬Fin15AnchoredAtom3074 chi ∧
      ¬Fin15AnchoredAtom3075 chi ∧
      ¬Fin15AnchoredAtom3084 chi ∧
      ¬Fin15AnchoredAtom3138 chi ∧
      ¬Fin15AnchoredAtom3139 chi ∧
      ¬Fin15AnchoredAtom3148 chi ∧
      ¬Fin15AnchoredAtom3194 chi ∧
      ¬Fin15AnchoredAtom3258 chi ∧
      ¬Fin15AnchoredAtom3259 chi ∧
      ¬Fin15AnchoredAtom3268 chi ∧
      ¬Fin15AnchoredAtom3314 chi ∧
      ¬Fin15AnchoredAtom3454 chi ∧
      ¬Fin15AnchoredAtom4083 chi ∧
      ¬Fin15AnchoredAtom4084 chi ∧
      ¬Fin15AnchoredAtom4093 chi ∧
      ¬Fin15AnchoredAtom4139 chi ∧
      ¬Fin15AnchoredAtom4279 chi ∧
      ¬Fin15AnchoredAtom4489 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 6, 9, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask12891
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1888 Fin15AnchoredAtom1891 Fin15AnchoredAtom1894
    Fin15AnchoredAtom1895 Fin15AnchoredAtom1908 Fin15AnchoredAtom1911 Fin15AnchoredAtom1912
    Fin15AnchoredAtom1929 Fin15AnchoredAtom1930 Fin15AnchoredAtom1939 Fin15AnchoredAtom1953
    Fin15AnchoredAtom1956 Fin15AnchoredAtom1957 Fin15AnchoredAtom1974 Fin15AnchoredAtom1975
    Fin15AnchoredAtom1984 Fin15AnchoredAtom2038 Fin15AnchoredAtom2039 Fin15AnchoredAtom2048
    Fin15AnchoredAtom2094 Fin15AnchoredAtom2338 Fin15AnchoredAtom2341 Fin15AnchoredAtom2342
    Fin15AnchoredAtom2359 Fin15AnchoredAtom2360 Fin15AnchoredAtom2369 Fin15AnchoredAtom2423
    Fin15AnchoredAtom2424 Fin15AnchoredAtom2433 Fin15AnchoredAtom2479 Fin15AnchoredAtom2543
    Fin15AnchoredAtom2544 Fin15AnchoredAtom2553 Fin15AnchoredAtom2599 Fin15AnchoredAtom2739
    Fin15AnchoredAtom3053 Fin15AnchoredAtom3056 Fin15AnchoredAtom3057 Fin15AnchoredAtom3074
    Fin15AnchoredAtom3075 Fin15AnchoredAtom3084 Fin15AnchoredAtom3138 Fin15AnchoredAtom3139
    Fin15AnchoredAtom3148 Fin15AnchoredAtom3194 Fin15AnchoredAtom3258 Fin15AnchoredAtom3259
    Fin15AnchoredAtom3268 Fin15AnchoredAtom3314 Fin15AnchoredAtom3454 Fin15AnchoredAtom4083
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

theorem fin15Anchored_clause30837 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom1940 chi ∧
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
      ¬Fin15AnchoredAtom3053 chi ∧
      ¬Fin15AnchoredAtom3056 chi ∧
      ¬Fin15AnchoredAtom3058 chi ∧
      ¬Fin15AnchoredAtom3074 chi ∧
      ¬Fin15AnchoredAtom3076 chi ∧
      ¬Fin15AnchoredAtom3085 chi ∧
      ¬Fin15AnchoredAtom3138 chi ∧
      ¬Fin15AnchoredAtom3140 chi ∧
      ¬Fin15AnchoredAtom3149 chi ∧
      ¬Fin15AnchoredAtom3195 chi ∧
      ¬Fin15AnchoredAtom3258 chi ∧
      ¬Fin15AnchoredAtom3260 chi ∧
      ¬Fin15AnchoredAtom3269 chi ∧
      ¬Fin15AnchoredAtom3315 chi ∧
      ¬Fin15AnchoredAtom3455 chi ∧
      ¬Fin15AnchoredAtom4083 chi ∧
      ¬Fin15AnchoredAtom4085 chi ∧
      ¬Fin15AnchoredAtom4094 chi ∧
      ¬Fin15AnchoredAtom4140 chi ∧
      ¬Fin15AnchoredAtom4280 chi ∧
      ¬Fin15AnchoredAtom4490 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 6, 9, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21083
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1888 Fin15AnchoredAtom1891 Fin15AnchoredAtom1894
    Fin15AnchoredAtom1896 Fin15AnchoredAtom1908 Fin15AnchoredAtom1911 Fin15AnchoredAtom1913
    Fin15AnchoredAtom1929 Fin15AnchoredAtom1931 Fin15AnchoredAtom1940 Fin15AnchoredAtom1953
    Fin15AnchoredAtom1956 Fin15AnchoredAtom1958 Fin15AnchoredAtom1974 Fin15AnchoredAtom1976
    Fin15AnchoredAtom1985 Fin15AnchoredAtom2038 Fin15AnchoredAtom2040 Fin15AnchoredAtom2049
    Fin15AnchoredAtom2095 Fin15AnchoredAtom2338 Fin15AnchoredAtom2341 Fin15AnchoredAtom2343
    Fin15AnchoredAtom2359 Fin15AnchoredAtom2361 Fin15AnchoredAtom2370 Fin15AnchoredAtom2423
    Fin15AnchoredAtom2425 Fin15AnchoredAtom2434 Fin15AnchoredAtom2480 Fin15AnchoredAtom2543
    Fin15AnchoredAtom2545 Fin15AnchoredAtom2554 Fin15AnchoredAtom2600 Fin15AnchoredAtom2740
    Fin15AnchoredAtom3053 Fin15AnchoredAtom3056 Fin15AnchoredAtom3058 Fin15AnchoredAtom3074
    Fin15AnchoredAtom3076 Fin15AnchoredAtom3085 Fin15AnchoredAtom3138 Fin15AnchoredAtom3140
    Fin15AnchoredAtom3149 Fin15AnchoredAtom3195 Fin15AnchoredAtom3258 Fin15AnchoredAtom3260
    Fin15AnchoredAtom3269 Fin15AnchoredAtom3315 Fin15AnchoredAtom3455 Fin15AnchoredAtom4083
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

theorem fin15Anchored_clause30838 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
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
      ¬Fin15AnchoredAtom3053 chi ∧
      ¬Fin15AnchoredAtom3057 chi ∧
      ¬Fin15AnchoredAtom3058 chi ∧
      ¬Fin15AnchoredAtom3075 chi ∧
      ¬Fin15AnchoredAtom3076 chi ∧
      ¬Fin15AnchoredAtom3086 chi ∧
      ¬Fin15AnchoredAtom3139 chi ∧
      ¬Fin15AnchoredAtom3140 chi ∧
      ¬Fin15AnchoredAtom3150 chi ∧
      ¬Fin15AnchoredAtom3196 chi ∧
      ¬Fin15AnchoredAtom3259 chi ∧
      ¬Fin15AnchoredAtom3260 chi ∧
      ¬Fin15AnchoredAtom3270 chi ∧
      ¬Fin15AnchoredAtom3316 chi ∧
      ¬Fin15AnchoredAtom3456 chi ∧
      ¬Fin15AnchoredAtom4084 chi ∧
      ¬Fin15AnchoredAtom4085 chi ∧
      ¬Fin15AnchoredAtom4095 chi ∧
      ¬Fin15AnchoredAtom4141 chi ∧
      ¬Fin15AnchoredAtom4281 chi ∧
      ¬Fin15AnchoredAtom4491 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 6, 9, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25179
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1888 Fin15AnchoredAtom1891 Fin15AnchoredAtom1895
    Fin15AnchoredAtom1896 Fin15AnchoredAtom1908 Fin15AnchoredAtom1912 Fin15AnchoredAtom1913
    Fin15AnchoredAtom1930 Fin15AnchoredAtom1931 Fin15AnchoredAtom1941 Fin15AnchoredAtom1953
    Fin15AnchoredAtom1957 Fin15AnchoredAtom1958 Fin15AnchoredAtom1975 Fin15AnchoredAtom1976
    Fin15AnchoredAtom1986 Fin15AnchoredAtom2039 Fin15AnchoredAtom2040 Fin15AnchoredAtom2050
    Fin15AnchoredAtom2096 Fin15AnchoredAtom2338 Fin15AnchoredAtom2342 Fin15AnchoredAtom2343
    Fin15AnchoredAtom2360 Fin15AnchoredAtom2361 Fin15AnchoredAtom2371 Fin15AnchoredAtom2424
    Fin15AnchoredAtom2425 Fin15AnchoredAtom2435 Fin15AnchoredAtom2481 Fin15AnchoredAtom2544
    Fin15AnchoredAtom2545 Fin15AnchoredAtom2555 Fin15AnchoredAtom2601 Fin15AnchoredAtom2741
    Fin15AnchoredAtom3053 Fin15AnchoredAtom3057 Fin15AnchoredAtom3058 Fin15AnchoredAtom3075
    Fin15AnchoredAtom3076 Fin15AnchoredAtom3086 Fin15AnchoredAtom3139 Fin15AnchoredAtom3140
    Fin15AnchoredAtom3150 Fin15AnchoredAtom3196 Fin15AnchoredAtom3259 Fin15AnchoredAtom3260
    Fin15AnchoredAtom3270 Fin15AnchoredAtom3316 Fin15AnchoredAtom3456 Fin15AnchoredAtom4084
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

theorem fin15Anchored_clause30839 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1893 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1910 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1932 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom1936 chi ∧
      ¬Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom1955 chi ∧
      ¬Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom1977 chi ∧
      ¬Fin15AnchoredAtom1978 chi ∧
      ¬Fin15AnchoredAtom1981 chi ∧
      ¬Fin15AnchoredAtom2041 chi ∧
      ¬Fin15AnchoredAtom2042 chi ∧
      ¬Fin15AnchoredAtom2045 chi ∧
      ¬Fin15AnchoredAtom2097 chi ∧
      ¬Fin15AnchoredAtom2339 chi ∧
      ¬Fin15AnchoredAtom2340 chi ∧
      ¬Fin15AnchoredAtom2341 chi ∧
      ¬Fin15AnchoredAtom2362 chi ∧
      ¬Fin15AnchoredAtom2363 chi ∧
      ¬Fin15AnchoredAtom2366 chi ∧
      ¬Fin15AnchoredAtom2426 chi ∧
      ¬Fin15AnchoredAtom2427 chi ∧
      ¬Fin15AnchoredAtom2430 chi ∧
      ¬Fin15AnchoredAtom2482 chi ∧
      ¬Fin15AnchoredAtom2546 chi ∧
      ¬Fin15AnchoredAtom2547 chi ∧
      ¬Fin15AnchoredAtom2550 chi ∧
      ¬Fin15AnchoredAtom2602 chi ∧
      ¬Fin15AnchoredAtom2742 chi ∧
      ¬Fin15AnchoredAtom3054 chi ∧
      ¬Fin15AnchoredAtom3055 chi ∧
      ¬Fin15AnchoredAtom3056 chi ∧
      ¬Fin15AnchoredAtom3077 chi ∧
      ¬Fin15AnchoredAtom3078 chi ∧
      ¬Fin15AnchoredAtom3081 chi ∧
      ¬Fin15AnchoredAtom3141 chi ∧
      ¬Fin15AnchoredAtom3142 chi ∧
      ¬Fin15AnchoredAtom3145 chi ∧
      ¬Fin15AnchoredAtom3197 chi ∧
      ¬Fin15AnchoredAtom3261 chi ∧
      ¬Fin15AnchoredAtom3262 chi ∧
      ¬Fin15AnchoredAtom3265 chi ∧
      ¬Fin15AnchoredAtom3317 chi ∧
      ¬Fin15AnchoredAtom3457 chi ∧
      ¬Fin15AnchoredAtom4086 chi ∧
      ¬Fin15AnchoredAtom4087 chi ∧
      ¬Fin15AnchoredAtom4090 chi ∧
      ¬Fin15AnchoredAtom4142 chi ∧
      ¬Fin15AnchoredAtom4282 chi ∧
      ¬Fin15AnchoredAtom4492 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 6, 10, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask07259
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1888 Fin15AnchoredAtom1892 Fin15AnchoredAtom1893
    Fin15AnchoredAtom1894 Fin15AnchoredAtom1909 Fin15AnchoredAtom1910 Fin15AnchoredAtom1911
    Fin15AnchoredAtom1932 Fin15AnchoredAtom1933 Fin15AnchoredAtom1936 Fin15AnchoredAtom1954
    Fin15AnchoredAtom1955 Fin15AnchoredAtom1956 Fin15AnchoredAtom1977 Fin15AnchoredAtom1978
    Fin15AnchoredAtom1981 Fin15AnchoredAtom2041 Fin15AnchoredAtom2042 Fin15AnchoredAtom2045
    Fin15AnchoredAtom2097 Fin15AnchoredAtom2339 Fin15AnchoredAtom2340 Fin15AnchoredAtom2341
    Fin15AnchoredAtom2362 Fin15AnchoredAtom2363 Fin15AnchoredAtom2366 Fin15AnchoredAtom2426
    Fin15AnchoredAtom2427 Fin15AnchoredAtom2430 Fin15AnchoredAtom2482 Fin15AnchoredAtom2546
    Fin15AnchoredAtom2547 Fin15AnchoredAtom2550 Fin15AnchoredAtom2602 Fin15AnchoredAtom2742
    Fin15AnchoredAtom3054 Fin15AnchoredAtom3055 Fin15AnchoredAtom3056 Fin15AnchoredAtom3077
    Fin15AnchoredAtom3078 Fin15AnchoredAtom3081 Fin15AnchoredAtom3141 Fin15AnchoredAtom3142
    Fin15AnchoredAtom3145 Fin15AnchoredAtom3197 Fin15AnchoredAtom3261 Fin15AnchoredAtom3262
    Fin15AnchoredAtom3265 Fin15AnchoredAtom3317 Fin15AnchoredAtom3457 Fin15AnchoredAtom4086
    Fin15AnchoredAtom4087 Fin15AnchoredAtom4090 Fin15AnchoredAtom4142 Fin15AnchoredAtom4282
    Fin15AnchoredAtom4492 at hbad
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

theorem fin15Anchored_clause30840 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom1939 chi ∧
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
      ¬Fin15AnchoredAtom3054 chi ∧
      ¬Fin15AnchoredAtom3056 chi ∧
      ¬Fin15AnchoredAtom3057 chi ∧
      ¬Fin15AnchoredAtom3078 chi ∧
      ¬Fin15AnchoredAtom3079 chi ∧
      ¬Fin15AnchoredAtom3084 chi ∧
      ¬Fin15AnchoredAtom3142 chi ∧
      ¬Fin15AnchoredAtom3143 chi ∧
      ¬Fin15AnchoredAtom3148 chi ∧
      ¬Fin15AnchoredAtom3200 chi ∧
      ¬Fin15AnchoredAtom3262 chi ∧
      ¬Fin15AnchoredAtom3263 chi ∧
      ¬Fin15AnchoredAtom3268 chi ∧
      ¬Fin15AnchoredAtom3320 chi ∧
      ¬Fin15AnchoredAtom3460 chi ∧
      ¬Fin15AnchoredAtom4087 chi ∧
      ¬Fin15AnchoredAtom4088 chi ∧
      ¬Fin15AnchoredAtom4093 chi ∧
      ¬Fin15AnchoredAtom4145 chi ∧
      ¬Fin15AnchoredAtom4285 chi ∧
      ¬Fin15AnchoredAtom4495 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 6, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13403
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1888 Fin15AnchoredAtom1892 Fin15AnchoredAtom1894
    Fin15AnchoredAtom1895 Fin15AnchoredAtom1909 Fin15AnchoredAtom1911 Fin15AnchoredAtom1912
    Fin15AnchoredAtom1933 Fin15AnchoredAtom1934 Fin15AnchoredAtom1939 Fin15AnchoredAtom1954
    Fin15AnchoredAtom1956 Fin15AnchoredAtom1957 Fin15AnchoredAtom1978 Fin15AnchoredAtom1979
    Fin15AnchoredAtom1984 Fin15AnchoredAtom2042 Fin15AnchoredAtom2043 Fin15AnchoredAtom2048
    Fin15AnchoredAtom2100 Fin15AnchoredAtom2339 Fin15AnchoredAtom2341 Fin15AnchoredAtom2342
    Fin15AnchoredAtom2363 Fin15AnchoredAtom2364 Fin15AnchoredAtom2369 Fin15AnchoredAtom2427
    Fin15AnchoredAtom2428 Fin15AnchoredAtom2433 Fin15AnchoredAtom2485 Fin15AnchoredAtom2547
    Fin15AnchoredAtom2548 Fin15AnchoredAtom2553 Fin15AnchoredAtom2605 Fin15AnchoredAtom2745
    Fin15AnchoredAtom3054 Fin15AnchoredAtom3056 Fin15AnchoredAtom3057 Fin15AnchoredAtom3078
    Fin15AnchoredAtom3079 Fin15AnchoredAtom3084 Fin15AnchoredAtom3142 Fin15AnchoredAtom3143
    Fin15AnchoredAtom3148 Fin15AnchoredAtom3200 Fin15AnchoredAtom3262 Fin15AnchoredAtom3263
    Fin15AnchoredAtom3268 Fin15AnchoredAtom3320 Fin15AnchoredAtom3460 Fin15AnchoredAtom4087
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

theorem fin15Anchored_clause30841 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom1935 chi ∧
      ¬Fin15AnchoredAtom1940 chi ∧
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
      ¬Fin15AnchoredAtom3054 chi ∧
      ¬Fin15AnchoredAtom3056 chi ∧
      ¬Fin15AnchoredAtom3058 chi ∧
      ¬Fin15AnchoredAtom3078 chi ∧
      ¬Fin15AnchoredAtom3080 chi ∧
      ¬Fin15AnchoredAtom3085 chi ∧
      ¬Fin15AnchoredAtom3142 chi ∧
      ¬Fin15AnchoredAtom3144 chi ∧
      ¬Fin15AnchoredAtom3149 chi ∧
      ¬Fin15AnchoredAtom3201 chi ∧
      ¬Fin15AnchoredAtom3262 chi ∧
      ¬Fin15AnchoredAtom3264 chi ∧
      ¬Fin15AnchoredAtom3269 chi ∧
      ¬Fin15AnchoredAtom3321 chi ∧
      ¬Fin15AnchoredAtom3461 chi ∧
      ¬Fin15AnchoredAtom4087 chi ∧
      ¬Fin15AnchoredAtom4089 chi ∧
      ¬Fin15AnchoredAtom4094 chi ∧
      ¬Fin15AnchoredAtom4146 chi ∧
      ¬Fin15AnchoredAtom4286 chi ∧
      ¬Fin15AnchoredAtom4496 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 6, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21595
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1888 Fin15AnchoredAtom1892 Fin15AnchoredAtom1894
    Fin15AnchoredAtom1896 Fin15AnchoredAtom1909 Fin15AnchoredAtom1911 Fin15AnchoredAtom1913
    Fin15AnchoredAtom1933 Fin15AnchoredAtom1935 Fin15AnchoredAtom1940 Fin15AnchoredAtom1954
    Fin15AnchoredAtom1956 Fin15AnchoredAtom1958 Fin15AnchoredAtom1978 Fin15AnchoredAtom1980
    Fin15AnchoredAtom1985 Fin15AnchoredAtom2042 Fin15AnchoredAtom2044 Fin15AnchoredAtom2049
    Fin15AnchoredAtom2101 Fin15AnchoredAtom2339 Fin15AnchoredAtom2341 Fin15AnchoredAtom2343
    Fin15AnchoredAtom2363 Fin15AnchoredAtom2365 Fin15AnchoredAtom2370 Fin15AnchoredAtom2427
    Fin15AnchoredAtom2429 Fin15AnchoredAtom2434 Fin15AnchoredAtom2486 Fin15AnchoredAtom2547
    Fin15AnchoredAtom2549 Fin15AnchoredAtom2554 Fin15AnchoredAtom2606 Fin15AnchoredAtom2746
    Fin15AnchoredAtom3054 Fin15AnchoredAtom3056 Fin15AnchoredAtom3058 Fin15AnchoredAtom3078
    Fin15AnchoredAtom3080 Fin15AnchoredAtom3085 Fin15AnchoredAtom3142 Fin15AnchoredAtom3144
    Fin15AnchoredAtom3149 Fin15AnchoredAtom3201 Fin15AnchoredAtom3262 Fin15AnchoredAtom3264
    Fin15AnchoredAtom3269 Fin15AnchoredAtom3321 Fin15AnchoredAtom3461 Fin15AnchoredAtom4087
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

theorem fin15Anchored_clause30842 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom1935 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
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
      ¬Fin15AnchoredAtom3054 chi ∧
      ¬Fin15AnchoredAtom3057 chi ∧
      ¬Fin15AnchoredAtom3058 chi ∧
      ¬Fin15AnchoredAtom3079 chi ∧
      ¬Fin15AnchoredAtom3080 chi ∧
      ¬Fin15AnchoredAtom3086 chi ∧
      ¬Fin15AnchoredAtom3143 chi ∧
      ¬Fin15AnchoredAtom3144 chi ∧
      ¬Fin15AnchoredAtom3150 chi ∧
      ¬Fin15AnchoredAtom3202 chi ∧
      ¬Fin15AnchoredAtom3263 chi ∧
      ¬Fin15AnchoredAtom3264 chi ∧
      ¬Fin15AnchoredAtom3270 chi ∧
      ¬Fin15AnchoredAtom3322 chi ∧
      ¬Fin15AnchoredAtom3462 chi ∧
      ¬Fin15AnchoredAtom4088 chi ∧
      ¬Fin15AnchoredAtom4089 chi ∧
      ¬Fin15AnchoredAtom4095 chi ∧
      ¬Fin15AnchoredAtom4147 chi ∧
      ¬Fin15AnchoredAtom4287 chi ∧
      ¬Fin15AnchoredAtom4497 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 6, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25691
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1888 Fin15AnchoredAtom1892 Fin15AnchoredAtom1895
    Fin15AnchoredAtom1896 Fin15AnchoredAtom1909 Fin15AnchoredAtom1912 Fin15AnchoredAtom1913
    Fin15AnchoredAtom1934 Fin15AnchoredAtom1935 Fin15AnchoredAtom1941 Fin15AnchoredAtom1954
    Fin15AnchoredAtom1957 Fin15AnchoredAtom1958 Fin15AnchoredAtom1979 Fin15AnchoredAtom1980
    Fin15AnchoredAtom1986 Fin15AnchoredAtom2043 Fin15AnchoredAtom2044 Fin15AnchoredAtom2050
    Fin15AnchoredAtom2102 Fin15AnchoredAtom2339 Fin15AnchoredAtom2342 Fin15AnchoredAtom2343
    Fin15AnchoredAtom2364 Fin15AnchoredAtom2365 Fin15AnchoredAtom2371 Fin15AnchoredAtom2428
    Fin15AnchoredAtom2429 Fin15AnchoredAtom2435 Fin15AnchoredAtom2487 Fin15AnchoredAtom2548
    Fin15AnchoredAtom2549 Fin15AnchoredAtom2555 Fin15AnchoredAtom2607 Fin15AnchoredAtom2747
    Fin15AnchoredAtom3054 Fin15AnchoredAtom3057 Fin15AnchoredAtom3058 Fin15AnchoredAtom3079
    Fin15AnchoredAtom3080 Fin15AnchoredAtom3086 Fin15AnchoredAtom3143 Fin15AnchoredAtom3144
    Fin15AnchoredAtom3150 Fin15AnchoredAtom3202 Fin15AnchoredAtom3263 Fin15AnchoredAtom3264
    Fin15AnchoredAtom3270 Fin15AnchoredAtom3322 Fin15AnchoredAtom3462 Fin15AnchoredAtom4088
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

theorem fin15Anchored_clause30843 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1939 chi ∧
      ¬Fin15AnchoredAtom1940 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
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
      ¬Fin15AnchoredAtom3056 chi ∧
      ¬Fin15AnchoredAtom3057 chi ∧
      ¬Fin15AnchoredAtom3058 chi ∧
      ¬Fin15AnchoredAtom3084 chi ∧
      ¬Fin15AnchoredAtom3085 chi ∧
      ¬Fin15AnchoredAtom3086 chi ∧
      ¬Fin15AnchoredAtom3148 chi ∧
      ¬Fin15AnchoredAtom3149 chi ∧
      ¬Fin15AnchoredAtom3150 chi ∧
      ¬Fin15AnchoredAtom3206 chi ∧
      ¬Fin15AnchoredAtom3268 chi ∧
      ¬Fin15AnchoredAtom3269 chi ∧
      ¬Fin15AnchoredAtom3270 chi ∧
      ¬Fin15AnchoredAtom3326 chi ∧
      ¬Fin15AnchoredAtom3466 chi ∧
      ¬Fin15AnchoredAtom4093 chi ∧
      ¬Fin15AnchoredAtom4094 chi ∧
      ¬Fin15AnchoredAtom4095 chi ∧
      ¬Fin15AnchoredAtom4151 chi ∧
      ¬Fin15AnchoredAtom4291 chi ∧
      ¬Fin15AnchoredAtom4501 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 6, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask28763
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1888 Fin15AnchoredAtom1894 Fin15AnchoredAtom1895
    Fin15AnchoredAtom1896 Fin15AnchoredAtom1911 Fin15AnchoredAtom1912 Fin15AnchoredAtom1913
    Fin15AnchoredAtom1939 Fin15AnchoredAtom1940 Fin15AnchoredAtom1941 Fin15AnchoredAtom1956
    Fin15AnchoredAtom1957 Fin15AnchoredAtom1958 Fin15AnchoredAtom1984 Fin15AnchoredAtom1985
    Fin15AnchoredAtom1986 Fin15AnchoredAtom2048 Fin15AnchoredAtom2049 Fin15AnchoredAtom2050
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2341 Fin15AnchoredAtom2342 Fin15AnchoredAtom2343
    Fin15AnchoredAtom2369 Fin15AnchoredAtom2370 Fin15AnchoredAtom2371 Fin15AnchoredAtom2433
    Fin15AnchoredAtom2434 Fin15AnchoredAtom2435 Fin15AnchoredAtom2491 Fin15AnchoredAtom2553
    Fin15AnchoredAtom2554 Fin15AnchoredAtom2555 Fin15AnchoredAtom2611 Fin15AnchoredAtom2751
    Fin15AnchoredAtom3056 Fin15AnchoredAtom3057 Fin15AnchoredAtom3058 Fin15AnchoredAtom3084
    Fin15AnchoredAtom3085 Fin15AnchoredAtom3086 Fin15AnchoredAtom3148 Fin15AnchoredAtom3149
    Fin15AnchoredAtom3150 Fin15AnchoredAtom3206 Fin15AnchoredAtom3268 Fin15AnchoredAtom3269
    Fin15AnchoredAtom3270 Fin15AnchoredAtom3326 Fin15AnchoredAtom3466 Fin15AnchoredAtom4093
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

theorem fin15Anchored_clause30844 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1890 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1914 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1921 chi ∧
      ¬Fin15AnchoredAtom1922 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1959 chi ∧
      ¬Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom1966 chi ∧
      ¬Fin15AnchoredAtom1967 chi ∧
      ¬Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom2051 chi ∧
      ¬Fin15AnchoredAtom2052 chi ∧
      ¬Fin15AnchoredAtom2057 chi ∧
      ¬Fin15AnchoredAtom2072 chi ∧
      ¬Fin15AnchoredAtom2344 chi ∧
      ¬Fin15AnchoredAtom2345 chi ∧
      ¬Fin15AnchoredAtom2346 chi ∧
      ¬Fin15AnchoredAtom2351 chi ∧
      ¬Fin15AnchoredAtom2352 chi ∧
      ¬Fin15AnchoredAtom2357 chi ∧
      ¬Fin15AnchoredAtom2436 chi ∧
      ¬Fin15AnchoredAtom2437 chi ∧
      ¬Fin15AnchoredAtom2442 chi ∧
      ¬Fin15AnchoredAtom2457 chi ∧
      ¬Fin15AnchoredAtom2556 chi ∧
      ¬Fin15AnchoredAtom2557 chi ∧
      ¬Fin15AnchoredAtom2562 chi ∧
      ¬Fin15AnchoredAtom2577 chi ∧
      ¬Fin15AnchoredAtom2752 chi ∧
      ¬Fin15AnchoredAtom3059 chi ∧
      ¬Fin15AnchoredAtom3060 chi ∧
      ¬Fin15AnchoredAtom3061 chi ∧
      ¬Fin15AnchoredAtom3066 chi ∧
      ¬Fin15AnchoredAtom3067 chi ∧
      ¬Fin15AnchoredAtom3072 chi ∧
      ¬Fin15AnchoredAtom3151 chi ∧
      ¬Fin15AnchoredAtom3152 chi ∧
      ¬Fin15AnchoredAtom3157 chi ∧
      ¬Fin15AnchoredAtom3172 chi ∧
      ¬Fin15AnchoredAtom3271 chi ∧
      ¬Fin15AnchoredAtom3272 chi ∧
      ¬Fin15AnchoredAtom3277 chi ∧
      ¬Fin15AnchoredAtom3292 chi ∧
      ¬Fin15AnchoredAtom3467 chi ∧
      ¬Fin15AnchoredAtom4096 chi ∧
      ¬Fin15AnchoredAtom4097 chi ∧
      ¬Fin15AnchoredAtom4102 chi ∧
      ¬Fin15AnchoredAtom4117 chi ∧
      ¬Fin15AnchoredAtom4292 chi ∧
      ¬Fin15AnchoredAtom4502 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 7, 8, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask01947
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1889 Fin15AnchoredAtom1890 Fin15AnchoredAtom1891
    Fin15AnchoredAtom1892 Fin15AnchoredAtom1914 Fin15AnchoredAtom1915 Fin15AnchoredAtom1916
    Fin15AnchoredAtom1921 Fin15AnchoredAtom1922 Fin15AnchoredAtom1927 Fin15AnchoredAtom1959
    Fin15AnchoredAtom1960 Fin15AnchoredAtom1961 Fin15AnchoredAtom1966 Fin15AnchoredAtom1967
    Fin15AnchoredAtom1972 Fin15AnchoredAtom2051 Fin15AnchoredAtom2052 Fin15AnchoredAtom2057
    Fin15AnchoredAtom2072 Fin15AnchoredAtom2344 Fin15AnchoredAtom2345 Fin15AnchoredAtom2346
    Fin15AnchoredAtom2351 Fin15AnchoredAtom2352 Fin15AnchoredAtom2357 Fin15AnchoredAtom2436
    Fin15AnchoredAtom2437 Fin15AnchoredAtom2442 Fin15AnchoredAtom2457 Fin15AnchoredAtom2556
    Fin15AnchoredAtom2557 Fin15AnchoredAtom2562 Fin15AnchoredAtom2577 Fin15AnchoredAtom2752
    Fin15AnchoredAtom3059 Fin15AnchoredAtom3060 Fin15AnchoredAtom3061 Fin15AnchoredAtom3066
    Fin15AnchoredAtom3067 Fin15AnchoredAtom3072 Fin15AnchoredAtom3151 Fin15AnchoredAtom3152
    Fin15AnchoredAtom3157 Fin15AnchoredAtom3172 Fin15AnchoredAtom3271 Fin15AnchoredAtom3272
    Fin15AnchoredAtom3277 Fin15AnchoredAtom3292 Fin15AnchoredAtom3467 Fin15AnchoredAtom4096
    Fin15AnchoredAtom4097 Fin15AnchoredAtom4102 Fin15AnchoredAtom4117 Fin15AnchoredAtom4292
    Fin15AnchoredAtom4502 at hbad
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

theorem fin15Anchored_clause30845 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1890 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1914 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1921 chi ∧
      ¬Fin15AnchoredAtom1924 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom1959 chi ∧
      ¬Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom1966 chi ∧
      ¬Fin15AnchoredAtom1969 chi ∧
      ¬Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom2051 chi ∧
      ¬Fin15AnchoredAtom2054 chi ∧
      ¬Fin15AnchoredAtom2059 chi ∧
      ¬Fin15AnchoredAtom2074 chi ∧
      ¬Fin15AnchoredAtom2344 chi ∧
      ¬Fin15AnchoredAtom2345 chi ∧
      ¬Fin15AnchoredAtom2348 chi ∧
      ¬Fin15AnchoredAtom2351 chi ∧
      ¬Fin15AnchoredAtom2354 chi ∧
      ¬Fin15AnchoredAtom2359 chi ∧
      ¬Fin15AnchoredAtom2436 chi ∧
      ¬Fin15AnchoredAtom2439 chi ∧
      ¬Fin15AnchoredAtom2444 chi ∧
      ¬Fin15AnchoredAtom2459 chi ∧
      ¬Fin15AnchoredAtom2556 chi ∧
      ¬Fin15AnchoredAtom2559 chi ∧
      ¬Fin15AnchoredAtom2564 chi ∧
      ¬Fin15AnchoredAtom2579 chi ∧
      ¬Fin15AnchoredAtom2754 chi ∧
      ¬Fin15AnchoredAtom3059 chi ∧
      ¬Fin15AnchoredAtom3060 chi ∧
      ¬Fin15AnchoredAtom3063 chi ∧
      ¬Fin15AnchoredAtom3066 chi ∧
      ¬Fin15AnchoredAtom3069 chi ∧
      ¬Fin15AnchoredAtom3074 chi ∧
      ¬Fin15AnchoredAtom3151 chi ∧
      ¬Fin15AnchoredAtom3154 chi ∧
      ¬Fin15AnchoredAtom3159 chi ∧
      ¬Fin15AnchoredAtom3174 chi ∧
      ¬Fin15AnchoredAtom3271 chi ∧
      ¬Fin15AnchoredAtom3274 chi ∧
      ¬Fin15AnchoredAtom3279 chi ∧
      ¬Fin15AnchoredAtom3294 chi ∧
      ¬Fin15AnchoredAtom3469 chi ∧
      ¬Fin15AnchoredAtom4096 chi ∧
      ¬Fin15AnchoredAtom4099 chi ∧
      ¬Fin15AnchoredAtom4104 chi ∧
      ¬Fin15AnchoredAtom4119 chi ∧
      ¬Fin15AnchoredAtom4294 chi ∧
      ¬Fin15AnchoredAtom4504 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 7, 8, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05019
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1889 Fin15AnchoredAtom1890 Fin15AnchoredAtom1891
    Fin15AnchoredAtom1894 Fin15AnchoredAtom1914 Fin15AnchoredAtom1915 Fin15AnchoredAtom1918
    Fin15AnchoredAtom1921 Fin15AnchoredAtom1924 Fin15AnchoredAtom1929 Fin15AnchoredAtom1959
    Fin15AnchoredAtom1960 Fin15AnchoredAtom1963 Fin15AnchoredAtom1966 Fin15AnchoredAtom1969
    Fin15AnchoredAtom1974 Fin15AnchoredAtom2051 Fin15AnchoredAtom2054 Fin15AnchoredAtom2059
    Fin15AnchoredAtom2074 Fin15AnchoredAtom2344 Fin15AnchoredAtom2345 Fin15AnchoredAtom2348
    Fin15AnchoredAtom2351 Fin15AnchoredAtom2354 Fin15AnchoredAtom2359 Fin15AnchoredAtom2436
    Fin15AnchoredAtom2439 Fin15AnchoredAtom2444 Fin15AnchoredAtom2459 Fin15AnchoredAtom2556
    Fin15AnchoredAtom2559 Fin15AnchoredAtom2564 Fin15AnchoredAtom2579 Fin15AnchoredAtom2754
    Fin15AnchoredAtom3059 Fin15AnchoredAtom3060 Fin15AnchoredAtom3063 Fin15AnchoredAtom3066
    Fin15AnchoredAtom3069 Fin15AnchoredAtom3074 Fin15AnchoredAtom3151 Fin15AnchoredAtom3154
    Fin15AnchoredAtom3159 Fin15AnchoredAtom3174 Fin15AnchoredAtom3271 Fin15AnchoredAtom3274
    Fin15AnchoredAtom3279 Fin15AnchoredAtom3294 Fin15AnchoredAtom3469 Fin15AnchoredAtom4096
    Fin15AnchoredAtom4099 Fin15AnchoredAtom4104 Fin15AnchoredAtom4119 Fin15AnchoredAtom4294
    Fin15AnchoredAtom4504 at hbad
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

theorem fin15Anchored_clause30846 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1890 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1914 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1921 chi ∧
      ¬Fin15AnchoredAtom1925 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1959 chi ∧
      ¬Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom1966 chi ∧
      ¬Fin15AnchoredAtom1970 chi ∧
      ¬Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom2051 chi ∧
      ¬Fin15AnchoredAtom2055 chi ∧
      ¬Fin15AnchoredAtom2060 chi ∧
      ¬Fin15AnchoredAtom2075 chi ∧
      ¬Fin15AnchoredAtom2344 chi ∧
      ¬Fin15AnchoredAtom2345 chi ∧
      ¬Fin15AnchoredAtom2349 chi ∧
      ¬Fin15AnchoredAtom2351 chi ∧
      ¬Fin15AnchoredAtom2355 chi ∧
      ¬Fin15AnchoredAtom2360 chi ∧
      ¬Fin15AnchoredAtom2436 chi ∧
      ¬Fin15AnchoredAtom2440 chi ∧
      ¬Fin15AnchoredAtom2445 chi ∧
      ¬Fin15AnchoredAtom2460 chi ∧
      ¬Fin15AnchoredAtom2556 chi ∧
      ¬Fin15AnchoredAtom2560 chi ∧
      ¬Fin15AnchoredAtom2565 chi ∧
      ¬Fin15AnchoredAtom2580 chi ∧
      ¬Fin15AnchoredAtom2755 chi ∧
      ¬Fin15AnchoredAtom3059 chi ∧
      ¬Fin15AnchoredAtom3060 chi ∧
      ¬Fin15AnchoredAtom3064 chi ∧
      ¬Fin15AnchoredAtom3066 chi ∧
      ¬Fin15AnchoredAtom3070 chi ∧
      ¬Fin15AnchoredAtom3075 chi ∧
      ¬Fin15AnchoredAtom3151 chi ∧
      ¬Fin15AnchoredAtom3155 chi ∧
      ¬Fin15AnchoredAtom3160 chi ∧
      ¬Fin15AnchoredAtom3175 chi ∧
      ¬Fin15AnchoredAtom3271 chi ∧
      ¬Fin15AnchoredAtom3275 chi ∧
      ¬Fin15AnchoredAtom3280 chi ∧
      ¬Fin15AnchoredAtom3295 chi ∧
      ¬Fin15AnchoredAtom3470 chi ∧
      ¬Fin15AnchoredAtom4096 chi ∧
      ¬Fin15AnchoredAtom4100 chi ∧
      ¬Fin15AnchoredAtom4105 chi ∧
      ¬Fin15AnchoredAtom4120 chi ∧
      ¬Fin15AnchoredAtom4295 chi ∧
      ¬Fin15AnchoredAtom4505 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 7, 8, 9, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09115
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1889 Fin15AnchoredAtom1890 Fin15AnchoredAtom1891
    Fin15AnchoredAtom1895 Fin15AnchoredAtom1914 Fin15AnchoredAtom1915 Fin15AnchoredAtom1919
    Fin15AnchoredAtom1921 Fin15AnchoredAtom1925 Fin15AnchoredAtom1930 Fin15AnchoredAtom1959
    Fin15AnchoredAtom1960 Fin15AnchoredAtom1964 Fin15AnchoredAtom1966 Fin15AnchoredAtom1970
    Fin15AnchoredAtom1975 Fin15AnchoredAtom2051 Fin15AnchoredAtom2055 Fin15AnchoredAtom2060
    Fin15AnchoredAtom2075 Fin15AnchoredAtom2344 Fin15AnchoredAtom2345 Fin15AnchoredAtom2349
    Fin15AnchoredAtom2351 Fin15AnchoredAtom2355 Fin15AnchoredAtom2360 Fin15AnchoredAtom2436
    Fin15AnchoredAtom2440 Fin15AnchoredAtom2445 Fin15AnchoredAtom2460 Fin15AnchoredAtom2556
    Fin15AnchoredAtom2560 Fin15AnchoredAtom2565 Fin15AnchoredAtom2580 Fin15AnchoredAtom2755
    Fin15AnchoredAtom3059 Fin15AnchoredAtom3060 Fin15AnchoredAtom3064 Fin15AnchoredAtom3066
    Fin15AnchoredAtom3070 Fin15AnchoredAtom3075 Fin15AnchoredAtom3151 Fin15AnchoredAtom3155
    Fin15AnchoredAtom3160 Fin15AnchoredAtom3175 Fin15AnchoredAtom3271 Fin15AnchoredAtom3275
    Fin15AnchoredAtom3280 Fin15AnchoredAtom3295 Fin15AnchoredAtom3470 Fin15AnchoredAtom4096
    Fin15AnchoredAtom4100 Fin15AnchoredAtom4105 Fin15AnchoredAtom4120 Fin15AnchoredAtom4295
    Fin15AnchoredAtom4505 at hbad
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

theorem fin15Anchored_clause30847 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1890 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1914 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1922 chi ∧
      ¬Fin15AnchoredAtom1924 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom1959 chi ∧
      ¬Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom1967 chi ∧
      ¬Fin15AnchoredAtom1969 chi ∧
      ¬Fin15AnchoredAtom1978 chi ∧
      ¬Fin15AnchoredAtom2052 chi ∧
      ¬Fin15AnchoredAtom2054 chi ∧
      ¬Fin15AnchoredAtom2063 chi ∧
      ¬Fin15AnchoredAtom2078 chi ∧
      ¬Fin15AnchoredAtom2344 chi ∧
      ¬Fin15AnchoredAtom2346 chi ∧
      ¬Fin15AnchoredAtom2348 chi ∧
      ¬Fin15AnchoredAtom2352 chi ∧
      ¬Fin15AnchoredAtom2354 chi ∧
      ¬Fin15AnchoredAtom2363 chi ∧
      ¬Fin15AnchoredAtom2437 chi ∧
      ¬Fin15AnchoredAtom2439 chi ∧
      ¬Fin15AnchoredAtom2448 chi ∧
      ¬Fin15AnchoredAtom2463 chi ∧
      ¬Fin15AnchoredAtom2557 chi ∧
      ¬Fin15AnchoredAtom2559 chi ∧
      ¬Fin15AnchoredAtom2568 chi ∧
      ¬Fin15AnchoredAtom2583 chi ∧
      ¬Fin15AnchoredAtom2758 chi ∧
      ¬Fin15AnchoredAtom3059 chi ∧
      ¬Fin15AnchoredAtom3061 chi ∧
      ¬Fin15AnchoredAtom3063 chi ∧
      ¬Fin15AnchoredAtom3067 chi ∧
      ¬Fin15AnchoredAtom3069 chi ∧
      ¬Fin15AnchoredAtom3078 chi ∧
      ¬Fin15AnchoredAtom3152 chi ∧
      ¬Fin15AnchoredAtom3154 chi ∧
      ¬Fin15AnchoredAtom3163 chi ∧
      ¬Fin15AnchoredAtom3178 chi ∧
      ¬Fin15AnchoredAtom3272 chi ∧
      ¬Fin15AnchoredAtom3274 chi ∧
      ¬Fin15AnchoredAtom3283 chi ∧
      ¬Fin15AnchoredAtom3298 chi ∧
      ¬Fin15AnchoredAtom3473 chi ∧
      ¬Fin15AnchoredAtom4097 chi ∧
      ¬Fin15AnchoredAtom4099 chi ∧
      ¬Fin15AnchoredAtom4108 chi ∧
      ¬Fin15AnchoredAtom4123 chi ∧
      ¬Fin15AnchoredAtom4298 chi ∧
      ¬Fin15AnchoredAtom4508 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 7, 8, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05531
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1889 Fin15AnchoredAtom1890 Fin15AnchoredAtom1892
    Fin15AnchoredAtom1894 Fin15AnchoredAtom1914 Fin15AnchoredAtom1916 Fin15AnchoredAtom1918
    Fin15AnchoredAtom1922 Fin15AnchoredAtom1924 Fin15AnchoredAtom1933 Fin15AnchoredAtom1959
    Fin15AnchoredAtom1961 Fin15AnchoredAtom1963 Fin15AnchoredAtom1967 Fin15AnchoredAtom1969
    Fin15AnchoredAtom1978 Fin15AnchoredAtom2052 Fin15AnchoredAtom2054 Fin15AnchoredAtom2063
    Fin15AnchoredAtom2078 Fin15AnchoredAtom2344 Fin15AnchoredAtom2346 Fin15AnchoredAtom2348
    Fin15AnchoredAtom2352 Fin15AnchoredAtom2354 Fin15AnchoredAtom2363 Fin15AnchoredAtom2437
    Fin15AnchoredAtom2439 Fin15AnchoredAtom2448 Fin15AnchoredAtom2463 Fin15AnchoredAtom2557
    Fin15AnchoredAtom2559 Fin15AnchoredAtom2568 Fin15AnchoredAtom2583 Fin15AnchoredAtom2758
    Fin15AnchoredAtom3059 Fin15AnchoredAtom3061 Fin15AnchoredAtom3063 Fin15AnchoredAtom3067
    Fin15AnchoredAtom3069 Fin15AnchoredAtom3078 Fin15AnchoredAtom3152 Fin15AnchoredAtom3154
    Fin15AnchoredAtom3163 Fin15AnchoredAtom3178 Fin15AnchoredAtom3272 Fin15AnchoredAtom3274
    Fin15AnchoredAtom3283 Fin15AnchoredAtom3298 Fin15AnchoredAtom3473 Fin15AnchoredAtom4097
    Fin15AnchoredAtom4099 Fin15AnchoredAtom4108 Fin15AnchoredAtom4123 Fin15AnchoredAtom4298
    Fin15AnchoredAtom4508 at hbad
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
