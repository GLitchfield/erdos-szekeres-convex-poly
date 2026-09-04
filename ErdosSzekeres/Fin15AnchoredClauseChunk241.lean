module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 241. -/

theorem fin15Anchored_clause30848 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1890 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1914 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1922 chi ∧
      ¬Fin15AnchoredAtom1925 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom1959 chi ∧
      ¬Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom1967 chi ∧
      ¬Fin15AnchoredAtom1970 chi ∧
      ¬Fin15AnchoredAtom1979 chi ∧
      ¬Fin15AnchoredAtom2052 chi ∧
      ¬Fin15AnchoredAtom2055 chi ∧
      ¬Fin15AnchoredAtom2064 chi ∧
      ¬Fin15AnchoredAtom2079 chi ∧
      ¬Fin15AnchoredAtom2344 chi ∧
      ¬Fin15AnchoredAtom2346 chi ∧
      ¬Fin15AnchoredAtom2349 chi ∧
      ¬Fin15AnchoredAtom2352 chi ∧
      ¬Fin15AnchoredAtom2355 chi ∧
      ¬Fin15AnchoredAtom2364 chi ∧
      ¬Fin15AnchoredAtom2437 chi ∧
      ¬Fin15AnchoredAtom2440 chi ∧
      ¬Fin15AnchoredAtom2449 chi ∧
      ¬Fin15AnchoredAtom2464 chi ∧
      ¬Fin15AnchoredAtom2557 chi ∧
      ¬Fin15AnchoredAtom2560 chi ∧
      ¬Fin15AnchoredAtom2569 chi ∧
      ¬Fin15AnchoredAtom2584 chi ∧
      ¬Fin15AnchoredAtom2759 chi ∧
      ¬Fin15AnchoredAtom3059 chi ∧
      ¬Fin15AnchoredAtom3061 chi ∧
      ¬Fin15AnchoredAtom3064 chi ∧
      ¬Fin15AnchoredAtom3067 chi ∧
      ¬Fin15AnchoredAtom3070 chi ∧
      ¬Fin15AnchoredAtom3079 chi ∧
      ¬Fin15AnchoredAtom3152 chi ∧
      ¬Fin15AnchoredAtom3155 chi ∧
      ¬Fin15AnchoredAtom3164 chi ∧
      ¬Fin15AnchoredAtom3179 chi ∧
      ¬Fin15AnchoredAtom3272 chi ∧
      ¬Fin15AnchoredAtom3275 chi ∧
      ¬Fin15AnchoredAtom3284 chi ∧
      ¬Fin15AnchoredAtom3299 chi ∧
      ¬Fin15AnchoredAtom3474 chi ∧
      ¬Fin15AnchoredAtom4097 chi ∧
      ¬Fin15AnchoredAtom4100 chi ∧
      ¬Fin15AnchoredAtom4109 chi ∧
      ¬Fin15AnchoredAtom4124 chi ∧
      ¬Fin15AnchoredAtom4299 chi ∧
      ¬Fin15AnchoredAtom4509 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 7, 8, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09627
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1889 Fin15AnchoredAtom1890 Fin15AnchoredAtom1892
    Fin15AnchoredAtom1895 Fin15AnchoredAtom1914 Fin15AnchoredAtom1916 Fin15AnchoredAtom1919
    Fin15AnchoredAtom1922 Fin15AnchoredAtom1925 Fin15AnchoredAtom1934 Fin15AnchoredAtom1959
    Fin15AnchoredAtom1961 Fin15AnchoredAtom1964 Fin15AnchoredAtom1967 Fin15AnchoredAtom1970
    Fin15AnchoredAtom1979 Fin15AnchoredAtom2052 Fin15AnchoredAtom2055 Fin15AnchoredAtom2064
    Fin15AnchoredAtom2079 Fin15AnchoredAtom2344 Fin15AnchoredAtom2346 Fin15AnchoredAtom2349
    Fin15AnchoredAtom2352 Fin15AnchoredAtom2355 Fin15AnchoredAtom2364 Fin15AnchoredAtom2437
    Fin15AnchoredAtom2440 Fin15AnchoredAtom2449 Fin15AnchoredAtom2464 Fin15AnchoredAtom2557
    Fin15AnchoredAtom2560 Fin15AnchoredAtom2569 Fin15AnchoredAtom2584 Fin15AnchoredAtom2759
    Fin15AnchoredAtom3059 Fin15AnchoredAtom3061 Fin15AnchoredAtom3064 Fin15AnchoredAtom3067
    Fin15AnchoredAtom3070 Fin15AnchoredAtom3079 Fin15AnchoredAtom3152 Fin15AnchoredAtom3155
    Fin15AnchoredAtom3164 Fin15AnchoredAtom3179 Fin15AnchoredAtom3272 Fin15AnchoredAtom3275
    Fin15AnchoredAtom3284 Fin15AnchoredAtom3299 Fin15AnchoredAtom3474 Fin15AnchoredAtom4097
    Fin15AnchoredAtom4100 Fin15AnchoredAtom4109 Fin15AnchoredAtom4124 Fin15AnchoredAtom4299
    Fin15AnchoredAtom4509 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30849 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1890 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1914 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1925 chi ∧
      ¬Fin15AnchoredAtom1926 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
      ¬Fin15AnchoredAtom1959 chi ∧
      ¬Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom1970 chi ∧
      ¬Fin15AnchoredAtom1971 chi ∧
      ¬Fin15AnchoredAtom1986 chi ∧
      ¬Fin15AnchoredAtom2055 chi ∧
      ¬Fin15AnchoredAtom2056 chi ∧
      ¬Fin15AnchoredAtom2071 chi ∧
      ¬Fin15AnchoredAtom2086 chi ∧
      ¬Fin15AnchoredAtom2344 chi ∧
      ¬Fin15AnchoredAtom2349 chi ∧
      ¬Fin15AnchoredAtom2350 chi ∧
      ¬Fin15AnchoredAtom2355 chi ∧
      ¬Fin15AnchoredAtom2356 chi ∧
      ¬Fin15AnchoredAtom2371 chi ∧
      ¬Fin15AnchoredAtom2440 chi ∧
      ¬Fin15AnchoredAtom2441 chi ∧
      ¬Fin15AnchoredAtom2456 chi ∧
      ¬Fin15AnchoredAtom2471 chi ∧
      ¬Fin15AnchoredAtom2560 chi ∧
      ¬Fin15AnchoredAtom2561 chi ∧
      ¬Fin15AnchoredAtom2576 chi ∧
      ¬Fin15AnchoredAtom2591 chi ∧
      ¬Fin15AnchoredAtom2766 chi ∧
      ¬Fin15AnchoredAtom3059 chi ∧
      ¬Fin15AnchoredAtom3064 chi ∧
      ¬Fin15AnchoredAtom3065 chi ∧
      ¬Fin15AnchoredAtom3070 chi ∧
      ¬Fin15AnchoredAtom3071 chi ∧
      ¬Fin15AnchoredAtom3086 chi ∧
      ¬Fin15AnchoredAtom3155 chi ∧
      ¬Fin15AnchoredAtom3156 chi ∧
      ¬Fin15AnchoredAtom3171 chi ∧
      ¬Fin15AnchoredAtom3186 chi ∧
      ¬Fin15AnchoredAtom3275 chi ∧
      ¬Fin15AnchoredAtom3276 chi ∧
      ¬Fin15AnchoredAtom3291 chi ∧
      ¬Fin15AnchoredAtom3306 chi ∧
      ¬Fin15AnchoredAtom3481 chi ∧
      ¬Fin15AnchoredAtom4100 chi ∧
      ¬Fin15AnchoredAtom4101 chi ∧
      ¬Fin15AnchoredAtom4116 chi ∧
      ¬Fin15AnchoredAtom4131 chi ∧
      ¬Fin15AnchoredAtom4306 chi ∧
      ¬Fin15AnchoredAtom4516 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 7, 8, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask24987
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1889 Fin15AnchoredAtom1890 Fin15AnchoredAtom1895
    Fin15AnchoredAtom1896 Fin15AnchoredAtom1914 Fin15AnchoredAtom1919 Fin15AnchoredAtom1920
    Fin15AnchoredAtom1925 Fin15AnchoredAtom1926 Fin15AnchoredAtom1941 Fin15AnchoredAtom1959
    Fin15AnchoredAtom1964 Fin15AnchoredAtom1965 Fin15AnchoredAtom1970 Fin15AnchoredAtom1971
    Fin15AnchoredAtom1986 Fin15AnchoredAtom2055 Fin15AnchoredAtom2056 Fin15AnchoredAtom2071
    Fin15AnchoredAtom2086 Fin15AnchoredAtom2344 Fin15AnchoredAtom2349 Fin15AnchoredAtom2350
    Fin15AnchoredAtom2355 Fin15AnchoredAtom2356 Fin15AnchoredAtom2371 Fin15AnchoredAtom2440
    Fin15AnchoredAtom2441 Fin15AnchoredAtom2456 Fin15AnchoredAtom2471 Fin15AnchoredAtom2560
    Fin15AnchoredAtom2561 Fin15AnchoredAtom2576 Fin15AnchoredAtom2591 Fin15AnchoredAtom2766
    Fin15AnchoredAtom3059 Fin15AnchoredAtom3064 Fin15AnchoredAtom3065 Fin15AnchoredAtom3070
    Fin15AnchoredAtom3071 Fin15AnchoredAtom3086 Fin15AnchoredAtom3155 Fin15AnchoredAtom3156
    Fin15AnchoredAtom3171 Fin15AnchoredAtom3186 Fin15AnchoredAtom3275 Fin15AnchoredAtom3276
    Fin15AnchoredAtom3291 Fin15AnchoredAtom3306 Fin15AnchoredAtom3481 Fin15AnchoredAtom4100
    Fin15AnchoredAtom4101 Fin15AnchoredAtom4116 Fin15AnchoredAtom4131 Fin15AnchoredAtom4306
    Fin15AnchoredAtom4516 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30850 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1893 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1917 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1928 chi ∧
      ¬Fin15AnchoredAtom1932 chi ∧
      ¬Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom1962 chi ∧
      ¬Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom1973 chi ∧
      ¬Fin15AnchoredAtom1977 chi ∧
      ¬Fin15AnchoredAtom2057 chi ∧
      ¬Fin15AnchoredAtom2058 chi ∧
      ¬Fin15AnchoredAtom2062 chi ∧
      ¬Fin15AnchoredAtom2087 chi ∧
      ¬Fin15AnchoredAtom2345 chi ∧
      ¬Fin15AnchoredAtom2346 chi ∧
      ¬Fin15AnchoredAtom2347 chi ∧
      ¬Fin15AnchoredAtom2357 chi ∧
      ¬Fin15AnchoredAtom2358 chi ∧
      ¬Fin15AnchoredAtom2362 chi ∧
      ¬Fin15AnchoredAtom2442 chi ∧
      ¬Fin15AnchoredAtom2443 chi ∧
      ¬Fin15AnchoredAtom2447 chi ∧
      ¬Fin15AnchoredAtom2472 chi ∧
      ¬Fin15AnchoredAtom2562 chi ∧
      ¬Fin15AnchoredAtom2563 chi ∧
      ¬Fin15AnchoredAtom2567 chi ∧
      ¬Fin15AnchoredAtom2592 chi ∧
      ¬Fin15AnchoredAtom2767 chi ∧
      ¬Fin15AnchoredAtom3060 chi ∧
      ¬Fin15AnchoredAtom3061 chi ∧
      ¬Fin15AnchoredAtom3062 chi ∧
      ¬Fin15AnchoredAtom3072 chi ∧
      ¬Fin15AnchoredAtom3073 chi ∧
      ¬Fin15AnchoredAtom3077 chi ∧
      ¬Fin15AnchoredAtom3157 chi ∧
      ¬Fin15AnchoredAtom3158 chi ∧
      ¬Fin15AnchoredAtom3162 chi ∧
      ¬Fin15AnchoredAtom3187 chi ∧
      ¬Fin15AnchoredAtom3277 chi ∧
      ¬Fin15AnchoredAtom3278 chi ∧
      ¬Fin15AnchoredAtom3282 chi ∧
      ¬Fin15AnchoredAtom3307 chi ∧
      ¬Fin15AnchoredAtom3482 chi ∧
      ¬Fin15AnchoredAtom4102 chi ∧
      ¬Fin15AnchoredAtom4103 chi ∧
      ¬Fin15AnchoredAtom4107 chi ∧
      ¬Fin15AnchoredAtom4132 chi ∧
      ¬Fin15AnchoredAtom4307 chi ∧
      ¬Fin15AnchoredAtom4517 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 7, 9, 10, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask03739
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1889 Fin15AnchoredAtom1891 Fin15AnchoredAtom1892
    Fin15AnchoredAtom1893 Fin15AnchoredAtom1915 Fin15AnchoredAtom1916 Fin15AnchoredAtom1917
    Fin15AnchoredAtom1927 Fin15AnchoredAtom1928 Fin15AnchoredAtom1932 Fin15AnchoredAtom1960
    Fin15AnchoredAtom1961 Fin15AnchoredAtom1962 Fin15AnchoredAtom1972 Fin15AnchoredAtom1973
    Fin15AnchoredAtom1977 Fin15AnchoredAtom2057 Fin15AnchoredAtom2058 Fin15AnchoredAtom2062
    Fin15AnchoredAtom2087 Fin15AnchoredAtom2345 Fin15AnchoredAtom2346 Fin15AnchoredAtom2347
    Fin15AnchoredAtom2357 Fin15AnchoredAtom2358 Fin15AnchoredAtom2362 Fin15AnchoredAtom2442
    Fin15AnchoredAtom2443 Fin15AnchoredAtom2447 Fin15AnchoredAtom2472 Fin15AnchoredAtom2562
    Fin15AnchoredAtom2563 Fin15AnchoredAtom2567 Fin15AnchoredAtom2592 Fin15AnchoredAtom2767
    Fin15AnchoredAtom3060 Fin15AnchoredAtom3061 Fin15AnchoredAtom3062 Fin15AnchoredAtom3072
    Fin15AnchoredAtom3073 Fin15AnchoredAtom3077 Fin15AnchoredAtom3157 Fin15AnchoredAtom3158
    Fin15AnchoredAtom3162 Fin15AnchoredAtom3187 Fin15AnchoredAtom3277 Fin15AnchoredAtom3278
    Fin15AnchoredAtom3282 Fin15AnchoredAtom3307 Fin15AnchoredAtom3482 Fin15AnchoredAtom4102
    Fin15AnchoredAtom4103 Fin15AnchoredAtom4107 Fin15AnchoredAtom4132 Fin15AnchoredAtom4307
    Fin15AnchoredAtom4517 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30851 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
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
      ¬Fin15AnchoredAtom3060 chi ∧
      ¬Fin15AnchoredAtom3061 chi ∧
      ¬Fin15AnchoredAtom3063 chi ∧
      ¬Fin15AnchoredAtom3072 chi ∧
      ¬Fin15AnchoredAtom3074 chi ∧
      ¬Fin15AnchoredAtom3078 chi ∧
      ¬Fin15AnchoredAtom3157 chi ∧
      ¬Fin15AnchoredAtom3159 chi ∧
      ¬Fin15AnchoredAtom3163 chi ∧
      ¬Fin15AnchoredAtom3188 chi ∧
      ¬Fin15AnchoredAtom3277 chi ∧
      ¬Fin15AnchoredAtom3279 chi ∧
      ¬Fin15AnchoredAtom3283 chi ∧
      ¬Fin15AnchoredAtom3308 chi ∧
      ¬Fin15AnchoredAtom3483 chi ∧
      ¬Fin15AnchoredAtom4102 chi ∧
      ¬Fin15AnchoredAtom4104 chi ∧
      ¬Fin15AnchoredAtom4108 chi ∧
      ¬Fin15AnchoredAtom4133 chi ∧
      ¬Fin15AnchoredAtom4308 chi ∧
      ¬Fin15AnchoredAtom4518 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 7, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05787
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1889 Fin15AnchoredAtom1891 Fin15AnchoredAtom1892
    Fin15AnchoredAtom1894 Fin15AnchoredAtom1915 Fin15AnchoredAtom1916 Fin15AnchoredAtom1918
    Fin15AnchoredAtom1927 Fin15AnchoredAtom1929 Fin15AnchoredAtom1933 Fin15AnchoredAtom1960
    Fin15AnchoredAtom1961 Fin15AnchoredAtom1963 Fin15AnchoredAtom1972 Fin15AnchoredAtom1974
    Fin15AnchoredAtom1978 Fin15AnchoredAtom2057 Fin15AnchoredAtom2059 Fin15AnchoredAtom2063
    Fin15AnchoredAtom2088 Fin15AnchoredAtom2345 Fin15AnchoredAtom2346 Fin15AnchoredAtom2348
    Fin15AnchoredAtom2357 Fin15AnchoredAtom2359 Fin15AnchoredAtom2363 Fin15AnchoredAtom2442
    Fin15AnchoredAtom2444 Fin15AnchoredAtom2448 Fin15AnchoredAtom2473 Fin15AnchoredAtom2562
    Fin15AnchoredAtom2564 Fin15AnchoredAtom2568 Fin15AnchoredAtom2593 Fin15AnchoredAtom2768
    Fin15AnchoredAtom3060 Fin15AnchoredAtom3061 Fin15AnchoredAtom3063 Fin15AnchoredAtom3072
    Fin15AnchoredAtom3074 Fin15AnchoredAtom3078 Fin15AnchoredAtom3157 Fin15AnchoredAtom3159
    Fin15AnchoredAtom3163 Fin15AnchoredAtom3188 Fin15AnchoredAtom3277 Fin15AnchoredAtom3279
    Fin15AnchoredAtom3283 Fin15AnchoredAtom3308 Fin15AnchoredAtom3483 Fin15AnchoredAtom4102
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

theorem fin15Anchored_clause30852 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
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
      ¬Fin15AnchoredAtom3060 chi ∧
      ¬Fin15AnchoredAtom3061 chi ∧
      ¬Fin15AnchoredAtom3064 chi ∧
      ¬Fin15AnchoredAtom3072 chi ∧
      ¬Fin15AnchoredAtom3075 chi ∧
      ¬Fin15AnchoredAtom3079 chi ∧
      ¬Fin15AnchoredAtom3157 chi ∧
      ¬Fin15AnchoredAtom3160 chi ∧
      ¬Fin15AnchoredAtom3164 chi ∧
      ¬Fin15AnchoredAtom3189 chi ∧
      ¬Fin15AnchoredAtom3277 chi ∧
      ¬Fin15AnchoredAtom3280 chi ∧
      ¬Fin15AnchoredAtom3284 chi ∧
      ¬Fin15AnchoredAtom3309 chi ∧
      ¬Fin15AnchoredAtom3484 chi ∧
      ¬Fin15AnchoredAtom4102 chi ∧
      ¬Fin15AnchoredAtom4105 chi ∧
      ¬Fin15AnchoredAtom4109 chi ∧
      ¬Fin15AnchoredAtom4134 chi ∧
      ¬Fin15AnchoredAtom4309 chi ∧
      ¬Fin15AnchoredAtom4519 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 7, 9, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09883
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1889 Fin15AnchoredAtom1891 Fin15AnchoredAtom1892
    Fin15AnchoredAtom1895 Fin15AnchoredAtom1915 Fin15AnchoredAtom1916 Fin15AnchoredAtom1919
    Fin15AnchoredAtom1927 Fin15AnchoredAtom1930 Fin15AnchoredAtom1934 Fin15AnchoredAtom1960
    Fin15AnchoredAtom1961 Fin15AnchoredAtom1964 Fin15AnchoredAtom1972 Fin15AnchoredAtom1975
    Fin15AnchoredAtom1979 Fin15AnchoredAtom2057 Fin15AnchoredAtom2060 Fin15AnchoredAtom2064
    Fin15AnchoredAtom2089 Fin15AnchoredAtom2345 Fin15AnchoredAtom2346 Fin15AnchoredAtom2349
    Fin15AnchoredAtom2357 Fin15AnchoredAtom2360 Fin15AnchoredAtom2364 Fin15AnchoredAtom2442
    Fin15AnchoredAtom2445 Fin15AnchoredAtom2449 Fin15AnchoredAtom2474 Fin15AnchoredAtom2562
    Fin15AnchoredAtom2565 Fin15AnchoredAtom2569 Fin15AnchoredAtom2594 Fin15AnchoredAtom2769
    Fin15AnchoredAtom3060 Fin15AnchoredAtom3061 Fin15AnchoredAtom3064 Fin15AnchoredAtom3072
    Fin15AnchoredAtom3075 Fin15AnchoredAtom3079 Fin15AnchoredAtom3157 Fin15AnchoredAtom3160
    Fin15AnchoredAtom3164 Fin15AnchoredAtom3189 Fin15AnchoredAtom3277 Fin15AnchoredAtom3280
    Fin15AnchoredAtom3284 Fin15AnchoredAtom3309 Fin15AnchoredAtom3484 Fin15AnchoredAtom4102
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

theorem fin15Anchored_clause30853 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom1935 chi ∧
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
      ¬Fin15AnchoredAtom3060 chi ∧
      ¬Fin15AnchoredAtom3061 chi ∧
      ¬Fin15AnchoredAtom3065 chi ∧
      ¬Fin15AnchoredAtom3072 chi ∧
      ¬Fin15AnchoredAtom3076 chi ∧
      ¬Fin15AnchoredAtom3080 chi ∧
      ¬Fin15AnchoredAtom3157 chi ∧
      ¬Fin15AnchoredAtom3161 chi ∧
      ¬Fin15AnchoredAtom3165 chi ∧
      ¬Fin15AnchoredAtom3190 chi ∧
      ¬Fin15AnchoredAtom3277 chi ∧
      ¬Fin15AnchoredAtom3281 chi ∧
      ¬Fin15AnchoredAtom3285 chi ∧
      ¬Fin15AnchoredAtom3310 chi ∧
      ¬Fin15AnchoredAtom3485 chi ∧
      ¬Fin15AnchoredAtom4102 chi ∧
      ¬Fin15AnchoredAtom4106 chi ∧
      ¬Fin15AnchoredAtom4110 chi ∧
      ¬Fin15AnchoredAtom4135 chi ∧
      ¬Fin15AnchoredAtom4310 chi ∧
      ¬Fin15AnchoredAtom4520 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 7, 9, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask18075
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1889 Fin15AnchoredAtom1891 Fin15AnchoredAtom1892
    Fin15AnchoredAtom1896 Fin15AnchoredAtom1915 Fin15AnchoredAtom1916 Fin15AnchoredAtom1920
    Fin15AnchoredAtom1927 Fin15AnchoredAtom1931 Fin15AnchoredAtom1935 Fin15AnchoredAtom1960
    Fin15AnchoredAtom1961 Fin15AnchoredAtom1965 Fin15AnchoredAtom1972 Fin15AnchoredAtom1976
    Fin15AnchoredAtom1980 Fin15AnchoredAtom2057 Fin15AnchoredAtom2061 Fin15AnchoredAtom2065
    Fin15AnchoredAtom2090 Fin15AnchoredAtom2345 Fin15AnchoredAtom2346 Fin15AnchoredAtom2350
    Fin15AnchoredAtom2357 Fin15AnchoredAtom2361 Fin15AnchoredAtom2365 Fin15AnchoredAtom2442
    Fin15AnchoredAtom2446 Fin15AnchoredAtom2450 Fin15AnchoredAtom2475 Fin15AnchoredAtom2562
    Fin15AnchoredAtom2566 Fin15AnchoredAtom2570 Fin15AnchoredAtom2595 Fin15AnchoredAtom2770
    Fin15AnchoredAtom3060 Fin15AnchoredAtom3061 Fin15AnchoredAtom3065 Fin15AnchoredAtom3072
    Fin15AnchoredAtom3076 Fin15AnchoredAtom3080 Fin15AnchoredAtom3157 Fin15AnchoredAtom3161
    Fin15AnchoredAtom3165 Fin15AnchoredAtom3190 Fin15AnchoredAtom3277 Fin15AnchoredAtom3281
    Fin15AnchoredAtom3285 Fin15AnchoredAtom3310 Fin15AnchoredAtom3485 Fin15AnchoredAtom4102
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

theorem fin15Anchored_clause30854 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1939 chi ∧
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
      ¬Fin15AnchoredAtom3060 chi ∧
      ¬Fin15AnchoredAtom3063 chi ∧
      ¬Fin15AnchoredAtom3064 chi ∧
      ¬Fin15AnchoredAtom3074 chi ∧
      ¬Fin15AnchoredAtom3075 chi ∧
      ¬Fin15AnchoredAtom3084 chi ∧
      ¬Fin15AnchoredAtom3159 chi ∧
      ¬Fin15AnchoredAtom3160 chi ∧
      ¬Fin15AnchoredAtom3169 chi ∧
      ¬Fin15AnchoredAtom3194 chi ∧
      ¬Fin15AnchoredAtom3279 chi ∧
      ¬Fin15AnchoredAtom3280 chi ∧
      ¬Fin15AnchoredAtom3289 chi ∧
      ¬Fin15AnchoredAtom3314 chi ∧
      ¬Fin15AnchoredAtom3489 chi ∧
      ¬Fin15AnchoredAtom4104 chi ∧
      ¬Fin15AnchoredAtom4105 chi ∧
      ¬Fin15AnchoredAtom4114 chi ∧
      ¬Fin15AnchoredAtom4139 chi ∧
      ¬Fin15AnchoredAtom4314 chi ∧
      ¬Fin15AnchoredAtom4524 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 7, 9, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask12955
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1889 Fin15AnchoredAtom1891 Fin15AnchoredAtom1894
    Fin15AnchoredAtom1895 Fin15AnchoredAtom1915 Fin15AnchoredAtom1918 Fin15AnchoredAtom1919
    Fin15AnchoredAtom1929 Fin15AnchoredAtom1930 Fin15AnchoredAtom1939 Fin15AnchoredAtom1960
    Fin15AnchoredAtom1963 Fin15AnchoredAtom1964 Fin15AnchoredAtom1974 Fin15AnchoredAtom1975
    Fin15AnchoredAtom1984 Fin15AnchoredAtom2059 Fin15AnchoredAtom2060 Fin15AnchoredAtom2069
    Fin15AnchoredAtom2094 Fin15AnchoredAtom2345 Fin15AnchoredAtom2348 Fin15AnchoredAtom2349
    Fin15AnchoredAtom2359 Fin15AnchoredAtom2360 Fin15AnchoredAtom2369 Fin15AnchoredAtom2444
    Fin15AnchoredAtom2445 Fin15AnchoredAtom2454 Fin15AnchoredAtom2479 Fin15AnchoredAtom2564
    Fin15AnchoredAtom2565 Fin15AnchoredAtom2574 Fin15AnchoredAtom2599 Fin15AnchoredAtom2774
    Fin15AnchoredAtom3060 Fin15AnchoredAtom3063 Fin15AnchoredAtom3064 Fin15AnchoredAtom3074
    Fin15AnchoredAtom3075 Fin15AnchoredAtom3084 Fin15AnchoredAtom3159 Fin15AnchoredAtom3160
    Fin15AnchoredAtom3169 Fin15AnchoredAtom3194 Fin15AnchoredAtom3279 Fin15AnchoredAtom3280
    Fin15AnchoredAtom3289 Fin15AnchoredAtom3314 Fin15AnchoredAtom3489 Fin15AnchoredAtom4104
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

theorem fin15Anchored_clause30855 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom1940 chi ∧
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
      ¬Fin15AnchoredAtom3060 chi ∧
      ¬Fin15AnchoredAtom3063 chi ∧
      ¬Fin15AnchoredAtom3065 chi ∧
      ¬Fin15AnchoredAtom3074 chi ∧
      ¬Fin15AnchoredAtom3076 chi ∧
      ¬Fin15AnchoredAtom3085 chi ∧
      ¬Fin15AnchoredAtom3159 chi ∧
      ¬Fin15AnchoredAtom3161 chi ∧
      ¬Fin15AnchoredAtom3170 chi ∧
      ¬Fin15AnchoredAtom3195 chi ∧
      ¬Fin15AnchoredAtom3279 chi ∧
      ¬Fin15AnchoredAtom3281 chi ∧
      ¬Fin15AnchoredAtom3290 chi ∧
      ¬Fin15AnchoredAtom3315 chi ∧
      ¬Fin15AnchoredAtom3490 chi ∧
      ¬Fin15AnchoredAtom4104 chi ∧
      ¬Fin15AnchoredAtom4106 chi ∧
      ¬Fin15AnchoredAtom4115 chi ∧
      ¬Fin15AnchoredAtom4140 chi ∧
      ¬Fin15AnchoredAtom4315 chi ∧
      ¬Fin15AnchoredAtom4525 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 7, 9, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21147
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1889 Fin15AnchoredAtom1891 Fin15AnchoredAtom1894
    Fin15AnchoredAtom1896 Fin15AnchoredAtom1915 Fin15AnchoredAtom1918 Fin15AnchoredAtom1920
    Fin15AnchoredAtom1929 Fin15AnchoredAtom1931 Fin15AnchoredAtom1940 Fin15AnchoredAtom1960
    Fin15AnchoredAtom1963 Fin15AnchoredAtom1965 Fin15AnchoredAtom1974 Fin15AnchoredAtom1976
    Fin15AnchoredAtom1985 Fin15AnchoredAtom2059 Fin15AnchoredAtom2061 Fin15AnchoredAtom2070
    Fin15AnchoredAtom2095 Fin15AnchoredAtom2345 Fin15AnchoredAtom2348 Fin15AnchoredAtom2350
    Fin15AnchoredAtom2359 Fin15AnchoredAtom2361 Fin15AnchoredAtom2370 Fin15AnchoredAtom2444
    Fin15AnchoredAtom2446 Fin15AnchoredAtom2455 Fin15AnchoredAtom2480 Fin15AnchoredAtom2564
    Fin15AnchoredAtom2566 Fin15AnchoredAtom2575 Fin15AnchoredAtom2600 Fin15AnchoredAtom2775
    Fin15AnchoredAtom3060 Fin15AnchoredAtom3063 Fin15AnchoredAtom3065 Fin15AnchoredAtom3074
    Fin15AnchoredAtom3076 Fin15AnchoredAtom3085 Fin15AnchoredAtom3159 Fin15AnchoredAtom3161
    Fin15AnchoredAtom3170 Fin15AnchoredAtom3195 Fin15AnchoredAtom3279 Fin15AnchoredAtom3281
    Fin15AnchoredAtom3290 Fin15AnchoredAtom3315 Fin15AnchoredAtom3490 Fin15AnchoredAtom4104
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

theorem fin15Anchored_clause30856 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
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
      ¬Fin15AnchoredAtom3060 chi ∧
      ¬Fin15AnchoredAtom3064 chi ∧
      ¬Fin15AnchoredAtom3065 chi ∧
      ¬Fin15AnchoredAtom3075 chi ∧
      ¬Fin15AnchoredAtom3076 chi ∧
      ¬Fin15AnchoredAtom3086 chi ∧
      ¬Fin15AnchoredAtom3160 chi ∧
      ¬Fin15AnchoredAtom3161 chi ∧
      ¬Fin15AnchoredAtom3171 chi ∧
      ¬Fin15AnchoredAtom3196 chi ∧
      ¬Fin15AnchoredAtom3280 chi ∧
      ¬Fin15AnchoredAtom3281 chi ∧
      ¬Fin15AnchoredAtom3291 chi ∧
      ¬Fin15AnchoredAtom3316 chi ∧
      ¬Fin15AnchoredAtom3491 chi ∧
      ¬Fin15AnchoredAtom4105 chi ∧
      ¬Fin15AnchoredAtom4106 chi ∧
      ¬Fin15AnchoredAtom4116 chi ∧
      ¬Fin15AnchoredAtom4141 chi ∧
      ¬Fin15AnchoredAtom4316 chi ∧
      ¬Fin15AnchoredAtom4526 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 7, 9, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25243
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1889 Fin15AnchoredAtom1891 Fin15AnchoredAtom1895
    Fin15AnchoredAtom1896 Fin15AnchoredAtom1915 Fin15AnchoredAtom1919 Fin15AnchoredAtom1920
    Fin15AnchoredAtom1930 Fin15AnchoredAtom1931 Fin15AnchoredAtom1941 Fin15AnchoredAtom1960
    Fin15AnchoredAtom1964 Fin15AnchoredAtom1965 Fin15AnchoredAtom1975 Fin15AnchoredAtom1976
    Fin15AnchoredAtom1986 Fin15AnchoredAtom2060 Fin15AnchoredAtom2061 Fin15AnchoredAtom2071
    Fin15AnchoredAtom2096 Fin15AnchoredAtom2345 Fin15AnchoredAtom2349 Fin15AnchoredAtom2350
    Fin15AnchoredAtom2360 Fin15AnchoredAtom2361 Fin15AnchoredAtom2371 Fin15AnchoredAtom2445
    Fin15AnchoredAtom2446 Fin15AnchoredAtom2456 Fin15AnchoredAtom2481 Fin15AnchoredAtom2565
    Fin15AnchoredAtom2566 Fin15AnchoredAtom2576 Fin15AnchoredAtom2601 Fin15AnchoredAtom2776
    Fin15AnchoredAtom3060 Fin15AnchoredAtom3064 Fin15AnchoredAtom3065 Fin15AnchoredAtom3075
    Fin15AnchoredAtom3076 Fin15AnchoredAtom3086 Fin15AnchoredAtom3160 Fin15AnchoredAtom3161
    Fin15AnchoredAtom3171 Fin15AnchoredAtom3196 Fin15AnchoredAtom3280 Fin15AnchoredAtom3281
    Fin15AnchoredAtom3291 Fin15AnchoredAtom3316 Fin15AnchoredAtom3491 Fin15AnchoredAtom4105
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

theorem fin15Anchored_clause30857 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom1939 chi ∧
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
      ¬Fin15AnchoredAtom3061 chi ∧
      ¬Fin15AnchoredAtom3063 chi ∧
      ¬Fin15AnchoredAtom3064 chi ∧
      ¬Fin15AnchoredAtom3078 chi ∧
      ¬Fin15AnchoredAtom3079 chi ∧
      ¬Fin15AnchoredAtom3084 chi ∧
      ¬Fin15AnchoredAtom3163 chi ∧
      ¬Fin15AnchoredAtom3164 chi ∧
      ¬Fin15AnchoredAtom3169 chi ∧
      ¬Fin15AnchoredAtom3200 chi ∧
      ¬Fin15AnchoredAtom3283 chi ∧
      ¬Fin15AnchoredAtom3284 chi ∧
      ¬Fin15AnchoredAtom3289 chi ∧
      ¬Fin15AnchoredAtom3320 chi ∧
      ¬Fin15AnchoredAtom3495 chi ∧
      ¬Fin15AnchoredAtom4108 chi ∧
      ¬Fin15AnchoredAtom4109 chi ∧
      ¬Fin15AnchoredAtom4114 chi ∧
      ¬Fin15AnchoredAtom4145 chi ∧
      ¬Fin15AnchoredAtom4320 chi ∧
      ¬Fin15AnchoredAtom4530 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 7, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13467
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1889 Fin15AnchoredAtom1892 Fin15AnchoredAtom1894
    Fin15AnchoredAtom1895 Fin15AnchoredAtom1916 Fin15AnchoredAtom1918 Fin15AnchoredAtom1919
    Fin15AnchoredAtom1933 Fin15AnchoredAtom1934 Fin15AnchoredAtom1939 Fin15AnchoredAtom1961
    Fin15AnchoredAtom1963 Fin15AnchoredAtom1964 Fin15AnchoredAtom1978 Fin15AnchoredAtom1979
    Fin15AnchoredAtom1984 Fin15AnchoredAtom2063 Fin15AnchoredAtom2064 Fin15AnchoredAtom2069
    Fin15AnchoredAtom2100 Fin15AnchoredAtom2346 Fin15AnchoredAtom2348 Fin15AnchoredAtom2349
    Fin15AnchoredAtom2363 Fin15AnchoredAtom2364 Fin15AnchoredAtom2369 Fin15AnchoredAtom2448
    Fin15AnchoredAtom2449 Fin15AnchoredAtom2454 Fin15AnchoredAtom2485 Fin15AnchoredAtom2568
    Fin15AnchoredAtom2569 Fin15AnchoredAtom2574 Fin15AnchoredAtom2605 Fin15AnchoredAtom2780
    Fin15AnchoredAtom3061 Fin15AnchoredAtom3063 Fin15AnchoredAtom3064 Fin15AnchoredAtom3078
    Fin15AnchoredAtom3079 Fin15AnchoredAtom3084 Fin15AnchoredAtom3163 Fin15AnchoredAtom3164
    Fin15AnchoredAtom3169 Fin15AnchoredAtom3200 Fin15AnchoredAtom3283 Fin15AnchoredAtom3284
    Fin15AnchoredAtom3289 Fin15AnchoredAtom3320 Fin15AnchoredAtom3495 Fin15AnchoredAtom4108
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

theorem fin15Anchored_clause30858 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom1935 chi ∧
      ¬Fin15AnchoredAtom1940 chi ∧
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
      ¬Fin15AnchoredAtom3061 chi ∧
      ¬Fin15AnchoredAtom3063 chi ∧
      ¬Fin15AnchoredAtom3065 chi ∧
      ¬Fin15AnchoredAtom3078 chi ∧
      ¬Fin15AnchoredAtom3080 chi ∧
      ¬Fin15AnchoredAtom3085 chi ∧
      ¬Fin15AnchoredAtom3163 chi ∧
      ¬Fin15AnchoredAtom3165 chi ∧
      ¬Fin15AnchoredAtom3170 chi ∧
      ¬Fin15AnchoredAtom3201 chi ∧
      ¬Fin15AnchoredAtom3283 chi ∧
      ¬Fin15AnchoredAtom3285 chi ∧
      ¬Fin15AnchoredAtom3290 chi ∧
      ¬Fin15AnchoredAtom3321 chi ∧
      ¬Fin15AnchoredAtom3496 chi ∧
      ¬Fin15AnchoredAtom4108 chi ∧
      ¬Fin15AnchoredAtom4110 chi ∧
      ¬Fin15AnchoredAtom4115 chi ∧
      ¬Fin15AnchoredAtom4146 chi ∧
      ¬Fin15AnchoredAtom4321 chi ∧
      ¬Fin15AnchoredAtom4531 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 7, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21659
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1889 Fin15AnchoredAtom1892 Fin15AnchoredAtom1894
    Fin15AnchoredAtom1896 Fin15AnchoredAtom1916 Fin15AnchoredAtom1918 Fin15AnchoredAtom1920
    Fin15AnchoredAtom1933 Fin15AnchoredAtom1935 Fin15AnchoredAtom1940 Fin15AnchoredAtom1961
    Fin15AnchoredAtom1963 Fin15AnchoredAtom1965 Fin15AnchoredAtom1978 Fin15AnchoredAtom1980
    Fin15AnchoredAtom1985 Fin15AnchoredAtom2063 Fin15AnchoredAtom2065 Fin15AnchoredAtom2070
    Fin15AnchoredAtom2101 Fin15AnchoredAtom2346 Fin15AnchoredAtom2348 Fin15AnchoredAtom2350
    Fin15AnchoredAtom2363 Fin15AnchoredAtom2365 Fin15AnchoredAtom2370 Fin15AnchoredAtom2448
    Fin15AnchoredAtom2450 Fin15AnchoredAtom2455 Fin15AnchoredAtom2486 Fin15AnchoredAtom2568
    Fin15AnchoredAtom2570 Fin15AnchoredAtom2575 Fin15AnchoredAtom2606 Fin15AnchoredAtom2781
    Fin15AnchoredAtom3061 Fin15AnchoredAtom3063 Fin15AnchoredAtom3065 Fin15AnchoredAtom3078
    Fin15AnchoredAtom3080 Fin15AnchoredAtom3085 Fin15AnchoredAtom3163 Fin15AnchoredAtom3165
    Fin15AnchoredAtom3170 Fin15AnchoredAtom3201 Fin15AnchoredAtom3283 Fin15AnchoredAtom3285
    Fin15AnchoredAtom3290 Fin15AnchoredAtom3321 Fin15AnchoredAtom3496 Fin15AnchoredAtom4108
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

theorem fin15Anchored_clause30859 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom1935 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
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
      ¬Fin15AnchoredAtom3061 chi ∧
      ¬Fin15AnchoredAtom3064 chi ∧
      ¬Fin15AnchoredAtom3065 chi ∧
      ¬Fin15AnchoredAtom3079 chi ∧
      ¬Fin15AnchoredAtom3080 chi ∧
      ¬Fin15AnchoredAtom3086 chi ∧
      ¬Fin15AnchoredAtom3164 chi ∧
      ¬Fin15AnchoredAtom3165 chi ∧
      ¬Fin15AnchoredAtom3171 chi ∧
      ¬Fin15AnchoredAtom3202 chi ∧
      ¬Fin15AnchoredAtom3284 chi ∧
      ¬Fin15AnchoredAtom3285 chi ∧
      ¬Fin15AnchoredAtom3291 chi ∧
      ¬Fin15AnchoredAtom3322 chi ∧
      ¬Fin15AnchoredAtom3497 chi ∧
      ¬Fin15AnchoredAtom4109 chi ∧
      ¬Fin15AnchoredAtom4110 chi ∧
      ¬Fin15AnchoredAtom4116 chi ∧
      ¬Fin15AnchoredAtom4147 chi ∧
      ¬Fin15AnchoredAtom4322 chi ∧
      ¬Fin15AnchoredAtom4532 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 7, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25755
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1889 Fin15AnchoredAtom1892 Fin15AnchoredAtom1895
    Fin15AnchoredAtom1896 Fin15AnchoredAtom1916 Fin15AnchoredAtom1919 Fin15AnchoredAtom1920
    Fin15AnchoredAtom1934 Fin15AnchoredAtom1935 Fin15AnchoredAtom1941 Fin15AnchoredAtom1961
    Fin15AnchoredAtom1964 Fin15AnchoredAtom1965 Fin15AnchoredAtom1979 Fin15AnchoredAtom1980
    Fin15AnchoredAtom1986 Fin15AnchoredAtom2064 Fin15AnchoredAtom2065 Fin15AnchoredAtom2071
    Fin15AnchoredAtom2102 Fin15AnchoredAtom2346 Fin15AnchoredAtom2349 Fin15AnchoredAtom2350
    Fin15AnchoredAtom2364 Fin15AnchoredAtom2365 Fin15AnchoredAtom2371 Fin15AnchoredAtom2449
    Fin15AnchoredAtom2450 Fin15AnchoredAtom2456 Fin15AnchoredAtom2487 Fin15AnchoredAtom2569
    Fin15AnchoredAtom2570 Fin15AnchoredAtom2576 Fin15AnchoredAtom2607 Fin15AnchoredAtom2782
    Fin15AnchoredAtom3061 Fin15AnchoredAtom3064 Fin15AnchoredAtom3065 Fin15AnchoredAtom3079
    Fin15AnchoredAtom3080 Fin15AnchoredAtom3086 Fin15AnchoredAtom3164 Fin15AnchoredAtom3165
    Fin15AnchoredAtom3171 Fin15AnchoredAtom3202 Fin15AnchoredAtom3284 Fin15AnchoredAtom3285
    Fin15AnchoredAtom3291 Fin15AnchoredAtom3322 Fin15AnchoredAtom3497 Fin15AnchoredAtom4109
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

theorem fin15Anchored_clause30860 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1939 chi ∧
      ¬Fin15AnchoredAtom1940 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
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
      ¬Fin15AnchoredAtom3063 chi ∧
      ¬Fin15AnchoredAtom3064 chi ∧
      ¬Fin15AnchoredAtom3065 chi ∧
      ¬Fin15AnchoredAtom3084 chi ∧
      ¬Fin15AnchoredAtom3085 chi ∧
      ¬Fin15AnchoredAtom3086 chi ∧
      ¬Fin15AnchoredAtom3169 chi ∧
      ¬Fin15AnchoredAtom3170 chi ∧
      ¬Fin15AnchoredAtom3171 chi ∧
      ¬Fin15AnchoredAtom3206 chi ∧
      ¬Fin15AnchoredAtom3289 chi ∧
      ¬Fin15AnchoredAtom3290 chi ∧
      ¬Fin15AnchoredAtom3291 chi ∧
      ¬Fin15AnchoredAtom3326 chi ∧
      ¬Fin15AnchoredAtom3501 chi ∧
      ¬Fin15AnchoredAtom4114 chi ∧
      ¬Fin15AnchoredAtom4115 chi ∧
      ¬Fin15AnchoredAtom4116 chi ∧
      ¬Fin15AnchoredAtom4151 chi ∧
      ¬Fin15AnchoredAtom4326 chi ∧
      ¬Fin15AnchoredAtom4536 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 7, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask28827
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1889 Fin15AnchoredAtom1894 Fin15AnchoredAtom1895
    Fin15AnchoredAtom1896 Fin15AnchoredAtom1918 Fin15AnchoredAtom1919 Fin15AnchoredAtom1920
    Fin15AnchoredAtom1939 Fin15AnchoredAtom1940 Fin15AnchoredAtom1941 Fin15AnchoredAtom1963
    Fin15AnchoredAtom1964 Fin15AnchoredAtom1965 Fin15AnchoredAtom1984 Fin15AnchoredAtom1985
    Fin15AnchoredAtom1986 Fin15AnchoredAtom2069 Fin15AnchoredAtom2070 Fin15AnchoredAtom2071
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2348 Fin15AnchoredAtom2349 Fin15AnchoredAtom2350
    Fin15AnchoredAtom2369 Fin15AnchoredAtom2370 Fin15AnchoredAtom2371 Fin15AnchoredAtom2454
    Fin15AnchoredAtom2455 Fin15AnchoredAtom2456 Fin15AnchoredAtom2491 Fin15AnchoredAtom2574
    Fin15AnchoredAtom2575 Fin15AnchoredAtom2576 Fin15AnchoredAtom2611 Fin15AnchoredAtom2786
    Fin15AnchoredAtom3063 Fin15AnchoredAtom3064 Fin15AnchoredAtom3065 Fin15AnchoredAtom3084
    Fin15AnchoredAtom3085 Fin15AnchoredAtom3086 Fin15AnchoredAtom3169 Fin15AnchoredAtom3170
    Fin15AnchoredAtom3171 Fin15AnchoredAtom3206 Fin15AnchoredAtom3289 Fin15AnchoredAtom3290
    Fin15AnchoredAtom3291 Fin15AnchoredAtom3326 Fin15AnchoredAtom3501 Fin15AnchoredAtom4114
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

theorem fin15Anchored_clause30861 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1890 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1921 chi ∧
      ¬Fin15AnchoredAtom1922 chi ∧
      ¬Fin15AnchoredAtom1924 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom1966 chi ∧
      ¬Fin15AnchoredAtom1967 chi ∧
      ¬Fin15AnchoredAtom1969 chi ∧
      ¬Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom1978 chi ∧
      ¬Fin15AnchoredAtom2072 chi ∧
      ¬Fin15AnchoredAtom2074 chi ∧
      ¬Fin15AnchoredAtom2078 chi ∧
      ¬Fin15AnchoredAtom2088 chi ∧
      ¬Fin15AnchoredAtom2351 chi ∧
      ¬Fin15AnchoredAtom2352 chi ∧
      ¬Fin15AnchoredAtom2354 chi ∧
      ¬Fin15AnchoredAtom2357 chi ∧
      ¬Fin15AnchoredAtom2359 chi ∧
      ¬Fin15AnchoredAtom2363 chi ∧
      ¬Fin15AnchoredAtom2457 chi ∧
      ¬Fin15AnchoredAtom2459 chi ∧
      ¬Fin15AnchoredAtom2463 chi ∧
      ¬Fin15AnchoredAtom2473 chi ∧
      ¬Fin15AnchoredAtom2577 chi ∧
      ¬Fin15AnchoredAtom2579 chi ∧
      ¬Fin15AnchoredAtom2583 chi ∧
      ¬Fin15AnchoredAtom2593 chi ∧
      ¬Fin15AnchoredAtom2788 chi ∧
      ¬Fin15AnchoredAtom3066 chi ∧
      ¬Fin15AnchoredAtom3067 chi ∧
      ¬Fin15AnchoredAtom3069 chi ∧
      ¬Fin15AnchoredAtom3072 chi ∧
      ¬Fin15AnchoredAtom3074 chi ∧
      ¬Fin15AnchoredAtom3078 chi ∧
      ¬Fin15AnchoredAtom3172 chi ∧
      ¬Fin15AnchoredAtom3174 chi ∧
      ¬Fin15AnchoredAtom3178 chi ∧
      ¬Fin15AnchoredAtom3188 chi ∧
      ¬Fin15AnchoredAtom3292 chi ∧
      ¬Fin15AnchoredAtom3294 chi ∧
      ¬Fin15AnchoredAtom3298 chi ∧
      ¬Fin15AnchoredAtom3308 chi ∧
      ¬Fin15AnchoredAtom3503 chi ∧
      ¬Fin15AnchoredAtom4117 chi ∧
      ¬Fin15AnchoredAtom4119 chi ∧
      ¬Fin15AnchoredAtom4123 chi ∧
      ¬Fin15AnchoredAtom4133 chi ∧
      ¬Fin15AnchoredAtom4328 chi ∧
      ¬Fin15AnchoredAtom4538 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 8, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05915
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1890 Fin15AnchoredAtom1891 Fin15AnchoredAtom1892
    Fin15AnchoredAtom1894 Fin15AnchoredAtom1921 Fin15AnchoredAtom1922 Fin15AnchoredAtom1924
    Fin15AnchoredAtom1927 Fin15AnchoredAtom1929 Fin15AnchoredAtom1933 Fin15AnchoredAtom1966
    Fin15AnchoredAtom1967 Fin15AnchoredAtom1969 Fin15AnchoredAtom1972 Fin15AnchoredAtom1974
    Fin15AnchoredAtom1978 Fin15AnchoredAtom2072 Fin15AnchoredAtom2074 Fin15AnchoredAtom2078
    Fin15AnchoredAtom2088 Fin15AnchoredAtom2351 Fin15AnchoredAtom2352 Fin15AnchoredAtom2354
    Fin15AnchoredAtom2357 Fin15AnchoredAtom2359 Fin15AnchoredAtom2363 Fin15AnchoredAtom2457
    Fin15AnchoredAtom2459 Fin15AnchoredAtom2463 Fin15AnchoredAtom2473 Fin15AnchoredAtom2577
    Fin15AnchoredAtom2579 Fin15AnchoredAtom2583 Fin15AnchoredAtom2593 Fin15AnchoredAtom2788
    Fin15AnchoredAtom3066 Fin15AnchoredAtom3067 Fin15AnchoredAtom3069 Fin15AnchoredAtom3072
    Fin15AnchoredAtom3074 Fin15AnchoredAtom3078 Fin15AnchoredAtom3172 Fin15AnchoredAtom3174
    Fin15AnchoredAtom3178 Fin15AnchoredAtom3188 Fin15AnchoredAtom3292 Fin15AnchoredAtom3294
    Fin15AnchoredAtom3298 Fin15AnchoredAtom3308 Fin15AnchoredAtom3503 Fin15AnchoredAtom4117
    Fin15AnchoredAtom4119 Fin15AnchoredAtom4123 Fin15AnchoredAtom4133 Fin15AnchoredAtom4328
    Fin15AnchoredAtom4538 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30862 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1890 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1921 chi ∧
      ¬Fin15AnchoredAtom1922 chi ∧
      ¬Fin15AnchoredAtom1925 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom1966 chi ∧
      ¬Fin15AnchoredAtom1967 chi ∧
      ¬Fin15AnchoredAtom1970 chi ∧
      ¬Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom1979 chi ∧
      ¬Fin15AnchoredAtom2072 chi ∧
      ¬Fin15AnchoredAtom2075 chi ∧
      ¬Fin15AnchoredAtom2079 chi ∧
      ¬Fin15AnchoredAtom2089 chi ∧
      ¬Fin15AnchoredAtom2351 chi ∧
      ¬Fin15AnchoredAtom2352 chi ∧
      ¬Fin15AnchoredAtom2355 chi ∧
      ¬Fin15AnchoredAtom2357 chi ∧
      ¬Fin15AnchoredAtom2360 chi ∧
      ¬Fin15AnchoredAtom2364 chi ∧
      ¬Fin15AnchoredAtom2457 chi ∧
      ¬Fin15AnchoredAtom2460 chi ∧
      ¬Fin15AnchoredAtom2464 chi ∧
      ¬Fin15AnchoredAtom2474 chi ∧
      ¬Fin15AnchoredAtom2577 chi ∧
      ¬Fin15AnchoredAtom2580 chi ∧
      ¬Fin15AnchoredAtom2584 chi ∧
      ¬Fin15AnchoredAtom2594 chi ∧
      ¬Fin15AnchoredAtom2789 chi ∧
      ¬Fin15AnchoredAtom3066 chi ∧
      ¬Fin15AnchoredAtom3067 chi ∧
      ¬Fin15AnchoredAtom3070 chi ∧
      ¬Fin15AnchoredAtom3072 chi ∧
      ¬Fin15AnchoredAtom3075 chi ∧
      ¬Fin15AnchoredAtom3079 chi ∧
      ¬Fin15AnchoredAtom3172 chi ∧
      ¬Fin15AnchoredAtom3175 chi ∧
      ¬Fin15AnchoredAtom3179 chi ∧
      ¬Fin15AnchoredAtom3189 chi ∧
      ¬Fin15AnchoredAtom3292 chi ∧
      ¬Fin15AnchoredAtom3295 chi ∧
      ¬Fin15AnchoredAtom3299 chi ∧
      ¬Fin15AnchoredAtom3309 chi ∧
      ¬Fin15AnchoredAtom3504 chi ∧
      ¬Fin15AnchoredAtom4117 chi ∧
      ¬Fin15AnchoredAtom4120 chi ∧
      ¬Fin15AnchoredAtom4124 chi ∧
      ¬Fin15AnchoredAtom4134 chi ∧
      ¬Fin15AnchoredAtom4329 chi ∧
      ¬Fin15AnchoredAtom4539 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 8, 9, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask10011
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1890 Fin15AnchoredAtom1891 Fin15AnchoredAtom1892
    Fin15AnchoredAtom1895 Fin15AnchoredAtom1921 Fin15AnchoredAtom1922 Fin15AnchoredAtom1925
    Fin15AnchoredAtom1927 Fin15AnchoredAtom1930 Fin15AnchoredAtom1934 Fin15AnchoredAtom1966
    Fin15AnchoredAtom1967 Fin15AnchoredAtom1970 Fin15AnchoredAtom1972 Fin15AnchoredAtom1975
    Fin15AnchoredAtom1979 Fin15AnchoredAtom2072 Fin15AnchoredAtom2075 Fin15AnchoredAtom2079
    Fin15AnchoredAtom2089 Fin15AnchoredAtom2351 Fin15AnchoredAtom2352 Fin15AnchoredAtom2355
    Fin15AnchoredAtom2357 Fin15AnchoredAtom2360 Fin15AnchoredAtom2364 Fin15AnchoredAtom2457
    Fin15AnchoredAtom2460 Fin15AnchoredAtom2464 Fin15AnchoredAtom2474 Fin15AnchoredAtom2577
    Fin15AnchoredAtom2580 Fin15AnchoredAtom2584 Fin15AnchoredAtom2594 Fin15AnchoredAtom2789
    Fin15AnchoredAtom3066 Fin15AnchoredAtom3067 Fin15AnchoredAtom3070 Fin15AnchoredAtom3072
    Fin15AnchoredAtom3075 Fin15AnchoredAtom3079 Fin15AnchoredAtom3172 Fin15AnchoredAtom3175
    Fin15AnchoredAtom3179 Fin15AnchoredAtom3189 Fin15AnchoredAtom3292 Fin15AnchoredAtom3295
    Fin15AnchoredAtom3299 Fin15AnchoredAtom3309 Fin15AnchoredAtom3504 Fin15AnchoredAtom4117
    Fin15AnchoredAtom4120 Fin15AnchoredAtom4124 Fin15AnchoredAtom4134 Fin15AnchoredAtom4329
    Fin15AnchoredAtom4539 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30863 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1890 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1921 chi ∧
      ¬Fin15AnchoredAtom1925 chi ∧
      ¬Fin15AnchoredAtom1926 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
      ¬Fin15AnchoredAtom1966 chi ∧
      ¬Fin15AnchoredAtom1970 chi ∧
      ¬Fin15AnchoredAtom1971 chi ∧
      ¬Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom1976 chi ∧
      ¬Fin15AnchoredAtom1986 chi ∧
      ¬Fin15AnchoredAtom2075 chi ∧
      ¬Fin15AnchoredAtom2076 chi ∧
      ¬Fin15AnchoredAtom2086 chi ∧
      ¬Fin15AnchoredAtom2096 chi ∧
      ¬Fin15AnchoredAtom2351 chi ∧
      ¬Fin15AnchoredAtom2355 chi ∧
      ¬Fin15AnchoredAtom2356 chi ∧
      ¬Fin15AnchoredAtom2360 chi ∧
      ¬Fin15AnchoredAtom2361 chi ∧
      ¬Fin15AnchoredAtom2371 chi ∧
      ¬Fin15AnchoredAtom2460 chi ∧
      ¬Fin15AnchoredAtom2461 chi ∧
      ¬Fin15AnchoredAtom2471 chi ∧
      ¬Fin15AnchoredAtom2481 chi ∧
      ¬Fin15AnchoredAtom2580 chi ∧
      ¬Fin15AnchoredAtom2581 chi ∧
      ¬Fin15AnchoredAtom2591 chi ∧
      ¬Fin15AnchoredAtom2601 chi ∧
      ¬Fin15AnchoredAtom2796 chi ∧
      ¬Fin15AnchoredAtom3066 chi ∧
      ¬Fin15AnchoredAtom3070 chi ∧
      ¬Fin15AnchoredAtom3071 chi ∧
      ¬Fin15AnchoredAtom3075 chi ∧
      ¬Fin15AnchoredAtom3076 chi ∧
      ¬Fin15AnchoredAtom3086 chi ∧
      ¬Fin15AnchoredAtom3175 chi ∧
      ¬Fin15AnchoredAtom3176 chi ∧
      ¬Fin15AnchoredAtom3186 chi ∧
      ¬Fin15AnchoredAtom3196 chi ∧
      ¬Fin15AnchoredAtom3295 chi ∧
      ¬Fin15AnchoredAtom3296 chi ∧
      ¬Fin15AnchoredAtom3306 chi ∧
      ¬Fin15AnchoredAtom3316 chi ∧
      ¬Fin15AnchoredAtom3511 chi ∧
      ¬Fin15AnchoredAtom4120 chi ∧
      ¬Fin15AnchoredAtom4121 chi ∧
      ¬Fin15AnchoredAtom4131 chi ∧
      ¬Fin15AnchoredAtom4141 chi ∧
      ¬Fin15AnchoredAtom4336 chi ∧
      ¬Fin15AnchoredAtom4546 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 8, 9, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25371
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1890 Fin15AnchoredAtom1891 Fin15AnchoredAtom1895
    Fin15AnchoredAtom1896 Fin15AnchoredAtom1921 Fin15AnchoredAtom1925 Fin15AnchoredAtom1926
    Fin15AnchoredAtom1930 Fin15AnchoredAtom1931 Fin15AnchoredAtom1941 Fin15AnchoredAtom1966
    Fin15AnchoredAtom1970 Fin15AnchoredAtom1971 Fin15AnchoredAtom1975 Fin15AnchoredAtom1976
    Fin15AnchoredAtom1986 Fin15AnchoredAtom2075 Fin15AnchoredAtom2076 Fin15AnchoredAtom2086
    Fin15AnchoredAtom2096 Fin15AnchoredAtom2351 Fin15AnchoredAtom2355 Fin15AnchoredAtom2356
    Fin15AnchoredAtom2360 Fin15AnchoredAtom2361 Fin15AnchoredAtom2371 Fin15AnchoredAtom2460
    Fin15AnchoredAtom2461 Fin15AnchoredAtom2471 Fin15AnchoredAtom2481 Fin15AnchoredAtom2580
    Fin15AnchoredAtom2581 Fin15AnchoredAtom2591 Fin15AnchoredAtom2601 Fin15AnchoredAtom2796
    Fin15AnchoredAtom3066 Fin15AnchoredAtom3070 Fin15AnchoredAtom3071 Fin15AnchoredAtom3075
    Fin15AnchoredAtom3076 Fin15AnchoredAtom3086 Fin15AnchoredAtom3175 Fin15AnchoredAtom3176
    Fin15AnchoredAtom3186 Fin15AnchoredAtom3196 Fin15AnchoredAtom3295 Fin15AnchoredAtom3296
    Fin15AnchoredAtom3306 Fin15AnchoredAtom3316 Fin15AnchoredAtom3511 Fin15AnchoredAtom4120
    Fin15AnchoredAtom4121 Fin15AnchoredAtom4131 Fin15AnchoredAtom4141 Fin15AnchoredAtom4336
    Fin15AnchoredAtom4546 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30864 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1893 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1928 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1932 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom1937 chi ∧
      ¬Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom1973 chi ∧
      ¬Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom1977 chi ∧
      ¬Fin15AnchoredAtom1979 chi ∧
      ¬Fin15AnchoredAtom1982 chi ∧
      ¬Fin15AnchoredAtom2087 chi ∧
      ¬Fin15AnchoredAtom2089 chi ∧
      ¬Fin15AnchoredAtom2092 chi ∧
      ¬Fin15AnchoredAtom2098 chi ∧
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
      ¬Fin15AnchoredAtom3072 chi ∧
      ¬Fin15AnchoredAtom3073 chi ∧
      ¬Fin15AnchoredAtom3075 chi ∧
      ¬Fin15AnchoredAtom3077 chi ∧
      ¬Fin15AnchoredAtom3079 chi ∧
      ¬Fin15AnchoredAtom3082 chi ∧
      ¬Fin15AnchoredAtom3187 chi ∧
      ¬Fin15AnchoredAtom3189 chi ∧
      ¬Fin15AnchoredAtom3192 chi ∧
      ¬Fin15AnchoredAtom3198 chi ∧
      ¬Fin15AnchoredAtom3307 chi ∧
      ¬Fin15AnchoredAtom3309 chi ∧
      ¬Fin15AnchoredAtom3312 chi ∧
      ¬Fin15AnchoredAtom3318 chi ∧
      ¬Fin15AnchoredAtom3523 chi ∧
      ¬Fin15AnchoredAtom4132 chi ∧
      ¬Fin15AnchoredAtom4134 chi ∧
      ¬Fin15AnchoredAtom4137 chi ∧
      ¬Fin15AnchoredAtom4143 chi ∧
      ¬Fin15AnchoredAtom4348 chi ∧
      ¬Fin15AnchoredAtom4558 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 9, 10, 11, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask11803
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1891 Fin15AnchoredAtom1892 Fin15AnchoredAtom1893
    Fin15AnchoredAtom1895 Fin15AnchoredAtom1927 Fin15AnchoredAtom1928 Fin15AnchoredAtom1930
    Fin15AnchoredAtom1932 Fin15AnchoredAtom1934 Fin15AnchoredAtom1937 Fin15AnchoredAtom1972
    Fin15AnchoredAtom1973 Fin15AnchoredAtom1975 Fin15AnchoredAtom1977 Fin15AnchoredAtom1979
    Fin15AnchoredAtom1982 Fin15AnchoredAtom2087 Fin15AnchoredAtom2089 Fin15AnchoredAtom2092
    Fin15AnchoredAtom2098 Fin15AnchoredAtom2357 Fin15AnchoredAtom2358 Fin15AnchoredAtom2360
    Fin15AnchoredAtom2362 Fin15AnchoredAtom2364 Fin15AnchoredAtom2367 Fin15AnchoredAtom2472
    Fin15AnchoredAtom2474 Fin15AnchoredAtom2477 Fin15AnchoredAtom2483 Fin15AnchoredAtom2592
    Fin15AnchoredAtom2594 Fin15AnchoredAtom2597 Fin15AnchoredAtom2603 Fin15AnchoredAtom2808
    Fin15AnchoredAtom3072 Fin15AnchoredAtom3073 Fin15AnchoredAtom3075 Fin15AnchoredAtom3077
    Fin15AnchoredAtom3079 Fin15AnchoredAtom3082 Fin15AnchoredAtom3187 Fin15AnchoredAtom3189
    Fin15AnchoredAtom3192 Fin15AnchoredAtom3198 Fin15AnchoredAtom3307 Fin15AnchoredAtom3309
    Fin15AnchoredAtom3312 Fin15AnchoredAtom3318 Fin15AnchoredAtom3523 Fin15AnchoredAtom4132
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

theorem fin15Anchored_clause30865 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom1939 chi ∧
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
      ¬Fin15AnchoredAtom3072 chi ∧
      ¬Fin15AnchoredAtom3074 chi ∧
      ¬Fin15AnchoredAtom3075 chi ∧
      ¬Fin15AnchoredAtom3078 chi ∧
      ¬Fin15AnchoredAtom3079 chi ∧
      ¬Fin15AnchoredAtom3084 chi ∧
      ¬Fin15AnchoredAtom3188 chi ∧
      ¬Fin15AnchoredAtom3189 chi ∧
      ¬Fin15AnchoredAtom3194 chi ∧
      ¬Fin15AnchoredAtom3200 chi ∧
      ¬Fin15AnchoredAtom3308 chi ∧
      ¬Fin15AnchoredAtom3309 chi ∧
      ¬Fin15AnchoredAtom3314 chi ∧
      ¬Fin15AnchoredAtom3320 chi ∧
      ¬Fin15AnchoredAtom3525 chi ∧
      ¬Fin15AnchoredAtom4133 chi ∧
      ¬Fin15AnchoredAtom4134 chi ∧
      ¬Fin15AnchoredAtom4139 chi ∧
      ¬Fin15AnchoredAtom4145 chi ∧
      ¬Fin15AnchoredAtom4350 chi ∧
      ¬Fin15AnchoredAtom4560 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13851
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1891 Fin15AnchoredAtom1892 Fin15AnchoredAtom1894
    Fin15AnchoredAtom1895 Fin15AnchoredAtom1927 Fin15AnchoredAtom1929 Fin15AnchoredAtom1930
    Fin15AnchoredAtom1933 Fin15AnchoredAtom1934 Fin15AnchoredAtom1939 Fin15AnchoredAtom1972
    Fin15AnchoredAtom1974 Fin15AnchoredAtom1975 Fin15AnchoredAtom1978 Fin15AnchoredAtom1979
    Fin15AnchoredAtom1984 Fin15AnchoredAtom2088 Fin15AnchoredAtom2089 Fin15AnchoredAtom2094
    Fin15AnchoredAtom2100 Fin15AnchoredAtom2357 Fin15AnchoredAtom2359 Fin15AnchoredAtom2360
    Fin15AnchoredAtom2363 Fin15AnchoredAtom2364 Fin15AnchoredAtom2369 Fin15AnchoredAtom2473
    Fin15AnchoredAtom2474 Fin15AnchoredAtom2479 Fin15AnchoredAtom2485 Fin15AnchoredAtom2593
    Fin15AnchoredAtom2594 Fin15AnchoredAtom2599 Fin15AnchoredAtom2605 Fin15AnchoredAtom2810
    Fin15AnchoredAtom3072 Fin15AnchoredAtom3074 Fin15AnchoredAtom3075 Fin15AnchoredAtom3078
    Fin15AnchoredAtom3079 Fin15AnchoredAtom3084 Fin15AnchoredAtom3188 Fin15AnchoredAtom3189
    Fin15AnchoredAtom3194 Fin15AnchoredAtom3200 Fin15AnchoredAtom3308 Fin15AnchoredAtom3309
    Fin15AnchoredAtom3314 Fin15AnchoredAtom3320 Fin15AnchoredAtom3525 Fin15AnchoredAtom4133
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

theorem fin15Anchored_clause30866 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom1935 chi ∧
      ¬Fin15AnchoredAtom1940 chi ∧
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
      ¬Fin15AnchoredAtom3072 chi ∧
      ¬Fin15AnchoredAtom3074 chi ∧
      ¬Fin15AnchoredAtom3076 chi ∧
      ¬Fin15AnchoredAtom3078 chi ∧
      ¬Fin15AnchoredAtom3080 chi ∧
      ¬Fin15AnchoredAtom3085 chi ∧
      ¬Fin15AnchoredAtom3188 chi ∧
      ¬Fin15AnchoredAtom3190 chi ∧
      ¬Fin15AnchoredAtom3195 chi ∧
      ¬Fin15AnchoredAtom3201 chi ∧
      ¬Fin15AnchoredAtom3308 chi ∧
      ¬Fin15AnchoredAtom3310 chi ∧
      ¬Fin15AnchoredAtom3315 chi ∧
      ¬Fin15AnchoredAtom3321 chi ∧
      ¬Fin15AnchoredAtom3526 chi ∧
      ¬Fin15AnchoredAtom4133 chi ∧
      ¬Fin15AnchoredAtom4135 chi ∧
      ¬Fin15AnchoredAtom4140 chi ∧
      ¬Fin15AnchoredAtom4146 chi ∧
      ¬Fin15AnchoredAtom4351 chi ∧
      ¬Fin15AnchoredAtom4561 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 9, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22043
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1891 Fin15AnchoredAtom1892 Fin15AnchoredAtom1894
    Fin15AnchoredAtom1896 Fin15AnchoredAtom1927 Fin15AnchoredAtom1929 Fin15AnchoredAtom1931
    Fin15AnchoredAtom1933 Fin15AnchoredAtom1935 Fin15AnchoredAtom1940 Fin15AnchoredAtom1972
    Fin15AnchoredAtom1974 Fin15AnchoredAtom1976 Fin15AnchoredAtom1978 Fin15AnchoredAtom1980
    Fin15AnchoredAtom1985 Fin15AnchoredAtom2088 Fin15AnchoredAtom2090 Fin15AnchoredAtom2095
    Fin15AnchoredAtom2101 Fin15AnchoredAtom2357 Fin15AnchoredAtom2359 Fin15AnchoredAtom2361
    Fin15AnchoredAtom2363 Fin15AnchoredAtom2365 Fin15AnchoredAtom2370 Fin15AnchoredAtom2473
    Fin15AnchoredAtom2475 Fin15AnchoredAtom2480 Fin15AnchoredAtom2486 Fin15AnchoredAtom2593
    Fin15AnchoredAtom2595 Fin15AnchoredAtom2600 Fin15AnchoredAtom2606 Fin15AnchoredAtom2811
    Fin15AnchoredAtom3072 Fin15AnchoredAtom3074 Fin15AnchoredAtom3076 Fin15AnchoredAtom3078
    Fin15AnchoredAtom3080 Fin15AnchoredAtom3085 Fin15AnchoredAtom3188 Fin15AnchoredAtom3190
    Fin15AnchoredAtom3195 Fin15AnchoredAtom3201 Fin15AnchoredAtom3308 Fin15AnchoredAtom3310
    Fin15AnchoredAtom3315 Fin15AnchoredAtom3321 Fin15AnchoredAtom3526 Fin15AnchoredAtom4133
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

theorem fin15Anchored_clause30867 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom1935 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
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
      ¬Fin15AnchoredAtom3072 chi ∧
      ¬Fin15AnchoredAtom3075 chi ∧
      ¬Fin15AnchoredAtom3076 chi ∧
      ¬Fin15AnchoredAtom3079 chi ∧
      ¬Fin15AnchoredAtom3080 chi ∧
      ¬Fin15AnchoredAtom3086 chi ∧
      ¬Fin15AnchoredAtom3189 chi ∧
      ¬Fin15AnchoredAtom3190 chi ∧
      ¬Fin15AnchoredAtom3196 chi ∧
      ¬Fin15AnchoredAtom3202 chi ∧
      ¬Fin15AnchoredAtom3309 chi ∧
      ¬Fin15AnchoredAtom3310 chi ∧
      ¬Fin15AnchoredAtom3316 chi ∧
      ¬Fin15AnchoredAtom3322 chi ∧
      ¬Fin15AnchoredAtom3527 chi ∧
      ¬Fin15AnchoredAtom4134 chi ∧
      ¬Fin15AnchoredAtom4135 chi ∧
      ¬Fin15AnchoredAtom4141 chi ∧
      ¬Fin15AnchoredAtom4147 chi ∧
      ¬Fin15AnchoredAtom4352 chi ∧
      ¬Fin15AnchoredAtom4562 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 9, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26139
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1891 Fin15AnchoredAtom1892 Fin15AnchoredAtom1895
    Fin15AnchoredAtom1896 Fin15AnchoredAtom1927 Fin15AnchoredAtom1930 Fin15AnchoredAtom1931
    Fin15AnchoredAtom1934 Fin15AnchoredAtom1935 Fin15AnchoredAtom1941 Fin15AnchoredAtom1972
    Fin15AnchoredAtom1975 Fin15AnchoredAtom1976 Fin15AnchoredAtom1979 Fin15AnchoredAtom1980
    Fin15AnchoredAtom1986 Fin15AnchoredAtom2089 Fin15AnchoredAtom2090 Fin15AnchoredAtom2096
    Fin15AnchoredAtom2102 Fin15AnchoredAtom2357 Fin15AnchoredAtom2360 Fin15AnchoredAtom2361
    Fin15AnchoredAtom2364 Fin15AnchoredAtom2365 Fin15AnchoredAtom2371 Fin15AnchoredAtom2474
    Fin15AnchoredAtom2475 Fin15AnchoredAtom2481 Fin15AnchoredAtom2487 Fin15AnchoredAtom2594
    Fin15AnchoredAtom2595 Fin15AnchoredAtom2601 Fin15AnchoredAtom2607 Fin15AnchoredAtom2812
    Fin15AnchoredAtom3072 Fin15AnchoredAtom3075 Fin15AnchoredAtom3076 Fin15AnchoredAtom3079
    Fin15AnchoredAtom3080 Fin15AnchoredAtom3086 Fin15AnchoredAtom3189 Fin15AnchoredAtom3190
    Fin15AnchoredAtom3196 Fin15AnchoredAtom3202 Fin15AnchoredAtom3309 Fin15AnchoredAtom3310
    Fin15AnchoredAtom3316 Fin15AnchoredAtom3322 Fin15AnchoredAtom3527 Fin15AnchoredAtom4134
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

theorem fin15Anchored_clause30868 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom1939 chi ∧
      ¬Fin15AnchoredAtom1940 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
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
      ¬Fin15AnchoredAtom3074 chi ∧
      ¬Fin15AnchoredAtom3075 chi ∧
      ¬Fin15AnchoredAtom3076 chi ∧
      ¬Fin15AnchoredAtom3084 chi ∧
      ¬Fin15AnchoredAtom3085 chi ∧
      ¬Fin15AnchoredAtom3086 chi ∧
      ¬Fin15AnchoredAtom3194 chi ∧
      ¬Fin15AnchoredAtom3195 chi ∧
      ¬Fin15AnchoredAtom3196 chi ∧
      ¬Fin15AnchoredAtom3206 chi ∧
      ¬Fin15AnchoredAtom3314 chi ∧
      ¬Fin15AnchoredAtom3315 chi ∧
      ¬Fin15AnchoredAtom3316 chi ∧
      ¬Fin15AnchoredAtom3326 chi ∧
      ¬Fin15AnchoredAtom3531 chi ∧
      ¬Fin15AnchoredAtom4139 chi ∧
      ¬Fin15AnchoredAtom4140 chi ∧
      ¬Fin15AnchoredAtom4141 chi ∧
      ¬Fin15AnchoredAtom4151 chi ∧
      ¬Fin15AnchoredAtom4356 chi ∧
      ¬Fin15AnchoredAtom4566 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 9, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29211
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1891 Fin15AnchoredAtom1894 Fin15AnchoredAtom1895
    Fin15AnchoredAtom1896 Fin15AnchoredAtom1929 Fin15AnchoredAtom1930 Fin15AnchoredAtom1931
    Fin15AnchoredAtom1939 Fin15AnchoredAtom1940 Fin15AnchoredAtom1941 Fin15AnchoredAtom1974
    Fin15AnchoredAtom1975 Fin15AnchoredAtom1976 Fin15AnchoredAtom1984 Fin15AnchoredAtom1985
    Fin15AnchoredAtom1986 Fin15AnchoredAtom2094 Fin15AnchoredAtom2095 Fin15AnchoredAtom2096
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2359 Fin15AnchoredAtom2360 Fin15AnchoredAtom2361
    Fin15AnchoredAtom2369 Fin15AnchoredAtom2370 Fin15AnchoredAtom2371 Fin15AnchoredAtom2479
    Fin15AnchoredAtom2480 Fin15AnchoredAtom2481 Fin15AnchoredAtom2491 Fin15AnchoredAtom2599
    Fin15AnchoredAtom2600 Fin15AnchoredAtom2601 Fin15AnchoredAtom2611 Fin15AnchoredAtom2816
    Fin15AnchoredAtom3074 Fin15AnchoredAtom3075 Fin15AnchoredAtom3076 Fin15AnchoredAtom3084
    Fin15AnchoredAtom3085 Fin15AnchoredAtom3086 Fin15AnchoredAtom3194 Fin15AnchoredAtom3195
    Fin15AnchoredAtom3196 Fin15AnchoredAtom3206 Fin15AnchoredAtom3314 Fin15AnchoredAtom3315
    Fin15AnchoredAtom3316 Fin15AnchoredAtom3326 Fin15AnchoredAtom3531 Fin15AnchoredAtom4139
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

theorem fin15Anchored_clause30869 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom1935 chi ∧
      ¬Fin15AnchoredAtom1939 chi ∧
      ¬Fin15AnchoredAtom1940 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
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
      ¬Fin15AnchoredAtom3078 chi ∧
      ¬Fin15AnchoredAtom3079 chi ∧
      ¬Fin15AnchoredAtom3080 chi ∧
      ¬Fin15AnchoredAtom3084 chi ∧
      ¬Fin15AnchoredAtom3085 chi ∧
      ¬Fin15AnchoredAtom3086 chi ∧
      ¬Fin15AnchoredAtom3200 chi ∧
      ¬Fin15AnchoredAtom3201 chi ∧
      ¬Fin15AnchoredAtom3202 chi ∧
      ¬Fin15AnchoredAtom3206 chi ∧
      ¬Fin15AnchoredAtom3320 chi ∧
      ¬Fin15AnchoredAtom3321 chi ∧
      ¬Fin15AnchoredAtom3322 chi ∧
      ¬Fin15AnchoredAtom3326 chi ∧
      ¬Fin15AnchoredAtom3535 chi ∧
      ¬Fin15AnchoredAtom4145 chi ∧
      ¬Fin15AnchoredAtom4146 chi ∧
      ¬Fin15AnchoredAtom4147 chi ∧
      ¬Fin15AnchoredAtom4151 chi ∧
      ¬Fin15AnchoredAtom4360 chi ∧
      ¬Fin15AnchoredAtom4570 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 4, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29723
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1892 Fin15AnchoredAtom1894 Fin15AnchoredAtom1895
    Fin15AnchoredAtom1896 Fin15AnchoredAtom1933 Fin15AnchoredAtom1934 Fin15AnchoredAtom1935
    Fin15AnchoredAtom1939 Fin15AnchoredAtom1940 Fin15AnchoredAtom1941 Fin15AnchoredAtom1978
    Fin15AnchoredAtom1979 Fin15AnchoredAtom1980 Fin15AnchoredAtom1984 Fin15AnchoredAtom1985
    Fin15AnchoredAtom1986 Fin15AnchoredAtom2100 Fin15AnchoredAtom2101 Fin15AnchoredAtom2102
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2363 Fin15AnchoredAtom2364 Fin15AnchoredAtom2365
    Fin15AnchoredAtom2369 Fin15AnchoredAtom2370 Fin15AnchoredAtom2371 Fin15AnchoredAtom2485
    Fin15AnchoredAtom2486 Fin15AnchoredAtom2487 Fin15AnchoredAtom2491 Fin15AnchoredAtom2605
    Fin15AnchoredAtom2606 Fin15AnchoredAtom2607 Fin15AnchoredAtom2611 Fin15AnchoredAtom2820
    Fin15AnchoredAtom3078 Fin15AnchoredAtom3079 Fin15AnchoredAtom3080 Fin15AnchoredAtom3084
    Fin15AnchoredAtom3085 Fin15AnchoredAtom3086 Fin15AnchoredAtom3200 Fin15AnchoredAtom3201
    Fin15AnchoredAtom3202 Fin15AnchoredAtom3206 Fin15AnchoredAtom3320 Fin15AnchoredAtom3321
    Fin15AnchoredAtom3322 Fin15AnchoredAtom3326 Fin15AnchoredAtom3535 Fin15AnchoredAtom4145
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

theorem fin15Anchored_clause30870 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1899 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1907 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1914 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1921 chi ∧
      ¬Fin15AnchoredAtom1987 chi ∧
      ¬Fin15AnchoredAtom1988 chi ∧
      ¬Fin15AnchoredAtom1989 chi ∧
      ¬Fin15AnchoredAtom1995 chi ∧
      ¬Fin15AnchoredAtom1996 chi ∧
      ¬Fin15AnchoredAtom2002 chi ∧
      ¬Fin15AnchoredAtom2023 chi ∧
      ¬Fin15AnchoredAtom2024 chi ∧
      ¬Fin15AnchoredAtom2030 chi ∧
      ¬Fin15AnchoredAtom2051 chi ∧
      ¬Fin15AnchoredAtom2372 chi ∧
      ¬Fin15AnchoredAtom2373 chi ∧
      ¬Fin15AnchoredAtom2374 chi ∧
      ¬Fin15AnchoredAtom2380 chi ∧
      ¬Fin15AnchoredAtom2381 chi ∧
      ¬Fin15AnchoredAtom2387 chi ∧
      ¬Fin15AnchoredAtom2408 chi ∧
      ¬Fin15AnchoredAtom2409 chi ∧
      ¬Fin15AnchoredAtom2415 chi ∧
      ¬Fin15AnchoredAtom2436 chi ∧
      ¬Fin15AnchoredAtom2612 chi ∧
      ¬Fin15AnchoredAtom2613 chi ∧
      ¬Fin15AnchoredAtom2619 chi ∧
      ¬Fin15AnchoredAtom2640 chi ∧
      ¬Fin15AnchoredAtom2696 chi ∧
      ¬Fin15AnchoredAtom3087 chi ∧
      ¬Fin15AnchoredAtom3088 chi ∧
      ¬Fin15AnchoredAtom3089 chi ∧
      ¬Fin15AnchoredAtom3095 chi ∧
      ¬Fin15AnchoredAtom3096 chi ∧
      ¬Fin15AnchoredAtom3102 chi ∧
      ¬Fin15AnchoredAtom3123 chi ∧
      ¬Fin15AnchoredAtom3124 chi ∧
      ¬Fin15AnchoredAtom3130 chi ∧
      ¬Fin15AnchoredAtom3151 chi ∧
      ¬Fin15AnchoredAtom3327 chi ∧
      ¬Fin15AnchoredAtom3328 chi ∧
      ¬Fin15AnchoredAtom3334 chi ∧
      ¬Fin15AnchoredAtom3355 chi ∧
      ¬Fin15AnchoredAtom3411 chi ∧
      ¬Fin15AnchoredAtom4152 chi ∧
      ¬Fin15AnchoredAtom4153 chi ∧
      ¬Fin15AnchoredAtom4159 chi ∧
      ¬Fin15AnchoredAtom4180 chi ∧
      ¬Fin15AnchoredAtom4236 chi ∧
      ¬Fin15AnchoredAtom4572 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 5, 6, 7, 8, 9}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask01003
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1897 Fin15AnchoredAtom1898 Fin15AnchoredAtom1899
    Fin15AnchoredAtom1900 Fin15AnchoredAtom1906 Fin15AnchoredAtom1907 Fin15AnchoredAtom1908
    Fin15AnchoredAtom1914 Fin15AnchoredAtom1915 Fin15AnchoredAtom1921 Fin15AnchoredAtom1987
    Fin15AnchoredAtom1988 Fin15AnchoredAtom1989 Fin15AnchoredAtom1995 Fin15AnchoredAtom1996
    Fin15AnchoredAtom2002 Fin15AnchoredAtom2023 Fin15AnchoredAtom2024 Fin15AnchoredAtom2030
    Fin15AnchoredAtom2051 Fin15AnchoredAtom2372 Fin15AnchoredAtom2373 Fin15AnchoredAtom2374
    Fin15AnchoredAtom2380 Fin15AnchoredAtom2381 Fin15AnchoredAtom2387 Fin15AnchoredAtom2408
    Fin15AnchoredAtom2409 Fin15AnchoredAtom2415 Fin15AnchoredAtom2436 Fin15AnchoredAtom2612
    Fin15AnchoredAtom2613 Fin15AnchoredAtom2619 Fin15AnchoredAtom2640 Fin15AnchoredAtom2696
    Fin15AnchoredAtom3087 Fin15AnchoredAtom3088 Fin15AnchoredAtom3089 Fin15AnchoredAtom3095
    Fin15AnchoredAtom3096 Fin15AnchoredAtom3102 Fin15AnchoredAtom3123 Fin15AnchoredAtom3124
    Fin15AnchoredAtom3130 Fin15AnchoredAtom3151 Fin15AnchoredAtom3327 Fin15AnchoredAtom3328
    Fin15AnchoredAtom3334 Fin15AnchoredAtom3355 Fin15AnchoredAtom3411 Fin15AnchoredAtom4152
    Fin15AnchoredAtom4153 Fin15AnchoredAtom4159 Fin15AnchoredAtom4180 Fin15AnchoredAtom4236
    Fin15AnchoredAtom4572 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30871 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1899 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1907 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1914 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1922 chi ∧
      ¬Fin15AnchoredAtom1987 chi ∧
      ¬Fin15AnchoredAtom1988 chi ∧
      ¬Fin15AnchoredAtom1990 chi ∧
      ¬Fin15AnchoredAtom1995 chi ∧
      ¬Fin15AnchoredAtom1997 chi ∧
      ¬Fin15AnchoredAtom2003 chi ∧
      ¬Fin15AnchoredAtom2023 chi ∧
      ¬Fin15AnchoredAtom2025 chi ∧
      ¬Fin15AnchoredAtom2031 chi ∧
      ¬Fin15AnchoredAtom2052 chi ∧
      ¬Fin15AnchoredAtom2372 chi ∧
      ¬Fin15AnchoredAtom2373 chi ∧
      ¬Fin15AnchoredAtom2375 chi ∧
      ¬Fin15AnchoredAtom2380 chi ∧
      ¬Fin15AnchoredAtom2382 chi ∧
      ¬Fin15AnchoredAtom2388 chi ∧
      ¬Fin15AnchoredAtom2408 chi ∧
      ¬Fin15AnchoredAtom2410 chi ∧
      ¬Fin15AnchoredAtom2416 chi ∧
      ¬Fin15AnchoredAtom2437 chi ∧
      ¬Fin15AnchoredAtom2612 chi ∧
      ¬Fin15AnchoredAtom2614 chi ∧
      ¬Fin15AnchoredAtom2620 chi ∧
      ¬Fin15AnchoredAtom2641 chi ∧
      ¬Fin15AnchoredAtom2697 chi ∧
      ¬Fin15AnchoredAtom3087 chi ∧
      ¬Fin15AnchoredAtom3088 chi ∧
      ¬Fin15AnchoredAtom3090 chi ∧
      ¬Fin15AnchoredAtom3095 chi ∧
      ¬Fin15AnchoredAtom3097 chi ∧
      ¬Fin15AnchoredAtom3103 chi ∧
      ¬Fin15AnchoredAtom3123 chi ∧
      ¬Fin15AnchoredAtom3125 chi ∧
      ¬Fin15AnchoredAtom3131 chi ∧
      ¬Fin15AnchoredAtom3152 chi ∧
      ¬Fin15AnchoredAtom3327 chi ∧
      ¬Fin15AnchoredAtom3329 chi ∧
      ¬Fin15AnchoredAtom3335 chi ∧
      ¬Fin15AnchoredAtom3356 chi ∧
      ¬Fin15AnchoredAtom3412 chi ∧
      ¬Fin15AnchoredAtom4152 chi ∧
      ¬Fin15AnchoredAtom4154 chi ∧
      ¬Fin15AnchoredAtom4160 chi ∧
      ¬Fin15AnchoredAtom4181 chi ∧
      ¬Fin15AnchoredAtom4237 chi ∧
      ¬Fin15AnchoredAtom4573 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 5, 6, 7, 8, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask01515
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1897 Fin15AnchoredAtom1898 Fin15AnchoredAtom1899
    Fin15AnchoredAtom1901 Fin15AnchoredAtom1906 Fin15AnchoredAtom1907 Fin15AnchoredAtom1909
    Fin15AnchoredAtom1914 Fin15AnchoredAtom1916 Fin15AnchoredAtom1922 Fin15AnchoredAtom1987
    Fin15AnchoredAtom1988 Fin15AnchoredAtom1990 Fin15AnchoredAtom1995 Fin15AnchoredAtom1997
    Fin15AnchoredAtom2003 Fin15AnchoredAtom2023 Fin15AnchoredAtom2025 Fin15AnchoredAtom2031
    Fin15AnchoredAtom2052 Fin15AnchoredAtom2372 Fin15AnchoredAtom2373 Fin15AnchoredAtom2375
    Fin15AnchoredAtom2380 Fin15AnchoredAtom2382 Fin15AnchoredAtom2388 Fin15AnchoredAtom2408
    Fin15AnchoredAtom2410 Fin15AnchoredAtom2416 Fin15AnchoredAtom2437 Fin15AnchoredAtom2612
    Fin15AnchoredAtom2614 Fin15AnchoredAtom2620 Fin15AnchoredAtom2641 Fin15AnchoredAtom2697
    Fin15AnchoredAtom3087 Fin15AnchoredAtom3088 Fin15AnchoredAtom3090 Fin15AnchoredAtom3095
    Fin15AnchoredAtom3097 Fin15AnchoredAtom3103 Fin15AnchoredAtom3123 Fin15AnchoredAtom3125
    Fin15AnchoredAtom3131 Fin15AnchoredAtom3152 Fin15AnchoredAtom3327 Fin15AnchoredAtom3329
    Fin15AnchoredAtom3335 Fin15AnchoredAtom3356 Fin15AnchoredAtom3412 Fin15AnchoredAtom4152
    Fin15AnchoredAtom4154 Fin15AnchoredAtom4160 Fin15AnchoredAtom4181 Fin15AnchoredAtom4237
    Fin15AnchoredAtom4573 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30872 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
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
      ¬Fin15AnchoredAtom3087 chi ∧
      ¬Fin15AnchoredAtom3089 chi ∧
      ¬Fin15AnchoredAtom3090 chi ∧
      ¬Fin15AnchoredAtom3096 chi ∧
      ¬Fin15AnchoredAtom3097 chi ∧
      ¬Fin15AnchoredAtom3108 chi ∧
      ¬Fin15AnchoredAtom3124 chi ∧
      ¬Fin15AnchoredAtom3125 chi ∧
      ¬Fin15AnchoredAtom3136 chi ∧
      ¬Fin15AnchoredAtom3157 chi ∧
      ¬Fin15AnchoredAtom3328 chi ∧
      ¬Fin15AnchoredAtom3329 chi ∧
      ¬Fin15AnchoredAtom3340 chi ∧
      ¬Fin15AnchoredAtom3361 chi ∧
      ¬Fin15AnchoredAtom3417 chi ∧
      ¬Fin15AnchoredAtom4153 chi ∧
      ¬Fin15AnchoredAtom4154 chi ∧
      ¬Fin15AnchoredAtom4165 chi ∧
      ¬Fin15AnchoredAtom4186 chi ∧
      ¬Fin15AnchoredAtom4242 chi ∧
      ¬Fin15AnchoredAtom4578 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 5, 6, 7, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask01771
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1897 Fin15AnchoredAtom1898 Fin15AnchoredAtom1900
    Fin15AnchoredAtom1901 Fin15AnchoredAtom1906 Fin15AnchoredAtom1908 Fin15AnchoredAtom1909
    Fin15AnchoredAtom1915 Fin15AnchoredAtom1916 Fin15AnchoredAtom1927 Fin15AnchoredAtom1987
    Fin15AnchoredAtom1989 Fin15AnchoredAtom1990 Fin15AnchoredAtom1996 Fin15AnchoredAtom1997
    Fin15AnchoredAtom2008 Fin15AnchoredAtom2024 Fin15AnchoredAtom2025 Fin15AnchoredAtom2036
    Fin15AnchoredAtom2057 Fin15AnchoredAtom2372 Fin15AnchoredAtom2374 Fin15AnchoredAtom2375
    Fin15AnchoredAtom2381 Fin15AnchoredAtom2382 Fin15AnchoredAtom2393 Fin15AnchoredAtom2409
    Fin15AnchoredAtom2410 Fin15AnchoredAtom2421 Fin15AnchoredAtom2442 Fin15AnchoredAtom2613
    Fin15AnchoredAtom2614 Fin15AnchoredAtom2625 Fin15AnchoredAtom2646 Fin15AnchoredAtom2702
    Fin15AnchoredAtom3087 Fin15AnchoredAtom3089 Fin15AnchoredAtom3090 Fin15AnchoredAtom3096
    Fin15AnchoredAtom3097 Fin15AnchoredAtom3108 Fin15AnchoredAtom3124 Fin15AnchoredAtom3125
    Fin15AnchoredAtom3136 Fin15AnchoredAtom3157 Fin15AnchoredAtom3328 Fin15AnchoredAtom3329
    Fin15AnchoredAtom3340 Fin15AnchoredAtom3361 Fin15AnchoredAtom3417 Fin15AnchoredAtom4153
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

theorem fin15Anchored_clause30873 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
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
      ¬Fin15AnchoredAtom3087 chi ∧
      ¬Fin15AnchoredAtom3089 chi ∧
      ¬Fin15AnchoredAtom3092 chi ∧
      ¬Fin15AnchoredAtom3096 chi ∧
      ¬Fin15AnchoredAtom3099 chi ∧
      ¬Fin15AnchoredAtom3110 chi ∧
      ¬Fin15AnchoredAtom3124 chi ∧
      ¬Fin15AnchoredAtom3127 chi ∧
      ¬Fin15AnchoredAtom3138 chi ∧
      ¬Fin15AnchoredAtom3159 chi ∧
      ¬Fin15AnchoredAtom3328 chi ∧
      ¬Fin15AnchoredAtom3331 chi ∧
      ¬Fin15AnchoredAtom3342 chi ∧
      ¬Fin15AnchoredAtom3363 chi ∧
      ¬Fin15AnchoredAtom3419 chi ∧
      ¬Fin15AnchoredAtom4153 chi ∧
      ¬Fin15AnchoredAtom4156 chi ∧
      ¬Fin15AnchoredAtom4167 chi ∧
      ¬Fin15AnchoredAtom4188 chi ∧
      ¬Fin15AnchoredAtom4244 chi ∧
      ¬Fin15AnchoredAtom4580 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 5, 6, 7, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask04843
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1897 Fin15AnchoredAtom1898 Fin15AnchoredAtom1900
    Fin15AnchoredAtom1903 Fin15AnchoredAtom1906 Fin15AnchoredAtom1908 Fin15AnchoredAtom1911
    Fin15AnchoredAtom1915 Fin15AnchoredAtom1918 Fin15AnchoredAtom1929 Fin15AnchoredAtom1987
    Fin15AnchoredAtom1989 Fin15AnchoredAtom1992 Fin15AnchoredAtom1996 Fin15AnchoredAtom1999
    Fin15AnchoredAtom2010 Fin15AnchoredAtom2024 Fin15AnchoredAtom2027 Fin15AnchoredAtom2038
    Fin15AnchoredAtom2059 Fin15AnchoredAtom2372 Fin15AnchoredAtom2374 Fin15AnchoredAtom2377
    Fin15AnchoredAtom2381 Fin15AnchoredAtom2384 Fin15AnchoredAtom2395 Fin15AnchoredAtom2409
    Fin15AnchoredAtom2412 Fin15AnchoredAtom2423 Fin15AnchoredAtom2444 Fin15AnchoredAtom2613
    Fin15AnchoredAtom2616 Fin15AnchoredAtom2627 Fin15AnchoredAtom2648 Fin15AnchoredAtom2704
    Fin15AnchoredAtom3087 Fin15AnchoredAtom3089 Fin15AnchoredAtom3092 Fin15AnchoredAtom3096
    Fin15AnchoredAtom3099 Fin15AnchoredAtom3110 Fin15AnchoredAtom3124 Fin15AnchoredAtom3127
    Fin15AnchoredAtom3138 Fin15AnchoredAtom3159 Fin15AnchoredAtom3328 Fin15AnchoredAtom3331
    Fin15AnchoredAtom3342 Fin15AnchoredAtom3363 Fin15AnchoredAtom3419 Fin15AnchoredAtom4153
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

theorem fin15Anchored_clause30874 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
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
      ¬Fin15AnchoredAtom3087 chi ∧
      ¬Fin15AnchoredAtom3089 chi ∧
      ¬Fin15AnchoredAtom3093 chi ∧
      ¬Fin15AnchoredAtom3096 chi ∧
      ¬Fin15AnchoredAtom3100 chi ∧
      ¬Fin15AnchoredAtom3111 chi ∧
      ¬Fin15AnchoredAtom3124 chi ∧
      ¬Fin15AnchoredAtom3128 chi ∧
      ¬Fin15AnchoredAtom3139 chi ∧
      ¬Fin15AnchoredAtom3160 chi ∧
      ¬Fin15AnchoredAtom3328 chi ∧
      ¬Fin15AnchoredAtom3332 chi ∧
      ¬Fin15AnchoredAtom3343 chi ∧
      ¬Fin15AnchoredAtom3364 chi ∧
      ¬Fin15AnchoredAtom3420 chi ∧
      ¬Fin15AnchoredAtom4153 chi ∧
      ¬Fin15AnchoredAtom4157 chi ∧
      ¬Fin15AnchoredAtom4168 chi ∧
      ¬Fin15AnchoredAtom4189 chi ∧
      ¬Fin15AnchoredAtom4245 chi ∧
      ¬Fin15AnchoredAtom4581 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 5, 6, 7, 9, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask08939
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1897 Fin15AnchoredAtom1898 Fin15AnchoredAtom1900
    Fin15AnchoredAtom1904 Fin15AnchoredAtom1906 Fin15AnchoredAtom1908 Fin15AnchoredAtom1912
    Fin15AnchoredAtom1915 Fin15AnchoredAtom1919 Fin15AnchoredAtom1930 Fin15AnchoredAtom1987
    Fin15AnchoredAtom1989 Fin15AnchoredAtom1993 Fin15AnchoredAtom1996 Fin15AnchoredAtom2000
    Fin15AnchoredAtom2011 Fin15AnchoredAtom2024 Fin15AnchoredAtom2028 Fin15AnchoredAtom2039
    Fin15AnchoredAtom2060 Fin15AnchoredAtom2372 Fin15AnchoredAtom2374 Fin15AnchoredAtom2378
    Fin15AnchoredAtom2381 Fin15AnchoredAtom2385 Fin15AnchoredAtom2396 Fin15AnchoredAtom2409
    Fin15AnchoredAtom2413 Fin15AnchoredAtom2424 Fin15AnchoredAtom2445 Fin15AnchoredAtom2613
    Fin15AnchoredAtom2617 Fin15AnchoredAtom2628 Fin15AnchoredAtom2649 Fin15AnchoredAtom2705
    Fin15AnchoredAtom3087 Fin15AnchoredAtom3089 Fin15AnchoredAtom3093 Fin15AnchoredAtom3096
    Fin15AnchoredAtom3100 Fin15AnchoredAtom3111 Fin15AnchoredAtom3124 Fin15AnchoredAtom3128
    Fin15AnchoredAtom3139 Fin15AnchoredAtom3160 Fin15AnchoredAtom3328 Fin15AnchoredAtom3332
    Fin15AnchoredAtom3343 Fin15AnchoredAtom3364 Fin15AnchoredAtom3420 Fin15AnchoredAtom4153
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

theorem fin15Anchored_clause30875 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
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
      ¬Fin15AnchoredAtom3087 chi ∧
      ¬Fin15AnchoredAtom3089 chi ∧
      ¬Fin15AnchoredAtom3094 chi ∧
      ¬Fin15AnchoredAtom3096 chi ∧
      ¬Fin15AnchoredAtom3101 chi ∧
      ¬Fin15AnchoredAtom3112 chi ∧
      ¬Fin15AnchoredAtom3124 chi ∧
      ¬Fin15AnchoredAtom3129 chi ∧
      ¬Fin15AnchoredAtom3140 chi ∧
      ¬Fin15AnchoredAtom3161 chi ∧
      ¬Fin15AnchoredAtom3328 chi ∧
      ¬Fin15AnchoredAtom3333 chi ∧
      ¬Fin15AnchoredAtom3344 chi ∧
      ¬Fin15AnchoredAtom3365 chi ∧
      ¬Fin15AnchoredAtom3421 chi ∧
      ¬Fin15AnchoredAtom4153 chi ∧
      ¬Fin15AnchoredAtom4158 chi ∧
      ¬Fin15AnchoredAtom4169 chi ∧
      ¬Fin15AnchoredAtom4190 chi ∧
      ¬Fin15AnchoredAtom4246 chi ∧
      ¬Fin15AnchoredAtom4582 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 5, 6, 7, 9, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17131
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1897 Fin15AnchoredAtom1898 Fin15AnchoredAtom1900
    Fin15AnchoredAtom1905 Fin15AnchoredAtom1906 Fin15AnchoredAtom1908 Fin15AnchoredAtom1913
    Fin15AnchoredAtom1915 Fin15AnchoredAtom1920 Fin15AnchoredAtom1931 Fin15AnchoredAtom1987
    Fin15AnchoredAtom1989 Fin15AnchoredAtom1994 Fin15AnchoredAtom1996 Fin15AnchoredAtom2001
    Fin15AnchoredAtom2012 Fin15AnchoredAtom2024 Fin15AnchoredAtom2029 Fin15AnchoredAtom2040
    Fin15AnchoredAtom2061 Fin15AnchoredAtom2372 Fin15AnchoredAtom2374 Fin15AnchoredAtom2379
    Fin15AnchoredAtom2381 Fin15AnchoredAtom2386 Fin15AnchoredAtom2397 Fin15AnchoredAtom2409
    Fin15AnchoredAtom2414 Fin15AnchoredAtom2425 Fin15AnchoredAtom2446 Fin15AnchoredAtom2613
    Fin15AnchoredAtom2618 Fin15AnchoredAtom2629 Fin15AnchoredAtom2650 Fin15AnchoredAtom2706
    Fin15AnchoredAtom3087 Fin15AnchoredAtom3089 Fin15AnchoredAtom3094 Fin15AnchoredAtom3096
    Fin15AnchoredAtom3101 Fin15AnchoredAtom3112 Fin15AnchoredAtom3124 Fin15AnchoredAtom3129
    Fin15AnchoredAtom3140 Fin15AnchoredAtom3161 Fin15AnchoredAtom3328 Fin15AnchoredAtom3333
    Fin15AnchoredAtom3344 Fin15AnchoredAtom3365 Fin15AnchoredAtom3421 Fin15AnchoredAtom4153
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

theorem fin15Anchored_clause30876 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
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
      ¬Fin15AnchoredAtom3087 chi ∧
      ¬Fin15AnchoredAtom3090 chi ∧
      ¬Fin15AnchoredAtom3092 chi ∧
      ¬Fin15AnchoredAtom3097 chi ∧
      ¬Fin15AnchoredAtom3099 chi ∧
      ¬Fin15AnchoredAtom3114 chi ∧
      ¬Fin15AnchoredAtom3125 chi ∧
      ¬Fin15AnchoredAtom3127 chi ∧
      ¬Fin15AnchoredAtom3142 chi ∧
      ¬Fin15AnchoredAtom3163 chi ∧
      ¬Fin15AnchoredAtom3329 chi ∧
      ¬Fin15AnchoredAtom3331 chi ∧
      ¬Fin15AnchoredAtom3346 chi ∧
      ¬Fin15AnchoredAtom3367 chi ∧
      ¬Fin15AnchoredAtom3423 chi ∧
      ¬Fin15AnchoredAtom4154 chi ∧
      ¬Fin15AnchoredAtom4156 chi ∧
      ¬Fin15AnchoredAtom4171 chi ∧
      ¬Fin15AnchoredAtom4192 chi ∧
      ¬Fin15AnchoredAtom4248 chi ∧
      ¬Fin15AnchoredAtom4584 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 5, 6, 7, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05355
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1897 Fin15AnchoredAtom1898 Fin15AnchoredAtom1901
    Fin15AnchoredAtom1903 Fin15AnchoredAtom1906 Fin15AnchoredAtom1909 Fin15AnchoredAtom1911
    Fin15AnchoredAtom1916 Fin15AnchoredAtom1918 Fin15AnchoredAtom1933 Fin15AnchoredAtom1987
    Fin15AnchoredAtom1990 Fin15AnchoredAtom1992 Fin15AnchoredAtom1997 Fin15AnchoredAtom1999
    Fin15AnchoredAtom2014 Fin15AnchoredAtom2025 Fin15AnchoredAtom2027 Fin15AnchoredAtom2042
    Fin15AnchoredAtom2063 Fin15AnchoredAtom2372 Fin15AnchoredAtom2375 Fin15AnchoredAtom2377
    Fin15AnchoredAtom2382 Fin15AnchoredAtom2384 Fin15AnchoredAtom2399 Fin15AnchoredAtom2410
    Fin15AnchoredAtom2412 Fin15AnchoredAtom2427 Fin15AnchoredAtom2448 Fin15AnchoredAtom2614
    Fin15AnchoredAtom2616 Fin15AnchoredAtom2631 Fin15AnchoredAtom2652 Fin15AnchoredAtom2708
    Fin15AnchoredAtom3087 Fin15AnchoredAtom3090 Fin15AnchoredAtom3092 Fin15AnchoredAtom3097
    Fin15AnchoredAtom3099 Fin15AnchoredAtom3114 Fin15AnchoredAtom3125 Fin15AnchoredAtom3127
    Fin15AnchoredAtom3142 Fin15AnchoredAtom3163 Fin15AnchoredAtom3329 Fin15AnchoredAtom3331
    Fin15AnchoredAtom3346 Fin15AnchoredAtom3367 Fin15AnchoredAtom3423 Fin15AnchoredAtom4154
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

theorem fin15Anchored_clause30877 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
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
      ¬Fin15AnchoredAtom3087 chi ∧
      ¬Fin15AnchoredAtom3090 chi ∧
      ¬Fin15AnchoredAtom3093 chi ∧
      ¬Fin15AnchoredAtom3097 chi ∧
      ¬Fin15AnchoredAtom3100 chi ∧
      ¬Fin15AnchoredAtom3115 chi ∧
      ¬Fin15AnchoredAtom3125 chi ∧
      ¬Fin15AnchoredAtom3128 chi ∧
      ¬Fin15AnchoredAtom3143 chi ∧
      ¬Fin15AnchoredAtom3164 chi ∧
      ¬Fin15AnchoredAtom3329 chi ∧
      ¬Fin15AnchoredAtom3332 chi ∧
      ¬Fin15AnchoredAtom3347 chi ∧
      ¬Fin15AnchoredAtom3368 chi ∧
      ¬Fin15AnchoredAtom3424 chi ∧
      ¬Fin15AnchoredAtom4154 chi ∧
      ¬Fin15AnchoredAtom4157 chi ∧
      ¬Fin15AnchoredAtom4172 chi ∧
      ¬Fin15AnchoredAtom4193 chi ∧
      ¬Fin15AnchoredAtom4249 chi ∧
      ¬Fin15AnchoredAtom4585 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 5, 6, 7, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09451
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1897 Fin15AnchoredAtom1898 Fin15AnchoredAtom1901
    Fin15AnchoredAtom1904 Fin15AnchoredAtom1906 Fin15AnchoredAtom1909 Fin15AnchoredAtom1912
    Fin15AnchoredAtom1916 Fin15AnchoredAtom1919 Fin15AnchoredAtom1934 Fin15AnchoredAtom1987
    Fin15AnchoredAtom1990 Fin15AnchoredAtom1993 Fin15AnchoredAtom1997 Fin15AnchoredAtom2000
    Fin15AnchoredAtom2015 Fin15AnchoredAtom2025 Fin15AnchoredAtom2028 Fin15AnchoredAtom2043
    Fin15AnchoredAtom2064 Fin15AnchoredAtom2372 Fin15AnchoredAtom2375 Fin15AnchoredAtom2378
    Fin15AnchoredAtom2382 Fin15AnchoredAtom2385 Fin15AnchoredAtom2400 Fin15AnchoredAtom2410
    Fin15AnchoredAtom2413 Fin15AnchoredAtom2428 Fin15AnchoredAtom2449 Fin15AnchoredAtom2614
    Fin15AnchoredAtom2617 Fin15AnchoredAtom2632 Fin15AnchoredAtom2653 Fin15AnchoredAtom2709
    Fin15AnchoredAtom3087 Fin15AnchoredAtom3090 Fin15AnchoredAtom3093 Fin15AnchoredAtom3097
    Fin15AnchoredAtom3100 Fin15AnchoredAtom3115 Fin15AnchoredAtom3125 Fin15AnchoredAtom3128
    Fin15AnchoredAtom3143 Fin15AnchoredAtom3164 Fin15AnchoredAtom3329 Fin15AnchoredAtom3332
    Fin15AnchoredAtom3347 Fin15AnchoredAtom3368 Fin15AnchoredAtom3424 Fin15AnchoredAtom4154
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

theorem fin15Anchored_clause30878 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1935 chi ∧
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
      ¬Fin15AnchoredAtom3087 chi ∧
      ¬Fin15AnchoredAtom3090 chi ∧
      ¬Fin15AnchoredAtom3094 chi ∧
      ¬Fin15AnchoredAtom3097 chi ∧
      ¬Fin15AnchoredAtom3101 chi ∧
      ¬Fin15AnchoredAtom3116 chi ∧
      ¬Fin15AnchoredAtom3125 chi ∧
      ¬Fin15AnchoredAtom3129 chi ∧
      ¬Fin15AnchoredAtom3144 chi ∧
      ¬Fin15AnchoredAtom3165 chi ∧
      ¬Fin15AnchoredAtom3329 chi ∧
      ¬Fin15AnchoredAtom3333 chi ∧
      ¬Fin15AnchoredAtom3348 chi ∧
      ¬Fin15AnchoredAtom3369 chi ∧
      ¬Fin15AnchoredAtom3425 chi ∧
      ¬Fin15AnchoredAtom4154 chi ∧
      ¬Fin15AnchoredAtom4158 chi ∧
      ¬Fin15AnchoredAtom4173 chi ∧
      ¬Fin15AnchoredAtom4194 chi ∧
      ¬Fin15AnchoredAtom4250 chi ∧
      ¬Fin15AnchoredAtom4586 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 5, 6, 7, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17643
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1897 Fin15AnchoredAtom1898 Fin15AnchoredAtom1901
    Fin15AnchoredAtom1905 Fin15AnchoredAtom1906 Fin15AnchoredAtom1909 Fin15AnchoredAtom1913
    Fin15AnchoredAtom1916 Fin15AnchoredAtom1920 Fin15AnchoredAtom1935 Fin15AnchoredAtom1987
    Fin15AnchoredAtom1990 Fin15AnchoredAtom1994 Fin15AnchoredAtom1997 Fin15AnchoredAtom2001
    Fin15AnchoredAtom2016 Fin15AnchoredAtom2025 Fin15AnchoredAtom2029 Fin15AnchoredAtom2044
    Fin15AnchoredAtom2065 Fin15AnchoredAtom2372 Fin15AnchoredAtom2375 Fin15AnchoredAtom2379
    Fin15AnchoredAtom2382 Fin15AnchoredAtom2386 Fin15AnchoredAtom2401 Fin15AnchoredAtom2410
    Fin15AnchoredAtom2414 Fin15AnchoredAtom2429 Fin15AnchoredAtom2450 Fin15AnchoredAtom2614
    Fin15AnchoredAtom2618 Fin15AnchoredAtom2633 Fin15AnchoredAtom2654 Fin15AnchoredAtom2710
    Fin15AnchoredAtom3087 Fin15AnchoredAtom3090 Fin15AnchoredAtom3094 Fin15AnchoredAtom3097
    Fin15AnchoredAtom3101 Fin15AnchoredAtom3116 Fin15AnchoredAtom3125 Fin15AnchoredAtom3129
    Fin15AnchoredAtom3144 Fin15AnchoredAtom3165 Fin15AnchoredAtom3329 Fin15AnchoredAtom3333
    Fin15AnchoredAtom3348 Fin15AnchoredAtom3369 Fin15AnchoredAtom3425 Fin15AnchoredAtom4154
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

theorem fin15Anchored_clause30879 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1939 chi ∧
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
      ¬Fin15AnchoredAtom3087 chi ∧
      ¬Fin15AnchoredAtom3092 chi ∧
      ¬Fin15AnchoredAtom3093 chi ∧
      ¬Fin15AnchoredAtom3099 chi ∧
      ¬Fin15AnchoredAtom3100 chi ∧
      ¬Fin15AnchoredAtom3120 chi ∧
      ¬Fin15AnchoredAtom3127 chi ∧
      ¬Fin15AnchoredAtom3128 chi ∧
      ¬Fin15AnchoredAtom3148 chi ∧
      ¬Fin15AnchoredAtom3169 chi ∧
      ¬Fin15AnchoredAtom3331 chi ∧
      ¬Fin15AnchoredAtom3332 chi ∧
      ¬Fin15AnchoredAtom3352 chi ∧
      ¬Fin15AnchoredAtom3373 chi ∧
      ¬Fin15AnchoredAtom3429 chi ∧
      ¬Fin15AnchoredAtom4156 chi ∧
      ¬Fin15AnchoredAtom4157 chi ∧
      ¬Fin15AnchoredAtom4177 chi ∧
      ¬Fin15AnchoredAtom4198 chi ∧
      ¬Fin15AnchoredAtom4254 chi ∧
      ¬Fin15AnchoredAtom4590 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 5, 6, 7, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask12523
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1897 Fin15AnchoredAtom1898 Fin15AnchoredAtom1903
    Fin15AnchoredAtom1904 Fin15AnchoredAtom1906 Fin15AnchoredAtom1911 Fin15AnchoredAtom1912
    Fin15AnchoredAtom1918 Fin15AnchoredAtom1919 Fin15AnchoredAtom1939 Fin15AnchoredAtom1987
    Fin15AnchoredAtom1992 Fin15AnchoredAtom1993 Fin15AnchoredAtom1999 Fin15AnchoredAtom2000
    Fin15AnchoredAtom2020 Fin15AnchoredAtom2027 Fin15AnchoredAtom2028 Fin15AnchoredAtom2048
    Fin15AnchoredAtom2069 Fin15AnchoredAtom2372 Fin15AnchoredAtom2377 Fin15AnchoredAtom2378
    Fin15AnchoredAtom2384 Fin15AnchoredAtom2385 Fin15AnchoredAtom2405 Fin15AnchoredAtom2412
    Fin15AnchoredAtom2413 Fin15AnchoredAtom2433 Fin15AnchoredAtom2454 Fin15AnchoredAtom2616
    Fin15AnchoredAtom2617 Fin15AnchoredAtom2637 Fin15AnchoredAtom2658 Fin15AnchoredAtom2714
    Fin15AnchoredAtom3087 Fin15AnchoredAtom3092 Fin15AnchoredAtom3093 Fin15AnchoredAtom3099
    Fin15AnchoredAtom3100 Fin15AnchoredAtom3120 Fin15AnchoredAtom3127 Fin15AnchoredAtom3128
    Fin15AnchoredAtom3148 Fin15AnchoredAtom3169 Fin15AnchoredAtom3331 Fin15AnchoredAtom3332
    Fin15AnchoredAtom3352 Fin15AnchoredAtom3373 Fin15AnchoredAtom3429 Fin15AnchoredAtom4156
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

theorem fin15Anchored_clause30880 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1940 chi ∧
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
      ¬Fin15AnchoredAtom3087 chi ∧
      ¬Fin15AnchoredAtom3092 chi ∧
      ¬Fin15AnchoredAtom3094 chi ∧
      ¬Fin15AnchoredAtom3099 chi ∧
      ¬Fin15AnchoredAtom3101 chi ∧
      ¬Fin15AnchoredAtom3121 chi ∧
      ¬Fin15AnchoredAtom3127 chi ∧
      ¬Fin15AnchoredAtom3129 chi ∧
      ¬Fin15AnchoredAtom3149 chi ∧
      ¬Fin15AnchoredAtom3170 chi ∧
      ¬Fin15AnchoredAtom3331 chi ∧
      ¬Fin15AnchoredAtom3333 chi ∧
      ¬Fin15AnchoredAtom3353 chi ∧
      ¬Fin15AnchoredAtom3374 chi ∧
      ¬Fin15AnchoredAtom3430 chi ∧
      ¬Fin15AnchoredAtom4156 chi ∧
      ¬Fin15AnchoredAtom4158 chi ∧
      ¬Fin15AnchoredAtom4178 chi ∧
      ¬Fin15AnchoredAtom4199 chi ∧
      ¬Fin15AnchoredAtom4255 chi ∧
      ¬Fin15AnchoredAtom4591 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 5, 6, 7, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask20715
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1897 Fin15AnchoredAtom1898 Fin15AnchoredAtom1903
    Fin15AnchoredAtom1905 Fin15AnchoredAtom1906 Fin15AnchoredAtom1911 Fin15AnchoredAtom1913
    Fin15AnchoredAtom1918 Fin15AnchoredAtom1920 Fin15AnchoredAtom1940 Fin15AnchoredAtom1987
    Fin15AnchoredAtom1992 Fin15AnchoredAtom1994 Fin15AnchoredAtom1999 Fin15AnchoredAtom2001
    Fin15AnchoredAtom2021 Fin15AnchoredAtom2027 Fin15AnchoredAtom2029 Fin15AnchoredAtom2049
    Fin15AnchoredAtom2070 Fin15AnchoredAtom2372 Fin15AnchoredAtom2377 Fin15AnchoredAtom2379
    Fin15AnchoredAtom2384 Fin15AnchoredAtom2386 Fin15AnchoredAtom2406 Fin15AnchoredAtom2412
    Fin15AnchoredAtom2414 Fin15AnchoredAtom2434 Fin15AnchoredAtom2455 Fin15AnchoredAtom2616
    Fin15AnchoredAtom2618 Fin15AnchoredAtom2638 Fin15AnchoredAtom2659 Fin15AnchoredAtom2715
    Fin15AnchoredAtom3087 Fin15AnchoredAtom3092 Fin15AnchoredAtom3094 Fin15AnchoredAtom3099
    Fin15AnchoredAtom3101 Fin15AnchoredAtom3121 Fin15AnchoredAtom3127 Fin15AnchoredAtom3129
    Fin15AnchoredAtom3149 Fin15AnchoredAtom3170 Fin15AnchoredAtom3331 Fin15AnchoredAtom3333
    Fin15AnchoredAtom3353 Fin15AnchoredAtom3374 Fin15AnchoredAtom3430 Fin15AnchoredAtom4156
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

theorem fin15Anchored_clause30881 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
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
      ¬Fin15AnchoredAtom3087 chi ∧
      ¬Fin15AnchoredAtom3093 chi ∧
      ¬Fin15AnchoredAtom3094 chi ∧
      ¬Fin15AnchoredAtom3100 chi ∧
      ¬Fin15AnchoredAtom3101 chi ∧
      ¬Fin15AnchoredAtom3122 chi ∧
      ¬Fin15AnchoredAtom3128 chi ∧
      ¬Fin15AnchoredAtom3129 chi ∧
      ¬Fin15AnchoredAtom3150 chi ∧
      ¬Fin15AnchoredAtom3171 chi ∧
      ¬Fin15AnchoredAtom3332 chi ∧
      ¬Fin15AnchoredAtom3333 chi ∧
      ¬Fin15AnchoredAtom3354 chi ∧
      ¬Fin15AnchoredAtom3375 chi ∧
      ¬Fin15AnchoredAtom3431 chi ∧
      ¬Fin15AnchoredAtom4157 chi ∧
      ¬Fin15AnchoredAtom4158 chi ∧
      ¬Fin15AnchoredAtom4179 chi ∧
      ¬Fin15AnchoredAtom4200 chi ∧
      ¬Fin15AnchoredAtom4256 chi ∧
      ¬Fin15AnchoredAtom4592 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 5, 6, 7, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask24811
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1897 Fin15AnchoredAtom1898 Fin15AnchoredAtom1904
    Fin15AnchoredAtom1905 Fin15AnchoredAtom1906 Fin15AnchoredAtom1912 Fin15AnchoredAtom1913
    Fin15AnchoredAtom1919 Fin15AnchoredAtom1920 Fin15AnchoredAtom1941 Fin15AnchoredAtom1987
    Fin15AnchoredAtom1993 Fin15AnchoredAtom1994 Fin15AnchoredAtom2000 Fin15AnchoredAtom2001
    Fin15AnchoredAtom2022 Fin15AnchoredAtom2028 Fin15AnchoredAtom2029 Fin15AnchoredAtom2050
    Fin15AnchoredAtom2071 Fin15AnchoredAtom2372 Fin15AnchoredAtom2378 Fin15AnchoredAtom2379
    Fin15AnchoredAtom2385 Fin15AnchoredAtom2386 Fin15AnchoredAtom2407 Fin15AnchoredAtom2413
    Fin15AnchoredAtom2414 Fin15AnchoredAtom2435 Fin15AnchoredAtom2456 Fin15AnchoredAtom2617
    Fin15AnchoredAtom2618 Fin15AnchoredAtom2639 Fin15AnchoredAtom2660 Fin15AnchoredAtom2716
    Fin15AnchoredAtom3087 Fin15AnchoredAtom3093 Fin15AnchoredAtom3094 Fin15AnchoredAtom3100
    Fin15AnchoredAtom3101 Fin15AnchoredAtom3122 Fin15AnchoredAtom3128 Fin15AnchoredAtom3129
    Fin15AnchoredAtom3150 Fin15AnchoredAtom3171 Fin15AnchoredAtom3332 Fin15AnchoredAtom3333
    Fin15AnchoredAtom3354 Fin15AnchoredAtom3375 Fin15AnchoredAtom3431 Fin15AnchoredAtom4157
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

theorem fin15Anchored_clause30882 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1899 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1907 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1921 chi ∧
      ¬Fin15AnchoredAtom1925 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1988 chi ∧
      ¬Fin15AnchoredAtom1989 chi ∧
      ¬Fin15AnchoredAtom1993 chi ∧
      ¬Fin15AnchoredAtom2002 chi ∧
      ¬Fin15AnchoredAtom2006 chi ∧
      ¬Fin15AnchoredAtom2011 chi ∧
      ¬Fin15AnchoredAtom2030 chi ∧
      ¬Fin15AnchoredAtom2034 chi ∧
      ¬Fin15AnchoredAtom2039 chi ∧
      ¬Fin15AnchoredAtom2075 chi ∧
      ¬Fin15AnchoredAtom2373 chi ∧
      ¬Fin15AnchoredAtom2374 chi ∧
      ¬Fin15AnchoredAtom2378 chi ∧
      ¬Fin15AnchoredAtom2387 chi ∧
      ¬Fin15AnchoredAtom2391 chi ∧
      ¬Fin15AnchoredAtom2396 chi ∧
      ¬Fin15AnchoredAtom2415 chi ∧
      ¬Fin15AnchoredAtom2419 chi ∧
      ¬Fin15AnchoredAtom2424 chi ∧
      ¬Fin15AnchoredAtom2460 chi ∧
      ¬Fin15AnchoredAtom2619 chi ∧
      ¬Fin15AnchoredAtom2623 chi ∧
      ¬Fin15AnchoredAtom2628 chi ∧
      ¬Fin15AnchoredAtom2664 chi ∧
      ¬Fin15AnchoredAtom2720 chi ∧
      ¬Fin15AnchoredAtom3088 chi ∧
      ¬Fin15AnchoredAtom3089 chi ∧
      ¬Fin15AnchoredAtom3093 chi ∧
      ¬Fin15AnchoredAtom3102 chi ∧
      ¬Fin15AnchoredAtom3106 chi ∧
      ¬Fin15AnchoredAtom3111 chi ∧
      ¬Fin15AnchoredAtom3130 chi ∧
      ¬Fin15AnchoredAtom3134 chi ∧
      ¬Fin15AnchoredAtom3139 chi ∧
      ¬Fin15AnchoredAtom3175 chi ∧
      ¬Fin15AnchoredAtom3334 chi ∧
      ¬Fin15AnchoredAtom3338 chi ∧
      ¬Fin15AnchoredAtom3343 chi ∧
      ¬Fin15AnchoredAtom3379 chi ∧
      ¬Fin15AnchoredAtom3435 chi ∧
      ¬Fin15AnchoredAtom4159 chi ∧
      ¬Fin15AnchoredAtom4163 chi ∧
      ¬Fin15AnchoredAtom4168 chi ∧
      ¬Fin15AnchoredAtom4204 chi ∧
      ¬Fin15AnchoredAtom4260 chi ∧
      ¬Fin15AnchoredAtom4596 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 5, 6, 8, 9, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09067
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1897 Fin15AnchoredAtom1899 Fin15AnchoredAtom1900
    Fin15AnchoredAtom1904 Fin15AnchoredAtom1907 Fin15AnchoredAtom1908 Fin15AnchoredAtom1912
    Fin15AnchoredAtom1921 Fin15AnchoredAtom1925 Fin15AnchoredAtom1930 Fin15AnchoredAtom1988
    Fin15AnchoredAtom1989 Fin15AnchoredAtom1993 Fin15AnchoredAtom2002 Fin15AnchoredAtom2006
    Fin15AnchoredAtom2011 Fin15AnchoredAtom2030 Fin15AnchoredAtom2034 Fin15AnchoredAtom2039
    Fin15AnchoredAtom2075 Fin15AnchoredAtom2373 Fin15AnchoredAtom2374 Fin15AnchoredAtom2378
    Fin15AnchoredAtom2387 Fin15AnchoredAtom2391 Fin15AnchoredAtom2396 Fin15AnchoredAtom2415
    Fin15AnchoredAtom2419 Fin15AnchoredAtom2424 Fin15AnchoredAtom2460 Fin15AnchoredAtom2619
    Fin15AnchoredAtom2623 Fin15AnchoredAtom2628 Fin15AnchoredAtom2664 Fin15AnchoredAtom2720
    Fin15AnchoredAtom3088 Fin15AnchoredAtom3089 Fin15AnchoredAtom3093 Fin15AnchoredAtom3102
    Fin15AnchoredAtom3106 Fin15AnchoredAtom3111 Fin15AnchoredAtom3130 Fin15AnchoredAtom3134
    Fin15AnchoredAtom3139 Fin15AnchoredAtom3175 Fin15AnchoredAtom3334 Fin15AnchoredAtom3338
    Fin15AnchoredAtom3343 Fin15AnchoredAtom3379 Fin15AnchoredAtom3435 Fin15AnchoredAtom4159
    Fin15AnchoredAtom4163 Fin15AnchoredAtom4168 Fin15AnchoredAtom4204 Fin15AnchoredAtom4260
    Fin15AnchoredAtom4596 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30883 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1899 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1907 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1922 chi ∧
      ¬Fin15AnchoredAtom1924 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom1988 chi ∧
      ¬Fin15AnchoredAtom1990 chi ∧
      ¬Fin15AnchoredAtom1992 chi ∧
      ¬Fin15AnchoredAtom2003 chi ∧
      ¬Fin15AnchoredAtom2005 chi ∧
      ¬Fin15AnchoredAtom2014 chi ∧
      ¬Fin15AnchoredAtom2031 chi ∧
      ¬Fin15AnchoredAtom2033 chi ∧
      ¬Fin15AnchoredAtom2042 chi ∧
      ¬Fin15AnchoredAtom2078 chi ∧
      ¬Fin15AnchoredAtom2373 chi ∧
      ¬Fin15AnchoredAtom2375 chi ∧
      ¬Fin15AnchoredAtom2377 chi ∧
      ¬Fin15AnchoredAtom2388 chi ∧
      ¬Fin15AnchoredAtom2390 chi ∧
      ¬Fin15AnchoredAtom2399 chi ∧
      ¬Fin15AnchoredAtom2416 chi ∧
      ¬Fin15AnchoredAtom2418 chi ∧
      ¬Fin15AnchoredAtom2427 chi ∧
      ¬Fin15AnchoredAtom2463 chi ∧
      ¬Fin15AnchoredAtom2620 chi ∧
      ¬Fin15AnchoredAtom2622 chi ∧
      ¬Fin15AnchoredAtom2631 chi ∧
      ¬Fin15AnchoredAtom2667 chi ∧
      ¬Fin15AnchoredAtom2723 chi ∧
      ¬Fin15AnchoredAtom3088 chi ∧
      ¬Fin15AnchoredAtom3090 chi ∧
      ¬Fin15AnchoredAtom3092 chi ∧
      ¬Fin15AnchoredAtom3103 chi ∧
      ¬Fin15AnchoredAtom3105 chi ∧
      ¬Fin15AnchoredAtom3114 chi ∧
      ¬Fin15AnchoredAtom3131 chi ∧
      ¬Fin15AnchoredAtom3133 chi ∧
      ¬Fin15AnchoredAtom3142 chi ∧
      ¬Fin15AnchoredAtom3178 chi ∧
      ¬Fin15AnchoredAtom3335 chi ∧
      ¬Fin15AnchoredAtom3337 chi ∧
      ¬Fin15AnchoredAtom3346 chi ∧
      ¬Fin15AnchoredAtom3382 chi ∧
      ¬Fin15AnchoredAtom3438 chi ∧
      ¬Fin15AnchoredAtom4160 chi ∧
      ¬Fin15AnchoredAtom4162 chi ∧
      ¬Fin15AnchoredAtom4171 chi ∧
      ¬Fin15AnchoredAtom4207 chi ∧
      ¬Fin15AnchoredAtom4263 chi ∧
      ¬Fin15AnchoredAtom4599 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 5, 6, 8, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05483
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1897 Fin15AnchoredAtom1899 Fin15AnchoredAtom1901
    Fin15AnchoredAtom1903 Fin15AnchoredAtom1907 Fin15AnchoredAtom1909 Fin15AnchoredAtom1911
    Fin15AnchoredAtom1922 Fin15AnchoredAtom1924 Fin15AnchoredAtom1933 Fin15AnchoredAtom1988
    Fin15AnchoredAtom1990 Fin15AnchoredAtom1992 Fin15AnchoredAtom2003 Fin15AnchoredAtom2005
    Fin15AnchoredAtom2014 Fin15AnchoredAtom2031 Fin15AnchoredAtom2033 Fin15AnchoredAtom2042
    Fin15AnchoredAtom2078 Fin15AnchoredAtom2373 Fin15AnchoredAtom2375 Fin15AnchoredAtom2377
    Fin15AnchoredAtom2388 Fin15AnchoredAtom2390 Fin15AnchoredAtom2399 Fin15AnchoredAtom2416
    Fin15AnchoredAtom2418 Fin15AnchoredAtom2427 Fin15AnchoredAtom2463 Fin15AnchoredAtom2620
    Fin15AnchoredAtom2622 Fin15AnchoredAtom2631 Fin15AnchoredAtom2667 Fin15AnchoredAtom2723
    Fin15AnchoredAtom3088 Fin15AnchoredAtom3090 Fin15AnchoredAtom3092 Fin15AnchoredAtom3103
    Fin15AnchoredAtom3105 Fin15AnchoredAtom3114 Fin15AnchoredAtom3131 Fin15AnchoredAtom3133
    Fin15AnchoredAtom3142 Fin15AnchoredAtom3178 Fin15AnchoredAtom3335 Fin15AnchoredAtom3337
    Fin15AnchoredAtom3346 Fin15AnchoredAtom3382 Fin15AnchoredAtom3438 Fin15AnchoredAtom4160
    Fin15AnchoredAtom4162 Fin15AnchoredAtom4171 Fin15AnchoredAtom4207 Fin15AnchoredAtom4263
    Fin15AnchoredAtom4599 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30884 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1899 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1907 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1922 chi ∧
      ¬Fin15AnchoredAtom1925 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom1988 chi ∧
      ¬Fin15AnchoredAtom1990 chi ∧
      ¬Fin15AnchoredAtom1993 chi ∧
      ¬Fin15AnchoredAtom2003 chi ∧
      ¬Fin15AnchoredAtom2006 chi ∧
      ¬Fin15AnchoredAtom2015 chi ∧
      ¬Fin15AnchoredAtom2031 chi ∧
      ¬Fin15AnchoredAtom2034 chi ∧
      ¬Fin15AnchoredAtom2043 chi ∧
      ¬Fin15AnchoredAtom2079 chi ∧
      ¬Fin15AnchoredAtom2373 chi ∧
      ¬Fin15AnchoredAtom2375 chi ∧
      ¬Fin15AnchoredAtom2378 chi ∧
      ¬Fin15AnchoredAtom2388 chi ∧
      ¬Fin15AnchoredAtom2391 chi ∧
      ¬Fin15AnchoredAtom2400 chi ∧
      ¬Fin15AnchoredAtom2416 chi ∧
      ¬Fin15AnchoredAtom2419 chi ∧
      ¬Fin15AnchoredAtom2428 chi ∧
      ¬Fin15AnchoredAtom2464 chi ∧
      ¬Fin15AnchoredAtom2620 chi ∧
      ¬Fin15AnchoredAtom2623 chi ∧
      ¬Fin15AnchoredAtom2632 chi ∧
      ¬Fin15AnchoredAtom2668 chi ∧
      ¬Fin15AnchoredAtom2724 chi ∧
      ¬Fin15AnchoredAtom3088 chi ∧
      ¬Fin15AnchoredAtom3090 chi ∧
      ¬Fin15AnchoredAtom3093 chi ∧
      ¬Fin15AnchoredAtom3103 chi ∧
      ¬Fin15AnchoredAtom3106 chi ∧
      ¬Fin15AnchoredAtom3115 chi ∧
      ¬Fin15AnchoredAtom3131 chi ∧
      ¬Fin15AnchoredAtom3134 chi ∧
      ¬Fin15AnchoredAtom3143 chi ∧
      ¬Fin15AnchoredAtom3179 chi ∧
      ¬Fin15AnchoredAtom3335 chi ∧
      ¬Fin15AnchoredAtom3338 chi ∧
      ¬Fin15AnchoredAtom3347 chi ∧
      ¬Fin15AnchoredAtom3383 chi ∧
      ¬Fin15AnchoredAtom3439 chi ∧
      ¬Fin15AnchoredAtom4160 chi ∧
      ¬Fin15AnchoredAtom4163 chi ∧
      ¬Fin15AnchoredAtom4172 chi ∧
      ¬Fin15AnchoredAtom4208 chi ∧
      ¬Fin15AnchoredAtom4264 chi ∧
      ¬Fin15AnchoredAtom4600 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 5, 6, 8, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09579
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1897 Fin15AnchoredAtom1899 Fin15AnchoredAtom1901
    Fin15AnchoredAtom1904 Fin15AnchoredAtom1907 Fin15AnchoredAtom1909 Fin15AnchoredAtom1912
    Fin15AnchoredAtom1922 Fin15AnchoredAtom1925 Fin15AnchoredAtom1934 Fin15AnchoredAtom1988
    Fin15AnchoredAtom1990 Fin15AnchoredAtom1993 Fin15AnchoredAtom2003 Fin15AnchoredAtom2006
    Fin15AnchoredAtom2015 Fin15AnchoredAtom2031 Fin15AnchoredAtom2034 Fin15AnchoredAtom2043
    Fin15AnchoredAtom2079 Fin15AnchoredAtom2373 Fin15AnchoredAtom2375 Fin15AnchoredAtom2378
    Fin15AnchoredAtom2388 Fin15AnchoredAtom2391 Fin15AnchoredAtom2400 Fin15AnchoredAtom2416
    Fin15AnchoredAtom2419 Fin15AnchoredAtom2428 Fin15AnchoredAtom2464 Fin15AnchoredAtom2620
    Fin15AnchoredAtom2623 Fin15AnchoredAtom2632 Fin15AnchoredAtom2668 Fin15AnchoredAtom2724
    Fin15AnchoredAtom3088 Fin15AnchoredAtom3090 Fin15AnchoredAtom3093 Fin15AnchoredAtom3103
    Fin15AnchoredAtom3106 Fin15AnchoredAtom3115 Fin15AnchoredAtom3131 Fin15AnchoredAtom3134
    Fin15AnchoredAtom3143 Fin15AnchoredAtom3179 Fin15AnchoredAtom3335 Fin15AnchoredAtom3338
    Fin15AnchoredAtom3347 Fin15AnchoredAtom3383 Fin15AnchoredAtom3439 Fin15AnchoredAtom4160
    Fin15AnchoredAtom4163 Fin15AnchoredAtom4172 Fin15AnchoredAtom4208 Fin15AnchoredAtom4264
    Fin15AnchoredAtom4600 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30885 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1899 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1907 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1925 chi ∧
      ¬Fin15AnchoredAtom1926 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
      ¬Fin15AnchoredAtom1988 chi ∧
      ¬Fin15AnchoredAtom1993 chi ∧
      ¬Fin15AnchoredAtom1994 chi ∧
      ¬Fin15AnchoredAtom2006 chi ∧
      ¬Fin15AnchoredAtom2007 chi ∧
      ¬Fin15AnchoredAtom2022 chi ∧
      ¬Fin15AnchoredAtom2034 chi ∧
      ¬Fin15AnchoredAtom2035 chi ∧
      ¬Fin15AnchoredAtom2050 chi ∧
      ¬Fin15AnchoredAtom2086 chi ∧
      ¬Fin15AnchoredAtom2373 chi ∧
      ¬Fin15AnchoredAtom2378 chi ∧
      ¬Fin15AnchoredAtom2379 chi ∧
      ¬Fin15AnchoredAtom2391 chi ∧
      ¬Fin15AnchoredAtom2392 chi ∧
      ¬Fin15AnchoredAtom2407 chi ∧
      ¬Fin15AnchoredAtom2419 chi ∧
      ¬Fin15AnchoredAtom2420 chi ∧
      ¬Fin15AnchoredAtom2435 chi ∧
      ¬Fin15AnchoredAtom2471 chi ∧
      ¬Fin15AnchoredAtom2623 chi ∧
      ¬Fin15AnchoredAtom2624 chi ∧
      ¬Fin15AnchoredAtom2639 chi ∧
      ¬Fin15AnchoredAtom2675 chi ∧
      ¬Fin15AnchoredAtom2731 chi ∧
      ¬Fin15AnchoredAtom3088 chi ∧
      ¬Fin15AnchoredAtom3093 chi ∧
      ¬Fin15AnchoredAtom3094 chi ∧
      ¬Fin15AnchoredAtom3106 chi ∧
      ¬Fin15AnchoredAtom3107 chi ∧
      ¬Fin15AnchoredAtom3122 chi ∧
      ¬Fin15AnchoredAtom3134 chi ∧
      ¬Fin15AnchoredAtom3135 chi ∧
      ¬Fin15AnchoredAtom3150 chi ∧
      ¬Fin15AnchoredAtom3186 chi ∧
      ¬Fin15AnchoredAtom3338 chi ∧
      ¬Fin15AnchoredAtom3339 chi ∧
      ¬Fin15AnchoredAtom3354 chi ∧
      ¬Fin15AnchoredAtom3390 chi ∧
      ¬Fin15AnchoredAtom3446 chi ∧
      ¬Fin15AnchoredAtom4163 chi ∧
      ¬Fin15AnchoredAtom4164 chi ∧
      ¬Fin15AnchoredAtom4179 chi ∧
      ¬Fin15AnchoredAtom4215 chi ∧
      ¬Fin15AnchoredAtom4271 chi ∧
      ¬Fin15AnchoredAtom4607 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 5, 6, 8, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask24939
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1897 Fin15AnchoredAtom1899 Fin15AnchoredAtom1904
    Fin15AnchoredAtom1905 Fin15AnchoredAtom1907 Fin15AnchoredAtom1912 Fin15AnchoredAtom1913
    Fin15AnchoredAtom1925 Fin15AnchoredAtom1926 Fin15AnchoredAtom1941 Fin15AnchoredAtom1988
    Fin15AnchoredAtom1993 Fin15AnchoredAtom1994 Fin15AnchoredAtom2006 Fin15AnchoredAtom2007
    Fin15AnchoredAtom2022 Fin15AnchoredAtom2034 Fin15AnchoredAtom2035 Fin15AnchoredAtom2050
    Fin15AnchoredAtom2086 Fin15AnchoredAtom2373 Fin15AnchoredAtom2378 Fin15AnchoredAtom2379
    Fin15AnchoredAtom2391 Fin15AnchoredAtom2392 Fin15AnchoredAtom2407 Fin15AnchoredAtom2419
    Fin15AnchoredAtom2420 Fin15AnchoredAtom2435 Fin15AnchoredAtom2471 Fin15AnchoredAtom2623
    Fin15AnchoredAtom2624 Fin15AnchoredAtom2639 Fin15AnchoredAtom2675 Fin15AnchoredAtom2731
    Fin15AnchoredAtom3088 Fin15AnchoredAtom3093 Fin15AnchoredAtom3094 Fin15AnchoredAtom3106
    Fin15AnchoredAtom3107 Fin15AnchoredAtom3122 Fin15AnchoredAtom3134 Fin15AnchoredAtom3135
    Fin15AnchoredAtom3150 Fin15AnchoredAtom3186 Fin15AnchoredAtom3338 Fin15AnchoredAtom3339
    Fin15AnchoredAtom3354 Fin15AnchoredAtom3390 Fin15AnchoredAtom3446 Fin15AnchoredAtom4163
    Fin15AnchoredAtom4164 Fin15AnchoredAtom4179 Fin15AnchoredAtom4215 Fin15AnchoredAtom4271
    Fin15AnchoredAtom4607 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30886 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
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
      ¬Fin15AnchoredAtom3089 chi ∧
      ¬Fin15AnchoredAtom3090 chi ∧
      ¬Fin15AnchoredAtom3092 chi ∧
      ¬Fin15AnchoredAtom3108 chi ∧
      ¬Fin15AnchoredAtom3110 chi ∧
      ¬Fin15AnchoredAtom3114 chi ∧
      ¬Fin15AnchoredAtom3136 chi ∧
      ¬Fin15AnchoredAtom3138 chi ∧
      ¬Fin15AnchoredAtom3142 chi ∧
      ¬Fin15AnchoredAtom3188 chi ∧
      ¬Fin15AnchoredAtom3340 chi ∧
      ¬Fin15AnchoredAtom3342 chi ∧
      ¬Fin15AnchoredAtom3346 chi ∧
      ¬Fin15AnchoredAtom3392 chi ∧
      ¬Fin15AnchoredAtom3448 chi ∧
      ¬Fin15AnchoredAtom4165 chi ∧
      ¬Fin15AnchoredAtom4167 chi ∧
      ¬Fin15AnchoredAtom4171 chi ∧
      ¬Fin15AnchoredAtom4217 chi ∧
      ¬Fin15AnchoredAtom4273 chi ∧
      ¬Fin15AnchoredAtom4609 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 5, 6, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05739
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1897 Fin15AnchoredAtom1900 Fin15AnchoredAtom1901
    Fin15AnchoredAtom1903 Fin15AnchoredAtom1908 Fin15AnchoredAtom1909 Fin15AnchoredAtom1911
    Fin15AnchoredAtom1927 Fin15AnchoredAtom1929 Fin15AnchoredAtom1933 Fin15AnchoredAtom1989
    Fin15AnchoredAtom1990 Fin15AnchoredAtom1992 Fin15AnchoredAtom2008 Fin15AnchoredAtom2010
    Fin15AnchoredAtom2014 Fin15AnchoredAtom2036 Fin15AnchoredAtom2038 Fin15AnchoredAtom2042
    Fin15AnchoredAtom2088 Fin15AnchoredAtom2374 Fin15AnchoredAtom2375 Fin15AnchoredAtom2377
    Fin15AnchoredAtom2393 Fin15AnchoredAtom2395 Fin15AnchoredAtom2399 Fin15AnchoredAtom2421
    Fin15AnchoredAtom2423 Fin15AnchoredAtom2427 Fin15AnchoredAtom2473 Fin15AnchoredAtom2625
    Fin15AnchoredAtom2627 Fin15AnchoredAtom2631 Fin15AnchoredAtom2677 Fin15AnchoredAtom2733
    Fin15AnchoredAtom3089 Fin15AnchoredAtom3090 Fin15AnchoredAtom3092 Fin15AnchoredAtom3108
    Fin15AnchoredAtom3110 Fin15AnchoredAtom3114 Fin15AnchoredAtom3136 Fin15AnchoredAtom3138
    Fin15AnchoredAtom3142 Fin15AnchoredAtom3188 Fin15AnchoredAtom3340 Fin15AnchoredAtom3342
    Fin15AnchoredAtom3346 Fin15AnchoredAtom3392 Fin15AnchoredAtom3448 Fin15AnchoredAtom4165
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

theorem fin15Anchored_clause30887 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
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
      ¬Fin15AnchoredAtom3089 chi ∧
      ¬Fin15AnchoredAtom3090 chi ∧
      ¬Fin15AnchoredAtom3093 chi ∧
      ¬Fin15AnchoredAtom3108 chi ∧
      ¬Fin15AnchoredAtom3111 chi ∧
      ¬Fin15AnchoredAtom3115 chi ∧
      ¬Fin15AnchoredAtom3136 chi ∧
      ¬Fin15AnchoredAtom3139 chi ∧
      ¬Fin15AnchoredAtom3143 chi ∧
      ¬Fin15AnchoredAtom3189 chi ∧
      ¬Fin15AnchoredAtom3340 chi ∧
      ¬Fin15AnchoredAtom3343 chi ∧
      ¬Fin15AnchoredAtom3347 chi ∧
      ¬Fin15AnchoredAtom3393 chi ∧
      ¬Fin15AnchoredAtom3449 chi ∧
      ¬Fin15AnchoredAtom4165 chi ∧
      ¬Fin15AnchoredAtom4168 chi ∧
      ¬Fin15AnchoredAtom4172 chi ∧
      ¬Fin15AnchoredAtom4218 chi ∧
      ¬Fin15AnchoredAtom4274 chi ∧
      ¬Fin15AnchoredAtom4610 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 5, 6, 9, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09835
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1897 Fin15AnchoredAtom1900 Fin15AnchoredAtom1901
    Fin15AnchoredAtom1904 Fin15AnchoredAtom1908 Fin15AnchoredAtom1909 Fin15AnchoredAtom1912
    Fin15AnchoredAtom1927 Fin15AnchoredAtom1930 Fin15AnchoredAtom1934 Fin15AnchoredAtom1989
    Fin15AnchoredAtom1990 Fin15AnchoredAtom1993 Fin15AnchoredAtom2008 Fin15AnchoredAtom2011
    Fin15AnchoredAtom2015 Fin15AnchoredAtom2036 Fin15AnchoredAtom2039 Fin15AnchoredAtom2043
    Fin15AnchoredAtom2089 Fin15AnchoredAtom2374 Fin15AnchoredAtom2375 Fin15AnchoredAtom2378
    Fin15AnchoredAtom2393 Fin15AnchoredAtom2396 Fin15AnchoredAtom2400 Fin15AnchoredAtom2421
    Fin15AnchoredAtom2424 Fin15AnchoredAtom2428 Fin15AnchoredAtom2474 Fin15AnchoredAtom2625
    Fin15AnchoredAtom2628 Fin15AnchoredAtom2632 Fin15AnchoredAtom2678 Fin15AnchoredAtom2734
    Fin15AnchoredAtom3089 Fin15AnchoredAtom3090 Fin15AnchoredAtom3093 Fin15AnchoredAtom3108
    Fin15AnchoredAtom3111 Fin15AnchoredAtom3115 Fin15AnchoredAtom3136 Fin15AnchoredAtom3139
    Fin15AnchoredAtom3143 Fin15AnchoredAtom3189 Fin15AnchoredAtom3340 Fin15AnchoredAtom3343
    Fin15AnchoredAtom3347 Fin15AnchoredAtom3393 Fin15AnchoredAtom3449 Fin15AnchoredAtom4165
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

theorem fin15Anchored_clause30888 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom1935 chi ∧
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
      ¬Fin15AnchoredAtom3089 chi ∧
      ¬Fin15AnchoredAtom3090 chi ∧
      ¬Fin15AnchoredAtom3094 chi ∧
      ¬Fin15AnchoredAtom3108 chi ∧
      ¬Fin15AnchoredAtom3112 chi ∧
      ¬Fin15AnchoredAtom3116 chi ∧
      ¬Fin15AnchoredAtom3136 chi ∧
      ¬Fin15AnchoredAtom3140 chi ∧
      ¬Fin15AnchoredAtom3144 chi ∧
      ¬Fin15AnchoredAtom3190 chi ∧
      ¬Fin15AnchoredAtom3340 chi ∧
      ¬Fin15AnchoredAtom3344 chi ∧
      ¬Fin15AnchoredAtom3348 chi ∧
      ¬Fin15AnchoredAtom3394 chi ∧
      ¬Fin15AnchoredAtom3450 chi ∧
      ¬Fin15AnchoredAtom4165 chi ∧
      ¬Fin15AnchoredAtom4169 chi ∧
      ¬Fin15AnchoredAtom4173 chi ∧
      ¬Fin15AnchoredAtom4219 chi ∧
      ¬Fin15AnchoredAtom4275 chi ∧
      ¬Fin15AnchoredAtom4611 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 5, 6, 9, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask18027
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1897 Fin15AnchoredAtom1900 Fin15AnchoredAtom1901
    Fin15AnchoredAtom1905 Fin15AnchoredAtom1908 Fin15AnchoredAtom1909 Fin15AnchoredAtom1913
    Fin15AnchoredAtom1927 Fin15AnchoredAtom1931 Fin15AnchoredAtom1935 Fin15AnchoredAtom1989
    Fin15AnchoredAtom1990 Fin15AnchoredAtom1994 Fin15AnchoredAtom2008 Fin15AnchoredAtom2012
    Fin15AnchoredAtom2016 Fin15AnchoredAtom2036 Fin15AnchoredAtom2040 Fin15AnchoredAtom2044
    Fin15AnchoredAtom2090 Fin15AnchoredAtom2374 Fin15AnchoredAtom2375 Fin15AnchoredAtom2379
    Fin15AnchoredAtom2393 Fin15AnchoredAtom2397 Fin15AnchoredAtom2401 Fin15AnchoredAtom2421
    Fin15AnchoredAtom2425 Fin15AnchoredAtom2429 Fin15AnchoredAtom2475 Fin15AnchoredAtom2625
    Fin15AnchoredAtom2629 Fin15AnchoredAtom2633 Fin15AnchoredAtom2679 Fin15AnchoredAtom2735
    Fin15AnchoredAtom3089 Fin15AnchoredAtom3090 Fin15AnchoredAtom3094 Fin15AnchoredAtom3108
    Fin15AnchoredAtom3112 Fin15AnchoredAtom3116 Fin15AnchoredAtom3136 Fin15AnchoredAtom3140
    Fin15AnchoredAtom3144 Fin15AnchoredAtom3190 Fin15AnchoredAtom3340 Fin15AnchoredAtom3344
    Fin15AnchoredAtom3348 Fin15AnchoredAtom3394 Fin15AnchoredAtom3450 Fin15AnchoredAtom4165
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

theorem fin15Anchored_clause30889 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1939 chi ∧
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
      ¬Fin15AnchoredAtom3089 chi ∧
      ¬Fin15AnchoredAtom3092 chi ∧
      ¬Fin15AnchoredAtom3093 chi ∧
      ¬Fin15AnchoredAtom3110 chi ∧
      ¬Fin15AnchoredAtom3111 chi ∧
      ¬Fin15AnchoredAtom3120 chi ∧
      ¬Fin15AnchoredAtom3138 chi ∧
      ¬Fin15AnchoredAtom3139 chi ∧
      ¬Fin15AnchoredAtom3148 chi ∧
      ¬Fin15AnchoredAtom3194 chi ∧
      ¬Fin15AnchoredAtom3342 chi ∧
      ¬Fin15AnchoredAtom3343 chi ∧
      ¬Fin15AnchoredAtom3352 chi ∧
      ¬Fin15AnchoredAtom3398 chi ∧
      ¬Fin15AnchoredAtom3454 chi ∧
      ¬Fin15AnchoredAtom4167 chi ∧
      ¬Fin15AnchoredAtom4168 chi ∧
      ¬Fin15AnchoredAtom4177 chi ∧
      ¬Fin15AnchoredAtom4223 chi ∧
      ¬Fin15AnchoredAtom4279 chi ∧
      ¬Fin15AnchoredAtom4615 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 5, 6, 9, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask12907
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1897 Fin15AnchoredAtom1900 Fin15AnchoredAtom1903
    Fin15AnchoredAtom1904 Fin15AnchoredAtom1908 Fin15AnchoredAtom1911 Fin15AnchoredAtom1912
    Fin15AnchoredAtom1929 Fin15AnchoredAtom1930 Fin15AnchoredAtom1939 Fin15AnchoredAtom1989
    Fin15AnchoredAtom1992 Fin15AnchoredAtom1993 Fin15AnchoredAtom2010 Fin15AnchoredAtom2011
    Fin15AnchoredAtom2020 Fin15AnchoredAtom2038 Fin15AnchoredAtom2039 Fin15AnchoredAtom2048
    Fin15AnchoredAtom2094 Fin15AnchoredAtom2374 Fin15AnchoredAtom2377 Fin15AnchoredAtom2378
    Fin15AnchoredAtom2395 Fin15AnchoredAtom2396 Fin15AnchoredAtom2405 Fin15AnchoredAtom2423
    Fin15AnchoredAtom2424 Fin15AnchoredAtom2433 Fin15AnchoredAtom2479 Fin15AnchoredAtom2627
    Fin15AnchoredAtom2628 Fin15AnchoredAtom2637 Fin15AnchoredAtom2683 Fin15AnchoredAtom2739
    Fin15AnchoredAtom3089 Fin15AnchoredAtom3092 Fin15AnchoredAtom3093 Fin15AnchoredAtom3110
    Fin15AnchoredAtom3111 Fin15AnchoredAtom3120 Fin15AnchoredAtom3138 Fin15AnchoredAtom3139
    Fin15AnchoredAtom3148 Fin15AnchoredAtom3194 Fin15AnchoredAtom3342 Fin15AnchoredAtom3343
    Fin15AnchoredAtom3352 Fin15AnchoredAtom3398 Fin15AnchoredAtom3454 Fin15AnchoredAtom4167
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

theorem fin15Anchored_clause30890 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom1940 chi ∧
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
      ¬Fin15AnchoredAtom3089 chi ∧
      ¬Fin15AnchoredAtom3092 chi ∧
      ¬Fin15AnchoredAtom3094 chi ∧
      ¬Fin15AnchoredAtom3110 chi ∧
      ¬Fin15AnchoredAtom3112 chi ∧
      ¬Fin15AnchoredAtom3121 chi ∧
      ¬Fin15AnchoredAtom3138 chi ∧
      ¬Fin15AnchoredAtom3140 chi ∧
      ¬Fin15AnchoredAtom3149 chi ∧
      ¬Fin15AnchoredAtom3195 chi ∧
      ¬Fin15AnchoredAtom3342 chi ∧
      ¬Fin15AnchoredAtom3344 chi ∧
      ¬Fin15AnchoredAtom3353 chi ∧
      ¬Fin15AnchoredAtom3399 chi ∧
      ¬Fin15AnchoredAtom3455 chi ∧
      ¬Fin15AnchoredAtom4167 chi ∧
      ¬Fin15AnchoredAtom4169 chi ∧
      ¬Fin15AnchoredAtom4178 chi ∧
      ¬Fin15AnchoredAtom4224 chi ∧
      ¬Fin15AnchoredAtom4280 chi ∧
      ¬Fin15AnchoredAtom4616 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 5, 6, 9, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21099
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1897 Fin15AnchoredAtom1900 Fin15AnchoredAtom1903
    Fin15AnchoredAtom1905 Fin15AnchoredAtom1908 Fin15AnchoredAtom1911 Fin15AnchoredAtom1913
    Fin15AnchoredAtom1929 Fin15AnchoredAtom1931 Fin15AnchoredAtom1940 Fin15AnchoredAtom1989
    Fin15AnchoredAtom1992 Fin15AnchoredAtom1994 Fin15AnchoredAtom2010 Fin15AnchoredAtom2012
    Fin15AnchoredAtom2021 Fin15AnchoredAtom2038 Fin15AnchoredAtom2040 Fin15AnchoredAtom2049
    Fin15AnchoredAtom2095 Fin15AnchoredAtom2374 Fin15AnchoredAtom2377 Fin15AnchoredAtom2379
    Fin15AnchoredAtom2395 Fin15AnchoredAtom2397 Fin15AnchoredAtom2406 Fin15AnchoredAtom2423
    Fin15AnchoredAtom2425 Fin15AnchoredAtom2434 Fin15AnchoredAtom2480 Fin15AnchoredAtom2627
    Fin15AnchoredAtom2629 Fin15AnchoredAtom2638 Fin15AnchoredAtom2684 Fin15AnchoredAtom2740
    Fin15AnchoredAtom3089 Fin15AnchoredAtom3092 Fin15AnchoredAtom3094 Fin15AnchoredAtom3110
    Fin15AnchoredAtom3112 Fin15AnchoredAtom3121 Fin15AnchoredAtom3138 Fin15AnchoredAtom3140
    Fin15AnchoredAtom3149 Fin15AnchoredAtom3195 Fin15AnchoredAtom3342 Fin15AnchoredAtom3344
    Fin15AnchoredAtom3353 Fin15AnchoredAtom3399 Fin15AnchoredAtom3455 Fin15AnchoredAtom4167
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

theorem fin15Anchored_clause30891 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
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
      ¬Fin15AnchoredAtom3089 chi ∧
      ¬Fin15AnchoredAtom3093 chi ∧
      ¬Fin15AnchoredAtom3094 chi ∧
      ¬Fin15AnchoredAtom3111 chi ∧
      ¬Fin15AnchoredAtom3112 chi ∧
      ¬Fin15AnchoredAtom3122 chi ∧
      ¬Fin15AnchoredAtom3139 chi ∧
      ¬Fin15AnchoredAtom3140 chi ∧
      ¬Fin15AnchoredAtom3150 chi ∧
      ¬Fin15AnchoredAtom3196 chi ∧
      ¬Fin15AnchoredAtom3343 chi ∧
      ¬Fin15AnchoredAtom3344 chi ∧
      ¬Fin15AnchoredAtom3354 chi ∧
      ¬Fin15AnchoredAtom3400 chi ∧
      ¬Fin15AnchoredAtom3456 chi ∧
      ¬Fin15AnchoredAtom4168 chi ∧
      ¬Fin15AnchoredAtom4169 chi ∧
      ¬Fin15AnchoredAtom4179 chi ∧
      ¬Fin15AnchoredAtom4225 chi ∧
      ¬Fin15AnchoredAtom4281 chi ∧
      ¬Fin15AnchoredAtom4617 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 5, 6, 9, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25195
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1897 Fin15AnchoredAtom1900 Fin15AnchoredAtom1904
    Fin15AnchoredAtom1905 Fin15AnchoredAtom1908 Fin15AnchoredAtom1912 Fin15AnchoredAtom1913
    Fin15AnchoredAtom1930 Fin15AnchoredAtom1931 Fin15AnchoredAtom1941 Fin15AnchoredAtom1989
    Fin15AnchoredAtom1993 Fin15AnchoredAtom1994 Fin15AnchoredAtom2011 Fin15AnchoredAtom2012
    Fin15AnchoredAtom2022 Fin15AnchoredAtom2039 Fin15AnchoredAtom2040 Fin15AnchoredAtom2050
    Fin15AnchoredAtom2096 Fin15AnchoredAtom2374 Fin15AnchoredAtom2378 Fin15AnchoredAtom2379
    Fin15AnchoredAtom2396 Fin15AnchoredAtom2397 Fin15AnchoredAtom2407 Fin15AnchoredAtom2424
    Fin15AnchoredAtom2425 Fin15AnchoredAtom2435 Fin15AnchoredAtom2481 Fin15AnchoredAtom2628
    Fin15AnchoredAtom2629 Fin15AnchoredAtom2639 Fin15AnchoredAtom2685 Fin15AnchoredAtom2741
    Fin15AnchoredAtom3089 Fin15AnchoredAtom3093 Fin15AnchoredAtom3094 Fin15AnchoredAtom3111
    Fin15AnchoredAtom3112 Fin15AnchoredAtom3122 Fin15AnchoredAtom3139 Fin15AnchoredAtom3140
    Fin15AnchoredAtom3150 Fin15AnchoredAtom3196 Fin15AnchoredAtom3343 Fin15AnchoredAtom3344
    Fin15AnchoredAtom3354 Fin15AnchoredAtom3400 Fin15AnchoredAtom3456 Fin15AnchoredAtom4168
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

theorem fin15Anchored_clause30892 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom1939 chi ∧
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
      ¬Fin15AnchoredAtom3090 chi ∧
      ¬Fin15AnchoredAtom3092 chi ∧
      ¬Fin15AnchoredAtom3093 chi ∧
      ¬Fin15AnchoredAtom3114 chi ∧
      ¬Fin15AnchoredAtom3115 chi ∧
      ¬Fin15AnchoredAtom3120 chi ∧
      ¬Fin15AnchoredAtom3142 chi ∧
      ¬Fin15AnchoredAtom3143 chi ∧
      ¬Fin15AnchoredAtom3148 chi ∧
      ¬Fin15AnchoredAtom3200 chi ∧
      ¬Fin15AnchoredAtom3346 chi ∧
      ¬Fin15AnchoredAtom3347 chi ∧
      ¬Fin15AnchoredAtom3352 chi ∧
      ¬Fin15AnchoredAtom3404 chi ∧
      ¬Fin15AnchoredAtom3460 chi ∧
      ¬Fin15AnchoredAtom4171 chi ∧
      ¬Fin15AnchoredAtom4172 chi ∧
      ¬Fin15AnchoredAtom4177 chi ∧
      ¬Fin15AnchoredAtom4229 chi ∧
      ¬Fin15AnchoredAtom4285 chi ∧
      ¬Fin15AnchoredAtom4621 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 5, 6, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13419
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1897 Fin15AnchoredAtom1901 Fin15AnchoredAtom1903
    Fin15AnchoredAtom1904 Fin15AnchoredAtom1909 Fin15AnchoredAtom1911 Fin15AnchoredAtom1912
    Fin15AnchoredAtom1933 Fin15AnchoredAtom1934 Fin15AnchoredAtom1939 Fin15AnchoredAtom1990
    Fin15AnchoredAtom1992 Fin15AnchoredAtom1993 Fin15AnchoredAtom2014 Fin15AnchoredAtom2015
    Fin15AnchoredAtom2020 Fin15AnchoredAtom2042 Fin15AnchoredAtom2043 Fin15AnchoredAtom2048
    Fin15AnchoredAtom2100 Fin15AnchoredAtom2375 Fin15AnchoredAtom2377 Fin15AnchoredAtom2378
    Fin15AnchoredAtom2399 Fin15AnchoredAtom2400 Fin15AnchoredAtom2405 Fin15AnchoredAtom2427
    Fin15AnchoredAtom2428 Fin15AnchoredAtom2433 Fin15AnchoredAtom2485 Fin15AnchoredAtom2631
    Fin15AnchoredAtom2632 Fin15AnchoredAtom2637 Fin15AnchoredAtom2689 Fin15AnchoredAtom2745
    Fin15AnchoredAtom3090 Fin15AnchoredAtom3092 Fin15AnchoredAtom3093 Fin15AnchoredAtom3114
    Fin15AnchoredAtom3115 Fin15AnchoredAtom3120 Fin15AnchoredAtom3142 Fin15AnchoredAtom3143
    Fin15AnchoredAtom3148 Fin15AnchoredAtom3200 Fin15AnchoredAtom3346 Fin15AnchoredAtom3347
    Fin15AnchoredAtom3352 Fin15AnchoredAtom3404 Fin15AnchoredAtom3460 Fin15AnchoredAtom4171
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

theorem fin15Anchored_clause30893 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom1935 chi ∧
      ¬Fin15AnchoredAtom1940 chi ∧
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
      ¬Fin15AnchoredAtom3090 chi ∧
      ¬Fin15AnchoredAtom3092 chi ∧
      ¬Fin15AnchoredAtom3094 chi ∧
      ¬Fin15AnchoredAtom3114 chi ∧
      ¬Fin15AnchoredAtom3116 chi ∧
      ¬Fin15AnchoredAtom3121 chi ∧
      ¬Fin15AnchoredAtom3142 chi ∧
      ¬Fin15AnchoredAtom3144 chi ∧
      ¬Fin15AnchoredAtom3149 chi ∧
      ¬Fin15AnchoredAtom3201 chi ∧
      ¬Fin15AnchoredAtom3346 chi ∧
      ¬Fin15AnchoredAtom3348 chi ∧
      ¬Fin15AnchoredAtom3353 chi ∧
      ¬Fin15AnchoredAtom3405 chi ∧
      ¬Fin15AnchoredAtom3461 chi ∧
      ¬Fin15AnchoredAtom4171 chi ∧
      ¬Fin15AnchoredAtom4173 chi ∧
      ¬Fin15AnchoredAtom4178 chi ∧
      ¬Fin15AnchoredAtom4230 chi ∧
      ¬Fin15AnchoredAtom4286 chi ∧
      ¬Fin15AnchoredAtom4622 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 5, 6, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21611
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1897 Fin15AnchoredAtom1901 Fin15AnchoredAtom1903
    Fin15AnchoredAtom1905 Fin15AnchoredAtom1909 Fin15AnchoredAtom1911 Fin15AnchoredAtom1913
    Fin15AnchoredAtom1933 Fin15AnchoredAtom1935 Fin15AnchoredAtom1940 Fin15AnchoredAtom1990
    Fin15AnchoredAtom1992 Fin15AnchoredAtom1994 Fin15AnchoredAtom2014 Fin15AnchoredAtom2016
    Fin15AnchoredAtom2021 Fin15AnchoredAtom2042 Fin15AnchoredAtom2044 Fin15AnchoredAtom2049
    Fin15AnchoredAtom2101 Fin15AnchoredAtom2375 Fin15AnchoredAtom2377 Fin15AnchoredAtom2379
    Fin15AnchoredAtom2399 Fin15AnchoredAtom2401 Fin15AnchoredAtom2406 Fin15AnchoredAtom2427
    Fin15AnchoredAtom2429 Fin15AnchoredAtom2434 Fin15AnchoredAtom2486 Fin15AnchoredAtom2631
    Fin15AnchoredAtom2633 Fin15AnchoredAtom2638 Fin15AnchoredAtom2690 Fin15AnchoredAtom2746
    Fin15AnchoredAtom3090 Fin15AnchoredAtom3092 Fin15AnchoredAtom3094 Fin15AnchoredAtom3114
    Fin15AnchoredAtom3116 Fin15AnchoredAtom3121 Fin15AnchoredAtom3142 Fin15AnchoredAtom3144
    Fin15AnchoredAtom3149 Fin15AnchoredAtom3201 Fin15AnchoredAtom3346 Fin15AnchoredAtom3348
    Fin15AnchoredAtom3353 Fin15AnchoredAtom3405 Fin15AnchoredAtom3461 Fin15AnchoredAtom4171
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

theorem fin15Anchored_clause30894 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom1935 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
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
      ¬Fin15AnchoredAtom3090 chi ∧
      ¬Fin15AnchoredAtom3093 chi ∧
      ¬Fin15AnchoredAtom3094 chi ∧
      ¬Fin15AnchoredAtom3115 chi ∧
      ¬Fin15AnchoredAtom3116 chi ∧
      ¬Fin15AnchoredAtom3122 chi ∧
      ¬Fin15AnchoredAtom3143 chi ∧
      ¬Fin15AnchoredAtom3144 chi ∧
      ¬Fin15AnchoredAtom3150 chi ∧
      ¬Fin15AnchoredAtom3202 chi ∧
      ¬Fin15AnchoredAtom3347 chi ∧
      ¬Fin15AnchoredAtom3348 chi ∧
      ¬Fin15AnchoredAtom3354 chi ∧
      ¬Fin15AnchoredAtom3406 chi ∧
      ¬Fin15AnchoredAtom3462 chi ∧
      ¬Fin15AnchoredAtom4172 chi ∧
      ¬Fin15AnchoredAtom4173 chi ∧
      ¬Fin15AnchoredAtom4179 chi ∧
      ¬Fin15AnchoredAtom4231 chi ∧
      ¬Fin15AnchoredAtom4287 chi ∧
      ¬Fin15AnchoredAtom4623 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 5, 6, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25707
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1897 Fin15AnchoredAtom1901 Fin15AnchoredAtom1904
    Fin15AnchoredAtom1905 Fin15AnchoredAtom1909 Fin15AnchoredAtom1912 Fin15AnchoredAtom1913
    Fin15AnchoredAtom1934 Fin15AnchoredAtom1935 Fin15AnchoredAtom1941 Fin15AnchoredAtom1990
    Fin15AnchoredAtom1993 Fin15AnchoredAtom1994 Fin15AnchoredAtom2015 Fin15AnchoredAtom2016
    Fin15AnchoredAtom2022 Fin15AnchoredAtom2043 Fin15AnchoredAtom2044 Fin15AnchoredAtom2050
    Fin15AnchoredAtom2102 Fin15AnchoredAtom2375 Fin15AnchoredAtom2378 Fin15AnchoredAtom2379
    Fin15AnchoredAtom2400 Fin15AnchoredAtom2401 Fin15AnchoredAtom2407 Fin15AnchoredAtom2428
    Fin15AnchoredAtom2429 Fin15AnchoredAtom2435 Fin15AnchoredAtom2487 Fin15AnchoredAtom2632
    Fin15AnchoredAtom2633 Fin15AnchoredAtom2639 Fin15AnchoredAtom2691 Fin15AnchoredAtom2747
    Fin15AnchoredAtom3090 Fin15AnchoredAtom3093 Fin15AnchoredAtom3094 Fin15AnchoredAtom3115
    Fin15AnchoredAtom3116 Fin15AnchoredAtom3122 Fin15AnchoredAtom3143 Fin15AnchoredAtom3144
    Fin15AnchoredAtom3150 Fin15AnchoredAtom3202 Fin15AnchoredAtom3347 Fin15AnchoredAtom3348
    Fin15AnchoredAtom3354 Fin15AnchoredAtom3406 Fin15AnchoredAtom3462 Fin15AnchoredAtom4172
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

theorem fin15Anchored_clause30895 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1939 chi ∧
      ¬Fin15AnchoredAtom1940 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
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
      ¬Fin15AnchoredAtom3092 chi ∧
      ¬Fin15AnchoredAtom3093 chi ∧
      ¬Fin15AnchoredAtom3094 chi ∧
      ¬Fin15AnchoredAtom3120 chi ∧
      ¬Fin15AnchoredAtom3121 chi ∧
      ¬Fin15AnchoredAtom3122 chi ∧
      ¬Fin15AnchoredAtom3148 chi ∧
      ¬Fin15AnchoredAtom3149 chi ∧
      ¬Fin15AnchoredAtom3150 chi ∧
      ¬Fin15AnchoredAtom3206 chi ∧
      ¬Fin15AnchoredAtom3352 chi ∧
      ¬Fin15AnchoredAtom3353 chi ∧
      ¬Fin15AnchoredAtom3354 chi ∧
      ¬Fin15AnchoredAtom3410 chi ∧
      ¬Fin15AnchoredAtom3466 chi ∧
      ¬Fin15AnchoredAtom4177 chi ∧
      ¬Fin15AnchoredAtom4178 chi ∧
      ¬Fin15AnchoredAtom4179 chi ∧
      ¬Fin15AnchoredAtom4235 chi ∧
      ¬Fin15AnchoredAtom4291 chi ∧
      ¬Fin15AnchoredAtom4627 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 5, 6, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask28779
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1897 Fin15AnchoredAtom1903 Fin15AnchoredAtom1904
    Fin15AnchoredAtom1905 Fin15AnchoredAtom1911 Fin15AnchoredAtom1912 Fin15AnchoredAtom1913
    Fin15AnchoredAtom1939 Fin15AnchoredAtom1940 Fin15AnchoredAtom1941 Fin15AnchoredAtom1992
    Fin15AnchoredAtom1993 Fin15AnchoredAtom1994 Fin15AnchoredAtom2020 Fin15AnchoredAtom2021
    Fin15AnchoredAtom2022 Fin15AnchoredAtom2048 Fin15AnchoredAtom2049 Fin15AnchoredAtom2050
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2377 Fin15AnchoredAtom2378 Fin15AnchoredAtom2379
    Fin15AnchoredAtom2405 Fin15AnchoredAtom2406 Fin15AnchoredAtom2407 Fin15AnchoredAtom2433
    Fin15AnchoredAtom2434 Fin15AnchoredAtom2435 Fin15AnchoredAtom2491 Fin15AnchoredAtom2637
    Fin15AnchoredAtom2638 Fin15AnchoredAtom2639 Fin15AnchoredAtom2695 Fin15AnchoredAtom2751
    Fin15AnchoredAtom3092 Fin15AnchoredAtom3093 Fin15AnchoredAtom3094 Fin15AnchoredAtom3120
    Fin15AnchoredAtom3121 Fin15AnchoredAtom3122 Fin15AnchoredAtom3148 Fin15AnchoredAtom3149
    Fin15AnchoredAtom3150 Fin15AnchoredAtom3206 Fin15AnchoredAtom3352 Fin15AnchoredAtom3353
    Fin15AnchoredAtom3354 Fin15AnchoredAtom3410 Fin15AnchoredAtom3466 Fin15AnchoredAtom4177
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

theorem fin15Anchored_clause30896 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1899 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1914 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1921 chi ∧
      ¬Fin15AnchoredAtom1922 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1995 chi ∧
      ¬Fin15AnchoredAtom1996 chi ∧
      ¬Fin15AnchoredAtom1997 chi ∧
      ¬Fin15AnchoredAtom2002 chi ∧
      ¬Fin15AnchoredAtom2003 chi ∧
      ¬Fin15AnchoredAtom2008 chi ∧
      ¬Fin15AnchoredAtom2051 chi ∧
      ¬Fin15AnchoredAtom2052 chi ∧
      ¬Fin15AnchoredAtom2057 chi ∧
      ¬Fin15AnchoredAtom2072 chi ∧
      ¬Fin15AnchoredAtom2380 chi ∧
      ¬Fin15AnchoredAtom2381 chi ∧
      ¬Fin15AnchoredAtom2382 chi ∧
      ¬Fin15AnchoredAtom2387 chi ∧
      ¬Fin15AnchoredAtom2388 chi ∧
      ¬Fin15AnchoredAtom2393 chi ∧
      ¬Fin15AnchoredAtom2436 chi ∧
      ¬Fin15AnchoredAtom2437 chi ∧
      ¬Fin15AnchoredAtom2442 chi ∧
      ¬Fin15AnchoredAtom2457 chi ∧
      ¬Fin15AnchoredAtom2640 chi ∧
      ¬Fin15AnchoredAtom2641 chi ∧
      ¬Fin15AnchoredAtom2646 chi ∧
      ¬Fin15AnchoredAtom2661 chi ∧
      ¬Fin15AnchoredAtom2752 chi ∧
      ¬Fin15AnchoredAtom3095 chi ∧
      ¬Fin15AnchoredAtom3096 chi ∧
      ¬Fin15AnchoredAtom3097 chi ∧
      ¬Fin15AnchoredAtom3102 chi ∧
      ¬Fin15AnchoredAtom3103 chi ∧
      ¬Fin15AnchoredAtom3108 chi ∧
      ¬Fin15AnchoredAtom3151 chi ∧
      ¬Fin15AnchoredAtom3152 chi ∧
      ¬Fin15AnchoredAtom3157 chi ∧
      ¬Fin15AnchoredAtom3172 chi ∧
      ¬Fin15AnchoredAtom3355 chi ∧
      ¬Fin15AnchoredAtom3356 chi ∧
      ¬Fin15AnchoredAtom3361 chi ∧
      ¬Fin15AnchoredAtom3376 chi ∧
      ¬Fin15AnchoredAtom3467 chi ∧
      ¬Fin15AnchoredAtom4180 chi ∧
      ¬Fin15AnchoredAtom4181 chi ∧
      ¬Fin15AnchoredAtom4186 chi ∧
      ¬Fin15AnchoredAtom4201 chi ∧
      ¬Fin15AnchoredAtom4292 chi ∧
      ¬Fin15AnchoredAtom4628 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 5, 7, 8, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask01963
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1898 Fin15AnchoredAtom1899 Fin15AnchoredAtom1900
    Fin15AnchoredAtom1901 Fin15AnchoredAtom1914 Fin15AnchoredAtom1915 Fin15AnchoredAtom1916
    Fin15AnchoredAtom1921 Fin15AnchoredAtom1922 Fin15AnchoredAtom1927 Fin15AnchoredAtom1995
    Fin15AnchoredAtom1996 Fin15AnchoredAtom1997 Fin15AnchoredAtom2002 Fin15AnchoredAtom2003
    Fin15AnchoredAtom2008 Fin15AnchoredAtom2051 Fin15AnchoredAtom2052 Fin15AnchoredAtom2057
    Fin15AnchoredAtom2072 Fin15AnchoredAtom2380 Fin15AnchoredAtom2381 Fin15AnchoredAtom2382
    Fin15AnchoredAtom2387 Fin15AnchoredAtom2388 Fin15AnchoredAtom2393 Fin15AnchoredAtom2436
    Fin15AnchoredAtom2437 Fin15AnchoredAtom2442 Fin15AnchoredAtom2457 Fin15AnchoredAtom2640
    Fin15AnchoredAtom2641 Fin15AnchoredAtom2646 Fin15AnchoredAtom2661 Fin15AnchoredAtom2752
    Fin15AnchoredAtom3095 Fin15AnchoredAtom3096 Fin15AnchoredAtom3097 Fin15AnchoredAtom3102
    Fin15AnchoredAtom3103 Fin15AnchoredAtom3108 Fin15AnchoredAtom3151 Fin15AnchoredAtom3152
    Fin15AnchoredAtom3157 Fin15AnchoredAtom3172 Fin15AnchoredAtom3355 Fin15AnchoredAtom3356
    Fin15AnchoredAtom3361 Fin15AnchoredAtom3376 Fin15AnchoredAtom3467 Fin15AnchoredAtom4180
    Fin15AnchoredAtom4181 Fin15AnchoredAtom4186 Fin15AnchoredAtom4201 Fin15AnchoredAtom4292
    Fin15AnchoredAtom4628 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30897 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1899 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1914 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1921 chi ∧
      ¬Fin15AnchoredAtom1924 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom1995 chi ∧
      ¬Fin15AnchoredAtom1996 chi ∧
      ¬Fin15AnchoredAtom1999 chi ∧
      ¬Fin15AnchoredAtom2002 chi ∧
      ¬Fin15AnchoredAtom2005 chi ∧
      ¬Fin15AnchoredAtom2010 chi ∧
      ¬Fin15AnchoredAtom2051 chi ∧
      ¬Fin15AnchoredAtom2054 chi ∧
      ¬Fin15AnchoredAtom2059 chi ∧
      ¬Fin15AnchoredAtom2074 chi ∧
      ¬Fin15AnchoredAtom2380 chi ∧
      ¬Fin15AnchoredAtom2381 chi ∧
      ¬Fin15AnchoredAtom2384 chi ∧
      ¬Fin15AnchoredAtom2387 chi ∧
      ¬Fin15AnchoredAtom2390 chi ∧
      ¬Fin15AnchoredAtom2395 chi ∧
      ¬Fin15AnchoredAtom2436 chi ∧
      ¬Fin15AnchoredAtom2439 chi ∧
      ¬Fin15AnchoredAtom2444 chi ∧
      ¬Fin15AnchoredAtom2459 chi ∧
      ¬Fin15AnchoredAtom2640 chi ∧
      ¬Fin15AnchoredAtom2643 chi ∧
      ¬Fin15AnchoredAtom2648 chi ∧
      ¬Fin15AnchoredAtom2663 chi ∧
      ¬Fin15AnchoredAtom2754 chi ∧
      ¬Fin15AnchoredAtom3095 chi ∧
      ¬Fin15AnchoredAtom3096 chi ∧
      ¬Fin15AnchoredAtom3099 chi ∧
      ¬Fin15AnchoredAtom3102 chi ∧
      ¬Fin15AnchoredAtom3105 chi ∧
      ¬Fin15AnchoredAtom3110 chi ∧
      ¬Fin15AnchoredAtom3151 chi ∧
      ¬Fin15AnchoredAtom3154 chi ∧
      ¬Fin15AnchoredAtom3159 chi ∧
      ¬Fin15AnchoredAtom3174 chi ∧
      ¬Fin15AnchoredAtom3355 chi ∧
      ¬Fin15AnchoredAtom3358 chi ∧
      ¬Fin15AnchoredAtom3363 chi ∧
      ¬Fin15AnchoredAtom3378 chi ∧
      ¬Fin15AnchoredAtom3469 chi ∧
      ¬Fin15AnchoredAtom4180 chi ∧
      ¬Fin15AnchoredAtom4183 chi ∧
      ¬Fin15AnchoredAtom4188 chi ∧
      ¬Fin15AnchoredAtom4203 chi ∧
      ¬Fin15AnchoredAtom4294 chi ∧
      ¬Fin15AnchoredAtom4630 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 5, 7, 8, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05035
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1898 Fin15AnchoredAtom1899 Fin15AnchoredAtom1900
    Fin15AnchoredAtom1903 Fin15AnchoredAtom1914 Fin15AnchoredAtom1915 Fin15AnchoredAtom1918
    Fin15AnchoredAtom1921 Fin15AnchoredAtom1924 Fin15AnchoredAtom1929 Fin15AnchoredAtom1995
    Fin15AnchoredAtom1996 Fin15AnchoredAtom1999 Fin15AnchoredAtom2002 Fin15AnchoredAtom2005
    Fin15AnchoredAtom2010 Fin15AnchoredAtom2051 Fin15AnchoredAtom2054 Fin15AnchoredAtom2059
    Fin15AnchoredAtom2074 Fin15AnchoredAtom2380 Fin15AnchoredAtom2381 Fin15AnchoredAtom2384
    Fin15AnchoredAtom2387 Fin15AnchoredAtom2390 Fin15AnchoredAtom2395 Fin15AnchoredAtom2436
    Fin15AnchoredAtom2439 Fin15AnchoredAtom2444 Fin15AnchoredAtom2459 Fin15AnchoredAtom2640
    Fin15AnchoredAtom2643 Fin15AnchoredAtom2648 Fin15AnchoredAtom2663 Fin15AnchoredAtom2754
    Fin15AnchoredAtom3095 Fin15AnchoredAtom3096 Fin15AnchoredAtom3099 Fin15AnchoredAtom3102
    Fin15AnchoredAtom3105 Fin15AnchoredAtom3110 Fin15AnchoredAtom3151 Fin15AnchoredAtom3154
    Fin15AnchoredAtom3159 Fin15AnchoredAtom3174 Fin15AnchoredAtom3355 Fin15AnchoredAtom3358
    Fin15AnchoredAtom3363 Fin15AnchoredAtom3378 Fin15AnchoredAtom3469 Fin15AnchoredAtom4180
    Fin15AnchoredAtom4183 Fin15AnchoredAtom4188 Fin15AnchoredAtom4203 Fin15AnchoredAtom4294
    Fin15AnchoredAtom4630 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30898 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1899 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1914 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1921 chi ∧
      ¬Fin15AnchoredAtom1925 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1995 chi ∧
      ¬Fin15AnchoredAtom1996 chi ∧
      ¬Fin15AnchoredAtom2000 chi ∧
      ¬Fin15AnchoredAtom2002 chi ∧
      ¬Fin15AnchoredAtom2006 chi ∧
      ¬Fin15AnchoredAtom2011 chi ∧
      ¬Fin15AnchoredAtom2051 chi ∧
      ¬Fin15AnchoredAtom2055 chi ∧
      ¬Fin15AnchoredAtom2060 chi ∧
      ¬Fin15AnchoredAtom2075 chi ∧
      ¬Fin15AnchoredAtom2380 chi ∧
      ¬Fin15AnchoredAtom2381 chi ∧
      ¬Fin15AnchoredAtom2385 chi ∧
      ¬Fin15AnchoredAtom2387 chi ∧
      ¬Fin15AnchoredAtom2391 chi ∧
      ¬Fin15AnchoredAtom2396 chi ∧
      ¬Fin15AnchoredAtom2436 chi ∧
      ¬Fin15AnchoredAtom2440 chi ∧
      ¬Fin15AnchoredAtom2445 chi ∧
      ¬Fin15AnchoredAtom2460 chi ∧
      ¬Fin15AnchoredAtom2640 chi ∧
      ¬Fin15AnchoredAtom2644 chi ∧
      ¬Fin15AnchoredAtom2649 chi ∧
      ¬Fin15AnchoredAtom2664 chi ∧
      ¬Fin15AnchoredAtom2755 chi ∧
      ¬Fin15AnchoredAtom3095 chi ∧
      ¬Fin15AnchoredAtom3096 chi ∧
      ¬Fin15AnchoredAtom3100 chi ∧
      ¬Fin15AnchoredAtom3102 chi ∧
      ¬Fin15AnchoredAtom3106 chi ∧
      ¬Fin15AnchoredAtom3111 chi ∧
      ¬Fin15AnchoredAtom3151 chi ∧
      ¬Fin15AnchoredAtom3155 chi ∧
      ¬Fin15AnchoredAtom3160 chi ∧
      ¬Fin15AnchoredAtom3175 chi ∧
      ¬Fin15AnchoredAtom3355 chi ∧
      ¬Fin15AnchoredAtom3359 chi ∧
      ¬Fin15AnchoredAtom3364 chi ∧
      ¬Fin15AnchoredAtom3379 chi ∧
      ¬Fin15AnchoredAtom3470 chi ∧
      ¬Fin15AnchoredAtom4180 chi ∧
      ¬Fin15AnchoredAtom4184 chi ∧
      ¬Fin15AnchoredAtom4189 chi ∧
      ¬Fin15AnchoredAtom4204 chi ∧
      ¬Fin15AnchoredAtom4295 chi ∧
      ¬Fin15AnchoredAtom4631 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 5, 7, 8, 9, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09131
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1898 Fin15AnchoredAtom1899 Fin15AnchoredAtom1900
    Fin15AnchoredAtom1904 Fin15AnchoredAtom1914 Fin15AnchoredAtom1915 Fin15AnchoredAtom1919
    Fin15AnchoredAtom1921 Fin15AnchoredAtom1925 Fin15AnchoredAtom1930 Fin15AnchoredAtom1995
    Fin15AnchoredAtom1996 Fin15AnchoredAtom2000 Fin15AnchoredAtom2002 Fin15AnchoredAtom2006
    Fin15AnchoredAtom2011 Fin15AnchoredAtom2051 Fin15AnchoredAtom2055 Fin15AnchoredAtom2060
    Fin15AnchoredAtom2075 Fin15AnchoredAtom2380 Fin15AnchoredAtom2381 Fin15AnchoredAtom2385
    Fin15AnchoredAtom2387 Fin15AnchoredAtom2391 Fin15AnchoredAtom2396 Fin15AnchoredAtom2436
    Fin15AnchoredAtom2440 Fin15AnchoredAtom2445 Fin15AnchoredAtom2460 Fin15AnchoredAtom2640
    Fin15AnchoredAtom2644 Fin15AnchoredAtom2649 Fin15AnchoredAtom2664 Fin15AnchoredAtom2755
    Fin15AnchoredAtom3095 Fin15AnchoredAtom3096 Fin15AnchoredAtom3100 Fin15AnchoredAtom3102
    Fin15AnchoredAtom3106 Fin15AnchoredAtom3111 Fin15AnchoredAtom3151 Fin15AnchoredAtom3155
    Fin15AnchoredAtom3160 Fin15AnchoredAtom3175 Fin15AnchoredAtom3355 Fin15AnchoredAtom3359
    Fin15AnchoredAtom3364 Fin15AnchoredAtom3379 Fin15AnchoredAtom3470 Fin15AnchoredAtom4180
    Fin15AnchoredAtom4184 Fin15AnchoredAtom4189 Fin15AnchoredAtom4204 Fin15AnchoredAtom4295
    Fin15AnchoredAtom4631 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30899 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1899 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1914 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1921 chi ∧
      ¬Fin15AnchoredAtom1926 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom1995 chi ∧
      ¬Fin15AnchoredAtom1996 chi ∧
      ¬Fin15AnchoredAtom2001 chi ∧
      ¬Fin15AnchoredAtom2002 chi ∧
      ¬Fin15AnchoredAtom2007 chi ∧
      ¬Fin15AnchoredAtom2012 chi ∧
      ¬Fin15AnchoredAtom2051 chi ∧
      ¬Fin15AnchoredAtom2056 chi ∧
      ¬Fin15AnchoredAtom2061 chi ∧
      ¬Fin15AnchoredAtom2076 chi ∧
      ¬Fin15AnchoredAtom2380 chi ∧
      ¬Fin15AnchoredAtom2381 chi ∧
      ¬Fin15AnchoredAtom2386 chi ∧
      ¬Fin15AnchoredAtom2387 chi ∧
      ¬Fin15AnchoredAtom2392 chi ∧
      ¬Fin15AnchoredAtom2397 chi ∧
      ¬Fin15AnchoredAtom2436 chi ∧
      ¬Fin15AnchoredAtom2441 chi ∧
      ¬Fin15AnchoredAtom2446 chi ∧
      ¬Fin15AnchoredAtom2461 chi ∧
      ¬Fin15AnchoredAtom2640 chi ∧
      ¬Fin15AnchoredAtom2645 chi ∧
      ¬Fin15AnchoredAtom2650 chi ∧
      ¬Fin15AnchoredAtom2665 chi ∧
      ¬Fin15AnchoredAtom2756 chi ∧
      ¬Fin15AnchoredAtom3095 chi ∧
      ¬Fin15AnchoredAtom3096 chi ∧
      ¬Fin15AnchoredAtom3101 chi ∧
      ¬Fin15AnchoredAtom3102 chi ∧
      ¬Fin15AnchoredAtom3107 chi ∧
      ¬Fin15AnchoredAtom3112 chi ∧
      ¬Fin15AnchoredAtom3151 chi ∧
      ¬Fin15AnchoredAtom3156 chi ∧
      ¬Fin15AnchoredAtom3161 chi ∧
      ¬Fin15AnchoredAtom3176 chi ∧
      ¬Fin15AnchoredAtom3355 chi ∧
      ¬Fin15AnchoredAtom3360 chi ∧
      ¬Fin15AnchoredAtom3365 chi ∧
      ¬Fin15AnchoredAtom3380 chi ∧
      ¬Fin15AnchoredAtom3471 chi ∧
      ¬Fin15AnchoredAtom4180 chi ∧
      ¬Fin15AnchoredAtom4185 chi ∧
      ¬Fin15AnchoredAtom4190 chi ∧
      ¬Fin15AnchoredAtom4205 chi ∧
      ¬Fin15AnchoredAtom4296 chi ∧
      ¬Fin15AnchoredAtom4632 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 5, 7, 8, 9, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17323
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1898 Fin15AnchoredAtom1899 Fin15AnchoredAtom1900
    Fin15AnchoredAtom1905 Fin15AnchoredAtom1914 Fin15AnchoredAtom1915 Fin15AnchoredAtom1920
    Fin15AnchoredAtom1921 Fin15AnchoredAtom1926 Fin15AnchoredAtom1931 Fin15AnchoredAtom1995
    Fin15AnchoredAtom1996 Fin15AnchoredAtom2001 Fin15AnchoredAtom2002 Fin15AnchoredAtom2007
    Fin15AnchoredAtom2012 Fin15AnchoredAtom2051 Fin15AnchoredAtom2056 Fin15AnchoredAtom2061
    Fin15AnchoredAtom2076 Fin15AnchoredAtom2380 Fin15AnchoredAtom2381 Fin15AnchoredAtom2386
    Fin15AnchoredAtom2387 Fin15AnchoredAtom2392 Fin15AnchoredAtom2397 Fin15AnchoredAtom2436
    Fin15AnchoredAtom2441 Fin15AnchoredAtom2446 Fin15AnchoredAtom2461 Fin15AnchoredAtom2640
    Fin15AnchoredAtom2645 Fin15AnchoredAtom2650 Fin15AnchoredAtom2665 Fin15AnchoredAtom2756
    Fin15AnchoredAtom3095 Fin15AnchoredAtom3096 Fin15AnchoredAtom3101 Fin15AnchoredAtom3102
    Fin15AnchoredAtom3107 Fin15AnchoredAtom3112 Fin15AnchoredAtom3151 Fin15AnchoredAtom3156
    Fin15AnchoredAtom3161 Fin15AnchoredAtom3176 Fin15AnchoredAtom3355 Fin15AnchoredAtom3360
    Fin15AnchoredAtom3365 Fin15AnchoredAtom3380 Fin15AnchoredAtom3471 Fin15AnchoredAtom4180
    Fin15AnchoredAtom4185 Fin15AnchoredAtom4190 Fin15AnchoredAtom4205 Fin15AnchoredAtom4296
    Fin15AnchoredAtom4632 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30900 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1899 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1914 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1922 chi ∧
      ¬Fin15AnchoredAtom1924 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom1995 chi ∧
      ¬Fin15AnchoredAtom1997 chi ∧
      ¬Fin15AnchoredAtom1999 chi ∧
      ¬Fin15AnchoredAtom2003 chi ∧
      ¬Fin15AnchoredAtom2005 chi ∧
      ¬Fin15AnchoredAtom2014 chi ∧
      ¬Fin15AnchoredAtom2052 chi ∧
      ¬Fin15AnchoredAtom2054 chi ∧
      ¬Fin15AnchoredAtom2063 chi ∧
      ¬Fin15AnchoredAtom2078 chi ∧
      ¬Fin15AnchoredAtom2380 chi ∧
      ¬Fin15AnchoredAtom2382 chi ∧
      ¬Fin15AnchoredAtom2384 chi ∧
      ¬Fin15AnchoredAtom2388 chi ∧
      ¬Fin15AnchoredAtom2390 chi ∧
      ¬Fin15AnchoredAtom2399 chi ∧
      ¬Fin15AnchoredAtom2437 chi ∧
      ¬Fin15AnchoredAtom2439 chi ∧
      ¬Fin15AnchoredAtom2448 chi ∧
      ¬Fin15AnchoredAtom2463 chi ∧
      ¬Fin15AnchoredAtom2641 chi ∧
      ¬Fin15AnchoredAtom2643 chi ∧
      ¬Fin15AnchoredAtom2652 chi ∧
      ¬Fin15AnchoredAtom2667 chi ∧
      ¬Fin15AnchoredAtom2758 chi ∧
      ¬Fin15AnchoredAtom3095 chi ∧
      ¬Fin15AnchoredAtom3097 chi ∧
      ¬Fin15AnchoredAtom3099 chi ∧
      ¬Fin15AnchoredAtom3103 chi ∧
      ¬Fin15AnchoredAtom3105 chi ∧
      ¬Fin15AnchoredAtom3114 chi ∧
      ¬Fin15AnchoredAtom3152 chi ∧
      ¬Fin15AnchoredAtom3154 chi ∧
      ¬Fin15AnchoredAtom3163 chi ∧
      ¬Fin15AnchoredAtom3178 chi ∧
      ¬Fin15AnchoredAtom3356 chi ∧
      ¬Fin15AnchoredAtom3358 chi ∧
      ¬Fin15AnchoredAtom3367 chi ∧
      ¬Fin15AnchoredAtom3382 chi ∧
      ¬Fin15AnchoredAtom3473 chi ∧
      ¬Fin15AnchoredAtom4181 chi ∧
      ¬Fin15AnchoredAtom4183 chi ∧
      ¬Fin15AnchoredAtom4192 chi ∧
      ¬Fin15AnchoredAtom4207 chi ∧
      ¬Fin15AnchoredAtom4298 chi ∧
      ¬Fin15AnchoredAtom4634 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 5, 7, 8, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05547
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1898 Fin15AnchoredAtom1899 Fin15AnchoredAtom1901
    Fin15AnchoredAtom1903 Fin15AnchoredAtom1914 Fin15AnchoredAtom1916 Fin15AnchoredAtom1918
    Fin15AnchoredAtom1922 Fin15AnchoredAtom1924 Fin15AnchoredAtom1933 Fin15AnchoredAtom1995
    Fin15AnchoredAtom1997 Fin15AnchoredAtom1999 Fin15AnchoredAtom2003 Fin15AnchoredAtom2005
    Fin15AnchoredAtom2014 Fin15AnchoredAtom2052 Fin15AnchoredAtom2054 Fin15AnchoredAtom2063
    Fin15AnchoredAtom2078 Fin15AnchoredAtom2380 Fin15AnchoredAtom2382 Fin15AnchoredAtom2384
    Fin15AnchoredAtom2388 Fin15AnchoredAtom2390 Fin15AnchoredAtom2399 Fin15AnchoredAtom2437
    Fin15AnchoredAtom2439 Fin15AnchoredAtom2448 Fin15AnchoredAtom2463 Fin15AnchoredAtom2641
    Fin15AnchoredAtom2643 Fin15AnchoredAtom2652 Fin15AnchoredAtom2667 Fin15AnchoredAtom2758
    Fin15AnchoredAtom3095 Fin15AnchoredAtom3097 Fin15AnchoredAtom3099 Fin15AnchoredAtom3103
    Fin15AnchoredAtom3105 Fin15AnchoredAtom3114 Fin15AnchoredAtom3152 Fin15AnchoredAtom3154
    Fin15AnchoredAtom3163 Fin15AnchoredAtom3178 Fin15AnchoredAtom3356 Fin15AnchoredAtom3358
    Fin15AnchoredAtom3367 Fin15AnchoredAtom3382 Fin15AnchoredAtom3473 Fin15AnchoredAtom4181
    Fin15AnchoredAtom4183 Fin15AnchoredAtom4192 Fin15AnchoredAtom4207 Fin15AnchoredAtom4298
    Fin15AnchoredAtom4634 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30901 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1899 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1914 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1922 chi ∧
      ¬Fin15AnchoredAtom1925 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom1995 chi ∧
      ¬Fin15AnchoredAtom1997 chi ∧
      ¬Fin15AnchoredAtom2000 chi ∧
      ¬Fin15AnchoredAtom2003 chi ∧
      ¬Fin15AnchoredAtom2006 chi ∧
      ¬Fin15AnchoredAtom2015 chi ∧
      ¬Fin15AnchoredAtom2052 chi ∧
      ¬Fin15AnchoredAtom2055 chi ∧
      ¬Fin15AnchoredAtom2064 chi ∧
      ¬Fin15AnchoredAtom2079 chi ∧
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
      ¬Fin15AnchoredAtom3095 chi ∧
      ¬Fin15AnchoredAtom3097 chi ∧
      ¬Fin15AnchoredAtom3100 chi ∧
      ¬Fin15AnchoredAtom3103 chi ∧
      ¬Fin15AnchoredAtom3106 chi ∧
      ¬Fin15AnchoredAtom3115 chi ∧
      ¬Fin15AnchoredAtom3152 chi ∧
      ¬Fin15AnchoredAtom3155 chi ∧
      ¬Fin15AnchoredAtom3164 chi ∧
      ¬Fin15AnchoredAtom3179 chi ∧
      ¬Fin15AnchoredAtom3356 chi ∧
      ¬Fin15AnchoredAtom3359 chi ∧
      ¬Fin15AnchoredAtom3368 chi ∧
      ¬Fin15AnchoredAtom3383 chi ∧
      ¬Fin15AnchoredAtom3474 chi ∧
      ¬Fin15AnchoredAtom4181 chi ∧
      ¬Fin15AnchoredAtom4184 chi ∧
      ¬Fin15AnchoredAtom4193 chi ∧
      ¬Fin15AnchoredAtom4208 chi ∧
      ¬Fin15AnchoredAtom4299 chi ∧
      ¬Fin15AnchoredAtom4635 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 5, 7, 8, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09643
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1898 Fin15AnchoredAtom1899 Fin15AnchoredAtom1901
    Fin15AnchoredAtom1904 Fin15AnchoredAtom1914 Fin15AnchoredAtom1916 Fin15AnchoredAtom1919
    Fin15AnchoredAtom1922 Fin15AnchoredAtom1925 Fin15AnchoredAtom1934 Fin15AnchoredAtom1995
    Fin15AnchoredAtom1997 Fin15AnchoredAtom2000 Fin15AnchoredAtom2003 Fin15AnchoredAtom2006
    Fin15AnchoredAtom2015 Fin15AnchoredAtom2052 Fin15AnchoredAtom2055 Fin15AnchoredAtom2064
    Fin15AnchoredAtom2079 Fin15AnchoredAtom2380 Fin15AnchoredAtom2382 Fin15AnchoredAtom2385
    Fin15AnchoredAtom2388 Fin15AnchoredAtom2391 Fin15AnchoredAtom2400 Fin15AnchoredAtom2437
    Fin15AnchoredAtom2440 Fin15AnchoredAtom2449 Fin15AnchoredAtom2464 Fin15AnchoredAtom2641
    Fin15AnchoredAtom2644 Fin15AnchoredAtom2653 Fin15AnchoredAtom2668 Fin15AnchoredAtom2759
    Fin15AnchoredAtom3095 Fin15AnchoredAtom3097 Fin15AnchoredAtom3100 Fin15AnchoredAtom3103
    Fin15AnchoredAtom3106 Fin15AnchoredAtom3115 Fin15AnchoredAtom3152 Fin15AnchoredAtom3155
    Fin15AnchoredAtom3164 Fin15AnchoredAtom3179 Fin15AnchoredAtom3356 Fin15AnchoredAtom3359
    Fin15AnchoredAtom3368 Fin15AnchoredAtom3383 Fin15AnchoredAtom3474 Fin15AnchoredAtom4181
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

theorem fin15Anchored_clause30902 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1899 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1914 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1925 chi ∧
      ¬Fin15AnchoredAtom1926 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
      ¬Fin15AnchoredAtom1995 chi ∧
      ¬Fin15AnchoredAtom2000 chi ∧
      ¬Fin15AnchoredAtom2001 chi ∧
      ¬Fin15AnchoredAtom2006 chi ∧
      ¬Fin15AnchoredAtom2007 chi ∧
      ¬Fin15AnchoredAtom2022 chi ∧
      ¬Fin15AnchoredAtom2055 chi ∧
      ¬Fin15AnchoredAtom2056 chi ∧
      ¬Fin15AnchoredAtom2071 chi ∧
      ¬Fin15AnchoredAtom2086 chi ∧
      ¬Fin15AnchoredAtom2380 chi ∧
      ¬Fin15AnchoredAtom2385 chi ∧
      ¬Fin15AnchoredAtom2386 chi ∧
      ¬Fin15AnchoredAtom2391 chi ∧
      ¬Fin15AnchoredAtom2392 chi ∧
      ¬Fin15AnchoredAtom2407 chi ∧
      ¬Fin15AnchoredAtom2440 chi ∧
      ¬Fin15AnchoredAtom2441 chi ∧
      ¬Fin15AnchoredAtom2456 chi ∧
      ¬Fin15AnchoredAtom2471 chi ∧
      ¬Fin15AnchoredAtom2644 chi ∧
      ¬Fin15AnchoredAtom2645 chi ∧
      ¬Fin15AnchoredAtom2660 chi ∧
      ¬Fin15AnchoredAtom2675 chi ∧
      ¬Fin15AnchoredAtom2766 chi ∧
      ¬Fin15AnchoredAtom3095 chi ∧
      ¬Fin15AnchoredAtom3100 chi ∧
      ¬Fin15AnchoredAtom3101 chi ∧
      ¬Fin15AnchoredAtom3106 chi ∧
      ¬Fin15AnchoredAtom3107 chi ∧
      ¬Fin15AnchoredAtom3122 chi ∧
      ¬Fin15AnchoredAtom3155 chi ∧
      ¬Fin15AnchoredAtom3156 chi ∧
      ¬Fin15AnchoredAtom3171 chi ∧
      ¬Fin15AnchoredAtom3186 chi ∧
      ¬Fin15AnchoredAtom3359 chi ∧
      ¬Fin15AnchoredAtom3360 chi ∧
      ¬Fin15AnchoredAtom3375 chi ∧
      ¬Fin15AnchoredAtom3390 chi ∧
      ¬Fin15AnchoredAtom3481 chi ∧
      ¬Fin15AnchoredAtom4184 chi ∧
      ¬Fin15AnchoredAtom4185 chi ∧
      ¬Fin15AnchoredAtom4200 chi ∧
      ¬Fin15AnchoredAtom4215 chi ∧
      ¬Fin15AnchoredAtom4306 chi ∧
      ¬Fin15AnchoredAtom4642 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 5, 7, 8, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25003
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1898 Fin15AnchoredAtom1899 Fin15AnchoredAtom1904
    Fin15AnchoredAtom1905 Fin15AnchoredAtom1914 Fin15AnchoredAtom1919 Fin15AnchoredAtom1920
    Fin15AnchoredAtom1925 Fin15AnchoredAtom1926 Fin15AnchoredAtom1941 Fin15AnchoredAtom1995
    Fin15AnchoredAtom2000 Fin15AnchoredAtom2001 Fin15AnchoredAtom2006 Fin15AnchoredAtom2007
    Fin15AnchoredAtom2022 Fin15AnchoredAtom2055 Fin15AnchoredAtom2056 Fin15AnchoredAtom2071
    Fin15AnchoredAtom2086 Fin15AnchoredAtom2380 Fin15AnchoredAtom2385 Fin15AnchoredAtom2386
    Fin15AnchoredAtom2391 Fin15AnchoredAtom2392 Fin15AnchoredAtom2407 Fin15AnchoredAtom2440
    Fin15AnchoredAtom2441 Fin15AnchoredAtom2456 Fin15AnchoredAtom2471 Fin15AnchoredAtom2644
    Fin15AnchoredAtom2645 Fin15AnchoredAtom2660 Fin15AnchoredAtom2675 Fin15AnchoredAtom2766
    Fin15AnchoredAtom3095 Fin15AnchoredAtom3100 Fin15AnchoredAtom3101 Fin15AnchoredAtom3106
    Fin15AnchoredAtom3107 Fin15AnchoredAtom3122 Fin15AnchoredAtom3155 Fin15AnchoredAtom3156
    Fin15AnchoredAtom3171 Fin15AnchoredAtom3186 Fin15AnchoredAtom3359 Fin15AnchoredAtom3360
    Fin15AnchoredAtom3375 Fin15AnchoredAtom3390 Fin15AnchoredAtom3481 Fin15AnchoredAtom4184
    Fin15AnchoredAtom4185 Fin15AnchoredAtom4200 Fin15AnchoredAtom4215 Fin15AnchoredAtom4306
    Fin15AnchoredAtom4642 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30903 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
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
      ¬Fin15AnchoredAtom3096 chi ∧
      ¬Fin15AnchoredAtom3097 chi ∧
      ¬Fin15AnchoredAtom3099 chi ∧
      ¬Fin15AnchoredAtom3108 chi ∧
      ¬Fin15AnchoredAtom3110 chi ∧
      ¬Fin15AnchoredAtom3114 chi ∧
      ¬Fin15AnchoredAtom3157 chi ∧
      ¬Fin15AnchoredAtom3159 chi ∧
      ¬Fin15AnchoredAtom3163 chi ∧
      ¬Fin15AnchoredAtom3188 chi ∧
      ¬Fin15AnchoredAtom3361 chi ∧
      ¬Fin15AnchoredAtom3363 chi ∧
      ¬Fin15AnchoredAtom3367 chi ∧
      ¬Fin15AnchoredAtom3392 chi ∧
      ¬Fin15AnchoredAtom3483 chi ∧
      ¬Fin15AnchoredAtom4186 chi ∧
      ¬Fin15AnchoredAtom4188 chi ∧
      ¬Fin15AnchoredAtom4192 chi ∧
      ¬Fin15AnchoredAtom4217 chi ∧
      ¬Fin15AnchoredAtom4308 chi ∧
      ¬Fin15AnchoredAtom4644 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 5, 7, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05803
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1898 Fin15AnchoredAtom1900 Fin15AnchoredAtom1901
    Fin15AnchoredAtom1903 Fin15AnchoredAtom1915 Fin15AnchoredAtom1916 Fin15AnchoredAtom1918
    Fin15AnchoredAtom1927 Fin15AnchoredAtom1929 Fin15AnchoredAtom1933 Fin15AnchoredAtom1996
    Fin15AnchoredAtom1997 Fin15AnchoredAtom1999 Fin15AnchoredAtom2008 Fin15AnchoredAtom2010
    Fin15AnchoredAtom2014 Fin15AnchoredAtom2057 Fin15AnchoredAtom2059 Fin15AnchoredAtom2063
    Fin15AnchoredAtom2088 Fin15AnchoredAtom2381 Fin15AnchoredAtom2382 Fin15AnchoredAtom2384
    Fin15AnchoredAtom2393 Fin15AnchoredAtom2395 Fin15AnchoredAtom2399 Fin15AnchoredAtom2442
    Fin15AnchoredAtom2444 Fin15AnchoredAtom2448 Fin15AnchoredAtom2473 Fin15AnchoredAtom2646
    Fin15AnchoredAtom2648 Fin15AnchoredAtom2652 Fin15AnchoredAtom2677 Fin15AnchoredAtom2768
    Fin15AnchoredAtom3096 Fin15AnchoredAtom3097 Fin15AnchoredAtom3099 Fin15AnchoredAtom3108
    Fin15AnchoredAtom3110 Fin15AnchoredAtom3114 Fin15AnchoredAtom3157 Fin15AnchoredAtom3159
    Fin15AnchoredAtom3163 Fin15AnchoredAtom3188 Fin15AnchoredAtom3361 Fin15AnchoredAtom3363
    Fin15AnchoredAtom3367 Fin15AnchoredAtom3392 Fin15AnchoredAtom3483 Fin15AnchoredAtom4186
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

theorem fin15Anchored_clause30904 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
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
      ¬Fin15AnchoredAtom3096 chi ∧
      ¬Fin15AnchoredAtom3097 chi ∧
      ¬Fin15AnchoredAtom3100 chi ∧
      ¬Fin15AnchoredAtom3108 chi ∧
      ¬Fin15AnchoredAtom3111 chi ∧
      ¬Fin15AnchoredAtom3115 chi ∧
      ¬Fin15AnchoredAtom3157 chi ∧
      ¬Fin15AnchoredAtom3160 chi ∧
      ¬Fin15AnchoredAtom3164 chi ∧
      ¬Fin15AnchoredAtom3189 chi ∧
      ¬Fin15AnchoredAtom3361 chi ∧
      ¬Fin15AnchoredAtom3364 chi ∧
      ¬Fin15AnchoredAtom3368 chi ∧
      ¬Fin15AnchoredAtom3393 chi ∧
      ¬Fin15AnchoredAtom3484 chi ∧
      ¬Fin15AnchoredAtom4186 chi ∧
      ¬Fin15AnchoredAtom4189 chi ∧
      ¬Fin15AnchoredAtom4193 chi ∧
      ¬Fin15AnchoredAtom4218 chi ∧
      ¬Fin15AnchoredAtom4309 chi ∧
      ¬Fin15AnchoredAtom4645 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 5, 7, 9, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09899
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1898 Fin15AnchoredAtom1900 Fin15AnchoredAtom1901
    Fin15AnchoredAtom1904 Fin15AnchoredAtom1915 Fin15AnchoredAtom1916 Fin15AnchoredAtom1919
    Fin15AnchoredAtom1927 Fin15AnchoredAtom1930 Fin15AnchoredAtom1934 Fin15AnchoredAtom1996
    Fin15AnchoredAtom1997 Fin15AnchoredAtom2000 Fin15AnchoredAtom2008 Fin15AnchoredAtom2011
    Fin15AnchoredAtom2015 Fin15AnchoredAtom2057 Fin15AnchoredAtom2060 Fin15AnchoredAtom2064
    Fin15AnchoredAtom2089 Fin15AnchoredAtom2381 Fin15AnchoredAtom2382 Fin15AnchoredAtom2385
    Fin15AnchoredAtom2393 Fin15AnchoredAtom2396 Fin15AnchoredAtom2400 Fin15AnchoredAtom2442
    Fin15AnchoredAtom2445 Fin15AnchoredAtom2449 Fin15AnchoredAtom2474 Fin15AnchoredAtom2646
    Fin15AnchoredAtom2649 Fin15AnchoredAtom2653 Fin15AnchoredAtom2678 Fin15AnchoredAtom2769
    Fin15AnchoredAtom3096 Fin15AnchoredAtom3097 Fin15AnchoredAtom3100 Fin15AnchoredAtom3108
    Fin15AnchoredAtom3111 Fin15AnchoredAtom3115 Fin15AnchoredAtom3157 Fin15AnchoredAtom3160
    Fin15AnchoredAtom3164 Fin15AnchoredAtom3189 Fin15AnchoredAtom3361 Fin15AnchoredAtom3364
    Fin15AnchoredAtom3368 Fin15AnchoredAtom3393 Fin15AnchoredAtom3484 Fin15AnchoredAtom4186
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

theorem fin15Anchored_clause30905 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom1935 chi ∧
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
      ¬Fin15AnchoredAtom3096 chi ∧
      ¬Fin15AnchoredAtom3097 chi ∧
      ¬Fin15AnchoredAtom3101 chi ∧
      ¬Fin15AnchoredAtom3108 chi ∧
      ¬Fin15AnchoredAtom3112 chi ∧
      ¬Fin15AnchoredAtom3116 chi ∧
      ¬Fin15AnchoredAtom3157 chi ∧
      ¬Fin15AnchoredAtom3161 chi ∧
      ¬Fin15AnchoredAtom3165 chi ∧
      ¬Fin15AnchoredAtom3190 chi ∧
      ¬Fin15AnchoredAtom3361 chi ∧
      ¬Fin15AnchoredAtom3365 chi ∧
      ¬Fin15AnchoredAtom3369 chi ∧
      ¬Fin15AnchoredAtom3394 chi ∧
      ¬Fin15AnchoredAtom3485 chi ∧
      ¬Fin15AnchoredAtom4186 chi ∧
      ¬Fin15AnchoredAtom4190 chi ∧
      ¬Fin15AnchoredAtom4194 chi ∧
      ¬Fin15AnchoredAtom4219 chi ∧
      ¬Fin15AnchoredAtom4310 chi ∧
      ¬Fin15AnchoredAtom4646 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 5, 7, 9, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask18091
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1898 Fin15AnchoredAtom1900 Fin15AnchoredAtom1901
    Fin15AnchoredAtom1905 Fin15AnchoredAtom1915 Fin15AnchoredAtom1916 Fin15AnchoredAtom1920
    Fin15AnchoredAtom1927 Fin15AnchoredAtom1931 Fin15AnchoredAtom1935 Fin15AnchoredAtom1996
    Fin15AnchoredAtom1997 Fin15AnchoredAtom2001 Fin15AnchoredAtom2008 Fin15AnchoredAtom2012
    Fin15AnchoredAtom2016 Fin15AnchoredAtom2057 Fin15AnchoredAtom2061 Fin15AnchoredAtom2065
    Fin15AnchoredAtom2090 Fin15AnchoredAtom2381 Fin15AnchoredAtom2382 Fin15AnchoredAtom2386
    Fin15AnchoredAtom2393 Fin15AnchoredAtom2397 Fin15AnchoredAtom2401 Fin15AnchoredAtom2442
    Fin15AnchoredAtom2446 Fin15AnchoredAtom2450 Fin15AnchoredAtom2475 Fin15AnchoredAtom2646
    Fin15AnchoredAtom2650 Fin15AnchoredAtom2654 Fin15AnchoredAtom2679 Fin15AnchoredAtom2770
    Fin15AnchoredAtom3096 Fin15AnchoredAtom3097 Fin15AnchoredAtom3101 Fin15AnchoredAtom3108
    Fin15AnchoredAtom3112 Fin15AnchoredAtom3116 Fin15AnchoredAtom3157 Fin15AnchoredAtom3161
    Fin15AnchoredAtom3165 Fin15AnchoredAtom3190 Fin15AnchoredAtom3361 Fin15AnchoredAtom3365
    Fin15AnchoredAtom3369 Fin15AnchoredAtom3394 Fin15AnchoredAtom3485 Fin15AnchoredAtom4186
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

theorem fin15Anchored_clause30906 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1939 chi ∧
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
      ¬Fin15AnchoredAtom3096 chi ∧
      ¬Fin15AnchoredAtom3099 chi ∧
      ¬Fin15AnchoredAtom3100 chi ∧
      ¬Fin15AnchoredAtom3110 chi ∧
      ¬Fin15AnchoredAtom3111 chi ∧
      ¬Fin15AnchoredAtom3120 chi ∧
      ¬Fin15AnchoredAtom3159 chi ∧
      ¬Fin15AnchoredAtom3160 chi ∧
      ¬Fin15AnchoredAtom3169 chi ∧
      ¬Fin15AnchoredAtom3194 chi ∧
      ¬Fin15AnchoredAtom3363 chi ∧
      ¬Fin15AnchoredAtom3364 chi ∧
      ¬Fin15AnchoredAtom3373 chi ∧
      ¬Fin15AnchoredAtom3398 chi ∧
      ¬Fin15AnchoredAtom3489 chi ∧
      ¬Fin15AnchoredAtom4188 chi ∧
      ¬Fin15AnchoredAtom4189 chi ∧
      ¬Fin15AnchoredAtom4198 chi ∧
      ¬Fin15AnchoredAtom4223 chi ∧
      ¬Fin15AnchoredAtom4314 chi ∧
      ¬Fin15AnchoredAtom4650 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 5, 7, 9, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask12971
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1898 Fin15AnchoredAtom1900 Fin15AnchoredAtom1903
    Fin15AnchoredAtom1904 Fin15AnchoredAtom1915 Fin15AnchoredAtom1918 Fin15AnchoredAtom1919
    Fin15AnchoredAtom1929 Fin15AnchoredAtom1930 Fin15AnchoredAtom1939 Fin15AnchoredAtom1996
    Fin15AnchoredAtom1999 Fin15AnchoredAtom2000 Fin15AnchoredAtom2010 Fin15AnchoredAtom2011
    Fin15AnchoredAtom2020 Fin15AnchoredAtom2059 Fin15AnchoredAtom2060 Fin15AnchoredAtom2069
    Fin15AnchoredAtom2094 Fin15AnchoredAtom2381 Fin15AnchoredAtom2384 Fin15AnchoredAtom2385
    Fin15AnchoredAtom2395 Fin15AnchoredAtom2396 Fin15AnchoredAtom2405 Fin15AnchoredAtom2444
    Fin15AnchoredAtom2445 Fin15AnchoredAtom2454 Fin15AnchoredAtom2479 Fin15AnchoredAtom2648
    Fin15AnchoredAtom2649 Fin15AnchoredAtom2658 Fin15AnchoredAtom2683 Fin15AnchoredAtom2774
    Fin15AnchoredAtom3096 Fin15AnchoredAtom3099 Fin15AnchoredAtom3100 Fin15AnchoredAtom3110
    Fin15AnchoredAtom3111 Fin15AnchoredAtom3120 Fin15AnchoredAtom3159 Fin15AnchoredAtom3160
    Fin15AnchoredAtom3169 Fin15AnchoredAtom3194 Fin15AnchoredAtom3363 Fin15AnchoredAtom3364
    Fin15AnchoredAtom3373 Fin15AnchoredAtom3398 Fin15AnchoredAtom3489 Fin15AnchoredAtom4188
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

theorem fin15Anchored_clause30907 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom1940 chi ∧
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
      ¬Fin15AnchoredAtom3096 chi ∧
      ¬Fin15AnchoredAtom3099 chi ∧
      ¬Fin15AnchoredAtom3101 chi ∧
      ¬Fin15AnchoredAtom3110 chi ∧
      ¬Fin15AnchoredAtom3112 chi ∧
      ¬Fin15AnchoredAtom3121 chi ∧
      ¬Fin15AnchoredAtom3159 chi ∧
      ¬Fin15AnchoredAtom3161 chi ∧
      ¬Fin15AnchoredAtom3170 chi ∧
      ¬Fin15AnchoredAtom3195 chi ∧
      ¬Fin15AnchoredAtom3363 chi ∧
      ¬Fin15AnchoredAtom3365 chi ∧
      ¬Fin15AnchoredAtom3374 chi ∧
      ¬Fin15AnchoredAtom3399 chi ∧
      ¬Fin15AnchoredAtom3490 chi ∧
      ¬Fin15AnchoredAtom4188 chi ∧
      ¬Fin15AnchoredAtom4190 chi ∧
      ¬Fin15AnchoredAtom4199 chi ∧
      ¬Fin15AnchoredAtom4224 chi ∧
      ¬Fin15AnchoredAtom4315 chi ∧
      ¬Fin15AnchoredAtom4651 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 5, 7, 9, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21163
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1898 Fin15AnchoredAtom1900 Fin15AnchoredAtom1903
    Fin15AnchoredAtom1905 Fin15AnchoredAtom1915 Fin15AnchoredAtom1918 Fin15AnchoredAtom1920
    Fin15AnchoredAtom1929 Fin15AnchoredAtom1931 Fin15AnchoredAtom1940 Fin15AnchoredAtom1996
    Fin15AnchoredAtom1999 Fin15AnchoredAtom2001 Fin15AnchoredAtom2010 Fin15AnchoredAtom2012
    Fin15AnchoredAtom2021 Fin15AnchoredAtom2059 Fin15AnchoredAtom2061 Fin15AnchoredAtom2070
    Fin15AnchoredAtom2095 Fin15AnchoredAtom2381 Fin15AnchoredAtom2384 Fin15AnchoredAtom2386
    Fin15AnchoredAtom2395 Fin15AnchoredAtom2397 Fin15AnchoredAtom2406 Fin15AnchoredAtom2444
    Fin15AnchoredAtom2446 Fin15AnchoredAtom2455 Fin15AnchoredAtom2480 Fin15AnchoredAtom2648
    Fin15AnchoredAtom2650 Fin15AnchoredAtom2659 Fin15AnchoredAtom2684 Fin15AnchoredAtom2775
    Fin15AnchoredAtom3096 Fin15AnchoredAtom3099 Fin15AnchoredAtom3101 Fin15AnchoredAtom3110
    Fin15AnchoredAtom3112 Fin15AnchoredAtom3121 Fin15AnchoredAtom3159 Fin15AnchoredAtom3161
    Fin15AnchoredAtom3170 Fin15AnchoredAtom3195 Fin15AnchoredAtom3363 Fin15AnchoredAtom3365
    Fin15AnchoredAtom3374 Fin15AnchoredAtom3399 Fin15AnchoredAtom3490 Fin15AnchoredAtom4188
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

theorem fin15Anchored_clause30908 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
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
      ¬Fin15AnchoredAtom3096 chi ∧
      ¬Fin15AnchoredAtom3100 chi ∧
      ¬Fin15AnchoredAtom3101 chi ∧
      ¬Fin15AnchoredAtom3111 chi ∧
      ¬Fin15AnchoredAtom3112 chi ∧
      ¬Fin15AnchoredAtom3122 chi ∧
      ¬Fin15AnchoredAtom3160 chi ∧
      ¬Fin15AnchoredAtom3161 chi ∧
      ¬Fin15AnchoredAtom3171 chi ∧
      ¬Fin15AnchoredAtom3196 chi ∧
      ¬Fin15AnchoredAtom3364 chi ∧
      ¬Fin15AnchoredAtom3365 chi ∧
      ¬Fin15AnchoredAtom3375 chi ∧
      ¬Fin15AnchoredAtom3400 chi ∧
      ¬Fin15AnchoredAtom3491 chi ∧
      ¬Fin15AnchoredAtom4189 chi ∧
      ¬Fin15AnchoredAtom4190 chi ∧
      ¬Fin15AnchoredAtom4200 chi ∧
      ¬Fin15AnchoredAtom4225 chi ∧
      ¬Fin15AnchoredAtom4316 chi ∧
      ¬Fin15AnchoredAtom4652 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 5, 7, 9, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25259
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1898 Fin15AnchoredAtom1900 Fin15AnchoredAtom1904
    Fin15AnchoredAtom1905 Fin15AnchoredAtom1915 Fin15AnchoredAtom1919 Fin15AnchoredAtom1920
    Fin15AnchoredAtom1930 Fin15AnchoredAtom1931 Fin15AnchoredAtom1941 Fin15AnchoredAtom1996
    Fin15AnchoredAtom2000 Fin15AnchoredAtom2001 Fin15AnchoredAtom2011 Fin15AnchoredAtom2012
    Fin15AnchoredAtom2022 Fin15AnchoredAtom2060 Fin15AnchoredAtom2061 Fin15AnchoredAtom2071
    Fin15AnchoredAtom2096 Fin15AnchoredAtom2381 Fin15AnchoredAtom2385 Fin15AnchoredAtom2386
    Fin15AnchoredAtom2396 Fin15AnchoredAtom2397 Fin15AnchoredAtom2407 Fin15AnchoredAtom2445
    Fin15AnchoredAtom2446 Fin15AnchoredAtom2456 Fin15AnchoredAtom2481 Fin15AnchoredAtom2649
    Fin15AnchoredAtom2650 Fin15AnchoredAtom2660 Fin15AnchoredAtom2685 Fin15AnchoredAtom2776
    Fin15AnchoredAtom3096 Fin15AnchoredAtom3100 Fin15AnchoredAtom3101 Fin15AnchoredAtom3111
    Fin15AnchoredAtom3112 Fin15AnchoredAtom3122 Fin15AnchoredAtom3160 Fin15AnchoredAtom3161
    Fin15AnchoredAtom3171 Fin15AnchoredAtom3196 Fin15AnchoredAtom3364 Fin15AnchoredAtom3365
    Fin15AnchoredAtom3375 Fin15AnchoredAtom3400 Fin15AnchoredAtom3491 Fin15AnchoredAtom4189
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

theorem fin15Anchored_clause30909 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom1939 chi ∧
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
      ¬Fin15AnchoredAtom3097 chi ∧
      ¬Fin15AnchoredAtom3099 chi ∧
      ¬Fin15AnchoredAtom3100 chi ∧
      ¬Fin15AnchoredAtom3114 chi ∧
      ¬Fin15AnchoredAtom3115 chi ∧
      ¬Fin15AnchoredAtom3120 chi ∧
      ¬Fin15AnchoredAtom3163 chi ∧
      ¬Fin15AnchoredAtom3164 chi ∧
      ¬Fin15AnchoredAtom3169 chi ∧
      ¬Fin15AnchoredAtom3200 chi ∧
      ¬Fin15AnchoredAtom3367 chi ∧
      ¬Fin15AnchoredAtom3368 chi ∧
      ¬Fin15AnchoredAtom3373 chi ∧
      ¬Fin15AnchoredAtom3404 chi ∧
      ¬Fin15AnchoredAtom3495 chi ∧
      ¬Fin15AnchoredAtom4192 chi ∧
      ¬Fin15AnchoredAtom4193 chi ∧
      ¬Fin15AnchoredAtom4198 chi ∧
      ¬Fin15AnchoredAtom4229 chi ∧
      ¬Fin15AnchoredAtom4320 chi ∧
      ¬Fin15AnchoredAtom4656 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 5, 7, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13483
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1898 Fin15AnchoredAtom1901 Fin15AnchoredAtom1903
    Fin15AnchoredAtom1904 Fin15AnchoredAtom1916 Fin15AnchoredAtom1918 Fin15AnchoredAtom1919
    Fin15AnchoredAtom1933 Fin15AnchoredAtom1934 Fin15AnchoredAtom1939 Fin15AnchoredAtom1997
    Fin15AnchoredAtom1999 Fin15AnchoredAtom2000 Fin15AnchoredAtom2014 Fin15AnchoredAtom2015
    Fin15AnchoredAtom2020 Fin15AnchoredAtom2063 Fin15AnchoredAtom2064 Fin15AnchoredAtom2069
    Fin15AnchoredAtom2100 Fin15AnchoredAtom2382 Fin15AnchoredAtom2384 Fin15AnchoredAtom2385
    Fin15AnchoredAtom2399 Fin15AnchoredAtom2400 Fin15AnchoredAtom2405 Fin15AnchoredAtom2448
    Fin15AnchoredAtom2449 Fin15AnchoredAtom2454 Fin15AnchoredAtom2485 Fin15AnchoredAtom2652
    Fin15AnchoredAtom2653 Fin15AnchoredAtom2658 Fin15AnchoredAtom2689 Fin15AnchoredAtom2780
    Fin15AnchoredAtom3097 Fin15AnchoredAtom3099 Fin15AnchoredAtom3100 Fin15AnchoredAtom3114
    Fin15AnchoredAtom3115 Fin15AnchoredAtom3120 Fin15AnchoredAtom3163 Fin15AnchoredAtom3164
    Fin15AnchoredAtom3169 Fin15AnchoredAtom3200 Fin15AnchoredAtom3367 Fin15AnchoredAtom3368
    Fin15AnchoredAtom3373 Fin15AnchoredAtom3404 Fin15AnchoredAtom3495 Fin15AnchoredAtom4192
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

theorem fin15Anchored_clause30910 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom1935 chi ∧
      ¬Fin15AnchoredAtom1940 chi ∧
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
      ¬Fin15AnchoredAtom3097 chi ∧
      ¬Fin15AnchoredAtom3099 chi ∧
      ¬Fin15AnchoredAtom3101 chi ∧
      ¬Fin15AnchoredAtom3114 chi ∧
      ¬Fin15AnchoredAtom3116 chi ∧
      ¬Fin15AnchoredAtom3121 chi ∧
      ¬Fin15AnchoredAtom3163 chi ∧
      ¬Fin15AnchoredAtom3165 chi ∧
      ¬Fin15AnchoredAtom3170 chi ∧
      ¬Fin15AnchoredAtom3201 chi ∧
      ¬Fin15AnchoredAtom3367 chi ∧
      ¬Fin15AnchoredAtom3369 chi ∧
      ¬Fin15AnchoredAtom3374 chi ∧
      ¬Fin15AnchoredAtom3405 chi ∧
      ¬Fin15AnchoredAtom3496 chi ∧
      ¬Fin15AnchoredAtom4192 chi ∧
      ¬Fin15AnchoredAtom4194 chi ∧
      ¬Fin15AnchoredAtom4199 chi ∧
      ¬Fin15AnchoredAtom4230 chi ∧
      ¬Fin15AnchoredAtom4321 chi ∧
      ¬Fin15AnchoredAtom4657 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 5, 7, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21675
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1898 Fin15AnchoredAtom1901 Fin15AnchoredAtom1903
    Fin15AnchoredAtom1905 Fin15AnchoredAtom1916 Fin15AnchoredAtom1918 Fin15AnchoredAtom1920
    Fin15AnchoredAtom1933 Fin15AnchoredAtom1935 Fin15AnchoredAtom1940 Fin15AnchoredAtom1997
    Fin15AnchoredAtom1999 Fin15AnchoredAtom2001 Fin15AnchoredAtom2014 Fin15AnchoredAtom2016
    Fin15AnchoredAtom2021 Fin15AnchoredAtom2063 Fin15AnchoredAtom2065 Fin15AnchoredAtom2070
    Fin15AnchoredAtom2101 Fin15AnchoredAtom2382 Fin15AnchoredAtom2384 Fin15AnchoredAtom2386
    Fin15AnchoredAtom2399 Fin15AnchoredAtom2401 Fin15AnchoredAtom2406 Fin15AnchoredAtom2448
    Fin15AnchoredAtom2450 Fin15AnchoredAtom2455 Fin15AnchoredAtom2486 Fin15AnchoredAtom2652
    Fin15AnchoredAtom2654 Fin15AnchoredAtom2659 Fin15AnchoredAtom2690 Fin15AnchoredAtom2781
    Fin15AnchoredAtom3097 Fin15AnchoredAtom3099 Fin15AnchoredAtom3101 Fin15AnchoredAtom3114
    Fin15AnchoredAtom3116 Fin15AnchoredAtom3121 Fin15AnchoredAtom3163 Fin15AnchoredAtom3165
    Fin15AnchoredAtom3170 Fin15AnchoredAtom3201 Fin15AnchoredAtom3367 Fin15AnchoredAtom3369
    Fin15AnchoredAtom3374 Fin15AnchoredAtom3405 Fin15AnchoredAtom3496 Fin15AnchoredAtom4192
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

theorem fin15Anchored_clause30911 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom1935 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
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
      ¬Fin15AnchoredAtom3097 chi ∧
      ¬Fin15AnchoredAtom3100 chi ∧
      ¬Fin15AnchoredAtom3101 chi ∧
      ¬Fin15AnchoredAtom3115 chi ∧
      ¬Fin15AnchoredAtom3116 chi ∧
      ¬Fin15AnchoredAtom3122 chi ∧
      ¬Fin15AnchoredAtom3164 chi ∧
      ¬Fin15AnchoredAtom3165 chi ∧
      ¬Fin15AnchoredAtom3171 chi ∧
      ¬Fin15AnchoredAtom3202 chi ∧
      ¬Fin15AnchoredAtom3368 chi ∧
      ¬Fin15AnchoredAtom3369 chi ∧
      ¬Fin15AnchoredAtom3375 chi ∧
      ¬Fin15AnchoredAtom3406 chi ∧
      ¬Fin15AnchoredAtom3497 chi ∧
      ¬Fin15AnchoredAtom4193 chi ∧
      ¬Fin15AnchoredAtom4194 chi ∧
      ¬Fin15AnchoredAtom4200 chi ∧
      ¬Fin15AnchoredAtom4231 chi ∧
      ¬Fin15AnchoredAtom4322 chi ∧
      ¬Fin15AnchoredAtom4658 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 5, 7, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25771
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1898 Fin15AnchoredAtom1901 Fin15AnchoredAtom1904
    Fin15AnchoredAtom1905 Fin15AnchoredAtom1916 Fin15AnchoredAtom1919 Fin15AnchoredAtom1920
    Fin15AnchoredAtom1934 Fin15AnchoredAtom1935 Fin15AnchoredAtom1941 Fin15AnchoredAtom1997
    Fin15AnchoredAtom2000 Fin15AnchoredAtom2001 Fin15AnchoredAtom2015 Fin15AnchoredAtom2016
    Fin15AnchoredAtom2022 Fin15AnchoredAtom2064 Fin15AnchoredAtom2065 Fin15AnchoredAtom2071
    Fin15AnchoredAtom2102 Fin15AnchoredAtom2382 Fin15AnchoredAtom2385 Fin15AnchoredAtom2386
    Fin15AnchoredAtom2400 Fin15AnchoredAtom2401 Fin15AnchoredAtom2407 Fin15AnchoredAtom2449
    Fin15AnchoredAtom2450 Fin15AnchoredAtom2456 Fin15AnchoredAtom2487 Fin15AnchoredAtom2653
    Fin15AnchoredAtom2654 Fin15AnchoredAtom2660 Fin15AnchoredAtom2691 Fin15AnchoredAtom2782
    Fin15AnchoredAtom3097 Fin15AnchoredAtom3100 Fin15AnchoredAtom3101 Fin15AnchoredAtom3115
    Fin15AnchoredAtom3116 Fin15AnchoredAtom3122 Fin15AnchoredAtom3164 Fin15AnchoredAtom3165
    Fin15AnchoredAtom3171 Fin15AnchoredAtom3202 Fin15AnchoredAtom3368 Fin15AnchoredAtom3369
    Fin15AnchoredAtom3375 Fin15AnchoredAtom3406 Fin15AnchoredAtom3497 Fin15AnchoredAtom4193
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

theorem fin15Anchored_clause30912 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1902 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1917 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1936 chi ∧
      ¬Fin15AnchoredAtom1938 chi ∧
      ¬Fin15AnchoredAtom1940 chi ∧
      ¬Fin15AnchoredAtom1998 chi ∧
      ¬Fin15AnchoredAtom1999 chi ∧
      ¬Fin15AnchoredAtom2001 chi ∧
      ¬Fin15AnchoredAtom2017 chi ∧
      ¬Fin15AnchoredAtom2019 chi ∧
      ¬Fin15AnchoredAtom2021 chi ∧
      ¬Fin15AnchoredAtom2066 chi ∧
      ¬Fin15AnchoredAtom2068 chi ∧
      ¬Fin15AnchoredAtom2070 chi ∧
      ¬Fin15AnchoredAtom2104 chi ∧
      ¬Fin15AnchoredAtom2383 chi ∧
      ¬Fin15AnchoredAtom2384 chi ∧
      ¬Fin15AnchoredAtom2386 chi ∧
      ¬Fin15AnchoredAtom2402 chi ∧
      ¬Fin15AnchoredAtom2404 chi ∧
      ¬Fin15AnchoredAtom2406 chi ∧
      ¬Fin15AnchoredAtom2451 chi ∧
      ¬Fin15AnchoredAtom2453 chi ∧
      ¬Fin15AnchoredAtom2455 chi ∧
      ¬Fin15AnchoredAtom2489 chi ∧
      ¬Fin15AnchoredAtom2655 chi ∧
      ¬Fin15AnchoredAtom2657 chi ∧
      ¬Fin15AnchoredAtom2659 chi ∧
      ¬Fin15AnchoredAtom2693 chi ∧
      ¬Fin15AnchoredAtom2784 chi ∧
      ¬Fin15AnchoredAtom3098 chi ∧
      ¬Fin15AnchoredAtom3099 chi ∧
      ¬Fin15AnchoredAtom3101 chi ∧
      ¬Fin15AnchoredAtom3117 chi ∧
      ¬Fin15AnchoredAtom3119 chi ∧
      ¬Fin15AnchoredAtom3121 chi ∧
      ¬Fin15AnchoredAtom3166 chi ∧
      ¬Fin15AnchoredAtom3168 chi ∧
      ¬Fin15AnchoredAtom3170 chi ∧
      ¬Fin15AnchoredAtom3204 chi ∧
      ¬Fin15AnchoredAtom3370 chi ∧
      ¬Fin15AnchoredAtom3372 chi ∧
      ¬Fin15AnchoredAtom3374 chi ∧
      ¬Fin15AnchoredAtom3408 chi ∧
      ¬Fin15AnchoredAtom3499 chi ∧
      ¬Fin15AnchoredAtom4195 chi ∧
      ¬Fin15AnchoredAtom4197 chi ∧
      ¬Fin15AnchoredAtom4199 chi ∧
      ¬Fin15AnchoredAtom4233 chi ∧
      ¬Fin15AnchoredAtom4324 chi ∧
      ¬Fin15AnchoredAtom4660 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 5, 7, 11, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22699
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1898 Fin15AnchoredAtom1902 Fin15AnchoredAtom1903
    Fin15AnchoredAtom1905 Fin15AnchoredAtom1917 Fin15AnchoredAtom1918 Fin15AnchoredAtom1920
    Fin15AnchoredAtom1936 Fin15AnchoredAtom1938 Fin15AnchoredAtom1940 Fin15AnchoredAtom1998
    Fin15AnchoredAtom1999 Fin15AnchoredAtom2001 Fin15AnchoredAtom2017 Fin15AnchoredAtom2019
    Fin15AnchoredAtom2021 Fin15AnchoredAtom2066 Fin15AnchoredAtom2068 Fin15AnchoredAtom2070
    Fin15AnchoredAtom2104 Fin15AnchoredAtom2383 Fin15AnchoredAtom2384 Fin15AnchoredAtom2386
    Fin15AnchoredAtom2402 Fin15AnchoredAtom2404 Fin15AnchoredAtom2406 Fin15AnchoredAtom2451
    Fin15AnchoredAtom2453 Fin15AnchoredAtom2455 Fin15AnchoredAtom2489 Fin15AnchoredAtom2655
    Fin15AnchoredAtom2657 Fin15AnchoredAtom2659 Fin15AnchoredAtom2693 Fin15AnchoredAtom2784
    Fin15AnchoredAtom3098 Fin15AnchoredAtom3099 Fin15AnchoredAtom3101 Fin15AnchoredAtom3117
    Fin15AnchoredAtom3119 Fin15AnchoredAtom3121 Fin15AnchoredAtom3166 Fin15AnchoredAtom3168
    Fin15AnchoredAtom3170 Fin15AnchoredAtom3204 Fin15AnchoredAtom3370 Fin15AnchoredAtom3372
    Fin15AnchoredAtom3374 Fin15AnchoredAtom3408 Fin15AnchoredAtom3499 Fin15AnchoredAtom4195
    Fin15AnchoredAtom4197 Fin15AnchoredAtom4199 Fin15AnchoredAtom4233 Fin15AnchoredAtom4324
    Fin15AnchoredAtom4660 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30913 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1939 chi ∧
      ¬Fin15AnchoredAtom1940 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
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
      ¬Fin15AnchoredAtom3099 chi ∧
      ¬Fin15AnchoredAtom3100 chi ∧
      ¬Fin15AnchoredAtom3101 chi ∧
      ¬Fin15AnchoredAtom3120 chi ∧
      ¬Fin15AnchoredAtom3121 chi ∧
      ¬Fin15AnchoredAtom3122 chi ∧
      ¬Fin15AnchoredAtom3169 chi ∧
      ¬Fin15AnchoredAtom3170 chi ∧
      ¬Fin15AnchoredAtom3171 chi ∧
      ¬Fin15AnchoredAtom3206 chi ∧
      ¬Fin15AnchoredAtom3373 chi ∧
      ¬Fin15AnchoredAtom3374 chi ∧
      ¬Fin15AnchoredAtom3375 chi ∧
      ¬Fin15AnchoredAtom3410 chi ∧
      ¬Fin15AnchoredAtom3501 chi ∧
      ¬Fin15AnchoredAtom4198 chi ∧
      ¬Fin15AnchoredAtom4199 chi ∧
      ¬Fin15AnchoredAtom4200 chi ∧
      ¬Fin15AnchoredAtom4235 chi ∧
      ¬Fin15AnchoredAtom4326 chi ∧
      ¬Fin15AnchoredAtom4662 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 5, 7, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask28843
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1898 Fin15AnchoredAtom1903 Fin15AnchoredAtom1904
    Fin15AnchoredAtom1905 Fin15AnchoredAtom1918 Fin15AnchoredAtom1919 Fin15AnchoredAtom1920
    Fin15AnchoredAtom1939 Fin15AnchoredAtom1940 Fin15AnchoredAtom1941 Fin15AnchoredAtom1999
    Fin15AnchoredAtom2000 Fin15AnchoredAtom2001 Fin15AnchoredAtom2020 Fin15AnchoredAtom2021
    Fin15AnchoredAtom2022 Fin15AnchoredAtom2069 Fin15AnchoredAtom2070 Fin15AnchoredAtom2071
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2384 Fin15AnchoredAtom2385 Fin15AnchoredAtom2386
    Fin15AnchoredAtom2405 Fin15AnchoredAtom2406 Fin15AnchoredAtom2407 Fin15AnchoredAtom2454
    Fin15AnchoredAtom2455 Fin15AnchoredAtom2456 Fin15AnchoredAtom2491 Fin15AnchoredAtom2658
    Fin15AnchoredAtom2659 Fin15AnchoredAtom2660 Fin15AnchoredAtom2695 Fin15AnchoredAtom2786
    Fin15AnchoredAtom3099 Fin15AnchoredAtom3100 Fin15AnchoredAtom3101 Fin15AnchoredAtom3120
    Fin15AnchoredAtom3121 Fin15AnchoredAtom3122 Fin15AnchoredAtom3169 Fin15AnchoredAtom3170
    Fin15AnchoredAtom3171 Fin15AnchoredAtom3206 Fin15AnchoredAtom3373 Fin15AnchoredAtom3374
    Fin15AnchoredAtom3375 Fin15AnchoredAtom3410 Fin15AnchoredAtom3501 Fin15AnchoredAtom4198
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

theorem fin15Anchored_clause30914 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1899 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1921 chi ∧
      ¬Fin15AnchoredAtom1922 chi ∧
      ¬Fin15AnchoredAtom1924 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom2002 chi ∧
      ¬Fin15AnchoredAtom2003 chi ∧
      ¬Fin15AnchoredAtom2005 chi ∧
      ¬Fin15AnchoredAtom2008 chi ∧
      ¬Fin15AnchoredAtom2010 chi ∧
      ¬Fin15AnchoredAtom2014 chi ∧
      ¬Fin15AnchoredAtom2072 chi ∧
      ¬Fin15AnchoredAtom2074 chi ∧
      ¬Fin15AnchoredAtom2078 chi ∧
      ¬Fin15AnchoredAtom2088 chi ∧
      ¬Fin15AnchoredAtom2387 chi ∧
      ¬Fin15AnchoredAtom2388 chi ∧
      ¬Fin15AnchoredAtom2390 chi ∧
      ¬Fin15AnchoredAtom2393 chi ∧
      ¬Fin15AnchoredAtom2395 chi ∧
      ¬Fin15AnchoredAtom2399 chi ∧
      ¬Fin15AnchoredAtom2457 chi ∧
      ¬Fin15AnchoredAtom2459 chi ∧
      ¬Fin15AnchoredAtom2463 chi ∧
      ¬Fin15AnchoredAtom2473 chi ∧
      ¬Fin15AnchoredAtom2661 chi ∧
      ¬Fin15AnchoredAtom2663 chi ∧
      ¬Fin15AnchoredAtom2667 chi ∧
      ¬Fin15AnchoredAtom2677 chi ∧
      ¬Fin15AnchoredAtom2788 chi ∧
      ¬Fin15AnchoredAtom3102 chi ∧
      ¬Fin15AnchoredAtom3103 chi ∧
      ¬Fin15AnchoredAtom3105 chi ∧
      ¬Fin15AnchoredAtom3108 chi ∧
      ¬Fin15AnchoredAtom3110 chi ∧
      ¬Fin15AnchoredAtom3114 chi ∧
      ¬Fin15AnchoredAtom3172 chi ∧
      ¬Fin15AnchoredAtom3174 chi ∧
      ¬Fin15AnchoredAtom3178 chi ∧
      ¬Fin15AnchoredAtom3188 chi ∧
      ¬Fin15AnchoredAtom3376 chi ∧
      ¬Fin15AnchoredAtom3378 chi ∧
      ¬Fin15AnchoredAtom3382 chi ∧
      ¬Fin15AnchoredAtom3392 chi ∧
      ¬Fin15AnchoredAtom3503 chi ∧
      ¬Fin15AnchoredAtom4201 chi ∧
      ¬Fin15AnchoredAtom4203 chi ∧
      ¬Fin15AnchoredAtom4207 chi ∧
      ¬Fin15AnchoredAtom4217 chi ∧
      ¬Fin15AnchoredAtom4328 chi ∧
      ¬Fin15AnchoredAtom4664 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 5, 8, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05931
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1899 Fin15AnchoredAtom1900 Fin15AnchoredAtom1901
    Fin15AnchoredAtom1903 Fin15AnchoredAtom1921 Fin15AnchoredAtom1922 Fin15AnchoredAtom1924
    Fin15AnchoredAtom1927 Fin15AnchoredAtom1929 Fin15AnchoredAtom1933 Fin15AnchoredAtom2002
    Fin15AnchoredAtom2003 Fin15AnchoredAtom2005 Fin15AnchoredAtom2008 Fin15AnchoredAtom2010
    Fin15AnchoredAtom2014 Fin15AnchoredAtom2072 Fin15AnchoredAtom2074 Fin15AnchoredAtom2078
    Fin15AnchoredAtom2088 Fin15AnchoredAtom2387 Fin15AnchoredAtom2388 Fin15AnchoredAtom2390
    Fin15AnchoredAtom2393 Fin15AnchoredAtom2395 Fin15AnchoredAtom2399 Fin15AnchoredAtom2457
    Fin15AnchoredAtom2459 Fin15AnchoredAtom2463 Fin15AnchoredAtom2473 Fin15AnchoredAtom2661
    Fin15AnchoredAtom2663 Fin15AnchoredAtom2667 Fin15AnchoredAtom2677 Fin15AnchoredAtom2788
    Fin15AnchoredAtom3102 Fin15AnchoredAtom3103 Fin15AnchoredAtom3105 Fin15AnchoredAtom3108
    Fin15AnchoredAtom3110 Fin15AnchoredAtom3114 Fin15AnchoredAtom3172 Fin15AnchoredAtom3174
    Fin15AnchoredAtom3178 Fin15AnchoredAtom3188 Fin15AnchoredAtom3376 Fin15AnchoredAtom3378
    Fin15AnchoredAtom3382 Fin15AnchoredAtom3392 Fin15AnchoredAtom3503 Fin15AnchoredAtom4201
    Fin15AnchoredAtom4203 Fin15AnchoredAtom4207 Fin15AnchoredAtom4217 Fin15AnchoredAtom4328
    Fin15AnchoredAtom4664 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30915 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1899 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1921 chi ∧
      ¬Fin15AnchoredAtom1925 chi ∧
      ¬Fin15AnchoredAtom1926 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
      ¬Fin15AnchoredAtom2002 chi ∧
      ¬Fin15AnchoredAtom2006 chi ∧
      ¬Fin15AnchoredAtom2007 chi ∧
      ¬Fin15AnchoredAtom2011 chi ∧
      ¬Fin15AnchoredAtom2012 chi ∧
      ¬Fin15AnchoredAtom2022 chi ∧
      ¬Fin15AnchoredAtom2075 chi ∧
      ¬Fin15AnchoredAtom2076 chi ∧
      ¬Fin15AnchoredAtom2086 chi ∧
      ¬Fin15AnchoredAtom2096 chi ∧
      ¬Fin15AnchoredAtom2387 chi ∧
      ¬Fin15AnchoredAtom2391 chi ∧
      ¬Fin15AnchoredAtom2392 chi ∧
      ¬Fin15AnchoredAtom2396 chi ∧
      ¬Fin15AnchoredAtom2397 chi ∧
      ¬Fin15AnchoredAtom2407 chi ∧
      ¬Fin15AnchoredAtom2460 chi ∧
      ¬Fin15AnchoredAtom2461 chi ∧
      ¬Fin15AnchoredAtom2471 chi ∧
      ¬Fin15AnchoredAtom2481 chi ∧
      ¬Fin15AnchoredAtom2664 chi ∧
      ¬Fin15AnchoredAtom2665 chi ∧
      ¬Fin15AnchoredAtom2675 chi ∧
      ¬Fin15AnchoredAtom2685 chi ∧
      ¬Fin15AnchoredAtom2796 chi ∧
      ¬Fin15AnchoredAtom3102 chi ∧
      ¬Fin15AnchoredAtom3106 chi ∧
      ¬Fin15AnchoredAtom3107 chi ∧
      ¬Fin15AnchoredAtom3111 chi ∧
      ¬Fin15AnchoredAtom3112 chi ∧
      ¬Fin15AnchoredAtom3122 chi ∧
      ¬Fin15AnchoredAtom3175 chi ∧
      ¬Fin15AnchoredAtom3176 chi ∧
      ¬Fin15AnchoredAtom3186 chi ∧
      ¬Fin15AnchoredAtom3196 chi ∧
      ¬Fin15AnchoredAtom3379 chi ∧
      ¬Fin15AnchoredAtom3380 chi ∧
      ¬Fin15AnchoredAtom3390 chi ∧
      ¬Fin15AnchoredAtom3400 chi ∧
      ¬Fin15AnchoredAtom3511 chi ∧
      ¬Fin15AnchoredAtom4204 chi ∧
      ¬Fin15AnchoredAtom4205 chi ∧
      ¬Fin15AnchoredAtom4215 chi ∧
      ¬Fin15AnchoredAtom4225 chi ∧
      ¬Fin15AnchoredAtom4336 chi ∧
      ¬Fin15AnchoredAtom4672 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 5, 8, 9, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25387
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1899 Fin15AnchoredAtom1900 Fin15AnchoredAtom1904
    Fin15AnchoredAtom1905 Fin15AnchoredAtom1921 Fin15AnchoredAtom1925 Fin15AnchoredAtom1926
    Fin15AnchoredAtom1930 Fin15AnchoredAtom1931 Fin15AnchoredAtom1941 Fin15AnchoredAtom2002
    Fin15AnchoredAtom2006 Fin15AnchoredAtom2007 Fin15AnchoredAtom2011 Fin15AnchoredAtom2012
    Fin15AnchoredAtom2022 Fin15AnchoredAtom2075 Fin15AnchoredAtom2076 Fin15AnchoredAtom2086
    Fin15AnchoredAtom2096 Fin15AnchoredAtom2387 Fin15AnchoredAtom2391 Fin15AnchoredAtom2392
    Fin15AnchoredAtom2396 Fin15AnchoredAtom2397 Fin15AnchoredAtom2407 Fin15AnchoredAtom2460
    Fin15AnchoredAtom2461 Fin15AnchoredAtom2471 Fin15AnchoredAtom2481 Fin15AnchoredAtom2664
    Fin15AnchoredAtom2665 Fin15AnchoredAtom2675 Fin15AnchoredAtom2685 Fin15AnchoredAtom2796
    Fin15AnchoredAtom3102 Fin15AnchoredAtom3106 Fin15AnchoredAtom3107 Fin15AnchoredAtom3111
    Fin15AnchoredAtom3112 Fin15AnchoredAtom3122 Fin15AnchoredAtom3175 Fin15AnchoredAtom3176
    Fin15AnchoredAtom3186 Fin15AnchoredAtom3196 Fin15AnchoredAtom3379 Fin15AnchoredAtom3380
    Fin15AnchoredAtom3390 Fin15AnchoredAtom3400 Fin15AnchoredAtom3511 Fin15AnchoredAtom4204
    Fin15AnchoredAtom4205 Fin15AnchoredAtom4215 Fin15AnchoredAtom4225 Fin15AnchoredAtom4336
    Fin15AnchoredAtom4672 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30916 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1899 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1922 chi ∧
      ¬Fin15AnchoredAtom1924 chi ∧
      ¬Fin15AnchoredAtom1925 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom1939 chi ∧
      ¬Fin15AnchoredAtom2003 chi ∧
      ¬Fin15AnchoredAtom2005 chi ∧
      ¬Fin15AnchoredAtom2006 chi ∧
      ¬Fin15AnchoredAtom2014 chi ∧
      ¬Fin15AnchoredAtom2015 chi ∧
      ¬Fin15AnchoredAtom2020 chi ∧
      ¬Fin15AnchoredAtom2078 chi ∧
      ¬Fin15AnchoredAtom2079 chi ∧
      ¬Fin15AnchoredAtom2084 chi ∧
      ¬Fin15AnchoredAtom2100 chi ∧
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
      ¬Fin15AnchoredAtom3103 chi ∧
      ¬Fin15AnchoredAtom3105 chi ∧
      ¬Fin15AnchoredAtom3106 chi ∧
      ¬Fin15AnchoredAtom3114 chi ∧
      ¬Fin15AnchoredAtom3115 chi ∧
      ¬Fin15AnchoredAtom3120 chi ∧
      ¬Fin15AnchoredAtom3178 chi ∧
      ¬Fin15AnchoredAtom3179 chi ∧
      ¬Fin15AnchoredAtom3184 chi ∧
      ¬Fin15AnchoredAtom3200 chi ∧
      ¬Fin15AnchoredAtom3382 chi ∧
      ¬Fin15AnchoredAtom3383 chi ∧
      ¬Fin15AnchoredAtom3388 chi ∧
      ¬Fin15AnchoredAtom3404 chi ∧
      ¬Fin15AnchoredAtom3515 chi ∧
      ¬Fin15AnchoredAtom4207 chi ∧
      ¬Fin15AnchoredAtom4208 chi ∧
      ¬Fin15AnchoredAtom4213 chi ∧
      ¬Fin15AnchoredAtom4229 chi ∧
      ¬Fin15AnchoredAtom4340 chi ∧
      ¬Fin15AnchoredAtom4676 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 5, 8, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13611
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1899 Fin15AnchoredAtom1901 Fin15AnchoredAtom1903
    Fin15AnchoredAtom1904 Fin15AnchoredAtom1922 Fin15AnchoredAtom1924 Fin15AnchoredAtom1925
    Fin15AnchoredAtom1933 Fin15AnchoredAtom1934 Fin15AnchoredAtom1939 Fin15AnchoredAtom2003
    Fin15AnchoredAtom2005 Fin15AnchoredAtom2006 Fin15AnchoredAtom2014 Fin15AnchoredAtom2015
    Fin15AnchoredAtom2020 Fin15AnchoredAtom2078 Fin15AnchoredAtom2079 Fin15AnchoredAtom2084
    Fin15AnchoredAtom2100 Fin15AnchoredAtom2388 Fin15AnchoredAtom2390 Fin15AnchoredAtom2391
    Fin15AnchoredAtom2399 Fin15AnchoredAtom2400 Fin15AnchoredAtom2405 Fin15AnchoredAtom2463
    Fin15AnchoredAtom2464 Fin15AnchoredAtom2469 Fin15AnchoredAtom2485 Fin15AnchoredAtom2667
    Fin15AnchoredAtom2668 Fin15AnchoredAtom2673 Fin15AnchoredAtom2689 Fin15AnchoredAtom2800
    Fin15AnchoredAtom3103 Fin15AnchoredAtom3105 Fin15AnchoredAtom3106 Fin15AnchoredAtom3114
    Fin15AnchoredAtom3115 Fin15AnchoredAtom3120 Fin15AnchoredAtom3178 Fin15AnchoredAtom3179
    Fin15AnchoredAtom3184 Fin15AnchoredAtom3200 Fin15AnchoredAtom3382 Fin15AnchoredAtom3383
    Fin15AnchoredAtom3388 Fin15AnchoredAtom3404 Fin15AnchoredAtom3515 Fin15AnchoredAtom4207
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

theorem fin15Anchored_clause30917 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1902 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1928 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom1932 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom1936 chi ∧
      ¬Fin15AnchoredAtom2008 chi ∧
      ¬Fin15AnchoredAtom2009 chi ∧
      ¬Fin15AnchoredAtom2010 chi ∧
      ¬Fin15AnchoredAtom2013 chi ∧
      ¬Fin15AnchoredAtom2014 chi ∧
      ¬Fin15AnchoredAtom2017 chi ∧
      ¬Fin15AnchoredAtom2087 chi ∧
      ¬Fin15AnchoredAtom2088 chi ∧
      ¬Fin15AnchoredAtom2091 chi ∧
      ¬Fin15AnchoredAtom2097 chi ∧
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
      ¬Fin15AnchoredAtom3108 chi ∧
      ¬Fin15AnchoredAtom3109 chi ∧
      ¬Fin15AnchoredAtom3110 chi ∧
      ¬Fin15AnchoredAtom3113 chi ∧
      ¬Fin15AnchoredAtom3114 chi ∧
      ¬Fin15AnchoredAtom3117 chi ∧
      ¬Fin15AnchoredAtom3187 chi ∧
      ¬Fin15AnchoredAtom3188 chi ∧
      ¬Fin15AnchoredAtom3191 chi ∧
      ¬Fin15AnchoredAtom3197 chi ∧
      ¬Fin15AnchoredAtom3391 chi ∧
      ¬Fin15AnchoredAtom3392 chi ∧
      ¬Fin15AnchoredAtom3395 chi ∧
      ¬Fin15AnchoredAtom3401 chi ∧
      ¬Fin15AnchoredAtom3522 chi ∧
      ¬Fin15AnchoredAtom4216 chi ∧
      ¬Fin15AnchoredAtom4217 chi ∧
      ¬Fin15AnchoredAtom4220 chi ∧
      ¬Fin15AnchoredAtom4226 chi ∧
      ¬Fin15AnchoredAtom4347 chi ∧
      ¬Fin15AnchoredAtom4683 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 5, 9, 10, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask07723
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1900 Fin15AnchoredAtom1901 Fin15AnchoredAtom1902
    Fin15AnchoredAtom1903 Fin15AnchoredAtom1927 Fin15AnchoredAtom1928 Fin15AnchoredAtom1929
    Fin15AnchoredAtom1932 Fin15AnchoredAtom1933 Fin15AnchoredAtom1936 Fin15AnchoredAtom2008
    Fin15AnchoredAtom2009 Fin15AnchoredAtom2010 Fin15AnchoredAtom2013 Fin15AnchoredAtom2014
    Fin15AnchoredAtom2017 Fin15AnchoredAtom2087 Fin15AnchoredAtom2088 Fin15AnchoredAtom2091
    Fin15AnchoredAtom2097 Fin15AnchoredAtom2393 Fin15AnchoredAtom2394 Fin15AnchoredAtom2395
    Fin15AnchoredAtom2398 Fin15AnchoredAtom2399 Fin15AnchoredAtom2402 Fin15AnchoredAtom2472
    Fin15AnchoredAtom2473 Fin15AnchoredAtom2476 Fin15AnchoredAtom2482 Fin15AnchoredAtom2676
    Fin15AnchoredAtom2677 Fin15AnchoredAtom2680 Fin15AnchoredAtom2686 Fin15AnchoredAtom2807
    Fin15AnchoredAtom3108 Fin15AnchoredAtom3109 Fin15AnchoredAtom3110 Fin15AnchoredAtom3113
    Fin15AnchoredAtom3114 Fin15AnchoredAtom3117 Fin15AnchoredAtom3187 Fin15AnchoredAtom3188
    Fin15AnchoredAtom3191 Fin15AnchoredAtom3197 Fin15AnchoredAtom3391 Fin15AnchoredAtom3392
    Fin15AnchoredAtom3395 Fin15AnchoredAtom3401 Fin15AnchoredAtom3522 Fin15AnchoredAtom4216
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

theorem fin15Anchored_clause30918 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom1939 chi ∧
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
      ¬Fin15AnchoredAtom3108 chi ∧
      ¬Fin15AnchoredAtom3110 chi ∧
      ¬Fin15AnchoredAtom3111 chi ∧
      ¬Fin15AnchoredAtom3114 chi ∧
      ¬Fin15AnchoredAtom3115 chi ∧
      ¬Fin15AnchoredAtom3120 chi ∧
      ¬Fin15AnchoredAtom3188 chi ∧
      ¬Fin15AnchoredAtom3189 chi ∧
      ¬Fin15AnchoredAtom3194 chi ∧
      ¬Fin15AnchoredAtom3200 chi ∧
      ¬Fin15AnchoredAtom3392 chi ∧
      ¬Fin15AnchoredAtom3393 chi ∧
      ¬Fin15AnchoredAtom3398 chi ∧
      ¬Fin15AnchoredAtom3404 chi ∧
      ¬Fin15AnchoredAtom3525 chi ∧
      ¬Fin15AnchoredAtom4217 chi ∧
      ¬Fin15AnchoredAtom4218 chi ∧
      ¬Fin15AnchoredAtom4223 chi ∧
      ¬Fin15AnchoredAtom4229 chi ∧
      ¬Fin15AnchoredAtom4350 chi ∧
      ¬Fin15AnchoredAtom4686 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 5, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13867
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1900 Fin15AnchoredAtom1901 Fin15AnchoredAtom1903
    Fin15AnchoredAtom1904 Fin15AnchoredAtom1927 Fin15AnchoredAtom1929 Fin15AnchoredAtom1930
    Fin15AnchoredAtom1933 Fin15AnchoredAtom1934 Fin15AnchoredAtom1939 Fin15AnchoredAtom2008
    Fin15AnchoredAtom2010 Fin15AnchoredAtom2011 Fin15AnchoredAtom2014 Fin15AnchoredAtom2015
    Fin15AnchoredAtom2020 Fin15AnchoredAtom2088 Fin15AnchoredAtom2089 Fin15AnchoredAtom2094
    Fin15AnchoredAtom2100 Fin15AnchoredAtom2393 Fin15AnchoredAtom2395 Fin15AnchoredAtom2396
    Fin15AnchoredAtom2399 Fin15AnchoredAtom2400 Fin15AnchoredAtom2405 Fin15AnchoredAtom2473
    Fin15AnchoredAtom2474 Fin15AnchoredAtom2479 Fin15AnchoredAtom2485 Fin15AnchoredAtom2677
    Fin15AnchoredAtom2678 Fin15AnchoredAtom2683 Fin15AnchoredAtom2689 Fin15AnchoredAtom2810
    Fin15AnchoredAtom3108 Fin15AnchoredAtom3110 Fin15AnchoredAtom3111 Fin15AnchoredAtom3114
    Fin15AnchoredAtom3115 Fin15AnchoredAtom3120 Fin15AnchoredAtom3188 Fin15AnchoredAtom3189
    Fin15AnchoredAtom3194 Fin15AnchoredAtom3200 Fin15AnchoredAtom3392 Fin15AnchoredAtom3393
    Fin15AnchoredAtom3398 Fin15AnchoredAtom3404 Fin15AnchoredAtom3525 Fin15AnchoredAtom4217
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

theorem fin15Anchored_clause30919 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom1935 chi ∧
      ¬Fin15AnchoredAtom1940 chi ∧
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
      ¬Fin15AnchoredAtom3108 chi ∧
      ¬Fin15AnchoredAtom3110 chi ∧
      ¬Fin15AnchoredAtom3112 chi ∧
      ¬Fin15AnchoredAtom3114 chi ∧
      ¬Fin15AnchoredAtom3116 chi ∧
      ¬Fin15AnchoredAtom3121 chi ∧
      ¬Fin15AnchoredAtom3188 chi ∧
      ¬Fin15AnchoredAtom3190 chi ∧
      ¬Fin15AnchoredAtom3195 chi ∧
      ¬Fin15AnchoredAtom3201 chi ∧
      ¬Fin15AnchoredAtom3392 chi ∧
      ¬Fin15AnchoredAtom3394 chi ∧
      ¬Fin15AnchoredAtom3399 chi ∧
      ¬Fin15AnchoredAtom3405 chi ∧
      ¬Fin15AnchoredAtom3526 chi ∧
      ¬Fin15AnchoredAtom4217 chi ∧
      ¬Fin15AnchoredAtom4219 chi ∧
      ¬Fin15AnchoredAtom4224 chi ∧
      ¬Fin15AnchoredAtom4230 chi ∧
      ¬Fin15AnchoredAtom4351 chi ∧
      ¬Fin15AnchoredAtom4687 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 5, 9, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22059
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1900 Fin15AnchoredAtom1901 Fin15AnchoredAtom1903
    Fin15AnchoredAtom1905 Fin15AnchoredAtom1927 Fin15AnchoredAtom1929 Fin15AnchoredAtom1931
    Fin15AnchoredAtom1933 Fin15AnchoredAtom1935 Fin15AnchoredAtom1940 Fin15AnchoredAtom2008
    Fin15AnchoredAtom2010 Fin15AnchoredAtom2012 Fin15AnchoredAtom2014 Fin15AnchoredAtom2016
    Fin15AnchoredAtom2021 Fin15AnchoredAtom2088 Fin15AnchoredAtom2090 Fin15AnchoredAtom2095
    Fin15AnchoredAtom2101 Fin15AnchoredAtom2393 Fin15AnchoredAtom2395 Fin15AnchoredAtom2397
    Fin15AnchoredAtom2399 Fin15AnchoredAtom2401 Fin15AnchoredAtom2406 Fin15AnchoredAtom2473
    Fin15AnchoredAtom2475 Fin15AnchoredAtom2480 Fin15AnchoredAtom2486 Fin15AnchoredAtom2677
    Fin15AnchoredAtom2679 Fin15AnchoredAtom2684 Fin15AnchoredAtom2690 Fin15AnchoredAtom2811
    Fin15AnchoredAtom3108 Fin15AnchoredAtom3110 Fin15AnchoredAtom3112 Fin15AnchoredAtom3114
    Fin15AnchoredAtom3116 Fin15AnchoredAtom3121 Fin15AnchoredAtom3188 Fin15AnchoredAtom3190
    Fin15AnchoredAtom3195 Fin15AnchoredAtom3201 Fin15AnchoredAtom3392 Fin15AnchoredAtom3394
    Fin15AnchoredAtom3399 Fin15AnchoredAtom3405 Fin15AnchoredAtom3526 Fin15AnchoredAtom4217
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

theorem fin15Anchored_clause30920 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom1935 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
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
      ¬Fin15AnchoredAtom3108 chi ∧
      ¬Fin15AnchoredAtom3111 chi ∧
      ¬Fin15AnchoredAtom3112 chi ∧
      ¬Fin15AnchoredAtom3115 chi ∧
      ¬Fin15AnchoredAtom3116 chi ∧
      ¬Fin15AnchoredAtom3122 chi ∧
      ¬Fin15AnchoredAtom3189 chi ∧
      ¬Fin15AnchoredAtom3190 chi ∧
      ¬Fin15AnchoredAtom3196 chi ∧
      ¬Fin15AnchoredAtom3202 chi ∧
      ¬Fin15AnchoredAtom3393 chi ∧
      ¬Fin15AnchoredAtom3394 chi ∧
      ¬Fin15AnchoredAtom3400 chi ∧
      ¬Fin15AnchoredAtom3406 chi ∧
      ¬Fin15AnchoredAtom3527 chi ∧
      ¬Fin15AnchoredAtom4218 chi ∧
      ¬Fin15AnchoredAtom4219 chi ∧
      ¬Fin15AnchoredAtom4225 chi ∧
      ¬Fin15AnchoredAtom4231 chi ∧
      ¬Fin15AnchoredAtom4352 chi ∧
      ¬Fin15AnchoredAtom4688 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 5, 9, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26155
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1900 Fin15AnchoredAtom1901 Fin15AnchoredAtom1904
    Fin15AnchoredAtom1905 Fin15AnchoredAtom1927 Fin15AnchoredAtom1930 Fin15AnchoredAtom1931
    Fin15AnchoredAtom1934 Fin15AnchoredAtom1935 Fin15AnchoredAtom1941 Fin15AnchoredAtom2008
    Fin15AnchoredAtom2011 Fin15AnchoredAtom2012 Fin15AnchoredAtom2015 Fin15AnchoredAtom2016
    Fin15AnchoredAtom2022 Fin15AnchoredAtom2089 Fin15AnchoredAtom2090 Fin15AnchoredAtom2096
    Fin15AnchoredAtom2102 Fin15AnchoredAtom2393 Fin15AnchoredAtom2396 Fin15AnchoredAtom2397
    Fin15AnchoredAtom2400 Fin15AnchoredAtom2401 Fin15AnchoredAtom2407 Fin15AnchoredAtom2474
    Fin15AnchoredAtom2475 Fin15AnchoredAtom2481 Fin15AnchoredAtom2487 Fin15AnchoredAtom2678
    Fin15AnchoredAtom2679 Fin15AnchoredAtom2685 Fin15AnchoredAtom2691 Fin15AnchoredAtom2812
    Fin15AnchoredAtom3108 Fin15AnchoredAtom3111 Fin15AnchoredAtom3112 Fin15AnchoredAtom3115
    Fin15AnchoredAtom3116 Fin15AnchoredAtom3122 Fin15AnchoredAtom3189 Fin15AnchoredAtom3190
    Fin15AnchoredAtom3196 Fin15AnchoredAtom3202 Fin15AnchoredAtom3393 Fin15AnchoredAtom3394
    Fin15AnchoredAtom3400 Fin15AnchoredAtom3406 Fin15AnchoredAtom3527 Fin15AnchoredAtom4218
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

theorem fin15Anchored_clause30921 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom1939 chi ∧
      ¬Fin15AnchoredAtom1940 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
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
      ¬Fin15AnchoredAtom2395 chi ∧
      ¬Fin15AnchoredAtom2396 chi ∧
      ¬Fin15AnchoredAtom2397 chi ∧
      ¬Fin15AnchoredAtom2405 chi ∧
      ¬Fin15AnchoredAtom2406 chi ∧
      ¬Fin15AnchoredAtom2407 chi ∧
      ¬Fin15AnchoredAtom2479 chi ∧
      ¬Fin15AnchoredAtom2480 chi ∧
      ¬Fin15AnchoredAtom2481 chi ∧
      ¬Fin15AnchoredAtom2491 chi ∧
      ¬Fin15AnchoredAtom2683 chi ∧
      ¬Fin15AnchoredAtom2684 chi ∧
      ¬Fin15AnchoredAtom2685 chi ∧
      ¬Fin15AnchoredAtom2695 chi ∧
      ¬Fin15AnchoredAtom2816 chi ∧
      ¬Fin15AnchoredAtom3110 chi ∧
      ¬Fin15AnchoredAtom3111 chi ∧
      ¬Fin15AnchoredAtom3112 chi ∧
      ¬Fin15AnchoredAtom3120 chi ∧
      ¬Fin15AnchoredAtom3121 chi ∧
      ¬Fin15AnchoredAtom3122 chi ∧
      ¬Fin15AnchoredAtom3194 chi ∧
      ¬Fin15AnchoredAtom3195 chi ∧
      ¬Fin15AnchoredAtom3196 chi ∧
      ¬Fin15AnchoredAtom3206 chi ∧
      ¬Fin15AnchoredAtom3398 chi ∧
      ¬Fin15AnchoredAtom3399 chi ∧
      ¬Fin15AnchoredAtom3400 chi ∧
      ¬Fin15AnchoredAtom3410 chi ∧
      ¬Fin15AnchoredAtom3531 chi ∧
      ¬Fin15AnchoredAtom4223 chi ∧
      ¬Fin15AnchoredAtom4224 chi ∧
      ¬Fin15AnchoredAtom4225 chi ∧
      ¬Fin15AnchoredAtom4235 chi ∧
      ¬Fin15AnchoredAtom4356 chi ∧
      ¬Fin15AnchoredAtom4692 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 5, 9, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29227
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1900 Fin15AnchoredAtom1903 Fin15AnchoredAtom1904
    Fin15AnchoredAtom1905 Fin15AnchoredAtom1929 Fin15AnchoredAtom1930 Fin15AnchoredAtom1931
    Fin15AnchoredAtom1939 Fin15AnchoredAtom1940 Fin15AnchoredAtom1941 Fin15AnchoredAtom2010
    Fin15AnchoredAtom2011 Fin15AnchoredAtom2012 Fin15AnchoredAtom2020 Fin15AnchoredAtom2021
    Fin15AnchoredAtom2022 Fin15AnchoredAtom2094 Fin15AnchoredAtom2095 Fin15AnchoredAtom2096
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2395 Fin15AnchoredAtom2396 Fin15AnchoredAtom2397
    Fin15AnchoredAtom2405 Fin15AnchoredAtom2406 Fin15AnchoredAtom2407 Fin15AnchoredAtom2479
    Fin15AnchoredAtom2480 Fin15AnchoredAtom2481 Fin15AnchoredAtom2491 Fin15AnchoredAtom2683
    Fin15AnchoredAtom2684 Fin15AnchoredAtom2685 Fin15AnchoredAtom2695 Fin15AnchoredAtom2816
    Fin15AnchoredAtom3110 Fin15AnchoredAtom3111 Fin15AnchoredAtom3112 Fin15AnchoredAtom3120
    Fin15AnchoredAtom3121 Fin15AnchoredAtom3122 Fin15AnchoredAtom3194 Fin15AnchoredAtom3195
    Fin15AnchoredAtom3196 Fin15AnchoredAtom3206 Fin15AnchoredAtom3398 Fin15AnchoredAtom3399
    Fin15AnchoredAtom3400 Fin15AnchoredAtom3410 Fin15AnchoredAtom3531 Fin15AnchoredAtom4223
    Fin15AnchoredAtom4224 Fin15AnchoredAtom4225 Fin15AnchoredAtom4235 Fin15AnchoredAtom4356
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

theorem fin15Anchored_clause30922 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom1935 chi ∧
      ¬Fin15AnchoredAtom1939 chi ∧
      ¬Fin15AnchoredAtom1940 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
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
      ¬Fin15AnchoredAtom2399 chi ∧
      ¬Fin15AnchoredAtom2400 chi ∧
      ¬Fin15AnchoredAtom2401 chi ∧
      ¬Fin15AnchoredAtom2405 chi ∧
      ¬Fin15AnchoredAtom2406 chi ∧
      ¬Fin15AnchoredAtom2407 chi ∧
      ¬Fin15AnchoredAtom2485 chi ∧
      ¬Fin15AnchoredAtom2486 chi ∧
      ¬Fin15AnchoredAtom2487 chi ∧
      ¬Fin15AnchoredAtom2491 chi ∧
      ¬Fin15AnchoredAtom2689 chi ∧
      ¬Fin15AnchoredAtom2690 chi ∧
      ¬Fin15AnchoredAtom2691 chi ∧
      ¬Fin15AnchoredAtom2695 chi ∧
      ¬Fin15AnchoredAtom2820 chi ∧
      ¬Fin15AnchoredAtom3114 chi ∧
      ¬Fin15AnchoredAtom3115 chi ∧
      ¬Fin15AnchoredAtom3116 chi ∧
      ¬Fin15AnchoredAtom3120 chi ∧
      ¬Fin15AnchoredAtom3121 chi ∧
      ¬Fin15AnchoredAtom3122 chi ∧
      ¬Fin15AnchoredAtom3200 chi ∧
      ¬Fin15AnchoredAtom3201 chi ∧
      ¬Fin15AnchoredAtom3202 chi ∧
      ¬Fin15AnchoredAtom3206 chi ∧
      ¬Fin15AnchoredAtom3404 chi ∧
      ¬Fin15AnchoredAtom3405 chi ∧
      ¬Fin15AnchoredAtom3406 chi ∧
      ¬Fin15AnchoredAtom3410 chi ∧
      ¬Fin15AnchoredAtom3535 chi ∧
      ¬Fin15AnchoredAtom4229 chi ∧
      ¬Fin15AnchoredAtom4230 chi ∧
      ¬Fin15AnchoredAtom4231 chi ∧
      ¬Fin15AnchoredAtom4235 chi ∧
      ¬Fin15AnchoredAtom4360 chi ∧
      ¬Fin15AnchoredAtom4696 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 5, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29739
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1901 Fin15AnchoredAtom1903 Fin15AnchoredAtom1904
    Fin15AnchoredAtom1905 Fin15AnchoredAtom1933 Fin15AnchoredAtom1934 Fin15AnchoredAtom1935
    Fin15AnchoredAtom1939 Fin15AnchoredAtom1940 Fin15AnchoredAtom1941 Fin15AnchoredAtom2014
    Fin15AnchoredAtom2015 Fin15AnchoredAtom2016 Fin15AnchoredAtom2020 Fin15AnchoredAtom2021
    Fin15AnchoredAtom2022 Fin15AnchoredAtom2100 Fin15AnchoredAtom2101 Fin15AnchoredAtom2102
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2399 Fin15AnchoredAtom2400 Fin15AnchoredAtom2401
    Fin15AnchoredAtom2405 Fin15AnchoredAtom2406 Fin15AnchoredAtom2407 Fin15AnchoredAtom2485
    Fin15AnchoredAtom2486 Fin15AnchoredAtom2487 Fin15AnchoredAtom2491 Fin15AnchoredAtom2689
    Fin15AnchoredAtom2690 Fin15AnchoredAtom2691 Fin15AnchoredAtom2695 Fin15AnchoredAtom2820
    Fin15AnchoredAtom3114 Fin15AnchoredAtom3115 Fin15AnchoredAtom3116 Fin15AnchoredAtom3120
    Fin15AnchoredAtom3121 Fin15AnchoredAtom3122 Fin15AnchoredAtom3200 Fin15AnchoredAtom3201
    Fin15AnchoredAtom3202 Fin15AnchoredAtom3206 Fin15AnchoredAtom3404 Fin15AnchoredAtom3405
    Fin15AnchoredAtom3406 Fin15AnchoredAtom3410 Fin15AnchoredAtom3535 Fin15AnchoredAtom4229
    Fin15AnchoredAtom4230 Fin15AnchoredAtom4231 Fin15AnchoredAtom4235 Fin15AnchoredAtom4360
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

theorem fin15Anchored_clause30923 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1907 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1914 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1921 chi ∧
      ¬Fin15AnchoredAtom1922 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
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
      ¬Fin15AnchoredAtom2408 chi ∧
      ¬Fin15AnchoredAtom2409 chi ∧
      ¬Fin15AnchoredAtom2410 chi ∧
      ¬Fin15AnchoredAtom2415 chi ∧
      ¬Fin15AnchoredAtom2416 chi ∧
      ¬Fin15AnchoredAtom2421 chi ∧
      ¬Fin15AnchoredAtom2436 chi ∧
      ¬Fin15AnchoredAtom2437 chi ∧
      ¬Fin15AnchoredAtom2442 chi ∧
      ¬Fin15AnchoredAtom2457 chi ∧
      ¬Fin15AnchoredAtom2696 chi ∧
      ¬Fin15AnchoredAtom2697 chi ∧
      ¬Fin15AnchoredAtom2702 chi ∧
      ¬Fin15AnchoredAtom2717 chi ∧
      ¬Fin15AnchoredAtom2752 chi ∧
      ¬Fin15AnchoredAtom3123 chi ∧
      ¬Fin15AnchoredAtom3124 chi ∧
      ¬Fin15AnchoredAtom3125 chi ∧
      ¬Fin15AnchoredAtom3130 chi ∧
      ¬Fin15AnchoredAtom3131 chi ∧
      ¬Fin15AnchoredAtom3136 chi ∧
      ¬Fin15AnchoredAtom3151 chi ∧
      ¬Fin15AnchoredAtom3152 chi ∧
      ¬Fin15AnchoredAtom3157 chi ∧
      ¬Fin15AnchoredAtom3172 chi ∧
      ¬Fin15AnchoredAtom3411 chi ∧
      ¬Fin15AnchoredAtom3412 chi ∧
      ¬Fin15AnchoredAtom3417 chi ∧
      ¬Fin15AnchoredAtom3432 chi ∧
      ¬Fin15AnchoredAtom3467 chi ∧
      ¬Fin15AnchoredAtom4236 chi ∧
      ¬Fin15AnchoredAtom4237 chi ∧
      ¬Fin15AnchoredAtom4242 chi ∧
      ¬Fin15AnchoredAtom4257 chi ∧
      ¬Fin15AnchoredAtom4292 chi ∧
      ¬Fin15AnchoredAtom4698 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 6, 7, 8, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask01995
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1906 Fin15AnchoredAtom1907 Fin15AnchoredAtom1908
    Fin15AnchoredAtom1909 Fin15AnchoredAtom1914 Fin15AnchoredAtom1915 Fin15AnchoredAtom1916
    Fin15AnchoredAtom1921 Fin15AnchoredAtom1922 Fin15AnchoredAtom1927 Fin15AnchoredAtom2023
    Fin15AnchoredAtom2024 Fin15AnchoredAtom2025 Fin15AnchoredAtom2030 Fin15AnchoredAtom2031
    Fin15AnchoredAtom2036 Fin15AnchoredAtom2051 Fin15AnchoredAtom2052 Fin15AnchoredAtom2057
    Fin15AnchoredAtom2072 Fin15AnchoredAtom2408 Fin15AnchoredAtom2409 Fin15AnchoredAtom2410
    Fin15AnchoredAtom2415 Fin15AnchoredAtom2416 Fin15AnchoredAtom2421 Fin15AnchoredAtom2436
    Fin15AnchoredAtom2437 Fin15AnchoredAtom2442 Fin15AnchoredAtom2457 Fin15AnchoredAtom2696
    Fin15AnchoredAtom2697 Fin15AnchoredAtom2702 Fin15AnchoredAtom2717 Fin15AnchoredAtom2752
    Fin15AnchoredAtom3123 Fin15AnchoredAtom3124 Fin15AnchoredAtom3125 Fin15AnchoredAtom3130
    Fin15AnchoredAtom3131 Fin15AnchoredAtom3136 Fin15AnchoredAtom3151 Fin15AnchoredAtom3152
    Fin15AnchoredAtom3157 Fin15AnchoredAtom3172 Fin15AnchoredAtom3411 Fin15AnchoredAtom3412
    Fin15AnchoredAtom3417 Fin15AnchoredAtom3432 Fin15AnchoredAtom3467 Fin15AnchoredAtom4236
    Fin15AnchoredAtom4237 Fin15AnchoredAtom4242 Fin15AnchoredAtom4257 Fin15AnchoredAtom4292
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

theorem fin15Anchored_clause30924 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1907 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1914 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1921 chi ∧
      ¬Fin15AnchoredAtom1924 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom2023 chi ∧
      ¬Fin15AnchoredAtom2024 chi ∧
      ¬Fin15AnchoredAtom2027 chi ∧
      ¬Fin15AnchoredAtom2030 chi ∧
      ¬Fin15AnchoredAtom2033 chi ∧
      ¬Fin15AnchoredAtom2038 chi ∧
      ¬Fin15AnchoredAtom2051 chi ∧
      ¬Fin15AnchoredAtom2054 chi ∧
      ¬Fin15AnchoredAtom2059 chi ∧
      ¬Fin15AnchoredAtom2074 chi ∧
      ¬Fin15AnchoredAtom2408 chi ∧
      ¬Fin15AnchoredAtom2409 chi ∧
      ¬Fin15AnchoredAtom2412 chi ∧
      ¬Fin15AnchoredAtom2415 chi ∧
      ¬Fin15AnchoredAtom2418 chi ∧
      ¬Fin15AnchoredAtom2423 chi ∧
      ¬Fin15AnchoredAtom2436 chi ∧
      ¬Fin15AnchoredAtom2439 chi ∧
      ¬Fin15AnchoredAtom2444 chi ∧
      ¬Fin15AnchoredAtom2459 chi ∧
      ¬Fin15AnchoredAtom2696 chi ∧
      ¬Fin15AnchoredAtom2699 chi ∧
      ¬Fin15AnchoredAtom2704 chi ∧
      ¬Fin15AnchoredAtom2719 chi ∧
      ¬Fin15AnchoredAtom2754 chi ∧
      ¬Fin15AnchoredAtom3123 chi ∧
      ¬Fin15AnchoredAtom3124 chi ∧
      ¬Fin15AnchoredAtom3127 chi ∧
      ¬Fin15AnchoredAtom3130 chi ∧
      ¬Fin15AnchoredAtom3133 chi ∧
      ¬Fin15AnchoredAtom3138 chi ∧
      ¬Fin15AnchoredAtom3151 chi ∧
      ¬Fin15AnchoredAtom3154 chi ∧
      ¬Fin15AnchoredAtom3159 chi ∧
      ¬Fin15AnchoredAtom3174 chi ∧
      ¬Fin15AnchoredAtom3411 chi ∧
      ¬Fin15AnchoredAtom3414 chi ∧
      ¬Fin15AnchoredAtom3419 chi ∧
      ¬Fin15AnchoredAtom3434 chi ∧
      ¬Fin15AnchoredAtom3469 chi ∧
      ¬Fin15AnchoredAtom4236 chi ∧
      ¬Fin15AnchoredAtom4239 chi ∧
      ¬Fin15AnchoredAtom4244 chi ∧
      ¬Fin15AnchoredAtom4259 chi ∧
      ¬Fin15AnchoredAtom4294 chi ∧
      ¬Fin15AnchoredAtom4700 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 6, 7, 8, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05067
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1906 Fin15AnchoredAtom1907 Fin15AnchoredAtom1908
    Fin15AnchoredAtom1911 Fin15AnchoredAtom1914 Fin15AnchoredAtom1915 Fin15AnchoredAtom1918
    Fin15AnchoredAtom1921 Fin15AnchoredAtom1924 Fin15AnchoredAtom1929 Fin15AnchoredAtom2023
    Fin15AnchoredAtom2024 Fin15AnchoredAtom2027 Fin15AnchoredAtom2030 Fin15AnchoredAtom2033
    Fin15AnchoredAtom2038 Fin15AnchoredAtom2051 Fin15AnchoredAtom2054 Fin15AnchoredAtom2059
    Fin15AnchoredAtom2074 Fin15AnchoredAtom2408 Fin15AnchoredAtom2409 Fin15AnchoredAtom2412
    Fin15AnchoredAtom2415 Fin15AnchoredAtom2418 Fin15AnchoredAtom2423 Fin15AnchoredAtom2436
    Fin15AnchoredAtom2439 Fin15AnchoredAtom2444 Fin15AnchoredAtom2459 Fin15AnchoredAtom2696
    Fin15AnchoredAtom2699 Fin15AnchoredAtom2704 Fin15AnchoredAtom2719 Fin15AnchoredAtom2754
    Fin15AnchoredAtom3123 Fin15AnchoredAtom3124 Fin15AnchoredAtom3127 Fin15AnchoredAtom3130
    Fin15AnchoredAtom3133 Fin15AnchoredAtom3138 Fin15AnchoredAtom3151 Fin15AnchoredAtom3154
    Fin15AnchoredAtom3159 Fin15AnchoredAtom3174 Fin15AnchoredAtom3411 Fin15AnchoredAtom3414
    Fin15AnchoredAtom3419 Fin15AnchoredAtom3434 Fin15AnchoredAtom3469 Fin15AnchoredAtom4236
    Fin15AnchoredAtom4239 Fin15AnchoredAtom4244 Fin15AnchoredAtom4259 Fin15AnchoredAtom4294
    Fin15AnchoredAtom4700 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30925 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1907 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1914 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1921 chi ∧
      ¬Fin15AnchoredAtom1925 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom2023 chi ∧
      ¬Fin15AnchoredAtom2024 chi ∧
      ¬Fin15AnchoredAtom2028 chi ∧
      ¬Fin15AnchoredAtom2030 chi ∧
      ¬Fin15AnchoredAtom2034 chi ∧
      ¬Fin15AnchoredAtom2039 chi ∧
      ¬Fin15AnchoredAtom2051 chi ∧
      ¬Fin15AnchoredAtom2055 chi ∧
      ¬Fin15AnchoredAtom2060 chi ∧
      ¬Fin15AnchoredAtom2075 chi ∧
      ¬Fin15AnchoredAtom2408 chi ∧
      ¬Fin15AnchoredAtom2409 chi ∧
      ¬Fin15AnchoredAtom2413 chi ∧
      ¬Fin15AnchoredAtom2415 chi ∧
      ¬Fin15AnchoredAtom2419 chi ∧
      ¬Fin15AnchoredAtom2424 chi ∧
      ¬Fin15AnchoredAtom2436 chi ∧
      ¬Fin15AnchoredAtom2440 chi ∧
      ¬Fin15AnchoredAtom2445 chi ∧
      ¬Fin15AnchoredAtom2460 chi ∧
      ¬Fin15AnchoredAtom2696 chi ∧
      ¬Fin15AnchoredAtom2700 chi ∧
      ¬Fin15AnchoredAtom2705 chi ∧
      ¬Fin15AnchoredAtom2720 chi ∧
      ¬Fin15AnchoredAtom2755 chi ∧
      ¬Fin15AnchoredAtom3123 chi ∧
      ¬Fin15AnchoredAtom3124 chi ∧
      ¬Fin15AnchoredAtom3128 chi ∧
      ¬Fin15AnchoredAtom3130 chi ∧
      ¬Fin15AnchoredAtom3134 chi ∧
      ¬Fin15AnchoredAtom3139 chi ∧
      ¬Fin15AnchoredAtom3151 chi ∧
      ¬Fin15AnchoredAtom3155 chi ∧
      ¬Fin15AnchoredAtom3160 chi ∧
      ¬Fin15AnchoredAtom3175 chi ∧
      ¬Fin15AnchoredAtom3411 chi ∧
      ¬Fin15AnchoredAtom3415 chi ∧
      ¬Fin15AnchoredAtom3420 chi ∧
      ¬Fin15AnchoredAtom3435 chi ∧
      ¬Fin15AnchoredAtom3470 chi ∧
      ¬Fin15AnchoredAtom4236 chi ∧
      ¬Fin15AnchoredAtom4240 chi ∧
      ¬Fin15AnchoredAtom4245 chi ∧
      ¬Fin15AnchoredAtom4260 chi ∧
      ¬Fin15AnchoredAtom4295 chi ∧
      ¬Fin15AnchoredAtom4701 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 6, 7, 8, 9, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09163
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1906 Fin15AnchoredAtom1907 Fin15AnchoredAtom1908
    Fin15AnchoredAtom1912 Fin15AnchoredAtom1914 Fin15AnchoredAtom1915 Fin15AnchoredAtom1919
    Fin15AnchoredAtom1921 Fin15AnchoredAtom1925 Fin15AnchoredAtom1930 Fin15AnchoredAtom2023
    Fin15AnchoredAtom2024 Fin15AnchoredAtom2028 Fin15AnchoredAtom2030 Fin15AnchoredAtom2034
    Fin15AnchoredAtom2039 Fin15AnchoredAtom2051 Fin15AnchoredAtom2055 Fin15AnchoredAtom2060
    Fin15AnchoredAtom2075 Fin15AnchoredAtom2408 Fin15AnchoredAtom2409 Fin15AnchoredAtom2413
    Fin15AnchoredAtom2415 Fin15AnchoredAtom2419 Fin15AnchoredAtom2424 Fin15AnchoredAtom2436
    Fin15AnchoredAtom2440 Fin15AnchoredAtom2445 Fin15AnchoredAtom2460 Fin15AnchoredAtom2696
    Fin15AnchoredAtom2700 Fin15AnchoredAtom2705 Fin15AnchoredAtom2720 Fin15AnchoredAtom2755
    Fin15AnchoredAtom3123 Fin15AnchoredAtom3124 Fin15AnchoredAtom3128 Fin15AnchoredAtom3130
    Fin15AnchoredAtom3134 Fin15AnchoredAtom3139 Fin15AnchoredAtom3151 Fin15AnchoredAtom3155
    Fin15AnchoredAtom3160 Fin15AnchoredAtom3175 Fin15AnchoredAtom3411 Fin15AnchoredAtom3415
    Fin15AnchoredAtom3420 Fin15AnchoredAtom3435 Fin15AnchoredAtom3470 Fin15AnchoredAtom4236
    Fin15AnchoredAtom4240 Fin15AnchoredAtom4245 Fin15AnchoredAtom4260 Fin15AnchoredAtom4295
    Fin15AnchoredAtom4701 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30926 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1907 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1914 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1921 chi ∧
      ¬Fin15AnchoredAtom1926 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom2023 chi ∧
      ¬Fin15AnchoredAtom2024 chi ∧
      ¬Fin15AnchoredAtom2029 chi ∧
      ¬Fin15AnchoredAtom2030 chi ∧
      ¬Fin15AnchoredAtom2035 chi ∧
      ¬Fin15AnchoredAtom2040 chi ∧
      ¬Fin15AnchoredAtom2051 chi ∧
      ¬Fin15AnchoredAtom2056 chi ∧
      ¬Fin15AnchoredAtom2061 chi ∧
      ¬Fin15AnchoredAtom2076 chi ∧
      ¬Fin15AnchoredAtom2408 chi ∧
      ¬Fin15AnchoredAtom2409 chi ∧
      ¬Fin15AnchoredAtom2414 chi ∧
      ¬Fin15AnchoredAtom2415 chi ∧
      ¬Fin15AnchoredAtom2420 chi ∧
      ¬Fin15AnchoredAtom2425 chi ∧
      ¬Fin15AnchoredAtom2436 chi ∧
      ¬Fin15AnchoredAtom2441 chi ∧
      ¬Fin15AnchoredAtom2446 chi ∧
      ¬Fin15AnchoredAtom2461 chi ∧
      ¬Fin15AnchoredAtom2696 chi ∧
      ¬Fin15AnchoredAtom2701 chi ∧
      ¬Fin15AnchoredAtom2706 chi ∧
      ¬Fin15AnchoredAtom2721 chi ∧
      ¬Fin15AnchoredAtom2756 chi ∧
      ¬Fin15AnchoredAtom3123 chi ∧
      ¬Fin15AnchoredAtom3124 chi ∧
      ¬Fin15AnchoredAtom3129 chi ∧
      ¬Fin15AnchoredAtom3130 chi ∧
      ¬Fin15AnchoredAtom3135 chi ∧
      ¬Fin15AnchoredAtom3140 chi ∧
      ¬Fin15AnchoredAtom3151 chi ∧
      ¬Fin15AnchoredAtom3156 chi ∧
      ¬Fin15AnchoredAtom3161 chi ∧
      ¬Fin15AnchoredAtom3176 chi ∧
      ¬Fin15AnchoredAtom3411 chi ∧
      ¬Fin15AnchoredAtom3416 chi ∧
      ¬Fin15AnchoredAtom3421 chi ∧
      ¬Fin15AnchoredAtom3436 chi ∧
      ¬Fin15AnchoredAtom3471 chi ∧
      ¬Fin15AnchoredAtom4236 chi ∧
      ¬Fin15AnchoredAtom4241 chi ∧
      ¬Fin15AnchoredAtom4246 chi ∧
      ¬Fin15AnchoredAtom4261 chi ∧
      ¬Fin15AnchoredAtom4296 chi ∧
      ¬Fin15AnchoredAtom4702 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 6, 7, 8, 9, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17355
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1906 Fin15AnchoredAtom1907 Fin15AnchoredAtom1908
    Fin15AnchoredAtom1913 Fin15AnchoredAtom1914 Fin15AnchoredAtom1915 Fin15AnchoredAtom1920
    Fin15AnchoredAtom1921 Fin15AnchoredAtom1926 Fin15AnchoredAtom1931 Fin15AnchoredAtom2023
    Fin15AnchoredAtom2024 Fin15AnchoredAtom2029 Fin15AnchoredAtom2030 Fin15AnchoredAtom2035
    Fin15AnchoredAtom2040 Fin15AnchoredAtom2051 Fin15AnchoredAtom2056 Fin15AnchoredAtom2061
    Fin15AnchoredAtom2076 Fin15AnchoredAtom2408 Fin15AnchoredAtom2409 Fin15AnchoredAtom2414
    Fin15AnchoredAtom2415 Fin15AnchoredAtom2420 Fin15AnchoredAtom2425 Fin15AnchoredAtom2436
    Fin15AnchoredAtom2441 Fin15AnchoredAtom2446 Fin15AnchoredAtom2461 Fin15AnchoredAtom2696
    Fin15AnchoredAtom2701 Fin15AnchoredAtom2706 Fin15AnchoredAtom2721 Fin15AnchoredAtom2756
    Fin15AnchoredAtom3123 Fin15AnchoredAtom3124 Fin15AnchoredAtom3129 Fin15AnchoredAtom3130
    Fin15AnchoredAtom3135 Fin15AnchoredAtom3140 Fin15AnchoredAtom3151 Fin15AnchoredAtom3156
    Fin15AnchoredAtom3161 Fin15AnchoredAtom3176 Fin15AnchoredAtom3411 Fin15AnchoredAtom3416
    Fin15AnchoredAtom3421 Fin15AnchoredAtom3436 Fin15AnchoredAtom3471 Fin15AnchoredAtom4236
    Fin15AnchoredAtom4241 Fin15AnchoredAtom4246 Fin15AnchoredAtom4261 Fin15AnchoredAtom4296
    Fin15AnchoredAtom4702 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30927 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1907 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1914 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1922 chi ∧
      ¬Fin15AnchoredAtom1924 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom2023 chi ∧
      ¬Fin15AnchoredAtom2025 chi ∧
      ¬Fin15AnchoredAtom2027 chi ∧
      ¬Fin15AnchoredAtom2031 chi ∧
      ¬Fin15AnchoredAtom2033 chi ∧
      ¬Fin15AnchoredAtom2042 chi ∧
      ¬Fin15AnchoredAtom2052 chi ∧
      ¬Fin15AnchoredAtom2054 chi ∧
      ¬Fin15AnchoredAtom2063 chi ∧
      ¬Fin15AnchoredAtom2078 chi ∧
      ¬Fin15AnchoredAtom2408 chi ∧
      ¬Fin15AnchoredAtom2410 chi ∧
      ¬Fin15AnchoredAtom2412 chi ∧
      ¬Fin15AnchoredAtom2416 chi ∧
      ¬Fin15AnchoredAtom2418 chi ∧
      ¬Fin15AnchoredAtom2427 chi ∧
      ¬Fin15AnchoredAtom2437 chi ∧
      ¬Fin15AnchoredAtom2439 chi ∧
      ¬Fin15AnchoredAtom2448 chi ∧
      ¬Fin15AnchoredAtom2463 chi ∧
      ¬Fin15AnchoredAtom2697 chi ∧
      ¬Fin15AnchoredAtom2699 chi ∧
      ¬Fin15AnchoredAtom2708 chi ∧
      ¬Fin15AnchoredAtom2723 chi ∧
      ¬Fin15AnchoredAtom2758 chi ∧
      ¬Fin15AnchoredAtom3123 chi ∧
      ¬Fin15AnchoredAtom3125 chi ∧
      ¬Fin15AnchoredAtom3127 chi ∧
      ¬Fin15AnchoredAtom3131 chi ∧
      ¬Fin15AnchoredAtom3133 chi ∧
      ¬Fin15AnchoredAtom3142 chi ∧
      ¬Fin15AnchoredAtom3152 chi ∧
      ¬Fin15AnchoredAtom3154 chi ∧
      ¬Fin15AnchoredAtom3163 chi ∧
      ¬Fin15AnchoredAtom3178 chi ∧
      ¬Fin15AnchoredAtom3412 chi ∧
      ¬Fin15AnchoredAtom3414 chi ∧
      ¬Fin15AnchoredAtom3423 chi ∧
      ¬Fin15AnchoredAtom3438 chi ∧
      ¬Fin15AnchoredAtom3473 chi ∧
      ¬Fin15AnchoredAtom4237 chi ∧
      ¬Fin15AnchoredAtom4239 chi ∧
      ¬Fin15AnchoredAtom4248 chi ∧
      ¬Fin15AnchoredAtom4263 chi ∧
      ¬Fin15AnchoredAtom4298 chi ∧
      ¬Fin15AnchoredAtom4704 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 6, 7, 8, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05579
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1906 Fin15AnchoredAtom1907 Fin15AnchoredAtom1909
    Fin15AnchoredAtom1911 Fin15AnchoredAtom1914 Fin15AnchoredAtom1916 Fin15AnchoredAtom1918
    Fin15AnchoredAtom1922 Fin15AnchoredAtom1924 Fin15AnchoredAtom1933 Fin15AnchoredAtom2023
    Fin15AnchoredAtom2025 Fin15AnchoredAtom2027 Fin15AnchoredAtom2031 Fin15AnchoredAtom2033
    Fin15AnchoredAtom2042 Fin15AnchoredAtom2052 Fin15AnchoredAtom2054 Fin15AnchoredAtom2063
    Fin15AnchoredAtom2078 Fin15AnchoredAtom2408 Fin15AnchoredAtom2410 Fin15AnchoredAtom2412
    Fin15AnchoredAtom2416 Fin15AnchoredAtom2418 Fin15AnchoredAtom2427 Fin15AnchoredAtom2437
    Fin15AnchoredAtom2439 Fin15AnchoredAtom2448 Fin15AnchoredAtom2463 Fin15AnchoredAtom2697
    Fin15AnchoredAtom2699 Fin15AnchoredAtom2708 Fin15AnchoredAtom2723 Fin15AnchoredAtom2758
    Fin15AnchoredAtom3123 Fin15AnchoredAtom3125 Fin15AnchoredAtom3127 Fin15AnchoredAtom3131
    Fin15AnchoredAtom3133 Fin15AnchoredAtom3142 Fin15AnchoredAtom3152 Fin15AnchoredAtom3154
    Fin15AnchoredAtom3163 Fin15AnchoredAtom3178 Fin15AnchoredAtom3412 Fin15AnchoredAtom3414
    Fin15AnchoredAtom3423 Fin15AnchoredAtom3438 Fin15AnchoredAtom3473 Fin15AnchoredAtom4237
    Fin15AnchoredAtom4239 Fin15AnchoredAtom4248 Fin15AnchoredAtom4263 Fin15AnchoredAtom4298
    Fin15AnchoredAtom4704 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30928 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1907 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1914 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1922 chi ∧
      ¬Fin15AnchoredAtom1925 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom2023 chi ∧
      ¬Fin15AnchoredAtom2025 chi ∧
      ¬Fin15AnchoredAtom2028 chi ∧
      ¬Fin15AnchoredAtom2031 chi ∧
      ¬Fin15AnchoredAtom2034 chi ∧
      ¬Fin15AnchoredAtom2043 chi ∧
      ¬Fin15AnchoredAtom2052 chi ∧
      ¬Fin15AnchoredAtom2055 chi ∧
      ¬Fin15AnchoredAtom2064 chi ∧
      ¬Fin15AnchoredAtom2079 chi ∧
      ¬Fin15AnchoredAtom2408 chi ∧
      ¬Fin15AnchoredAtom2410 chi ∧
      ¬Fin15AnchoredAtom2413 chi ∧
      ¬Fin15AnchoredAtom2416 chi ∧
      ¬Fin15AnchoredAtom2419 chi ∧
      ¬Fin15AnchoredAtom2428 chi ∧
      ¬Fin15AnchoredAtom2437 chi ∧
      ¬Fin15AnchoredAtom2440 chi ∧
      ¬Fin15AnchoredAtom2449 chi ∧
      ¬Fin15AnchoredAtom2464 chi ∧
      ¬Fin15AnchoredAtom2697 chi ∧
      ¬Fin15AnchoredAtom2700 chi ∧
      ¬Fin15AnchoredAtom2709 chi ∧
      ¬Fin15AnchoredAtom2724 chi ∧
      ¬Fin15AnchoredAtom2759 chi ∧
      ¬Fin15AnchoredAtom3123 chi ∧
      ¬Fin15AnchoredAtom3125 chi ∧
      ¬Fin15AnchoredAtom3128 chi ∧
      ¬Fin15AnchoredAtom3131 chi ∧
      ¬Fin15AnchoredAtom3134 chi ∧
      ¬Fin15AnchoredAtom3143 chi ∧
      ¬Fin15AnchoredAtom3152 chi ∧
      ¬Fin15AnchoredAtom3155 chi ∧
      ¬Fin15AnchoredAtom3164 chi ∧
      ¬Fin15AnchoredAtom3179 chi ∧
      ¬Fin15AnchoredAtom3412 chi ∧
      ¬Fin15AnchoredAtom3415 chi ∧
      ¬Fin15AnchoredAtom3424 chi ∧
      ¬Fin15AnchoredAtom3439 chi ∧
      ¬Fin15AnchoredAtom3474 chi ∧
      ¬Fin15AnchoredAtom4237 chi ∧
      ¬Fin15AnchoredAtom4240 chi ∧
      ¬Fin15AnchoredAtom4249 chi ∧
      ¬Fin15AnchoredAtom4264 chi ∧
      ¬Fin15AnchoredAtom4299 chi ∧
      ¬Fin15AnchoredAtom4705 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 6, 7, 8, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09675
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1906 Fin15AnchoredAtom1907 Fin15AnchoredAtom1909
    Fin15AnchoredAtom1912 Fin15AnchoredAtom1914 Fin15AnchoredAtom1916 Fin15AnchoredAtom1919
    Fin15AnchoredAtom1922 Fin15AnchoredAtom1925 Fin15AnchoredAtom1934 Fin15AnchoredAtom2023
    Fin15AnchoredAtom2025 Fin15AnchoredAtom2028 Fin15AnchoredAtom2031 Fin15AnchoredAtom2034
    Fin15AnchoredAtom2043 Fin15AnchoredAtom2052 Fin15AnchoredAtom2055 Fin15AnchoredAtom2064
    Fin15AnchoredAtom2079 Fin15AnchoredAtom2408 Fin15AnchoredAtom2410 Fin15AnchoredAtom2413
    Fin15AnchoredAtom2416 Fin15AnchoredAtom2419 Fin15AnchoredAtom2428 Fin15AnchoredAtom2437
    Fin15AnchoredAtom2440 Fin15AnchoredAtom2449 Fin15AnchoredAtom2464 Fin15AnchoredAtom2697
    Fin15AnchoredAtom2700 Fin15AnchoredAtom2709 Fin15AnchoredAtom2724 Fin15AnchoredAtom2759
    Fin15AnchoredAtom3123 Fin15AnchoredAtom3125 Fin15AnchoredAtom3128 Fin15AnchoredAtom3131
    Fin15AnchoredAtom3134 Fin15AnchoredAtom3143 Fin15AnchoredAtom3152 Fin15AnchoredAtom3155
    Fin15AnchoredAtom3164 Fin15AnchoredAtom3179 Fin15AnchoredAtom3412 Fin15AnchoredAtom3415
    Fin15AnchoredAtom3424 Fin15AnchoredAtom3439 Fin15AnchoredAtom3474 Fin15AnchoredAtom4237
    Fin15AnchoredAtom4240 Fin15AnchoredAtom4249 Fin15AnchoredAtom4264 Fin15AnchoredAtom4299
    Fin15AnchoredAtom4705 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30929 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1907 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1914 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1922 chi ∧
      ¬Fin15AnchoredAtom1926 chi ∧
      ¬Fin15AnchoredAtom1935 chi ∧
      ¬Fin15AnchoredAtom2023 chi ∧
      ¬Fin15AnchoredAtom2025 chi ∧
      ¬Fin15AnchoredAtom2029 chi ∧
      ¬Fin15AnchoredAtom2031 chi ∧
      ¬Fin15AnchoredAtom2035 chi ∧
      ¬Fin15AnchoredAtom2044 chi ∧
      ¬Fin15AnchoredAtom2052 chi ∧
      ¬Fin15AnchoredAtom2056 chi ∧
      ¬Fin15AnchoredAtom2065 chi ∧
      ¬Fin15AnchoredAtom2080 chi ∧
      ¬Fin15AnchoredAtom2408 chi ∧
      ¬Fin15AnchoredAtom2410 chi ∧
      ¬Fin15AnchoredAtom2414 chi ∧
      ¬Fin15AnchoredAtom2416 chi ∧
      ¬Fin15AnchoredAtom2420 chi ∧
      ¬Fin15AnchoredAtom2429 chi ∧
      ¬Fin15AnchoredAtom2437 chi ∧
      ¬Fin15AnchoredAtom2441 chi ∧
      ¬Fin15AnchoredAtom2450 chi ∧
      ¬Fin15AnchoredAtom2465 chi ∧
      ¬Fin15AnchoredAtom2697 chi ∧
      ¬Fin15AnchoredAtom2701 chi ∧
      ¬Fin15AnchoredAtom2710 chi ∧
      ¬Fin15AnchoredAtom2725 chi ∧
      ¬Fin15AnchoredAtom2760 chi ∧
      ¬Fin15AnchoredAtom3123 chi ∧
      ¬Fin15AnchoredAtom3125 chi ∧
      ¬Fin15AnchoredAtom3129 chi ∧
      ¬Fin15AnchoredAtom3131 chi ∧
      ¬Fin15AnchoredAtom3135 chi ∧
      ¬Fin15AnchoredAtom3144 chi ∧
      ¬Fin15AnchoredAtom3152 chi ∧
      ¬Fin15AnchoredAtom3156 chi ∧
      ¬Fin15AnchoredAtom3165 chi ∧
      ¬Fin15AnchoredAtom3180 chi ∧
      ¬Fin15AnchoredAtom3412 chi ∧
      ¬Fin15AnchoredAtom3416 chi ∧
      ¬Fin15AnchoredAtom3425 chi ∧
      ¬Fin15AnchoredAtom3440 chi ∧
      ¬Fin15AnchoredAtom3475 chi ∧
      ¬Fin15AnchoredAtom4237 chi ∧
      ¬Fin15AnchoredAtom4241 chi ∧
      ¬Fin15AnchoredAtom4250 chi ∧
      ¬Fin15AnchoredAtom4265 chi ∧
      ¬Fin15AnchoredAtom4300 chi ∧
      ¬Fin15AnchoredAtom4706 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 6, 7, 8, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17867
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1906 Fin15AnchoredAtom1907 Fin15AnchoredAtom1909
    Fin15AnchoredAtom1913 Fin15AnchoredAtom1914 Fin15AnchoredAtom1916 Fin15AnchoredAtom1920
    Fin15AnchoredAtom1922 Fin15AnchoredAtom1926 Fin15AnchoredAtom1935 Fin15AnchoredAtom2023
    Fin15AnchoredAtom2025 Fin15AnchoredAtom2029 Fin15AnchoredAtom2031 Fin15AnchoredAtom2035
    Fin15AnchoredAtom2044 Fin15AnchoredAtom2052 Fin15AnchoredAtom2056 Fin15AnchoredAtom2065
    Fin15AnchoredAtom2080 Fin15AnchoredAtom2408 Fin15AnchoredAtom2410 Fin15AnchoredAtom2414
    Fin15AnchoredAtom2416 Fin15AnchoredAtom2420 Fin15AnchoredAtom2429 Fin15AnchoredAtom2437
    Fin15AnchoredAtom2441 Fin15AnchoredAtom2450 Fin15AnchoredAtom2465 Fin15AnchoredAtom2697
    Fin15AnchoredAtom2701 Fin15AnchoredAtom2710 Fin15AnchoredAtom2725 Fin15AnchoredAtom2760
    Fin15AnchoredAtom3123 Fin15AnchoredAtom3125 Fin15AnchoredAtom3129 Fin15AnchoredAtom3131
    Fin15AnchoredAtom3135 Fin15AnchoredAtom3144 Fin15AnchoredAtom3152 Fin15AnchoredAtom3156
    Fin15AnchoredAtom3165 Fin15AnchoredAtom3180 Fin15AnchoredAtom3412 Fin15AnchoredAtom3416
    Fin15AnchoredAtom3425 Fin15AnchoredAtom3440 Fin15AnchoredAtom3475 Fin15AnchoredAtom4237
    Fin15AnchoredAtom4241 Fin15AnchoredAtom4250 Fin15AnchoredAtom4265 Fin15AnchoredAtom4300
    Fin15AnchoredAtom4706 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30930 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1907 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1914 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1924 chi ∧
      ¬Fin15AnchoredAtom1926 chi ∧
      ¬Fin15AnchoredAtom1940 chi ∧
      ¬Fin15AnchoredAtom2023 chi ∧
      ¬Fin15AnchoredAtom2027 chi ∧
      ¬Fin15AnchoredAtom2029 chi ∧
      ¬Fin15AnchoredAtom2033 chi ∧
      ¬Fin15AnchoredAtom2035 chi ∧
      ¬Fin15AnchoredAtom2049 chi ∧
      ¬Fin15AnchoredAtom2054 chi ∧
      ¬Fin15AnchoredAtom2056 chi ∧
      ¬Fin15AnchoredAtom2070 chi ∧
      ¬Fin15AnchoredAtom2085 chi ∧
      ¬Fin15AnchoredAtom2408 chi ∧
      ¬Fin15AnchoredAtom2412 chi ∧
      ¬Fin15AnchoredAtom2414 chi ∧
      ¬Fin15AnchoredAtom2418 chi ∧
      ¬Fin15AnchoredAtom2420 chi ∧
      ¬Fin15AnchoredAtom2434 chi ∧
      ¬Fin15AnchoredAtom2439 chi ∧
      ¬Fin15AnchoredAtom2441 chi ∧
      ¬Fin15AnchoredAtom2455 chi ∧
      ¬Fin15AnchoredAtom2470 chi ∧
      ¬Fin15AnchoredAtom2699 chi ∧
      ¬Fin15AnchoredAtom2701 chi ∧
      ¬Fin15AnchoredAtom2715 chi ∧
      ¬Fin15AnchoredAtom2730 chi ∧
      ¬Fin15AnchoredAtom2765 chi ∧
      ¬Fin15AnchoredAtom3123 chi ∧
      ¬Fin15AnchoredAtom3127 chi ∧
      ¬Fin15AnchoredAtom3129 chi ∧
      ¬Fin15AnchoredAtom3133 chi ∧
      ¬Fin15AnchoredAtom3135 chi ∧
      ¬Fin15AnchoredAtom3149 chi ∧
      ¬Fin15AnchoredAtom3154 chi ∧
      ¬Fin15AnchoredAtom3156 chi ∧
      ¬Fin15AnchoredAtom3170 chi ∧
      ¬Fin15AnchoredAtom3185 chi ∧
      ¬Fin15AnchoredAtom3414 chi ∧
      ¬Fin15AnchoredAtom3416 chi ∧
      ¬Fin15AnchoredAtom3430 chi ∧
      ¬Fin15AnchoredAtom3445 chi ∧
      ¬Fin15AnchoredAtom3480 chi ∧
      ¬Fin15AnchoredAtom4239 chi ∧
      ¬Fin15AnchoredAtom4241 chi ∧
      ¬Fin15AnchoredAtom4255 chi ∧
      ¬Fin15AnchoredAtom4270 chi ∧
      ¬Fin15AnchoredAtom4305 chi ∧
      ¬Fin15AnchoredAtom4711 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 6, 7, 8, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask20939
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1906 Fin15AnchoredAtom1907 Fin15AnchoredAtom1911
    Fin15AnchoredAtom1913 Fin15AnchoredAtom1914 Fin15AnchoredAtom1918 Fin15AnchoredAtom1920
    Fin15AnchoredAtom1924 Fin15AnchoredAtom1926 Fin15AnchoredAtom1940 Fin15AnchoredAtom2023
    Fin15AnchoredAtom2027 Fin15AnchoredAtom2029 Fin15AnchoredAtom2033 Fin15AnchoredAtom2035
    Fin15AnchoredAtom2049 Fin15AnchoredAtom2054 Fin15AnchoredAtom2056 Fin15AnchoredAtom2070
    Fin15AnchoredAtom2085 Fin15AnchoredAtom2408 Fin15AnchoredAtom2412 Fin15AnchoredAtom2414
    Fin15AnchoredAtom2418 Fin15AnchoredAtom2420 Fin15AnchoredAtom2434 Fin15AnchoredAtom2439
    Fin15AnchoredAtom2441 Fin15AnchoredAtom2455 Fin15AnchoredAtom2470 Fin15AnchoredAtom2699
    Fin15AnchoredAtom2701 Fin15AnchoredAtom2715 Fin15AnchoredAtom2730 Fin15AnchoredAtom2765
    Fin15AnchoredAtom3123 Fin15AnchoredAtom3127 Fin15AnchoredAtom3129 Fin15AnchoredAtom3133
    Fin15AnchoredAtom3135 Fin15AnchoredAtom3149 Fin15AnchoredAtom3154 Fin15AnchoredAtom3156
    Fin15AnchoredAtom3170 Fin15AnchoredAtom3185 Fin15AnchoredAtom3414 Fin15AnchoredAtom3416
    Fin15AnchoredAtom3430 Fin15AnchoredAtom3445 Fin15AnchoredAtom3480 Fin15AnchoredAtom4239
    Fin15AnchoredAtom4241 Fin15AnchoredAtom4255 Fin15AnchoredAtom4270 Fin15AnchoredAtom4305
    Fin15AnchoredAtom4711 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30931 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1907 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1914 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1925 chi ∧
      ¬Fin15AnchoredAtom1926 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
      ¬Fin15AnchoredAtom2023 chi ∧
      ¬Fin15AnchoredAtom2028 chi ∧
      ¬Fin15AnchoredAtom2029 chi ∧
      ¬Fin15AnchoredAtom2034 chi ∧
      ¬Fin15AnchoredAtom2035 chi ∧
      ¬Fin15AnchoredAtom2050 chi ∧
      ¬Fin15AnchoredAtom2055 chi ∧
      ¬Fin15AnchoredAtom2056 chi ∧
      ¬Fin15AnchoredAtom2071 chi ∧
      ¬Fin15AnchoredAtom2086 chi ∧
      ¬Fin15AnchoredAtom2408 chi ∧
      ¬Fin15AnchoredAtom2413 chi ∧
      ¬Fin15AnchoredAtom2414 chi ∧
      ¬Fin15AnchoredAtom2419 chi ∧
      ¬Fin15AnchoredAtom2420 chi ∧
      ¬Fin15AnchoredAtom2435 chi ∧
      ¬Fin15AnchoredAtom2440 chi ∧
      ¬Fin15AnchoredAtom2441 chi ∧
      ¬Fin15AnchoredAtom2456 chi ∧
      ¬Fin15AnchoredAtom2471 chi ∧
      ¬Fin15AnchoredAtom2700 chi ∧
      ¬Fin15AnchoredAtom2701 chi ∧
      ¬Fin15AnchoredAtom2716 chi ∧
      ¬Fin15AnchoredAtom2731 chi ∧
      ¬Fin15AnchoredAtom2766 chi ∧
      ¬Fin15AnchoredAtom3123 chi ∧
      ¬Fin15AnchoredAtom3128 chi ∧
      ¬Fin15AnchoredAtom3129 chi ∧
      ¬Fin15AnchoredAtom3134 chi ∧
      ¬Fin15AnchoredAtom3135 chi ∧
      ¬Fin15AnchoredAtom3150 chi ∧
      ¬Fin15AnchoredAtom3155 chi ∧
      ¬Fin15AnchoredAtom3156 chi ∧
      ¬Fin15AnchoredAtom3171 chi ∧
      ¬Fin15AnchoredAtom3186 chi ∧
      ¬Fin15AnchoredAtom3415 chi ∧
      ¬Fin15AnchoredAtom3416 chi ∧
      ¬Fin15AnchoredAtom3431 chi ∧
      ¬Fin15AnchoredAtom3446 chi ∧
      ¬Fin15AnchoredAtom3481 chi ∧
      ¬Fin15AnchoredAtom4240 chi ∧
      ¬Fin15AnchoredAtom4241 chi ∧
      ¬Fin15AnchoredAtom4256 chi ∧
      ¬Fin15AnchoredAtom4271 chi ∧
      ¬Fin15AnchoredAtom4306 chi ∧
      ¬Fin15AnchoredAtom4712 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 6, 7, 8, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25035
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1906 Fin15AnchoredAtom1907 Fin15AnchoredAtom1912
    Fin15AnchoredAtom1913 Fin15AnchoredAtom1914 Fin15AnchoredAtom1919 Fin15AnchoredAtom1920
    Fin15AnchoredAtom1925 Fin15AnchoredAtom1926 Fin15AnchoredAtom1941 Fin15AnchoredAtom2023
    Fin15AnchoredAtom2028 Fin15AnchoredAtom2029 Fin15AnchoredAtom2034 Fin15AnchoredAtom2035
    Fin15AnchoredAtom2050 Fin15AnchoredAtom2055 Fin15AnchoredAtom2056 Fin15AnchoredAtom2071
    Fin15AnchoredAtom2086 Fin15AnchoredAtom2408 Fin15AnchoredAtom2413 Fin15AnchoredAtom2414
    Fin15AnchoredAtom2419 Fin15AnchoredAtom2420 Fin15AnchoredAtom2435 Fin15AnchoredAtom2440
    Fin15AnchoredAtom2441 Fin15AnchoredAtom2456 Fin15AnchoredAtom2471 Fin15AnchoredAtom2700
    Fin15AnchoredAtom2701 Fin15AnchoredAtom2716 Fin15AnchoredAtom2731 Fin15AnchoredAtom2766
    Fin15AnchoredAtom3123 Fin15AnchoredAtom3128 Fin15AnchoredAtom3129 Fin15AnchoredAtom3134
    Fin15AnchoredAtom3135 Fin15AnchoredAtom3150 Fin15AnchoredAtom3155 Fin15AnchoredAtom3156
    Fin15AnchoredAtom3171 Fin15AnchoredAtom3186 Fin15AnchoredAtom3415 Fin15AnchoredAtom3416
    Fin15AnchoredAtom3431 Fin15AnchoredAtom3446 Fin15AnchoredAtom3481 Fin15AnchoredAtom4240
    Fin15AnchoredAtom4241 Fin15AnchoredAtom4256 Fin15AnchoredAtom4271 Fin15AnchoredAtom4306
    Fin15AnchoredAtom4712 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30932 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
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
      ¬Fin15AnchoredAtom2409 chi ∧
      ¬Fin15AnchoredAtom2410 chi ∧
      ¬Fin15AnchoredAtom2412 chi ∧
      ¬Fin15AnchoredAtom2421 chi ∧
      ¬Fin15AnchoredAtom2423 chi ∧
      ¬Fin15AnchoredAtom2427 chi ∧
      ¬Fin15AnchoredAtom2442 chi ∧
      ¬Fin15AnchoredAtom2444 chi ∧
      ¬Fin15AnchoredAtom2448 chi ∧
      ¬Fin15AnchoredAtom2473 chi ∧
      ¬Fin15AnchoredAtom2702 chi ∧
      ¬Fin15AnchoredAtom2704 chi ∧
      ¬Fin15AnchoredAtom2708 chi ∧
      ¬Fin15AnchoredAtom2733 chi ∧
      ¬Fin15AnchoredAtom2768 chi ∧
      ¬Fin15AnchoredAtom3124 chi ∧
      ¬Fin15AnchoredAtom3125 chi ∧
      ¬Fin15AnchoredAtom3127 chi ∧
      ¬Fin15AnchoredAtom3136 chi ∧
      ¬Fin15AnchoredAtom3138 chi ∧
      ¬Fin15AnchoredAtom3142 chi ∧
      ¬Fin15AnchoredAtom3157 chi ∧
      ¬Fin15AnchoredAtom3159 chi ∧
      ¬Fin15AnchoredAtom3163 chi ∧
      ¬Fin15AnchoredAtom3188 chi ∧
      ¬Fin15AnchoredAtom3417 chi ∧
      ¬Fin15AnchoredAtom3419 chi ∧
      ¬Fin15AnchoredAtom3423 chi ∧
      ¬Fin15AnchoredAtom3448 chi ∧
      ¬Fin15AnchoredAtom3483 chi ∧
      ¬Fin15AnchoredAtom4242 chi ∧
      ¬Fin15AnchoredAtom4244 chi ∧
      ¬Fin15AnchoredAtom4248 chi ∧
      ¬Fin15AnchoredAtom4273 chi ∧
      ¬Fin15AnchoredAtom4308 chi ∧
      ¬Fin15AnchoredAtom4714 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 6, 7, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05835
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1906 Fin15AnchoredAtom1908 Fin15AnchoredAtom1909
    Fin15AnchoredAtom1911 Fin15AnchoredAtom1915 Fin15AnchoredAtom1916 Fin15AnchoredAtom1918
    Fin15AnchoredAtom1927 Fin15AnchoredAtom1929 Fin15AnchoredAtom1933 Fin15AnchoredAtom2024
    Fin15AnchoredAtom2025 Fin15AnchoredAtom2027 Fin15AnchoredAtom2036 Fin15AnchoredAtom2038
    Fin15AnchoredAtom2042 Fin15AnchoredAtom2057 Fin15AnchoredAtom2059 Fin15AnchoredAtom2063
    Fin15AnchoredAtom2088 Fin15AnchoredAtom2409 Fin15AnchoredAtom2410 Fin15AnchoredAtom2412
    Fin15AnchoredAtom2421 Fin15AnchoredAtom2423 Fin15AnchoredAtom2427 Fin15AnchoredAtom2442
    Fin15AnchoredAtom2444 Fin15AnchoredAtom2448 Fin15AnchoredAtom2473 Fin15AnchoredAtom2702
    Fin15AnchoredAtom2704 Fin15AnchoredAtom2708 Fin15AnchoredAtom2733 Fin15AnchoredAtom2768
    Fin15AnchoredAtom3124 Fin15AnchoredAtom3125 Fin15AnchoredAtom3127 Fin15AnchoredAtom3136
    Fin15AnchoredAtom3138 Fin15AnchoredAtom3142 Fin15AnchoredAtom3157 Fin15AnchoredAtom3159
    Fin15AnchoredAtom3163 Fin15AnchoredAtom3188 Fin15AnchoredAtom3417 Fin15AnchoredAtom3419
    Fin15AnchoredAtom3423 Fin15AnchoredAtom3448 Fin15AnchoredAtom3483 Fin15AnchoredAtom4242
    Fin15AnchoredAtom4244 Fin15AnchoredAtom4248 Fin15AnchoredAtom4273 Fin15AnchoredAtom4308
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

theorem fin15Anchored_clause30933 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
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
      ¬Fin15AnchoredAtom2409 chi ∧
      ¬Fin15AnchoredAtom2410 chi ∧
      ¬Fin15AnchoredAtom2413 chi ∧
      ¬Fin15AnchoredAtom2421 chi ∧
      ¬Fin15AnchoredAtom2424 chi ∧
      ¬Fin15AnchoredAtom2428 chi ∧
      ¬Fin15AnchoredAtom2442 chi ∧
      ¬Fin15AnchoredAtom2445 chi ∧
      ¬Fin15AnchoredAtom2449 chi ∧
      ¬Fin15AnchoredAtom2474 chi ∧
      ¬Fin15AnchoredAtom2702 chi ∧
      ¬Fin15AnchoredAtom2705 chi ∧
      ¬Fin15AnchoredAtom2709 chi ∧
      ¬Fin15AnchoredAtom2734 chi ∧
      ¬Fin15AnchoredAtom2769 chi ∧
      ¬Fin15AnchoredAtom3124 chi ∧
      ¬Fin15AnchoredAtom3125 chi ∧
      ¬Fin15AnchoredAtom3128 chi ∧
      ¬Fin15AnchoredAtom3136 chi ∧
      ¬Fin15AnchoredAtom3139 chi ∧
      ¬Fin15AnchoredAtom3143 chi ∧
      ¬Fin15AnchoredAtom3157 chi ∧
      ¬Fin15AnchoredAtom3160 chi ∧
      ¬Fin15AnchoredAtom3164 chi ∧
      ¬Fin15AnchoredAtom3189 chi ∧
      ¬Fin15AnchoredAtom3417 chi ∧
      ¬Fin15AnchoredAtom3420 chi ∧
      ¬Fin15AnchoredAtom3424 chi ∧
      ¬Fin15AnchoredAtom3449 chi ∧
      ¬Fin15AnchoredAtom3484 chi ∧
      ¬Fin15AnchoredAtom4242 chi ∧
      ¬Fin15AnchoredAtom4245 chi ∧
      ¬Fin15AnchoredAtom4249 chi ∧
      ¬Fin15AnchoredAtom4274 chi ∧
      ¬Fin15AnchoredAtom4309 chi ∧
      ¬Fin15AnchoredAtom4715 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 6, 7, 9, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09931
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1906 Fin15AnchoredAtom1908 Fin15AnchoredAtom1909
    Fin15AnchoredAtom1912 Fin15AnchoredAtom1915 Fin15AnchoredAtom1916 Fin15AnchoredAtom1919
    Fin15AnchoredAtom1927 Fin15AnchoredAtom1930 Fin15AnchoredAtom1934 Fin15AnchoredAtom2024
    Fin15AnchoredAtom2025 Fin15AnchoredAtom2028 Fin15AnchoredAtom2036 Fin15AnchoredAtom2039
    Fin15AnchoredAtom2043 Fin15AnchoredAtom2057 Fin15AnchoredAtom2060 Fin15AnchoredAtom2064
    Fin15AnchoredAtom2089 Fin15AnchoredAtom2409 Fin15AnchoredAtom2410 Fin15AnchoredAtom2413
    Fin15AnchoredAtom2421 Fin15AnchoredAtom2424 Fin15AnchoredAtom2428 Fin15AnchoredAtom2442
    Fin15AnchoredAtom2445 Fin15AnchoredAtom2449 Fin15AnchoredAtom2474 Fin15AnchoredAtom2702
    Fin15AnchoredAtom2705 Fin15AnchoredAtom2709 Fin15AnchoredAtom2734 Fin15AnchoredAtom2769
    Fin15AnchoredAtom3124 Fin15AnchoredAtom3125 Fin15AnchoredAtom3128 Fin15AnchoredAtom3136
    Fin15AnchoredAtom3139 Fin15AnchoredAtom3143 Fin15AnchoredAtom3157 Fin15AnchoredAtom3160
    Fin15AnchoredAtom3164 Fin15AnchoredAtom3189 Fin15AnchoredAtom3417 Fin15AnchoredAtom3420
    Fin15AnchoredAtom3424 Fin15AnchoredAtom3449 Fin15AnchoredAtom3484 Fin15AnchoredAtom4242
    Fin15AnchoredAtom4245 Fin15AnchoredAtom4249 Fin15AnchoredAtom4274 Fin15AnchoredAtom4309
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

theorem fin15Anchored_clause30934 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom1935 chi ∧
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
      ¬Fin15AnchoredAtom2409 chi ∧
      ¬Fin15AnchoredAtom2410 chi ∧
      ¬Fin15AnchoredAtom2414 chi ∧
      ¬Fin15AnchoredAtom2421 chi ∧
      ¬Fin15AnchoredAtom2425 chi ∧
      ¬Fin15AnchoredAtom2429 chi ∧
      ¬Fin15AnchoredAtom2442 chi ∧
      ¬Fin15AnchoredAtom2446 chi ∧
      ¬Fin15AnchoredAtom2450 chi ∧
      ¬Fin15AnchoredAtom2475 chi ∧
      ¬Fin15AnchoredAtom2702 chi ∧
      ¬Fin15AnchoredAtom2706 chi ∧
      ¬Fin15AnchoredAtom2710 chi ∧
      ¬Fin15AnchoredAtom2735 chi ∧
      ¬Fin15AnchoredAtom2770 chi ∧
      ¬Fin15AnchoredAtom3124 chi ∧
      ¬Fin15AnchoredAtom3125 chi ∧
      ¬Fin15AnchoredAtom3129 chi ∧
      ¬Fin15AnchoredAtom3136 chi ∧
      ¬Fin15AnchoredAtom3140 chi ∧
      ¬Fin15AnchoredAtom3144 chi ∧
      ¬Fin15AnchoredAtom3157 chi ∧
      ¬Fin15AnchoredAtom3161 chi ∧
      ¬Fin15AnchoredAtom3165 chi ∧
      ¬Fin15AnchoredAtom3190 chi ∧
      ¬Fin15AnchoredAtom3417 chi ∧
      ¬Fin15AnchoredAtom3421 chi ∧
      ¬Fin15AnchoredAtom3425 chi ∧
      ¬Fin15AnchoredAtom3450 chi ∧
      ¬Fin15AnchoredAtom3485 chi ∧
      ¬Fin15AnchoredAtom4242 chi ∧
      ¬Fin15AnchoredAtom4246 chi ∧
      ¬Fin15AnchoredAtom4250 chi ∧
      ¬Fin15AnchoredAtom4275 chi ∧
      ¬Fin15AnchoredAtom4310 chi ∧
      ¬Fin15AnchoredAtom4716 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 6, 7, 9, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask18123
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1906 Fin15AnchoredAtom1908 Fin15AnchoredAtom1909
    Fin15AnchoredAtom1913 Fin15AnchoredAtom1915 Fin15AnchoredAtom1916 Fin15AnchoredAtom1920
    Fin15AnchoredAtom1927 Fin15AnchoredAtom1931 Fin15AnchoredAtom1935 Fin15AnchoredAtom2024
    Fin15AnchoredAtom2025 Fin15AnchoredAtom2029 Fin15AnchoredAtom2036 Fin15AnchoredAtom2040
    Fin15AnchoredAtom2044 Fin15AnchoredAtom2057 Fin15AnchoredAtom2061 Fin15AnchoredAtom2065
    Fin15AnchoredAtom2090 Fin15AnchoredAtom2409 Fin15AnchoredAtom2410 Fin15AnchoredAtom2414
    Fin15AnchoredAtom2421 Fin15AnchoredAtom2425 Fin15AnchoredAtom2429 Fin15AnchoredAtom2442
    Fin15AnchoredAtom2446 Fin15AnchoredAtom2450 Fin15AnchoredAtom2475 Fin15AnchoredAtom2702
    Fin15AnchoredAtom2706 Fin15AnchoredAtom2710 Fin15AnchoredAtom2735 Fin15AnchoredAtom2770
    Fin15AnchoredAtom3124 Fin15AnchoredAtom3125 Fin15AnchoredAtom3129 Fin15AnchoredAtom3136
    Fin15AnchoredAtom3140 Fin15AnchoredAtom3144 Fin15AnchoredAtom3157 Fin15AnchoredAtom3161
    Fin15AnchoredAtom3165 Fin15AnchoredAtom3190 Fin15AnchoredAtom3417 Fin15AnchoredAtom3421
    Fin15AnchoredAtom3425 Fin15AnchoredAtom3450 Fin15AnchoredAtom3485 Fin15AnchoredAtom4242
    Fin15AnchoredAtom4246 Fin15AnchoredAtom4250 Fin15AnchoredAtom4275 Fin15AnchoredAtom4310
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

theorem fin15Anchored_clause30935 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1939 chi ∧
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
      ¬Fin15AnchoredAtom2409 chi ∧
      ¬Fin15AnchoredAtom2412 chi ∧
      ¬Fin15AnchoredAtom2413 chi ∧
      ¬Fin15AnchoredAtom2423 chi ∧
      ¬Fin15AnchoredAtom2424 chi ∧
      ¬Fin15AnchoredAtom2433 chi ∧
      ¬Fin15AnchoredAtom2444 chi ∧
      ¬Fin15AnchoredAtom2445 chi ∧
      ¬Fin15AnchoredAtom2454 chi ∧
      ¬Fin15AnchoredAtom2479 chi ∧
      ¬Fin15AnchoredAtom2704 chi ∧
      ¬Fin15AnchoredAtom2705 chi ∧
      ¬Fin15AnchoredAtom2714 chi ∧
      ¬Fin15AnchoredAtom2739 chi ∧
      ¬Fin15AnchoredAtom2774 chi ∧
      ¬Fin15AnchoredAtom3124 chi ∧
      ¬Fin15AnchoredAtom3127 chi ∧
      ¬Fin15AnchoredAtom3128 chi ∧
      ¬Fin15AnchoredAtom3138 chi ∧
      ¬Fin15AnchoredAtom3139 chi ∧
      ¬Fin15AnchoredAtom3148 chi ∧
      ¬Fin15AnchoredAtom3159 chi ∧
      ¬Fin15AnchoredAtom3160 chi ∧
      ¬Fin15AnchoredAtom3169 chi ∧
      ¬Fin15AnchoredAtom3194 chi ∧
      ¬Fin15AnchoredAtom3419 chi ∧
      ¬Fin15AnchoredAtom3420 chi ∧
      ¬Fin15AnchoredAtom3429 chi ∧
      ¬Fin15AnchoredAtom3454 chi ∧
      ¬Fin15AnchoredAtom3489 chi ∧
      ¬Fin15AnchoredAtom4244 chi ∧
      ¬Fin15AnchoredAtom4245 chi ∧
      ¬Fin15AnchoredAtom4254 chi ∧
      ¬Fin15AnchoredAtom4279 chi ∧
      ¬Fin15AnchoredAtom4314 chi ∧
      ¬Fin15AnchoredAtom4720 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 6, 7, 9, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13003
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1906 Fin15AnchoredAtom1908 Fin15AnchoredAtom1911
    Fin15AnchoredAtom1912 Fin15AnchoredAtom1915 Fin15AnchoredAtom1918 Fin15AnchoredAtom1919
    Fin15AnchoredAtom1929 Fin15AnchoredAtom1930 Fin15AnchoredAtom1939 Fin15AnchoredAtom2024
    Fin15AnchoredAtom2027 Fin15AnchoredAtom2028 Fin15AnchoredAtom2038 Fin15AnchoredAtom2039
    Fin15AnchoredAtom2048 Fin15AnchoredAtom2059 Fin15AnchoredAtom2060 Fin15AnchoredAtom2069
    Fin15AnchoredAtom2094 Fin15AnchoredAtom2409 Fin15AnchoredAtom2412 Fin15AnchoredAtom2413
    Fin15AnchoredAtom2423 Fin15AnchoredAtom2424 Fin15AnchoredAtom2433 Fin15AnchoredAtom2444
    Fin15AnchoredAtom2445 Fin15AnchoredAtom2454 Fin15AnchoredAtom2479 Fin15AnchoredAtom2704
    Fin15AnchoredAtom2705 Fin15AnchoredAtom2714 Fin15AnchoredAtom2739 Fin15AnchoredAtom2774
    Fin15AnchoredAtom3124 Fin15AnchoredAtom3127 Fin15AnchoredAtom3128 Fin15AnchoredAtom3138
    Fin15AnchoredAtom3139 Fin15AnchoredAtom3148 Fin15AnchoredAtom3159 Fin15AnchoredAtom3160
    Fin15AnchoredAtom3169 Fin15AnchoredAtom3194 Fin15AnchoredAtom3419 Fin15AnchoredAtom3420
    Fin15AnchoredAtom3429 Fin15AnchoredAtom3454 Fin15AnchoredAtom3489 Fin15AnchoredAtom4244
    Fin15AnchoredAtom4245 Fin15AnchoredAtom4254 Fin15AnchoredAtom4279 Fin15AnchoredAtom4314
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

theorem fin15Anchored_clause30936 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom1940 chi ∧
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
      ¬Fin15AnchoredAtom2409 chi ∧
      ¬Fin15AnchoredAtom2412 chi ∧
      ¬Fin15AnchoredAtom2414 chi ∧
      ¬Fin15AnchoredAtom2423 chi ∧
      ¬Fin15AnchoredAtom2425 chi ∧
      ¬Fin15AnchoredAtom2434 chi ∧
      ¬Fin15AnchoredAtom2444 chi ∧
      ¬Fin15AnchoredAtom2446 chi ∧
      ¬Fin15AnchoredAtom2455 chi ∧
      ¬Fin15AnchoredAtom2480 chi ∧
      ¬Fin15AnchoredAtom2704 chi ∧
      ¬Fin15AnchoredAtom2706 chi ∧
      ¬Fin15AnchoredAtom2715 chi ∧
      ¬Fin15AnchoredAtom2740 chi ∧
      ¬Fin15AnchoredAtom2775 chi ∧
      ¬Fin15AnchoredAtom3124 chi ∧
      ¬Fin15AnchoredAtom3127 chi ∧
      ¬Fin15AnchoredAtom3129 chi ∧
      ¬Fin15AnchoredAtom3138 chi ∧
      ¬Fin15AnchoredAtom3140 chi ∧
      ¬Fin15AnchoredAtom3149 chi ∧
      ¬Fin15AnchoredAtom3159 chi ∧
      ¬Fin15AnchoredAtom3161 chi ∧
      ¬Fin15AnchoredAtom3170 chi ∧
      ¬Fin15AnchoredAtom3195 chi ∧
      ¬Fin15AnchoredAtom3419 chi ∧
      ¬Fin15AnchoredAtom3421 chi ∧
      ¬Fin15AnchoredAtom3430 chi ∧
      ¬Fin15AnchoredAtom3455 chi ∧
      ¬Fin15AnchoredAtom3490 chi ∧
      ¬Fin15AnchoredAtom4244 chi ∧
      ¬Fin15AnchoredAtom4246 chi ∧
      ¬Fin15AnchoredAtom4255 chi ∧
      ¬Fin15AnchoredAtom4280 chi ∧
      ¬Fin15AnchoredAtom4315 chi ∧
      ¬Fin15AnchoredAtom4721 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 6, 7, 9, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21195
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1906 Fin15AnchoredAtom1908 Fin15AnchoredAtom1911
    Fin15AnchoredAtom1913 Fin15AnchoredAtom1915 Fin15AnchoredAtom1918 Fin15AnchoredAtom1920
    Fin15AnchoredAtom1929 Fin15AnchoredAtom1931 Fin15AnchoredAtom1940 Fin15AnchoredAtom2024
    Fin15AnchoredAtom2027 Fin15AnchoredAtom2029 Fin15AnchoredAtom2038 Fin15AnchoredAtom2040
    Fin15AnchoredAtom2049 Fin15AnchoredAtom2059 Fin15AnchoredAtom2061 Fin15AnchoredAtom2070
    Fin15AnchoredAtom2095 Fin15AnchoredAtom2409 Fin15AnchoredAtom2412 Fin15AnchoredAtom2414
    Fin15AnchoredAtom2423 Fin15AnchoredAtom2425 Fin15AnchoredAtom2434 Fin15AnchoredAtom2444
    Fin15AnchoredAtom2446 Fin15AnchoredAtom2455 Fin15AnchoredAtom2480 Fin15AnchoredAtom2704
    Fin15AnchoredAtom2706 Fin15AnchoredAtom2715 Fin15AnchoredAtom2740 Fin15AnchoredAtom2775
    Fin15AnchoredAtom3124 Fin15AnchoredAtom3127 Fin15AnchoredAtom3129 Fin15AnchoredAtom3138
    Fin15AnchoredAtom3140 Fin15AnchoredAtom3149 Fin15AnchoredAtom3159 Fin15AnchoredAtom3161
    Fin15AnchoredAtom3170 Fin15AnchoredAtom3195 Fin15AnchoredAtom3419 Fin15AnchoredAtom3421
    Fin15AnchoredAtom3430 Fin15AnchoredAtom3455 Fin15AnchoredAtom3490 Fin15AnchoredAtom4244
    Fin15AnchoredAtom4246 Fin15AnchoredAtom4255 Fin15AnchoredAtom4280 Fin15AnchoredAtom4315
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

theorem fin15Anchored_clause30937 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
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
      ¬Fin15AnchoredAtom2409 chi ∧
      ¬Fin15AnchoredAtom2413 chi ∧
      ¬Fin15AnchoredAtom2414 chi ∧
      ¬Fin15AnchoredAtom2424 chi ∧
      ¬Fin15AnchoredAtom2425 chi ∧
      ¬Fin15AnchoredAtom2435 chi ∧
      ¬Fin15AnchoredAtom2445 chi ∧
      ¬Fin15AnchoredAtom2446 chi ∧
      ¬Fin15AnchoredAtom2456 chi ∧
      ¬Fin15AnchoredAtom2481 chi ∧
      ¬Fin15AnchoredAtom2705 chi ∧
      ¬Fin15AnchoredAtom2706 chi ∧
      ¬Fin15AnchoredAtom2716 chi ∧
      ¬Fin15AnchoredAtom2741 chi ∧
      ¬Fin15AnchoredAtom2776 chi ∧
      ¬Fin15AnchoredAtom3124 chi ∧
      ¬Fin15AnchoredAtom3128 chi ∧
      ¬Fin15AnchoredAtom3129 chi ∧
      ¬Fin15AnchoredAtom3139 chi ∧
      ¬Fin15AnchoredAtom3140 chi ∧
      ¬Fin15AnchoredAtom3150 chi ∧
      ¬Fin15AnchoredAtom3160 chi ∧
      ¬Fin15AnchoredAtom3161 chi ∧
      ¬Fin15AnchoredAtom3171 chi ∧
      ¬Fin15AnchoredAtom3196 chi ∧
      ¬Fin15AnchoredAtom3420 chi ∧
      ¬Fin15AnchoredAtom3421 chi ∧
      ¬Fin15AnchoredAtom3431 chi ∧
      ¬Fin15AnchoredAtom3456 chi ∧
      ¬Fin15AnchoredAtom3491 chi ∧
      ¬Fin15AnchoredAtom4245 chi ∧
      ¬Fin15AnchoredAtom4246 chi ∧
      ¬Fin15AnchoredAtom4256 chi ∧
      ¬Fin15AnchoredAtom4281 chi ∧
      ¬Fin15AnchoredAtom4316 chi ∧
      ¬Fin15AnchoredAtom4722 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 6, 7, 9, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25291
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1906 Fin15AnchoredAtom1908 Fin15AnchoredAtom1912
    Fin15AnchoredAtom1913 Fin15AnchoredAtom1915 Fin15AnchoredAtom1919 Fin15AnchoredAtom1920
    Fin15AnchoredAtom1930 Fin15AnchoredAtom1931 Fin15AnchoredAtom1941 Fin15AnchoredAtom2024
    Fin15AnchoredAtom2028 Fin15AnchoredAtom2029 Fin15AnchoredAtom2039 Fin15AnchoredAtom2040
    Fin15AnchoredAtom2050 Fin15AnchoredAtom2060 Fin15AnchoredAtom2061 Fin15AnchoredAtom2071
    Fin15AnchoredAtom2096 Fin15AnchoredAtom2409 Fin15AnchoredAtom2413 Fin15AnchoredAtom2414
    Fin15AnchoredAtom2424 Fin15AnchoredAtom2425 Fin15AnchoredAtom2435 Fin15AnchoredAtom2445
    Fin15AnchoredAtom2446 Fin15AnchoredAtom2456 Fin15AnchoredAtom2481 Fin15AnchoredAtom2705
    Fin15AnchoredAtom2706 Fin15AnchoredAtom2716 Fin15AnchoredAtom2741 Fin15AnchoredAtom2776
    Fin15AnchoredAtom3124 Fin15AnchoredAtom3128 Fin15AnchoredAtom3129 Fin15AnchoredAtom3139
    Fin15AnchoredAtom3140 Fin15AnchoredAtom3150 Fin15AnchoredAtom3160 Fin15AnchoredAtom3161
    Fin15AnchoredAtom3171 Fin15AnchoredAtom3196 Fin15AnchoredAtom3420 Fin15AnchoredAtom3421
    Fin15AnchoredAtom3431 Fin15AnchoredAtom3456 Fin15AnchoredAtom3491 Fin15AnchoredAtom4245
    Fin15AnchoredAtom4246 Fin15AnchoredAtom4256 Fin15AnchoredAtom4281 Fin15AnchoredAtom4316
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

theorem fin15Anchored_clause30938 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom1939 chi ∧
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
      ¬Fin15AnchoredAtom2410 chi ∧
      ¬Fin15AnchoredAtom2412 chi ∧
      ¬Fin15AnchoredAtom2413 chi ∧
      ¬Fin15AnchoredAtom2427 chi ∧
      ¬Fin15AnchoredAtom2428 chi ∧
      ¬Fin15AnchoredAtom2433 chi ∧
      ¬Fin15AnchoredAtom2448 chi ∧
      ¬Fin15AnchoredAtom2449 chi ∧
      ¬Fin15AnchoredAtom2454 chi ∧
      ¬Fin15AnchoredAtom2485 chi ∧
      ¬Fin15AnchoredAtom2708 chi ∧
      ¬Fin15AnchoredAtom2709 chi ∧
      ¬Fin15AnchoredAtom2714 chi ∧
      ¬Fin15AnchoredAtom2745 chi ∧
      ¬Fin15AnchoredAtom2780 chi ∧
      ¬Fin15AnchoredAtom3125 chi ∧
      ¬Fin15AnchoredAtom3127 chi ∧
      ¬Fin15AnchoredAtom3128 chi ∧
      ¬Fin15AnchoredAtom3142 chi ∧
      ¬Fin15AnchoredAtom3143 chi ∧
      ¬Fin15AnchoredAtom3148 chi ∧
      ¬Fin15AnchoredAtom3163 chi ∧
      ¬Fin15AnchoredAtom3164 chi ∧
      ¬Fin15AnchoredAtom3169 chi ∧
      ¬Fin15AnchoredAtom3200 chi ∧
      ¬Fin15AnchoredAtom3423 chi ∧
      ¬Fin15AnchoredAtom3424 chi ∧
      ¬Fin15AnchoredAtom3429 chi ∧
      ¬Fin15AnchoredAtom3460 chi ∧
      ¬Fin15AnchoredAtom3495 chi ∧
      ¬Fin15AnchoredAtom4248 chi ∧
      ¬Fin15AnchoredAtom4249 chi ∧
      ¬Fin15AnchoredAtom4254 chi ∧
      ¬Fin15AnchoredAtom4285 chi ∧
      ¬Fin15AnchoredAtom4320 chi ∧
      ¬Fin15AnchoredAtom4726 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 6, 7, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13515
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1906 Fin15AnchoredAtom1909 Fin15AnchoredAtom1911
    Fin15AnchoredAtom1912 Fin15AnchoredAtom1916 Fin15AnchoredAtom1918 Fin15AnchoredAtom1919
    Fin15AnchoredAtom1933 Fin15AnchoredAtom1934 Fin15AnchoredAtom1939 Fin15AnchoredAtom2025
    Fin15AnchoredAtom2027 Fin15AnchoredAtom2028 Fin15AnchoredAtom2042 Fin15AnchoredAtom2043
    Fin15AnchoredAtom2048 Fin15AnchoredAtom2063 Fin15AnchoredAtom2064 Fin15AnchoredAtom2069
    Fin15AnchoredAtom2100 Fin15AnchoredAtom2410 Fin15AnchoredAtom2412 Fin15AnchoredAtom2413
    Fin15AnchoredAtom2427 Fin15AnchoredAtom2428 Fin15AnchoredAtom2433 Fin15AnchoredAtom2448
    Fin15AnchoredAtom2449 Fin15AnchoredAtom2454 Fin15AnchoredAtom2485 Fin15AnchoredAtom2708
    Fin15AnchoredAtom2709 Fin15AnchoredAtom2714 Fin15AnchoredAtom2745 Fin15AnchoredAtom2780
    Fin15AnchoredAtom3125 Fin15AnchoredAtom3127 Fin15AnchoredAtom3128 Fin15AnchoredAtom3142
    Fin15AnchoredAtom3143 Fin15AnchoredAtom3148 Fin15AnchoredAtom3163 Fin15AnchoredAtom3164
    Fin15AnchoredAtom3169 Fin15AnchoredAtom3200 Fin15AnchoredAtom3423 Fin15AnchoredAtom3424
    Fin15AnchoredAtom3429 Fin15AnchoredAtom3460 Fin15AnchoredAtom3495 Fin15AnchoredAtom4248
    Fin15AnchoredAtom4249 Fin15AnchoredAtom4254 Fin15AnchoredAtom4285 Fin15AnchoredAtom4320
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

theorem fin15Anchored_clause30939 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom1935 chi ∧
      ¬Fin15AnchoredAtom1940 chi ∧
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
      ¬Fin15AnchoredAtom2410 chi ∧
      ¬Fin15AnchoredAtom2412 chi ∧
      ¬Fin15AnchoredAtom2414 chi ∧
      ¬Fin15AnchoredAtom2427 chi ∧
      ¬Fin15AnchoredAtom2429 chi ∧
      ¬Fin15AnchoredAtom2434 chi ∧
      ¬Fin15AnchoredAtom2448 chi ∧
      ¬Fin15AnchoredAtom2450 chi ∧
      ¬Fin15AnchoredAtom2455 chi ∧
      ¬Fin15AnchoredAtom2486 chi ∧
      ¬Fin15AnchoredAtom2708 chi ∧
      ¬Fin15AnchoredAtom2710 chi ∧
      ¬Fin15AnchoredAtom2715 chi ∧
      ¬Fin15AnchoredAtom2746 chi ∧
      ¬Fin15AnchoredAtom2781 chi ∧
      ¬Fin15AnchoredAtom3125 chi ∧
      ¬Fin15AnchoredAtom3127 chi ∧
      ¬Fin15AnchoredAtom3129 chi ∧
      ¬Fin15AnchoredAtom3142 chi ∧
      ¬Fin15AnchoredAtom3144 chi ∧
      ¬Fin15AnchoredAtom3149 chi ∧
      ¬Fin15AnchoredAtom3163 chi ∧
      ¬Fin15AnchoredAtom3165 chi ∧
      ¬Fin15AnchoredAtom3170 chi ∧
      ¬Fin15AnchoredAtom3201 chi ∧
      ¬Fin15AnchoredAtom3423 chi ∧
      ¬Fin15AnchoredAtom3425 chi ∧
      ¬Fin15AnchoredAtom3430 chi ∧
      ¬Fin15AnchoredAtom3461 chi ∧
      ¬Fin15AnchoredAtom3496 chi ∧
      ¬Fin15AnchoredAtom4248 chi ∧
      ¬Fin15AnchoredAtom4250 chi ∧
      ¬Fin15AnchoredAtom4255 chi ∧
      ¬Fin15AnchoredAtom4286 chi ∧
      ¬Fin15AnchoredAtom4321 chi ∧
      ¬Fin15AnchoredAtom4727 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 6, 7, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21707
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1906 Fin15AnchoredAtom1909 Fin15AnchoredAtom1911
    Fin15AnchoredAtom1913 Fin15AnchoredAtom1916 Fin15AnchoredAtom1918 Fin15AnchoredAtom1920
    Fin15AnchoredAtom1933 Fin15AnchoredAtom1935 Fin15AnchoredAtom1940 Fin15AnchoredAtom2025
    Fin15AnchoredAtom2027 Fin15AnchoredAtom2029 Fin15AnchoredAtom2042 Fin15AnchoredAtom2044
    Fin15AnchoredAtom2049 Fin15AnchoredAtom2063 Fin15AnchoredAtom2065 Fin15AnchoredAtom2070
    Fin15AnchoredAtom2101 Fin15AnchoredAtom2410 Fin15AnchoredAtom2412 Fin15AnchoredAtom2414
    Fin15AnchoredAtom2427 Fin15AnchoredAtom2429 Fin15AnchoredAtom2434 Fin15AnchoredAtom2448
    Fin15AnchoredAtom2450 Fin15AnchoredAtom2455 Fin15AnchoredAtom2486 Fin15AnchoredAtom2708
    Fin15AnchoredAtom2710 Fin15AnchoredAtom2715 Fin15AnchoredAtom2746 Fin15AnchoredAtom2781
    Fin15AnchoredAtom3125 Fin15AnchoredAtom3127 Fin15AnchoredAtom3129 Fin15AnchoredAtom3142
    Fin15AnchoredAtom3144 Fin15AnchoredAtom3149 Fin15AnchoredAtom3163 Fin15AnchoredAtom3165
    Fin15AnchoredAtom3170 Fin15AnchoredAtom3201 Fin15AnchoredAtom3423 Fin15AnchoredAtom3425
    Fin15AnchoredAtom3430 Fin15AnchoredAtom3461 Fin15AnchoredAtom3496 Fin15AnchoredAtom4248
    Fin15AnchoredAtom4250 Fin15AnchoredAtom4255 Fin15AnchoredAtom4286 Fin15AnchoredAtom4321
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

theorem fin15Anchored_clause30940 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom1935 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
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
      ¬Fin15AnchoredAtom2410 chi ∧
      ¬Fin15AnchoredAtom2413 chi ∧
      ¬Fin15AnchoredAtom2414 chi ∧
      ¬Fin15AnchoredAtom2428 chi ∧
      ¬Fin15AnchoredAtom2429 chi ∧
      ¬Fin15AnchoredAtom2435 chi ∧
      ¬Fin15AnchoredAtom2449 chi ∧
      ¬Fin15AnchoredAtom2450 chi ∧
      ¬Fin15AnchoredAtom2456 chi ∧
      ¬Fin15AnchoredAtom2487 chi ∧
      ¬Fin15AnchoredAtom2709 chi ∧
      ¬Fin15AnchoredAtom2710 chi ∧
      ¬Fin15AnchoredAtom2716 chi ∧
      ¬Fin15AnchoredAtom2747 chi ∧
      ¬Fin15AnchoredAtom2782 chi ∧
      ¬Fin15AnchoredAtom3125 chi ∧
      ¬Fin15AnchoredAtom3128 chi ∧
      ¬Fin15AnchoredAtom3129 chi ∧
      ¬Fin15AnchoredAtom3143 chi ∧
      ¬Fin15AnchoredAtom3144 chi ∧
      ¬Fin15AnchoredAtom3150 chi ∧
      ¬Fin15AnchoredAtom3164 chi ∧
      ¬Fin15AnchoredAtom3165 chi ∧
      ¬Fin15AnchoredAtom3171 chi ∧
      ¬Fin15AnchoredAtom3202 chi ∧
      ¬Fin15AnchoredAtom3424 chi ∧
      ¬Fin15AnchoredAtom3425 chi ∧
      ¬Fin15AnchoredAtom3431 chi ∧
      ¬Fin15AnchoredAtom3462 chi ∧
      ¬Fin15AnchoredAtom3497 chi ∧
      ¬Fin15AnchoredAtom4249 chi ∧
      ¬Fin15AnchoredAtom4250 chi ∧
      ¬Fin15AnchoredAtom4256 chi ∧
      ¬Fin15AnchoredAtom4287 chi ∧
      ¬Fin15AnchoredAtom4322 chi ∧
      ¬Fin15AnchoredAtom4728 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 6, 7, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25803
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1906 Fin15AnchoredAtom1909 Fin15AnchoredAtom1912
    Fin15AnchoredAtom1913 Fin15AnchoredAtom1916 Fin15AnchoredAtom1919 Fin15AnchoredAtom1920
    Fin15AnchoredAtom1934 Fin15AnchoredAtom1935 Fin15AnchoredAtom1941 Fin15AnchoredAtom2025
    Fin15AnchoredAtom2028 Fin15AnchoredAtom2029 Fin15AnchoredAtom2043 Fin15AnchoredAtom2044
    Fin15AnchoredAtom2050 Fin15AnchoredAtom2064 Fin15AnchoredAtom2065 Fin15AnchoredAtom2071
    Fin15AnchoredAtom2102 Fin15AnchoredAtom2410 Fin15AnchoredAtom2413 Fin15AnchoredAtom2414
    Fin15AnchoredAtom2428 Fin15AnchoredAtom2429 Fin15AnchoredAtom2435 Fin15AnchoredAtom2449
    Fin15AnchoredAtom2450 Fin15AnchoredAtom2456 Fin15AnchoredAtom2487 Fin15AnchoredAtom2709
    Fin15AnchoredAtom2710 Fin15AnchoredAtom2716 Fin15AnchoredAtom2747 Fin15AnchoredAtom2782
    Fin15AnchoredAtom3125 Fin15AnchoredAtom3128 Fin15AnchoredAtom3129 Fin15AnchoredAtom3143
    Fin15AnchoredAtom3144 Fin15AnchoredAtom3150 Fin15AnchoredAtom3164 Fin15AnchoredAtom3165
    Fin15AnchoredAtom3171 Fin15AnchoredAtom3202 Fin15AnchoredAtom3424 Fin15AnchoredAtom3425
    Fin15AnchoredAtom3431 Fin15AnchoredAtom3462 Fin15AnchoredAtom3497 Fin15AnchoredAtom4249
    Fin15AnchoredAtom4250 Fin15AnchoredAtom4256 Fin15AnchoredAtom4287 Fin15AnchoredAtom4322
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

theorem fin15Anchored_clause30941 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1939 chi ∧
      ¬Fin15AnchoredAtom1940 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
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
      ¬Fin15AnchoredAtom2412 chi ∧
      ¬Fin15AnchoredAtom2413 chi ∧
      ¬Fin15AnchoredAtom2414 chi ∧
      ¬Fin15AnchoredAtom2433 chi ∧
      ¬Fin15AnchoredAtom2434 chi ∧
      ¬Fin15AnchoredAtom2435 chi ∧
      ¬Fin15AnchoredAtom2454 chi ∧
      ¬Fin15AnchoredAtom2455 chi ∧
      ¬Fin15AnchoredAtom2456 chi ∧
      ¬Fin15AnchoredAtom2491 chi ∧
      ¬Fin15AnchoredAtom2714 chi ∧
      ¬Fin15AnchoredAtom2715 chi ∧
      ¬Fin15AnchoredAtom2716 chi ∧
      ¬Fin15AnchoredAtom2751 chi ∧
      ¬Fin15AnchoredAtom2786 chi ∧
      ¬Fin15AnchoredAtom3127 chi ∧
      ¬Fin15AnchoredAtom3128 chi ∧
      ¬Fin15AnchoredAtom3129 chi ∧
      ¬Fin15AnchoredAtom3148 chi ∧
      ¬Fin15AnchoredAtom3149 chi ∧
      ¬Fin15AnchoredAtom3150 chi ∧
      ¬Fin15AnchoredAtom3169 chi ∧
      ¬Fin15AnchoredAtom3170 chi ∧
      ¬Fin15AnchoredAtom3171 chi ∧
      ¬Fin15AnchoredAtom3206 chi ∧
      ¬Fin15AnchoredAtom3429 chi ∧
      ¬Fin15AnchoredAtom3430 chi ∧
      ¬Fin15AnchoredAtom3431 chi ∧
      ¬Fin15AnchoredAtom3466 chi ∧
      ¬Fin15AnchoredAtom3501 chi ∧
      ¬Fin15AnchoredAtom4254 chi ∧
      ¬Fin15AnchoredAtom4255 chi ∧
      ¬Fin15AnchoredAtom4256 chi ∧
      ¬Fin15AnchoredAtom4291 chi ∧
      ¬Fin15AnchoredAtom4326 chi ∧
      ¬Fin15AnchoredAtom4732 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 6, 7, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask28875
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1906 Fin15AnchoredAtom1911 Fin15AnchoredAtom1912
    Fin15AnchoredAtom1913 Fin15AnchoredAtom1918 Fin15AnchoredAtom1919 Fin15AnchoredAtom1920
    Fin15AnchoredAtom1939 Fin15AnchoredAtom1940 Fin15AnchoredAtom1941 Fin15AnchoredAtom2027
    Fin15AnchoredAtom2028 Fin15AnchoredAtom2029 Fin15AnchoredAtom2048 Fin15AnchoredAtom2049
    Fin15AnchoredAtom2050 Fin15AnchoredAtom2069 Fin15AnchoredAtom2070 Fin15AnchoredAtom2071
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2412 Fin15AnchoredAtom2413 Fin15AnchoredAtom2414
    Fin15AnchoredAtom2433 Fin15AnchoredAtom2434 Fin15AnchoredAtom2435 Fin15AnchoredAtom2454
    Fin15AnchoredAtom2455 Fin15AnchoredAtom2456 Fin15AnchoredAtom2491 Fin15AnchoredAtom2714
    Fin15AnchoredAtom2715 Fin15AnchoredAtom2716 Fin15AnchoredAtom2751 Fin15AnchoredAtom2786
    Fin15AnchoredAtom3127 Fin15AnchoredAtom3128 Fin15AnchoredAtom3129 Fin15AnchoredAtom3148
    Fin15AnchoredAtom3149 Fin15AnchoredAtom3150 Fin15AnchoredAtom3169 Fin15AnchoredAtom3170
    Fin15AnchoredAtom3171 Fin15AnchoredAtom3206 Fin15AnchoredAtom3429 Fin15AnchoredAtom3430
    Fin15AnchoredAtom3431 Fin15AnchoredAtom3466 Fin15AnchoredAtom3501 Fin15AnchoredAtom4254
    Fin15AnchoredAtom4255 Fin15AnchoredAtom4256 Fin15AnchoredAtom4291 Fin15AnchoredAtom4326
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

theorem fin15Anchored_clause30942 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1907 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1921 chi ∧
      ¬Fin15AnchoredAtom1922 chi ∧
      ¬Fin15AnchoredAtom1924 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom2030 chi ∧
      ¬Fin15AnchoredAtom2031 chi ∧
      ¬Fin15AnchoredAtom2033 chi ∧
      ¬Fin15AnchoredAtom2036 chi ∧
      ¬Fin15AnchoredAtom2038 chi ∧
      ¬Fin15AnchoredAtom2042 chi ∧
      ¬Fin15AnchoredAtom2072 chi ∧
      ¬Fin15AnchoredAtom2074 chi ∧
      ¬Fin15AnchoredAtom2078 chi ∧
      ¬Fin15AnchoredAtom2088 chi ∧
      ¬Fin15AnchoredAtom2415 chi ∧
      ¬Fin15AnchoredAtom2416 chi ∧
      ¬Fin15AnchoredAtom2418 chi ∧
      ¬Fin15AnchoredAtom2421 chi ∧
      ¬Fin15AnchoredAtom2423 chi ∧
      ¬Fin15AnchoredAtom2427 chi ∧
      ¬Fin15AnchoredAtom2457 chi ∧
      ¬Fin15AnchoredAtom2459 chi ∧
      ¬Fin15AnchoredAtom2463 chi ∧
      ¬Fin15AnchoredAtom2473 chi ∧
      ¬Fin15AnchoredAtom2717 chi ∧
      ¬Fin15AnchoredAtom2719 chi ∧
      ¬Fin15AnchoredAtom2723 chi ∧
      ¬Fin15AnchoredAtom2733 chi ∧
      ¬Fin15AnchoredAtom2788 chi ∧
      ¬Fin15AnchoredAtom3130 chi ∧
      ¬Fin15AnchoredAtom3131 chi ∧
      ¬Fin15AnchoredAtom3133 chi ∧
      ¬Fin15AnchoredAtom3136 chi ∧
      ¬Fin15AnchoredAtom3138 chi ∧
      ¬Fin15AnchoredAtom3142 chi ∧
      ¬Fin15AnchoredAtom3172 chi ∧
      ¬Fin15AnchoredAtom3174 chi ∧
      ¬Fin15AnchoredAtom3178 chi ∧
      ¬Fin15AnchoredAtom3188 chi ∧
      ¬Fin15AnchoredAtom3432 chi ∧
      ¬Fin15AnchoredAtom3434 chi ∧
      ¬Fin15AnchoredAtom3438 chi ∧
      ¬Fin15AnchoredAtom3448 chi ∧
      ¬Fin15AnchoredAtom3503 chi ∧
      ¬Fin15AnchoredAtom4257 chi ∧
      ¬Fin15AnchoredAtom4259 chi ∧
      ¬Fin15AnchoredAtom4263 chi ∧
      ¬Fin15AnchoredAtom4273 chi ∧
      ¬Fin15AnchoredAtom4328 chi ∧
      ¬Fin15AnchoredAtom4734 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 6, 8, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05963
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1907 Fin15AnchoredAtom1908 Fin15AnchoredAtom1909
    Fin15AnchoredAtom1911 Fin15AnchoredAtom1921 Fin15AnchoredAtom1922 Fin15AnchoredAtom1924
    Fin15AnchoredAtom1927 Fin15AnchoredAtom1929 Fin15AnchoredAtom1933 Fin15AnchoredAtom2030
    Fin15AnchoredAtom2031 Fin15AnchoredAtom2033 Fin15AnchoredAtom2036 Fin15AnchoredAtom2038
    Fin15AnchoredAtom2042 Fin15AnchoredAtom2072 Fin15AnchoredAtom2074 Fin15AnchoredAtom2078
    Fin15AnchoredAtom2088 Fin15AnchoredAtom2415 Fin15AnchoredAtom2416 Fin15AnchoredAtom2418
    Fin15AnchoredAtom2421 Fin15AnchoredAtom2423 Fin15AnchoredAtom2427 Fin15AnchoredAtom2457
    Fin15AnchoredAtom2459 Fin15AnchoredAtom2463 Fin15AnchoredAtom2473 Fin15AnchoredAtom2717
    Fin15AnchoredAtom2719 Fin15AnchoredAtom2723 Fin15AnchoredAtom2733 Fin15AnchoredAtom2788
    Fin15AnchoredAtom3130 Fin15AnchoredAtom3131 Fin15AnchoredAtom3133 Fin15AnchoredAtom3136
    Fin15AnchoredAtom3138 Fin15AnchoredAtom3142 Fin15AnchoredAtom3172 Fin15AnchoredAtom3174
    Fin15AnchoredAtom3178 Fin15AnchoredAtom3188 Fin15AnchoredAtom3432 Fin15AnchoredAtom3434
    Fin15AnchoredAtom3438 Fin15AnchoredAtom3448 Fin15AnchoredAtom3503 Fin15AnchoredAtom4257
    Fin15AnchoredAtom4259 Fin15AnchoredAtom4263 Fin15AnchoredAtom4273 Fin15AnchoredAtom4328
    Fin15AnchoredAtom4734 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30943 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1907 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1921 chi ∧
      ¬Fin15AnchoredAtom1922 chi ∧
      ¬Fin15AnchoredAtom1925 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom2030 chi ∧
      ¬Fin15AnchoredAtom2031 chi ∧
      ¬Fin15AnchoredAtom2034 chi ∧
      ¬Fin15AnchoredAtom2036 chi ∧
      ¬Fin15AnchoredAtom2039 chi ∧
      ¬Fin15AnchoredAtom2043 chi ∧
      ¬Fin15AnchoredAtom2072 chi ∧
      ¬Fin15AnchoredAtom2075 chi ∧
      ¬Fin15AnchoredAtom2079 chi ∧
      ¬Fin15AnchoredAtom2089 chi ∧
      ¬Fin15AnchoredAtom2415 chi ∧
      ¬Fin15AnchoredAtom2416 chi ∧
      ¬Fin15AnchoredAtom2419 chi ∧
      ¬Fin15AnchoredAtom2421 chi ∧
      ¬Fin15AnchoredAtom2424 chi ∧
      ¬Fin15AnchoredAtom2428 chi ∧
      ¬Fin15AnchoredAtom2457 chi ∧
      ¬Fin15AnchoredAtom2460 chi ∧
      ¬Fin15AnchoredAtom2464 chi ∧
      ¬Fin15AnchoredAtom2474 chi ∧
      ¬Fin15AnchoredAtom2717 chi ∧
      ¬Fin15AnchoredAtom2720 chi ∧
      ¬Fin15AnchoredAtom2724 chi ∧
      ¬Fin15AnchoredAtom2734 chi ∧
      ¬Fin15AnchoredAtom2789 chi ∧
      ¬Fin15AnchoredAtom3130 chi ∧
      ¬Fin15AnchoredAtom3131 chi ∧
      ¬Fin15AnchoredAtom3134 chi ∧
      ¬Fin15AnchoredAtom3136 chi ∧
      ¬Fin15AnchoredAtom3139 chi ∧
      ¬Fin15AnchoredAtom3143 chi ∧
      ¬Fin15AnchoredAtom3172 chi ∧
      ¬Fin15AnchoredAtom3175 chi ∧
      ¬Fin15AnchoredAtom3179 chi ∧
      ¬Fin15AnchoredAtom3189 chi ∧
      ¬Fin15AnchoredAtom3432 chi ∧
      ¬Fin15AnchoredAtom3435 chi ∧
      ¬Fin15AnchoredAtom3439 chi ∧
      ¬Fin15AnchoredAtom3449 chi ∧
      ¬Fin15AnchoredAtom3504 chi ∧
      ¬Fin15AnchoredAtom4257 chi ∧
      ¬Fin15AnchoredAtom4260 chi ∧
      ¬Fin15AnchoredAtom4264 chi ∧
      ¬Fin15AnchoredAtom4274 chi ∧
      ¬Fin15AnchoredAtom4329 chi ∧
      ¬Fin15AnchoredAtom4735 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 6, 8, 9, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask10059
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1907 Fin15AnchoredAtom1908 Fin15AnchoredAtom1909
    Fin15AnchoredAtom1912 Fin15AnchoredAtom1921 Fin15AnchoredAtom1922 Fin15AnchoredAtom1925
    Fin15AnchoredAtom1927 Fin15AnchoredAtom1930 Fin15AnchoredAtom1934 Fin15AnchoredAtom2030
    Fin15AnchoredAtom2031 Fin15AnchoredAtom2034 Fin15AnchoredAtom2036 Fin15AnchoredAtom2039
    Fin15AnchoredAtom2043 Fin15AnchoredAtom2072 Fin15AnchoredAtom2075 Fin15AnchoredAtom2079
    Fin15AnchoredAtom2089 Fin15AnchoredAtom2415 Fin15AnchoredAtom2416 Fin15AnchoredAtom2419
    Fin15AnchoredAtom2421 Fin15AnchoredAtom2424 Fin15AnchoredAtom2428 Fin15AnchoredAtom2457
    Fin15AnchoredAtom2460 Fin15AnchoredAtom2464 Fin15AnchoredAtom2474 Fin15AnchoredAtom2717
    Fin15AnchoredAtom2720 Fin15AnchoredAtom2724 Fin15AnchoredAtom2734 Fin15AnchoredAtom2789
    Fin15AnchoredAtom3130 Fin15AnchoredAtom3131 Fin15AnchoredAtom3134 Fin15AnchoredAtom3136
    Fin15AnchoredAtom3139 Fin15AnchoredAtom3143 Fin15AnchoredAtom3172 Fin15AnchoredAtom3175
    Fin15AnchoredAtom3179 Fin15AnchoredAtom3189 Fin15AnchoredAtom3432 Fin15AnchoredAtom3435
    Fin15AnchoredAtom3439 Fin15AnchoredAtom3449 Fin15AnchoredAtom3504 Fin15AnchoredAtom4257
    Fin15AnchoredAtom4260 Fin15AnchoredAtom4264 Fin15AnchoredAtom4274 Fin15AnchoredAtom4329
    Fin15AnchoredAtom4735 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30944 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1907 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1921 chi ∧
      ¬Fin15AnchoredAtom1925 chi ∧
      ¬Fin15AnchoredAtom1926 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
      ¬Fin15AnchoredAtom2030 chi ∧
      ¬Fin15AnchoredAtom2034 chi ∧
      ¬Fin15AnchoredAtom2035 chi ∧
      ¬Fin15AnchoredAtom2039 chi ∧
      ¬Fin15AnchoredAtom2040 chi ∧
      ¬Fin15AnchoredAtom2050 chi ∧
      ¬Fin15AnchoredAtom2075 chi ∧
      ¬Fin15AnchoredAtom2076 chi ∧
      ¬Fin15AnchoredAtom2086 chi ∧
      ¬Fin15AnchoredAtom2096 chi ∧
      ¬Fin15AnchoredAtom2415 chi ∧
      ¬Fin15AnchoredAtom2419 chi ∧
      ¬Fin15AnchoredAtom2420 chi ∧
      ¬Fin15AnchoredAtom2424 chi ∧
      ¬Fin15AnchoredAtom2425 chi ∧
      ¬Fin15AnchoredAtom2435 chi ∧
      ¬Fin15AnchoredAtom2460 chi ∧
      ¬Fin15AnchoredAtom2461 chi ∧
      ¬Fin15AnchoredAtom2471 chi ∧
      ¬Fin15AnchoredAtom2481 chi ∧
      ¬Fin15AnchoredAtom2720 chi ∧
      ¬Fin15AnchoredAtom2721 chi ∧
      ¬Fin15AnchoredAtom2731 chi ∧
      ¬Fin15AnchoredAtom2741 chi ∧
      ¬Fin15AnchoredAtom2796 chi ∧
      ¬Fin15AnchoredAtom3130 chi ∧
      ¬Fin15AnchoredAtom3134 chi ∧
      ¬Fin15AnchoredAtom3135 chi ∧
      ¬Fin15AnchoredAtom3139 chi ∧
      ¬Fin15AnchoredAtom3140 chi ∧
      ¬Fin15AnchoredAtom3150 chi ∧
      ¬Fin15AnchoredAtom3175 chi ∧
      ¬Fin15AnchoredAtom3176 chi ∧
      ¬Fin15AnchoredAtom3186 chi ∧
      ¬Fin15AnchoredAtom3196 chi ∧
      ¬Fin15AnchoredAtom3435 chi ∧
      ¬Fin15AnchoredAtom3436 chi ∧
      ¬Fin15AnchoredAtom3446 chi ∧
      ¬Fin15AnchoredAtom3456 chi ∧
      ¬Fin15AnchoredAtom3511 chi ∧
      ¬Fin15AnchoredAtom4260 chi ∧
      ¬Fin15AnchoredAtom4261 chi ∧
      ¬Fin15AnchoredAtom4271 chi ∧
      ¬Fin15AnchoredAtom4281 chi ∧
      ¬Fin15AnchoredAtom4336 chi ∧
      ¬Fin15AnchoredAtom4742 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 6, 8, 9, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25419
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1907 Fin15AnchoredAtom1908 Fin15AnchoredAtom1912
    Fin15AnchoredAtom1913 Fin15AnchoredAtom1921 Fin15AnchoredAtom1925 Fin15AnchoredAtom1926
    Fin15AnchoredAtom1930 Fin15AnchoredAtom1931 Fin15AnchoredAtom1941 Fin15AnchoredAtom2030
    Fin15AnchoredAtom2034 Fin15AnchoredAtom2035 Fin15AnchoredAtom2039 Fin15AnchoredAtom2040
    Fin15AnchoredAtom2050 Fin15AnchoredAtom2075 Fin15AnchoredAtom2076 Fin15AnchoredAtom2086
    Fin15AnchoredAtom2096 Fin15AnchoredAtom2415 Fin15AnchoredAtom2419 Fin15AnchoredAtom2420
    Fin15AnchoredAtom2424 Fin15AnchoredAtom2425 Fin15AnchoredAtom2435 Fin15AnchoredAtom2460
    Fin15AnchoredAtom2461 Fin15AnchoredAtom2471 Fin15AnchoredAtom2481 Fin15AnchoredAtom2720
    Fin15AnchoredAtom2721 Fin15AnchoredAtom2731 Fin15AnchoredAtom2741 Fin15AnchoredAtom2796
    Fin15AnchoredAtom3130 Fin15AnchoredAtom3134 Fin15AnchoredAtom3135 Fin15AnchoredAtom3139
    Fin15AnchoredAtom3140 Fin15AnchoredAtom3150 Fin15AnchoredAtom3175 Fin15AnchoredAtom3176
    Fin15AnchoredAtom3186 Fin15AnchoredAtom3196 Fin15AnchoredAtom3435 Fin15AnchoredAtom3436
    Fin15AnchoredAtom3446 Fin15AnchoredAtom3456 Fin15AnchoredAtom3511 Fin15AnchoredAtom4260
    Fin15AnchoredAtom4261 Fin15AnchoredAtom4271 Fin15AnchoredAtom4281 Fin15AnchoredAtom4336
    Fin15AnchoredAtom4742 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30945 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom1939 chi ∧
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
      ¬Fin15AnchoredAtom2421 chi ∧
      ¬Fin15AnchoredAtom2423 chi ∧
      ¬Fin15AnchoredAtom2424 chi ∧
      ¬Fin15AnchoredAtom2427 chi ∧
      ¬Fin15AnchoredAtom2428 chi ∧
      ¬Fin15AnchoredAtom2433 chi ∧
      ¬Fin15AnchoredAtom2473 chi ∧
      ¬Fin15AnchoredAtom2474 chi ∧
      ¬Fin15AnchoredAtom2479 chi ∧
      ¬Fin15AnchoredAtom2485 chi ∧
      ¬Fin15AnchoredAtom2733 chi ∧
      ¬Fin15AnchoredAtom2734 chi ∧
      ¬Fin15AnchoredAtom2739 chi ∧
      ¬Fin15AnchoredAtom2745 chi ∧
      ¬Fin15AnchoredAtom2810 chi ∧
      ¬Fin15AnchoredAtom3136 chi ∧
      ¬Fin15AnchoredAtom3138 chi ∧
      ¬Fin15AnchoredAtom3139 chi ∧
      ¬Fin15AnchoredAtom3142 chi ∧
      ¬Fin15AnchoredAtom3143 chi ∧
      ¬Fin15AnchoredAtom3148 chi ∧
      ¬Fin15AnchoredAtom3188 chi ∧
      ¬Fin15AnchoredAtom3189 chi ∧
      ¬Fin15AnchoredAtom3194 chi ∧
      ¬Fin15AnchoredAtom3200 chi ∧
      ¬Fin15AnchoredAtom3448 chi ∧
      ¬Fin15AnchoredAtom3449 chi ∧
      ¬Fin15AnchoredAtom3454 chi ∧
      ¬Fin15AnchoredAtom3460 chi ∧
      ¬Fin15AnchoredAtom3525 chi ∧
      ¬Fin15AnchoredAtom4273 chi ∧
      ¬Fin15AnchoredAtom4274 chi ∧
      ¬Fin15AnchoredAtom4279 chi ∧
      ¬Fin15AnchoredAtom4285 chi ∧
      ¬Fin15AnchoredAtom4350 chi ∧
      ¬Fin15AnchoredAtom4756 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 6, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13899
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1908 Fin15AnchoredAtom1909 Fin15AnchoredAtom1911
    Fin15AnchoredAtom1912 Fin15AnchoredAtom1927 Fin15AnchoredAtom1929 Fin15AnchoredAtom1930
    Fin15AnchoredAtom1933 Fin15AnchoredAtom1934 Fin15AnchoredAtom1939 Fin15AnchoredAtom2036
    Fin15AnchoredAtom2038 Fin15AnchoredAtom2039 Fin15AnchoredAtom2042 Fin15AnchoredAtom2043
    Fin15AnchoredAtom2048 Fin15AnchoredAtom2088 Fin15AnchoredAtom2089 Fin15AnchoredAtom2094
    Fin15AnchoredAtom2100 Fin15AnchoredAtom2421 Fin15AnchoredAtom2423 Fin15AnchoredAtom2424
    Fin15AnchoredAtom2427 Fin15AnchoredAtom2428 Fin15AnchoredAtom2433 Fin15AnchoredAtom2473
    Fin15AnchoredAtom2474 Fin15AnchoredAtom2479 Fin15AnchoredAtom2485 Fin15AnchoredAtom2733
    Fin15AnchoredAtom2734 Fin15AnchoredAtom2739 Fin15AnchoredAtom2745 Fin15AnchoredAtom2810
    Fin15AnchoredAtom3136 Fin15AnchoredAtom3138 Fin15AnchoredAtom3139 Fin15AnchoredAtom3142
    Fin15AnchoredAtom3143 Fin15AnchoredAtom3148 Fin15AnchoredAtom3188 Fin15AnchoredAtom3189
    Fin15AnchoredAtom3194 Fin15AnchoredAtom3200 Fin15AnchoredAtom3448 Fin15AnchoredAtom3449
    Fin15AnchoredAtom3454 Fin15AnchoredAtom3460 Fin15AnchoredAtom3525 Fin15AnchoredAtom4273
    Fin15AnchoredAtom4274 Fin15AnchoredAtom4279 Fin15AnchoredAtom4285 Fin15AnchoredAtom4350
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

theorem fin15Anchored_clause30946 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom1935 chi ∧
      ¬Fin15AnchoredAtom1940 chi ∧
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
      ¬Fin15AnchoredAtom2421 chi ∧
      ¬Fin15AnchoredAtom2423 chi ∧
      ¬Fin15AnchoredAtom2425 chi ∧
      ¬Fin15AnchoredAtom2427 chi ∧
      ¬Fin15AnchoredAtom2429 chi ∧
      ¬Fin15AnchoredAtom2434 chi ∧
      ¬Fin15AnchoredAtom2473 chi ∧
      ¬Fin15AnchoredAtom2475 chi ∧
      ¬Fin15AnchoredAtom2480 chi ∧
      ¬Fin15AnchoredAtom2486 chi ∧
      ¬Fin15AnchoredAtom2733 chi ∧
      ¬Fin15AnchoredAtom2735 chi ∧
      ¬Fin15AnchoredAtom2740 chi ∧
      ¬Fin15AnchoredAtom2746 chi ∧
      ¬Fin15AnchoredAtom2811 chi ∧
      ¬Fin15AnchoredAtom3136 chi ∧
      ¬Fin15AnchoredAtom3138 chi ∧
      ¬Fin15AnchoredAtom3140 chi ∧
      ¬Fin15AnchoredAtom3142 chi ∧
      ¬Fin15AnchoredAtom3144 chi ∧
      ¬Fin15AnchoredAtom3149 chi ∧
      ¬Fin15AnchoredAtom3188 chi ∧
      ¬Fin15AnchoredAtom3190 chi ∧
      ¬Fin15AnchoredAtom3195 chi ∧
      ¬Fin15AnchoredAtom3201 chi ∧
      ¬Fin15AnchoredAtom3448 chi ∧
      ¬Fin15AnchoredAtom3450 chi ∧
      ¬Fin15AnchoredAtom3455 chi ∧
      ¬Fin15AnchoredAtom3461 chi ∧
      ¬Fin15AnchoredAtom3526 chi ∧
      ¬Fin15AnchoredAtom4273 chi ∧
      ¬Fin15AnchoredAtom4275 chi ∧
      ¬Fin15AnchoredAtom4280 chi ∧
      ¬Fin15AnchoredAtom4286 chi ∧
      ¬Fin15AnchoredAtom4351 chi ∧
      ¬Fin15AnchoredAtom4757 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 6, 9, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22091
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1908 Fin15AnchoredAtom1909 Fin15AnchoredAtom1911
    Fin15AnchoredAtom1913 Fin15AnchoredAtom1927 Fin15AnchoredAtom1929 Fin15AnchoredAtom1931
    Fin15AnchoredAtom1933 Fin15AnchoredAtom1935 Fin15AnchoredAtom1940 Fin15AnchoredAtom2036
    Fin15AnchoredAtom2038 Fin15AnchoredAtom2040 Fin15AnchoredAtom2042 Fin15AnchoredAtom2044
    Fin15AnchoredAtom2049 Fin15AnchoredAtom2088 Fin15AnchoredAtom2090 Fin15AnchoredAtom2095
    Fin15AnchoredAtom2101 Fin15AnchoredAtom2421 Fin15AnchoredAtom2423 Fin15AnchoredAtom2425
    Fin15AnchoredAtom2427 Fin15AnchoredAtom2429 Fin15AnchoredAtom2434 Fin15AnchoredAtom2473
    Fin15AnchoredAtom2475 Fin15AnchoredAtom2480 Fin15AnchoredAtom2486 Fin15AnchoredAtom2733
    Fin15AnchoredAtom2735 Fin15AnchoredAtom2740 Fin15AnchoredAtom2746 Fin15AnchoredAtom2811
    Fin15AnchoredAtom3136 Fin15AnchoredAtom3138 Fin15AnchoredAtom3140 Fin15AnchoredAtom3142
    Fin15AnchoredAtom3144 Fin15AnchoredAtom3149 Fin15AnchoredAtom3188 Fin15AnchoredAtom3190
    Fin15AnchoredAtom3195 Fin15AnchoredAtom3201 Fin15AnchoredAtom3448 Fin15AnchoredAtom3450
    Fin15AnchoredAtom3455 Fin15AnchoredAtom3461 Fin15AnchoredAtom3526 Fin15AnchoredAtom4273
    Fin15AnchoredAtom4275 Fin15AnchoredAtom4280 Fin15AnchoredAtom4286 Fin15AnchoredAtom4351
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

theorem fin15Anchored_clause30947 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom1935 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
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
      ¬Fin15AnchoredAtom2421 chi ∧
      ¬Fin15AnchoredAtom2424 chi ∧
      ¬Fin15AnchoredAtom2425 chi ∧
      ¬Fin15AnchoredAtom2428 chi ∧
      ¬Fin15AnchoredAtom2429 chi ∧
      ¬Fin15AnchoredAtom2435 chi ∧
      ¬Fin15AnchoredAtom2474 chi ∧
      ¬Fin15AnchoredAtom2475 chi ∧
      ¬Fin15AnchoredAtom2481 chi ∧
      ¬Fin15AnchoredAtom2487 chi ∧
      ¬Fin15AnchoredAtom2734 chi ∧
      ¬Fin15AnchoredAtom2735 chi ∧
      ¬Fin15AnchoredAtom2741 chi ∧
      ¬Fin15AnchoredAtom2747 chi ∧
      ¬Fin15AnchoredAtom2812 chi ∧
      ¬Fin15AnchoredAtom3136 chi ∧
      ¬Fin15AnchoredAtom3139 chi ∧
      ¬Fin15AnchoredAtom3140 chi ∧
      ¬Fin15AnchoredAtom3143 chi ∧
      ¬Fin15AnchoredAtom3144 chi ∧
      ¬Fin15AnchoredAtom3150 chi ∧
      ¬Fin15AnchoredAtom3189 chi ∧
      ¬Fin15AnchoredAtom3190 chi ∧
      ¬Fin15AnchoredAtom3196 chi ∧
      ¬Fin15AnchoredAtom3202 chi ∧
      ¬Fin15AnchoredAtom3449 chi ∧
      ¬Fin15AnchoredAtom3450 chi ∧
      ¬Fin15AnchoredAtom3456 chi ∧
      ¬Fin15AnchoredAtom3462 chi ∧
      ¬Fin15AnchoredAtom3527 chi ∧
      ¬Fin15AnchoredAtom4274 chi ∧
      ¬Fin15AnchoredAtom4275 chi ∧
      ¬Fin15AnchoredAtom4281 chi ∧
      ¬Fin15AnchoredAtom4287 chi ∧
      ¬Fin15AnchoredAtom4352 chi ∧
      ¬Fin15AnchoredAtom4758 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 6, 9, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26187
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1908 Fin15AnchoredAtom1909 Fin15AnchoredAtom1912
    Fin15AnchoredAtom1913 Fin15AnchoredAtom1927 Fin15AnchoredAtom1930 Fin15AnchoredAtom1931
    Fin15AnchoredAtom1934 Fin15AnchoredAtom1935 Fin15AnchoredAtom1941 Fin15AnchoredAtom2036
    Fin15AnchoredAtom2039 Fin15AnchoredAtom2040 Fin15AnchoredAtom2043 Fin15AnchoredAtom2044
    Fin15AnchoredAtom2050 Fin15AnchoredAtom2089 Fin15AnchoredAtom2090 Fin15AnchoredAtom2096
    Fin15AnchoredAtom2102 Fin15AnchoredAtom2421 Fin15AnchoredAtom2424 Fin15AnchoredAtom2425
    Fin15AnchoredAtom2428 Fin15AnchoredAtom2429 Fin15AnchoredAtom2435 Fin15AnchoredAtom2474
    Fin15AnchoredAtom2475 Fin15AnchoredAtom2481 Fin15AnchoredAtom2487 Fin15AnchoredAtom2734
    Fin15AnchoredAtom2735 Fin15AnchoredAtom2741 Fin15AnchoredAtom2747 Fin15AnchoredAtom2812
    Fin15AnchoredAtom3136 Fin15AnchoredAtom3139 Fin15AnchoredAtom3140 Fin15AnchoredAtom3143
    Fin15AnchoredAtom3144 Fin15AnchoredAtom3150 Fin15AnchoredAtom3189 Fin15AnchoredAtom3190
    Fin15AnchoredAtom3196 Fin15AnchoredAtom3202 Fin15AnchoredAtom3449 Fin15AnchoredAtom3450
    Fin15AnchoredAtom3456 Fin15AnchoredAtom3462 Fin15AnchoredAtom3527 Fin15AnchoredAtom4274
    Fin15AnchoredAtom4275 Fin15AnchoredAtom4281 Fin15AnchoredAtom4287 Fin15AnchoredAtom4352
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

theorem fin15Anchored_clause30948 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom1939 chi ∧
      ¬Fin15AnchoredAtom1940 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
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
      ¬Fin15AnchoredAtom2423 chi ∧
      ¬Fin15AnchoredAtom2424 chi ∧
      ¬Fin15AnchoredAtom2425 chi ∧
      ¬Fin15AnchoredAtom2433 chi ∧
      ¬Fin15AnchoredAtom2434 chi ∧
      ¬Fin15AnchoredAtom2435 chi ∧
      ¬Fin15AnchoredAtom2479 chi ∧
      ¬Fin15AnchoredAtom2480 chi ∧
      ¬Fin15AnchoredAtom2481 chi ∧
      ¬Fin15AnchoredAtom2491 chi ∧
      ¬Fin15AnchoredAtom2739 chi ∧
      ¬Fin15AnchoredAtom2740 chi ∧
      ¬Fin15AnchoredAtom2741 chi ∧
      ¬Fin15AnchoredAtom2751 chi ∧
      ¬Fin15AnchoredAtom2816 chi ∧
      ¬Fin15AnchoredAtom3138 chi ∧
      ¬Fin15AnchoredAtom3139 chi ∧
      ¬Fin15AnchoredAtom3140 chi ∧
      ¬Fin15AnchoredAtom3148 chi ∧
      ¬Fin15AnchoredAtom3149 chi ∧
      ¬Fin15AnchoredAtom3150 chi ∧
      ¬Fin15AnchoredAtom3194 chi ∧
      ¬Fin15AnchoredAtom3195 chi ∧
      ¬Fin15AnchoredAtom3196 chi ∧
      ¬Fin15AnchoredAtom3206 chi ∧
      ¬Fin15AnchoredAtom3454 chi ∧
      ¬Fin15AnchoredAtom3455 chi ∧
      ¬Fin15AnchoredAtom3456 chi ∧
      ¬Fin15AnchoredAtom3466 chi ∧
      ¬Fin15AnchoredAtom3531 chi ∧
      ¬Fin15AnchoredAtom4279 chi ∧
      ¬Fin15AnchoredAtom4280 chi ∧
      ¬Fin15AnchoredAtom4281 chi ∧
      ¬Fin15AnchoredAtom4291 chi ∧
      ¬Fin15AnchoredAtom4356 chi ∧
      ¬Fin15AnchoredAtom4762 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 6, 9, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29259
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1908 Fin15AnchoredAtom1911 Fin15AnchoredAtom1912
    Fin15AnchoredAtom1913 Fin15AnchoredAtom1929 Fin15AnchoredAtom1930 Fin15AnchoredAtom1931
    Fin15AnchoredAtom1939 Fin15AnchoredAtom1940 Fin15AnchoredAtom1941 Fin15AnchoredAtom2038
    Fin15AnchoredAtom2039 Fin15AnchoredAtom2040 Fin15AnchoredAtom2048 Fin15AnchoredAtom2049
    Fin15AnchoredAtom2050 Fin15AnchoredAtom2094 Fin15AnchoredAtom2095 Fin15AnchoredAtom2096
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2423 Fin15AnchoredAtom2424 Fin15AnchoredAtom2425
    Fin15AnchoredAtom2433 Fin15AnchoredAtom2434 Fin15AnchoredAtom2435 Fin15AnchoredAtom2479
    Fin15AnchoredAtom2480 Fin15AnchoredAtom2481 Fin15AnchoredAtom2491 Fin15AnchoredAtom2739
    Fin15AnchoredAtom2740 Fin15AnchoredAtom2741 Fin15AnchoredAtom2751 Fin15AnchoredAtom2816
    Fin15AnchoredAtom3138 Fin15AnchoredAtom3139 Fin15AnchoredAtom3140 Fin15AnchoredAtom3148
    Fin15AnchoredAtom3149 Fin15AnchoredAtom3150 Fin15AnchoredAtom3194 Fin15AnchoredAtom3195
    Fin15AnchoredAtom3196 Fin15AnchoredAtom3206 Fin15AnchoredAtom3454 Fin15AnchoredAtom3455
    Fin15AnchoredAtom3456 Fin15AnchoredAtom3466 Fin15AnchoredAtom3531 Fin15AnchoredAtom4279
    Fin15AnchoredAtom4280 Fin15AnchoredAtom4281 Fin15AnchoredAtom4291 Fin15AnchoredAtom4356
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

theorem fin15Anchored_clause30949 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom1935 chi ∧
      ¬Fin15AnchoredAtom1939 chi ∧
      ¬Fin15AnchoredAtom1940 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
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
      ¬Fin15AnchoredAtom2427 chi ∧
      ¬Fin15AnchoredAtom2428 chi ∧
      ¬Fin15AnchoredAtom2429 chi ∧
      ¬Fin15AnchoredAtom2433 chi ∧
      ¬Fin15AnchoredAtom2434 chi ∧
      ¬Fin15AnchoredAtom2435 chi ∧
      ¬Fin15AnchoredAtom2485 chi ∧
      ¬Fin15AnchoredAtom2486 chi ∧
      ¬Fin15AnchoredAtom2487 chi ∧
      ¬Fin15AnchoredAtom2491 chi ∧
      ¬Fin15AnchoredAtom2745 chi ∧
      ¬Fin15AnchoredAtom2746 chi ∧
      ¬Fin15AnchoredAtom2747 chi ∧
      ¬Fin15AnchoredAtom2751 chi ∧
      ¬Fin15AnchoredAtom2820 chi ∧
      ¬Fin15AnchoredAtom3142 chi ∧
      ¬Fin15AnchoredAtom3143 chi ∧
      ¬Fin15AnchoredAtom3144 chi ∧
      ¬Fin15AnchoredAtom3148 chi ∧
      ¬Fin15AnchoredAtom3149 chi ∧
      ¬Fin15AnchoredAtom3150 chi ∧
      ¬Fin15AnchoredAtom3200 chi ∧
      ¬Fin15AnchoredAtom3201 chi ∧
      ¬Fin15AnchoredAtom3202 chi ∧
      ¬Fin15AnchoredAtom3206 chi ∧
      ¬Fin15AnchoredAtom3460 chi ∧
      ¬Fin15AnchoredAtom3461 chi ∧
      ¬Fin15AnchoredAtom3462 chi ∧
      ¬Fin15AnchoredAtom3466 chi ∧
      ¬Fin15AnchoredAtom3535 chi ∧
      ¬Fin15AnchoredAtom4285 chi ∧
      ¬Fin15AnchoredAtom4286 chi ∧
      ¬Fin15AnchoredAtom4287 chi ∧
      ¬Fin15AnchoredAtom4291 chi ∧
      ¬Fin15AnchoredAtom4360 chi ∧
      ¬Fin15AnchoredAtom4766 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 6, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29771
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1909 Fin15AnchoredAtom1911 Fin15AnchoredAtom1912
    Fin15AnchoredAtom1913 Fin15AnchoredAtom1933 Fin15AnchoredAtom1934 Fin15AnchoredAtom1935
    Fin15AnchoredAtom1939 Fin15AnchoredAtom1940 Fin15AnchoredAtom1941 Fin15AnchoredAtom2042
    Fin15AnchoredAtom2043 Fin15AnchoredAtom2044 Fin15AnchoredAtom2048 Fin15AnchoredAtom2049
    Fin15AnchoredAtom2050 Fin15AnchoredAtom2100 Fin15AnchoredAtom2101 Fin15AnchoredAtom2102
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2427 Fin15AnchoredAtom2428 Fin15AnchoredAtom2429
    Fin15AnchoredAtom2433 Fin15AnchoredAtom2434 Fin15AnchoredAtom2435 Fin15AnchoredAtom2485
    Fin15AnchoredAtom2486 Fin15AnchoredAtom2487 Fin15AnchoredAtom2491 Fin15AnchoredAtom2745
    Fin15AnchoredAtom2746 Fin15AnchoredAtom2747 Fin15AnchoredAtom2751 Fin15AnchoredAtom2820
    Fin15AnchoredAtom3142 Fin15AnchoredAtom3143 Fin15AnchoredAtom3144 Fin15AnchoredAtom3148
    Fin15AnchoredAtom3149 Fin15AnchoredAtom3150 Fin15AnchoredAtom3200 Fin15AnchoredAtom3201
    Fin15AnchoredAtom3202 Fin15AnchoredAtom3206 Fin15AnchoredAtom3460 Fin15AnchoredAtom3461
    Fin15AnchoredAtom3462 Fin15AnchoredAtom3466 Fin15AnchoredAtom3535 Fin15AnchoredAtom4285
    Fin15AnchoredAtom4286 Fin15AnchoredAtom4287 Fin15AnchoredAtom4291 Fin15AnchoredAtom4360
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

theorem fin15Anchored_clause30950 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1914 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1921 chi ∧
      ¬Fin15AnchoredAtom1922 chi ∧
      ¬Fin15AnchoredAtom1925 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom2051 chi ∧
      ¬Fin15AnchoredAtom2052 chi ∧
      ¬Fin15AnchoredAtom2055 chi ∧
      ¬Fin15AnchoredAtom2057 chi ∧
      ¬Fin15AnchoredAtom2060 chi ∧
      ¬Fin15AnchoredAtom2064 chi ∧
      ¬Fin15AnchoredAtom2072 chi ∧
      ¬Fin15AnchoredAtom2075 chi ∧
      ¬Fin15AnchoredAtom2079 chi ∧
      ¬Fin15AnchoredAtom2089 chi ∧
      ¬Fin15AnchoredAtom2436 chi ∧
      ¬Fin15AnchoredAtom2437 chi ∧
      ¬Fin15AnchoredAtom2440 chi ∧
      ¬Fin15AnchoredAtom2442 chi ∧
      ¬Fin15AnchoredAtom2445 chi ∧
      ¬Fin15AnchoredAtom2449 chi ∧
      ¬Fin15AnchoredAtom2457 chi ∧
      ¬Fin15AnchoredAtom2460 chi ∧
      ¬Fin15AnchoredAtom2464 chi ∧
      ¬Fin15AnchoredAtom2474 chi ∧
      ¬Fin15AnchoredAtom2752 chi ∧
      ¬Fin15AnchoredAtom2755 chi ∧
      ¬Fin15AnchoredAtom2759 chi ∧
      ¬Fin15AnchoredAtom2769 chi ∧
      ¬Fin15AnchoredAtom2789 chi ∧
      ¬Fin15AnchoredAtom3151 chi ∧
      ¬Fin15AnchoredAtom3152 chi ∧
      ¬Fin15AnchoredAtom3155 chi ∧
      ¬Fin15AnchoredAtom3157 chi ∧
      ¬Fin15AnchoredAtom3160 chi ∧
      ¬Fin15AnchoredAtom3164 chi ∧
      ¬Fin15AnchoredAtom3172 chi ∧
      ¬Fin15AnchoredAtom3175 chi ∧
      ¬Fin15AnchoredAtom3179 chi ∧
      ¬Fin15AnchoredAtom3189 chi ∧
      ¬Fin15AnchoredAtom3467 chi ∧
      ¬Fin15AnchoredAtom3470 chi ∧
      ¬Fin15AnchoredAtom3474 chi ∧
      ¬Fin15AnchoredAtom3484 chi ∧
      ¬Fin15AnchoredAtom3504 chi ∧
      ¬Fin15AnchoredAtom4292 chi ∧
      ¬Fin15AnchoredAtom4295 chi ∧
      ¬Fin15AnchoredAtom4299 chi ∧
      ¬Fin15AnchoredAtom4309 chi ∧
      ¬Fin15AnchoredAtom4329 chi ∧
      ¬Fin15AnchoredAtom4770 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 7, 8, 9, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask10123
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1914 Fin15AnchoredAtom1915 Fin15AnchoredAtom1916
    Fin15AnchoredAtom1919 Fin15AnchoredAtom1921 Fin15AnchoredAtom1922 Fin15AnchoredAtom1925
    Fin15AnchoredAtom1927 Fin15AnchoredAtom1930 Fin15AnchoredAtom1934 Fin15AnchoredAtom2051
    Fin15AnchoredAtom2052 Fin15AnchoredAtom2055 Fin15AnchoredAtom2057 Fin15AnchoredAtom2060
    Fin15AnchoredAtom2064 Fin15AnchoredAtom2072 Fin15AnchoredAtom2075 Fin15AnchoredAtom2079
    Fin15AnchoredAtom2089 Fin15AnchoredAtom2436 Fin15AnchoredAtom2437 Fin15AnchoredAtom2440
    Fin15AnchoredAtom2442 Fin15AnchoredAtom2445 Fin15AnchoredAtom2449 Fin15AnchoredAtom2457
    Fin15AnchoredAtom2460 Fin15AnchoredAtom2464 Fin15AnchoredAtom2474 Fin15AnchoredAtom2752
    Fin15AnchoredAtom2755 Fin15AnchoredAtom2759 Fin15AnchoredAtom2769 Fin15AnchoredAtom2789
    Fin15AnchoredAtom3151 Fin15AnchoredAtom3152 Fin15AnchoredAtom3155 Fin15AnchoredAtom3157
    Fin15AnchoredAtom3160 Fin15AnchoredAtom3164 Fin15AnchoredAtom3172 Fin15AnchoredAtom3175
    Fin15AnchoredAtom3179 Fin15AnchoredAtom3189 Fin15AnchoredAtom3467 Fin15AnchoredAtom3470
    Fin15AnchoredAtom3474 Fin15AnchoredAtom3484 Fin15AnchoredAtom3504 Fin15AnchoredAtom4292
    Fin15AnchoredAtom4295 Fin15AnchoredAtom4299 Fin15AnchoredAtom4309 Fin15AnchoredAtom4329
    Fin15AnchoredAtom4770 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30951 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1914 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1921 chi ∧
      ¬Fin15AnchoredAtom1922 chi ∧
      ¬Fin15AnchoredAtom1926 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom1935 chi ∧
      ¬Fin15AnchoredAtom2051 chi ∧
      ¬Fin15AnchoredAtom2052 chi ∧
      ¬Fin15AnchoredAtom2056 chi ∧
      ¬Fin15AnchoredAtom2057 chi ∧
      ¬Fin15AnchoredAtom2061 chi ∧
      ¬Fin15AnchoredAtom2065 chi ∧
      ¬Fin15AnchoredAtom2072 chi ∧
      ¬Fin15AnchoredAtom2076 chi ∧
      ¬Fin15AnchoredAtom2080 chi ∧
      ¬Fin15AnchoredAtom2090 chi ∧
      ¬Fin15AnchoredAtom2436 chi ∧
      ¬Fin15AnchoredAtom2437 chi ∧
      ¬Fin15AnchoredAtom2441 chi ∧
      ¬Fin15AnchoredAtom2442 chi ∧
      ¬Fin15AnchoredAtom2446 chi ∧
      ¬Fin15AnchoredAtom2450 chi ∧
      ¬Fin15AnchoredAtom2457 chi ∧
      ¬Fin15AnchoredAtom2461 chi ∧
      ¬Fin15AnchoredAtom2465 chi ∧
      ¬Fin15AnchoredAtom2475 chi ∧
      ¬Fin15AnchoredAtom2752 chi ∧
      ¬Fin15AnchoredAtom2756 chi ∧
      ¬Fin15AnchoredAtom2760 chi ∧
      ¬Fin15AnchoredAtom2770 chi ∧
      ¬Fin15AnchoredAtom2790 chi ∧
      ¬Fin15AnchoredAtom3151 chi ∧
      ¬Fin15AnchoredAtom3152 chi ∧
      ¬Fin15AnchoredAtom3156 chi ∧
      ¬Fin15AnchoredAtom3157 chi ∧
      ¬Fin15AnchoredAtom3161 chi ∧
      ¬Fin15AnchoredAtom3165 chi ∧
      ¬Fin15AnchoredAtom3172 chi ∧
      ¬Fin15AnchoredAtom3176 chi ∧
      ¬Fin15AnchoredAtom3180 chi ∧
      ¬Fin15AnchoredAtom3190 chi ∧
      ¬Fin15AnchoredAtom3467 chi ∧
      ¬Fin15AnchoredAtom3471 chi ∧
      ¬Fin15AnchoredAtom3475 chi ∧
      ¬Fin15AnchoredAtom3485 chi ∧
      ¬Fin15AnchoredAtom3505 chi ∧
      ¬Fin15AnchoredAtom4292 chi ∧
      ¬Fin15AnchoredAtom4296 chi ∧
      ¬Fin15AnchoredAtom4300 chi ∧
      ¬Fin15AnchoredAtom4310 chi ∧
      ¬Fin15AnchoredAtom4330 chi ∧
      ¬Fin15AnchoredAtom4771 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 7, 8, 9, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask18315
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1914 Fin15AnchoredAtom1915 Fin15AnchoredAtom1916
    Fin15AnchoredAtom1920 Fin15AnchoredAtom1921 Fin15AnchoredAtom1922 Fin15AnchoredAtom1926
    Fin15AnchoredAtom1927 Fin15AnchoredAtom1931 Fin15AnchoredAtom1935 Fin15AnchoredAtom2051
    Fin15AnchoredAtom2052 Fin15AnchoredAtom2056 Fin15AnchoredAtom2057 Fin15AnchoredAtom2061
    Fin15AnchoredAtom2065 Fin15AnchoredAtom2072 Fin15AnchoredAtom2076 Fin15AnchoredAtom2080
    Fin15AnchoredAtom2090 Fin15AnchoredAtom2436 Fin15AnchoredAtom2437 Fin15AnchoredAtom2441
    Fin15AnchoredAtom2442 Fin15AnchoredAtom2446 Fin15AnchoredAtom2450 Fin15AnchoredAtom2457
    Fin15AnchoredAtom2461 Fin15AnchoredAtom2465 Fin15AnchoredAtom2475 Fin15AnchoredAtom2752
    Fin15AnchoredAtom2756 Fin15AnchoredAtom2760 Fin15AnchoredAtom2770 Fin15AnchoredAtom2790
    Fin15AnchoredAtom3151 Fin15AnchoredAtom3152 Fin15AnchoredAtom3156 Fin15AnchoredAtom3157
    Fin15AnchoredAtom3161 Fin15AnchoredAtom3165 Fin15AnchoredAtom3172 Fin15AnchoredAtom3176
    Fin15AnchoredAtom3180 Fin15AnchoredAtom3190 Fin15AnchoredAtom3467 Fin15AnchoredAtom3471
    Fin15AnchoredAtom3475 Fin15AnchoredAtom3485 Fin15AnchoredAtom3505 Fin15AnchoredAtom4292
    Fin15AnchoredAtom4296 Fin15AnchoredAtom4300 Fin15AnchoredAtom4310 Fin15AnchoredAtom4330
    Fin15AnchoredAtom4771 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30952 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1917 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1928 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom1932 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom1936 chi ∧
      ¬Fin15AnchoredAtom2057 chi ∧
      ¬Fin15AnchoredAtom2058 chi ∧
      ¬Fin15AnchoredAtom2059 chi ∧
      ¬Fin15AnchoredAtom2062 chi ∧
      ¬Fin15AnchoredAtom2063 chi ∧
      ¬Fin15AnchoredAtom2066 chi ∧
      ¬Fin15AnchoredAtom2087 chi ∧
      ¬Fin15AnchoredAtom2088 chi ∧
      ¬Fin15AnchoredAtom2091 chi ∧
      ¬Fin15AnchoredAtom2097 chi ∧
      ¬Fin15AnchoredAtom2442 chi ∧
      ¬Fin15AnchoredAtom2443 chi ∧
      ¬Fin15AnchoredAtom2444 chi ∧
      ¬Fin15AnchoredAtom2447 chi ∧
      ¬Fin15AnchoredAtom2448 chi ∧
      ¬Fin15AnchoredAtom2451 chi ∧
      ¬Fin15AnchoredAtom2472 chi ∧
      ¬Fin15AnchoredAtom2473 chi ∧
      ¬Fin15AnchoredAtom2476 chi ∧
      ¬Fin15AnchoredAtom2482 chi ∧
      ¬Fin15AnchoredAtom2767 chi ∧
      ¬Fin15AnchoredAtom2768 chi ∧
      ¬Fin15AnchoredAtom2771 chi ∧
      ¬Fin15AnchoredAtom2777 chi ∧
      ¬Fin15AnchoredAtom2807 chi ∧
      ¬Fin15AnchoredAtom3157 chi ∧
      ¬Fin15AnchoredAtom3158 chi ∧
      ¬Fin15AnchoredAtom3159 chi ∧
      ¬Fin15AnchoredAtom3162 chi ∧
      ¬Fin15AnchoredAtom3163 chi ∧
      ¬Fin15AnchoredAtom3166 chi ∧
      ¬Fin15AnchoredAtom3187 chi ∧
      ¬Fin15AnchoredAtom3188 chi ∧
      ¬Fin15AnchoredAtom3191 chi ∧
      ¬Fin15AnchoredAtom3197 chi ∧
      ¬Fin15AnchoredAtom3482 chi ∧
      ¬Fin15AnchoredAtom3483 chi ∧
      ¬Fin15AnchoredAtom3486 chi ∧
      ¬Fin15AnchoredAtom3492 chi ∧
      ¬Fin15AnchoredAtom3522 chi ∧
      ¬Fin15AnchoredAtom4307 chi ∧
      ¬Fin15AnchoredAtom4308 chi ∧
      ¬Fin15AnchoredAtom4311 chi ∧
      ¬Fin15AnchoredAtom4317 chi ∧
      ¬Fin15AnchoredAtom4347 chi ∧
      ¬Fin15AnchoredAtom4788 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 7, 9, 10, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask07819
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1915 Fin15AnchoredAtom1916 Fin15AnchoredAtom1917
    Fin15AnchoredAtom1918 Fin15AnchoredAtom1927 Fin15AnchoredAtom1928 Fin15AnchoredAtom1929
    Fin15AnchoredAtom1932 Fin15AnchoredAtom1933 Fin15AnchoredAtom1936 Fin15AnchoredAtom2057
    Fin15AnchoredAtom2058 Fin15AnchoredAtom2059 Fin15AnchoredAtom2062 Fin15AnchoredAtom2063
    Fin15AnchoredAtom2066 Fin15AnchoredAtom2087 Fin15AnchoredAtom2088 Fin15AnchoredAtom2091
    Fin15AnchoredAtom2097 Fin15AnchoredAtom2442 Fin15AnchoredAtom2443 Fin15AnchoredAtom2444
    Fin15AnchoredAtom2447 Fin15AnchoredAtom2448 Fin15AnchoredAtom2451 Fin15AnchoredAtom2472
    Fin15AnchoredAtom2473 Fin15AnchoredAtom2476 Fin15AnchoredAtom2482 Fin15AnchoredAtom2767
    Fin15AnchoredAtom2768 Fin15AnchoredAtom2771 Fin15AnchoredAtom2777 Fin15AnchoredAtom2807
    Fin15AnchoredAtom3157 Fin15AnchoredAtom3158 Fin15AnchoredAtom3159 Fin15AnchoredAtom3162
    Fin15AnchoredAtom3163 Fin15AnchoredAtom3166 Fin15AnchoredAtom3187 Fin15AnchoredAtom3188
    Fin15AnchoredAtom3191 Fin15AnchoredAtom3197 Fin15AnchoredAtom3482 Fin15AnchoredAtom3483
    Fin15AnchoredAtom3486 Fin15AnchoredAtom3492 Fin15AnchoredAtom3522 Fin15AnchoredAtom4307
    Fin15AnchoredAtom4308 Fin15AnchoredAtom4311 Fin15AnchoredAtom4317 Fin15AnchoredAtom4347
    Fin15AnchoredAtom4788 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30953 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1917 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1928 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1932 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom1937 chi ∧
      ¬Fin15AnchoredAtom2057 chi ∧
      ¬Fin15AnchoredAtom2058 chi ∧
      ¬Fin15AnchoredAtom2060 chi ∧
      ¬Fin15AnchoredAtom2062 chi ∧
      ¬Fin15AnchoredAtom2064 chi ∧
      ¬Fin15AnchoredAtom2067 chi ∧
      ¬Fin15AnchoredAtom2087 chi ∧
      ¬Fin15AnchoredAtom2089 chi ∧
      ¬Fin15AnchoredAtom2092 chi ∧
      ¬Fin15AnchoredAtom2098 chi ∧
      ¬Fin15AnchoredAtom2442 chi ∧
      ¬Fin15AnchoredAtom2443 chi ∧
      ¬Fin15AnchoredAtom2445 chi ∧
      ¬Fin15AnchoredAtom2447 chi ∧
      ¬Fin15AnchoredAtom2449 chi ∧
      ¬Fin15AnchoredAtom2452 chi ∧
      ¬Fin15AnchoredAtom2472 chi ∧
      ¬Fin15AnchoredAtom2474 chi ∧
      ¬Fin15AnchoredAtom2477 chi ∧
      ¬Fin15AnchoredAtom2483 chi ∧
      ¬Fin15AnchoredAtom2767 chi ∧
      ¬Fin15AnchoredAtom2769 chi ∧
      ¬Fin15AnchoredAtom2772 chi ∧
      ¬Fin15AnchoredAtom2778 chi ∧
      ¬Fin15AnchoredAtom2808 chi ∧
      ¬Fin15AnchoredAtom3157 chi ∧
      ¬Fin15AnchoredAtom3158 chi ∧
      ¬Fin15AnchoredAtom3160 chi ∧
      ¬Fin15AnchoredAtom3162 chi ∧
      ¬Fin15AnchoredAtom3164 chi ∧
      ¬Fin15AnchoredAtom3167 chi ∧
      ¬Fin15AnchoredAtom3187 chi ∧
      ¬Fin15AnchoredAtom3189 chi ∧
      ¬Fin15AnchoredAtom3192 chi ∧
      ¬Fin15AnchoredAtom3198 chi ∧
      ¬Fin15AnchoredAtom3482 chi ∧
      ¬Fin15AnchoredAtom3484 chi ∧
      ¬Fin15AnchoredAtom3487 chi ∧
      ¬Fin15AnchoredAtom3493 chi ∧
      ¬Fin15AnchoredAtom3523 chi ∧
      ¬Fin15AnchoredAtom4307 chi ∧
      ¬Fin15AnchoredAtom4309 chi ∧
      ¬Fin15AnchoredAtom4312 chi ∧
      ¬Fin15AnchoredAtom4318 chi ∧
      ¬Fin15AnchoredAtom4348 chi ∧
      ¬Fin15AnchoredAtom4789 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 7, 9, 10, 11, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask11915
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1915 Fin15AnchoredAtom1916 Fin15AnchoredAtom1917
    Fin15AnchoredAtom1919 Fin15AnchoredAtom1927 Fin15AnchoredAtom1928 Fin15AnchoredAtom1930
    Fin15AnchoredAtom1932 Fin15AnchoredAtom1934 Fin15AnchoredAtom1937 Fin15AnchoredAtom2057
    Fin15AnchoredAtom2058 Fin15AnchoredAtom2060 Fin15AnchoredAtom2062 Fin15AnchoredAtom2064
    Fin15AnchoredAtom2067 Fin15AnchoredAtom2087 Fin15AnchoredAtom2089 Fin15AnchoredAtom2092
    Fin15AnchoredAtom2098 Fin15AnchoredAtom2442 Fin15AnchoredAtom2443 Fin15AnchoredAtom2445
    Fin15AnchoredAtom2447 Fin15AnchoredAtom2449 Fin15AnchoredAtom2452 Fin15AnchoredAtom2472
    Fin15AnchoredAtom2474 Fin15AnchoredAtom2477 Fin15AnchoredAtom2483 Fin15AnchoredAtom2767
    Fin15AnchoredAtom2769 Fin15AnchoredAtom2772 Fin15AnchoredAtom2778 Fin15AnchoredAtom2808
    Fin15AnchoredAtom3157 Fin15AnchoredAtom3158 Fin15AnchoredAtom3160 Fin15AnchoredAtom3162
    Fin15AnchoredAtom3164 Fin15AnchoredAtom3167 Fin15AnchoredAtom3187 Fin15AnchoredAtom3189
    Fin15AnchoredAtom3192 Fin15AnchoredAtom3198 Fin15AnchoredAtom3482 Fin15AnchoredAtom3484
    Fin15AnchoredAtom3487 Fin15AnchoredAtom3493 Fin15AnchoredAtom3523 Fin15AnchoredAtom4307
    Fin15AnchoredAtom4309 Fin15AnchoredAtom4312 Fin15AnchoredAtom4318 Fin15AnchoredAtom4348
    Fin15AnchoredAtom4789 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30954 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom1939 chi ∧
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
      ¬Fin15AnchoredAtom2442 chi ∧
      ¬Fin15AnchoredAtom2444 chi ∧
      ¬Fin15AnchoredAtom2445 chi ∧
      ¬Fin15AnchoredAtom2448 chi ∧
      ¬Fin15AnchoredAtom2449 chi ∧
      ¬Fin15AnchoredAtom2454 chi ∧
      ¬Fin15AnchoredAtom2473 chi ∧
      ¬Fin15AnchoredAtom2474 chi ∧
      ¬Fin15AnchoredAtom2479 chi ∧
      ¬Fin15AnchoredAtom2485 chi ∧
      ¬Fin15AnchoredAtom2768 chi ∧
      ¬Fin15AnchoredAtom2769 chi ∧
      ¬Fin15AnchoredAtom2774 chi ∧
      ¬Fin15AnchoredAtom2780 chi ∧
      ¬Fin15AnchoredAtom2810 chi ∧
      ¬Fin15AnchoredAtom3157 chi ∧
      ¬Fin15AnchoredAtom3159 chi ∧
      ¬Fin15AnchoredAtom3160 chi ∧
      ¬Fin15AnchoredAtom3163 chi ∧
      ¬Fin15AnchoredAtom3164 chi ∧
      ¬Fin15AnchoredAtom3169 chi ∧
      ¬Fin15AnchoredAtom3188 chi ∧
      ¬Fin15AnchoredAtom3189 chi ∧
      ¬Fin15AnchoredAtom3194 chi ∧
      ¬Fin15AnchoredAtom3200 chi ∧
      ¬Fin15AnchoredAtom3483 chi ∧
      ¬Fin15AnchoredAtom3484 chi ∧
      ¬Fin15AnchoredAtom3489 chi ∧
      ¬Fin15AnchoredAtom3495 chi ∧
      ¬Fin15AnchoredAtom3525 chi ∧
      ¬Fin15AnchoredAtom4308 chi ∧
      ¬Fin15AnchoredAtom4309 chi ∧
      ¬Fin15AnchoredAtom4314 chi ∧
      ¬Fin15AnchoredAtom4320 chi ∧
      ¬Fin15AnchoredAtom4350 chi ∧
      ¬Fin15AnchoredAtom4791 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 7, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13963
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1915 Fin15AnchoredAtom1916 Fin15AnchoredAtom1918
    Fin15AnchoredAtom1919 Fin15AnchoredAtom1927 Fin15AnchoredAtom1929 Fin15AnchoredAtom1930
    Fin15AnchoredAtom1933 Fin15AnchoredAtom1934 Fin15AnchoredAtom1939 Fin15AnchoredAtom2057
    Fin15AnchoredAtom2059 Fin15AnchoredAtom2060 Fin15AnchoredAtom2063 Fin15AnchoredAtom2064
    Fin15AnchoredAtom2069 Fin15AnchoredAtom2088 Fin15AnchoredAtom2089 Fin15AnchoredAtom2094
    Fin15AnchoredAtom2100 Fin15AnchoredAtom2442 Fin15AnchoredAtom2444 Fin15AnchoredAtom2445
    Fin15AnchoredAtom2448 Fin15AnchoredAtom2449 Fin15AnchoredAtom2454 Fin15AnchoredAtom2473
    Fin15AnchoredAtom2474 Fin15AnchoredAtom2479 Fin15AnchoredAtom2485 Fin15AnchoredAtom2768
    Fin15AnchoredAtom2769 Fin15AnchoredAtom2774 Fin15AnchoredAtom2780 Fin15AnchoredAtom2810
    Fin15AnchoredAtom3157 Fin15AnchoredAtom3159 Fin15AnchoredAtom3160 Fin15AnchoredAtom3163
    Fin15AnchoredAtom3164 Fin15AnchoredAtom3169 Fin15AnchoredAtom3188 Fin15AnchoredAtom3189
    Fin15AnchoredAtom3194 Fin15AnchoredAtom3200 Fin15AnchoredAtom3483 Fin15AnchoredAtom3484
    Fin15AnchoredAtom3489 Fin15AnchoredAtom3495 Fin15AnchoredAtom3525 Fin15AnchoredAtom4308
    Fin15AnchoredAtom4309 Fin15AnchoredAtom4314 Fin15AnchoredAtom4320 Fin15AnchoredAtom4350
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

theorem fin15Anchored_clause30955 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom1935 chi ∧
      ¬Fin15AnchoredAtom1940 chi ∧
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
      ¬Fin15AnchoredAtom2442 chi ∧
      ¬Fin15AnchoredAtom2444 chi ∧
      ¬Fin15AnchoredAtom2446 chi ∧
      ¬Fin15AnchoredAtom2448 chi ∧
      ¬Fin15AnchoredAtom2450 chi ∧
      ¬Fin15AnchoredAtom2455 chi ∧
      ¬Fin15AnchoredAtom2473 chi ∧
      ¬Fin15AnchoredAtom2475 chi ∧
      ¬Fin15AnchoredAtom2480 chi ∧
      ¬Fin15AnchoredAtom2486 chi ∧
      ¬Fin15AnchoredAtom2768 chi ∧
      ¬Fin15AnchoredAtom2770 chi ∧
      ¬Fin15AnchoredAtom2775 chi ∧
      ¬Fin15AnchoredAtom2781 chi ∧
      ¬Fin15AnchoredAtom2811 chi ∧
      ¬Fin15AnchoredAtom3157 chi ∧
      ¬Fin15AnchoredAtom3159 chi ∧
      ¬Fin15AnchoredAtom3161 chi ∧
      ¬Fin15AnchoredAtom3163 chi ∧
      ¬Fin15AnchoredAtom3165 chi ∧
      ¬Fin15AnchoredAtom3170 chi ∧
      ¬Fin15AnchoredAtom3188 chi ∧
      ¬Fin15AnchoredAtom3190 chi ∧
      ¬Fin15AnchoredAtom3195 chi ∧
      ¬Fin15AnchoredAtom3201 chi ∧
      ¬Fin15AnchoredAtom3483 chi ∧
      ¬Fin15AnchoredAtom3485 chi ∧
      ¬Fin15AnchoredAtom3490 chi ∧
      ¬Fin15AnchoredAtom3496 chi ∧
      ¬Fin15AnchoredAtom3526 chi ∧
      ¬Fin15AnchoredAtom4308 chi ∧
      ¬Fin15AnchoredAtom4310 chi ∧
      ¬Fin15AnchoredAtom4315 chi ∧
      ¬Fin15AnchoredAtom4321 chi ∧
      ¬Fin15AnchoredAtom4351 chi ∧
      ¬Fin15AnchoredAtom4792 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 7, 9, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22155
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1915 Fin15AnchoredAtom1916 Fin15AnchoredAtom1918
    Fin15AnchoredAtom1920 Fin15AnchoredAtom1927 Fin15AnchoredAtom1929 Fin15AnchoredAtom1931
    Fin15AnchoredAtom1933 Fin15AnchoredAtom1935 Fin15AnchoredAtom1940 Fin15AnchoredAtom2057
    Fin15AnchoredAtom2059 Fin15AnchoredAtom2061 Fin15AnchoredAtom2063 Fin15AnchoredAtom2065
    Fin15AnchoredAtom2070 Fin15AnchoredAtom2088 Fin15AnchoredAtom2090 Fin15AnchoredAtom2095
    Fin15AnchoredAtom2101 Fin15AnchoredAtom2442 Fin15AnchoredAtom2444 Fin15AnchoredAtom2446
    Fin15AnchoredAtom2448 Fin15AnchoredAtom2450 Fin15AnchoredAtom2455 Fin15AnchoredAtom2473
    Fin15AnchoredAtom2475 Fin15AnchoredAtom2480 Fin15AnchoredAtom2486 Fin15AnchoredAtom2768
    Fin15AnchoredAtom2770 Fin15AnchoredAtom2775 Fin15AnchoredAtom2781 Fin15AnchoredAtom2811
    Fin15AnchoredAtom3157 Fin15AnchoredAtom3159 Fin15AnchoredAtom3161 Fin15AnchoredAtom3163
    Fin15AnchoredAtom3165 Fin15AnchoredAtom3170 Fin15AnchoredAtom3188 Fin15AnchoredAtom3190
    Fin15AnchoredAtom3195 Fin15AnchoredAtom3201 Fin15AnchoredAtom3483 Fin15AnchoredAtom3485
    Fin15AnchoredAtom3490 Fin15AnchoredAtom3496 Fin15AnchoredAtom3526 Fin15AnchoredAtom4308
    Fin15AnchoredAtom4310 Fin15AnchoredAtom4315 Fin15AnchoredAtom4321 Fin15AnchoredAtom4351
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

theorem fin15Anchored_clause30956 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom1935 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
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
      ¬Fin15AnchoredAtom2442 chi ∧
      ¬Fin15AnchoredAtom2445 chi ∧
      ¬Fin15AnchoredAtom2446 chi ∧
      ¬Fin15AnchoredAtom2449 chi ∧
      ¬Fin15AnchoredAtom2450 chi ∧
      ¬Fin15AnchoredAtom2456 chi ∧
      ¬Fin15AnchoredAtom2474 chi ∧
      ¬Fin15AnchoredAtom2475 chi ∧
      ¬Fin15AnchoredAtom2481 chi ∧
      ¬Fin15AnchoredAtom2487 chi ∧
      ¬Fin15AnchoredAtom2769 chi ∧
      ¬Fin15AnchoredAtom2770 chi ∧
      ¬Fin15AnchoredAtom2776 chi ∧
      ¬Fin15AnchoredAtom2782 chi ∧
      ¬Fin15AnchoredAtom2812 chi ∧
      ¬Fin15AnchoredAtom3157 chi ∧
      ¬Fin15AnchoredAtom3160 chi ∧
      ¬Fin15AnchoredAtom3161 chi ∧
      ¬Fin15AnchoredAtom3164 chi ∧
      ¬Fin15AnchoredAtom3165 chi ∧
      ¬Fin15AnchoredAtom3171 chi ∧
      ¬Fin15AnchoredAtom3189 chi ∧
      ¬Fin15AnchoredAtom3190 chi ∧
      ¬Fin15AnchoredAtom3196 chi ∧
      ¬Fin15AnchoredAtom3202 chi ∧
      ¬Fin15AnchoredAtom3484 chi ∧
      ¬Fin15AnchoredAtom3485 chi ∧
      ¬Fin15AnchoredAtom3491 chi ∧
      ¬Fin15AnchoredAtom3497 chi ∧
      ¬Fin15AnchoredAtom3527 chi ∧
      ¬Fin15AnchoredAtom4309 chi ∧
      ¬Fin15AnchoredAtom4310 chi ∧
      ¬Fin15AnchoredAtom4316 chi ∧
      ¬Fin15AnchoredAtom4322 chi ∧
      ¬Fin15AnchoredAtom4352 chi ∧
      ¬Fin15AnchoredAtom4793 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 7, 9, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26251
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1915 Fin15AnchoredAtom1916 Fin15AnchoredAtom1919
    Fin15AnchoredAtom1920 Fin15AnchoredAtom1927 Fin15AnchoredAtom1930 Fin15AnchoredAtom1931
    Fin15AnchoredAtom1934 Fin15AnchoredAtom1935 Fin15AnchoredAtom1941 Fin15AnchoredAtom2057
    Fin15AnchoredAtom2060 Fin15AnchoredAtom2061 Fin15AnchoredAtom2064 Fin15AnchoredAtom2065
    Fin15AnchoredAtom2071 Fin15AnchoredAtom2089 Fin15AnchoredAtom2090 Fin15AnchoredAtom2096
    Fin15AnchoredAtom2102 Fin15AnchoredAtom2442 Fin15AnchoredAtom2445 Fin15AnchoredAtom2446
    Fin15AnchoredAtom2449 Fin15AnchoredAtom2450 Fin15AnchoredAtom2456 Fin15AnchoredAtom2474
    Fin15AnchoredAtom2475 Fin15AnchoredAtom2481 Fin15AnchoredAtom2487 Fin15AnchoredAtom2769
    Fin15AnchoredAtom2770 Fin15AnchoredAtom2776 Fin15AnchoredAtom2782 Fin15AnchoredAtom2812
    Fin15AnchoredAtom3157 Fin15AnchoredAtom3160 Fin15AnchoredAtom3161 Fin15AnchoredAtom3164
    Fin15AnchoredAtom3165 Fin15AnchoredAtom3171 Fin15AnchoredAtom3189 Fin15AnchoredAtom3190
    Fin15AnchoredAtom3196 Fin15AnchoredAtom3202 Fin15AnchoredAtom3484 Fin15AnchoredAtom3485
    Fin15AnchoredAtom3491 Fin15AnchoredAtom3497 Fin15AnchoredAtom3527 Fin15AnchoredAtom4309
    Fin15AnchoredAtom4310 Fin15AnchoredAtom4316 Fin15AnchoredAtom4322 Fin15AnchoredAtom4352
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

theorem fin15Anchored_clause30957 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom1939 chi ∧
      ¬Fin15AnchoredAtom1940 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
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
      ¬Fin15AnchoredAtom2444 chi ∧
      ¬Fin15AnchoredAtom2445 chi ∧
      ¬Fin15AnchoredAtom2446 chi ∧
      ¬Fin15AnchoredAtom2454 chi ∧
      ¬Fin15AnchoredAtom2455 chi ∧
      ¬Fin15AnchoredAtom2456 chi ∧
      ¬Fin15AnchoredAtom2479 chi ∧
      ¬Fin15AnchoredAtom2480 chi ∧
      ¬Fin15AnchoredAtom2481 chi ∧
      ¬Fin15AnchoredAtom2491 chi ∧
      ¬Fin15AnchoredAtom2774 chi ∧
      ¬Fin15AnchoredAtom2775 chi ∧
      ¬Fin15AnchoredAtom2776 chi ∧
      ¬Fin15AnchoredAtom2786 chi ∧
      ¬Fin15AnchoredAtom2816 chi ∧
      ¬Fin15AnchoredAtom3159 chi ∧
      ¬Fin15AnchoredAtom3160 chi ∧
      ¬Fin15AnchoredAtom3161 chi ∧
      ¬Fin15AnchoredAtom3169 chi ∧
      ¬Fin15AnchoredAtom3170 chi ∧
      ¬Fin15AnchoredAtom3171 chi ∧
      ¬Fin15AnchoredAtom3194 chi ∧
      ¬Fin15AnchoredAtom3195 chi ∧
      ¬Fin15AnchoredAtom3196 chi ∧
      ¬Fin15AnchoredAtom3206 chi ∧
      ¬Fin15AnchoredAtom3489 chi ∧
      ¬Fin15AnchoredAtom3490 chi ∧
      ¬Fin15AnchoredAtom3491 chi ∧
      ¬Fin15AnchoredAtom3501 chi ∧
      ¬Fin15AnchoredAtom3531 chi ∧
      ¬Fin15AnchoredAtom4314 chi ∧
      ¬Fin15AnchoredAtom4315 chi ∧
      ¬Fin15AnchoredAtom4316 chi ∧
      ¬Fin15AnchoredAtom4326 chi ∧
      ¬Fin15AnchoredAtom4356 chi ∧
      ¬Fin15AnchoredAtom4797 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 7, 9, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29323
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1915 Fin15AnchoredAtom1918 Fin15AnchoredAtom1919
    Fin15AnchoredAtom1920 Fin15AnchoredAtom1929 Fin15AnchoredAtom1930 Fin15AnchoredAtom1931
    Fin15AnchoredAtom1939 Fin15AnchoredAtom1940 Fin15AnchoredAtom1941 Fin15AnchoredAtom2059
    Fin15AnchoredAtom2060 Fin15AnchoredAtom2061 Fin15AnchoredAtom2069 Fin15AnchoredAtom2070
    Fin15AnchoredAtom2071 Fin15AnchoredAtom2094 Fin15AnchoredAtom2095 Fin15AnchoredAtom2096
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2444 Fin15AnchoredAtom2445 Fin15AnchoredAtom2446
    Fin15AnchoredAtom2454 Fin15AnchoredAtom2455 Fin15AnchoredAtom2456 Fin15AnchoredAtom2479
    Fin15AnchoredAtom2480 Fin15AnchoredAtom2481 Fin15AnchoredAtom2491 Fin15AnchoredAtom2774
    Fin15AnchoredAtom2775 Fin15AnchoredAtom2776 Fin15AnchoredAtom2786 Fin15AnchoredAtom2816
    Fin15AnchoredAtom3159 Fin15AnchoredAtom3160 Fin15AnchoredAtom3161 Fin15AnchoredAtom3169
    Fin15AnchoredAtom3170 Fin15AnchoredAtom3171 Fin15AnchoredAtom3194 Fin15AnchoredAtom3195
    Fin15AnchoredAtom3196 Fin15AnchoredAtom3206 Fin15AnchoredAtom3489 Fin15AnchoredAtom3490
    Fin15AnchoredAtom3491 Fin15AnchoredAtom3501 Fin15AnchoredAtom3531 Fin15AnchoredAtom4314
    Fin15AnchoredAtom4315 Fin15AnchoredAtom4316 Fin15AnchoredAtom4326 Fin15AnchoredAtom4356
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

theorem fin15Anchored_clause30958 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1917 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1932 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom1935 chi ∧
      ¬Fin15AnchoredAtom1936 chi ∧
      ¬Fin15AnchoredAtom1938 chi ∧
      ¬Fin15AnchoredAtom1940 chi ∧
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
      ¬Fin15AnchoredAtom2447 chi ∧
      ¬Fin15AnchoredAtom2448 chi ∧
      ¬Fin15AnchoredAtom2450 chi ∧
      ¬Fin15AnchoredAtom2451 chi ∧
      ¬Fin15AnchoredAtom2453 chi ∧
      ¬Fin15AnchoredAtom2455 chi ∧
      ¬Fin15AnchoredAtom2482 chi ∧
      ¬Fin15AnchoredAtom2484 chi ∧
      ¬Fin15AnchoredAtom2486 chi ∧
      ¬Fin15AnchoredAtom2489 chi ∧
      ¬Fin15AnchoredAtom2777 chi ∧
      ¬Fin15AnchoredAtom2779 chi ∧
      ¬Fin15AnchoredAtom2781 chi ∧
      ¬Fin15AnchoredAtom2784 chi ∧
      ¬Fin15AnchoredAtom2818 chi ∧
      ¬Fin15AnchoredAtom3162 chi ∧
      ¬Fin15AnchoredAtom3163 chi ∧
      ¬Fin15AnchoredAtom3165 chi ∧
      ¬Fin15AnchoredAtom3166 chi ∧
      ¬Fin15AnchoredAtom3168 chi ∧
      ¬Fin15AnchoredAtom3170 chi ∧
      ¬Fin15AnchoredAtom3197 chi ∧
      ¬Fin15AnchoredAtom3199 chi ∧
      ¬Fin15AnchoredAtom3201 chi ∧
      ¬Fin15AnchoredAtom3204 chi ∧
      ¬Fin15AnchoredAtom3492 chi ∧
      ¬Fin15AnchoredAtom3494 chi ∧
      ¬Fin15AnchoredAtom3496 chi ∧
      ¬Fin15AnchoredAtom3499 chi ∧
      ¬Fin15AnchoredAtom3533 chi ∧
      ¬Fin15AnchoredAtom4317 chi ∧
      ¬Fin15AnchoredAtom4319 chi ∧
      ¬Fin15AnchoredAtom4321 chi ∧
      ¬Fin15AnchoredAtom4324 chi ∧
      ¬Fin15AnchoredAtom4358 chi ∧
      ¬Fin15AnchoredAtom4799 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 7, 10, 11, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask23691
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1916 Fin15AnchoredAtom1917 Fin15AnchoredAtom1918
    Fin15AnchoredAtom1920 Fin15AnchoredAtom1932 Fin15AnchoredAtom1933 Fin15AnchoredAtom1935
    Fin15AnchoredAtom1936 Fin15AnchoredAtom1938 Fin15AnchoredAtom1940 Fin15AnchoredAtom2062
    Fin15AnchoredAtom2063 Fin15AnchoredAtom2065 Fin15AnchoredAtom2066 Fin15AnchoredAtom2068
    Fin15AnchoredAtom2070 Fin15AnchoredAtom2097 Fin15AnchoredAtom2099 Fin15AnchoredAtom2101
    Fin15AnchoredAtom2104 Fin15AnchoredAtom2447 Fin15AnchoredAtom2448 Fin15AnchoredAtom2450
    Fin15AnchoredAtom2451 Fin15AnchoredAtom2453 Fin15AnchoredAtom2455 Fin15AnchoredAtom2482
    Fin15AnchoredAtom2484 Fin15AnchoredAtom2486 Fin15AnchoredAtom2489 Fin15AnchoredAtom2777
    Fin15AnchoredAtom2779 Fin15AnchoredAtom2781 Fin15AnchoredAtom2784 Fin15AnchoredAtom2818
    Fin15AnchoredAtom3162 Fin15AnchoredAtom3163 Fin15AnchoredAtom3165 Fin15AnchoredAtom3166
    Fin15AnchoredAtom3168 Fin15AnchoredAtom3170 Fin15AnchoredAtom3197 Fin15AnchoredAtom3199
    Fin15AnchoredAtom3201 Fin15AnchoredAtom3204 Fin15AnchoredAtom3492 Fin15AnchoredAtom3494
    Fin15AnchoredAtom3496 Fin15AnchoredAtom3499 Fin15AnchoredAtom3533 Fin15AnchoredAtom4317
    Fin15AnchoredAtom4319 Fin15AnchoredAtom4321 Fin15AnchoredAtom4324 Fin15AnchoredAtom4358
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

theorem fin15Anchored_clause30959 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom1935 chi ∧
      ¬Fin15AnchoredAtom1939 chi ∧
      ¬Fin15AnchoredAtom1940 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
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
      ¬Fin15AnchoredAtom2448 chi ∧
      ¬Fin15AnchoredAtom2449 chi ∧
      ¬Fin15AnchoredAtom2450 chi ∧
      ¬Fin15AnchoredAtom2454 chi ∧
      ¬Fin15AnchoredAtom2455 chi ∧
      ¬Fin15AnchoredAtom2456 chi ∧
      ¬Fin15AnchoredAtom2485 chi ∧
      ¬Fin15AnchoredAtom2486 chi ∧
      ¬Fin15AnchoredAtom2487 chi ∧
      ¬Fin15AnchoredAtom2491 chi ∧
      ¬Fin15AnchoredAtom2780 chi ∧
      ¬Fin15AnchoredAtom2781 chi ∧
      ¬Fin15AnchoredAtom2782 chi ∧
      ¬Fin15AnchoredAtom2786 chi ∧
      ¬Fin15AnchoredAtom2820 chi ∧
      ¬Fin15AnchoredAtom3163 chi ∧
      ¬Fin15AnchoredAtom3164 chi ∧
      ¬Fin15AnchoredAtom3165 chi ∧
      ¬Fin15AnchoredAtom3169 chi ∧
      ¬Fin15AnchoredAtom3170 chi ∧
      ¬Fin15AnchoredAtom3171 chi ∧
      ¬Fin15AnchoredAtom3200 chi ∧
      ¬Fin15AnchoredAtom3201 chi ∧
      ¬Fin15AnchoredAtom3202 chi ∧
      ¬Fin15AnchoredAtom3206 chi ∧
      ¬Fin15AnchoredAtom3495 chi ∧
      ¬Fin15AnchoredAtom3496 chi ∧
      ¬Fin15AnchoredAtom3497 chi ∧
      ¬Fin15AnchoredAtom3501 chi ∧
      ¬Fin15AnchoredAtom3535 chi ∧
      ¬Fin15AnchoredAtom4320 chi ∧
      ¬Fin15AnchoredAtom4321 chi ∧
      ¬Fin15AnchoredAtom4322 chi ∧
      ¬Fin15AnchoredAtom4326 chi ∧
      ¬Fin15AnchoredAtom4360 chi ∧
      ¬Fin15AnchoredAtom4801 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 7, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29835
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1916 Fin15AnchoredAtom1918 Fin15AnchoredAtom1919
    Fin15AnchoredAtom1920 Fin15AnchoredAtom1933 Fin15AnchoredAtom1934 Fin15AnchoredAtom1935
    Fin15AnchoredAtom1939 Fin15AnchoredAtom1940 Fin15AnchoredAtom1941 Fin15AnchoredAtom2063
    Fin15AnchoredAtom2064 Fin15AnchoredAtom2065 Fin15AnchoredAtom2069 Fin15AnchoredAtom2070
    Fin15AnchoredAtom2071 Fin15AnchoredAtom2100 Fin15AnchoredAtom2101 Fin15AnchoredAtom2102
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2448 Fin15AnchoredAtom2449 Fin15AnchoredAtom2450
    Fin15AnchoredAtom2454 Fin15AnchoredAtom2455 Fin15AnchoredAtom2456 Fin15AnchoredAtom2485
    Fin15AnchoredAtom2486 Fin15AnchoredAtom2487 Fin15AnchoredAtom2491 Fin15AnchoredAtom2780
    Fin15AnchoredAtom2781 Fin15AnchoredAtom2782 Fin15AnchoredAtom2786 Fin15AnchoredAtom2820
    Fin15AnchoredAtom3163 Fin15AnchoredAtom3164 Fin15AnchoredAtom3165 Fin15AnchoredAtom3169
    Fin15AnchoredAtom3170 Fin15AnchoredAtom3171 Fin15AnchoredAtom3200 Fin15AnchoredAtom3201
    Fin15AnchoredAtom3202 Fin15AnchoredAtom3206 Fin15AnchoredAtom3495 Fin15AnchoredAtom3496
    Fin15AnchoredAtom3497 Fin15AnchoredAtom3501 Fin15AnchoredAtom3535 Fin15AnchoredAtom4320
    Fin15AnchoredAtom4321 Fin15AnchoredAtom4322 Fin15AnchoredAtom4326 Fin15AnchoredAtom4360
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

theorem fin15Anchored_clause30960 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1921 chi ∧
      ¬Fin15AnchoredAtom1922 chi ∧
      ¬Fin15AnchoredAtom1925 chi ∧
      ¬Fin15AnchoredAtom1926 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom1935 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
      ¬Fin15AnchoredAtom2072 chi ∧
      ¬Fin15AnchoredAtom2075 chi ∧
      ¬Fin15AnchoredAtom2076 chi ∧
      ¬Fin15AnchoredAtom2079 chi ∧
      ¬Fin15AnchoredAtom2080 chi ∧
      ¬Fin15AnchoredAtom2086 chi ∧
      ¬Fin15AnchoredAtom2089 chi ∧
      ¬Fin15AnchoredAtom2090 chi ∧
      ¬Fin15AnchoredAtom2096 chi ∧
      ¬Fin15AnchoredAtom2102 chi ∧
      ¬Fin15AnchoredAtom2457 chi ∧
      ¬Fin15AnchoredAtom2460 chi ∧
      ¬Fin15AnchoredAtom2461 chi ∧
      ¬Fin15AnchoredAtom2464 chi ∧
      ¬Fin15AnchoredAtom2465 chi ∧
      ¬Fin15AnchoredAtom2471 chi ∧
      ¬Fin15AnchoredAtom2474 chi ∧
      ¬Fin15AnchoredAtom2475 chi ∧
      ¬Fin15AnchoredAtom2481 chi ∧
      ¬Fin15AnchoredAtom2487 chi ∧
      ¬Fin15AnchoredAtom2789 chi ∧
      ¬Fin15AnchoredAtom2790 chi ∧
      ¬Fin15AnchoredAtom2796 chi ∧
      ¬Fin15AnchoredAtom2802 chi ∧
      ¬Fin15AnchoredAtom2812 chi ∧
      ¬Fin15AnchoredAtom3172 chi ∧
      ¬Fin15AnchoredAtom3175 chi ∧
      ¬Fin15AnchoredAtom3176 chi ∧
      ¬Fin15AnchoredAtom3179 chi ∧
      ¬Fin15AnchoredAtom3180 chi ∧
      ¬Fin15AnchoredAtom3186 chi ∧
      ¬Fin15AnchoredAtom3189 chi ∧
      ¬Fin15AnchoredAtom3190 chi ∧
      ¬Fin15AnchoredAtom3196 chi ∧
      ¬Fin15AnchoredAtom3202 chi ∧
      ¬Fin15AnchoredAtom3504 chi ∧
      ¬Fin15AnchoredAtom3505 chi ∧
      ¬Fin15AnchoredAtom3511 chi ∧
      ¬Fin15AnchoredAtom3517 chi ∧
      ¬Fin15AnchoredAtom3527 chi ∧
      ¬Fin15AnchoredAtom4329 chi ∧
      ¬Fin15AnchoredAtom4330 chi ∧
      ¬Fin15AnchoredAtom4336 chi ∧
      ¬Fin15AnchoredAtom4342 chi ∧
      ¬Fin15AnchoredAtom4352 chi ∧
      ¬Fin15AnchoredAtom4808 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 8, 9, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26379
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1921 Fin15AnchoredAtom1922 Fin15AnchoredAtom1925
    Fin15AnchoredAtom1926 Fin15AnchoredAtom1927 Fin15AnchoredAtom1930 Fin15AnchoredAtom1931
    Fin15AnchoredAtom1934 Fin15AnchoredAtom1935 Fin15AnchoredAtom1941 Fin15AnchoredAtom2072
    Fin15AnchoredAtom2075 Fin15AnchoredAtom2076 Fin15AnchoredAtom2079 Fin15AnchoredAtom2080
    Fin15AnchoredAtom2086 Fin15AnchoredAtom2089 Fin15AnchoredAtom2090 Fin15AnchoredAtom2096
    Fin15AnchoredAtom2102 Fin15AnchoredAtom2457 Fin15AnchoredAtom2460 Fin15AnchoredAtom2461
    Fin15AnchoredAtom2464 Fin15AnchoredAtom2465 Fin15AnchoredAtom2471 Fin15AnchoredAtom2474
    Fin15AnchoredAtom2475 Fin15AnchoredAtom2481 Fin15AnchoredAtom2487 Fin15AnchoredAtom2789
    Fin15AnchoredAtom2790 Fin15AnchoredAtom2796 Fin15AnchoredAtom2802 Fin15AnchoredAtom2812
    Fin15AnchoredAtom3172 Fin15AnchoredAtom3175 Fin15AnchoredAtom3176 Fin15AnchoredAtom3179
    Fin15AnchoredAtom3180 Fin15AnchoredAtom3186 Fin15AnchoredAtom3189 Fin15AnchoredAtom3190
    Fin15AnchoredAtom3196 Fin15AnchoredAtom3202 Fin15AnchoredAtom3504 Fin15AnchoredAtom3505
    Fin15AnchoredAtom3511 Fin15AnchoredAtom3517 Fin15AnchoredAtom3527 Fin15AnchoredAtom4329
    Fin15AnchoredAtom4330 Fin15AnchoredAtom4336 Fin15AnchoredAtom4342 Fin15AnchoredAtom4352
    Fin15AnchoredAtom4808 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30961 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1928 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1932 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom1936 chi ∧
      ¬Fin15AnchoredAtom1937 chi ∧
      ¬Fin15AnchoredAtom1939 chi ∧
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
      ¬Fin15AnchoredAtom2472 chi ∧
      ¬Fin15AnchoredAtom2473 chi ∧
      ¬Fin15AnchoredAtom2474 chi ∧
      ¬Fin15AnchoredAtom2476 chi ∧
      ¬Fin15AnchoredAtom2477 chi ∧
      ¬Fin15AnchoredAtom2479 chi ∧
      ¬Fin15AnchoredAtom2482 chi ∧
      ¬Fin15AnchoredAtom2483 chi ∧
      ¬Fin15AnchoredAtom2485 chi ∧
      ¬Fin15AnchoredAtom2488 chi ∧
      ¬Fin15AnchoredAtom2807 chi ∧
      ¬Fin15AnchoredAtom2808 chi ∧
      ¬Fin15AnchoredAtom2810 chi ∧
      ¬Fin15AnchoredAtom2813 chi ∧
      ¬Fin15AnchoredAtom2817 chi ∧
      ¬Fin15AnchoredAtom3187 chi ∧
      ¬Fin15AnchoredAtom3188 chi ∧
      ¬Fin15AnchoredAtom3189 chi ∧
      ¬Fin15AnchoredAtom3191 chi ∧
      ¬Fin15AnchoredAtom3192 chi ∧
      ¬Fin15AnchoredAtom3194 chi ∧
      ¬Fin15AnchoredAtom3197 chi ∧
      ¬Fin15AnchoredAtom3198 chi ∧
      ¬Fin15AnchoredAtom3200 chi ∧
      ¬Fin15AnchoredAtom3203 chi ∧
      ¬Fin15AnchoredAtom3522 chi ∧
      ¬Fin15AnchoredAtom3523 chi ∧
      ¬Fin15AnchoredAtom3525 chi ∧
      ¬Fin15AnchoredAtom3528 chi ∧
      ¬Fin15AnchoredAtom3532 chi ∧
      ¬Fin15AnchoredAtom4347 chi ∧
      ¬Fin15AnchoredAtom4348 chi ∧
      ¬Fin15AnchoredAtom4350 chi ∧
      ¬Fin15AnchoredAtom4353 chi ∧
      ¬Fin15AnchoredAtom4357 chi ∧
      ¬Fin15AnchoredAtom4818 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 9, 10, 11, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask15883
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1927 Fin15AnchoredAtom1928 Fin15AnchoredAtom1929
    Fin15AnchoredAtom1930 Fin15AnchoredAtom1932 Fin15AnchoredAtom1933 Fin15AnchoredAtom1934
    Fin15AnchoredAtom1936 Fin15AnchoredAtom1937 Fin15AnchoredAtom1939 Fin15AnchoredAtom2087
    Fin15AnchoredAtom2088 Fin15AnchoredAtom2089 Fin15AnchoredAtom2091 Fin15AnchoredAtom2092
    Fin15AnchoredAtom2094 Fin15AnchoredAtom2097 Fin15AnchoredAtom2098 Fin15AnchoredAtom2100
    Fin15AnchoredAtom2103 Fin15AnchoredAtom2472 Fin15AnchoredAtom2473 Fin15AnchoredAtom2474
    Fin15AnchoredAtom2476 Fin15AnchoredAtom2477 Fin15AnchoredAtom2479 Fin15AnchoredAtom2482
    Fin15AnchoredAtom2483 Fin15AnchoredAtom2485 Fin15AnchoredAtom2488 Fin15AnchoredAtom2807
    Fin15AnchoredAtom2808 Fin15AnchoredAtom2810 Fin15AnchoredAtom2813 Fin15AnchoredAtom2817
    Fin15AnchoredAtom3187 Fin15AnchoredAtom3188 Fin15AnchoredAtom3189 Fin15AnchoredAtom3191
    Fin15AnchoredAtom3192 Fin15AnchoredAtom3194 Fin15AnchoredAtom3197 Fin15AnchoredAtom3198
    Fin15AnchoredAtom3200 Fin15AnchoredAtom3203 Fin15AnchoredAtom3522 Fin15AnchoredAtom3523
    Fin15AnchoredAtom3525 Fin15AnchoredAtom3528 Fin15AnchoredAtom3532 Fin15AnchoredAtom4347
    Fin15AnchoredAtom4348 Fin15AnchoredAtom4350 Fin15AnchoredAtom4353 Fin15AnchoredAtom4357
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

theorem fin15Anchored_clause30962 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom1935 chi ∧
      ¬Fin15AnchoredAtom1939 chi ∧
      ¬Fin15AnchoredAtom1940 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
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
      ¬Fin15AnchoredAtom2473 chi ∧
      ¬Fin15AnchoredAtom2474 chi ∧
      ¬Fin15AnchoredAtom2475 chi ∧
      ¬Fin15AnchoredAtom2479 chi ∧
      ¬Fin15AnchoredAtom2480 chi ∧
      ¬Fin15AnchoredAtom2481 chi ∧
      ¬Fin15AnchoredAtom2485 chi ∧
      ¬Fin15AnchoredAtom2486 chi ∧
      ¬Fin15AnchoredAtom2487 chi ∧
      ¬Fin15AnchoredAtom2491 chi ∧
      ¬Fin15AnchoredAtom2810 chi ∧
      ¬Fin15AnchoredAtom2811 chi ∧
      ¬Fin15AnchoredAtom2812 chi ∧
      ¬Fin15AnchoredAtom2816 chi ∧
      ¬Fin15AnchoredAtom2820 chi ∧
      ¬Fin15AnchoredAtom3188 chi ∧
      ¬Fin15AnchoredAtom3189 chi ∧
      ¬Fin15AnchoredAtom3190 chi ∧
      ¬Fin15AnchoredAtom3194 chi ∧
      ¬Fin15AnchoredAtom3195 chi ∧
      ¬Fin15AnchoredAtom3196 chi ∧
      ¬Fin15AnchoredAtom3200 chi ∧
      ¬Fin15AnchoredAtom3201 chi ∧
      ¬Fin15AnchoredAtom3202 chi ∧
      ¬Fin15AnchoredAtom3206 chi ∧
      ¬Fin15AnchoredAtom3525 chi ∧
      ¬Fin15AnchoredAtom3526 chi ∧
      ¬Fin15AnchoredAtom3527 chi ∧
      ¬Fin15AnchoredAtom3531 chi ∧
      ¬Fin15AnchoredAtom3535 chi ∧
      ¬Fin15AnchoredAtom4350 chi ∧
      ¬Fin15AnchoredAtom4351 chi ∧
      ¬Fin15AnchoredAtom4352 chi ∧
      ¬Fin15AnchoredAtom4356 chi ∧
      ¬Fin15AnchoredAtom4360 chi ∧
      ¬Fin15AnchoredAtom4821 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 3, 9, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask30219
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1927 Fin15AnchoredAtom1929 Fin15AnchoredAtom1930
    Fin15AnchoredAtom1931 Fin15AnchoredAtom1933 Fin15AnchoredAtom1934 Fin15AnchoredAtom1935
    Fin15AnchoredAtom1939 Fin15AnchoredAtom1940 Fin15AnchoredAtom1941 Fin15AnchoredAtom2088
    Fin15AnchoredAtom2089 Fin15AnchoredAtom2090 Fin15AnchoredAtom2094 Fin15AnchoredAtom2095
    Fin15AnchoredAtom2096 Fin15AnchoredAtom2100 Fin15AnchoredAtom2101 Fin15AnchoredAtom2102
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2473 Fin15AnchoredAtom2474 Fin15AnchoredAtom2475
    Fin15AnchoredAtom2479 Fin15AnchoredAtom2480 Fin15AnchoredAtom2481 Fin15AnchoredAtom2485
    Fin15AnchoredAtom2486 Fin15AnchoredAtom2487 Fin15AnchoredAtom2491 Fin15AnchoredAtom2810
    Fin15AnchoredAtom2811 Fin15AnchoredAtom2812 Fin15AnchoredAtom2816 Fin15AnchoredAtom2820
    Fin15AnchoredAtom3188 Fin15AnchoredAtom3189 Fin15AnchoredAtom3190 Fin15AnchoredAtom3194
    Fin15AnchoredAtom3195 Fin15AnchoredAtom3196 Fin15AnchoredAtom3200 Fin15AnchoredAtom3201
    Fin15AnchoredAtom3202 Fin15AnchoredAtom3206 Fin15AnchoredAtom3525 Fin15AnchoredAtom3526
    Fin15AnchoredAtom3527 Fin15AnchoredAtom3531 Fin15AnchoredAtom3535 Fin15AnchoredAtom4350
    Fin15AnchoredAtom4351 Fin15AnchoredAtom4352 Fin15AnchoredAtom4356 Fin15AnchoredAtom4360
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

theorem fin15Anchored_clause30963 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1942 chi ∧
      ¬Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom1972 chi ∧
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
      ¬Fin15AnchoredAtom2492 chi ∧
      ¬Fin15AnchoredAtom2494 chi ∧
      ¬Fin15AnchoredAtom2495 chi ∧
      ¬Fin15AnchoredAtom2501 chi ∧
      ¬Fin15AnchoredAtom2502 chi ∧
      ¬Fin15AnchoredAtom2513 chi ∧
      ¬Fin15AnchoredAtom2529 chi ∧
      ¬Fin15AnchoredAtom2530 chi ∧
      ¬Fin15AnchoredAtom2541 chi ∧
      ¬Fin15AnchoredAtom2562 chi ∧
      ¬Fin15AnchoredAtom2613 chi ∧
      ¬Fin15AnchoredAtom2614 chi ∧
      ¬Fin15AnchoredAtom2625 chi ∧
      ¬Fin15AnchoredAtom2646 chi ∧
      ¬Fin15AnchoredAtom2702 chi ∧
      ¬Fin15AnchoredAtom3207 chi ∧
      ¬Fin15AnchoredAtom3209 chi ∧
      ¬Fin15AnchoredAtom3210 chi ∧
      ¬Fin15AnchoredAtom3216 chi ∧
      ¬Fin15AnchoredAtom3217 chi ∧
      ¬Fin15AnchoredAtom3228 chi ∧
      ¬Fin15AnchoredAtom3244 chi ∧
      ¬Fin15AnchoredAtom3245 chi ∧
      ¬Fin15AnchoredAtom3256 chi ∧
      ¬Fin15AnchoredAtom3277 chi ∧
      ¬Fin15AnchoredAtom3328 chi ∧
      ¬Fin15AnchoredAtom3329 chi ∧
      ¬Fin15AnchoredAtom3340 chi ∧
      ¬Fin15AnchoredAtom3361 chi ∧
      ¬Fin15AnchoredAtom3417 chi ∧
      ¬Fin15AnchoredAtom4363 chi ∧
      ¬Fin15AnchoredAtom4364 chi ∧
      ¬Fin15AnchoredAtom4375 chi ∧
      ¬Fin15AnchoredAtom4396 chi ∧
      ¬Fin15AnchoredAtom4452 chi ∧
      ¬Fin15AnchoredAtom4578 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 5, 6, 7, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask01779
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1942 Fin15AnchoredAtom1943 Fin15AnchoredAtom1945
    Fin15AnchoredAtom1946 Fin15AnchoredAtom1951 Fin15AnchoredAtom1953 Fin15AnchoredAtom1954
    Fin15AnchoredAtom1960 Fin15AnchoredAtom1961 Fin15AnchoredAtom1972 Fin15AnchoredAtom1987
    Fin15AnchoredAtom1989 Fin15AnchoredAtom1990 Fin15AnchoredAtom1996 Fin15AnchoredAtom1997
    Fin15AnchoredAtom2008 Fin15AnchoredAtom2024 Fin15AnchoredAtom2025 Fin15AnchoredAtom2036
    Fin15AnchoredAtom2057 Fin15AnchoredAtom2492 Fin15AnchoredAtom2494 Fin15AnchoredAtom2495
    Fin15AnchoredAtom2501 Fin15AnchoredAtom2502 Fin15AnchoredAtom2513 Fin15AnchoredAtom2529
    Fin15AnchoredAtom2530 Fin15AnchoredAtom2541 Fin15AnchoredAtom2562 Fin15AnchoredAtom2613
    Fin15AnchoredAtom2614 Fin15AnchoredAtom2625 Fin15AnchoredAtom2646 Fin15AnchoredAtom2702
    Fin15AnchoredAtom3207 Fin15AnchoredAtom3209 Fin15AnchoredAtom3210 Fin15AnchoredAtom3216
    Fin15AnchoredAtom3217 Fin15AnchoredAtom3228 Fin15AnchoredAtom3244 Fin15AnchoredAtom3245
    Fin15AnchoredAtom3256 Fin15AnchoredAtom3277 Fin15AnchoredAtom3328 Fin15AnchoredAtom3329
    Fin15AnchoredAtom3340 Fin15AnchoredAtom3361 Fin15AnchoredAtom3417 Fin15AnchoredAtom4363
    Fin15AnchoredAtom4364 Fin15AnchoredAtom4375 Fin15AnchoredAtom4396 Fin15AnchoredAtom4452
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

theorem fin15Anchored_clause30964 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1942 chi ∧
      ¬Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom1974 chi ∧
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
      ¬Fin15AnchoredAtom2492 chi ∧
      ¬Fin15AnchoredAtom2494 chi ∧
      ¬Fin15AnchoredAtom2497 chi ∧
      ¬Fin15AnchoredAtom2501 chi ∧
      ¬Fin15AnchoredAtom2504 chi ∧
      ¬Fin15AnchoredAtom2515 chi ∧
      ¬Fin15AnchoredAtom2529 chi ∧
      ¬Fin15AnchoredAtom2532 chi ∧
      ¬Fin15AnchoredAtom2543 chi ∧
      ¬Fin15AnchoredAtom2564 chi ∧
      ¬Fin15AnchoredAtom2613 chi ∧
      ¬Fin15AnchoredAtom2616 chi ∧
      ¬Fin15AnchoredAtom2627 chi ∧
      ¬Fin15AnchoredAtom2648 chi ∧
      ¬Fin15AnchoredAtom2704 chi ∧
      ¬Fin15AnchoredAtom3207 chi ∧
      ¬Fin15AnchoredAtom3209 chi ∧
      ¬Fin15AnchoredAtom3212 chi ∧
      ¬Fin15AnchoredAtom3216 chi ∧
      ¬Fin15AnchoredAtom3219 chi ∧
      ¬Fin15AnchoredAtom3230 chi ∧
      ¬Fin15AnchoredAtom3244 chi ∧
      ¬Fin15AnchoredAtom3247 chi ∧
      ¬Fin15AnchoredAtom3258 chi ∧
      ¬Fin15AnchoredAtom3279 chi ∧
      ¬Fin15AnchoredAtom3328 chi ∧
      ¬Fin15AnchoredAtom3331 chi ∧
      ¬Fin15AnchoredAtom3342 chi ∧
      ¬Fin15AnchoredAtom3363 chi ∧
      ¬Fin15AnchoredAtom3419 chi ∧
      ¬Fin15AnchoredAtom4363 chi ∧
      ¬Fin15AnchoredAtom4366 chi ∧
      ¬Fin15AnchoredAtom4377 chi ∧
      ¬Fin15AnchoredAtom4398 chi ∧
      ¬Fin15AnchoredAtom4454 chi ∧
      ¬Fin15AnchoredAtom4580 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 5, 6, 7, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask04851
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1942 Fin15AnchoredAtom1943 Fin15AnchoredAtom1945
    Fin15AnchoredAtom1948 Fin15AnchoredAtom1951 Fin15AnchoredAtom1953 Fin15AnchoredAtom1956
    Fin15AnchoredAtom1960 Fin15AnchoredAtom1963 Fin15AnchoredAtom1974 Fin15AnchoredAtom1987
    Fin15AnchoredAtom1989 Fin15AnchoredAtom1992 Fin15AnchoredAtom1996 Fin15AnchoredAtom1999
    Fin15AnchoredAtom2010 Fin15AnchoredAtom2024 Fin15AnchoredAtom2027 Fin15AnchoredAtom2038
    Fin15AnchoredAtom2059 Fin15AnchoredAtom2492 Fin15AnchoredAtom2494 Fin15AnchoredAtom2497
    Fin15AnchoredAtom2501 Fin15AnchoredAtom2504 Fin15AnchoredAtom2515 Fin15AnchoredAtom2529
    Fin15AnchoredAtom2532 Fin15AnchoredAtom2543 Fin15AnchoredAtom2564 Fin15AnchoredAtom2613
    Fin15AnchoredAtom2616 Fin15AnchoredAtom2627 Fin15AnchoredAtom2648 Fin15AnchoredAtom2704
    Fin15AnchoredAtom3207 Fin15AnchoredAtom3209 Fin15AnchoredAtom3212 Fin15AnchoredAtom3216
    Fin15AnchoredAtom3219 Fin15AnchoredAtom3230 Fin15AnchoredAtom3244 Fin15AnchoredAtom3247
    Fin15AnchoredAtom3258 Fin15AnchoredAtom3279 Fin15AnchoredAtom3328 Fin15AnchoredAtom3331
    Fin15AnchoredAtom3342 Fin15AnchoredAtom3363 Fin15AnchoredAtom3419 Fin15AnchoredAtom4363
    Fin15AnchoredAtom4366 Fin15AnchoredAtom4377 Fin15AnchoredAtom4398 Fin15AnchoredAtom4454
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

theorem fin15Anchored_clause30965 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1942 chi ∧
      ¬Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom1975 chi ∧
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
      ¬Fin15AnchoredAtom2492 chi ∧
      ¬Fin15AnchoredAtom2494 chi ∧
      ¬Fin15AnchoredAtom2498 chi ∧
      ¬Fin15AnchoredAtom2501 chi ∧
      ¬Fin15AnchoredAtom2505 chi ∧
      ¬Fin15AnchoredAtom2516 chi ∧
      ¬Fin15AnchoredAtom2529 chi ∧
      ¬Fin15AnchoredAtom2533 chi ∧
      ¬Fin15AnchoredAtom2544 chi ∧
      ¬Fin15AnchoredAtom2565 chi ∧
      ¬Fin15AnchoredAtom2613 chi ∧
      ¬Fin15AnchoredAtom2617 chi ∧
      ¬Fin15AnchoredAtom2628 chi ∧
      ¬Fin15AnchoredAtom2649 chi ∧
      ¬Fin15AnchoredAtom2705 chi ∧
      ¬Fin15AnchoredAtom3207 chi ∧
      ¬Fin15AnchoredAtom3209 chi ∧
      ¬Fin15AnchoredAtom3213 chi ∧
      ¬Fin15AnchoredAtom3216 chi ∧
      ¬Fin15AnchoredAtom3220 chi ∧
      ¬Fin15AnchoredAtom3231 chi ∧
      ¬Fin15AnchoredAtom3244 chi ∧
      ¬Fin15AnchoredAtom3248 chi ∧
      ¬Fin15AnchoredAtom3259 chi ∧
      ¬Fin15AnchoredAtom3280 chi ∧
      ¬Fin15AnchoredAtom3328 chi ∧
      ¬Fin15AnchoredAtom3332 chi ∧
      ¬Fin15AnchoredAtom3343 chi ∧
      ¬Fin15AnchoredAtom3364 chi ∧
      ¬Fin15AnchoredAtom3420 chi ∧
      ¬Fin15AnchoredAtom4363 chi ∧
      ¬Fin15AnchoredAtom4367 chi ∧
      ¬Fin15AnchoredAtom4378 chi ∧
      ¬Fin15AnchoredAtom4399 chi ∧
      ¬Fin15AnchoredAtom4455 chi ∧
      ¬Fin15AnchoredAtom4581 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 5, 6, 7, 9, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask08947
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1942 Fin15AnchoredAtom1943 Fin15AnchoredAtom1945
    Fin15AnchoredAtom1949 Fin15AnchoredAtom1951 Fin15AnchoredAtom1953 Fin15AnchoredAtom1957
    Fin15AnchoredAtom1960 Fin15AnchoredAtom1964 Fin15AnchoredAtom1975 Fin15AnchoredAtom1987
    Fin15AnchoredAtom1989 Fin15AnchoredAtom1993 Fin15AnchoredAtom1996 Fin15AnchoredAtom2000
    Fin15AnchoredAtom2011 Fin15AnchoredAtom2024 Fin15AnchoredAtom2028 Fin15AnchoredAtom2039
    Fin15AnchoredAtom2060 Fin15AnchoredAtom2492 Fin15AnchoredAtom2494 Fin15AnchoredAtom2498
    Fin15AnchoredAtom2501 Fin15AnchoredAtom2505 Fin15AnchoredAtom2516 Fin15AnchoredAtom2529
    Fin15AnchoredAtom2533 Fin15AnchoredAtom2544 Fin15AnchoredAtom2565 Fin15AnchoredAtom2613
    Fin15AnchoredAtom2617 Fin15AnchoredAtom2628 Fin15AnchoredAtom2649 Fin15AnchoredAtom2705
    Fin15AnchoredAtom3207 Fin15AnchoredAtom3209 Fin15AnchoredAtom3213 Fin15AnchoredAtom3216
    Fin15AnchoredAtom3220 Fin15AnchoredAtom3231 Fin15AnchoredAtom3244 Fin15AnchoredAtom3248
    Fin15AnchoredAtom3259 Fin15AnchoredAtom3280 Fin15AnchoredAtom3328 Fin15AnchoredAtom3332
    Fin15AnchoredAtom3343 Fin15AnchoredAtom3364 Fin15AnchoredAtom3420 Fin15AnchoredAtom4363
    Fin15AnchoredAtom4367 Fin15AnchoredAtom4378 Fin15AnchoredAtom4399 Fin15AnchoredAtom4455
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

theorem fin15Anchored_clause30966 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1942 chi ∧
      ¬Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom1976 chi ∧
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
      ¬Fin15AnchoredAtom2492 chi ∧
      ¬Fin15AnchoredAtom2494 chi ∧
      ¬Fin15AnchoredAtom2499 chi ∧
      ¬Fin15AnchoredAtom2501 chi ∧
      ¬Fin15AnchoredAtom2506 chi ∧
      ¬Fin15AnchoredAtom2517 chi ∧
      ¬Fin15AnchoredAtom2529 chi ∧
      ¬Fin15AnchoredAtom2534 chi ∧
      ¬Fin15AnchoredAtom2545 chi ∧
      ¬Fin15AnchoredAtom2566 chi ∧
      ¬Fin15AnchoredAtom2613 chi ∧
      ¬Fin15AnchoredAtom2618 chi ∧
      ¬Fin15AnchoredAtom2629 chi ∧
      ¬Fin15AnchoredAtom2650 chi ∧
      ¬Fin15AnchoredAtom2706 chi ∧
      ¬Fin15AnchoredAtom3207 chi ∧
      ¬Fin15AnchoredAtom3209 chi ∧
      ¬Fin15AnchoredAtom3214 chi ∧
      ¬Fin15AnchoredAtom3216 chi ∧
      ¬Fin15AnchoredAtom3221 chi ∧
      ¬Fin15AnchoredAtom3232 chi ∧
      ¬Fin15AnchoredAtom3244 chi ∧
      ¬Fin15AnchoredAtom3249 chi ∧
      ¬Fin15AnchoredAtom3260 chi ∧
      ¬Fin15AnchoredAtom3281 chi ∧
      ¬Fin15AnchoredAtom3328 chi ∧
      ¬Fin15AnchoredAtom3333 chi ∧
      ¬Fin15AnchoredAtom3344 chi ∧
      ¬Fin15AnchoredAtom3365 chi ∧
      ¬Fin15AnchoredAtom3421 chi ∧
      ¬Fin15AnchoredAtom4363 chi ∧
      ¬Fin15AnchoredAtom4368 chi ∧
      ¬Fin15AnchoredAtom4379 chi ∧
      ¬Fin15AnchoredAtom4400 chi ∧
      ¬Fin15AnchoredAtom4456 chi ∧
      ¬Fin15AnchoredAtom4582 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 5, 6, 7, 9, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17139
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1942 Fin15AnchoredAtom1943 Fin15AnchoredAtom1945
    Fin15AnchoredAtom1950 Fin15AnchoredAtom1951 Fin15AnchoredAtom1953 Fin15AnchoredAtom1958
    Fin15AnchoredAtom1960 Fin15AnchoredAtom1965 Fin15AnchoredAtom1976 Fin15AnchoredAtom1987
    Fin15AnchoredAtom1989 Fin15AnchoredAtom1994 Fin15AnchoredAtom1996 Fin15AnchoredAtom2001
    Fin15AnchoredAtom2012 Fin15AnchoredAtom2024 Fin15AnchoredAtom2029 Fin15AnchoredAtom2040
    Fin15AnchoredAtom2061 Fin15AnchoredAtom2492 Fin15AnchoredAtom2494 Fin15AnchoredAtom2499
    Fin15AnchoredAtom2501 Fin15AnchoredAtom2506 Fin15AnchoredAtom2517 Fin15AnchoredAtom2529
    Fin15AnchoredAtom2534 Fin15AnchoredAtom2545 Fin15AnchoredAtom2566 Fin15AnchoredAtom2613
    Fin15AnchoredAtom2618 Fin15AnchoredAtom2629 Fin15AnchoredAtom2650 Fin15AnchoredAtom2706
    Fin15AnchoredAtom3207 Fin15AnchoredAtom3209 Fin15AnchoredAtom3214 Fin15AnchoredAtom3216
    Fin15AnchoredAtom3221 Fin15AnchoredAtom3232 Fin15AnchoredAtom3244 Fin15AnchoredAtom3249
    Fin15AnchoredAtom3260 Fin15AnchoredAtom3281 Fin15AnchoredAtom3328 Fin15AnchoredAtom3333
    Fin15AnchoredAtom3344 Fin15AnchoredAtom3365 Fin15AnchoredAtom3421 Fin15AnchoredAtom4363
    Fin15AnchoredAtom4368 Fin15AnchoredAtom4379 Fin15AnchoredAtom4400 Fin15AnchoredAtom4456
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

theorem fin15Anchored_clause30967 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1942 chi ∧
      ¬Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom1978 chi ∧
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
      ¬Fin15AnchoredAtom2492 chi ∧
      ¬Fin15AnchoredAtom2495 chi ∧
      ¬Fin15AnchoredAtom2497 chi ∧
      ¬Fin15AnchoredAtom2502 chi ∧
      ¬Fin15AnchoredAtom2504 chi ∧
      ¬Fin15AnchoredAtom2519 chi ∧
      ¬Fin15AnchoredAtom2530 chi ∧
      ¬Fin15AnchoredAtom2532 chi ∧
      ¬Fin15AnchoredAtom2547 chi ∧
      ¬Fin15AnchoredAtom2568 chi ∧
      ¬Fin15AnchoredAtom2614 chi ∧
      ¬Fin15AnchoredAtom2616 chi ∧
      ¬Fin15AnchoredAtom2631 chi ∧
      ¬Fin15AnchoredAtom2652 chi ∧
      ¬Fin15AnchoredAtom2708 chi ∧
      ¬Fin15AnchoredAtom3207 chi ∧
      ¬Fin15AnchoredAtom3210 chi ∧
      ¬Fin15AnchoredAtom3212 chi ∧
      ¬Fin15AnchoredAtom3217 chi ∧
      ¬Fin15AnchoredAtom3219 chi ∧
      ¬Fin15AnchoredAtom3234 chi ∧
      ¬Fin15AnchoredAtom3245 chi ∧
      ¬Fin15AnchoredAtom3247 chi ∧
      ¬Fin15AnchoredAtom3262 chi ∧
      ¬Fin15AnchoredAtom3283 chi ∧
      ¬Fin15AnchoredAtom3329 chi ∧
      ¬Fin15AnchoredAtom3331 chi ∧
      ¬Fin15AnchoredAtom3346 chi ∧
      ¬Fin15AnchoredAtom3367 chi ∧
      ¬Fin15AnchoredAtom3423 chi ∧
      ¬Fin15AnchoredAtom4364 chi ∧
      ¬Fin15AnchoredAtom4366 chi ∧
      ¬Fin15AnchoredAtom4381 chi ∧
      ¬Fin15AnchoredAtom4402 chi ∧
      ¬Fin15AnchoredAtom4458 chi ∧
      ¬Fin15AnchoredAtom4584 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 5, 6, 7, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05363
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1942 Fin15AnchoredAtom1943 Fin15AnchoredAtom1946
    Fin15AnchoredAtom1948 Fin15AnchoredAtom1951 Fin15AnchoredAtom1954 Fin15AnchoredAtom1956
    Fin15AnchoredAtom1961 Fin15AnchoredAtom1963 Fin15AnchoredAtom1978 Fin15AnchoredAtom1987
    Fin15AnchoredAtom1990 Fin15AnchoredAtom1992 Fin15AnchoredAtom1997 Fin15AnchoredAtom1999
    Fin15AnchoredAtom2014 Fin15AnchoredAtom2025 Fin15AnchoredAtom2027 Fin15AnchoredAtom2042
    Fin15AnchoredAtom2063 Fin15AnchoredAtom2492 Fin15AnchoredAtom2495 Fin15AnchoredAtom2497
    Fin15AnchoredAtom2502 Fin15AnchoredAtom2504 Fin15AnchoredAtom2519 Fin15AnchoredAtom2530
    Fin15AnchoredAtom2532 Fin15AnchoredAtom2547 Fin15AnchoredAtom2568 Fin15AnchoredAtom2614
    Fin15AnchoredAtom2616 Fin15AnchoredAtom2631 Fin15AnchoredAtom2652 Fin15AnchoredAtom2708
    Fin15AnchoredAtom3207 Fin15AnchoredAtom3210 Fin15AnchoredAtom3212 Fin15AnchoredAtom3217
    Fin15AnchoredAtom3219 Fin15AnchoredAtom3234 Fin15AnchoredAtom3245 Fin15AnchoredAtom3247
    Fin15AnchoredAtom3262 Fin15AnchoredAtom3283 Fin15AnchoredAtom3329 Fin15AnchoredAtom3331
    Fin15AnchoredAtom3346 Fin15AnchoredAtom3367 Fin15AnchoredAtom3423 Fin15AnchoredAtom4364
    Fin15AnchoredAtom4366 Fin15AnchoredAtom4381 Fin15AnchoredAtom4402 Fin15AnchoredAtom4458
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

theorem fin15Anchored_clause30968 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1942 chi ∧
      ¬Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom1979 chi ∧
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
      ¬Fin15AnchoredAtom2492 chi ∧
      ¬Fin15AnchoredAtom2495 chi ∧
      ¬Fin15AnchoredAtom2498 chi ∧
      ¬Fin15AnchoredAtom2502 chi ∧
      ¬Fin15AnchoredAtom2505 chi ∧
      ¬Fin15AnchoredAtom2520 chi ∧
      ¬Fin15AnchoredAtom2530 chi ∧
      ¬Fin15AnchoredAtom2533 chi ∧
      ¬Fin15AnchoredAtom2548 chi ∧
      ¬Fin15AnchoredAtom2569 chi ∧
      ¬Fin15AnchoredAtom2614 chi ∧
      ¬Fin15AnchoredAtom2617 chi ∧
      ¬Fin15AnchoredAtom2632 chi ∧
      ¬Fin15AnchoredAtom2653 chi ∧
      ¬Fin15AnchoredAtom2709 chi ∧
      ¬Fin15AnchoredAtom3207 chi ∧
      ¬Fin15AnchoredAtom3210 chi ∧
      ¬Fin15AnchoredAtom3213 chi ∧
      ¬Fin15AnchoredAtom3217 chi ∧
      ¬Fin15AnchoredAtom3220 chi ∧
      ¬Fin15AnchoredAtom3235 chi ∧
      ¬Fin15AnchoredAtom3245 chi ∧
      ¬Fin15AnchoredAtom3248 chi ∧
      ¬Fin15AnchoredAtom3263 chi ∧
      ¬Fin15AnchoredAtom3284 chi ∧
      ¬Fin15AnchoredAtom3329 chi ∧
      ¬Fin15AnchoredAtom3332 chi ∧
      ¬Fin15AnchoredAtom3347 chi ∧
      ¬Fin15AnchoredAtom3368 chi ∧
      ¬Fin15AnchoredAtom3424 chi ∧
      ¬Fin15AnchoredAtom4364 chi ∧
      ¬Fin15AnchoredAtom4367 chi ∧
      ¬Fin15AnchoredAtom4382 chi ∧
      ¬Fin15AnchoredAtom4403 chi ∧
      ¬Fin15AnchoredAtom4459 chi ∧
      ¬Fin15AnchoredAtom4585 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 5, 6, 7, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09459
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1942 Fin15AnchoredAtom1943 Fin15AnchoredAtom1946
    Fin15AnchoredAtom1949 Fin15AnchoredAtom1951 Fin15AnchoredAtom1954 Fin15AnchoredAtom1957
    Fin15AnchoredAtom1961 Fin15AnchoredAtom1964 Fin15AnchoredAtom1979 Fin15AnchoredAtom1987
    Fin15AnchoredAtom1990 Fin15AnchoredAtom1993 Fin15AnchoredAtom1997 Fin15AnchoredAtom2000
    Fin15AnchoredAtom2015 Fin15AnchoredAtom2025 Fin15AnchoredAtom2028 Fin15AnchoredAtom2043
    Fin15AnchoredAtom2064 Fin15AnchoredAtom2492 Fin15AnchoredAtom2495 Fin15AnchoredAtom2498
    Fin15AnchoredAtom2502 Fin15AnchoredAtom2505 Fin15AnchoredAtom2520 Fin15AnchoredAtom2530
    Fin15AnchoredAtom2533 Fin15AnchoredAtom2548 Fin15AnchoredAtom2569 Fin15AnchoredAtom2614
    Fin15AnchoredAtom2617 Fin15AnchoredAtom2632 Fin15AnchoredAtom2653 Fin15AnchoredAtom2709
    Fin15AnchoredAtom3207 Fin15AnchoredAtom3210 Fin15AnchoredAtom3213 Fin15AnchoredAtom3217
    Fin15AnchoredAtom3220 Fin15AnchoredAtom3235 Fin15AnchoredAtom3245 Fin15AnchoredAtom3248
    Fin15AnchoredAtom3263 Fin15AnchoredAtom3284 Fin15AnchoredAtom3329 Fin15AnchoredAtom3332
    Fin15AnchoredAtom3347 Fin15AnchoredAtom3368 Fin15AnchoredAtom3424 Fin15AnchoredAtom4364
    Fin15AnchoredAtom4367 Fin15AnchoredAtom4382 Fin15AnchoredAtom4403 Fin15AnchoredAtom4459
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

theorem fin15Anchored_clause30969 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1942 chi ∧
      ¬Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom1980 chi ∧
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
      ¬Fin15AnchoredAtom2492 chi ∧
      ¬Fin15AnchoredAtom2495 chi ∧
      ¬Fin15AnchoredAtom2499 chi ∧
      ¬Fin15AnchoredAtom2502 chi ∧
      ¬Fin15AnchoredAtom2506 chi ∧
      ¬Fin15AnchoredAtom2521 chi ∧
      ¬Fin15AnchoredAtom2530 chi ∧
      ¬Fin15AnchoredAtom2534 chi ∧
      ¬Fin15AnchoredAtom2549 chi ∧
      ¬Fin15AnchoredAtom2570 chi ∧
      ¬Fin15AnchoredAtom2614 chi ∧
      ¬Fin15AnchoredAtom2618 chi ∧
      ¬Fin15AnchoredAtom2633 chi ∧
      ¬Fin15AnchoredAtom2654 chi ∧
      ¬Fin15AnchoredAtom2710 chi ∧
      ¬Fin15AnchoredAtom3207 chi ∧
      ¬Fin15AnchoredAtom3210 chi ∧
      ¬Fin15AnchoredAtom3214 chi ∧
      ¬Fin15AnchoredAtom3217 chi ∧
      ¬Fin15AnchoredAtom3221 chi ∧
      ¬Fin15AnchoredAtom3236 chi ∧
      ¬Fin15AnchoredAtom3245 chi ∧
      ¬Fin15AnchoredAtom3249 chi ∧
      ¬Fin15AnchoredAtom3264 chi ∧
      ¬Fin15AnchoredAtom3285 chi ∧
      ¬Fin15AnchoredAtom3329 chi ∧
      ¬Fin15AnchoredAtom3333 chi ∧
      ¬Fin15AnchoredAtom3348 chi ∧
      ¬Fin15AnchoredAtom3369 chi ∧
      ¬Fin15AnchoredAtom3425 chi ∧
      ¬Fin15AnchoredAtom4364 chi ∧
      ¬Fin15AnchoredAtom4368 chi ∧
      ¬Fin15AnchoredAtom4383 chi ∧
      ¬Fin15AnchoredAtom4404 chi ∧
      ¬Fin15AnchoredAtom4460 chi ∧
      ¬Fin15AnchoredAtom4586 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 5, 6, 7, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17651
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1942 Fin15AnchoredAtom1943 Fin15AnchoredAtom1946
    Fin15AnchoredAtom1950 Fin15AnchoredAtom1951 Fin15AnchoredAtom1954 Fin15AnchoredAtom1958
    Fin15AnchoredAtom1961 Fin15AnchoredAtom1965 Fin15AnchoredAtom1980 Fin15AnchoredAtom1987
    Fin15AnchoredAtom1990 Fin15AnchoredAtom1994 Fin15AnchoredAtom1997 Fin15AnchoredAtom2001
    Fin15AnchoredAtom2016 Fin15AnchoredAtom2025 Fin15AnchoredAtom2029 Fin15AnchoredAtom2044
    Fin15AnchoredAtom2065 Fin15AnchoredAtom2492 Fin15AnchoredAtom2495 Fin15AnchoredAtom2499
    Fin15AnchoredAtom2502 Fin15AnchoredAtom2506 Fin15AnchoredAtom2521 Fin15AnchoredAtom2530
    Fin15AnchoredAtom2534 Fin15AnchoredAtom2549 Fin15AnchoredAtom2570 Fin15AnchoredAtom2614
    Fin15AnchoredAtom2618 Fin15AnchoredAtom2633 Fin15AnchoredAtom2654 Fin15AnchoredAtom2710
    Fin15AnchoredAtom3207 Fin15AnchoredAtom3210 Fin15AnchoredAtom3214 Fin15AnchoredAtom3217
    Fin15AnchoredAtom3221 Fin15AnchoredAtom3236 Fin15AnchoredAtom3245 Fin15AnchoredAtom3249
    Fin15AnchoredAtom3264 Fin15AnchoredAtom3285 Fin15AnchoredAtom3329 Fin15AnchoredAtom3333
    Fin15AnchoredAtom3348 Fin15AnchoredAtom3369 Fin15AnchoredAtom3425 Fin15AnchoredAtom4364
    Fin15AnchoredAtom4368 Fin15AnchoredAtom4383 Fin15AnchoredAtom4404 Fin15AnchoredAtom4460
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

theorem fin15Anchored_clause30970 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1942 chi ∧
      ¬Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom1984 chi ∧
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
      ¬Fin15AnchoredAtom2492 chi ∧
      ¬Fin15AnchoredAtom2497 chi ∧
      ¬Fin15AnchoredAtom2498 chi ∧
      ¬Fin15AnchoredAtom2504 chi ∧
      ¬Fin15AnchoredAtom2505 chi ∧
      ¬Fin15AnchoredAtom2525 chi ∧
      ¬Fin15AnchoredAtom2532 chi ∧
      ¬Fin15AnchoredAtom2533 chi ∧
      ¬Fin15AnchoredAtom2553 chi ∧
      ¬Fin15AnchoredAtom2574 chi ∧
      ¬Fin15AnchoredAtom2616 chi ∧
      ¬Fin15AnchoredAtom2617 chi ∧
      ¬Fin15AnchoredAtom2637 chi ∧
      ¬Fin15AnchoredAtom2658 chi ∧
      ¬Fin15AnchoredAtom2714 chi ∧
      ¬Fin15AnchoredAtom3207 chi ∧
      ¬Fin15AnchoredAtom3212 chi ∧
      ¬Fin15AnchoredAtom3213 chi ∧
      ¬Fin15AnchoredAtom3219 chi ∧
      ¬Fin15AnchoredAtom3220 chi ∧
      ¬Fin15AnchoredAtom3240 chi ∧
      ¬Fin15AnchoredAtom3247 chi ∧
      ¬Fin15AnchoredAtom3248 chi ∧
      ¬Fin15AnchoredAtom3268 chi ∧
      ¬Fin15AnchoredAtom3289 chi ∧
      ¬Fin15AnchoredAtom3331 chi ∧
      ¬Fin15AnchoredAtom3332 chi ∧
      ¬Fin15AnchoredAtom3352 chi ∧
      ¬Fin15AnchoredAtom3373 chi ∧
      ¬Fin15AnchoredAtom3429 chi ∧
      ¬Fin15AnchoredAtom4366 chi ∧
      ¬Fin15AnchoredAtom4367 chi ∧
      ¬Fin15AnchoredAtom4387 chi ∧
      ¬Fin15AnchoredAtom4408 chi ∧
      ¬Fin15AnchoredAtom4464 chi ∧
      ¬Fin15AnchoredAtom4590 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 5, 6, 7, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask12531
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1942 Fin15AnchoredAtom1943 Fin15AnchoredAtom1948
    Fin15AnchoredAtom1949 Fin15AnchoredAtom1951 Fin15AnchoredAtom1956 Fin15AnchoredAtom1957
    Fin15AnchoredAtom1963 Fin15AnchoredAtom1964 Fin15AnchoredAtom1984 Fin15AnchoredAtom1987
    Fin15AnchoredAtom1992 Fin15AnchoredAtom1993 Fin15AnchoredAtom1999 Fin15AnchoredAtom2000
    Fin15AnchoredAtom2020 Fin15AnchoredAtom2027 Fin15AnchoredAtom2028 Fin15AnchoredAtom2048
    Fin15AnchoredAtom2069 Fin15AnchoredAtom2492 Fin15AnchoredAtom2497 Fin15AnchoredAtom2498
    Fin15AnchoredAtom2504 Fin15AnchoredAtom2505 Fin15AnchoredAtom2525 Fin15AnchoredAtom2532
    Fin15AnchoredAtom2533 Fin15AnchoredAtom2553 Fin15AnchoredAtom2574 Fin15AnchoredAtom2616
    Fin15AnchoredAtom2617 Fin15AnchoredAtom2637 Fin15AnchoredAtom2658 Fin15AnchoredAtom2714
    Fin15AnchoredAtom3207 Fin15AnchoredAtom3212 Fin15AnchoredAtom3213 Fin15AnchoredAtom3219
    Fin15AnchoredAtom3220 Fin15AnchoredAtom3240 Fin15AnchoredAtom3247 Fin15AnchoredAtom3248
    Fin15AnchoredAtom3268 Fin15AnchoredAtom3289 Fin15AnchoredAtom3331 Fin15AnchoredAtom3332
    Fin15AnchoredAtom3352 Fin15AnchoredAtom3373 Fin15AnchoredAtom3429 Fin15AnchoredAtom4366
    Fin15AnchoredAtom4367 Fin15AnchoredAtom4387 Fin15AnchoredAtom4408 Fin15AnchoredAtom4464
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

theorem fin15Anchored_clause30971 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1942 chi ∧
      ¬Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom1985 chi ∧
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
      ¬Fin15AnchoredAtom2492 chi ∧
      ¬Fin15AnchoredAtom2497 chi ∧
      ¬Fin15AnchoredAtom2499 chi ∧
      ¬Fin15AnchoredAtom2504 chi ∧
      ¬Fin15AnchoredAtom2506 chi ∧
      ¬Fin15AnchoredAtom2526 chi ∧
      ¬Fin15AnchoredAtom2532 chi ∧
      ¬Fin15AnchoredAtom2534 chi ∧
      ¬Fin15AnchoredAtom2554 chi ∧
      ¬Fin15AnchoredAtom2575 chi ∧
      ¬Fin15AnchoredAtom2616 chi ∧
      ¬Fin15AnchoredAtom2618 chi ∧
      ¬Fin15AnchoredAtom2638 chi ∧
      ¬Fin15AnchoredAtom2659 chi ∧
      ¬Fin15AnchoredAtom2715 chi ∧
      ¬Fin15AnchoredAtom3207 chi ∧
      ¬Fin15AnchoredAtom3212 chi ∧
      ¬Fin15AnchoredAtom3214 chi ∧
      ¬Fin15AnchoredAtom3219 chi ∧
      ¬Fin15AnchoredAtom3221 chi ∧
      ¬Fin15AnchoredAtom3241 chi ∧
      ¬Fin15AnchoredAtom3247 chi ∧
      ¬Fin15AnchoredAtom3249 chi ∧
      ¬Fin15AnchoredAtom3269 chi ∧
      ¬Fin15AnchoredAtom3290 chi ∧
      ¬Fin15AnchoredAtom3331 chi ∧
      ¬Fin15AnchoredAtom3333 chi ∧
      ¬Fin15AnchoredAtom3353 chi ∧
      ¬Fin15AnchoredAtom3374 chi ∧
      ¬Fin15AnchoredAtom3430 chi ∧
      ¬Fin15AnchoredAtom4366 chi ∧
      ¬Fin15AnchoredAtom4368 chi ∧
      ¬Fin15AnchoredAtom4388 chi ∧
      ¬Fin15AnchoredAtom4409 chi ∧
      ¬Fin15AnchoredAtom4465 chi ∧
      ¬Fin15AnchoredAtom4591 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 5, 6, 7, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask20723
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1942 Fin15AnchoredAtom1943 Fin15AnchoredAtom1948
    Fin15AnchoredAtom1950 Fin15AnchoredAtom1951 Fin15AnchoredAtom1956 Fin15AnchoredAtom1958
    Fin15AnchoredAtom1963 Fin15AnchoredAtom1965 Fin15AnchoredAtom1985 Fin15AnchoredAtom1987
    Fin15AnchoredAtom1992 Fin15AnchoredAtom1994 Fin15AnchoredAtom1999 Fin15AnchoredAtom2001
    Fin15AnchoredAtom2021 Fin15AnchoredAtom2027 Fin15AnchoredAtom2029 Fin15AnchoredAtom2049
    Fin15AnchoredAtom2070 Fin15AnchoredAtom2492 Fin15AnchoredAtom2497 Fin15AnchoredAtom2499
    Fin15AnchoredAtom2504 Fin15AnchoredAtom2506 Fin15AnchoredAtom2526 Fin15AnchoredAtom2532
    Fin15AnchoredAtom2534 Fin15AnchoredAtom2554 Fin15AnchoredAtom2575 Fin15AnchoredAtom2616
    Fin15AnchoredAtom2618 Fin15AnchoredAtom2638 Fin15AnchoredAtom2659 Fin15AnchoredAtom2715
    Fin15AnchoredAtom3207 Fin15AnchoredAtom3212 Fin15AnchoredAtom3214 Fin15AnchoredAtom3219
    Fin15AnchoredAtom3221 Fin15AnchoredAtom3241 Fin15AnchoredAtom3247 Fin15AnchoredAtom3249
    Fin15AnchoredAtom3269 Fin15AnchoredAtom3290 Fin15AnchoredAtom3331 Fin15AnchoredAtom3333
    Fin15AnchoredAtom3353 Fin15AnchoredAtom3374 Fin15AnchoredAtom3430 Fin15AnchoredAtom4366
    Fin15AnchoredAtom4368 Fin15AnchoredAtom4388 Fin15AnchoredAtom4409 Fin15AnchoredAtom4465
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

theorem fin15Anchored_clause30972 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1942 chi ∧
      ¬Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom1986 chi ∧
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
      ¬Fin15AnchoredAtom2492 chi ∧
      ¬Fin15AnchoredAtom2498 chi ∧
      ¬Fin15AnchoredAtom2499 chi ∧
      ¬Fin15AnchoredAtom2505 chi ∧
      ¬Fin15AnchoredAtom2506 chi ∧
      ¬Fin15AnchoredAtom2527 chi ∧
      ¬Fin15AnchoredAtom2533 chi ∧
      ¬Fin15AnchoredAtom2534 chi ∧
      ¬Fin15AnchoredAtom2555 chi ∧
      ¬Fin15AnchoredAtom2576 chi ∧
      ¬Fin15AnchoredAtom2617 chi ∧
      ¬Fin15AnchoredAtom2618 chi ∧
      ¬Fin15AnchoredAtom2639 chi ∧
      ¬Fin15AnchoredAtom2660 chi ∧
      ¬Fin15AnchoredAtom2716 chi ∧
      ¬Fin15AnchoredAtom3207 chi ∧
      ¬Fin15AnchoredAtom3213 chi ∧
      ¬Fin15AnchoredAtom3214 chi ∧
      ¬Fin15AnchoredAtom3220 chi ∧
      ¬Fin15AnchoredAtom3221 chi ∧
      ¬Fin15AnchoredAtom3242 chi ∧
      ¬Fin15AnchoredAtom3248 chi ∧
      ¬Fin15AnchoredAtom3249 chi ∧
      ¬Fin15AnchoredAtom3270 chi ∧
      ¬Fin15AnchoredAtom3291 chi ∧
      ¬Fin15AnchoredAtom3332 chi ∧
      ¬Fin15AnchoredAtom3333 chi ∧
      ¬Fin15AnchoredAtom3354 chi ∧
      ¬Fin15AnchoredAtom3375 chi ∧
      ¬Fin15AnchoredAtom3431 chi ∧
      ¬Fin15AnchoredAtom4367 chi ∧
      ¬Fin15AnchoredAtom4368 chi ∧
      ¬Fin15AnchoredAtom4389 chi ∧
      ¬Fin15AnchoredAtom4410 chi ∧
      ¬Fin15AnchoredAtom4466 chi ∧
      ¬Fin15AnchoredAtom4592 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 5, 6, 7, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask24819
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1942 Fin15AnchoredAtom1943 Fin15AnchoredAtom1949
    Fin15AnchoredAtom1950 Fin15AnchoredAtom1951 Fin15AnchoredAtom1957 Fin15AnchoredAtom1958
    Fin15AnchoredAtom1964 Fin15AnchoredAtom1965 Fin15AnchoredAtom1986 Fin15AnchoredAtom1987
    Fin15AnchoredAtom1993 Fin15AnchoredAtom1994 Fin15AnchoredAtom2000 Fin15AnchoredAtom2001
    Fin15AnchoredAtom2022 Fin15AnchoredAtom2028 Fin15AnchoredAtom2029 Fin15AnchoredAtom2050
    Fin15AnchoredAtom2071 Fin15AnchoredAtom2492 Fin15AnchoredAtom2498 Fin15AnchoredAtom2499
    Fin15AnchoredAtom2505 Fin15AnchoredAtom2506 Fin15AnchoredAtom2527 Fin15AnchoredAtom2533
    Fin15AnchoredAtom2534 Fin15AnchoredAtom2555 Fin15AnchoredAtom2576 Fin15AnchoredAtom2617
    Fin15AnchoredAtom2618 Fin15AnchoredAtom2639 Fin15AnchoredAtom2660 Fin15AnchoredAtom2716
    Fin15AnchoredAtom3207 Fin15AnchoredAtom3213 Fin15AnchoredAtom3214 Fin15AnchoredAtom3220
    Fin15AnchoredAtom3221 Fin15AnchoredAtom3242 Fin15AnchoredAtom3248 Fin15AnchoredAtom3249
    Fin15AnchoredAtom3270 Fin15AnchoredAtom3291 Fin15AnchoredAtom3332 Fin15AnchoredAtom3333
    Fin15AnchoredAtom3354 Fin15AnchoredAtom3375 Fin15AnchoredAtom3431 Fin15AnchoredAtom4367
    Fin15AnchoredAtom4368 Fin15AnchoredAtom4389 Fin15AnchoredAtom4410 Fin15AnchoredAtom4466
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

theorem fin15Anchored_clause30973 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1942 chi ∧
      ¬Fin15AnchoredAtom1944 chi ∧
      ¬Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom1952 chi ∧
      ¬Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom1966 chi ∧
      ¬Fin15AnchoredAtom1970 chi ∧
      ¬Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom1988 chi ∧
      ¬Fin15AnchoredAtom1989 chi ∧
      ¬Fin15AnchoredAtom1993 chi ∧
      ¬Fin15AnchoredAtom2002 chi ∧
      ¬Fin15AnchoredAtom2006 chi ∧
      ¬Fin15AnchoredAtom2011 chi ∧
      ¬Fin15AnchoredAtom2030 chi ∧
      ¬Fin15AnchoredAtom2034 chi ∧
      ¬Fin15AnchoredAtom2039 chi ∧
      ¬Fin15AnchoredAtom2075 chi ∧
      ¬Fin15AnchoredAtom2493 chi ∧
      ¬Fin15AnchoredAtom2494 chi ∧
      ¬Fin15AnchoredAtom2498 chi ∧
      ¬Fin15AnchoredAtom2507 chi ∧
      ¬Fin15AnchoredAtom2511 chi ∧
      ¬Fin15AnchoredAtom2516 chi ∧
      ¬Fin15AnchoredAtom2535 chi ∧
      ¬Fin15AnchoredAtom2539 chi ∧
      ¬Fin15AnchoredAtom2544 chi ∧
      ¬Fin15AnchoredAtom2580 chi ∧
      ¬Fin15AnchoredAtom2619 chi ∧
      ¬Fin15AnchoredAtom2623 chi ∧
      ¬Fin15AnchoredAtom2628 chi ∧
      ¬Fin15AnchoredAtom2664 chi ∧
      ¬Fin15AnchoredAtom2720 chi ∧
      ¬Fin15AnchoredAtom3208 chi ∧
      ¬Fin15AnchoredAtom3209 chi ∧
      ¬Fin15AnchoredAtom3213 chi ∧
      ¬Fin15AnchoredAtom3222 chi ∧
      ¬Fin15AnchoredAtom3226 chi ∧
      ¬Fin15AnchoredAtom3231 chi ∧
      ¬Fin15AnchoredAtom3250 chi ∧
      ¬Fin15AnchoredAtom3254 chi ∧
      ¬Fin15AnchoredAtom3259 chi ∧
      ¬Fin15AnchoredAtom3295 chi ∧
      ¬Fin15AnchoredAtom3334 chi ∧
      ¬Fin15AnchoredAtom3338 chi ∧
      ¬Fin15AnchoredAtom3343 chi ∧
      ¬Fin15AnchoredAtom3379 chi ∧
      ¬Fin15AnchoredAtom3435 chi ∧
      ¬Fin15AnchoredAtom4369 chi ∧
      ¬Fin15AnchoredAtom4373 chi ∧
      ¬Fin15AnchoredAtom4378 chi ∧
      ¬Fin15AnchoredAtom4414 chi ∧
      ¬Fin15AnchoredAtom4470 chi ∧
      ¬Fin15AnchoredAtom4596 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 5, 6, 8, 9, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09075
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1942 Fin15AnchoredAtom1944 Fin15AnchoredAtom1945
    Fin15AnchoredAtom1949 Fin15AnchoredAtom1952 Fin15AnchoredAtom1953 Fin15AnchoredAtom1957
    Fin15AnchoredAtom1966 Fin15AnchoredAtom1970 Fin15AnchoredAtom1975 Fin15AnchoredAtom1988
    Fin15AnchoredAtom1989 Fin15AnchoredAtom1993 Fin15AnchoredAtom2002 Fin15AnchoredAtom2006
    Fin15AnchoredAtom2011 Fin15AnchoredAtom2030 Fin15AnchoredAtom2034 Fin15AnchoredAtom2039
    Fin15AnchoredAtom2075 Fin15AnchoredAtom2493 Fin15AnchoredAtom2494 Fin15AnchoredAtom2498
    Fin15AnchoredAtom2507 Fin15AnchoredAtom2511 Fin15AnchoredAtom2516 Fin15AnchoredAtom2535
    Fin15AnchoredAtom2539 Fin15AnchoredAtom2544 Fin15AnchoredAtom2580 Fin15AnchoredAtom2619
    Fin15AnchoredAtom2623 Fin15AnchoredAtom2628 Fin15AnchoredAtom2664 Fin15AnchoredAtom2720
    Fin15AnchoredAtom3208 Fin15AnchoredAtom3209 Fin15AnchoredAtom3213 Fin15AnchoredAtom3222
    Fin15AnchoredAtom3226 Fin15AnchoredAtom3231 Fin15AnchoredAtom3250 Fin15AnchoredAtom3254
    Fin15AnchoredAtom3259 Fin15AnchoredAtom3295 Fin15AnchoredAtom3334 Fin15AnchoredAtom3338
    Fin15AnchoredAtom3343 Fin15AnchoredAtom3379 Fin15AnchoredAtom3435 Fin15AnchoredAtom4369
    Fin15AnchoredAtom4373 Fin15AnchoredAtom4378 Fin15AnchoredAtom4414 Fin15AnchoredAtom4470
    Fin15AnchoredAtom4596 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30974 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1942 chi ∧
      ¬Fin15AnchoredAtom1944 chi ∧
      ¬Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom1952 chi ∧
      ¬Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom1966 chi ∧
      ¬Fin15AnchoredAtom1971 chi ∧
      ¬Fin15AnchoredAtom1976 chi ∧
      ¬Fin15AnchoredAtom1988 chi ∧
      ¬Fin15AnchoredAtom1989 chi ∧
      ¬Fin15AnchoredAtom1994 chi ∧
      ¬Fin15AnchoredAtom2002 chi ∧
      ¬Fin15AnchoredAtom2007 chi ∧
      ¬Fin15AnchoredAtom2012 chi ∧
      ¬Fin15AnchoredAtom2030 chi ∧
      ¬Fin15AnchoredAtom2035 chi ∧
      ¬Fin15AnchoredAtom2040 chi ∧
      ¬Fin15AnchoredAtom2076 chi ∧
      ¬Fin15AnchoredAtom2493 chi ∧
      ¬Fin15AnchoredAtom2494 chi ∧
      ¬Fin15AnchoredAtom2499 chi ∧
      ¬Fin15AnchoredAtom2507 chi ∧
      ¬Fin15AnchoredAtom2512 chi ∧
      ¬Fin15AnchoredAtom2517 chi ∧
      ¬Fin15AnchoredAtom2535 chi ∧
      ¬Fin15AnchoredAtom2540 chi ∧
      ¬Fin15AnchoredAtom2545 chi ∧
      ¬Fin15AnchoredAtom2581 chi ∧
      ¬Fin15AnchoredAtom2619 chi ∧
      ¬Fin15AnchoredAtom2624 chi ∧
      ¬Fin15AnchoredAtom2629 chi ∧
      ¬Fin15AnchoredAtom2665 chi ∧
      ¬Fin15AnchoredAtom2721 chi ∧
      ¬Fin15AnchoredAtom3208 chi ∧
      ¬Fin15AnchoredAtom3209 chi ∧
      ¬Fin15AnchoredAtom3214 chi ∧
      ¬Fin15AnchoredAtom3222 chi ∧
      ¬Fin15AnchoredAtom3227 chi ∧
      ¬Fin15AnchoredAtom3232 chi ∧
      ¬Fin15AnchoredAtom3250 chi ∧
      ¬Fin15AnchoredAtom3255 chi ∧
      ¬Fin15AnchoredAtom3260 chi ∧
      ¬Fin15AnchoredAtom3296 chi ∧
      ¬Fin15AnchoredAtom3334 chi ∧
      ¬Fin15AnchoredAtom3339 chi ∧
      ¬Fin15AnchoredAtom3344 chi ∧
      ¬Fin15AnchoredAtom3380 chi ∧
      ¬Fin15AnchoredAtom3436 chi ∧
      ¬Fin15AnchoredAtom4369 chi ∧
      ¬Fin15AnchoredAtom4374 chi ∧
      ¬Fin15AnchoredAtom4379 chi ∧
      ¬Fin15AnchoredAtom4415 chi ∧
      ¬Fin15AnchoredAtom4471 chi ∧
      ¬Fin15AnchoredAtom4597 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 5, 6, 8, 9, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17267
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1942 Fin15AnchoredAtom1944 Fin15AnchoredAtom1945
    Fin15AnchoredAtom1950 Fin15AnchoredAtom1952 Fin15AnchoredAtom1953 Fin15AnchoredAtom1958
    Fin15AnchoredAtom1966 Fin15AnchoredAtom1971 Fin15AnchoredAtom1976 Fin15AnchoredAtom1988
    Fin15AnchoredAtom1989 Fin15AnchoredAtom1994 Fin15AnchoredAtom2002 Fin15AnchoredAtom2007
    Fin15AnchoredAtom2012 Fin15AnchoredAtom2030 Fin15AnchoredAtom2035 Fin15AnchoredAtom2040
    Fin15AnchoredAtom2076 Fin15AnchoredAtom2493 Fin15AnchoredAtom2494 Fin15AnchoredAtom2499
    Fin15AnchoredAtom2507 Fin15AnchoredAtom2512 Fin15AnchoredAtom2517 Fin15AnchoredAtom2535
    Fin15AnchoredAtom2540 Fin15AnchoredAtom2545 Fin15AnchoredAtom2581 Fin15AnchoredAtom2619
    Fin15AnchoredAtom2624 Fin15AnchoredAtom2629 Fin15AnchoredAtom2665 Fin15AnchoredAtom2721
    Fin15AnchoredAtom3208 Fin15AnchoredAtom3209 Fin15AnchoredAtom3214 Fin15AnchoredAtom3222
    Fin15AnchoredAtom3227 Fin15AnchoredAtom3232 Fin15AnchoredAtom3250 Fin15AnchoredAtom3255
    Fin15AnchoredAtom3260 Fin15AnchoredAtom3296 Fin15AnchoredAtom3334 Fin15AnchoredAtom3339
    Fin15AnchoredAtom3344 Fin15AnchoredAtom3380 Fin15AnchoredAtom3436 Fin15AnchoredAtom4369
    Fin15AnchoredAtom4374 Fin15AnchoredAtom4379 Fin15AnchoredAtom4415 Fin15AnchoredAtom4471
    Fin15AnchoredAtom4597 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30975 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1942 chi ∧
      ¬Fin15AnchoredAtom1944 chi ∧
      ¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom1952 chi ∧
      ¬Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom1967 chi ∧
      ¬Fin15AnchoredAtom1969 chi ∧
      ¬Fin15AnchoredAtom1978 chi ∧
      ¬Fin15AnchoredAtom1988 chi ∧
      ¬Fin15AnchoredAtom1990 chi ∧
      ¬Fin15AnchoredAtom1992 chi ∧
      ¬Fin15AnchoredAtom2003 chi ∧
      ¬Fin15AnchoredAtom2005 chi ∧
      ¬Fin15AnchoredAtom2014 chi ∧
      ¬Fin15AnchoredAtom2031 chi ∧
      ¬Fin15AnchoredAtom2033 chi ∧
      ¬Fin15AnchoredAtom2042 chi ∧
      ¬Fin15AnchoredAtom2078 chi ∧
      ¬Fin15AnchoredAtom2493 chi ∧
      ¬Fin15AnchoredAtom2495 chi ∧
      ¬Fin15AnchoredAtom2497 chi ∧
      ¬Fin15AnchoredAtom2508 chi ∧
      ¬Fin15AnchoredAtom2510 chi ∧
      ¬Fin15AnchoredAtom2519 chi ∧
      ¬Fin15AnchoredAtom2536 chi ∧
      ¬Fin15AnchoredAtom2538 chi ∧
      ¬Fin15AnchoredAtom2547 chi ∧
      ¬Fin15AnchoredAtom2583 chi ∧
      ¬Fin15AnchoredAtom2620 chi ∧
      ¬Fin15AnchoredAtom2622 chi ∧
      ¬Fin15AnchoredAtom2631 chi ∧
      ¬Fin15AnchoredAtom2667 chi ∧
      ¬Fin15AnchoredAtom2723 chi ∧
      ¬Fin15AnchoredAtom3208 chi ∧
      ¬Fin15AnchoredAtom3210 chi ∧
      ¬Fin15AnchoredAtom3212 chi ∧
      ¬Fin15AnchoredAtom3223 chi ∧
      ¬Fin15AnchoredAtom3225 chi ∧
      ¬Fin15AnchoredAtom3234 chi ∧
      ¬Fin15AnchoredAtom3251 chi ∧
      ¬Fin15AnchoredAtom3253 chi ∧
      ¬Fin15AnchoredAtom3262 chi ∧
      ¬Fin15AnchoredAtom3298 chi ∧
      ¬Fin15AnchoredAtom3335 chi ∧
      ¬Fin15AnchoredAtom3337 chi ∧
      ¬Fin15AnchoredAtom3346 chi ∧
      ¬Fin15AnchoredAtom3382 chi ∧
      ¬Fin15AnchoredAtom3438 chi ∧
      ¬Fin15AnchoredAtom4370 chi ∧
      ¬Fin15AnchoredAtom4372 chi ∧
      ¬Fin15AnchoredAtom4381 chi ∧
      ¬Fin15AnchoredAtom4417 chi ∧
      ¬Fin15AnchoredAtom4473 chi ∧
      ¬Fin15AnchoredAtom4599 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 5, 6, 8, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05491
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1942 Fin15AnchoredAtom1944 Fin15AnchoredAtom1946
    Fin15AnchoredAtom1948 Fin15AnchoredAtom1952 Fin15AnchoredAtom1954 Fin15AnchoredAtom1956
    Fin15AnchoredAtom1967 Fin15AnchoredAtom1969 Fin15AnchoredAtom1978 Fin15AnchoredAtom1988
    Fin15AnchoredAtom1990 Fin15AnchoredAtom1992 Fin15AnchoredAtom2003 Fin15AnchoredAtom2005
    Fin15AnchoredAtom2014 Fin15AnchoredAtom2031 Fin15AnchoredAtom2033 Fin15AnchoredAtom2042
    Fin15AnchoredAtom2078 Fin15AnchoredAtom2493 Fin15AnchoredAtom2495 Fin15AnchoredAtom2497
    Fin15AnchoredAtom2508 Fin15AnchoredAtom2510 Fin15AnchoredAtom2519 Fin15AnchoredAtom2536
    Fin15AnchoredAtom2538 Fin15AnchoredAtom2547 Fin15AnchoredAtom2583 Fin15AnchoredAtom2620
    Fin15AnchoredAtom2622 Fin15AnchoredAtom2631 Fin15AnchoredAtom2667 Fin15AnchoredAtom2723
    Fin15AnchoredAtom3208 Fin15AnchoredAtom3210 Fin15AnchoredAtom3212 Fin15AnchoredAtom3223
    Fin15AnchoredAtom3225 Fin15AnchoredAtom3234 Fin15AnchoredAtom3251 Fin15AnchoredAtom3253
    Fin15AnchoredAtom3262 Fin15AnchoredAtom3298 Fin15AnchoredAtom3335 Fin15AnchoredAtom3337
    Fin15AnchoredAtom3346 Fin15AnchoredAtom3382 Fin15AnchoredAtom3438 Fin15AnchoredAtom4370
    Fin15AnchoredAtom4372 Fin15AnchoredAtom4381 Fin15AnchoredAtom4417 Fin15AnchoredAtom4473
    Fin15AnchoredAtom4599 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
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
