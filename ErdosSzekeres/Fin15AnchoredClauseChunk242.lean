module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 242. -/

theorem fin15Anchored_clause30976 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1942 chi ∧
      ¬Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom1978 chi ∧
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
      ¬Fin15AnchoredAtom2494 chi ∧
      ¬Fin15AnchoredAtom2495 chi ∧
      ¬Fin15AnchoredAtom2497 chi ∧
      ¬Fin15AnchoredAtom2513 chi ∧
      ¬Fin15AnchoredAtom2515 chi ∧
      ¬Fin15AnchoredAtom2519 chi ∧
      ¬Fin15AnchoredAtom2541 chi ∧
      ¬Fin15AnchoredAtom2543 chi ∧
      ¬Fin15AnchoredAtom2547 chi ∧
      ¬Fin15AnchoredAtom2593 chi ∧
      ¬Fin15AnchoredAtom2625 chi ∧
      ¬Fin15AnchoredAtom2627 chi ∧
      ¬Fin15AnchoredAtom2631 chi ∧
      ¬Fin15AnchoredAtom2677 chi ∧
      ¬Fin15AnchoredAtom2733 chi ∧
      ¬Fin15AnchoredAtom3209 chi ∧
      ¬Fin15AnchoredAtom3210 chi ∧
      ¬Fin15AnchoredAtom3212 chi ∧
      ¬Fin15AnchoredAtom3228 chi ∧
      ¬Fin15AnchoredAtom3230 chi ∧
      ¬Fin15AnchoredAtom3234 chi ∧
      ¬Fin15AnchoredAtom3256 chi ∧
      ¬Fin15AnchoredAtom3258 chi ∧
      ¬Fin15AnchoredAtom3262 chi ∧
      ¬Fin15AnchoredAtom3308 chi ∧
      ¬Fin15AnchoredAtom3340 chi ∧
      ¬Fin15AnchoredAtom3342 chi ∧
      ¬Fin15AnchoredAtom3346 chi ∧
      ¬Fin15AnchoredAtom3392 chi ∧
      ¬Fin15AnchoredAtom3448 chi ∧
      ¬Fin15AnchoredAtom4375 chi ∧
      ¬Fin15AnchoredAtom4377 chi ∧
      ¬Fin15AnchoredAtom4381 chi ∧
      ¬Fin15AnchoredAtom4427 chi ∧
      ¬Fin15AnchoredAtom4483 chi ∧
      ¬Fin15AnchoredAtom4609 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 5, 6, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05747
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1942 Fin15AnchoredAtom1945 Fin15AnchoredAtom1946
    Fin15AnchoredAtom1948 Fin15AnchoredAtom1953 Fin15AnchoredAtom1954 Fin15AnchoredAtom1956
    Fin15AnchoredAtom1972 Fin15AnchoredAtom1974 Fin15AnchoredAtom1978 Fin15AnchoredAtom1989
    Fin15AnchoredAtom1990 Fin15AnchoredAtom1992 Fin15AnchoredAtom2008 Fin15AnchoredAtom2010
    Fin15AnchoredAtom2014 Fin15AnchoredAtom2036 Fin15AnchoredAtom2038 Fin15AnchoredAtom2042
    Fin15AnchoredAtom2088 Fin15AnchoredAtom2494 Fin15AnchoredAtom2495 Fin15AnchoredAtom2497
    Fin15AnchoredAtom2513 Fin15AnchoredAtom2515 Fin15AnchoredAtom2519 Fin15AnchoredAtom2541
    Fin15AnchoredAtom2543 Fin15AnchoredAtom2547 Fin15AnchoredAtom2593 Fin15AnchoredAtom2625
    Fin15AnchoredAtom2627 Fin15AnchoredAtom2631 Fin15AnchoredAtom2677 Fin15AnchoredAtom2733
    Fin15AnchoredAtom3209 Fin15AnchoredAtom3210 Fin15AnchoredAtom3212 Fin15AnchoredAtom3228
    Fin15AnchoredAtom3230 Fin15AnchoredAtom3234 Fin15AnchoredAtom3256 Fin15AnchoredAtom3258
    Fin15AnchoredAtom3262 Fin15AnchoredAtom3308 Fin15AnchoredAtom3340 Fin15AnchoredAtom3342
    Fin15AnchoredAtom3346 Fin15AnchoredAtom3392 Fin15AnchoredAtom3448 Fin15AnchoredAtom4375
    Fin15AnchoredAtom4377 Fin15AnchoredAtom4381 Fin15AnchoredAtom4427 Fin15AnchoredAtom4483
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

theorem fin15Anchored_clause30977 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1942 chi ∧
      ¬Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom1979 chi ∧
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
      ¬Fin15AnchoredAtom2494 chi ∧
      ¬Fin15AnchoredAtom2495 chi ∧
      ¬Fin15AnchoredAtom2498 chi ∧
      ¬Fin15AnchoredAtom2513 chi ∧
      ¬Fin15AnchoredAtom2516 chi ∧
      ¬Fin15AnchoredAtom2520 chi ∧
      ¬Fin15AnchoredAtom2541 chi ∧
      ¬Fin15AnchoredAtom2544 chi ∧
      ¬Fin15AnchoredAtom2548 chi ∧
      ¬Fin15AnchoredAtom2594 chi ∧
      ¬Fin15AnchoredAtom2625 chi ∧
      ¬Fin15AnchoredAtom2628 chi ∧
      ¬Fin15AnchoredAtom2632 chi ∧
      ¬Fin15AnchoredAtom2678 chi ∧
      ¬Fin15AnchoredAtom2734 chi ∧
      ¬Fin15AnchoredAtom3209 chi ∧
      ¬Fin15AnchoredAtom3210 chi ∧
      ¬Fin15AnchoredAtom3213 chi ∧
      ¬Fin15AnchoredAtom3228 chi ∧
      ¬Fin15AnchoredAtom3231 chi ∧
      ¬Fin15AnchoredAtom3235 chi ∧
      ¬Fin15AnchoredAtom3256 chi ∧
      ¬Fin15AnchoredAtom3259 chi ∧
      ¬Fin15AnchoredAtom3263 chi ∧
      ¬Fin15AnchoredAtom3309 chi ∧
      ¬Fin15AnchoredAtom3340 chi ∧
      ¬Fin15AnchoredAtom3343 chi ∧
      ¬Fin15AnchoredAtom3347 chi ∧
      ¬Fin15AnchoredAtom3393 chi ∧
      ¬Fin15AnchoredAtom3449 chi ∧
      ¬Fin15AnchoredAtom4375 chi ∧
      ¬Fin15AnchoredAtom4378 chi ∧
      ¬Fin15AnchoredAtom4382 chi ∧
      ¬Fin15AnchoredAtom4428 chi ∧
      ¬Fin15AnchoredAtom4484 chi ∧
      ¬Fin15AnchoredAtom4610 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 5, 6, 9, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09843
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1942 Fin15AnchoredAtom1945 Fin15AnchoredAtom1946
    Fin15AnchoredAtom1949 Fin15AnchoredAtom1953 Fin15AnchoredAtom1954 Fin15AnchoredAtom1957
    Fin15AnchoredAtom1972 Fin15AnchoredAtom1975 Fin15AnchoredAtom1979 Fin15AnchoredAtom1989
    Fin15AnchoredAtom1990 Fin15AnchoredAtom1993 Fin15AnchoredAtom2008 Fin15AnchoredAtom2011
    Fin15AnchoredAtom2015 Fin15AnchoredAtom2036 Fin15AnchoredAtom2039 Fin15AnchoredAtom2043
    Fin15AnchoredAtom2089 Fin15AnchoredAtom2494 Fin15AnchoredAtom2495 Fin15AnchoredAtom2498
    Fin15AnchoredAtom2513 Fin15AnchoredAtom2516 Fin15AnchoredAtom2520 Fin15AnchoredAtom2541
    Fin15AnchoredAtom2544 Fin15AnchoredAtom2548 Fin15AnchoredAtom2594 Fin15AnchoredAtom2625
    Fin15AnchoredAtom2628 Fin15AnchoredAtom2632 Fin15AnchoredAtom2678 Fin15AnchoredAtom2734
    Fin15AnchoredAtom3209 Fin15AnchoredAtom3210 Fin15AnchoredAtom3213 Fin15AnchoredAtom3228
    Fin15AnchoredAtom3231 Fin15AnchoredAtom3235 Fin15AnchoredAtom3256 Fin15AnchoredAtom3259
    Fin15AnchoredAtom3263 Fin15AnchoredAtom3309 Fin15AnchoredAtom3340 Fin15AnchoredAtom3343
    Fin15AnchoredAtom3347 Fin15AnchoredAtom3393 Fin15AnchoredAtom3449 Fin15AnchoredAtom4375
    Fin15AnchoredAtom4378 Fin15AnchoredAtom4382 Fin15AnchoredAtom4428 Fin15AnchoredAtom4484
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

theorem fin15Anchored_clause30978 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1942 chi ∧
      ¬Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom1976 chi ∧
      ¬Fin15AnchoredAtom1980 chi ∧
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
      ¬Fin15AnchoredAtom2494 chi ∧
      ¬Fin15AnchoredAtom2495 chi ∧
      ¬Fin15AnchoredAtom2499 chi ∧
      ¬Fin15AnchoredAtom2513 chi ∧
      ¬Fin15AnchoredAtom2517 chi ∧
      ¬Fin15AnchoredAtom2521 chi ∧
      ¬Fin15AnchoredAtom2541 chi ∧
      ¬Fin15AnchoredAtom2545 chi ∧
      ¬Fin15AnchoredAtom2549 chi ∧
      ¬Fin15AnchoredAtom2595 chi ∧
      ¬Fin15AnchoredAtom2625 chi ∧
      ¬Fin15AnchoredAtom2629 chi ∧
      ¬Fin15AnchoredAtom2633 chi ∧
      ¬Fin15AnchoredAtom2679 chi ∧
      ¬Fin15AnchoredAtom2735 chi ∧
      ¬Fin15AnchoredAtom3209 chi ∧
      ¬Fin15AnchoredAtom3210 chi ∧
      ¬Fin15AnchoredAtom3214 chi ∧
      ¬Fin15AnchoredAtom3228 chi ∧
      ¬Fin15AnchoredAtom3232 chi ∧
      ¬Fin15AnchoredAtom3236 chi ∧
      ¬Fin15AnchoredAtom3256 chi ∧
      ¬Fin15AnchoredAtom3260 chi ∧
      ¬Fin15AnchoredAtom3264 chi ∧
      ¬Fin15AnchoredAtom3310 chi ∧
      ¬Fin15AnchoredAtom3340 chi ∧
      ¬Fin15AnchoredAtom3344 chi ∧
      ¬Fin15AnchoredAtom3348 chi ∧
      ¬Fin15AnchoredAtom3394 chi ∧
      ¬Fin15AnchoredAtom3450 chi ∧
      ¬Fin15AnchoredAtom4375 chi ∧
      ¬Fin15AnchoredAtom4379 chi ∧
      ¬Fin15AnchoredAtom4383 chi ∧
      ¬Fin15AnchoredAtom4429 chi ∧
      ¬Fin15AnchoredAtom4485 chi ∧
      ¬Fin15AnchoredAtom4611 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 5, 6, 9, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask18035
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1942 Fin15AnchoredAtom1945 Fin15AnchoredAtom1946
    Fin15AnchoredAtom1950 Fin15AnchoredAtom1953 Fin15AnchoredAtom1954 Fin15AnchoredAtom1958
    Fin15AnchoredAtom1972 Fin15AnchoredAtom1976 Fin15AnchoredAtom1980 Fin15AnchoredAtom1989
    Fin15AnchoredAtom1990 Fin15AnchoredAtom1994 Fin15AnchoredAtom2008 Fin15AnchoredAtom2012
    Fin15AnchoredAtom2016 Fin15AnchoredAtom2036 Fin15AnchoredAtom2040 Fin15AnchoredAtom2044
    Fin15AnchoredAtom2090 Fin15AnchoredAtom2494 Fin15AnchoredAtom2495 Fin15AnchoredAtom2499
    Fin15AnchoredAtom2513 Fin15AnchoredAtom2517 Fin15AnchoredAtom2521 Fin15AnchoredAtom2541
    Fin15AnchoredAtom2545 Fin15AnchoredAtom2549 Fin15AnchoredAtom2595 Fin15AnchoredAtom2625
    Fin15AnchoredAtom2629 Fin15AnchoredAtom2633 Fin15AnchoredAtom2679 Fin15AnchoredAtom2735
    Fin15AnchoredAtom3209 Fin15AnchoredAtom3210 Fin15AnchoredAtom3214 Fin15AnchoredAtom3228
    Fin15AnchoredAtom3232 Fin15AnchoredAtom3236 Fin15AnchoredAtom3256 Fin15AnchoredAtom3260
    Fin15AnchoredAtom3264 Fin15AnchoredAtom3310 Fin15AnchoredAtom3340 Fin15AnchoredAtom3344
    Fin15AnchoredAtom3348 Fin15AnchoredAtom3394 Fin15AnchoredAtom3450 Fin15AnchoredAtom4375
    Fin15AnchoredAtom4379 Fin15AnchoredAtom4383 Fin15AnchoredAtom4429 Fin15AnchoredAtom4485
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

theorem fin15Anchored_clause30979 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1942 chi ∧
      ¬Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom1984 chi ∧
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
      ¬Fin15AnchoredAtom2494 chi ∧
      ¬Fin15AnchoredAtom2497 chi ∧
      ¬Fin15AnchoredAtom2498 chi ∧
      ¬Fin15AnchoredAtom2515 chi ∧
      ¬Fin15AnchoredAtom2516 chi ∧
      ¬Fin15AnchoredAtom2525 chi ∧
      ¬Fin15AnchoredAtom2543 chi ∧
      ¬Fin15AnchoredAtom2544 chi ∧
      ¬Fin15AnchoredAtom2553 chi ∧
      ¬Fin15AnchoredAtom2599 chi ∧
      ¬Fin15AnchoredAtom2627 chi ∧
      ¬Fin15AnchoredAtom2628 chi ∧
      ¬Fin15AnchoredAtom2637 chi ∧
      ¬Fin15AnchoredAtom2683 chi ∧
      ¬Fin15AnchoredAtom2739 chi ∧
      ¬Fin15AnchoredAtom3209 chi ∧
      ¬Fin15AnchoredAtom3212 chi ∧
      ¬Fin15AnchoredAtom3213 chi ∧
      ¬Fin15AnchoredAtom3230 chi ∧
      ¬Fin15AnchoredAtom3231 chi ∧
      ¬Fin15AnchoredAtom3240 chi ∧
      ¬Fin15AnchoredAtom3258 chi ∧
      ¬Fin15AnchoredAtom3259 chi ∧
      ¬Fin15AnchoredAtom3268 chi ∧
      ¬Fin15AnchoredAtom3314 chi ∧
      ¬Fin15AnchoredAtom3342 chi ∧
      ¬Fin15AnchoredAtom3343 chi ∧
      ¬Fin15AnchoredAtom3352 chi ∧
      ¬Fin15AnchoredAtom3398 chi ∧
      ¬Fin15AnchoredAtom3454 chi ∧
      ¬Fin15AnchoredAtom4377 chi ∧
      ¬Fin15AnchoredAtom4378 chi ∧
      ¬Fin15AnchoredAtom4387 chi ∧
      ¬Fin15AnchoredAtom4433 chi ∧
      ¬Fin15AnchoredAtom4489 chi ∧
      ¬Fin15AnchoredAtom4615 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 5, 6, 9, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask12915
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1942 Fin15AnchoredAtom1945 Fin15AnchoredAtom1948
    Fin15AnchoredAtom1949 Fin15AnchoredAtom1953 Fin15AnchoredAtom1956 Fin15AnchoredAtom1957
    Fin15AnchoredAtom1974 Fin15AnchoredAtom1975 Fin15AnchoredAtom1984 Fin15AnchoredAtom1989
    Fin15AnchoredAtom1992 Fin15AnchoredAtom1993 Fin15AnchoredAtom2010 Fin15AnchoredAtom2011
    Fin15AnchoredAtom2020 Fin15AnchoredAtom2038 Fin15AnchoredAtom2039 Fin15AnchoredAtom2048
    Fin15AnchoredAtom2094 Fin15AnchoredAtom2494 Fin15AnchoredAtom2497 Fin15AnchoredAtom2498
    Fin15AnchoredAtom2515 Fin15AnchoredAtom2516 Fin15AnchoredAtom2525 Fin15AnchoredAtom2543
    Fin15AnchoredAtom2544 Fin15AnchoredAtom2553 Fin15AnchoredAtom2599 Fin15AnchoredAtom2627
    Fin15AnchoredAtom2628 Fin15AnchoredAtom2637 Fin15AnchoredAtom2683 Fin15AnchoredAtom2739
    Fin15AnchoredAtom3209 Fin15AnchoredAtom3212 Fin15AnchoredAtom3213 Fin15AnchoredAtom3230
    Fin15AnchoredAtom3231 Fin15AnchoredAtom3240 Fin15AnchoredAtom3258 Fin15AnchoredAtom3259
    Fin15AnchoredAtom3268 Fin15AnchoredAtom3314 Fin15AnchoredAtom3342 Fin15AnchoredAtom3343
    Fin15AnchoredAtom3352 Fin15AnchoredAtom3398 Fin15AnchoredAtom3454 Fin15AnchoredAtom4377
    Fin15AnchoredAtom4378 Fin15AnchoredAtom4387 Fin15AnchoredAtom4433 Fin15AnchoredAtom4489
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

theorem fin15Anchored_clause30980 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1942 chi ∧
      ¬Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom1976 chi ∧
      ¬Fin15AnchoredAtom1985 chi ∧
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
      ¬Fin15AnchoredAtom2494 chi ∧
      ¬Fin15AnchoredAtom2497 chi ∧
      ¬Fin15AnchoredAtom2499 chi ∧
      ¬Fin15AnchoredAtom2515 chi ∧
      ¬Fin15AnchoredAtom2517 chi ∧
      ¬Fin15AnchoredAtom2526 chi ∧
      ¬Fin15AnchoredAtom2543 chi ∧
      ¬Fin15AnchoredAtom2545 chi ∧
      ¬Fin15AnchoredAtom2554 chi ∧
      ¬Fin15AnchoredAtom2600 chi ∧
      ¬Fin15AnchoredAtom2627 chi ∧
      ¬Fin15AnchoredAtom2629 chi ∧
      ¬Fin15AnchoredAtom2638 chi ∧
      ¬Fin15AnchoredAtom2684 chi ∧
      ¬Fin15AnchoredAtom2740 chi ∧
      ¬Fin15AnchoredAtom3209 chi ∧
      ¬Fin15AnchoredAtom3212 chi ∧
      ¬Fin15AnchoredAtom3214 chi ∧
      ¬Fin15AnchoredAtom3230 chi ∧
      ¬Fin15AnchoredAtom3232 chi ∧
      ¬Fin15AnchoredAtom3241 chi ∧
      ¬Fin15AnchoredAtom3258 chi ∧
      ¬Fin15AnchoredAtom3260 chi ∧
      ¬Fin15AnchoredAtom3269 chi ∧
      ¬Fin15AnchoredAtom3315 chi ∧
      ¬Fin15AnchoredAtom3342 chi ∧
      ¬Fin15AnchoredAtom3344 chi ∧
      ¬Fin15AnchoredAtom3353 chi ∧
      ¬Fin15AnchoredAtom3399 chi ∧
      ¬Fin15AnchoredAtom3455 chi ∧
      ¬Fin15AnchoredAtom4377 chi ∧
      ¬Fin15AnchoredAtom4379 chi ∧
      ¬Fin15AnchoredAtom4388 chi ∧
      ¬Fin15AnchoredAtom4434 chi ∧
      ¬Fin15AnchoredAtom4490 chi ∧
      ¬Fin15AnchoredAtom4616 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 5, 6, 9, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21107
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1942 Fin15AnchoredAtom1945 Fin15AnchoredAtom1948
    Fin15AnchoredAtom1950 Fin15AnchoredAtom1953 Fin15AnchoredAtom1956 Fin15AnchoredAtom1958
    Fin15AnchoredAtom1974 Fin15AnchoredAtom1976 Fin15AnchoredAtom1985 Fin15AnchoredAtom1989
    Fin15AnchoredAtom1992 Fin15AnchoredAtom1994 Fin15AnchoredAtom2010 Fin15AnchoredAtom2012
    Fin15AnchoredAtom2021 Fin15AnchoredAtom2038 Fin15AnchoredAtom2040 Fin15AnchoredAtom2049
    Fin15AnchoredAtom2095 Fin15AnchoredAtom2494 Fin15AnchoredAtom2497 Fin15AnchoredAtom2499
    Fin15AnchoredAtom2515 Fin15AnchoredAtom2517 Fin15AnchoredAtom2526 Fin15AnchoredAtom2543
    Fin15AnchoredAtom2545 Fin15AnchoredAtom2554 Fin15AnchoredAtom2600 Fin15AnchoredAtom2627
    Fin15AnchoredAtom2629 Fin15AnchoredAtom2638 Fin15AnchoredAtom2684 Fin15AnchoredAtom2740
    Fin15AnchoredAtom3209 Fin15AnchoredAtom3212 Fin15AnchoredAtom3214 Fin15AnchoredAtom3230
    Fin15AnchoredAtom3232 Fin15AnchoredAtom3241 Fin15AnchoredAtom3258 Fin15AnchoredAtom3260
    Fin15AnchoredAtom3269 Fin15AnchoredAtom3315 Fin15AnchoredAtom3342 Fin15AnchoredAtom3344
    Fin15AnchoredAtom3353 Fin15AnchoredAtom3399 Fin15AnchoredAtom3455 Fin15AnchoredAtom4377
    Fin15AnchoredAtom4379 Fin15AnchoredAtom4388 Fin15AnchoredAtom4434 Fin15AnchoredAtom4490
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

theorem fin15Anchored_clause30981 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1942 chi ∧
      ¬Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom1976 chi ∧
      ¬Fin15AnchoredAtom1986 chi ∧
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
      ¬Fin15AnchoredAtom2494 chi ∧
      ¬Fin15AnchoredAtom2498 chi ∧
      ¬Fin15AnchoredAtom2499 chi ∧
      ¬Fin15AnchoredAtom2516 chi ∧
      ¬Fin15AnchoredAtom2517 chi ∧
      ¬Fin15AnchoredAtom2527 chi ∧
      ¬Fin15AnchoredAtom2544 chi ∧
      ¬Fin15AnchoredAtom2545 chi ∧
      ¬Fin15AnchoredAtom2555 chi ∧
      ¬Fin15AnchoredAtom2601 chi ∧
      ¬Fin15AnchoredAtom2628 chi ∧
      ¬Fin15AnchoredAtom2629 chi ∧
      ¬Fin15AnchoredAtom2639 chi ∧
      ¬Fin15AnchoredAtom2685 chi ∧
      ¬Fin15AnchoredAtom2741 chi ∧
      ¬Fin15AnchoredAtom3209 chi ∧
      ¬Fin15AnchoredAtom3213 chi ∧
      ¬Fin15AnchoredAtom3214 chi ∧
      ¬Fin15AnchoredAtom3231 chi ∧
      ¬Fin15AnchoredAtom3232 chi ∧
      ¬Fin15AnchoredAtom3242 chi ∧
      ¬Fin15AnchoredAtom3259 chi ∧
      ¬Fin15AnchoredAtom3260 chi ∧
      ¬Fin15AnchoredAtom3270 chi ∧
      ¬Fin15AnchoredAtom3316 chi ∧
      ¬Fin15AnchoredAtom3343 chi ∧
      ¬Fin15AnchoredAtom3344 chi ∧
      ¬Fin15AnchoredAtom3354 chi ∧
      ¬Fin15AnchoredAtom3400 chi ∧
      ¬Fin15AnchoredAtom3456 chi ∧
      ¬Fin15AnchoredAtom4378 chi ∧
      ¬Fin15AnchoredAtom4379 chi ∧
      ¬Fin15AnchoredAtom4389 chi ∧
      ¬Fin15AnchoredAtom4435 chi ∧
      ¬Fin15AnchoredAtom4491 chi ∧
      ¬Fin15AnchoredAtom4617 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 5, 6, 9, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25203
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1942 Fin15AnchoredAtom1945 Fin15AnchoredAtom1949
    Fin15AnchoredAtom1950 Fin15AnchoredAtom1953 Fin15AnchoredAtom1957 Fin15AnchoredAtom1958
    Fin15AnchoredAtom1975 Fin15AnchoredAtom1976 Fin15AnchoredAtom1986 Fin15AnchoredAtom1989
    Fin15AnchoredAtom1993 Fin15AnchoredAtom1994 Fin15AnchoredAtom2011 Fin15AnchoredAtom2012
    Fin15AnchoredAtom2022 Fin15AnchoredAtom2039 Fin15AnchoredAtom2040 Fin15AnchoredAtom2050
    Fin15AnchoredAtom2096 Fin15AnchoredAtom2494 Fin15AnchoredAtom2498 Fin15AnchoredAtom2499
    Fin15AnchoredAtom2516 Fin15AnchoredAtom2517 Fin15AnchoredAtom2527 Fin15AnchoredAtom2544
    Fin15AnchoredAtom2545 Fin15AnchoredAtom2555 Fin15AnchoredAtom2601 Fin15AnchoredAtom2628
    Fin15AnchoredAtom2629 Fin15AnchoredAtom2639 Fin15AnchoredAtom2685 Fin15AnchoredAtom2741
    Fin15AnchoredAtom3209 Fin15AnchoredAtom3213 Fin15AnchoredAtom3214 Fin15AnchoredAtom3231
    Fin15AnchoredAtom3232 Fin15AnchoredAtom3242 Fin15AnchoredAtom3259 Fin15AnchoredAtom3260
    Fin15AnchoredAtom3270 Fin15AnchoredAtom3316 Fin15AnchoredAtom3343 Fin15AnchoredAtom3344
    Fin15AnchoredAtom3354 Fin15AnchoredAtom3400 Fin15AnchoredAtom3456 Fin15AnchoredAtom4378
    Fin15AnchoredAtom4379 Fin15AnchoredAtom4389 Fin15AnchoredAtom4435 Fin15AnchoredAtom4491
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

theorem fin15Anchored_clause30982 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1942 chi ∧
      ¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom1978 chi ∧
      ¬Fin15AnchoredAtom1979 chi ∧
      ¬Fin15AnchoredAtom1984 chi ∧
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
      ¬Fin15AnchoredAtom2495 chi ∧
      ¬Fin15AnchoredAtom2497 chi ∧
      ¬Fin15AnchoredAtom2498 chi ∧
      ¬Fin15AnchoredAtom2519 chi ∧
      ¬Fin15AnchoredAtom2520 chi ∧
      ¬Fin15AnchoredAtom2525 chi ∧
      ¬Fin15AnchoredAtom2547 chi ∧
      ¬Fin15AnchoredAtom2548 chi ∧
      ¬Fin15AnchoredAtom2553 chi ∧
      ¬Fin15AnchoredAtom2605 chi ∧
      ¬Fin15AnchoredAtom2631 chi ∧
      ¬Fin15AnchoredAtom2632 chi ∧
      ¬Fin15AnchoredAtom2637 chi ∧
      ¬Fin15AnchoredAtom2689 chi ∧
      ¬Fin15AnchoredAtom2745 chi ∧
      ¬Fin15AnchoredAtom3210 chi ∧
      ¬Fin15AnchoredAtom3212 chi ∧
      ¬Fin15AnchoredAtom3213 chi ∧
      ¬Fin15AnchoredAtom3234 chi ∧
      ¬Fin15AnchoredAtom3235 chi ∧
      ¬Fin15AnchoredAtom3240 chi ∧
      ¬Fin15AnchoredAtom3262 chi ∧
      ¬Fin15AnchoredAtom3263 chi ∧
      ¬Fin15AnchoredAtom3268 chi ∧
      ¬Fin15AnchoredAtom3320 chi ∧
      ¬Fin15AnchoredAtom3346 chi ∧
      ¬Fin15AnchoredAtom3347 chi ∧
      ¬Fin15AnchoredAtom3352 chi ∧
      ¬Fin15AnchoredAtom3404 chi ∧
      ¬Fin15AnchoredAtom3460 chi ∧
      ¬Fin15AnchoredAtom4381 chi ∧
      ¬Fin15AnchoredAtom4382 chi ∧
      ¬Fin15AnchoredAtom4387 chi ∧
      ¬Fin15AnchoredAtom4439 chi ∧
      ¬Fin15AnchoredAtom4495 chi ∧
      ¬Fin15AnchoredAtom4621 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 5, 6, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13427
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1942 Fin15AnchoredAtom1946 Fin15AnchoredAtom1948
    Fin15AnchoredAtom1949 Fin15AnchoredAtom1954 Fin15AnchoredAtom1956 Fin15AnchoredAtom1957
    Fin15AnchoredAtom1978 Fin15AnchoredAtom1979 Fin15AnchoredAtom1984 Fin15AnchoredAtom1990
    Fin15AnchoredAtom1992 Fin15AnchoredAtom1993 Fin15AnchoredAtom2014 Fin15AnchoredAtom2015
    Fin15AnchoredAtom2020 Fin15AnchoredAtom2042 Fin15AnchoredAtom2043 Fin15AnchoredAtom2048
    Fin15AnchoredAtom2100 Fin15AnchoredAtom2495 Fin15AnchoredAtom2497 Fin15AnchoredAtom2498
    Fin15AnchoredAtom2519 Fin15AnchoredAtom2520 Fin15AnchoredAtom2525 Fin15AnchoredAtom2547
    Fin15AnchoredAtom2548 Fin15AnchoredAtom2553 Fin15AnchoredAtom2605 Fin15AnchoredAtom2631
    Fin15AnchoredAtom2632 Fin15AnchoredAtom2637 Fin15AnchoredAtom2689 Fin15AnchoredAtom2745
    Fin15AnchoredAtom3210 Fin15AnchoredAtom3212 Fin15AnchoredAtom3213 Fin15AnchoredAtom3234
    Fin15AnchoredAtom3235 Fin15AnchoredAtom3240 Fin15AnchoredAtom3262 Fin15AnchoredAtom3263
    Fin15AnchoredAtom3268 Fin15AnchoredAtom3320 Fin15AnchoredAtom3346 Fin15AnchoredAtom3347
    Fin15AnchoredAtom3352 Fin15AnchoredAtom3404 Fin15AnchoredAtom3460 Fin15AnchoredAtom4381
    Fin15AnchoredAtom4382 Fin15AnchoredAtom4387 Fin15AnchoredAtom4439 Fin15AnchoredAtom4495
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

theorem fin15Anchored_clause30983 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1942 chi ∧
      ¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom1978 chi ∧
      ¬Fin15AnchoredAtom1980 chi ∧
      ¬Fin15AnchoredAtom1985 chi ∧
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
      ¬Fin15AnchoredAtom2495 chi ∧
      ¬Fin15AnchoredAtom2497 chi ∧
      ¬Fin15AnchoredAtom2499 chi ∧
      ¬Fin15AnchoredAtom2519 chi ∧
      ¬Fin15AnchoredAtom2521 chi ∧
      ¬Fin15AnchoredAtom2526 chi ∧
      ¬Fin15AnchoredAtom2547 chi ∧
      ¬Fin15AnchoredAtom2549 chi ∧
      ¬Fin15AnchoredAtom2554 chi ∧
      ¬Fin15AnchoredAtom2606 chi ∧
      ¬Fin15AnchoredAtom2631 chi ∧
      ¬Fin15AnchoredAtom2633 chi ∧
      ¬Fin15AnchoredAtom2638 chi ∧
      ¬Fin15AnchoredAtom2690 chi ∧
      ¬Fin15AnchoredAtom2746 chi ∧
      ¬Fin15AnchoredAtom3210 chi ∧
      ¬Fin15AnchoredAtom3212 chi ∧
      ¬Fin15AnchoredAtom3214 chi ∧
      ¬Fin15AnchoredAtom3234 chi ∧
      ¬Fin15AnchoredAtom3236 chi ∧
      ¬Fin15AnchoredAtom3241 chi ∧
      ¬Fin15AnchoredAtom3262 chi ∧
      ¬Fin15AnchoredAtom3264 chi ∧
      ¬Fin15AnchoredAtom3269 chi ∧
      ¬Fin15AnchoredAtom3321 chi ∧
      ¬Fin15AnchoredAtom3346 chi ∧
      ¬Fin15AnchoredAtom3348 chi ∧
      ¬Fin15AnchoredAtom3353 chi ∧
      ¬Fin15AnchoredAtom3405 chi ∧
      ¬Fin15AnchoredAtom3461 chi ∧
      ¬Fin15AnchoredAtom4381 chi ∧
      ¬Fin15AnchoredAtom4383 chi ∧
      ¬Fin15AnchoredAtom4388 chi ∧
      ¬Fin15AnchoredAtom4440 chi ∧
      ¬Fin15AnchoredAtom4496 chi ∧
      ¬Fin15AnchoredAtom4622 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 5, 6, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21619
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1942 Fin15AnchoredAtom1946 Fin15AnchoredAtom1948
    Fin15AnchoredAtom1950 Fin15AnchoredAtom1954 Fin15AnchoredAtom1956 Fin15AnchoredAtom1958
    Fin15AnchoredAtom1978 Fin15AnchoredAtom1980 Fin15AnchoredAtom1985 Fin15AnchoredAtom1990
    Fin15AnchoredAtom1992 Fin15AnchoredAtom1994 Fin15AnchoredAtom2014 Fin15AnchoredAtom2016
    Fin15AnchoredAtom2021 Fin15AnchoredAtom2042 Fin15AnchoredAtom2044 Fin15AnchoredAtom2049
    Fin15AnchoredAtom2101 Fin15AnchoredAtom2495 Fin15AnchoredAtom2497 Fin15AnchoredAtom2499
    Fin15AnchoredAtom2519 Fin15AnchoredAtom2521 Fin15AnchoredAtom2526 Fin15AnchoredAtom2547
    Fin15AnchoredAtom2549 Fin15AnchoredAtom2554 Fin15AnchoredAtom2606 Fin15AnchoredAtom2631
    Fin15AnchoredAtom2633 Fin15AnchoredAtom2638 Fin15AnchoredAtom2690 Fin15AnchoredAtom2746
    Fin15AnchoredAtom3210 Fin15AnchoredAtom3212 Fin15AnchoredAtom3214 Fin15AnchoredAtom3234
    Fin15AnchoredAtom3236 Fin15AnchoredAtom3241 Fin15AnchoredAtom3262 Fin15AnchoredAtom3264
    Fin15AnchoredAtom3269 Fin15AnchoredAtom3321 Fin15AnchoredAtom3346 Fin15AnchoredAtom3348
    Fin15AnchoredAtom3353 Fin15AnchoredAtom3405 Fin15AnchoredAtom3461 Fin15AnchoredAtom4381
    Fin15AnchoredAtom4383 Fin15AnchoredAtom4388 Fin15AnchoredAtom4440 Fin15AnchoredAtom4496
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

theorem fin15Anchored_clause30984 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1942 chi ∧
      ¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom1979 chi ∧
      ¬Fin15AnchoredAtom1980 chi ∧
      ¬Fin15AnchoredAtom1986 chi ∧
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
      ¬Fin15AnchoredAtom2495 chi ∧
      ¬Fin15AnchoredAtom2498 chi ∧
      ¬Fin15AnchoredAtom2499 chi ∧
      ¬Fin15AnchoredAtom2520 chi ∧
      ¬Fin15AnchoredAtom2521 chi ∧
      ¬Fin15AnchoredAtom2527 chi ∧
      ¬Fin15AnchoredAtom2548 chi ∧
      ¬Fin15AnchoredAtom2549 chi ∧
      ¬Fin15AnchoredAtom2555 chi ∧
      ¬Fin15AnchoredAtom2607 chi ∧
      ¬Fin15AnchoredAtom2632 chi ∧
      ¬Fin15AnchoredAtom2633 chi ∧
      ¬Fin15AnchoredAtom2639 chi ∧
      ¬Fin15AnchoredAtom2691 chi ∧
      ¬Fin15AnchoredAtom2747 chi ∧
      ¬Fin15AnchoredAtom3210 chi ∧
      ¬Fin15AnchoredAtom3213 chi ∧
      ¬Fin15AnchoredAtom3214 chi ∧
      ¬Fin15AnchoredAtom3235 chi ∧
      ¬Fin15AnchoredAtom3236 chi ∧
      ¬Fin15AnchoredAtom3242 chi ∧
      ¬Fin15AnchoredAtom3263 chi ∧
      ¬Fin15AnchoredAtom3264 chi ∧
      ¬Fin15AnchoredAtom3270 chi ∧
      ¬Fin15AnchoredAtom3322 chi ∧
      ¬Fin15AnchoredAtom3347 chi ∧
      ¬Fin15AnchoredAtom3348 chi ∧
      ¬Fin15AnchoredAtom3354 chi ∧
      ¬Fin15AnchoredAtom3406 chi ∧
      ¬Fin15AnchoredAtom3462 chi ∧
      ¬Fin15AnchoredAtom4382 chi ∧
      ¬Fin15AnchoredAtom4383 chi ∧
      ¬Fin15AnchoredAtom4389 chi ∧
      ¬Fin15AnchoredAtom4441 chi ∧
      ¬Fin15AnchoredAtom4497 chi ∧
      ¬Fin15AnchoredAtom4623 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 5, 6, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25715
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1942 Fin15AnchoredAtom1946 Fin15AnchoredAtom1949
    Fin15AnchoredAtom1950 Fin15AnchoredAtom1954 Fin15AnchoredAtom1957 Fin15AnchoredAtom1958
    Fin15AnchoredAtom1979 Fin15AnchoredAtom1980 Fin15AnchoredAtom1986 Fin15AnchoredAtom1990
    Fin15AnchoredAtom1993 Fin15AnchoredAtom1994 Fin15AnchoredAtom2015 Fin15AnchoredAtom2016
    Fin15AnchoredAtom2022 Fin15AnchoredAtom2043 Fin15AnchoredAtom2044 Fin15AnchoredAtom2050
    Fin15AnchoredAtom2102 Fin15AnchoredAtom2495 Fin15AnchoredAtom2498 Fin15AnchoredAtom2499
    Fin15AnchoredAtom2520 Fin15AnchoredAtom2521 Fin15AnchoredAtom2527 Fin15AnchoredAtom2548
    Fin15AnchoredAtom2549 Fin15AnchoredAtom2555 Fin15AnchoredAtom2607 Fin15AnchoredAtom2632
    Fin15AnchoredAtom2633 Fin15AnchoredAtom2639 Fin15AnchoredAtom2691 Fin15AnchoredAtom2747
    Fin15AnchoredAtom3210 Fin15AnchoredAtom3213 Fin15AnchoredAtom3214 Fin15AnchoredAtom3235
    Fin15AnchoredAtom3236 Fin15AnchoredAtom3242 Fin15AnchoredAtom3263 Fin15AnchoredAtom3264
    Fin15AnchoredAtom3270 Fin15AnchoredAtom3322 Fin15AnchoredAtom3347 Fin15AnchoredAtom3348
    Fin15AnchoredAtom3354 Fin15AnchoredAtom3406 Fin15AnchoredAtom3462 Fin15AnchoredAtom4382
    Fin15AnchoredAtom4383 Fin15AnchoredAtom4389 Fin15AnchoredAtom4441 Fin15AnchoredAtom4497
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

theorem fin15Anchored_clause30985 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1942 chi ∧
      ¬Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom1984 chi ∧
      ¬Fin15AnchoredAtom1985 chi ∧
      ¬Fin15AnchoredAtom1986 chi ∧
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
      ¬Fin15AnchoredAtom2497 chi ∧
      ¬Fin15AnchoredAtom2498 chi ∧
      ¬Fin15AnchoredAtom2499 chi ∧
      ¬Fin15AnchoredAtom2525 chi ∧
      ¬Fin15AnchoredAtom2526 chi ∧
      ¬Fin15AnchoredAtom2527 chi ∧
      ¬Fin15AnchoredAtom2553 chi ∧
      ¬Fin15AnchoredAtom2554 chi ∧
      ¬Fin15AnchoredAtom2555 chi ∧
      ¬Fin15AnchoredAtom2611 chi ∧
      ¬Fin15AnchoredAtom2637 chi ∧
      ¬Fin15AnchoredAtom2638 chi ∧
      ¬Fin15AnchoredAtom2639 chi ∧
      ¬Fin15AnchoredAtom2695 chi ∧
      ¬Fin15AnchoredAtom2751 chi ∧
      ¬Fin15AnchoredAtom3212 chi ∧
      ¬Fin15AnchoredAtom3213 chi ∧
      ¬Fin15AnchoredAtom3214 chi ∧
      ¬Fin15AnchoredAtom3240 chi ∧
      ¬Fin15AnchoredAtom3241 chi ∧
      ¬Fin15AnchoredAtom3242 chi ∧
      ¬Fin15AnchoredAtom3268 chi ∧
      ¬Fin15AnchoredAtom3269 chi ∧
      ¬Fin15AnchoredAtom3270 chi ∧
      ¬Fin15AnchoredAtom3326 chi ∧
      ¬Fin15AnchoredAtom3352 chi ∧
      ¬Fin15AnchoredAtom3353 chi ∧
      ¬Fin15AnchoredAtom3354 chi ∧
      ¬Fin15AnchoredAtom3410 chi ∧
      ¬Fin15AnchoredAtom3466 chi ∧
      ¬Fin15AnchoredAtom4387 chi ∧
      ¬Fin15AnchoredAtom4388 chi ∧
      ¬Fin15AnchoredAtom4389 chi ∧
      ¬Fin15AnchoredAtom4445 chi ∧
      ¬Fin15AnchoredAtom4501 chi ∧
      ¬Fin15AnchoredAtom4627 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 5, 6, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask28787
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1942 Fin15AnchoredAtom1948 Fin15AnchoredAtom1949
    Fin15AnchoredAtom1950 Fin15AnchoredAtom1956 Fin15AnchoredAtom1957 Fin15AnchoredAtom1958
    Fin15AnchoredAtom1984 Fin15AnchoredAtom1985 Fin15AnchoredAtom1986 Fin15AnchoredAtom1992
    Fin15AnchoredAtom1993 Fin15AnchoredAtom1994 Fin15AnchoredAtom2020 Fin15AnchoredAtom2021
    Fin15AnchoredAtom2022 Fin15AnchoredAtom2048 Fin15AnchoredAtom2049 Fin15AnchoredAtom2050
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2497 Fin15AnchoredAtom2498 Fin15AnchoredAtom2499
    Fin15AnchoredAtom2525 Fin15AnchoredAtom2526 Fin15AnchoredAtom2527 Fin15AnchoredAtom2553
    Fin15AnchoredAtom2554 Fin15AnchoredAtom2555 Fin15AnchoredAtom2611 Fin15AnchoredAtom2637
    Fin15AnchoredAtom2638 Fin15AnchoredAtom2639 Fin15AnchoredAtom2695 Fin15AnchoredAtom2751
    Fin15AnchoredAtom3212 Fin15AnchoredAtom3213 Fin15AnchoredAtom3214 Fin15AnchoredAtom3240
    Fin15AnchoredAtom3241 Fin15AnchoredAtom3242 Fin15AnchoredAtom3268 Fin15AnchoredAtom3269
    Fin15AnchoredAtom3270 Fin15AnchoredAtom3326 Fin15AnchoredAtom3352 Fin15AnchoredAtom3353
    Fin15AnchoredAtom3354 Fin15AnchoredAtom3410 Fin15AnchoredAtom3466 Fin15AnchoredAtom4387
    Fin15AnchoredAtom4388 Fin15AnchoredAtom4389 Fin15AnchoredAtom4445 Fin15AnchoredAtom4501
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

theorem fin15Anchored_clause30986 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom1944 chi ∧
      ¬Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1959 chi ∧
      ¬Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom1966 chi ∧
      ¬Fin15AnchoredAtom1967 chi ∧
      ¬Fin15AnchoredAtom1972 chi ∧
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
      ¬Fin15AnchoredAtom2500 chi ∧
      ¬Fin15AnchoredAtom2501 chi ∧
      ¬Fin15AnchoredAtom2502 chi ∧
      ¬Fin15AnchoredAtom2507 chi ∧
      ¬Fin15AnchoredAtom2508 chi ∧
      ¬Fin15AnchoredAtom2513 chi ∧
      ¬Fin15AnchoredAtom2556 chi ∧
      ¬Fin15AnchoredAtom2557 chi ∧
      ¬Fin15AnchoredAtom2562 chi ∧
      ¬Fin15AnchoredAtom2577 chi ∧
      ¬Fin15AnchoredAtom2640 chi ∧
      ¬Fin15AnchoredAtom2641 chi ∧
      ¬Fin15AnchoredAtom2646 chi ∧
      ¬Fin15AnchoredAtom2661 chi ∧
      ¬Fin15AnchoredAtom2752 chi ∧
      ¬Fin15AnchoredAtom3215 chi ∧
      ¬Fin15AnchoredAtom3216 chi ∧
      ¬Fin15AnchoredAtom3217 chi ∧
      ¬Fin15AnchoredAtom3222 chi ∧
      ¬Fin15AnchoredAtom3223 chi ∧
      ¬Fin15AnchoredAtom3228 chi ∧
      ¬Fin15AnchoredAtom3271 chi ∧
      ¬Fin15AnchoredAtom3272 chi ∧
      ¬Fin15AnchoredAtom3277 chi ∧
      ¬Fin15AnchoredAtom3292 chi ∧
      ¬Fin15AnchoredAtom3355 chi ∧
      ¬Fin15AnchoredAtom3356 chi ∧
      ¬Fin15AnchoredAtom3361 chi ∧
      ¬Fin15AnchoredAtom3376 chi ∧
      ¬Fin15AnchoredAtom3467 chi ∧
      ¬Fin15AnchoredAtom4390 chi ∧
      ¬Fin15AnchoredAtom4391 chi ∧
      ¬Fin15AnchoredAtom4396 chi ∧
      ¬Fin15AnchoredAtom4411 chi ∧
      ¬Fin15AnchoredAtom4502 chi ∧
      ¬Fin15AnchoredAtom4628 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 5, 7, 8, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask01971
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1943 Fin15AnchoredAtom1944 Fin15AnchoredAtom1945
    Fin15AnchoredAtom1946 Fin15AnchoredAtom1959 Fin15AnchoredAtom1960 Fin15AnchoredAtom1961
    Fin15AnchoredAtom1966 Fin15AnchoredAtom1967 Fin15AnchoredAtom1972 Fin15AnchoredAtom1995
    Fin15AnchoredAtom1996 Fin15AnchoredAtom1997 Fin15AnchoredAtom2002 Fin15AnchoredAtom2003
    Fin15AnchoredAtom2008 Fin15AnchoredAtom2051 Fin15AnchoredAtom2052 Fin15AnchoredAtom2057
    Fin15AnchoredAtom2072 Fin15AnchoredAtom2500 Fin15AnchoredAtom2501 Fin15AnchoredAtom2502
    Fin15AnchoredAtom2507 Fin15AnchoredAtom2508 Fin15AnchoredAtom2513 Fin15AnchoredAtom2556
    Fin15AnchoredAtom2557 Fin15AnchoredAtom2562 Fin15AnchoredAtom2577 Fin15AnchoredAtom2640
    Fin15AnchoredAtom2641 Fin15AnchoredAtom2646 Fin15AnchoredAtom2661 Fin15AnchoredAtom2752
    Fin15AnchoredAtom3215 Fin15AnchoredAtom3216 Fin15AnchoredAtom3217 Fin15AnchoredAtom3222
    Fin15AnchoredAtom3223 Fin15AnchoredAtom3228 Fin15AnchoredAtom3271 Fin15AnchoredAtom3272
    Fin15AnchoredAtom3277 Fin15AnchoredAtom3292 Fin15AnchoredAtom3355 Fin15AnchoredAtom3356
    Fin15AnchoredAtom3361 Fin15AnchoredAtom3376 Fin15AnchoredAtom3467 Fin15AnchoredAtom4390
    Fin15AnchoredAtom4391 Fin15AnchoredAtom4396 Fin15AnchoredAtom4411 Fin15AnchoredAtom4502
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

theorem fin15Anchored_clause30987 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom1944 chi ∧
      ¬Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom1959 chi ∧
      ¬Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom1966 chi ∧
      ¬Fin15AnchoredAtom1971 chi ∧
      ¬Fin15AnchoredAtom1976 chi ∧
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
      ¬Fin15AnchoredAtom2500 chi ∧
      ¬Fin15AnchoredAtom2501 chi ∧
      ¬Fin15AnchoredAtom2506 chi ∧
      ¬Fin15AnchoredAtom2507 chi ∧
      ¬Fin15AnchoredAtom2512 chi ∧
      ¬Fin15AnchoredAtom2517 chi ∧
      ¬Fin15AnchoredAtom2556 chi ∧
      ¬Fin15AnchoredAtom2561 chi ∧
      ¬Fin15AnchoredAtom2566 chi ∧
      ¬Fin15AnchoredAtom2581 chi ∧
      ¬Fin15AnchoredAtom2640 chi ∧
      ¬Fin15AnchoredAtom2645 chi ∧
      ¬Fin15AnchoredAtom2650 chi ∧
      ¬Fin15AnchoredAtom2665 chi ∧
      ¬Fin15AnchoredAtom2756 chi ∧
      ¬Fin15AnchoredAtom3215 chi ∧
      ¬Fin15AnchoredAtom3216 chi ∧
      ¬Fin15AnchoredAtom3221 chi ∧
      ¬Fin15AnchoredAtom3222 chi ∧
      ¬Fin15AnchoredAtom3227 chi ∧
      ¬Fin15AnchoredAtom3232 chi ∧
      ¬Fin15AnchoredAtom3271 chi ∧
      ¬Fin15AnchoredAtom3276 chi ∧
      ¬Fin15AnchoredAtom3281 chi ∧
      ¬Fin15AnchoredAtom3296 chi ∧
      ¬Fin15AnchoredAtom3355 chi ∧
      ¬Fin15AnchoredAtom3360 chi ∧
      ¬Fin15AnchoredAtom3365 chi ∧
      ¬Fin15AnchoredAtom3380 chi ∧
      ¬Fin15AnchoredAtom3471 chi ∧
      ¬Fin15AnchoredAtom4390 chi ∧
      ¬Fin15AnchoredAtom4395 chi ∧
      ¬Fin15AnchoredAtom4400 chi ∧
      ¬Fin15AnchoredAtom4415 chi ∧
      ¬Fin15AnchoredAtom4506 chi ∧
      ¬Fin15AnchoredAtom4632 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 5, 7, 8, 9, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17331
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1943 Fin15AnchoredAtom1944 Fin15AnchoredAtom1945
    Fin15AnchoredAtom1950 Fin15AnchoredAtom1959 Fin15AnchoredAtom1960 Fin15AnchoredAtom1965
    Fin15AnchoredAtom1966 Fin15AnchoredAtom1971 Fin15AnchoredAtom1976 Fin15AnchoredAtom1995
    Fin15AnchoredAtom1996 Fin15AnchoredAtom2001 Fin15AnchoredAtom2002 Fin15AnchoredAtom2007
    Fin15AnchoredAtom2012 Fin15AnchoredAtom2051 Fin15AnchoredAtom2056 Fin15AnchoredAtom2061
    Fin15AnchoredAtom2076 Fin15AnchoredAtom2500 Fin15AnchoredAtom2501 Fin15AnchoredAtom2506
    Fin15AnchoredAtom2507 Fin15AnchoredAtom2512 Fin15AnchoredAtom2517 Fin15AnchoredAtom2556
    Fin15AnchoredAtom2561 Fin15AnchoredAtom2566 Fin15AnchoredAtom2581 Fin15AnchoredAtom2640
    Fin15AnchoredAtom2645 Fin15AnchoredAtom2650 Fin15AnchoredAtom2665 Fin15AnchoredAtom2756
    Fin15AnchoredAtom3215 Fin15AnchoredAtom3216 Fin15AnchoredAtom3221 Fin15AnchoredAtom3222
    Fin15AnchoredAtom3227 Fin15AnchoredAtom3232 Fin15AnchoredAtom3271 Fin15AnchoredAtom3276
    Fin15AnchoredAtom3281 Fin15AnchoredAtom3296 Fin15AnchoredAtom3355 Fin15AnchoredAtom3360
    Fin15AnchoredAtom3365 Fin15AnchoredAtom3380 Fin15AnchoredAtom3471 Fin15AnchoredAtom4390
    Fin15AnchoredAtom4395 Fin15AnchoredAtom4400 Fin15AnchoredAtom4415 Fin15AnchoredAtom4506
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

theorem fin15Anchored_clause30988 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom1944 chi ∧
      ¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom1959 chi ∧
      ¬Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom1967 chi ∧
      ¬Fin15AnchoredAtom1969 chi ∧
      ¬Fin15AnchoredAtom1978 chi ∧
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
      ¬Fin15AnchoredAtom2500 chi ∧
      ¬Fin15AnchoredAtom2502 chi ∧
      ¬Fin15AnchoredAtom2504 chi ∧
      ¬Fin15AnchoredAtom2508 chi ∧
      ¬Fin15AnchoredAtom2510 chi ∧
      ¬Fin15AnchoredAtom2519 chi ∧
      ¬Fin15AnchoredAtom2557 chi ∧
      ¬Fin15AnchoredAtom2559 chi ∧
      ¬Fin15AnchoredAtom2568 chi ∧
      ¬Fin15AnchoredAtom2583 chi ∧
      ¬Fin15AnchoredAtom2641 chi ∧
      ¬Fin15AnchoredAtom2643 chi ∧
      ¬Fin15AnchoredAtom2652 chi ∧
      ¬Fin15AnchoredAtom2667 chi ∧
      ¬Fin15AnchoredAtom2758 chi ∧
      ¬Fin15AnchoredAtom3215 chi ∧
      ¬Fin15AnchoredAtom3217 chi ∧
      ¬Fin15AnchoredAtom3219 chi ∧
      ¬Fin15AnchoredAtom3223 chi ∧
      ¬Fin15AnchoredAtom3225 chi ∧
      ¬Fin15AnchoredAtom3234 chi ∧
      ¬Fin15AnchoredAtom3272 chi ∧
      ¬Fin15AnchoredAtom3274 chi ∧
      ¬Fin15AnchoredAtom3283 chi ∧
      ¬Fin15AnchoredAtom3298 chi ∧
      ¬Fin15AnchoredAtom3356 chi ∧
      ¬Fin15AnchoredAtom3358 chi ∧
      ¬Fin15AnchoredAtom3367 chi ∧
      ¬Fin15AnchoredAtom3382 chi ∧
      ¬Fin15AnchoredAtom3473 chi ∧
      ¬Fin15AnchoredAtom4391 chi ∧
      ¬Fin15AnchoredAtom4393 chi ∧
      ¬Fin15AnchoredAtom4402 chi ∧
      ¬Fin15AnchoredAtom4417 chi ∧
      ¬Fin15AnchoredAtom4508 chi ∧
      ¬Fin15AnchoredAtom4634 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 5, 7, 8, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05555
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1943 Fin15AnchoredAtom1944 Fin15AnchoredAtom1946
    Fin15AnchoredAtom1948 Fin15AnchoredAtom1959 Fin15AnchoredAtom1961 Fin15AnchoredAtom1963
    Fin15AnchoredAtom1967 Fin15AnchoredAtom1969 Fin15AnchoredAtom1978 Fin15AnchoredAtom1995
    Fin15AnchoredAtom1997 Fin15AnchoredAtom1999 Fin15AnchoredAtom2003 Fin15AnchoredAtom2005
    Fin15AnchoredAtom2014 Fin15AnchoredAtom2052 Fin15AnchoredAtom2054 Fin15AnchoredAtom2063
    Fin15AnchoredAtom2078 Fin15AnchoredAtom2500 Fin15AnchoredAtom2502 Fin15AnchoredAtom2504
    Fin15AnchoredAtom2508 Fin15AnchoredAtom2510 Fin15AnchoredAtom2519 Fin15AnchoredAtom2557
    Fin15AnchoredAtom2559 Fin15AnchoredAtom2568 Fin15AnchoredAtom2583 Fin15AnchoredAtom2641
    Fin15AnchoredAtom2643 Fin15AnchoredAtom2652 Fin15AnchoredAtom2667 Fin15AnchoredAtom2758
    Fin15AnchoredAtom3215 Fin15AnchoredAtom3217 Fin15AnchoredAtom3219 Fin15AnchoredAtom3223
    Fin15AnchoredAtom3225 Fin15AnchoredAtom3234 Fin15AnchoredAtom3272 Fin15AnchoredAtom3274
    Fin15AnchoredAtom3283 Fin15AnchoredAtom3298 Fin15AnchoredAtom3356 Fin15AnchoredAtom3358
    Fin15AnchoredAtom3367 Fin15AnchoredAtom3382 Fin15AnchoredAtom3473 Fin15AnchoredAtom4391
    Fin15AnchoredAtom4393 Fin15AnchoredAtom4402 Fin15AnchoredAtom4417 Fin15AnchoredAtom4508
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

theorem fin15Anchored_clause30989 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom1944 chi ∧
      ¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom1959 chi ∧
      ¬Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom1967 chi ∧
      ¬Fin15AnchoredAtom1970 chi ∧
      ¬Fin15AnchoredAtom1979 chi ∧
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
      ¬Fin15AnchoredAtom2500 chi ∧
      ¬Fin15AnchoredAtom2502 chi ∧
      ¬Fin15AnchoredAtom2505 chi ∧
      ¬Fin15AnchoredAtom2508 chi ∧
      ¬Fin15AnchoredAtom2511 chi ∧
      ¬Fin15AnchoredAtom2520 chi ∧
      ¬Fin15AnchoredAtom2557 chi ∧
      ¬Fin15AnchoredAtom2560 chi ∧
      ¬Fin15AnchoredAtom2569 chi ∧
      ¬Fin15AnchoredAtom2584 chi ∧
      ¬Fin15AnchoredAtom2641 chi ∧
      ¬Fin15AnchoredAtom2644 chi ∧
      ¬Fin15AnchoredAtom2653 chi ∧
      ¬Fin15AnchoredAtom2668 chi ∧
      ¬Fin15AnchoredAtom2759 chi ∧
      ¬Fin15AnchoredAtom3215 chi ∧
      ¬Fin15AnchoredAtom3217 chi ∧
      ¬Fin15AnchoredAtom3220 chi ∧
      ¬Fin15AnchoredAtom3223 chi ∧
      ¬Fin15AnchoredAtom3226 chi ∧
      ¬Fin15AnchoredAtom3235 chi ∧
      ¬Fin15AnchoredAtom3272 chi ∧
      ¬Fin15AnchoredAtom3275 chi ∧
      ¬Fin15AnchoredAtom3284 chi ∧
      ¬Fin15AnchoredAtom3299 chi ∧
      ¬Fin15AnchoredAtom3356 chi ∧
      ¬Fin15AnchoredAtom3359 chi ∧
      ¬Fin15AnchoredAtom3368 chi ∧
      ¬Fin15AnchoredAtom3383 chi ∧
      ¬Fin15AnchoredAtom3474 chi ∧
      ¬Fin15AnchoredAtom4391 chi ∧
      ¬Fin15AnchoredAtom4394 chi ∧
      ¬Fin15AnchoredAtom4403 chi ∧
      ¬Fin15AnchoredAtom4418 chi ∧
      ¬Fin15AnchoredAtom4509 chi ∧
      ¬Fin15AnchoredAtom4635 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 5, 7, 8, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09651
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1943 Fin15AnchoredAtom1944 Fin15AnchoredAtom1946
    Fin15AnchoredAtom1949 Fin15AnchoredAtom1959 Fin15AnchoredAtom1961 Fin15AnchoredAtom1964
    Fin15AnchoredAtom1967 Fin15AnchoredAtom1970 Fin15AnchoredAtom1979 Fin15AnchoredAtom1995
    Fin15AnchoredAtom1997 Fin15AnchoredAtom2000 Fin15AnchoredAtom2003 Fin15AnchoredAtom2006
    Fin15AnchoredAtom2015 Fin15AnchoredAtom2052 Fin15AnchoredAtom2055 Fin15AnchoredAtom2064
    Fin15AnchoredAtom2079 Fin15AnchoredAtom2500 Fin15AnchoredAtom2502 Fin15AnchoredAtom2505
    Fin15AnchoredAtom2508 Fin15AnchoredAtom2511 Fin15AnchoredAtom2520 Fin15AnchoredAtom2557
    Fin15AnchoredAtom2560 Fin15AnchoredAtom2569 Fin15AnchoredAtom2584 Fin15AnchoredAtom2641
    Fin15AnchoredAtom2644 Fin15AnchoredAtom2653 Fin15AnchoredAtom2668 Fin15AnchoredAtom2759
    Fin15AnchoredAtom3215 Fin15AnchoredAtom3217 Fin15AnchoredAtom3220 Fin15AnchoredAtom3223
    Fin15AnchoredAtom3226 Fin15AnchoredAtom3235 Fin15AnchoredAtom3272 Fin15AnchoredAtom3275
    Fin15AnchoredAtom3284 Fin15AnchoredAtom3299 Fin15AnchoredAtom3356 Fin15AnchoredAtom3359
    Fin15AnchoredAtom3368 Fin15AnchoredAtom3383 Fin15AnchoredAtom3474 Fin15AnchoredAtom4391
    Fin15AnchoredAtom4394 Fin15AnchoredAtom4403 Fin15AnchoredAtom4418 Fin15AnchoredAtom4509
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

theorem fin15Anchored_clause30990 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom1944 chi ∧
      ¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom1959 chi ∧
      ¬Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom1967 chi ∧
      ¬Fin15AnchoredAtom1971 chi ∧
      ¬Fin15AnchoredAtom1980 chi ∧
      ¬Fin15AnchoredAtom1995 chi ∧
      ¬Fin15AnchoredAtom1997 chi ∧
      ¬Fin15AnchoredAtom2001 chi ∧
      ¬Fin15AnchoredAtom2003 chi ∧
      ¬Fin15AnchoredAtom2007 chi ∧
      ¬Fin15AnchoredAtom2016 chi ∧
      ¬Fin15AnchoredAtom2052 chi ∧
      ¬Fin15AnchoredAtom2056 chi ∧
      ¬Fin15AnchoredAtom2065 chi ∧
      ¬Fin15AnchoredAtom2080 chi ∧
      ¬Fin15AnchoredAtom2500 chi ∧
      ¬Fin15AnchoredAtom2502 chi ∧
      ¬Fin15AnchoredAtom2506 chi ∧
      ¬Fin15AnchoredAtom2508 chi ∧
      ¬Fin15AnchoredAtom2512 chi ∧
      ¬Fin15AnchoredAtom2521 chi ∧
      ¬Fin15AnchoredAtom2557 chi ∧
      ¬Fin15AnchoredAtom2561 chi ∧
      ¬Fin15AnchoredAtom2570 chi ∧
      ¬Fin15AnchoredAtom2585 chi ∧
      ¬Fin15AnchoredAtom2641 chi ∧
      ¬Fin15AnchoredAtom2645 chi ∧
      ¬Fin15AnchoredAtom2654 chi ∧
      ¬Fin15AnchoredAtom2669 chi ∧
      ¬Fin15AnchoredAtom2760 chi ∧
      ¬Fin15AnchoredAtom3215 chi ∧
      ¬Fin15AnchoredAtom3217 chi ∧
      ¬Fin15AnchoredAtom3221 chi ∧
      ¬Fin15AnchoredAtom3223 chi ∧
      ¬Fin15AnchoredAtom3227 chi ∧
      ¬Fin15AnchoredAtom3236 chi ∧
      ¬Fin15AnchoredAtom3272 chi ∧
      ¬Fin15AnchoredAtom3276 chi ∧
      ¬Fin15AnchoredAtom3285 chi ∧
      ¬Fin15AnchoredAtom3300 chi ∧
      ¬Fin15AnchoredAtom3356 chi ∧
      ¬Fin15AnchoredAtom3360 chi ∧
      ¬Fin15AnchoredAtom3369 chi ∧
      ¬Fin15AnchoredAtom3384 chi ∧
      ¬Fin15AnchoredAtom3475 chi ∧
      ¬Fin15AnchoredAtom4391 chi ∧
      ¬Fin15AnchoredAtom4395 chi ∧
      ¬Fin15AnchoredAtom4404 chi ∧
      ¬Fin15AnchoredAtom4419 chi ∧
      ¬Fin15AnchoredAtom4510 chi ∧
      ¬Fin15AnchoredAtom4636 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 5, 7, 8, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17843
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1943 Fin15AnchoredAtom1944 Fin15AnchoredAtom1946
    Fin15AnchoredAtom1950 Fin15AnchoredAtom1959 Fin15AnchoredAtom1961 Fin15AnchoredAtom1965
    Fin15AnchoredAtom1967 Fin15AnchoredAtom1971 Fin15AnchoredAtom1980 Fin15AnchoredAtom1995
    Fin15AnchoredAtom1997 Fin15AnchoredAtom2001 Fin15AnchoredAtom2003 Fin15AnchoredAtom2007
    Fin15AnchoredAtom2016 Fin15AnchoredAtom2052 Fin15AnchoredAtom2056 Fin15AnchoredAtom2065
    Fin15AnchoredAtom2080 Fin15AnchoredAtom2500 Fin15AnchoredAtom2502 Fin15AnchoredAtom2506
    Fin15AnchoredAtom2508 Fin15AnchoredAtom2512 Fin15AnchoredAtom2521 Fin15AnchoredAtom2557
    Fin15AnchoredAtom2561 Fin15AnchoredAtom2570 Fin15AnchoredAtom2585 Fin15AnchoredAtom2641
    Fin15AnchoredAtom2645 Fin15AnchoredAtom2654 Fin15AnchoredAtom2669 Fin15AnchoredAtom2760
    Fin15AnchoredAtom3215 Fin15AnchoredAtom3217 Fin15AnchoredAtom3221 Fin15AnchoredAtom3223
    Fin15AnchoredAtom3227 Fin15AnchoredAtom3236 Fin15AnchoredAtom3272 Fin15AnchoredAtom3276
    Fin15AnchoredAtom3285 Fin15AnchoredAtom3300 Fin15AnchoredAtom3356 Fin15AnchoredAtom3360
    Fin15AnchoredAtom3369 Fin15AnchoredAtom3384 Fin15AnchoredAtom3475 Fin15AnchoredAtom4391
    Fin15AnchoredAtom4395 Fin15AnchoredAtom4404 Fin15AnchoredAtom4419 Fin15AnchoredAtom4510
    Fin15AnchoredAtom4636 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30991 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom1944 chi ∧
      ¬Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom1959 chi ∧
      ¬Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom1970 chi ∧
      ¬Fin15AnchoredAtom1971 chi ∧
      ¬Fin15AnchoredAtom1986 chi ∧
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
      ¬Fin15AnchoredAtom2500 chi ∧
      ¬Fin15AnchoredAtom2505 chi ∧
      ¬Fin15AnchoredAtom2506 chi ∧
      ¬Fin15AnchoredAtom2511 chi ∧
      ¬Fin15AnchoredAtom2512 chi ∧
      ¬Fin15AnchoredAtom2527 chi ∧
      ¬Fin15AnchoredAtom2560 chi ∧
      ¬Fin15AnchoredAtom2561 chi ∧
      ¬Fin15AnchoredAtom2576 chi ∧
      ¬Fin15AnchoredAtom2591 chi ∧
      ¬Fin15AnchoredAtom2644 chi ∧
      ¬Fin15AnchoredAtom2645 chi ∧
      ¬Fin15AnchoredAtom2660 chi ∧
      ¬Fin15AnchoredAtom2675 chi ∧
      ¬Fin15AnchoredAtom2766 chi ∧
      ¬Fin15AnchoredAtom3215 chi ∧
      ¬Fin15AnchoredAtom3220 chi ∧
      ¬Fin15AnchoredAtom3221 chi ∧
      ¬Fin15AnchoredAtom3226 chi ∧
      ¬Fin15AnchoredAtom3227 chi ∧
      ¬Fin15AnchoredAtom3242 chi ∧
      ¬Fin15AnchoredAtom3275 chi ∧
      ¬Fin15AnchoredAtom3276 chi ∧
      ¬Fin15AnchoredAtom3291 chi ∧
      ¬Fin15AnchoredAtom3306 chi ∧
      ¬Fin15AnchoredAtom3359 chi ∧
      ¬Fin15AnchoredAtom3360 chi ∧
      ¬Fin15AnchoredAtom3375 chi ∧
      ¬Fin15AnchoredAtom3390 chi ∧
      ¬Fin15AnchoredAtom3481 chi ∧
      ¬Fin15AnchoredAtom4394 chi ∧
      ¬Fin15AnchoredAtom4395 chi ∧
      ¬Fin15AnchoredAtom4410 chi ∧
      ¬Fin15AnchoredAtom4425 chi ∧
      ¬Fin15AnchoredAtom4516 chi ∧
      ¬Fin15AnchoredAtom4642 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 5, 7, 8, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25011
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1943 Fin15AnchoredAtom1944 Fin15AnchoredAtom1949
    Fin15AnchoredAtom1950 Fin15AnchoredAtom1959 Fin15AnchoredAtom1964 Fin15AnchoredAtom1965
    Fin15AnchoredAtom1970 Fin15AnchoredAtom1971 Fin15AnchoredAtom1986 Fin15AnchoredAtom1995
    Fin15AnchoredAtom2000 Fin15AnchoredAtom2001 Fin15AnchoredAtom2006 Fin15AnchoredAtom2007
    Fin15AnchoredAtom2022 Fin15AnchoredAtom2055 Fin15AnchoredAtom2056 Fin15AnchoredAtom2071
    Fin15AnchoredAtom2086 Fin15AnchoredAtom2500 Fin15AnchoredAtom2505 Fin15AnchoredAtom2506
    Fin15AnchoredAtom2511 Fin15AnchoredAtom2512 Fin15AnchoredAtom2527 Fin15AnchoredAtom2560
    Fin15AnchoredAtom2561 Fin15AnchoredAtom2576 Fin15AnchoredAtom2591 Fin15AnchoredAtom2644
    Fin15AnchoredAtom2645 Fin15AnchoredAtom2660 Fin15AnchoredAtom2675 Fin15AnchoredAtom2766
    Fin15AnchoredAtom3215 Fin15AnchoredAtom3220 Fin15AnchoredAtom3221 Fin15AnchoredAtom3226
    Fin15AnchoredAtom3227 Fin15AnchoredAtom3242 Fin15AnchoredAtom3275 Fin15AnchoredAtom3276
    Fin15AnchoredAtom3291 Fin15AnchoredAtom3306 Fin15AnchoredAtom3359 Fin15AnchoredAtom3360
    Fin15AnchoredAtom3375 Fin15AnchoredAtom3390 Fin15AnchoredAtom3481 Fin15AnchoredAtom4394
    Fin15AnchoredAtom4395 Fin15AnchoredAtom4410 Fin15AnchoredAtom4425 Fin15AnchoredAtom4516
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

theorem fin15Anchored_clause30992 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom1978 chi ∧
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
      ¬Fin15AnchoredAtom2501 chi ∧
      ¬Fin15AnchoredAtom2502 chi ∧
      ¬Fin15AnchoredAtom2504 chi ∧
      ¬Fin15AnchoredAtom2513 chi ∧
      ¬Fin15AnchoredAtom2515 chi ∧
      ¬Fin15AnchoredAtom2519 chi ∧
      ¬Fin15AnchoredAtom2562 chi ∧
      ¬Fin15AnchoredAtom2564 chi ∧
      ¬Fin15AnchoredAtom2568 chi ∧
      ¬Fin15AnchoredAtom2593 chi ∧
      ¬Fin15AnchoredAtom2646 chi ∧
      ¬Fin15AnchoredAtom2648 chi ∧
      ¬Fin15AnchoredAtom2652 chi ∧
      ¬Fin15AnchoredAtom2677 chi ∧
      ¬Fin15AnchoredAtom2768 chi ∧
      ¬Fin15AnchoredAtom3216 chi ∧
      ¬Fin15AnchoredAtom3217 chi ∧
      ¬Fin15AnchoredAtom3219 chi ∧
      ¬Fin15AnchoredAtom3228 chi ∧
      ¬Fin15AnchoredAtom3230 chi ∧
      ¬Fin15AnchoredAtom3234 chi ∧
      ¬Fin15AnchoredAtom3277 chi ∧
      ¬Fin15AnchoredAtom3279 chi ∧
      ¬Fin15AnchoredAtom3283 chi ∧
      ¬Fin15AnchoredAtom3308 chi ∧
      ¬Fin15AnchoredAtom3361 chi ∧
      ¬Fin15AnchoredAtom3363 chi ∧
      ¬Fin15AnchoredAtom3367 chi ∧
      ¬Fin15AnchoredAtom3392 chi ∧
      ¬Fin15AnchoredAtom3483 chi ∧
      ¬Fin15AnchoredAtom4396 chi ∧
      ¬Fin15AnchoredAtom4398 chi ∧
      ¬Fin15AnchoredAtom4402 chi ∧
      ¬Fin15AnchoredAtom4427 chi ∧
      ¬Fin15AnchoredAtom4518 chi ∧
      ¬Fin15AnchoredAtom4644 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 5, 7, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05811
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1943 Fin15AnchoredAtom1945 Fin15AnchoredAtom1946
    Fin15AnchoredAtom1948 Fin15AnchoredAtom1960 Fin15AnchoredAtom1961 Fin15AnchoredAtom1963
    Fin15AnchoredAtom1972 Fin15AnchoredAtom1974 Fin15AnchoredAtom1978 Fin15AnchoredAtom1996
    Fin15AnchoredAtom1997 Fin15AnchoredAtom1999 Fin15AnchoredAtom2008 Fin15AnchoredAtom2010
    Fin15AnchoredAtom2014 Fin15AnchoredAtom2057 Fin15AnchoredAtom2059 Fin15AnchoredAtom2063
    Fin15AnchoredAtom2088 Fin15AnchoredAtom2501 Fin15AnchoredAtom2502 Fin15AnchoredAtom2504
    Fin15AnchoredAtom2513 Fin15AnchoredAtom2515 Fin15AnchoredAtom2519 Fin15AnchoredAtom2562
    Fin15AnchoredAtom2564 Fin15AnchoredAtom2568 Fin15AnchoredAtom2593 Fin15AnchoredAtom2646
    Fin15AnchoredAtom2648 Fin15AnchoredAtom2652 Fin15AnchoredAtom2677 Fin15AnchoredAtom2768
    Fin15AnchoredAtom3216 Fin15AnchoredAtom3217 Fin15AnchoredAtom3219 Fin15AnchoredAtom3228
    Fin15AnchoredAtom3230 Fin15AnchoredAtom3234 Fin15AnchoredAtom3277 Fin15AnchoredAtom3279
    Fin15AnchoredAtom3283 Fin15AnchoredAtom3308 Fin15AnchoredAtom3361 Fin15AnchoredAtom3363
    Fin15AnchoredAtom3367 Fin15AnchoredAtom3392 Fin15AnchoredAtom3483 Fin15AnchoredAtom4396
    Fin15AnchoredAtom4398 Fin15AnchoredAtom4402 Fin15AnchoredAtom4427 Fin15AnchoredAtom4518
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

theorem fin15Anchored_clause30993 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom1979 chi ∧
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
      ¬Fin15AnchoredAtom2501 chi ∧
      ¬Fin15AnchoredAtom2502 chi ∧
      ¬Fin15AnchoredAtom2505 chi ∧
      ¬Fin15AnchoredAtom2513 chi ∧
      ¬Fin15AnchoredAtom2516 chi ∧
      ¬Fin15AnchoredAtom2520 chi ∧
      ¬Fin15AnchoredAtom2562 chi ∧
      ¬Fin15AnchoredAtom2565 chi ∧
      ¬Fin15AnchoredAtom2569 chi ∧
      ¬Fin15AnchoredAtom2594 chi ∧
      ¬Fin15AnchoredAtom2646 chi ∧
      ¬Fin15AnchoredAtom2649 chi ∧
      ¬Fin15AnchoredAtom2653 chi ∧
      ¬Fin15AnchoredAtom2678 chi ∧
      ¬Fin15AnchoredAtom2769 chi ∧
      ¬Fin15AnchoredAtom3216 chi ∧
      ¬Fin15AnchoredAtom3217 chi ∧
      ¬Fin15AnchoredAtom3220 chi ∧
      ¬Fin15AnchoredAtom3228 chi ∧
      ¬Fin15AnchoredAtom3231 chi ∧
      ¬Fin15AnchoredAtom3235 chi ∧
      ¬Fin15AnchoredAtom3277 chi ∧
      ¬Fin15AnchoredAtom3280 chi ∧
      ¬Fin15AnchoredAtom3284 chi ∧
      ¬Fin15AnchoredAtom3309 chi ∧
      ¬Fin15AnchoredAtom3361 chi ∧
      ¬Fin15AnchoredAtom3364 chi ∧
      ¬Fin15AnchoredAtom3368 chi ∧
      ¬Fin15AnchoredAtom3393 chi ∧
      ¬Fin15AnchoredAtom3484 chi ∧
      ¬Fin15AnchoredAtom4396 chi ∧
      ¬Fin15AnchoredAtom4399 chi ∧
      ¬Fin15AnchoredAtom4403 chi ∧
      ¬Fin15AnchoredAtom4428 chi ∧
      ¬Fin15AnchoredAtom4519 chi ∧
      ¬Fin15AnchoredAtom4645 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 5, 7, 9, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09907
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1943 Fin15AnchoredAtom1945 Fin15AnchoredAtom1946
    Fin15AnchoredAtom1949 Fin15AnchoredAtom1960 Fin15AnchoredAtom1961 Fin15AnchoredAtom1964
    Fin15AnchoredAtom1972 Fin15AnchoredAtom1975 Fin15AnchoredAtom1979 Fin15AnchoredAtom1996
    Fin15AnchoredAtom1997 Fin15AnchoredAtom2000 Fin15AnchoredAtom2008 Fin15AnchoredAtom2011
    Fin15AnchoredAtom2015 Fin15AnchoredAtom2057 Fin15AnchoredAtom2060 Fin15AnchoredAtom2064
    Fin15AnchoredAtom2089 Fin15AnchoredAtom2501 Fin15AnchoredAtom2502 Fin15AnchoredAtom2505
    Fin15AnchoredAtom2513 Fin15AnchoredAtom2516 Fin15AnchoredAtom2520 Fin15AnchoredAtom2562
    Fin15AnchoredAtom2565 Fin15AnchoredAtom2569 Fin15AnchoredAtom2594 Fin15AnchoredAtom2646
    Fin15AnchoredAtom2649 Fin15AnchoredAtom2653 Fin15AnchoredAtom2678 Fin15AnchoredAtom2769
    Fin15AnchoredAtom3216 Fin15AnchoredAtom3217 Fin15AnchoredAtom3220 Fin15AnchoredAtom3228
    Fin15AnchoredAtom3231 Fin15AnchoredAtom3235 Fin15AnchoredAtom3277 Fin15AnchoredAtom3280
    Fin15AnchoredAtom3284 Fin15AnchoredAtom3309 Fin15AnchoredAtom3361 Fin15AnchoredAtom3364
    Fin15AnchoredAtom3368 Fin15AnchoredAtom3393 Fin15AnchoredAtom3484 Fin15AnchoredAtom4396
    Fin15AnchoredAtom4399 Fin15AnchoredAtom4403 Fin15AnchoredAtom4428 Fin15AnchoredAtom4519
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

theorem fin15Anchored_clause30994 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom1976 chi ∧
      ¬Fin15AnchoredAtom1980 chi ∧
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
      ¬Fin15AnchoredAtom2501 chi ∧
      ¬Fin15AnchoredAtom2502 chi ∧
      ¬Fin15AnchoredAtom2506 chi ∧
      ¬Fin15AnchoredAtom2513 chi ∧
      ¬Fin15AnchoredAtom2517 chi ∧
      ¬Fin15AnchoredAtom2521 chi ∧
      ¬Fin15AnchoredAtom2562 chi ∧
      ¬Fin15AnchoredAtom2566 chi ∧
      ¬Fin15AnchoredAtom2570 chi ∧
      ¬Fin15AnchoredAtom2595 chi ∧
      ¬Fin15AnchoredAtom2646 chi ∧
      ¬Fin15AnchoredAtom2650 chi ∧
      ¬Fin15AnchoredAtom2654 chi ∧
      ¬Fin15AnchoredAtom2679 chi ∧
      ¬Fin15AnchoredAtom2770 chi ∧
      ¬Fin15AnchoredAtom3216 chi ∧
      ¬Fin15AnchoredAtom3217 chi ∧
      ¬Fin15AnchoredAtom3221 chi ∧
      ¬Fin15AnchoredAtom3228 chi ∧
      ¬Fin15AnchoredAtom3232 chi ∧
      ¬Fin15AnchoredAtom3236 chi ∧
      ¬Fin15AnchoredAtom3277 chi ∧
      ¬Fin15AnchoredAtom3281 chi ∧
      ¬Fin15AnchoredAtom3285 chi ∧
      ¬Fin15AnchoredAtom3310 chi ∧
      ¬Fin15AnchoredAtom3361 chi ∧
      ¬Fin15AnchoredAtom3365 chi ∧
      ¬Fin15AnchoredAtom3369 chi ∧
      ¬Fin15AnchoredAtom3394 chi ∧
      ¬Fin15AnchoredAtom3485 chi ∧
      ¬Fin15AnchoredAtom4396 chi ∧
      ¬Fin15AnchoredAtom4400 chi ∧
      ¬Fin15AnchoredAtom4404 chi ∧
      ¬Fin15AnchoredAtom4429 chi ∧
      ¬Fin15AnchoredAtom4520 chi ∧
      ¬Fin15AnchoredAtom4646 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 5, 7, 9, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask18099
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1943 Fin15AnchoredAtom1945 Fin15AnchoredAtom1946
    Fin15AnchoredAtom1950 Fin15AnchoredAtom1960 Fin15AnchoredAtom1961 Fin15AnchoredAtom1965
    Fin15AnchoredAtom1972 Fin15AnchoredAtom1976 Fin15AnchoredAtom1980 Fin15AnchoredAtom1996
    Fin15AnchoredAtom1997 Fin15AnchoredAtom2001 Fin15AnchoredAtom2008 Fin15AnchoredAtom2012
    Fin15AnchoredAtom2016 Fin15AnchoredAtom2057 Fin15AnchoredAtom2061 Fin15AnchoredAtom2065
    Fin15AnchoredAtom2090 Fin15AnchoredAtom2501 Fin15AnchoredAtom2502 Fin15AnchoredAtom2506
    Fin15AnchoredAtom2513 Fin15AnchoredAtom2517 Fin15AnchoredAtom2521 Fin15AnchoredAtom2562
    Fin15AnchoredAtom2566 Fin15AnchoredAtom2570 Fin15AnchoredAtom2595 Fin15AnchoredAtom2646
    Fin15AnchoredAtom2650 Fin15AnchoredAtom2654 Fin15AnchoredAtom2679 Fin15AnchoredAtom2770
    Fin15AnchoredAtom3216 Fin15AnchoredAtom3217 Fin15AnchoredAtom3221 Fin15AnchoredAtom3228
    Fin15AnchoredAtom3232 Fin15AnchoredAtom3236 Fin15AnchoredAtom3277 Fin15AnchoredAtom3281
    Fin15AnchoredAtom3285 Fin15AnchoredAtom3310 Fin15AnchoredAtom3361 Fin15AnchoredAtom3365
    Fin15AnchoredAtom3369 Fin15AnchoredAtom3394 Fin15AnchoredAtom3485 Fin15AnchoredAtom4396
    Fin15AnchoredAtom4400 Fin15AnchoredAtom4404 Fin15AnchoredAtom4429 Fin15AnchoredAtom4520
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

theorem fin15Anchored_clause30995 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom1947 chi ∧
      ¬Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom1962 chi ∧
      ¬Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom1973 chi ∧
      ¬Fin15AnchoredAtom1976 chi ∧
      ¬Fin15AnchoredAtom1983 chi ∧
      ¬Fin15AnchoredAtom1996 chi ∧
      ¬Fin15AnchoredAtom1998 chi ∧
      ¬Fin15AnchoredAtom2001 chi ∧
      ¬Fin15AnchoredAtom2009 chi ∧
      ¬Fin15AnchoredAtom2012 chi ∧
      ¬Fin15AnchoredAtom2019 chi ∧
      ¬Fin15AnchoredAtom2058 chi ∧
      ¬Fin15AnchoredAtom2061 chi ∧
      ¬Fin15AnchoredAtom2068 chi ∧
      ¬Fin15AnchoredAtom2093 chi ∧
      ¬Fin15AnchoredAtom2501 chi ∧
      ¬Fin15AnchoredAtom2503 chi ∧
      ¬Fin15AnchoredAtom2506 chi ∧
      ¬Fin15AnchoredAtom2514 chi ∧
      ¬Fin15AnchoredAtom2517 chi ∧
      ¬Fin15AnchoredAtom2524 chi ∧
      ¬Fin15AnchoredAtom2563 chi ∧
      ¬Fin15AnchoredAtom2566 chi ∧
      ¬Fin15AnchoredAtom2573 chi ∧
      ¬Fin15AnchoredAtom2598 chi ∧
      ¬Fin15AnchoredAtom2647 chi ∧
      ¬Fin15AnchoredAtom2650 chi ∧
      ¬Fin15AnchoredAtom2657 chi ∧
      ¬Fin15AnchoredAtom2682 chi ∧
      ¬Fin15AnchoredAtom2773 chi ∧
      ¬Fin15AnchoredAtom3216 chi ∧
      ¬Fin15AnchoredAtom3218 chi ∧
      ¬Fin15AnchoredAtom3221 chi ∧
      ¬Fin15AnchoredAtom3229 chi ∧
      ¬Fin15AnchoredAtom3232 chi ∧
      ¬Fin15AnchoredAtom3239 chi ∧
      ¬Fin15AnchoredAtom3278 chi ∧
      ¬Fin15AnchoredAtom3281 chi ∧
      ¬Fin15AnchoredAtom3288 chi ∧
      ¬Fin15AnchoredAtom3313 chi ∧
      ¬Fin15AnchoredAtom3362 chi ∧
      ¬Fin15AnchoredAtom3365 chi ∧
      ¬Fin15AnchoredAtom3372 chi ∧
      ¬Fin15AnchoredAtom3397 chi ∧
      ¬Fin15AnchoredAtom3488 chi ∧
      ¬Fin15AnchoredAtom4397 chi ∧
      ¬Fin15AnchoredAtom4400 chi ∧
      ¬Fin15AnchoredAtom4407 chi ∧
      ¬Fin15AnchoredAtom4432 chi ∧
      ¬Fin15AnchoredAtom4523 chi ∧
      ¬Fin15AnchoredAtom4649 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 5, 7, 9, 11, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask19123
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1943 Fin15AnchoredAtom1945 Fin15AnchoredAtom1947
    Fin15AnchoredAtom1950 Fin15AnchoredAtom1960 Fin15AnchoredAtom1962 Fin15AnchoredAtom1965
    Fin15AnchoredAtom1973 Fin15AnchoredAtom1976 Fin15AnchoredAtom1983 Fin15AnchoredAtom1996
    Fin15AnchoredAtom1998 Fin15AnchoredAtom2001 Fin15AnchoredAtom2009 Fin15AnchoredAtom2012
    Fin15AnchoredAtom2019 Fin15AnchoredAtom2058 Fin15AnchoredAtom2061 Fin15AnchoredAtom2068
    Fin15AnchoredAtom2093 Fin15AnchoredAtom2501 Fin15AnchoredAtom2503 Fin15AnchoredAtom2506
    Fin15AnchoredAtom2514 Fin15AnchoredAtom2517 Fin15AnchoredAtom2524 Fin15AnchoredAtom2563
    Fin15AnchoredAtom2566 Fin15AnchoredAtom2573 Fin15AnchoredAtom2598 Fin15AnchoredAtom2647
    Fin15AnchoredAtom2650 Fin15AnchoredAtom2657 Fin15AnchoredAtom2682 Fin15AnchoredAtom2773
    Fin15AnchoredAtom3216 Fin15AnchoredAtom3218 Fin15AnchoredAtom3221 Fin15AnchoredAtom3229
    Fin15AnchoredAtom3232 Fin15AnchoredAtom3239 Fin15AnchoredAtom3278 Fin15AnchoredAtom3281
    Fin15AnchoredAtom3288 Fin15AnchoredAtom3313 Fin15AnchoredAtom3362 Fin15AnchoredAtom3365
    Fin15AnchoredAtom3372 Fin15AnchoredAtom3397 Fin15AnchoredAtom3488 Fin15AnchoredAtom4397
    Fin15AnchoredAtom4400 Fin15AnchoredAtom4407 Fin15AnchoredAtom4432 Fin15AnchoredAtom4523
    Fin15AnchoredAtom4649 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30996 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom1984 chi ∧
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
      ¬Fin15AnchoredAtom2501 chi ∧
      ¬Fin15AnchoredAtom2504 chi ∧
      ¬Fin15AnchoredAtom2505 chi ∧
      ¬Fin15AnchoredAtom2515 chi ∧
      ¬Fin15AnchoredAtom2516 chi ∧
      ¬Fin15AnchoredAtom2525 chi ∧
      ¬Fin15AnchoredAtom2564 chi ∧
      ¬Fin15AnchoredAtom2565 chi ∧
      ¬Fin15AnchoredAtom2574 chi ∧
      ¬Fin15AnchoredAtom2599 chi ∧
      ¬Fin15AnchoredAtom2648 chi ∧
      ¬Fin15AnchoredAtom2649 chi ∧
      ¬Fin15AnchoredAtom2658 chi ∧
      ¬Fin15AnchoredAtom2683 chi ∧
      ¬Fin15AnchoredAtom2774 chi ∧
      ¬Fin15AnchoredAtom3216 chi ∧
      ¬Fin15AnchoredAtom3219 chi ∧
      ¬Fin15AnchoredAtom3220 chi ∧
      ¬Fin15AnchoredAtom3230 chi ∧
      ¬Fin15AnchoredAtom3231 chi ∧
      ¬Fin15AnchoredAtom3240 chi ∧
      ¬Fin15AnchoredAtom3279 chi ∧
      ¬Fin15AnchoredAtom3280 chi ∧
      ¬Fin15AnchoredAtom3289 chi ∧
      ¬Fin15AnchoredAtom3314 chi ∧
      ¬Fin15AnchoredAtom3363 chi ∧
      ¬Fin15AnchoredAtom3364 chi ∧
      ¬Fin15AnchoredAtom3373 chi ∧
      ¬Fin15AnchoredAtom3398 chi ∧
      ¬Fin15AnchoredAtom3489 chi ∧
      ¬Fin15AnchoredAtom4398 chi ∧
      ¬Fin15AnchoredAtom4399 chi ∧
      ¬Fin15AnchoredAtom4408 chi ∧
      ¬Fin15AnchoredAtom4433 chi ∧
      ¬Fin15AnchoredAtom4524 chi ∧
      ¬Fin15AnchoredAtom4650 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 5, 7, 9, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask12979
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1943 Fin15AnchoredAtom1945 Fin15AnchoredAtom1948
    Fin15AnchoredAtom1949 Fin15AnchoredAtom1960 Fin15AnchoredAtom1963 Fin15AnchoredAtom1964
    Fin15AnchoredAtom1974 Fin15AnchoredAtom1975 Fin15AnchoredAtom1984 Fin15AnchoredAtom1996
    Fin15AnchoredAtom1999 Fin15AnchoredAtom2000 Fin15AnchoredAtom2010 Fin15AnchoredAtom2011
    Fin15AnchoredAtom2020 Fin15AnchoredAtom2059 Fin15AnchoredAtom2060 Fin15AnchoredAtom2069
    Fin15AnchoredAtom2094 Fin15AnchoredAtom2501 Fin15AnchoredAtom2504 Fin15AnchoredAtom2505
    Fin15AnchoredAtom2515 Fin15AnchoredAtom2516 Fin15AnchoredAtom2525 Fin15AnchoredAtom2564
    Fin15AnchoredAtom2565 Fin15AnchoredAtom2574 Fin15AnchoredAtom2599 Fin15AnchoredAtom2648
    Fin15AnchoredAtom2649 Fin15AnchoredAtom2658 Fin15AnchoredAtom2683 Fin15AnchoredAtom2774
    Fin15AnchoredAtom3216 Fin15AnchoredAtom3219 Fin15AnchoredAtom3220 Fin15AnchoredAtom3230
    Fin15AnchoredAtom3231 Fin15AnchoredAtom3240 Fin15AnchoredAtom3279 Fin15AnchoredAtom3280
    Fin15AnchoredAtom3289 Fin15AnchoredAtom3314 Fin15AnchoredAtom3363 Fin15AnchoredAtom3364
    Fin15AnchoredAtom3373 Fin15AnchoredAtom3398 Fin15AnchoredAtom3489 Fin15AnchoredAtom4398
    Fin15AnchoredAtom4399 Fin15AnchoredAtom4408 Fin15AnchoredAtom4433 Fin15AnchoredAtom4524
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

theorem fin15Anchored_clause30997 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom1976 chi ∧
      ¬Fin15AnchoredAtom1985 chi ∧
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
      ¬Fin15AnchoredAtom2501 chi ∧
      ¬Fin15AnchoredAtom2504 chi ∧
      ¬Fin15AnchoredAtom2506 chi ∧
      ¬Fin15AnchoredAtom2515 chi ∧
      ¬Fin15AnchoredAtom2517 chi ∧
      ¬Fin15AnchoredAtom2526 chi ∧
      ¬Fin15AnchoredAtom2564 chi ∧
      ¬Fin15AnchoredAtom2566 chi ∧
      ¬Fin15AnchoredAtom2575 chi ∧
      ¬Fin15AnchoredAtom2600 chi ∧
      ¬Fin15AnchoredAtom2648 chi ∧
      ¬Fin15AnchoredAtom2650 chi ∧
      ¬Fin15AnchoredAtom2659 chi ∧
      ¬Fin15AnchoredAtom2684 chi ∧
      ¬Fin15AnchoredAtom2775 chi ∧
      ¬Fin15AnchoredAtom3216 chi ∧
      ¬Fin15AnchoredAtom3219 chi ∧
      ¬Fin15AnchoredAtom3221 chi ∧
      ¬Fin15AnchoredAtom3230 chi ∧
      ¬Fin15AnchoredAtom3232 chi ∧
      ¬Fin15AnchoredAtom3241 chi ∧
      ¬Fin15AnchoredAtom3279 chi ∧
      ¬Fin15AnchoredAtom3281 chi ∧
      ¬Fin15AnchoredAtom3290 chi ∧
      ¬Fin15AnchoredAtom3315 chi ∧
      ¬Fin15AnchoredAtom3363 chi ∧
      ¬Fin15AnchoredAtom3365 chi ∧
      ¬Fin15AnchoredAtom3374 chi ∧
      ¬Fin15AnchoredAtom3399 chi ∧
      ¬Fin15AnchoredAtom3490 chi ∧
      ¬Fin15AnchoredAtom4398 chi ∧
      ¬Fin15AnchoredAtom4400 chi ∧
      ¬Fin15AnchoredAtom4409 chi ∧
      ¬Fin15AnchoredAtom4434 chi ∧
      ¬Fin15AnchoredAtom4525 chi ∧
      ¬Fin15AnchoredAtom4651 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 5, 7, 9, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21171
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1943 Fin15AnchoredAtom1945 Fin15AnchoredAtom1948
    Fin15AnchoredAtom1950 Fin15AnchoredAtom1960 Fin15AnchoredAtom1963 Fin15AnchoredAtom1965
    Fin15AnchoredAtom1974 Fin15AnchoredAtom1976 Fin15AnchoredAtom1985 Fin15AnchoredAtom1996
    Fin15AnchoredAtom1999 Fin15AnchoredAtom2001 Fin15AnchoredAtom2010 Fin15AnchoredAtom2012
    Fin15AnchoredAtom2021 Fin15AnchoredAtom2059 Fin15AnchoredAtom2061 Fin15AnchoredAtom2070
    Fin15AnchoredAtom2095 Fin15AnchoredAtom2501 Fin15AnchoredAtom2504 Fin15AnchoredAtom2506
    Fin15AnchoredAtom2515 Fin15AnchoredAtom2517 Fin15AnchoredAtom2526 Fin15AnchoredAtom2564
    Fin15AnchoredAtom2566 Fin15AnchoredAtom2575 Fin15AnchoredAtom2600 Fin15AnchoredAtom2648
    Fin15AnchoredAtom2650 Fin15AnchoredAtom2659 Fin15AnchoredAtom2684 Fin15AnchoredAtom2775
    Fin15AnchoredAtom3216 Fin15AnchoredAtom3219 Fin15AnchoredAtom3221 Fin15AnchoredAtom3230
    Fin15AnchoredAtom3232 Fin15AnchoredAtom3241 Fin15AnchoredAtom3279 Fin15AnchoredAtom3281
    Fin15AnchoredAtom3290 Fin15AnchoredAtom3315 Fin15AnchoredAtom3363 Fin15AnchoredAtom3365
    Fin15AnchoredAtom3374 Fin15AnchoredAtom3399 Fin15AnchoredAtom3490 Fin15AnchoredAtom4398
    Fin15AnchoredAtom4400 Fin15AnchoredAtom4409 Fin15AnchoredAtom4434 Fin15AnchoredAtom4525
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

theorem fin15Anchored_clause30998 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom1976 chi ∧
      ¬Fin15AnchoredAtom1986 chi ∧
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
      ¬Fin15AnchoredAtom2501 chi ∧
      ¬Fin15AnchoredAtom2505 chi ∧
      ¬Fin15AnchoredAtom2506 chi ∧
      ¬Fin15AnchoredAtom2516 chi ∧
      ¬Fin15AnchoredAtom2517 chi ∧
      ¬Fin15AnchoredAtom2527 chi ∧
      ¬Fin15AnchoredAtom2565 chi ∧
      ¬Fin15AnchoredAtom2566 chi ∧
      ¬Fin15AnchoredAtom2576 chi ∧
      ¬Fin15AnchoredAtom2601 chi ∧
      ¬Fin15AnchoredAtom2649 chi ∧
      ¬Fin15AnchoredAtom2650 chi ∧
      ¬Fin15AnchoredAtom2660 chi ∧
      ¬Fin15AnchoredAtom2685 chi ∧
      ¬Fin15AnchoredAtom2776 chi ∧
      ¬Fin15AnchoredAtom3216 chi ∧
      ¬Fin15AnchoredAtom3220 chi ∧
      ¬Fin15AnchoredAtom3221 chi ∧
      ¬Fin15AnchoredAtom3231 chi ∧
      ¬Fin15AnchoredAtom3232 chi ∧
      ¬Fin15AnchoredAtom3242 chi ∧
      ¬Fin15AnchoredAtom3280 chi ∧
      ¬Fin15AnchoredAtom3281 chi ∧
      ¬Fin15AnchoredAtom3291 chi ∧
      ¬Fin15AnchoredAtom3316 chi ∧
      ¬Fin15AnchoredAtom3364 chi ∧
      ¬Fin15AnchoredAtom3365 chi ∧
      ¬Fin15AnchoredAtom3375 chi ∧
      ¬Fin15AnchoredAtom3400 chi ∧
      ¬Fin15AnchoredAtom3491 chi ∧
      ¬Fin15AnchoredAtom4399 chi ∧
      ¬Fin15AnchoredAtom4400 chi ∧
      ¬Fin15AnchoredAtom4410 chi ∧
      ¬Fin15AnchoredAtom4435 chi ∧
      ¬Fin15AnchoredAtom4526 chi ∧
      ¬Fin15AnchoredAtom4652 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 5, 7, 9, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25267
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1943 Fin15AnchoredAtom1945 Fin15AnchoredAtom1949
    Fin15AnchoredAtom1950 Fin15AnchoredAtom1960 Fin15AnchoredAtom1964 Fin15AnchoredAtom1965
    Fin15AnchoredAtom1975 Fin15AnchoredAtom1976 Fin15AnchoredAtom1986 Fin15AnchoredAtom1996
    Fin15AnchoredAtom2000 Fin15AnchoredAtom2001 Fin15AnchoredAtom2011 Fin15AnchoredAtom2012
    Fin15AnchoredAtom2022 Fin15AnchoredAtom2060 Fin15AnchoredAtom2061 Fin15AnchoredAtom2071
    Fin15AnchoredAtom2096 Fin15AnchoredAtom2501 Fin15AnchoredAtom2505 Fin15AnchoredAtom2506
    Fin15AnchoredAtom2516 Fin15AnchoredAtom2517 Fin15AnchoredAtom2527 Fin15AnchoredAtom2565
    Fin15AnchoredAtom2566 Fin15AnchoredAtom2576 Fin15AnchoredAtom2601 Fin15AnchoredAtom2649
    Fin15AnchoredAtom2650 Fin15AnchoredAtom2660 Fin15AnchoredAtom2685 Fin15AnchoredAtom2776
    Fin15AnchoredAtom3216 Fin15AnchoredAtom3220 Fin15AnchoredAtom3221 Fin15AnchoredAtom3231
    Fin15AnchoredAtom3232 Fin15AnchoredAtom3242 Fin15AnchoredAtom3280 Fin15AnchoredAtom3281
    Fin15AnchoredAtom3291 Fin15AnchoredAtom3316 Fin15AnchoredAtom3364 Fin15AnchoredAtom3365
    Fin15AnchoredAtom3375 Fin15AnchoredAtom3400 Fin15AnchoredAtom3491 Fin15AnchoredAtom4399
    Fin15AnchoredAtom4400 Fin15AnchoredAtom4410 Fin15AnchoredAtom4435 Fin15AnchoredAtom4526
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

theorem fin15Anchored_clause30999 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1947 chi ∧
      ¬Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom1962 chi ∧
      ¬Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom1977 chi ∧
      ¬Fin15AnchoredAtom1980 chi ∧
      ¬Fin15AnchoredAtom1983 chi ∧
      ¬Fin15AnchoredAtom1997 chi ∧
      ¬Fin15AnchoredAtom1998 chi ∧
      ¬Fin15AnchoredAtom2001 chi ∧
      ¬Fin15AnchoredAtom2013 chi ∧
      ¬Fin15AnchoredAtom2016 chi ∧
      ¬Fin15AnchoredAtom2019 chi ∧
      ¬Fin15AnchoredAtom2062 chi ∧
      ¬Fin15AnchoredAtom2065 chi ∧
      ¬Fin15AnchoredAtom2068 chi ∧
      ¬Fin15AnchoredAtom2099 chi ∧
      ¬Fin15AnchoredAtom2502 chi ∧
      ¬Fin15AnchoredAtom2503 chi ∧
      ¬Fin15AnchoredAtom2506 chi ∧
      ¬Fin15AnchoredAtom2518 chi ∧
      ¬Fin15AnchoredAtom2521 chi ∧
      ¬Fin15AnchoredAtom2524 chi ∧
      ¬Fin15AnchoredAtom2567 chi ∧
      ¬Fin15AnchoredAtom2570 chi ∧
      ¬Fin15AnchoredAtom2573 chi ∧
      ¬Fin15AnchoredAtom2604 chi ∧
      ¬Fin15AnchoredAtom2651 chi ∧
      ¬Fin15AnchoredAtom2654 chi ∧
      ¬Fin15AnchoredAtom2657 chi ∧
      ¬Fin15AnchoredAtom2688 chi ∧
      ¬Fin15AnchoredAtom2779 chi ∧
      ¬Fin15AnchoredAtom3217 chi ∧
      ¬Fin15AnchoredAtom3218 chi ∧
      ¬Fin15AnchoredAtom3221 chi ∧
      ¬Fin15AnchoredAtom3233 chi ∧
      ¬Fin15AnchoredAtom3236 chi ∧
      ¬Fin15AnchoredAtom3239 chi ∧
      ¬Fin15AnchoredAtom3282 chi ∧
      ¬Fin15AnchoredAtom3285 chi ∧
      ¬Fin15AnchoredAtom3288 chi ∧
      ¬Fin15AnchoredAtom3319 chi ∧
      ¬Fin15AnchoredAtom3366 chi ∧
      ¬Fin15AnchoredAtom3369 chi ∧
      ¬Fin15AnchoredAtom3372 chi ∧
      ¬Fin15AnchoredAtom3403 chi ∧
      ¬Fin15AnchoredAtom3494 chi ∧
      ¬Fin15AnchoredAtom4401 chi ∧
      ¬Fin15AnchoredAtom4404 chi ∧
      ¬Fin15AnchoredAtom4407 chi ∧
      ¬Fin15AnchoredAtom4438 chi ∧
      ¬Fin15AnchoredAtom4529 chi ∧
      ¬Fin15AnchoredAtom4655 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 5, 7, 10, 11, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask19635
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1943 Fin15AnchoredAtom1946 Fin15AnchoredAtom1947
    Fin15AnchoredAtom1950 Fin15AnchoredAtom1961 Fin15AnchoredAtom1962 Fin15AnchoredAtom1965
    Fin15AnchoredAtom1977 Fin15AnchoredAtom1980 Fin15AnchoredAtom1983 Fin15AnchoredAtom1997
    Fin15AnchoredAtom1998 Fin15AnchoredAtom2001 Fin15AnchoredAtom2013 Fin15AnchoredAtom2016
    Fin15AnchoredAtom2019 Fin15AnchoredAtom2062 Fin15AnchoredAtom2065 Fin15AnchoredAtom2068
    Fin15AnchoredAtom2099 Fin15AnchoredAtom2502 Fin15AnchoredAtom2503 Fin15AnchoredAtom2506
    Fin15AnchoredAtom2518 Fin15AnchoredAtom2521 Fin15AnchoredAtom2524 Fin15AnchoredAtom2567
    Fin15AnchoredAtom2570 Fin15AnchoredAtom2573 Fin15AnchoredAtom2604 Fin15AnchoredAtom2651
    Fin15AnchoredAtom2654 Fin15AnchoredAtom2657 Fin15AnchoredAtom2688 Fin15AnchoredAtom2779
    Fin15AnchoredAtom3217 Fin15AnchoredAtom3218 Fin15AnchoredAtom3221 Fin15AnchoredAtom3233
    Fin15AnchoredAtom3236 Fin15AnchoredAtom3239 Fin15AnchoredAtom3282 Fin15AnchoredAtom3285
    Fin15AnchoredAtom3288 Fin15AnchoredAtom3319 Fin15AnchoredAtom3366 Fin15AnchoredAtom3369
    Fin15AnchoredAtom3372 Fin15AnchoredAtom3403 Fin15AnchoredAtom3494 Fin15AnchoredAtom4401
    Fin15AnchoredAtom4404 Fin15AnchoredAtom4407 Fin15AnchoredAtom4438 Fin15AnchoredAtom4529
    Fin15AnchoredAtom4655 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31000 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom1978 chi ∧
      ¬Fin15AnchoredAtom1979 chi ∧
      ¬Fin15AnchoredAtom1984 chi ∧
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
      ¬Fin15AnchoredAtom2502 chi ∧
      ¬Fin15AnchoredAtom2504 chi ∧
      ¬Fin15AnchoredAtom2505 chi ∧
      ¬Fin15AnchoredAtom2519 chi ∧
      ¬Fin15AnchoredAtom2520 chi ∧
      ¬Fin15AnchoredAtom2525 chi ∧
      ¬Fin15AnchoredAtom2568 chi ∧
      ¬Fin15AnchoredAtom2569 chi ∧
      ¬Fin15AnchoredAtom2574 chi ∧
      ¬Fin15AnchoredAtom2605 chi ∧
      ¬Fin15AnchoredAtom2652 chi ∧
      ¬Fin15AnchoredAtom2653 chi ∧
      ¬Fin15AnchoredAtom2658 chi ∧
      ¬Fin15AnchoredAtom2689 chi ∧
      ¬Fin15AnchoredAtom2780 chi ∧
      ¬Fin15AnchoredAtom3217 chi ∧
      ¬Fin15AnchoredAtom3219 chi ∧
      ¬Fin15AnchoredAtom3220 chi ∧
      ¬Fin15AnchoredAtom3234 chi ∧
      ¬Fin15AnchoredAtom3235 chi ∧
      ¬Fin15AnchoredAtom3240 chi ∧
      ¬Fin15AnchoredAtom3283 chi ∧
      ¬Fin15AnchoredAtom3284 chi ∧
      ¬Fin15AnchoredAtom3289 chi ∧
      ¬Fin15AnchoredAtom3320 chi ∧
      ¬Fin15AnchoredAtom3367 chi ∧
      ¬Fin15AnchoredAtom3368 chi ∧
      ¬Fin15AnchoredAtom3373 chi ∧
      ¬Fin15AnchoredAtom3404 chi ∧
      ¬Fin15AnchoredAtom3495 chi ∧
      ¬Fin15AnchoredAtom4402 chi ∧
      ¬Fin15AnchoredAtom4403 chi ∧
      ¬Fin15AnchoredAtom4408 chi ∧
      ¬Fin15AnchoredAtom4439 chi ∧
      ¬Fin15AnchoredAtom4530 chi ∧
      ¬Fin15AnchoredAtom4656 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 5, 7, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13491
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1943 Fin15AnchoredAtom1946 Fin15AnchoredAtom1948
    Fin15AnchoredAtom1949 Fin15AnchoredAtom1961 Fin15AnchoredAtom1963 Fin15AnchoredAtom1964
    Fin15AnchoredAtom1978 Fin15AnchoredAtom1979 Fin15AnchoredAtom1984 Fin15AnchoredAtom1997
    Fin15AnchoredAtom1999 Fin15AnchoredAtom2000 Fin15AnchoredAtom2014 Fin15AnchoredAtom2015
    Fin15AnchoredAtom2020 Fin15AnchoredAtom2063 Fin15AnchoredAtom2064 Fin15AnchoredAtom2069
    Fin15AnchoredAtom2100 Fin15AnchoredAtom2502 Fin15AnchoredAtom2504 Fin15AnchoredAtom2505
    Fin15AnchoredAtom2519 Fin15AnchoredAtom2520 Fin15AnchoredAtom2525 Fin15AnchoredAtom2568
    Fin15AnchoredAtom2569 Fin15AnchoredAtom2574 Fin15AnchoredAtom2605 Fin15AnchoredAtom2652
    Fin15AnchoredAtom2653 Fin15AnchoredAtom2658 Fin15AnchoredAtom2689 Fin15AnchoredAtom2780
    Fin15AnchoredAtom3217 Fin15AnchoredAtom3219 Fin15AnchoredAtom3220 Fin15AnchoredAtom3234
    Fin15AnchoredAtom3235 Fin15AnchoredAtom3240 Fin15AnchoredAtom3283 Fin15AnchoredAtom3284
    Fin15AnchoredAtom3289 Fin15AnchoredAtom3320 Fin15AnchoredAtom3367 Fin15AnchoredAtom3368
    Fin15AnchoredAtom3373 Fin15AnchoredAtom3404 Fin15AnchoredAtom3495 Fin15AnchoredAtom4402
    Fin15AnchoredAtom4403 Fin15AnchoredAtom4408 Fin15AnchoredAtom4439 Fin15AnchoredAtom4530
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

theorem fin15Anchored_clause31001 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom1978 chi ∧
      ¬Fin15AnchoredAtom1980 chi ∧
      ¬Fin15AnchoredAtom1985 chi ∧
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
      ¬Fin15AnchoredAtom2502 chi ∧
      ¬Fin15AnchoredAtom2504 chi ∧
      ¬Fin15AnchoredAtom2506 chi ∧
      ¬Fin15AnchoredAtom2519 chi ∧
      ¬Fin15AnchoredAtom2521 chi ∧
      ¬Fin15AnchoredAtom2526 chi ∧
      ¬Fin15AnchoredAtom2568 chi ∧
      ¬Fin15AnchoredAtom2570 chi ∧
      ¬Fin15AnchoredAtom2575 chi ∧
      ¬Fin15AnchoredAtom2606 chi ∧
      ¬Fin15AnchoredAtom2652 chi ∧
      ¬Fin15AnchoredAtom2654 chi ∧
      ¬Fin15AnchoredAtom2659 chi ∧
      ¬Fin15AnchoredAtom2690 chi ∧
      ¬Fin15AnchoredAtom2781 chi ∧
      ¬Fin15AnchoredAtom3217 chi ∧
      ¬Fin15AnchoredAtom3219 chi ∧
      ¬Fin15AnchoredAtom3221 chi ∧
      ¬Fin15AnchoredAtom3234 chi ∧
      ¬Fin15AnchoredAtom3236 chi ∧
      ¬Fin15AnchoredAtom3241 chi ∧
      ¬Fin15AnchoredAtom3283 chi ∧
      ¬Fin15AnchoredAtom3285 chi ∧
      ¬Fin15AnchoredAtom3290 chi ∧
      ¬Fin15AnchoredAtom3321 chi ∧
      ¬Fin15AnchoredAtom3367 chi ∧
      ¬Fin15AnchoredAtom3369 chi ∧
      ¬Fin15AnchoredAtom3374 chi ∧
      ¬Fin15AnchoredAtom3405 chi ∧
      ¬Fin15AnchoredAtom3496 chi ∧
      ¬Fin15AnchoredAtom4402 chi ∧
      ¬Fin15AnchoredAtom4404 chi ∧
      ¬Fin15AnchoredAtom4409 chi ∧
      ¬Fin15AnchoredAtom4440 chi ∧
      ¬Fin15AnchoredAtom4531 chi ∧
      ¬Fin15AnchoredAtom4657 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 5, 7, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21683
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1943 Fin15AnchoredAtom1946 Fin15AnchoredAtom1948
    Fin15AnchoredAtom1950 Fin15AnchoredAtom1961 Fin15AnchoredAtom1963 Fin15AnchoredAtom1965
    Fin15AnchoredAtom1978 Fin15AnchoredAtom1980 Fin15AnchoredAtom1985 Fin15AnchoredAtom1997
    Fin15AnchoredAtom1999 Fin15AnchoredAtom2001 Fin15AnchoredAtom2014 Fin15AnchoredAtom2016
    Fin15AnchoredAtom2021 Fin15AnchoredAtom2063 Fin15AnchoredAtom2065 Fin15AnchoredAtom2070
    Fin15AnchoredAtom2101 Fin15AnchoredAtom2502 Fin15AnchoredAtom2504 Fin15AnchoredAtom2506
    Fin15AnchoredAtom2519 Fin15AnchoredAtom2521 Fin15AnchoredAtom2526 Fin15AnchoredAtom2568
    Fin15AnchoredAtom2570 Fin15AnchoredAtom2575 Fin15AnchoredAtom2606 Fin15AnchoredAtom2652
    Fin15AnchoredAtom2654 Fin15AnchoredAtom2659 Fin15AnchoredAtom2690 Fin15AnchoredAtom2781
    Fin15AnchoredAtom3217 Fin15AnchoredAtom3219 Fin15AnchoredAtom3221 Fin15AnchoredAtom3234
    Fin15AnchoredAtom3236 Fin15AnchoredAtom3241 Fin15AnchoredAtom3283 Fin15AnchoredAtom3285
    Fin15AnchoredAtom3290 Fin15AnchoredAtom3321 Fin15AnchoredAtom3367 Fin15AnchoredAtom3369
    Fin15AnchoredAtom3374 Fin15AnchoredAtom3405 Fin15AnchoredAtom3496 Fin15AnchoredAtom4402
    Fin15AnchoredAtom4404 Fin15AnchoredAtom4409 Fin15AnchoredAtom4440 Fin15AnchoredAtom4531
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

theorem fin15Anchored_clause31002 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom1979 chi ∧
      ¬Fin15AnchoredAtom1980 chi ∧
      ¬Fin15AnchoredAtom1986 chi ∧
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
      ¬Fin15AnchoredAtom2502 chi ∧
      ¬Fin15AnchoredAtom2505 chi ∧
      ¬Fin15AnchoredAtom2506 chi ∧
      ¬Fin15AnchoredAtom2520 chi ∧
      ¬Fin15AnchoredAtom2521 chi ∧
      ¬Fin15AnchoredAtom2527 chi ∧
      ¬Fin15AnchoredAtom2569 chi ∧
      ¬Fin15AnchoredAtom2570 chi ∧
      ¬Fin15AnchoredAtom2576 chi ∧
      ¬Fin15AnchoredAtom2607 chi ∧
      ¬Fin15AnchoredAtom2653 chi ∧
      ¬Fin15AnchoredAtom2654 chi ∧
      ¬Fin15AnchoredAtom2660 chi ∧
      ¬Fin15AnchoredAtom2691 chi ∧
      ¬Fin15AnchoredAtom2782 chi ∧
      ¬Fin15AnchoredAtom3217 chi ∧
      ¬Fin15AnchoredAtom3220 chi ∧
      ¬Fin15AnchoredAtom3221 chi ∧
      ¬Fin15AnchoredAtom3235 chi ∧
      ¬Fin15AnchoredAtom3236 chi ∧
      ¬Fin15AnchoredAtom3242 chi ∧
      ¬Fin15AnchoredAtom3284 chi ∧
      ¬Fin15AnchoredAtom3285 chi ∧
      ¬Fin15AnchoredAtom3291 chi ∧
      ¬Fin15AnchoredAtom3322 chi ∧
      ¬Fin15AnchoredAtom3368 chi ∧
      ¬Fin15AnchoredAtom3369 chi ∧
      ¬Fin15AnchoredAtom3375 chi ∧
      ¬Fin15AnchoredAtom3406 chi ∧
      ¬Fin15AnchoredAtom3497 chi ∧
      ¬Fin15AnchoredAtom4403 chi ∧
      ¬Fin15AnchoredAtom4404 chi ∧
      ¬Fin15AnchoredAtom4410 chi ∧
      ¬Fin15AnchoredAtom4441 chi ∧
      ¬Fin15AnchoredAtom4532 chi ∧
      ¬Fin15AnchoredAtom4658 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 5, 7, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25779
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1943 Fin15AnchoredAtom1946 Fin15AnchoredAtom1949
    Fin15AnchoredAtom1950 Fin15AnchoredAtom1961 Fin15AnchoredAtom1964 Fin15AnchoredAtom1965
    Fin15AnchoredAtom1979 Fin15AnchoredAtom1980 Fin15AnchoredAtom1986 Fin15AnchoredAtom1997
    Fin15AnchoredAtom2000 Fin15AnchoredAtom2001 Fin15AnchoredAtom2015 Fin15AnchoredAtom2016
    Fin15AnchoredAtom2022 Fin15AnchoredAtom2064 Fin15AnchoredAtom2065 Fin15AnchoredAtom2071
    Fin15AnchoredAtom2102 Fin15AnchoredAtom2502 Fin15AnchoredAtom2505 Fin15AnchoredAtom2506
    Fin15AnchoredAtom2520 Fin15AnchoredAtom2521 Fin15AnchoredAtom2527 Fin15AnchoredAtom2569
    Fin15AnchoredAtom2570 Fin15AnchoredAtom2576 Fin15AnchoredAtom2607 Fin15AnchoredAtom2653
    Fin15AnchoredAtom2654 Fin15AnchoredAtom2660 Fin15AnchoredAtom2691 Fin15AnchoredAtom2782
    Fin15AnchoredAtom3217 Fin15AnchoredAtom3220 Fin15AnchoredAtom3221 Fin15AnchoredAtom3235
    Fin15AnchoredAtom3236 Fin15AnchoredAtom3242 Fin15AnchoredAtom3284 Fin15AnchoredAtom3285
    Fin15AnchoredAtom3291 Fin15AnchoredAtom3322 Fin15AnchoredAtom3368 Fin15AnchoredAtom3369
    Fin15AnchoredAtom3375 Fin15AnchoredAtom3406 Fin15AnchoredAtom3497 Fin15AnchoredAtom4403
    Fin15AnchoredAtom4404 Fin15AnchoredAtom4410 Fin15AnchoredAtom4441 Fin15AnchoredAtom4532
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

theorem fin15Anchored_clause31003 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom1947 chi ∧
      ¬Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom1962 chi ∧
      ¬Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom1981 chi ∧
      ¬Fin15AnchoredAtom1983 chi ∧
      ¬Fin15AnchoredAtom1985 chi ∧
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
      ¬Fin15AnchoredAtom2503 chi ∧
      ¬Fin15AnchoredAtom2504 chi ∧
      ¬Fin15AnchoredAtom2506 chi ∧
      ¬Fin15AnchoredAtom2522 chi ∧
      ¬Fin15AnchoredAtom2524 chi ∧
      ¬Fin15AnchoredAtom2526 chi ∧
      ¬Fin15AnchoredAtom2571 chi ∧
      ¬Fin15AnchoredAtom2573 chi ∧
      ¬Fin15AnchoredAtom2575 chi ∧
      ¬Fin15AnchoredAtom2609 chi ∧
      ¬Fin15AnchoredAtom2655 chi ∧
      ¬Fin15AnchoredAtom2657 chi ∧
      ¬Fin15AnchoredAtom2659 chi ∧
      ¬Fin15AnchoredAtom2693 chi ∧
      ¬Fin15AnchoredAtom2784 chi ∧
      ¬Fin15AnchoredAtom3218 chi ∧
      ¬Fin15AnchoredAtom3219 chi ∧
      ¬Fin15AnchoredAtom3221 chi ∧
      ¬Fin15AnchoredAtom3237 chi ∧
      ¬Fin15AnchoredAtom3239 chi ∧
      ¬Fin15AnchoredAtom3241 chi ∧
      ¬Fin15AnchoredAtom3286 chi ∧
      ¬Fin15AnchoredAtom3288 chi ∧
      ¬Fin15AnchoredAtom3290 chi ∧
      ¬Fin15AnchoredAtom3324 chi ∧
      ¬Fin15AnchoredAtom3370 chi ∧
      ¬Fin15AnchoredAtom3372 chi ∧
      ¬Fin15AnchoredAtom3374 chi ∧
      ¬Fin15AnchoredAtom3408 chi ∧
      ¬Fin15AnchoredAtom3499 chi ∧
      ¬Fin15AnchoredAtom4405 chi ∧
      ¬Fin15AnchoredAtom4407 chi ∧
      ¬Fin15AnchoredAtom4409 chi ∧
      ¬Fin15AnchoredAtom4443 chi ∧
      ¬Fin15AnchoredAtom4534 chi ∧
      ¬Fin15AnchoredAtom4660 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 5, 7, 11, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22707
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1943 Fin15AnchoredAtom1947 Fin15AnchoredAtom1948
    Fin15AnchoredAtom1950 Fin15AnchoredAtom1962 Fin15AnchoredAtom1963 Fin15AnchoredAtom1965
    Fin15AnchoredAtom1981 Fin15AnchoredAtom1983 Fin15AnchoredAtom1985 Fin15AnchoredAtom1998
    Fin15AnchoredAtom1999 Fin15AnchoredAtom2001 Fin15AnchoredAtom2017 Fin15AnchoredAtom2019
    Fin15AnchoredAtom2021 Fin15AnchoredAtom2066 Fin15AnchoredAtom2068 Fin15AnchoredAtom2070
    Fin15AnchoredAtom2104 Fin15AnchoredAtom2503 Fin15AnchoredAtom2504 Fin15AnchoredAtom2506
    Fin15AnchoredAtom2522 Fin15AnchoredAtom2524 Fin15AnchoredAtom2526 Fin15AnchoredAtom2571
    Fin15AnchoredAtom2573 Fin15AnchoredAtom2575 Fin15AnchoredAtom2609 Fin15AnchoredAtom2655
    Fin15AnchoredAtom2657 Fin15AnchoredAtom2659 Fin15AnchoredAtom2693 Fin15AnchoredAtom2784
    Fin15AnchoredAtom3218 Fin15AnchoredAtom3219 Fin15AnchoredAtom3221 Fin15AnchoredAtom3237
    Fin15AnchoredAtom3239 Fin15AnchoredAtom3241 Fin15AnchoredAtom3286 Fin15AnchoredAtom3288
    Fin15AnchoredAtom3290 Fin15AnchoredAtom3324 Fin15AnchoredAtom3370 Fin15AnchoredAtom3372
    Fin15AnchoredAtom3374 Fin15AnchoredAtom3408 Fin15AnchoredAtom3499 Fin15AnchoredAtom4405
    Fin15AnchoredAtom4407 Fin15AnchoredAtom4409 Fin15AnchoredAtom4443 Fin15AnchoredAtom4534
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

theorem fin15Anchored_clause31004 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom1984 chi ∧
      ¬Fin15AnchoredAtom1985 chi ∧
      ¬Fin15AnchoredAtom1986 chi ∧
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
      ¬Fin15AnchoredAtom2504 chi ∧
      ¬Fin15AnchoredAtom2505 chi ∧
      ¬Fin15AnchoredAtom2506 chi ∧
      ¬Fin15AnchoredAtom2525 chi ∧
      ¬Fin15AnchoredAtom2526 chi ∧
      ¬Fin15AnchoredAtom2527 chi ∧
      ¬Fin15AnchoredAtom2574 chi ∧
      ¬Fin15AnchoredAtom2575 chi ∧
      ¬Fin15AnchoredAtom2576 chi ∧
      ¬Fin15AnchoredAtom2611 chi ∧
      ¬Fin15AnchoredAtom2658 chi ∧
      ¬Fin15AnchoredAtom2659 chi ∧
      ¬Fin15AnchoredAtom2660 chi ∧
      ¬Fin15AnchoredAtom2695 chi ∧
      ¬Fin15AnchoredAtom2786 chi ∧
      ¬Fin15AnchoredAtom3219 chi ∧
      ¬Fin15AnchoredAtom3220 chi ∧
      ¬Fin15AnchoredAtom3221 chi ∧
      ¬Fin15AnchoredAtom3240 chi ∧
      ¬Fin15AnchoredAtom3241 chi ∧
      ¬Fin15AnchoredAtom3242 chi ∧
      ¬Fin15AnchoredAtom3289 chi ∧
      ¬Fin15AnchoredAtom3290 chi ∧
      ¬Fin15AnchoredAtom3291 chi ∧
      ¬Fin15AnchoredAtom3326 chi ∧
      ¬Fin15AnchoredAtom3373 chi ∧
      ¬Fin15AnchoredAtom3374 chi ∧
      ¬Fin15AnchoredAtom3375 chi ∧
      ¬Fin15AnchoredAtom3410 chi ∧
      ¬Fin15AnchoredAtom3501 chi ∧
      ¬Fin15AnchoredAtom4408 chi ∧
      ¬Fin15AnchoredAtom4409 chi ∧
      ¬Fin15AnchoredAtom4410 chi ∧
      ¬Fin15AnchoredAtom4445 chi ∧
      ¬Fin15AnchoredAtom4536 chi ∧
      ¬Fin15AnchoredAtom4662 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 5, 7, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask28851
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1943 Fin15AnchoredAtom1948 Fin15AnchoredAtom1949
    Fin15AnchoredAtom1950 Fin15AnchoredAtom1963 Fin15AnchoredAtom1964 Fin15AnchoredAtom1965
    Fin15AnchoredAtom1984 Fin15AnchoredAtom1985 Fin15AnchoredAtom1986 Fin15AnchoredAtom1999
    Fin15AnchoredAtom2000 Fin15AnchoredAtom2001 Fin15AnchoredAtom2020 Fin15AnchoredAtom2021
    Fin15AnchoredAtom2022 Fin15AnchoredAtom2069 Fin15AnchoredAtom2070 Fin15AnchoredAtom2071
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2504 Fin15AnchoredAtom2505 Fin15AnchoredAtom2506
    Fin15AnchoredAtom2525 Fin15AnchoredAtom2526 Fin15AnchoredAtom2527 Fin15AnchoredAtom2574
    Fin15AnchoredAtom2575 Fin15AnchoredAtom2576 Fin15AnchoredAtom2611 Fin15AnchoredAtom2658
    Fin15AnchoredAtom2659 Fin15AnchoredAtom2660 Fin15AnchoredAtom2695 Fin15AnchoredAtom2786
    Fin15AnchoredAtom3219 Fin15AnchoredAtom3220 Fin15AnchoredAtom3221 Fin15AnchoredAtom3240
    Fin15AnchoredAtom3241 Fin15AnchoredAtom3242 Fin15AnchoredAtom3289 Fin15AnchoredAtom3290
    Fin15AnchoredAtom3291 Fin15AnchoredAtom3326 Fin15AnchoredAtom3373 Fin15AnchoredAtom3374
    Fin15AnchoredAtom3375 Fin15AnchoredAtom3410 Fin15AnchoredAtom3501 Fin15AnchoredAtom4408
    Fin15AnchoredAtom4409 Fin15AnchoredAtom4410 Fin15AnchoredAtom4445 Fin15AnchoredAtom4536
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

theorem fin15Anchored_clause31005 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1944 chi ∧
      ¬Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom1966 chi ∧
      ¬Fin15AnchoredAtom1967 chi ∧
      ¬Fin15AnchoredAtom1970 chi ∧
      ¬Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom1979 chi ∧
      ¬Fin15AnchoredAtom2002 chi ∧
      ¬Fin15AnchoredAtom2003 chi ∧
      ¬Fin15AnchoredAtom2006 chi ∧
      ¬Fin15AnchoredAtom2008 chi ∧
      ¬Fin15AnchoredAtom2011 chi ∧
      ¬Fin15AnchoredAtom2015 chi ∧
      ¬Fin15AnchoredAtom2072 chi ∧
      ¬Fin15AnchoredAtom2075 chi ∧
      ¬Fin15AnchoredAtom2079 chi ∧
      ¬Fin15AnchoredAtom2089 chi ∧
      ¬Fin15AnchoredAtom2507 chi ∧
      ¬Fin15AnchoredAtom2508 chi ∧
      ¬Fin15AnchoredAtom2511 chi ∧
      ¬Fin15AnchoredAtom2513 chi ∧
      ¬Fin15AnchoredAtom2516 chi ∧
      ¬Fin15AnchoredAtom2520 chi ∧
      ¬Fin15AnchoredAtom2577 chi ∧
      ¬Fin15AnchoredAtom2580 chi ∧
      ¬Fin15AnchoredAtom2584 chi ∧
      ¬Fin15AnchoredAtom2594 chi ∧
      ¬Fin15AnchoredAtom2661 chi ∧
      ¬Fin15AnchoredAtom2664 chi ∧
      ¬Fin15AnchoredAtom2668 chi ∧
      ¬Fin15AnchoredAtom2678 chi ∧
      ¬Fin15AnchoredAtom2789 chi ∧
      ¬Fin15AnchoredAtom3222 chi ∧
      ¬Fin15AnchoredAtom3223 chi ∧
      ¬Fin15AnchoredAtom3226 chi ∧
      ¬Fin15AnchoredAtom3228 chi ∧
      ¬Fin15AnchoredAtom3231 chi ∧
      ¬Fin15AnchoredAtom3235 chi ∧
      ¬Fin15AnchoredAtom3292 chi ∧
      ¬Fin15AnchoredAtom3295 chi ∧
      ¬Fin15AnchoredAtom3299 chi ∧
      ¬Fin15AnchoredAtom3309 chi ∧
      ¬Fin15AnchoredAtom3376 chi ∧
      ¬Fin15AnchoredAtom3379 chi ∧
      ¬Fin15AnchoredAtom3383 chi ∧
      ¬Fin15AnchoredAtom3393 chi ∧
      ¬Fin15AnchoredAtom3504 chi ∧
      ¬Fin15AnchoredAtom4411 chi ∧
      ¬Fin15AnchoredAtom4414 chi ∧
      ¬Fin15AnchoredAtom4418 chi ∧
      ¬Fin15AnchoredAtom4428 chi ∧
      ¬Fin15AnchoredAtom4539 chi ∧
      ¬Fin15AnchoredAtom4665 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 5, 8, 9, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask10035
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1944 Fin15AnchoredAtom1945 Fin15AnchoredAtom1946
    Fin15AnchoredAtom1949 Fin15AnchoredAtom1966 Fin15AnchoredAtom1967 Fin15AnchoredAtom1970
    Fin15AnchoredAtom1972 Fin15AnchoredAtom1975 Fin15AnchoredAtom1979 Fin15AnchoredAtom2002
    Fin15AnchoredAtom2003 Fin15AnchoredAtom2006 Fin15AnchoredAtom2008 Fin15AnchoredAtom2011
    Fin15AnchoredAtom2015 Fin15AnchoredAtom2072 Fin15AnchoredAtom2075 Fin15AnchoredAtom2079
    Fin15AnchoredAtom2089 Fin15AnchoredAtom2507 Fin15AnchoredAtom2508 Fin15AnchoredAtom2511
    Fin15AnchoredAtom2513 Fin15AnchoredAtom2516 Fin15AnchoredAtom2520 Fin15AnchoredAtom2577
    Fin15AnchoredAtom2580 Fin15AnchoredAtom2584 Fin15AnchoredAtom2594 Fin15AnchoredAtom2661
    Fin15AnchoredAtom2664 Fin15AnchoredAtom2668 Fin15AnchoredAtom2678 Fin15AnchoredAtom2789
    Fin15AnchoredAtom3222 Fin15AnchoredAtom3223 Fin15AnchoredAtom3226 Fin15AnchoredAtom3228
    Fin15AnchoredAtom3231 Fin15AnchoredAtom3235 Fin15AnchoredAtom3292 Fin15AnchoredAtom3295
    Fin15AnchoredAtom3299 Fin15AnchoredAtom3309 Fin15AnchoredAtom3376 Fin15AnchoredAtom3379
    Fin15AnchoredAtom3383 Fin15AnchoredAtom3393 Fin15AnchoredAtom3504 Fin15AnchoredAtom4411
    Fin15AnchoredAtom4414 Fin15AnchoredAtom4418 Fin15AnchoredAtom4428 Fin15AnchoredAtom4539
    Fin15AnchoredAtom4665 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31006 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1944 chi ∧
      ¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom1967 chi ∧
      ¬Fin15AnchoredAtom1969 chi ∧
      ¬Fin15AnchoredAtom1970 chi ∧
      ¬Fin15AnchoredAtom1978 chi ∧
      ¬Fin15AnchoredAtom1979 chi ∧
      ¬Fin15AnchoredAtom1984 chi ∧
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
      ¬Fin15AnchoredAtom2508 chi ∧
      ¬Fin15AnchoredAtom2510 chi ∧
      ¬Fin15AnchoredAtom2511 chi ∧
      ¬Fin15AnchoredAtom2519 chi ∧
      ¬Fin15AnchoredAtom2520 chi ∧
      ¬Fin15AnchoredAtom2525 chi ∧
      ¬Fin15AnchoredAtom2583 chi ∧
      ¬Fin15AnchoredAtom2584 chi ∧
      ¬Fin15AnchoredAtom2589 chi ∧
      ¬Fin15AnchoredAtom2605 chi ∧
      ¬Fin15AnchoredAtom2667 chi ∧
      ¬Fin15AnchoredAtom2668 chi ∧
      ¬Fin15AnchoredAtom2673 chi ∧
      ¬Fin15AnchoredAtom2689 chi ∧
      ¬Fin15AnchoredAtom2800 chi ∧
      ¬Fin15AnchoredAtom3223 chi ∧
      ¬Fin15AnchoredAtom3225 chi ∧
      ¬Fin15AnchoredAtom3226 chi ∧
      ¬Fin15AnchoredAtom3234 chi ∧
      ¬Fin15AnchoredAtom3235 chi ∧
      ¬Fin15AnchoredAtom3240 chi ∧
      ¬Fin15AnchoredAtom3298 chi ∧
      ¬Fin15AnchoredAtom3299 chi ∧
      ¬Fin15AnchoredAtom3304 chi ∧
      ¬Fin15AnchoredAtom3320 chi ∧
      ¬Fin15AnchoredAtom3382 chi ∧
      ¬Fin15AnchoredAtom3383 chi ∧
      ¬Fin15AnchoredAtom3388 chi ∧
      ¬Fin15AnchoredAtom3404 chi ∧
      ¬Fin15AnchoredAtom3515 chi ∧
      ¬Fin15AnchoredAtom4417 chi ∧
      ¬Fin15AnchoredAtom4418 chi ∧
      ¬Fin15AnchoredAtom4423 chi ∧
      ¬Fin15AnchoredAtom4439 chi ∧
      ¬Fin15AnchoredAtom4550 chi ∧
      ¬Fin15AnchoredAtom4676 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 5, 8, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13619
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1944 Fin15AnchoredAtom1946 Fin15AnchoredAtom1948
    Fin15AnchoredAtom1949 Fin15AnchoredAtom1967 Fin15AnchoredAtom1969 Fin15AnchoredAtom1970
    Fin15AnchoredAtom1978 Fin15AnchoredAtom1979 Fin15AnchoredAtom1984 Fin15AnchoredAtom2003
    Fin15AnchoredAtom2005 Fin15AnchoredAtom2006 Fin15AnchoredAtom2014 Fin15AnchoredAtom2015
    Fin15AnchoredAtom2020 Fin15AnchoredAtom2078 Fin15AnchoredAtom2079 Fin15AnchoredAtom2084
    Fin15AnchoredAtom2100 Fin15AnchoredAtom2508 Fin15AnchoredAtom2510 Fin15AnchoredAtom2511
    Fin15AnchoredAtom2519 Fin15AnchoredAtom2520 Fin15AnchoredAtom2525 Fin15AnchoredAtom2583
    Fin15AnchoredAtom2584 Fin15AnchoredAtom2589 Fin15AnchoredAtom2605 Fin15AnchoredAtom2667
    Fin15AnchoredAtom2668 Fin15AnchoredAtom2673 Fin15AnchoredAtom2689 Fin15AnchoredAtom2800
    Fin15AnchoredAtom3223 Fin15AnchoredAtom3225 Fin15AnchoredAtom3226 Fin15AnchoredAtom3234
    Fin15AnchoredAtom3235 Fin15AnchoredAtom3240 Fin15AnchoredAtom3298 Fin15AnchoredAtom3299
    Fin15AnchoredAtom3304 Fin15AnchoredAtom3320 Fin15AnchoredAtom3382 Fin15AnchoredAtom3383
    Fin15AnchoredAtom3388 Fin15AnchoredAtom3404 Fin15AnchoredAtom3515 Fin15AnchoredAtom4417
    Fin15AnchoredAtom4418 Fin15AnchoredAtom4423 Fin15AnchoredAtom4439 Fin15AnchoredAtom4550
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

theorem fin15Anchored_clause31007 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1944 chi ∧
      ¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom1967 chi ∧
      ¬Fin15AnchoredAtom1970 chi ∧
      ¬Fin15AnchoredAtom1971 chi ∧
      ¬Fin15AnchoredAtom1979 chi ∧
      ¬Fin15AnchoredAtom1980 chi ∧
      ¬Fin15AnchoredAtom1986 chi ∧
      ¬Fin15AnchoredAtom2003 chi ∧
      ¬Fin15AnchoredAtom2006 chi ∧
      ¬Fin15AnchoredAtom2007 chi ∧
      ¬Fin15AnchoredAtom2015 chi ∧
      ¬Fin15AnchoredAtom2016 chi ∧
      ¬Fin15AnchoredAtom2022 chi ∧
      ¬Fin15AnchoredAtom2079 chi ∧
      ¬Fin15AnchoredAtom2080 chi ∧
      ¬Fin15AnchoredAtom2086 chi ∧
      ¬Fin15AnchoredAtom2102 chi ∧
      ¬Fin15AnchoredAtom2508 chi ∧
      ¬Fin15AnchoredAtom2511 chi ∧
      ¬Fin15AnchoredAtom2512 chi ∧
      ¬Fin15AnchoredAtom2520 chi ∧
      ¬Fin15AnchoredAtom2521 chi ∧
      ¬Fin15AnchoredAtom2527 chi ∧
      ¬Fin15AnchoredAtom2584 chi ∧
      ¬Fin15AnchoredAtom2585 chi ∧
      ¬Fin15AnchoredAtom2591 chi ∧
      ¬Fin15AnchoredAtom2607 chi ∧
      ¬Fin15AnchoredAtom2668 chi ∧
      ¬Fin15AnchoredAtom2669 chi ∧
      ¬Fin15AnchoredAtom2675 chi ∧
      ¬Fin15AnchoredAtom2691 chi ∧
      ¬Fin15AnchoredAtom2802 chi ∧
      ¬Fin15AnchoredAtom3223 chi ∧
      ¬Fin15AnchoredAtom3226 chi ∧
      ¬Fin15AnchoredAtom3227 chi ∧
      ¬Fin15AnchoredAtom3235 chi ∧
      ¬Fin15AnchoredAtom3236 chi ∧
      ¬Fin15AnchoredAtom3242 chi ∧
      ¬Fin15AnchoredAtom3299 chi ∧
      ¬Fin15AnchoredAtom3300 chi ∧
      ¬Fin15AnchoredAtom3306 chi ∧
      ¬Fin15AnchoredAtom3322 chi ∧
      ¬Fin15AnchoredAtom3383 chi ∧
      ¬Fin15AnchoredAtom3384 chi ∧
      ¬Fin15AnchoredAtom3390 chi ∧
      ¬Fin15AnchoredAtom3406 chi ∧
      ¬Fin15AnchoredAtom3517 chi ∧
      ¬Fin15AnchoredAtom4418 chi ∧
      ¬Fin15AnchoredAtom4419 chi ∧
      ¬Fin15AnchoredAtom4425 chi ∧
      ¬Fin15AnchoredAtom4441 chi ∧
      ¬Fin15AnchoredAtom4552 chi ∧
      ¬Fin15AnchoredAtom4678 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 5, 8, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25907
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1944 Fin15AnchoredAtom1946 Fin15AnchoredAtom1949
    Fin15AnchoredAtom1950 Fin15AnchoredAtom1967 Fin15AnchoredAtom1970 Fin15AnchoredAtom1971
    Fin15AnchoredAtom1979 Fin15AnchoredAtom1980 Fin15AnchoredAtom1986 Fin15AnchoredAtom2003
    Fin15AnchoredAtom2006 Fin15AnchoredAtom2007 Fin15AnchoredAtom2015 Fin15AnchoredAtom2016
    Fin15AnchoredAtom2022 Fin15AnchoredAtom2079 Fin15AnchoredAtom2080 Fin15AnchoredAtom2086
    Fin15AnchoredAtom2102 Fin15AnchoredAtom2508 Fin15AnchoredAtom2511 Fin15AnchoredAtom2512
    Fin15AnchoredAtom2520 Fin15AnchoredAtom2521 Fin15AnchoredAtom2527 Fin15AnchoredAtom2584
    Fin15AnchoredAtom2585 Fin15AnchoredAtom2591 Fin15AnchoredAtom2607 Fin15AnchoredAtom2668
    Fin15AnchoredAtom2669 Fin15AnchoredAtom2675 Fin15AnchoredAtom2691 Fin15AnchoredAtom2802
    Fin15AnchoredAtom3223 Fin15AnchoredAtom3226 Fin15AnchoredAtom3227 Fin15AnchoredAtom3235
    Fin15AnchoredAtom3236 Fin15AnchoredAtom3242 Fin15AnchoredAtom3299 Fin15AnchoredAtom3300
    Fin15AnchoredAtom3306 Fin15AnchoredAtom3322 Fin15AnchoredAtom3383 Fin15AnchoredAtom3384
    Fin15AnchoredAtom3390 Fin15AnchoredAtom3406 Fin15AnchoredAtom3517 Fin15AnchoredAtom4418
    Fin15AnchoredAtom4419 Fin15AnchoredAtom4425 Fin15AnchoredAtom4441 Fin15AnchoredAtom4552
    Fin15AnchoredAtom4678 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31008 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom1978 chi ∧
      ¬Fin15AnchoredAtom1979 chi ∧
      ¬Fin15AnchoredAtom1984 chi ∧
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
      ¬Fin15AnchoredAtom2513 chi ∧
      ¬Fin15AnchoredAtom2515 chi ∧
      ¬Fin15AnchoredAtom2516 chi ∧
      ¬Fin15AnchoredAtom2519 chi ∧
      ¬Fin15AnchoredAtom2520 chi ∧
      ¬Fin15AnchoredAtom2525 chi ∧
      ¬Fin15AnchoredAtom2593 chi ∧
      ¬Fin15AnchoredAtom2594 chi ∧
      ¬Fin15AnchoredAtom2599 chi ∧
      ¬Fin15AnchoredAtom2605 chi ∧
      ¬Fin15AnchoredAtom2677 chi ∧
      ¬Fin15AnchoredAtom2678 chi ∧
      ¬Fin15AnchoredAtom2683 chi ∧
      ¬Fin15AnchoredAtom2689 chi ∧
      ¬Fin15AnchoredAtom2810 chi ∧
      ¬Fin15AnchoredAtom3228 chi ∧
      ¬Fin15AnchoredAtom3230 chi ∧
      ¬Fin15AnchoredAtom3231 chi ∧
      ¬Fin15AnchoredAtom3234 chi ∧
      ¬Fin15AnchoredAtom3235 chi ∧
      ¬Fin15AnchoredAtom3240 chi ∧
      ¬Fin15AnchoredAtom3308 chi ∧
      ¬Fin15AnchoredAtom3309 chi ∧
      ¬Fin15AnchoredAtom3314 chi ∧
      ¬Fin15AnchoredAtom3320 chi ∧
      ¬Fin15AnchoredAtom3392 chi ∧
      ¬Fin15AnchoredAtom3393 chi ∧
      ¬Fin15AnchoredAtom3398 chi ∧
      ¬Fin15AnchoredAtom3404 chi ∧
      ¬Fin15AnchoredAtom3525 chi ∧
      ¬Fin15AnchoredAtom4427 chi ∧
      ¬Fin15AnchoredAtom4428 chi ∧
      ¬Fin15AnchoredAtom4433 chi ∧
      ¬Fin15AnchoredAtom4439 chi ∧
      ¬Fin15AnchoredAtom4560 chi ∧
      ¬Fin15AnchoredAtom4686 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 5, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13875
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1945 Fin15AnchoredAtom1946 Fin15AnchoredAtom1948
    Fin15AnchoredAtom1949 Fin15AnchoredAtom1972 Fin15AnchoredAtom1974 Fin15AnchoredAtom1975
    Fin15AnchoredAtom1978 Fin15AnchoredAtom1979 Fin15AnchoredAtom1984 Fin15AnchoredAtom2008
    Fin15AnchoredAtom2010 Fin15AnchoredAtom2011 Fin15AnchoredAtom2014 Fin15AnchoredAtom2015
    Fin15AnchoredAtom2020 Fin15AnchoredAtom2088 Fin15AnchoredAtom2089 Fin15AnchoredAtom2094
    Fin15AnchoredAtom2100 Fin15AnchoredAtom2513 Fin15AnchoredAtom2515 Fin15AnchoredAtom2516
    Fin15AnchoredAtom2519 Fin15AnchoredAtom2520 Fin15AnchoredAtom2525 Fin15AnchoredAtom2593
    Fin15AnchoredAtom2594 Fin15AnchoredAtom2599 Fin15AnchoredAtom2605 Fin15AnchoredAtom2677
    Fin15AnchoredAtom2678 Fin15AnchoredAtom2683 Fin15AnchoredAtom2689 Fin15AnchoredAtom2810
    Fin15AnchoredAtom3228 Fin15AnchoredAtom3230 Fin15AnchoredAtom3231 Fin15AnchoredAtom3234
    Fin15AnchoredAtom3235 Fin15AnchoredAtom3240 Fin15AnchoredAtom3308 Fin15AnchoredAtom3309
    Fin15AnchoredAtom3314 Fin15AnchoredAtom3320 Fin15AnchoredAtom3392 Fin15AnchoredAtom3393
    Fin15AnchoredAtom3398 Fin15AnchoredAtom3404 Fin15AnchoredAtom3525 Fin15AnchoredAtom4427
    Fin15AnchoredAtom4428 Fin15AnchoredAtom4433 Fin15AnchoredAtom4439 Fin15AnchoredAtom4560
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

theorem fin15Anchored_clause31009 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom1976 chi ∧
      ¬Fin15AnchoredAtom1978 chi ∧
      ¬Fin15AnchoredAtom1980 chi ∧
      ¬Fin15AnchoredAtom1985 chi ∧
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
      ¬Fin15AnchoredAtom2513 chi ∧
      ¬Fin15AnchoredAtom2515 chi ∧
      ¬Fin15AnchoredAtom2517 chi ∧
      ¬Fin15AnchoredAtom2519 chi ∧
      ¬Fin15AnchoredAtom2521 chi ∧
      ¬Fin15AnchoredAtom2526 chi ∧
      ¬Fin15AnchoredAtom2593 chi ∧
      ¬Fin15AnchoredAtom2595 chi ∧
      ¬Fin15AnchoredAtom2600 chi ∧
      ¬Fin15AnchoredAtom2606 chi ∧
      ¬Fin15AnchoredAtom2677 chi ∧
      ¬Fin15AnchoredAtom2679 chi ∧
      ¬Fin15AnchoredAtom2684 chi ∧
      ¬Fin15AnchoredAtom2690 chi ∧
      ¬Fin15AnchoredAtom2811 chi ∧
      ¬Fin15AnchoredAtom3228 chi ∧
      ¬Fin15AnchoredAtom3230 chi ∧
      ¬Fin15AnchoredAtom3232 chi ∧
      ¬Fin15AnchoredAtom3234 chi ∧
      ¬Fin15AnchoredAtom3236 chi ∧
      ¬Fin15AnchoredAtom3241 chi ∧
      ¬Fin15AnchoredAtom3308 chi ∧
      ¬Fin15AnchoredAtom3310 chi ∧
      ¬Fin15AnchoredAtom3315 chi ∧
      ¬Fin15AnchoredAtom3321 chi ∧
      ¬Fin15AnchoredAtom3392 chi ∧
      ¬Fin15AnchoredAtom3394 chi ∧
      ¬Fin15AnchoredAtom3399 chi ∧
      ¬Fin15AnchoredAtom3405 chi ∧
      ¬Fin15AnchoredAtom3526 chi ∧
      ¬Fin15AnchoredAtom4427 chi ∧
      ¬Fin15AnchoredAtom4429 chi ∧
      ¬Fin15AnchoredAtom4434 chi ∧
      ¬Fin15AnchoredAtom4440 chi ∧
      ¬Fin15AnchoredAtom4561 chi ∧
      ¬Fin15AnchoredAtom4687 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 5, 9, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22067
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1945 Fin15AnchoredAtom1946 Fin15AnchoredAtom1948
    Fin15AnchoredAtom1950 Fin15AnchoredAtom1972 Fin15AnchoredAtom1974 Fin15AnchoredAtom1976
    Fin15AnchoredAtom1978 Fin15AnchoredAtom1980 Fin15AnchoredAtom1985 Fin15AnchoredAtom2008
    Fin15AnchoredAtom2010 Fin15AnchoredAtom2012 Fin15AnchoredAtom2014 Fin15AnchoredAtom2016
    Fin15AnchoredAtom2021 Fin15AnchoredAtom2088 Fin15AnchoredAtom2090 Fin15AnchoredAtom2095
    Fin15AnchoredAtom2101 Fin15AnchoredAtom2513 Fin15AnchoredAtom2515 Fin15AnchoredAtom2517
    Fin15AnchoredAtom2519 Fin15AnchoredAtom2521 Fin15AnchoredAtom2526 Fin15AnchoredAtom2593
    Fin15AnchoredAtom2595 Fin15AnchoredAtom2600 Fin15AnchoredAtom2606 Fin15AnchoredAtom2677
    Fin15AnchoredAtom2679 Fin15AnchoredAtom2684 Fin15AnchoredAtom2690 Fin15AnchoredAtom2811
    Fin15AnchoredAtom3228 Fin15AnchoredAtom3230 Fin15AnchoredAtom3232 Fin15AnchoredAtom3234
    Fin15AnchoredAtom3236 Fin15AnchoredAtom3241 Fin15AnchoredAtom3308 Fin15AnchoredAtom3310
    Fin15AnchoredAtom3315 Fin15AnchoredAtom3321 Fin15AnchoredAtom3392 Fin15AnchoredAtom3394
    Fin15AnchoredAtom3399 Fin15AnchoredAtom3405 Fin15AnchoredAtom3526 Fin15AnchoredAtom4427
    Fin15AnchoredAtom4429 Fin15AnchoredAtom4434 Fin15AnchoredAtom4440 Fin15AnchoredAtom4561
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

theorem fin15Anchored_clause31010 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom1976 chi ∧
      ¬Fin15AnchoredAtom1979 chi ∧
      ¬Fin15AnchoredAtom1980 chi ∧
      ¬Fin15AnchoredAtom1986 chi ∧
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
      ¬Fin15AnchoredAtom2513 chi ∧
      ¬Fin15AnchoredAtom2516 chi ∧
      ¬Fin15AnchoredAtom2517 chi ∧
      ¬Fin15AnchoredAtom2520 chi ∧
      ¬Fin15AnchoredAtom2521 chi ∧
      ¬Fin15AnchoredAtom2527 chi ∧
      ¬Fin15AnchoredAtom2594 chi ∧
      ¬Fin15AnchoredAtom2595 chi ∧
      ¬Fin15AnchoredAtom2601 chi ∧
      ¬Fin15AnchoredAtom2607 chi ∧
      ¬Fin15AnchoredAtom2678 chi ∧
      ¬Fin15AnchoredAtom2679 chi ∧
      ¬Fin15AnchoredAtom2685 chi ∧
      ¬Fin15AnchoredAtom2691 chi ∧
      ¬Fin15AnchoredAtom2812 chi ∧
      ¬Fin15AnchoredAtom3228 chi ∧
      ¬Fin15AnchoredAtom3231 chi ∧
      ¬Fin15AnchoredAtom3232 chi ∧
      ¬Fin15AnchoredAtom3235 chi ∧
      ¬Fin15AnchoredAtom3236 chi ∧
      ¬Fin15AnchoredAtom3242 chi ∧
      ¬Fin15AnchoredAtom3309 chi ∧
      ¬Fin15AnchoredAtom3310 chi ∧
      ¬Fin15AnchoredAtom3316 chi ∧
      ¬Fin15AnchoredAtom3322 chi ∧
      ¬Fin15AnchoredAtom3393 chi ∧
      ¬Fin15AnchoredAtom3394 chi ∧
      ¬Fin15AnchoredAtom3400 chi ∧
      ¬Fin15AnchoredAtom3406 chi ∧
      ¬Fin15AnchoredAtom3527 chi ∧
      ¬Fin15AnchoredAtom4428 chi ∧
      ¬Fin15AnchoredAtom4429 chi ∧
      ¬Fin15AnchoredAtom4435 chi ∧
      ¬Fin15AnchoredAtom4441 chi ∧
      ¬Fin15AnchoredAtom4562 chi ∧
      ¬Fin15AnchoredAtom4688 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 5, 9, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26163
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1945 Fin15AnchoredAtom1946 Fin15AnchoredAtom1949
    Fin15AnchoredAtom1950 Fin15AnchoredAtom1972 Fin15AnchoredAtom1975 Fin15AnchoredAtom1976
    Fin15AnchoredAtom1979 Fin15AnchoredAtom1980 Fin15AnchoredAtom1986 Fin15AnchoredAtom2008
    Fin15AnchoredAtom2011 Fin15AnchoredAtom2012 Fin15AnchoredAtom2015 Fin15AnchoredAtom2016
    Fin15AnchoredAtom2022 Fin15AnchoredAtom2089 Fin15AnchoredAtom2090 Fin15AnchoredAtom2096
    Fin15AnchoredAtom2102 Fin15AnchoredAtom2513 Fin15AnchoredAtom2516 Fin15AnchoredAtom2517
    Fin15AnchoredAtom2520 Fin15AnchoredAtom2521 Fin15AnchoredAtom2527 Fin15AnchoredAtom2594
    Fin15AnchoredAtom2595 Fin15AnchoredAtom2601 Fin15AnchoredAtom2607 Fin15AnchoredAtom2678
    Fin15AnchoredAtom2679 Fin15AnchoredAtom2685 Fin15AnchoredAtom2691 Fin15AnchoredAtom2812
    Fin15AnchoredAtom3228 Fin15AnchoredAtom3231 Fin15AnchoredAtom3232 Fin15AnchoredAtom3235
    Fin15AnchoredAtom3236 Fin15AnchoredAtom3242 Fin15AnchoredAtom3309 Fin15AnchoredAtom3310
    Fin15AnchoredAtom3316 Fin15AnchoredAtom3322 Fin15AnchoredAtom3393 Fin15AnchoredAtom3394
    Fin15AnchoredAtom3400 Fin15AnchoredAtom3406 Fin15AnchoredAtom3527 Fin15AnchoredAtom4428
    Fin15AnchoredAtom4429 Fin15AnchoredAtom4435 Fin15AnchoredAtom4441 Fin15AnchoredAtom4562
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

theorem fin15Anchored_clause31011 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom1947 chi ∧
      ¬Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom1973 chi ∧
      ¬Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom1976 chi ∧
      ¬Fin15AnchoredAtom1981 chi ∧
      ¬Fin15AnchoredAtom1983 chi ∧
      ¬Fin15AnchoredAtom1985 chi ∧
      ¬Fin15AnchoredAtom2009 chi ∧
      ¬Fin15AnchoredAtom2010 chi ∧
      ¬Fin15AnchoredAtom2012 chi ∧
      ¬Fin15AnchoredAtom2017 chi ∧
      ¬Fin15AnchoredAtom2019 chi ∧
      ¬Fin15AnchoredAtom2021 chi ∧
      ¬Fin15AnchoredAtom2091 chi ∧
      ¬Fin15AnchoredAtom2093 chi ∧
      ¬Fin15AnchoredAtom2095 chi ∧
      ¬Fin15AnchoredAtom2104 chi ∧
      ¬Fin15AnchoredAtom2514 chi ∧
      ¬Fin15AnchoredAtom2515 chi ∧
      ¬Fin15AnchoredAtom2517 chi ∧
      ¬Fin15AnchoredAtom2522 chi ∧
      ¬Fin15AnchoredAtom2524 chi ∧
      ¬Fin15AnchoredAtom2526 chi ∧
      ¬Fin15AnchoredAtom2596 chi ∧
      ¬Fin15AnchoredAtom2598 chi ∧
      ¬Fin15AnchoredAtom2600 chi ∧
      ¬Fin15AnchoredAtom2609 chi ∧
      ¬Fin15AnchoredAtom2680 chi ∧
      ¬Fin15AnchoredAtom2682 chi ∧
      ¬Fin15AnchoredAtom2684 chi ∧
      ¬Fin15AnchoredAtom2693 chi ∧
      ¬Fin15AnchoredAtom2814 chi ∧
      ¬Fin15AnchoredAtom3229 chi ∧
      ¬Fin15AnchoredAtom3230 chi ∧
      ¬Fin15AnchoredAtom3232 chi ∧
      ¬Fin15AnchoredAtom3237 chi ∧
      ¬Fin15AnchoredAtom3239 chi ∧
      ¬Fin15AnchoredAtom3241 chi ∧
      ¬Fin15AnchoredAtom3311 chi ∧
      ¬Fin15AnchoredAtom3313 chi ∧
      ¬Fin15AnchoredAtom3315 chi ∧
      ¬Fin15AnchoredAtom3324 chi ∧
      ¬Fin15AnchoredAtom3395 chi ∧
      ¬Fin15AnchoredAtom3397 chi ∧
      ¬Fin15AnchoredAtom3399 chi ∧
      ¬Fin15AnchoredAtom3408 chi ∧
      ¬Fin15AnchoredAtom3529 chi ∧
      ¬Fin15AnchoredAtom4430 chi ∧
      ¬Fin15AnchoredAtom4432 chi ∧
      ¬Fin15AnchoredAtom4434 chi ∧
      ¬Fin15AnchoredAtom4443 chi ∧
      ¬Fin15AnchoredAtom4564 chi ∧
      ¬Fin15AnchoredAtom4690 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 5, 9, 11, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask23091
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1945 Fin15AnchoredAtom1947 Fin15AnchoredAtom1948
    Fin15AnchoredAtom1950 Fin15AnchoredAtom1973 Fin15AnchoredAtom1974 Fin15AnchoredAtom1976
    Fin15AnchoredAtom1981 Fin15AnchoredAtom1983 Fin15AnchoredAtom1985 Fin15AnchoredAtom2009
    Fin15AnchoredAtom2010 Fin15AnchoredAtom2012 Fin15AnchoredAtom2017 Fin15AnchoredAtom2019
    Fin15AnchoredAtom2021 Fin15AnchoredAtom2091 Fin15AnchoredAtom2093 Fin15AnchoredAtom2095
    Fin15AnchoredAtom2104 Fin15AnchoredAtom2514 Fin15AnchoredAtom2515 Fin15AnchoredAtom2517
    Fin15AnchoredAtom2522 Fin15AnchoredAtom2524 Fin15AnchoredAtom2526 Fin15AnchoredAtom2596
    Fin15AnchoredAtom2598 Fin15AnchoredAtom2600 Fin15AnchoredAtom2609 Fin15AnchoredAtom2680
    Fin15AnchoredAtom2682 Fin15AnchoredAtom2684 Fin15AnchoredAtom2693 Fin15AnchoredAtom2814
    Fin15AnchoredAtom3229 Fin15AnchoredAtom3230 Fin15AnchoredAtom3232 Fin15AnchoredAtom3237
    Fin15AnchoredAtom3239 Fin15AnchoredAtom3241 Fin15AnchoredAtom3311 Fin15AnchoredAtom3313
    Fin15AnchoredAtom3315 Fin15AnchoredAtom3324 Fin15AnchoredAtom3395 Fin15AnchoredAtom3397
    Fin15AnchoredAtom3399 Fin15AnchoredAtom3408 Fin15AnchoredAtom3529 Fin15AnchoredAtom4430
    Fin15AnchoredAtom4432 Fin15AnchoredAtom4434 Fin15AnchoredAtom4443 Fin15AnchoredAtom4564
    Fin15AnchoredAtom4690 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31012 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom1976 chi ∧
      ¬Fin15AnchoredAtom1984 chi ∧
      ¬Fin15AnchoredAtom1985 chi ∧
      ¬Fin15AnchoredAtom1986 chi ∧
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
      ¬Fin15AnchoredAtom2515 chi ∧
      ¬Fin15AnchoredAtom2516 chi ∧
      ¬Fin15AnchoredAtom2517 chi ∧
      ¬Fin15AnchoredAtom2525 chi ∧
      ¬Fin15AnchoredAtom2526 chi ∧
      ¬Fin15AnchoredAtom2527 chi ∧
      ¬Fin15AnchoredAtom2599 chi ∧
      ¬Fin15AnchoredAtom2600 chi ∧
      ¬Fin15AnchoredAtom2601 chi ∧
      ¬Fin15AnchoredAtom2611 chi ∧
      ¬Fin15AnchoredAtom2683 chi ∧
      ¬Fin15AnchoredAtom2684 chi ∧
      ¬Fin15AnchoredAtom2685 chi ∧
      ¬Fin15AnchoredAtom2695 chi ∧
      ¬Fin15AnchoredAtom2816 chi ∧
      ¬Fin15AnchoredAtom3230 chi ∧
      ¬Fin15AnchoredAtom3231 chi ∧
      ¬Fin15AnchoredAtom3232 chi ∧
      ¬Fin15AnchoredAtom3240 chi ∧
      ¬Fin15AnchoredAtom3241 chi ∧
      ¬Fin15AnchoredAtom3242 chi ∧
      ¬Fin15AnchoredAtom3314 chi ∧
      ¬Fin15AnchoredAtom3315 chi ∧
      ¬Fin15AnchoredAtom3316 chi ∧
      ¬Fin15AnchoredAtom3326 chi ∧
      ¬Fin15AnchoredAtom3398 chi ∧
      ¬Fin15AnchoredAtom3399 chi ∧
      ¬Fin15AnchoredAtom3400 chi ∧
      ¬Fin15AnchoredAtom3410 chi ∧
      ¬Fin15AnchoredAtom3531 chi ∧
      ¬Fin15AnchoredAtom4433 chi ∧
      ¬Fin15AnchoredAtom4434 chi ∧
      ¬Fin15AnchoredAtom4435 chi ∧
      ¬Fin15AnchoredAtom4445 chi ∧
      ¬Fin15AnchoredAtom4566 chi ∧
      ¬Fin15AnchoredAtom4692 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 5, 9, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29235
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1945 Fin15AnchoredAtom1948 Fin15AnchoredAtom1949
    Fin15AnchoredAtom1950 Fin15AnchoredAtom1974 Fin15AnchoredAtom1975 Fin15AnchoredAtom1976
    Fin15AnchoredAtom1984 Fin15AnchoredAtom1985 Fin15AnchoredAtom1986 Fin15AnchoredAtom2010
    Fin15AnchoredAtom2011 Fin15AnchoredAtom2012 Fin15AnchoredAtom2020 Fin15AnchoredAtom2021
    Fin15AnchoredAtom2022 Fin15AnchoredAtom2094 Fin15AnchoredAtom2095 Fin15AnchoredAtom2096
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2515 Fin15AnchoredAtom2516 Fin15AnchoredAtom2517
    Fin15AnchoredAtom2525 Fin15AnchoredAtom2526 Fin15AnchoredAtom2527 Fin15AnchoredAtom2599
    Fin15AnchoredAtom2600 Fin15AnchoredAtom2601 Fin15AnchoredAtom2611 Fin15AnchoredAtom2683
    Fin15AnchoredAtom2684 Fin15AnchoredAtom2685 Fin15AnchoredAtom2695 Fin15AnchoredAtom2816
    Fin15AnchoredAtom3230 Fin15AnchoredAtom3231 Fin15AnchoredAtom3232 Fin15AnchoredAtom3240
    Fin15AnchoredAtom3241 Fin15AnchoredAtom3242 Fin15AnchoredAtom3314 Fin15AnchoredAtom3315
    Fin15AnchoredAtom3316 Fin15AnchoredAtom3326 Fin15AnchoredAtom3398 Fin15AnchoredAtom3399
    Fin15AnchoredAtom3400 Fin15AnchoredAtom3410 Fin15AnchoredAtom3531 Fin15AnchoredAtom4433
    Fin15AnchoredAtom4434 Fin15AnchoredAtom4435 Fin15AnchoredAtom4445 Fin15AnchoredAtom4566
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

theorem fin15Anchored_clause31013 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom1978 chi ∧
      ¬Fin15AnchoredAtom1979 chi ∧
      ¬Fin15AnchoredAtom1980 chi ∧
      ¬Fin15AnchoredAtom1984 chi ∧
      ¬Fin15AnchoredAtom1985 chi ∧
      ¬Fin15AnchoredAtom1986 chi ∧
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
      ¬Fin15AnchoredAtom2519 chi ∧
      ¬Fin15AnchoredAtom2520 chi ∧
      ¬Fin15AnchoredAtom2521 chi ∧
      ¬Fin15AnchoredAtom2525 chi ∧
      ¬Fin15AnchoredAtom2526 chi ∧
      ¬Fin15AnchoredAtom2527 chi ∧
      ¬Fin15AnchoredAtom2605 chi ∧
      ¬Fin15AnchoredAtom2606 chi ∧
      ¬Fin15AnchoredAtom2607 chi ∧
      ¬Fin15AnchoredAtom2611 chi ∧
      ¬Fin15AnchoredAtom2689 chi ∧
      ¬Fin15AnchoredAtom2690 chi ∧
      ¬Fin15AnchoredAtom2691 chi ∧
      ¬Fin15AnchoredAtom2695 chi ∧
      ¬Fin15AnchoredAtom2820 chi ∧
      ¬Fin15AnchoredAtom3234 chi ∧
      ¬Fin15AnchoredAtom3235 chi ∧
      ¬Fin15AnchoredAtom3236 chi ∧
      ¬Fin15AnchoredAtom3240 chi ∧
      ¬Fin15AnchoredAtom3241 chi ∧
      ¬Fin15AnchoredAtom3242 chi ∧
      ¬Fin15AnchoredAtom3320 chi ∧
      ¬Fin15AnchoredAtom3321 chi ∧
      ¬Fin15AnchoredAtom3322 chi ∧
      ¬Fin15AnchoredAtom3326 chi ∧
      ¬Fin15AnchoredAtom3404 chi ∧
      ¬Fin15AnchoredAtom3405 chi ∧
      ¬Fin15AnchoredAtom3406 chi ∧
      ¬Fin15AnchoredAtom3410 chi ∧
      ¬Fin15AnchoredAtom3535 chi ∧
      ¬Fin15AnchoredAtom4439 chi ∧
      ¬Fin15AnchoredAtom4440 chi ∧
      ¬Fin15AnchoredAtom4441 chi ∧
      ¬Fin15AnchoredAtom4445 chi ∧
      ¬Fin15AnchoredAtom4570 chi ∧
      ¬Fin15AnchoredAtom4696 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 5, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29747
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1946 Fin15AnchoredAtom1948 Fin15AnchoredAtom1949
    Fin15AnchoredAtom1950 Fin15AnchoredAtom1978 Fin15AnchoredAtom1979 Fin15AnchoredAtom1980
    Fin15AnchoredAtom1984 Fin15AnchoredAtom1985 Fin15AnchoredAtom1986 Fin15AnchoredAtom2014
    Fin15AnchoredAtom2015 Fin15AnchoredAtom2016 Fin15AnchoredAtom2020 Fin15AnchoredAtom2021
    Fin15AnchoredAtom2022 Fin15AnchoredAtom2100 Fin15AnchoredAtom2101 Fin15AnchoredAtom2102
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2519 Fin15AnchoredAtom2520 Fin15AnchoredAtom2521
    Fin15AnchoredAtom2525 Fin15AnchoredAtom2526 Fin15AnchoredAtom2527 Fin15AnchoredAtom2605
    Fin15AnchoredAtom2606 Fin15AnchoredAtom2607 Fin15AnchoredAtom2611 Fin15AnchoredAtom2689
    Fin15AnchoredAtom2690 Fin15AnchoredAtom2691 Fin15AnchoredAtom2695 Fin15AnchoredAtom2820
    Fin15AnchoredAtom3234 Fin15AnchoredAtom3235 Fin15AnchoredAtom3236 Fin15AnchoredAtom3240
    Fin15AnchoredAtom3241 Fin15AnchoredAtom3242 Fin15AnchoredAtom3320 Fin15AnchoredAtom3321
    Fin15AnchoredAtom3322 Fin15AnchoredAtom3326 Fin15AnchoredAtom3404 Fin15AnchoredAtom3405
    Fin15AnchoredAtom3406 Fin15AnchoredAtom3410 Fin15AnchoredAtom3535 Fin15AnchoredAtom4439
    Fin15AnchoredAtom4440 Fin15AnchoredAtom4441 Fin15AnchoredAtom4445 Fin15AnchoredAtom4570
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

theorem fin15Anchored_clause31014 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom1952 chi ∧
      ¬Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom1959 chi ∧
      ¬Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom1966 chi ∧
      ¬Fin15AnchoredAtom1967 chi ∧
      ¬Fin15AnchoredAtom1972 chi ∧
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
      ¬Fin15AnchoredAtom2528 chi ∧
      ¬Fin15AnchoredAtom2529 chi ∧
      ¬Fin15AnchoredAtom2530 chi ∧
      ¬Fin15AnchoredAtom2535 chi ∧
      ¬Fin15AnchoredAtom2536 chi ∧
      ¬Fin15AnchoredAtom2541 chi ∧
      ¬Fin15AnchoredAtom2556 chi ∧
      ¬Fin15AnchoredAtom2557 chi ∧
      ¬Fin15AnchoredAtom2562 chi ∧
      ¬Fin15AnchoredAtom2577 chi ∧
      ¬Fin15AnchoredAtom2696 chi ∧
      ¬Fin15AnchoredAtom2697 chi ∧
      ¬Fin15AnchoredAtom2702 chi ∧
      ¬Fin15AnchoredAtom2717 chi ∧
      ¬Fin15AnchoredAtom2752 chi ∧
      ¬Fin15AnchoredAtom3243 chi ∧
      ¬Fin15AnchoredAtom3244 chi ∧
      ¬Fin15AnchoredAtom3245 chi ∧
      ¬Fin15AnchoredAtom3250 chi ∧
      ¬Fin15AnchoredAtom3251 chi ∧
      ¬Fin15AnchoredAtom3256 chi ∧
      ¬Fin15AnchoredAtom3271 chi ∧
      ¬Fin15AnchoredAtom3272 chi ∧
      ¬Fin15AnchoredAtom3277 chi ∧
      ¬Fin15AnchoredAtom3292 chi ∧
      ¬Fin15AnchoredAtom3411 chi ∧
      ¬Fin15AnchoredAtom3412 chi ∧
      ¬Fin15AnchoredAtom3417 chi ∧
      ¬Fin15AnchoredAtom3432 chi ∧
      ¬Fin15AnchoredAtom3467 chi ∧
      ¬Fin15AnchoredAtom4446 chi ∧
      ¬Fin15AnchoredAtom4447 chi ∧
      ¬Fin15AnchoredAtom4452 chi ∧
      ¬Fin15AnchoredAtom4467 chi ∧
      ¬Fin15AnchoredAtom4502 chi ∧
      ¬Fin15AnchoredAtom4698 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 6, 7, 8, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask02003
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1951 Fin15AnchoredAtom1952 Fin15AnchoredAtom1953
    Fin15AnchoredAtom1954 Fin15AnchoredAtom1959 Fin15AnchoredAtom1960 Fin15AnchoredAtom1961
    Fin15AnchoredAtom1966 Fin15AnchoredAtom1967 Fin15AnchoredAtom1972 Fin15AnchoredAtom2023
    Fin15AnchoredAtom2024 Fin15AnchoredAtom2025 Fin15AnchoredAtom2030 Fin15AnchoredAtom2031
    Fin15AnchoredAtom2036 Fin15AnchoredAtom2051 Fin15AnchoredAtom2052 Fin15AnchoredAtom2057
    Fin15AnchoredAtom2072 Fin15AnchoredAtom2528 Fin15AnchoredAtom2529 Fin15AnchoredAtom2530
    Fin15AnchoredAtom2535 Fin15AnchoredAtom2536 Fin15AnchoredAtom2541 Fin15AnchoredAtom2556
    Fin15AnchoredAtom2557 Fin15AnchoredAtom2562 Fin15AnchoredAtom2577 Fin15AnchoredAtom2696
    Fin15AnchoredAtom2697 Fin15AnchoredAtom2702 Fin15AnchoredAtom2717 Fin15AnchoredAtom2752
    Fin15AnchoredAtom3243 Fin15AnchoredAtom3244 Fin15AnchoredAtom3245 Fin15AnchoredAtom3250
    Fin15AnchoredAtom3251 Fin15AnchoredAtom3256 Fin15AnchoredAtom3271 Fin15AnchoredAtom3272
    Fin15AnchoredAtom3277 Fin15AnchoredAtom3292 Fin15AnchoredAtom3411 Fin15AnchoredAtom3412
    Fin15AnchoredAtom3417 Fin15AnchoredAtom3432 Fin15AnchoredAtom3467 Fin15AnchoredAtom4446
    Fin15AnchoredAtom4447 Fin15AnchoredAtom4452 Fin15AnchoredAtom4467 Fin15AnchoredAtom4502
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

theorem fin15Anchored_clause31015 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom1952 chi ∧
      ¬Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom1959 chi ∧
      ¬Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom1966 chi ∧
      ¬Fin15AnchoredAtom1969 chi ∧
      ¬Fin15AnchoredAtom1974 chi ∧
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
      ¬Fin15AnchoredAtom2528 chi ∧
      ¬Fin15AnchoredAtom2529 chi ∧
      ¬Fin15AnchoredAtom2532 chi ∧
      ¬Fin15AnchoredAtom2535 chi ∧
      ¬Fin15AnchoredAtom2538 chi ∧
      ¬Fin15AnchoredAtom2543 chi ∧
      ¬Fin15AnchoredAtom2556 chi ∧
      ¬Fin15AnchoredAtom2559 chi ∧
      ¬Fin15AnchoredAtom2564 chi ∧
      ¬Fin15AnchoredAtom2579 chi ∧
      ¬Fin15AnchoredAtom2696 chi ∧
      ¬Fin15AnchoredAtom2699 chi ∧
      ¬Fin15AnchoredAtom2704 chi ∧
      ¬Fin15AnchoredAtom2719 chi ∧
      ¬Fin15AnchoredAtom2754 chi ∧
      ¬Fin15AnchoredAtom3243 chi ∧
      ¬Fin15AnchoredAtom3244 chi ∧
      ¬Fin15AnchoredAtom3247 chi ∧
      ¬Fin15AnchoredAtom3250 chi ∧
      ¬Fin15AnchoredAtom3253 chi ∧
      ¬Fin15AnchoredAtom3258 chi ∧
      ¬Fin15AnchoredAtom3271 chi ∧
      ¬Fin15AnchoredAtom3274 chi ∧
      ¬Fin15AnchoredAtom3279 chi ∧
      ¬Fin15AnchoredAtom3294 chi ∧
      ¬Fin15AnchoredAtom3411 chi ∧
      ¬Fin15AnchoredAtom3414 chi ∧
      ¬Fin15AnchoredAtom3419 chi ∧
      ¬Fin15AnchoredAtom3434 chi ∧
      ¬Fin15AnchoredAtom3469 chi ∧
      ¬Fin15AnchoredAtom4446 chi ∧
      ¬Fin15AnchoredAtom4449 chi ∧
      ¬Fin15AnchoredAtom4454 chi ∧
      ¬Fin15AnchoredAtom4469 chi ∧
      ¬Fin15AnchoredAtom4504 chi ∧
      ¬Fin15AnchoredAtom4700 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 6, 7, 8, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05075
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1951 Fin15AnchoredAtom1952 Fin15AnchoredAtom1953
    Fin15AnchoredAtom1956 Fin15AnchoredAtom1959 Fin15AnchoredAtom1960 Fin15AnchoredAtom1963
    Fin15AnchoredAtom1966 Fin15AnchoredAtom1969 Fin15AnchoredAtom1974 Fin15AnchoredAtom2023
    Fin15AnchoredAtom2024 Fin15AnchoredAtom2027 Fin15AnchoredAtom2030 Fin15AnchoredAtom2033
    Fin15AnchoredAtom2038 Fin15AnchoredAtom2051 Fin15AnchoredAtom2054 Fin15AnchoredAtom2059
    Fin15AnchoredAtom2074 Fin15AnchoredAtom2528 Fin15AnchoredAtom2529 Fin15AnchoredAtom2532
    Fin15AnchoredAtom2535 Fin15AnchoredAtom2538 Fin15AnchoredAtom2543 Fin15AnchoredAtom2556
    Fin15AnchoredAtom2559 Fin15AnchoredAtom2564 Fin15AnchoredAtom2579 Fin15AnchoredAtom2696
    Fin15AnchoredAtom2699 Fin15AnchoredAtom2704 Fin15AnchoredAtom2719 Fin15AnchoredAtom2754
    Fin15AnchoredAtom3243 Fin15AnchoredAtom3244 Fin15AnchoredAtom3247 Fin15AnchoredAtom3250
    Fin15AnchoredAtom3253 Fin15AnchoredAtom3258 Fin15AnchoredAtom3271 Fin15AnchoredAtom3274
    Fin15AnchoredAtom3279 Fin15AnchoredAtom3294 Fin15AnchoredAtom3411 Fin15AnchoredAtom3414
    Fin15AnchoredAtom3419 Fin15AnchoredAtom3434 Fin15AnchoredAtom3469 Fin15AnchoredAtom4446
    Fin15AnchoredAtom4449 Fin15AnchoredAtom4454 Fin15AnchoredAtom4469 Fin15AnchoredAtom4504
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

theorem fin15Anchored_clause31016 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom1952 chi ∧
      ¬Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom1959 chi ∧
      ¬Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom1966 chi ∧
      ¬Fin15AnchoredAtom1970 chi ∧
      ¬Fin15AnchoredAtom1975 chi ∧
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
      ¬Fin15AnchoredAtom2528 chi ∧
      ¬Fin15AnchoredAtom2529 chi ∧
      ¬Fin15AnchoredAtom2533 chi ∧
      ¬Fin15AnchoredAtom2535 chi ∧
      ¬Fin15AnchoredAtom2539 chi ∧
      ¬Fin15AnchoredAtom2544 chi ∧
      ¬Fin15AnchoredAtom2556 chi ∧
      ¬Fin15AnchoredAtom2560 chi ∧
      ¬Fin15AnchoredAtom2565 chi ∧
      ¬Fin15AnchoredAtom2580 chi ∧
      ¬Fin15AnchoredAtom2696 chi ∧
      ¬Fin15AnchoredAtom2700 chi ∧
      ¬Fin15AnchoredAtom2705 chi ∧
      ¬Fin15AnchoredAtom2720 chi ∧
      ¬Fin15AnchoredAtom2755 chi ∧
      ¬Fin15AnchoredAtom3243 chi ∧
      ¬Fin15AnchoredAtom3244 chi ∧
      ¬Fin15AnchoredAtom3248 chi ∧
      ¬Fin15AnchoredAtom3250 chi ∧
      ¬Fin15AnchoredAtom3254 chi ∧
      ¬Fin15AnchoredAtom3259 chi ∧
      ¬Fin15AnchoredAtom3271 chi ∧
      ¬Fin15AnchoredAtom3275 chi ∧
      ¬Fin15AnchoredAtom3280 chi ∧
      ¬Fin15AnchoredAtom3295 chi ∧
      ¬Fin15AnchoredAtom3411 chi ∧
      ¬Fin15AnchoredAtom3415 chi ∧
      ¬Fin15AnchoredAtom3420 chi ∧
      ¬Fin15AnchoredAtom3435 chi ∧
      ¬Fin15AnchoredAtom3470 chi ∧
      ¬Fin15AnchoredAtom4446 chi ∧
      ¬Fin15AnchoredAtom4450 chi ∧
      ¬Fin15AnchoredAtom4455 chi ∧
      ¬Fin15AnchoredAtom4470 chi ∧
      ¬Fin15AnchoredAtom4505 chi ∧
      ¬Fin15AnchoredAtom4701 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 6, 7, 8, 9, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09171
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1951 Fin15AnchoredAtom1952 Fin15AnchoredAtom1953
    Fin15AnchoredAtom1957 Fin15AnchoredAtom1959 Fin15AnchoredAtom1960 Fin15AnchoredAtom1964
    Fin15AnchoredAtom1966 Fin15AnchoredAtom1970 Fin15AnchoredAtom1975 Fin15AnchoredAtom2023
    Fin15AnchoredAtom2024 Fin15AnchoredAtom2028 Fin15AnchoredAtom2030 Fin15AnchoredAtom2034
    Fin15AnchoredAtom2039 Fin15AnchoredAtom2051 Fin15AnchoredAtom2055 Fin15AnchoredAtom2060
    Fin15AnchoredAtom2075 Fin15AnchoredAtom2528 Fin15AnchoredAtom2529 Fin15AnchoredAtom2533
    Fin15AnchoredAtom2535 Fin15AnchoredAtom2539 Fin15AnchoredAtom2544 Fin15AnchoredAtom2556
    Fin15AnchoredAtom2560 Fin15AnchoredAtom2565 Fin15AnchoredAtom2580 Fin15AnchoredAtom2696
    Fin15AnchoredAtom2700 Fin15AnchoredAtom2705 Fin15AnchoredAtom2720 Fin15AnchoredAtom2755
    Fin15AnchoredAtom3243 Fin15AnchoredAtom3244 Fin15AnchoredAtom3248 Fin15AnchoredAtom3250
    Fin15AnchoredAtom3254 Fin15AnchoredAtom3259 Fin15AnchoredAtom3271 Fin15AnchoredAtom3275
    Fin15AnchoredAtom3280 Fin15AnchoredAtom3295 Fin15AnchoredAtom3411 Fin15AnchoredAtom3415
    Fin15AnchoredAtom3420 Fin15AnchoredAtom3435 Fin15AnchoredAtom3470 Fin15AnchoredAtom4446
    Fin15AnchoredAtom4450 Fin15AnchoredAtom4455 Fin15AnchoredAtom4470 Fin15AnchoredAtom4505
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

theorem fin15Anchored_clause31017 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom1952 chi ∧
      ¬Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom1959 chi ∧
      ¬Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom1967 chi ∧
      ¬Fin15AnchoredAtom1969 chi ∧
      ¬Fin15AnchoredAtom1978 chi ∧
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
      ¬Fin15AnchoredAtom2528 chi ∧
      ¬Fin15AnchoredAtom2530 chi ∧
      ¬Fin15AnchoredAtom2532 chi ∧
      ¬Fin15AnchoredAtom2536 chi ∧
      ¬Fin15AnchoredAtom2538 chi ∧
      ¬Fin15AnchoredAtom2547 chi ∧
      ¬Fin15AnchoredAtom2557 chi ∧
      ¬Fin15AnchoredAtom2559 chi ∧
      ¬Fin15AnchoredAtom2568 chi ∧
      ¬Fin15AnchoredAtom2583 chi ∧
      ¬Fin15AnchoredAtom2697 chi ∧
      ¬Fin15AnchoredAtom2699 chi ∧
      ¬Fin15AnchoredAtom2708 chi ∧
      ¬Fin15AnchoredAtom2723 chi ∧
      ¬Fin15AnchoredAtom2758 chi ∧
      ¬Fin15AnchoredAtom3243 chi ∧
      ¬Fin15AnchoredAtom3245 chi ∧
      ¬Fin15AnchoredAtom3247 chi ∧
      ¬Fin15AnchoredAtom3251 chi ∧
      ¬Fin15AnchoredAtom3253 chi ∧
      ¬Fin15AnchoredAtom3262 chi ∧
      ¬Fin15AnchoredAtom3272 chi ∧
      ¬Fin15AnchoredAtom3274 chi ∧
      ¬Fin15AnchoredAtom3283 chi ∧
      ¬Fin15AnchoredAtom3298 chi ∧
      ¬Fin15AnchoredAtom3412 chi ∧
      ¬Fin15AnchoredAtom3414 chi ∧
      ¬Fin15AnchoredAtom3423 chi ∧
      ¬Fin15AnchoredAtom3438 chi ∧
      ¬Fin15AnchoredAtom3473 chi ∧
      ¬Fin15AnchoredAtom4447 chi ∧
      ¬Fin15AnchoredAtom4449 chi ∧
      ¬Fin15AnchoredAtom4458 chi ∧
      ¬Fin15AnchoredAtom4473 chi ∧
      ¬Fin15AnchoredAtom4508 chi ∧
      ¬Fin15AnchoredAtom4704 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 6, 7, 8, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05587
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1951 Fin15AnchoredAtom1952 Fin15AnchoredAtom1954
    Fin15AnchoredAtom1956 Fin15AnchoredAtom1959 Fin15AnchoredAtom1961 Fin15AnchoredAtom1963
    Fin15AnchoredAtom1967 Fin15AnchoredAtom1969 Fin15AnchoredAtom1978 Fin15AnchoredAtom2023
    Fin15AnchoredAtom2025 Fin15AnchoredAtom2027 Fin15AnchoredAtom2031 Fin15AnchoredAtom2033
    Fin15AnchoredAtom2042 Fin15AnchoredAtom2052 Fin15AnchoredAtom2054 Fin15AnchoredAtom2063
    Fin15AnchoredAtom2078 Fin15AnchoredAtom2528 Fin15AnchoredAtom2530 Fin15AnchoredAtom2532
    Fin15AnchoredAtom2536 Fin15AnchoredAtom2538 Fin15AnchoredAtom2547 Fin15AnchoredAtom2557
    Fin15AnchoredAtom2559 Fin15AnchoredAtom2568 Fin15AnchoredAtom2583 Fin15AnchoredAtom2697
    Fin15AnchoredAtom2699 Fin15AnchoredAtom2708 Fin15AnchoredAtom2723 Fin15AnchoredAtom2758
    Fin15AnchoredAtom3243 Fin15AnchoredAtom3245 Fin15AnchoredAtom3247 Fin15AnchoredAtom3251
    Fin15AnchoredAtom3253 Fin15AnchoredAtom3262 Fin15AnchoredAtom3272 Fin15AnchoredAtom3274
    Fin15AnchoredAtom3283 Fin15AnchoredAtom3298 Fin15AnchoredAtom3412 Fin15AnchoredAtom3414
    Fin15AnchoredAtom3423 Fin15AnchoredAtom3438 Fin15AnchoredAtom3473 Fin15AnchoredAtom4447
    Fin15AnchoredAtom4449 Fin15AnchoredAtom4458 Fin15AnchoredAtom4473 Fin15AnchoredAtom4508
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

theorem fin15Anchored_clause31018 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom1952 chi ∧
      ¬Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom1959 chi ∧
      ¬Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom1967 chi ∧
      ¬Fin15AnchoredAtom1970 chi ∧
      ¬Fin15AnchoredAtom1979 chi ∧
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
      ¬Fin15AnchoredAtom2528 chi ∧
      ¬Fin15AnchoredAtom2530 chi ∧
      ¬Fin15AnchoredAtom2533 chi ∧
      ¬Fin15AnchoredAtom2536 chi ∧
      ¬Fin15AnchoredAtom2539 chi ∧
      ¬Fin15AnchoredAtom2548 chi ∧
      ¬Fin15AnchoredAtom2557 chi ∧
      ¬Fin15AnchoredAtom2560 chi ∧
      ¬Fin15AnchoredAtom2569 chi ∧
      ¬Fin15AnchoredAtom2584 chi ∧
      ¬Fin15AnchoredAtom2697 chi ∧
      ¬Fin15AnchoredAtom2700 chi ∧
      ¬Fin15AnchoredAtom2709 chi ∧
      ¬Fin15AnchoredAtom2724 chi ∧
      ¬Fin15AnchoredAtom2759 chi ∧
      ¬Fin15AnchoredAtom3243 chi ∧
      ¬Fin15AnchoredAtom3245 chi ∧
      ¬Fin15AnchoredAtom3248 chi ∧
      ¬Fin15AnchoredAtom3251 chi ∧
      ¬Fin15AnchoredAtom3254 chi ∧
      ¬Fin15AnchoredAtom3263 chi ∧
      ¬Fin15AnchoredAtom3272 chi ∧
      ¬Fin15AnchoredAtom3275 chi ∧
      ¬Fin15AnchoredAtom3284 chi ∧
      ¬Fin15AnchoredAtom3299 chi ∧
      ¬Fin15AnchoredAtom3412 chi ∧
      ¬Fin15AnchoredAtom3415 chi ∧
      ¬Fin15AnchoredAtom3424 chi ∧
      ¬Fin15AnchoredAtom3439 chi ∧
      ¬Fin15AnchoredAtom3474 chi ∧
      ¬Fin15AnchoredAtom4447 chi ∧
      ¬Fin15AnchoredAtom4450 chi ∧
      ¬Fin15AnchoredAtom4459 chi ∧
      ¬Fin15AnchoredAtom4474 chi ∧
      ¬Fin15AnchoredAtom4509 chi ∧
      ¬Fin15AnchoredAtom4705 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 6, 7, 8, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09683
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1951 Fin15AnchoredAtom1952 Fin15AnchoredAtom1954
    Fin15AnchoredAtom1957 Fin15AnchoredAtom1959 Fin15AnchoredAtom1961 Fin15AnchoredAtom1964
    Fin15AnchoredAtom1967 Fin15AnchoredAtom1970 Fin15AnchoredAtom1979 Fin15AnchoredAtom2023
    Fin15AnchoredAtom2025 Fin15AnchoredAtom2028 Fin15AnchoredAtom2031 Fin15AnchoredAtom2034
    Fin15AnchoredAtom2043 Fin15AnchoredAtom2052 Fin15AnchoredAtom2055 Fin15AnchoredAtom2064
    Fin15AnchoredAtom2079 Fin15AnchoredAtom2528 Fin15AnchoredAtom2530 Fin15AnchoredAtom2533
    Fin15AnchoredAtom2536 Fin15AnchoredAtom2539 Fin15AnchoredAtom2548 Fin15AnchoredAtom2557
    Fin15AnchoredAtom2560 Fin15AnchoredAtom2569 Fin15AnchoredAtom2584 Fin15AnchoredAtom2697
    Fin15AnchoredAtom2700 Fin15AnchoredAtom2709 Fin15AnchoredAtom2724 Fin15AnchoredAtom2759
    Fin15AnchoredAtom3243 Fin15AnchoredAtom3245 Fin15AnchoredAtom3248 Fin15AnchoredAtom3251
    Fin15AnchoredAtom3254 Fin15AnchoredAtom3263 Fin15AnchoredAtom3272 Fin15AnchoredAtom3275
    Fin15AnchoredAtom3284 Fin15AnchoredAtom3299 Fin15AnchoredAtom3412 Fin15AnchoredAtom3415
    Fin15AnchoredAtom3424 Fin15AnchoredAtom3439 Fin15AnchoredAtom3474 Fin15AnchoredAtom4447
    Fin15AnchoredAtom4450 Fin15AnchoredAtom4459 Fin15AnchoredAtom4474 Fin15AnchoredAtom4509
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

theorem fin15Anchored_clause31019 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom1952 chi ∧
      ¬Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom1959 chi ∧
      ¬Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom1967 chi ∧
      ¬Fin15AnchoredAtom1971 chi ∧
      ¬Fin15AnchoredAtom1980 chi ∧
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
      ¬Fin15AnchoredAtom2528 chi ∧
      ¬Fin15AnchoredAtom2530 chi ∧
      ¬Fin15AnchoredAtom2534 chi ∧
      ¬Fin15AnchoredAtom2536 chi ∧
      ¬Fin15AnchoredAtom2540 chi ∧
      ¬Fin15AnchoredAtom2549 chi ∧
      ¬Fin15AnchoredAtom2557 chi ∧
      ¬Fin15AnchoredAtom2561 chi ∧
      ¬Fin15AnchoredAtom2570 chi ∧
      ¬Fin15AnchoredAtom2585 chi ∧
      ¬Fin15AnchoredAtom2697 chi ∧
      ¬Fin15AnchoredAtom2701 chi ∧
      ¬Fin15AnchoredAtom2710 chi ∧
      ¬Fin15AnchoredAtom2725 chi ∧
      ¬Fin15AnchoredAtom2760 chi ∧
      ¬Fin15AnchoredAtom3243 chi ∧
      ¬Fin15AnchoredAtom3245 chi ∧
      ¬Fin15AnchoredAtom3249 chi ∧
      ¬Fin15AnchoredAtom3251 chi ∧
      ¬Fin15AnchoredAtom3255 chi ∧
      ¬Fin15AnchoredAtom3264 chi ∧
      ¬Fin15AnchoredAtom3272 chi ∧
      ¬Fin15AnchoredAtom3276 chi ∧
      ¬Fin15AnchoredAtom3285 chi ∧
      ¬Fin15AnchoredAtom3300 chi ∧
      ¬Fin15AnchoredAtom3412 chi ∧
      ¬Fin15AnchoredAtom3416 chi ∧
      ¬Fin15AnchoredAtom3425 chi ∧
      ¬Fin15AnchoredAtom3440 chi ∧
      ¬Fin15AnchoredAtom3475 chi ∧
      ¬Fin15AnchoredAtom4447 chi ∧
      ¬Fin15AnchoredAtom4451 chi ∧
      ¬Fin15AnchoredAtom4460 chi ∧
      ¬Fin15AnchoredAtom4475 chi ∧
      ¬Fin15AnchoredAtom4510 chi ∧
      ¬Fin15AnchoredAtom4706 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 6, 7, 8, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17875
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1951 Fin15AnchoredAtom1952 Fin15AnchoredAtom1954
    Fin15AnchoredAtom1958 Fin15AnchoredAtom1959 Fin15AnchoredAtom1961 Fin15AnchoredAtom1965
    Fin15AnchoredAtom1967 Fin15AnchoredAtom1971 Fin15AnchoredAtom1980 Fin15AnchoredAtom2023
    Fin15AnchoredAtom2025 Fin15AnchoredAtom2029 Fin15AnchoredAtom2031 Fin15AnchoredAtom2035
    Fin15AnchoredAtom2044 Fin15AnchoredAtom2052 Fin15AnchoredAtom2056 Fin15AnchoredAtom2065
    Fin15AnchoredAtom2080 Fin15AnchoredAtom2528 Fin15AnchoredAtom2530 Fin15AnchoredAtom2534
    Fin15AnchoredAtom2536 Fin15AnchoredAtom2540 Fin15AnchoredAtom2549 Fin15AnchoredAtom2557
    Fin15AnchoredAtom2561 Fin15AnchoredAtom2570 Fin15AnchoredAtom2585 Fin15AnchoredAtom2697
    Fin15AnchoredAtom2701 Fin15AnchoredAtom2710 Fin15AnchoredAtom2725 Fin15AnchoredAtom2760
    Fin15AnchoredAtom3243 Fin15AnchoredAtom3245 Fin15AnchoredAtom3249 Fin15AnchoredAtom3251
    Fin15AnchoredAtom3255 Fin15AnchoredAtom3264 Fin15AnchoredAtom3272 Fin15AnchoredAtom3276
    Fin15AnchoredAtom3285 Fin15AnchoredAtom3300 Fin15AnchoredAtom3412 Fin15AnchoredAtom3416
    Fin15AnchoredAtom3425 Fin15AnchoredAtom3440 Fin15AnchoredAtom3475 Fin15AnchoredAtom4447
    Fin15AnchoredAtom4451 Fin15AnchoredAtom4460 Fin15AnchoredAtom4475 Fin15AnchoredAtom4510
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

theorem fin15Anchored_clause31020 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom1952 chi ∧
      ¬Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom1959 chi ∧
      ¬Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom1969 chi ∧
      ¬Fin15AnchoredAtom1971 chi ∧
      ¬Fin15AnchoredAtom1985 chi ∧
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
      ¬Fin15AnchoredAtom2528 chi ∧
      ¬Fin15AnchoredAtom2532 chi ∧
      ¬Fin15AnchoredAtom2534 chi ∧
      ¬Fin15AnchoredAtom2538 chi ∧
      ¬Fin15AnchoredAtom2540 chi ∧
      ¬Fin15AnchoredAtom2554 chi ∧
      ¬Fin15AnchoredAtom2559 chi ∧
      ¬Fin15AnchoredAtom2561 chi ∧
      ¬Fin15AnchoredAtom2575 chi ∧
      ¬Fin15AnchoredAtom2590 chi ∧
      ¬Fin15AnchoredAtom2699 chi ∧
      ¬Fin15AnchoredAtom2701 chi ∧
      ¬Fin15AnchoredAtom2715 chi ∧
      ¬Fin15AnchoredAtom2730 chi ∧
      ¬Fin15AnchoredAtom2765 chi ∧
      ¬Fin15AnchoredAtom3243 chi ∧
      ¬Fin15AnchoredAtom3247 chi ∧
      ¬Fin15AnchoredAtom3249 chi ∧
      ¬Fin15AnchoredAtom3253 chi ∧
      ¬Fin15AnchoredAtom3255 chi ∧
      ¬Fin15AnchoredAtom3269 chi ∧
      ¬Fin15AnchoredAtom3274 chi ∧
      ¬Fin15AnchoredAtom3276 chi ∧
      ¬Fin15AnchoredAtom3290 chi ∧
      ¬Fin15AnchoredAtom3305 chi ∧
      ¬Fin15AnchoredAtom3414 chi ∧
      ¬Fin15AnchoredAtom3416 chi ∧
      ¬Fin15AnchoredAtom3430 chi ∧
      ¬Fin15AnchoredAtom3445 chi ∧
      ¬Fin15AnchoredAtom3480 chi ∧
      ¬Fin15AnchoredAtom4449 chi ∧
      ¬Fin15AnchoredAtom4451 chi ∧
      ¬Fin15AnchoredAtom4465 chi ∧
      ¬Fin15AnchoredAtom4480 chi ∧
      ¬Fin15AnchoredAtom4515 chi ∧
      ¬Fin15AnchoredAtom4711 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 6, 7, 8, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask20947
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1951 Fin15AnchoredAtom1952 Fin15AnchoredAtom1956
    Fin15AnchoredAtom1958 Fin15AnchoredAtom1959 Fin15AnchoredAtom1963 Fin15AnchoredAtom1965
    Fin15AnchoredAtom1969 Fin15AnchoredAtom1971 Fin15AnchoredAtom1985 Fin15AnchoredAtom2023
    Fin15AnchoredAtom2027 Fin15AnchoredAtom2029 Fin15AnchoredAtom2033 Fin15AnchoredAtom2035
    Fin15AnchoredAtom2049 Fin15AnchoredAtom2054 Fin15AnchoredAtom2056 Fin15AnchoredAtom2070
    Fin15AnchoredAtom2085 Fin15AnchoredAtom2528 Fin15AnchoredAtom2532 Fin15AnchoredAtom2534
    Fin15AnchoredAtom2538 Fin15AnchoredAtom2540 Fin15AnchoredAtom2554 Fin15AnchoredAtom2559
    Fin15AnchoredAtom2561 Fin15AnchoredAtom2575 Fin15AnchoredAtom2590 Fin15AnchoredAtom2699
    Fin15AnchoredAtom2701 Fin15AnchoredAtom2715 Fin15AnchoredAtom2730 Fin15AnchoredAtom2765
    Fin15AnchoredAtom3243 Fin15AnchoredAtom3247 Fin15AnchoredAtom3249 Fin15AnchoredAtom3253
    Fin15AnchoredAtom3255 Fin15AnchoredAtom3269 Fin15AnchoredAtom3274 Fin15AnchoredAtom3276
    Fin15AnchoredAtom3290 Fin15AnchoredAtom3305 Fin15AnchoredAtom3414 Fin15AnchoredAtom3416
    Fin15AnchoredAtom3430 Fin15AnchoredAtom3445 Fin15AnchoredAtom3480 Fin15AnchoredAtom4449
    Fin15AnchoredAtom4451 Fin15AnchoredAtom4465 Fin15AnchoredAtom4480 Fin15AnchoredAtom4515
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

theorem fin15Anchored_clause31021 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom1952 chi ∧
      ¬Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom1959 chi ∧
      ¬Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom1970 chi ∧
      ¬Fin15AnchoredAtom1971 chi ∧
      ¬Fin15AnchoredAtom1986 chi ∧
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
      ¬Fin15AnchoredAtom2528 chi ∧
      ¬Fin15AnchoredAtom2533 chi ∧
      ¬Fin15AnchoredAtom2534 chi ∧
      ¬Fin15AnchoredAtom2539 chi ∧
      ¬Fin15AnchoredAtom2540 chi ∧
      ¬Fin15AnchoredAtom2555 chi ∧
      ¬Fin15AnchoredAtom2560 chi ∧
      ¬Fin15AnchoredAtom2561 chi ∧
      ¬Fin15AnchoredAtom2576 chi ∧
      ¬Fin15AnchoredAtom2591 chi ∧
      ¬Fin15AnchoredAtom2700 chi ∧
      ¬Fin15AnchoredAtom2701 chi ∧
      ¬Fin15AnchoredAtom2716 chi ∧
      ¬Fin15AnchoredAtom2731 chi ∧
      ¬Fin15AnchoredAtom2766 chi ∧
      ¬Fin15AnchoredAtom3243 chi ∧
      ¬Fin15AnchoredAtom3248 chi ∧
      ¬Fin15AnchoredAtom3249 chi ∧
      ¬Fin15AnchoredAtom3254 chi ∧
      ¬Fin15AnchoredAtom3255 chi ∧
      ¬Fin15AnchoredAtom3270 chi ∧
      ¬Fin15AnchoredAtom3275 chi ∧
      ¬Fin15AnchoredAtom3276 chi ∧
      ¬Fin15AnchoredAtom3291 chi ∧
      ¬Fin15AnchoredAtom3306 chi ∧
      ¬Fin15AnchoredAtom3415 chi ∧
      ¬Fin15AnchoredAtom3416 chi ∧
      ¬Fin15AnchoredAtom3431 chi ∧
      ¬Fin15AnchoredAtom3446 chi ∧
      ¬Fin15AnchoredAtom3481 chi ∧
      ¬Fin15AnchoredAtom4450 chi ∧
      ¬Fin15AnchoredAtom4451 chi ∧
      ¬Fin15AnchoredAtom4466 chi ∧
      ¬Fin15AnchoredAtom4481 chi ∧
      ¬Fin15AnchoredAtom4516 chi ∧
      ¬Fin15AnchoredAtom4712 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 6, 7, 8, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25043
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1951 Fin15AnchoredAtom1952 Fin15AnchoredAtom1957
    Fin15AnchoredAtom1958 Fin15AnchoredAtom1959 Fin15AnchoredAtom1964 Fin15AnchoredAtom1965
    Fin15AnchoredAtom1970 Fin15AnchoredAtom1971 Fin15AnchoredAtom1986 Fin15AnchoredAtom2023
    Fin15AnchoredAtom2028 Fin15AnchoredAtom2029 Fin15AnchoredAtom2034 Fin15AnchoredAtom2035
    Fin15AnchoredAtom2050 Fin15AnchoredAtom2055 Fin15AnchoredAtom2056 Fin15AnchoredAtom2071
    Fin15AnchoredAtom2086 Fin15AnchoredAtom2528 Fin15AnchoredAtom2533 Fin15AnchoredAtom2534
    Fin15AnchoredAtom2539 Fin15AnchoredAtom2540 Fin15AnchoredAtom2555 Fin15AnchoredAtom2560
    Fin15AnchoredAtom2561 Fin15AnchoredAtom2576 Fin15AnchoredAtom2591 Fin15AnchoredAtom2700
    Fin15AnchoredAtom2701 Fin15AnchoredAtom2716 Fin15AnchoredAtom2731 Fin15AnchoredAtom2766
    Fin15AnchoredAtom3243 Fin15AnchoredAtom3248 Fin15AnchoredAtom3249 Fin15AnchoredAtom3254
    Fin15AnchoredAtom3255 Fin15AnchoredAtom3270 Fin15AnchoredAtom3275 Fin15AnchoredAtom3276
    Fin15AnchoredAtom3291 Fin15AnchoredAtom3306 Fin15AnchoredAtom3415 Fin15AnchoredAtom3416
    Fin15AnchoredAtom3431 Fin15AnchoredAtom3446 Fin15AnchoredAtom3481 Fin15AnchoredAtom4450
    Fin15AnchoredAtom4451 Fin15AnchoredAtom4466 Fin15AnchoredAtom4481 Fin15AnchoredAtom4516
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

theorem fin15Anchored_clause31022 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom1978 chi ∧
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
      ¬Fin15AnchoredAtom2529 chi ∧
      ¬Fin15AnchoredAtom2530 chi ∧
      ¬Fin15AnchoredAtom2532 chi ∧
      ¬Fin15AnchoredAtom2541 chi ∧
      ¬Fin15AnchoredAtom2543 chi ∧
      ¬Fin15AnchoredAtom2547 chi ∧
      ¬Fin15AnchoredAtom2562 chi ∧
      ¬Fin15AnchoredAtom2564 chi ∧
      ¬Fin15AnchoredAtom2568 chi ∧
      ¬Fin15AnchoredAtom2593 chi ∧
      ¬Fin15AnchoredAtom2702 chi ∧
      ¬Fin15AnchoredAtom2704 chi ∧
      ¬Fin15AnchoredAtom2708 chi ∧
      ¬Fin15AnchoredAtom2733 chi ∧
      ¬Fin15AnchoredAtom2768 chi ∧
      ¬Fin15AnchoredAtom3244 chi ∧
      ¬Fin15AnchoredAtom3245 chi ∧
      ¬Fin15AnchoredAtom3247 chi ∧
      ¬Fin15AnchoredAtom3256 chi ∧
      ¬Fin15AnchoredAtom3258 chi ∧
      ¬Fin15AnchoredAtom3262 chi ∧
      ¬Fin15AnchoredAtom3277 chi ∧
      ¬Fin15AnchoredAtom3279 chi ∧
      ¬Fin15AnchoredAtom3283 chi ∧
      ¬Fin15AnchoredAtom3308 chi ∧
      ¬Fin15AnchoredAtom3417 chi ∧
      ¬Fin15AnchoredAtom3419 chi ∧
      ¬Fin15AnchoredAtom3423 chi ∧
      ¬Fin15AnchoredAtom3448 chi ∧
      ¬Fin15AnchoredAtom3483 chi ∧
      ¬Fin15AnchoredAtom4452 chi ∧
      ¬Fin15AnchoredAtom4454 chi ∧
      ¬Fin15AnchoredAtom4458 chi ∧
      ¬Fin15AnchoredAtom4483 chi ∧
      ¬Fin15AnchoredAtom4518 chi ∧
      ¬Fin15AnchoredAtom4714 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 6, 7, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05843
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1951 Fin15AnchoredAtom1953 Fin15AnchoredAtom1954
    Fin15AnchoredAtom1956 Fin15AnchoredAtom1960 Fin15AnchoredAtom1961 Fin15AnchoredAtom1963
    Fin15AnchoredAtom1972 Fin15AnchoredAtom1974 Fin15AnchoredAtom1978 Fin15AnchoredAtom2024
    Fin15AnchoredAtom2025 Fin15AnchoredAtom2027 Fin15AnchoredAtom2036 Fin15AnchoredAtom2038
    Fin15AnchoredAtom2042 Fin15AnchoredAtom2057 Fin15AnchoredAtom2059 Fin15AnchoredAtom2063
    Fin15AnchoredAtom2088 Fin15AnchoredAtom2529 Fin15AnchoredAtom2530 Fin15AnchoredAtom2532
    Fin15AnchoredAtom2541 Fin15AnchoredAtom2543 Fin15AnchoredAtom2547 Fin15AnchoredAtom2562
    Fin15AnchoredAtom2564 Fin15AnchoredAtom2568 Fin15AnchoredAtom2593 Fin15AnchoredAtom2702
    Fin15AnchoredAtom2704 Fin15AnchoredAtom2708 Fin15AnchoredAtom2733 Fin15AnchoredAtom2768
    Fin15AnchoredAtom3244 Fin15AnchoredAtom3245 Fin15AnchoredAtom3247 Fin15AnchoredAtom3256
    Fin15AnchoredAtom3258 Fin15AnchoredAtom3262 Fin15AnchoredAtom3277 Fin15AnchoredAtom3279
    Fin15AnchoredAtom3283 Fin15AnchoredAtom3308 Fin15AnchoredAtom3417 Fin15AnchoredAtom3419
    Fin15AnchoredAtom3423 Fin15AnchoredAtom3448 Fin15AnchoredAtom3483 Fin15AnchoredAtom4452
    Fin15AnchoredAtom4454 Fin15AnchoredAtom4458 Fin15AnchoredAtom4483 Fin15AnchoredAtom4518
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

theorem fin15Anchored_clause31023 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom1979 chi ∧
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
      ¬Fin15AnchoredAtom2529 chi ∧
      ¬Fin15AnchoredAtom2530 chi ∧
      ¬Fin15AnchoredAtom2533 chi ∧
      ¬Fin15AnchoredAtom2541 chi ∧
      ¬Fin15AnchoredAtom2544 chi ∧
      ¬Fin15AnchoredAtom2548 chi ∧
      ¬Fin15AnchoredAtom2562 chi ∧
      ¬Fin15AnchoredAtom2565 chi ∧
      ¬Fin15AnchoredAtom2569 chi ∧
      ¬Fin15AnchoredAtom2594 chi ∧
      ¬Fin15AnchoredAtom2702 chi ∧
      ¬Fin15AnchoredAtom2705 chi ∧
      ¬Fin15AnchoredAtom2709 chi ∧
      ¬Fin15AnchoredAtom2734 chi ∧
      ¬Fin15AnchoredAtom2769 chi ∧
      ¬Fin15AnchoredAtom3244 chi ∧
      ¬Fin15AnchoredAtom3245 chi ∧
      ¬Fin15AnchoredAtom3248 chi ∧
      ¬Fin15AnchoredAtom3256 chi ∧
      ¬Fin15AnchoredAtom3259 chi ∧
      ¬Fin15AnchoredAtom3263 chi ∧
      ¬Fin15AnchoredAtom3277 chi ∧
      ¬Fin15AnchoredAtom3280 chi ∧
      ¬Fin15AnchoredAtom3284 chi ∧
      ¬Fin15AnchoredAtom3309 chi ∧
      ¬Fin15AnchoredAtom3417 chi ∧
      ¬Fin15AnchoredAtom3420 chi ∧
      ¬Fin15AnchoredAtom3424 chi ∧
      ¬Fin15AnchoredAtom3449 chi ∧
      ¬Fin15AnchoredAtom3484 chi ∧
      ¬Fin15AnchoredAtom4452 chi ∧
      ¬Fin15AnchoredAtom4455 chi ∧
      ¬Fin15AnchoredAtom4459 chi ∧
      ¬Fin15AnchoredAtom4484 chi ∧
      ¬Fin15AnchoredAtom4519 chi ∧
      ¬Fin15AnchoredAtom4715 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 6, 7, 9, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09939
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1951 Fin15AnchoredAtom1953 Fin15AnchoredAtom1954
    Fin15AnchoredAtom1957 Fin15AnchoredAtom1960 Fin15AnchoredAtom1961 Fin15AnchoredAtom1964
    Fin15AnchoredAtom1972 Fin15AnchoredAtom1975 Fin15AnchoredAtom1979 Fin15AnchoredAtom2024
    Fin15AnchoredAtom2025 Fin15AnchoredAtom2028 Fin15AnchoredAtom2036 Fin15AnchoredAtom2039
    Fin15AnchoredAtom2043 Fin15AnchoredAtom2057 Fin15AnchoredAtom2060 Fin15AnchoredAtom2064
    Fin15AnchoredAtom2089 Fin15AnchoredAtom2529 Fin15AnchoredAtom2530 Fin15AnchoredAtom2533
    Fin15AnchoredAtom2541 Fin15AnchoredAtom2544 Fin15AnchoredAtom2548 Fin15AnchoredAtom2562
    Fin15AnchoredAtom2565 Fin15AnchoredAtom2569 Fin15AnchoredAtom2594 Fin15AnchoredAtom2702
    Fin15AnchoredAtom2705 Fin15AnchoredAtom2709 Fin15AnchoredAtom2734 Fin15AnchoredAtom2769
    Fin15AnchoredAtom3244 Fin15AnchoredAtom3245 Fin15AnchoredAtom3248 Fin15AnchoredAtom3256
    Fin15AnchoredAtom3259 Fin15AnchoredAtom3263 Fin15AnchoredAtom3277 Fin15AnchoredAtom3280
    Fin15AnchoredAtom3284 Fin15AnchoredAtom3309 Fin15AnchoredAtom3417 Fin15AnchoredAtom3420
    Fin15AnchoredAtom3424 Fin15AnchoredAtom3449 Fin15AnchoredAtom3484 Fin15AnchoredAtom4452
    Fin15AnchoredAtom4455 Fin15AnchoredAtom4459 Fin15AnchoredAtom4484 Fin15AnchoredAtom4519
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

theorem fin15Anchored_clause31024 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom1976 chi ∧
      ¬Fin15AnchoredAtom1980 chi ∧
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
      ¬Fin15AnchoredAtom2529 chi ∧
      ¬Fin15AnchoredAtom2530 chi ∧
      ¬Fin15AnchoredAtom2534 chi ∧
      ¬Fin15AnchoredAtom2541 chi ∧
      ¬Fin15AnchoredAtom2545 chi ∧
      ¬Fin15AnchoredAtom2549 chi ∧
      ¬Fin15AnchoredAtom2562 chi ∧
      ¬Fin15AnchoredAtom2566 chi ∧
      ¬Fin15AnchoredAtom2570 chi ∧
      ¬Fin15AnchoredAtom2595 chi ∧
      ¬Fin15AnchoredAtom2702 chi ∧
      ¬Fin15AnchoredAtom2706 chi ∧
      ¬Fin15AnchoredAtom2710 chi ∧
      ¬Fin15AnchoredAtom2735 chi ∧
      ¬Fin15AnchoredAtom2770 chi ∧
      ¬Fin15AnchoredAtom3244 chi ∧
      ¬Fin15AnchoredAtom3245 chi ∧
      ¬Fin15AnchoredAtom3249 chi ∧
      ¬Fin15AnchoredAtom3256 chi ∧
      ¬Fin15AnchoredAtom3260 chi ∧
      ¬Fin15AnchoredAtom3264 chi ∧
      ¬Fin15AnchoredAtom3277 chi ∧
      ¬Fin15AnchoredAtom3281 chi ∧
      ¬Fin15AnchoredAtom3285 chi ∧
      ¬Fin15AnchoredAtom3310 chi ∧
      ¬Fin15AnchoredAtom3417 chi ∧
      ¬Fin15AnchoredAtom3421 chi ∧
      ¬Fin15AnchoredAtom3425 chi ∧
      ¬Fin15AnchoredAtom3450 chi ∧
      ¬Fin15AnchoredAtom3485 chi ∧
      ¬Fin15AnchoredAtom4452 chi ∧
      ¬Fin15AnchoredAtom4456 chi ∧
      ¬Fin15AnchoredAtom4460 chi ∧
      ¬Fin15AnchoredAtom4485 chi ∧
      ¬Fin15AnchoredAtom4520 chi ∧
      ¬Fin15AnchoredAtom4716 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 6, 7, 9, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask18131
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1951 Fin15AnchoredAtom1953 Fin15AnchoredAtom1954
    Fin15AnchoredAtom1958 Fin15AnchoredAtom1960 Fin15AnchoredAtom1961 Fin15AnchoredAtom1965
    Fin15AnchoredAtom1972 Fin15AnchoredAtom1976 Fin15AnchoredAtom1980 Fin15AnchoredAtom2024
    Fin15AnchoredAtom2025 Fin15AnchoredAtom2029 Fin15AnchoredAtom2036 Fin15AnchoredAtom2040
    Fin15AnchoredAtom2044 Fin15AnchoredAtom2057 Fin15AnchoredAtom2061 Fin15AnchoredAtom2065
    Fin15AnchoredAtom2090 Fin15AnchoredAtom2529 Fin15AnchoredAtom2530 Fin15AnchoredAtom2534
    Fin15AnchoredAtom2541 Fin15AnchoredAtom2545 Fin15AnchoredAtom2549 Fin15AnchoredAtom2562
    Fin15AnchoredAtom2566 Fin15AnchoredAtom2570 Fin15AnchoredAtom2595 Fin15AnchoredAtom2702
    Fin15AnchoredAtom2706 Fin15AnchoredAtom2710 Fin15AnchoredAtom2735 Fin15AnchoredAtom2770
    Fin15AnchoredAtom3244 Fin15AnchoredAtom3245 Fin15AnchoredAtom3249 Fin15AnchoredAtom3256
    Fin15AnchoredAtom3260 Fin15AnchoredAtom3264 Fin15AnchoredAtom3277 Fin15AnchoredAtom3281
    Fin15AnchoredAtom3285 Fin15AnchoredAtom3310 Fin15AnchoredAtom3417 Fin15AnchoredAtom3421
    Fin15AnchoredAtom3425 Fin15AnchoredAtom3450 Fin15AnchoredAtom3485 Fin15AnchoredAtom4452
    Fin15AnchoredAtom4456 Fin15AnchoredAtom4460 Fin15AnchoredAtom4485 Fin15AnchoredAtom4520
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

theorem fin15Anchored_clause31025 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom1984 chi ∧
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
      ¬Fin15AnchoredAtom2529 chi ∧
      ¬Fin15AnchoredAtom2532 chi ∧
      ¬Fin15AnchoredAtom2533 chi ∧
      ¬Fin15AnchoredAtom2543 chi ∧
      ¬Fin15AnchoredAtom2544 chi ∧
      ¬Fin15AnchoredAtom2553 chi ∧
      ¬Fin15AnchoredAtom2564 chi ∧
      ¬Fin15AnchoredAtom2565 chi ∧
      ¬Fin15AnchoredAtom2574 chi ∧
      ¬Fin15AnchoredAtom2599 chi ∧
      ¬Fin15AnchoredAtom2704 chi ∧
      ¬Fin15AnchoredAtom2705 chi ∧
      ¬Fin15AnchoredAtom2714 chi ∧
      ¬Fin15AnchoredAtom2739 chi ∧
      ¬Fin15AnchoredAtom2774 chi ∧
      ¬Fin15AnchoredAtom3244 chi ∧
      ¬Fin15AnchoredAtom3247 chi ∧
      ¬Fin15AnchoredAtom3248 chi ∧
      ¬Fin15AnchoredAtom3258 chi ∧
      ¬Fin15AnchoredAtom3259 chi ∧
      ¬Fin15AnchoredAtom3268 chi ∧
      ¬Fin15AnchoredAtom3279 chi ∧
      ¬Fin15AnchoredAtom3280 chi ∧
      ¬Fin15AnchoredAtom3289 chi ∧
      ¬Fin15AnchoredAtom3314 chi ∧
      ¬Fin15AnchoredAtom3419 chi ∧
      ¬Fin15AnchoredAtom3420 chi ∧
      ¬Fin15AnchoredAtom3429 chi ∧
      ¬Fin15AnchoredAtom3454 chi ∧
      ¬Fin15AnchoredAtom3489 chi ∧
      ¬Fin15AnchoredAtom4454 chi ∧
      ¬Fin15AnchoredAtom4455 chi ∧
      ¬Fin15AnchoredAtom4464 chi ∧
      ¬Fin15AnchoredAtom4489 chi ∧
      ¬Fin15AnchoredAtom4524 chi ∧
      ¬Fin15AnchoredAtom4720 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 6, 7, 9, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13011
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1951 Fin15AnchoredAtom1953 Fin15AnchoredAtom1956
    Fin15AnchoredAtom1957 Fin15AnchoredAtom1960 Fin15AnchoredAtom1963 Fin15AnchoredAtom1964
    Fin15AnchoredAtom1974 Fin15AnchoredAtom1975 Fin15AnchoredAtom1984 Fin15AnchoredAtom2024
    Fin15AnchoredAtom2027 Fin15AnchoredAtom2028 Fin15AnchoredAtom2038 Fin15AnchoredAtom2039
    Fin15AnchoredAtom2048 Fin15AnchoredAtom2059 Fin15AnchoredAtom2060 Fin15AnchoredAtom2069
    Fin15AnchoredAtom2094 Fin15AnchoredAtom2529 Fin15AnchoredAtom2532 Fin15AnchoredAtom2533
    Fin15AnchoredAtom2543 Fin15AnchoredAtom2544 Fin15AnchoredAtom2553 Fin15AnchoredAtom2564
    Fin15AnchoredAtom2565 Fin15AnchoredAtom2574 Fin15AnchoredAtom2599 Fin15AnchoredAtom2704
    Fin15AnchoredAtom2705 Fin15AnchoredAtom2714 Fin15AnchoredAtom2739 Fin15AnchoredAtom2774
    Fin15AnchoredAtom3244 Fin15AnchoredAtom3247 Fin15AnchoredAtom3248 Fin15AnchoredAtom3258
    Fin15AnchoredAtom3259 Fin15AnchoredAtom3268 Fin15AnchoredAtom3279 Fin15AnchoredAtom3280
    Fin15AnchoredAtom3289 Fin15AnchoredAtom3314 Fin15AnchoredAtom3419 Fin15AnchoredAtom3420
    Fin15AnchoredAtom3429 Fin15AnchoredAtom3454 Fin15AnchoredAtom3489 Fin15AnchoredAtom4454
    Fin15AnchoredAtom4455 Fin15AnchoredAtom4464 Fin15AnchoredAtom4489 Fin15AnchoredAtom4524
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

theorem fin15Anchored_clause31026 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom1976 chi ∧
      ¬Fin15AnchoredAtom1985 chi ∧
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
      ¬Fin15AnchoredAtom2529 chi ∧
      ¬Fin15AnchoredAtom2532 chi ∧
      ¬Fin15AnchoredAtom2534 chi ∧
      ¬Fin15AnchoredAtom2543 chi ∧
      ¬Fin15AnchoredAtom2545 chi ∧
      ¬Fin15AnchoredAtom2554 chi ∧
      ¬Fin15AnchoredAtom2564 chi ∧
      ¬Fin15AnchoredAtom2566 chi ∧
      ¬Fin15AnchoredAtom2575 chi ∧
      ¬Fin15AnchoredAtom2600 chi ∧
      ¬Fin15AnchoredAtom2704 chi ∧
      ¬Fin15AnchoredAtom2706 chi ∧
      ¬Fin15AnchoredAtom2715 chi ∧
      ¬Fin15AnchoredAtom2740 chi ∧
      ¬Fin15AnchoredAtom2775 chi ∧
      ¬Fin15AnchoredAtom3244 chi ∧
      ¬Fin15AnchoredAtom3247 chi ∧
      ¬Fin15AnchoredAtom3249 chi ∧
      ¬Fin15AnchoredAtom3258 chi ∧
      ¬Fin15AnchoredAtom3260 chi ∧
      ¬Fin15AnchoredAtom3269 chi ∧
      ¬Fin15AnchoredAtom3279 chi ∧
      ¬Fin15AnchoredAtom3281 chi ∧
      ¬Fin15AnchoredAtom3290 chi ∧
      ¬Fin15AnchoredAtom3315 chi ∧
      ¬Fin15AnchoredAtom3419 chi ∧
      ¬Fin15AnchoredAtom3421 chi ∧
      ¬Fin15AnchoredAtom3430 chi ∧
      ¬Fin15AnchoredAtom3455 chi ∧
      ¬Fin15AnchoredAtom3490 chi ∧
      ¬Fin15AnchoredAtom4454 chi ∧
      ¬Fin15AnchoredAtom4456 chi ∧
      ¬Fin15AnchoredAtom4465 chi ∧
      ¬Fin15AnchoredAtom4490 chi ∧
      ¬Fin15AnchoredAtom4525 chi ∧
      ¬Fin15AnchoredAtom4721 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 6, 7, 9, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21203
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1951 Fin15AnchoredAtom1953 Fin15AnchoredAtom1956
    Fin15AnchoredAtom1958 Fin15AnchoredAtom1960 Fin15AnchoredAtom1963 Fin15AnchoredAtom1965
    Fin15AnchoredAtom1974 Fin15AnchoredAtom1976 Fin15AnchoredAtom1985 Fin15AnchoredAtom2024
    Fin15AnchoredAtom2027 Fin15AnchoredAtom2029 Fin15AnchoredAtom2038 Fin15AnchoredAtom2040
    Fin15AnchoredAtom2049 Fin15AnchoredAtom2059 Fin15AnchoredAtom2061 Fin15AnchoredAtom2070
    Fin15AnchoredAtom2095 Fin15AnchoredAtom2529 Fin15AnchoredAtom2532 Fin15AnchoredAtom2534
    Fin15AnchoredAtom2543 Fin15AnchoredAtom2545 Fin15AnchoredAtom2554 Fin15AnchoredAtom2564
    Fin15AnchoredAtom2566 Fin15AnchoredAtom2575 Fin15AnchoredAtom2600 Fin15AnchoredAtom2704
    Fin15AnchoredAtom2706 Fin15AnchoredAtom2715 Fin15AnchoredAtom2740 Fin15AnchoredAtom2775
    Fin15AnchoredAtom3244 Fin15AnchoredAtom3247 Fin15AnchoredAtom3249 Fin15AnchoredAtom3258
    Fin15AnchoredAtom3260 Fin15AnchoredAtom3269 Fin15AnchoredAtom3279 Fin15AnchoredAtom3281
    Fin15AnchoredAtom3290 Fin15AnchoredAtom3315 Fin15AnchoredAtom3419 Fin15AnchoredAtom3421
    Fin15AnchoredAtom3430 Fin15AnchoredAtom3455 Fin15AnchoredAtom3490 Fin15AnchoredAtom4454
    Fin15AnchoredAtom4456 Fin15AnchoredAtom4465 Fin15AnchoredAtom4490 Fin15AnchoredAtom4525
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

theorem fin15Anchored_clause31027 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom1976 chi ∧
      ¬Fin15AnchoredAtom1986 chi ∧
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
      ¬Fin15AnchoredAtom2529 chi ∧
      ¬Fin15AnchoredAtom2533 chi ∧
      ¬Fin15AnchoredAtom2534 chi ∧
      ¬Fin15AnchoredAtom2544 chi ∧
      ¬Fin15AnchoredAtom2545 chi ∧
      ¬Fin15AnchoredAtom2555 chi ∧
      ¬Fin15AnchoredAtom2565 chi ∧
      ¬Fin15AnchoredAtom2566 chi ∧
      ¬Fin15AnchoredAtom2576 chi ∧
      ¬Fin15AnchoredAtom2601 chi ∧
      ¬Fin15AnchoredAtom2705 chi ∧
      ¬Fin15AnchoredAtom2706 chi ∧
      ¬Fin15AnchoredAtom2716 chi ∧
      ¬Fin15AnchoredAtom2741 chi ∧
      ¬Fin15AnchoredAtom2776 chi ∧
      ¬Fin15AnchoredAtom3244 chi ∧
      ¬Fin15AnchoredAtom3248 chi ∧
      ¬Fin15AnchoredAtom3249 chi ∧
      ¬Fin15AnchoredAtom3259 chi ∧
      ¬Fin15AnchoredAtom3260 chi ∧
      ¬Fin15AnchoredAtom3270 chi ∧
      ¬Fin15AnchoredAtom3280 chi ∧
      ¬Fin15AnchoredAtom3281 chi ∧
      ¬Fin15AnchoredAtom3291 chi ∧
      ¬Fin15AnchoredAtom3316 chi ∧
      ¬Fin15AnchoredAtom3420 chi ∧
      ¬Fin15AnchoredAtom3421 chi ∧
      ¬Fin15AnchoredAtom3431 chi ∧
      ¬Fin15AnchoredAtom3456 chi ∧
      ¬Fin15AnchoredAtom3491 chi ∧
      ¬Fin15AnchoredAtom4455 chi ∧
      ¬Fin15AnchoredAtom4456 chi ∧
      ¬Fin15AnchoredAtom4466 chi ∧
      ¬Fin15AnchoredAtom4491 chi ∧
      ¬Fin15AnchoredAtom4526 chi ∧
      ¬Fin15AnchoredAtom4722 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 6, 7, 9, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25299
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1951 Fin15AnchoredAtom1953 Fin15AnchoredAtom1957
    Fin15AnchoredAtom1958 Fin15AnchoredAtom1960 Fin15AnchoredAtom1964 Fin15AnchoredAtom1965
    Fin15AnchoredAtom1975 Fin15AnchoredAtom1976 Fin15AnchoredAtom1986 Fin15AnchoredAtom2024
    Fin15AnchoredAtom2028 Fin15AnchoredAtom2029 Fin15AnchoredAtom2039 Fin15AnchoredAtom2040
    Fin15AnchoredAtom2050 Fin15AnchoredAtom2060 Fin15AnchoredAtom2061 Fin15AnchoredAtom2071
    Fin15AnchoredAtom2096 Fin15AnchoredAtom2529 Fin15AnchoredAtom2533 Fin15AnchoredAtom2534
    Fin15AnchoredAtom2544 Fin15AnchoredAtom2545 Fin15AnchoredAtom2555 Fin15AnchoredAtom2565
    Fin15AnchoredAtom2566 Fin15AnchoredAtom2576 Fin15AnchoredAtom2601 Fin15AnchoredAtom2705
    Fin15AnchoredAtom2706 Fin15AnchoredAtom2716 Fin15AnchoredAtom2741 Fin15AnchoredAtom2776
    Fin15AnchoredAtom3244 Fin15AnchoredAtom3248 Fin15AnchoredAtom3249 Fin15AnchoredAtom3259
    Fin15AnchoredAtom3260 Fin15AnchoredAtom3270 Fin15AnchoredAtom3280 Fin15AnchoredAtom3281
    Fin15AnchoredAtom3291 Fin15AnchoredAtom3316 Fin15AnchoredAtom3420 Fin15AnchoredAtom3421
    Fin15AnchoredAtom3431 Fin15AnchoredAtom3456 Fin15AnchoredAtom3491 Fin15AnchoredAtom4455
    Fin15AnchoredAtom4456 Fin15AnchoredAtom4466 Fin15AnchoredAtom4491 Fin15AnchoredAtom4526
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

theorem fin15Anchored_clause31028 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom1955 chi ∧
      ¬Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom1962 chi ∧
      ¬Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom1977 chi ∧
      ¬Fin15AnchoredAtom1978 chi ∧
      ¬Fin15AnchoredAtom1981 chi ∧
      ¬Fin15AnchoredAtom2025 chi ∧
      ¬Fin15AnchoredAtom2026 chi ∧
      ¬Fin15AnchoredAtom2027 chi ∧
      ¬Fin15AnchoredAtom2041 chi ∧
      ¬Fin15AnchoredAtom2042 chi ∧
      ¬Fin15AnchoredAtom2045 chi ∧
      ¬Fin15AnchoredAtom2062 chi ∧
      ¬Fin15AnchoredAtom2063 chi ∧
      ¬Fin15AnchoredAtom2066 chi ∧
      ¬Fin15AnchoredAtom2097 chi ∧
      ¬Fin15AnchoredAtom2530 chi ∧
      ¬Fin15AnchoredAtom2531 chi ∧
      ¬Fin15AnchoredAtom2532 chi ∧
      ¬Fin15AnchoredAtom2546 chi ∧
      ¬Fin15AnchoredAtom2547 chi ∧
      ¬Fin15AnchoredAtom2550 chi ∧
      ¬Fin15AnchoredAtom2567 chi ∧
      ¬Fin15AnchoredAtom2568 chi ∧
      ¬Fin15AnchoredAtom2571 chi ∧
      ¬Fin15AnchoredAtom2602 chi ∧
      ¬Fin15AnchoredAtom2707 chi ∧
      ¬Fin15AnchoredAtom2708 chi ∧
      ¬Fin15AnchoredAtom2711 chi ∧
      ¬Fin15AnchoredAtom2742 chi ∧
      ¬Fin15AnchoredAtom2777 chi ∧
      ¬Fin15AnchoredAtom3245 chi ∧
      ¬Fin15AnchoredAtom3246 chi ∧
      ¬Fin15AnchoredAtom3247 chi ∧
      ¬Fin15AnchoredAtom3261 chi ∧
      ¬Fin15AnchoredAtom3262 chi ∧
      ¬Fin15AnchoredAtom3265 chi ∧
      ¬Fin15AnchoredAtom3282 chi ∧
      ¬Fin15AnchoredAtom3283 chi ∧
      ¬Fin15AnchoredAtom3286 chi ∧
      ¬Fin15AnchoredAtom3317 chi ∧
      ¬Fin15AnchoredAtom3422 chi ∧
      ¬Fin15AnchoredAtom3423 chi ∧
      ¬Fin15AnchoredAtom3426 chi ∧
      ¬Fin15AnchoredAtom3457 chi ∧
      ¬Fin15AnchoredAtom3492 chi ∧
      ¬Fin15AnchoredAtom4457 chi ∧
      ¬Fin15AnchoredAtom4458 chi ∧
      ¬Fin15AnchoredAtom4461 chi ∧
      ¬Fin15AnchoredAtom4492 chi ∧
      ¬Fin15AnchoredAtom4527 chi ∧
      ¬Fin15AnchoredAtom4723 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 6, 7, 10, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask07379
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1951 Fin15AnchoredAtom1954 Fin15AnchoredAtom1955
    Fin15AnchoredAtom1956 Fin15AnchoredAtom1961 Fin15AnchoredAtom1962 Fin15AnchoredAtom1963
    Fin15AnchoredAtom1977 Fin15AnchoredAtom1978 Fin15AnchoredAtom1981 Fin15AnchoredAtom2025
    Fin15AnchoredAtom2026 Fin15AnchoredAtom2027 Fin15AnchoredAtom2041 Fin15AnchoredAtom2042
    Fin15AnchoredAtom2045 Fin15AnchoredAtom2062 Fin15AnchoredAtom2063 Fin15AnchoredAtom2066
    Fin15AnchoredAtom2097 Fin15AnchoredAtom2530 Fin15AnchoredAtom2531 Fin15AnchoredAtom2532
    Fin15AnchoredAtom2546 Fin15AnchoredAtom2547 Fin15AnchoredAtom2550 Fin15AnchoredAtom2567
    Fin15AnchoredAtom2568 Fin15AnchoredAtom2571 Fin15AnchoredAtom2602 Fin15AnchoredAtom2707
    Fin15AnchoredAtom2708 Fin15AnchoredAtom2711 Fin15AnchoredAtom2742 Fin15AnchoredAtom2777
    Fin15AnchoredAtom3245 Fin15AnchoredAtom3246 Fin15AnchoredAtom3247 Fin15AnchoredAtom3261
    Fin15AnchoredAtom3262 Fin15AnchoredAtom3265 Fin15AnchoredAtom3282 Fin15AnchoredAtom3283
    Fin15AnchoredAtom3286 Fin15AnchoredAtom3317 Fin15AnchoredAtom3422 Fin15AnchoredAtom3423
    Fin15AnchoredAtom3426 Fin15AnchoredAtom3457 Fin15AnchoredAtom3492 Fin15AnchoredAtom4457
    Fin15AnchoredAtom4458 Fin15AnchoredAtom4461 Fin15AnchoredAtom4492 Fin15AnchoredAtom4527
    Fin15AnchoredAtom4723 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31029 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom1978 chi ∧
      ¬Fin15AnchoredAtom1979 chi ∧
      ¬Fin15AnchoredAtom1984 chi ∧
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
      ¬Fin15AnchoredAtom2530 chi ∧
      ¬Fin15AnchoredAtom2532 chi ∧
      ¬Fin15AnchoredAtom2533 chi ∧
      ¬Fin15AnchoredAtom2547 chi ∧
      ¬Fin15AnchoredAtom2548 chi ∧
      ¬Fin15AnchoredAtom2553 chi ∧
      ¬Fin15AnchoredAtom2568 chi ∧
      ¬Fin15AnchoredAtom2569 chi ∧
      ¬Fin15AnchoredAtom2574 chi ∧
      ¬Fin15AnchoredAtom2605 chi ∧
      ¬Fin15AnchoredAtom2708 chi ∧
      ¬Fin15AnchoredAtom2709 chi ∧
      ¬Fin15AnchoredAtom2714 chi ∧
      ¬Fin15AnchoredAtom2745 chi ∧
      ¬Fin15AnchoredAtom2780 chi ∧
      ¬Fin15AnchoredAtom3245 chi ∧
      ¬Fin15AnchoredAtom3247 chi ∧
      ¬Fin15AnchoredAtom3248 chi ∧
      ¬Fin15AnchoredAtom3262 chi ∧
      ¬Fin15AnchoredAtom3263 chi ∧
      ¬Fin15AnchoredAtom3268 chi ∧
      ¬Fin15AnchoredAtom3283 chi ∧
      ¬Fin15AnchoredAtom3284 chi ∧
      ¬Fin15AnchoredAtom3289 chi ∧
      ¬Fin15AnchoredAtom3320 chi ∧
      ¬Fin15AnchoredAtom3423 chi ∧
      ¬Fin15AnchoredAtom3424 chi ∧
      ¬Fin15AnchoredAtom3429 chi ∧
      ¬Fin15AnchoredAtom3460 chi ∧
      ¬Fin15AnchoredAtom3495 chi ∧
      ¬Fin15AnchoredAtom4458 chi ∧
      ¬Fin15AnchoredAtom4459 chi ∧
      ¬Fin15AnchoredAtom4464 chi ∧
      ¬Fin15AnchoredAtom4495 chi ∧
      ¬Fin15AnchoredAtom4530 chi ∧
      ¬Fin15AnchoredAtom4726 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 6, 7, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13523
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1951 Fin15AnchoredAtom1954 Fin15AnchoredAtom1956
    Fin15AnchoredAtom1957 Fin15AnchoredAtom1961 Fin15AnchoredAtom1963 Fin15AnchoredAtom1964
    Fin15AnchoredAtom1978 Fin15AnchoredAtom1979 Fin15AnchoredAtom1984 Fin15AnchoredAtom2025
    Fin15AnchoredAtom2027 Fin15AnchoredAtom2028 Fin15AnchoredAtom2042 Fin15AnchoredAtom2043
    Fin15AnchoredAtom2048 Fin15AnchoredAtom2063 Fin15AnchoredAtom2064 Fin15AnchoredAtom2069
    Fin15AnchoredAtom2100 Fin15AnchoredAtom2530 Fin15AnchoredAtom2532 Fin15AnchoredAtom2533
    Fin15AnchoredAtom2547 Fin15AnchoredAtom2548 Fin15AnchoredAtom2553 Fin15AnchoredAtom2568
    Fin15AnchoredAtom2569 Fin15AnchoredAtom2574 Fin15AnchoredAtom2605 Fin15AnchoredAtom2708
    Fin15AnchoredAtom2709 Fin15AnchoredAtom2714 Fin15AnchoredAtom2745 Fin15AnchoredAtom2780
    Fin15AnchoredAtom3245 Fin15AnchoredAtom3247 Fin15AnchoredAtom3248 Fin15AnchoredAtom3262
    Fin15AnchoredAtom3263 Fin15AnchoredAtom3268 Fin15AnchoredAtom3283 Fin15AnchoredAtom3284
    Fin15AnchoredAtom3289 Fin15AnchoredAtom3320 Fin15AnchoredAtom3423 Fin15AnchoredAtom3424
    Fin15AnchoredAtom3429 Fin15AnchoredAtom3460 Fin15AnchoredAtom3495 Fin15AnchoredAtom4458
    Fin15AnchoredAtom4459 Fin15AnchoredAtom4464 Fin15AnchoredAtom4495 Fin15AnchoredAtom4530
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

theorem fin15Anchored_clause31030 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom1978 chi ∧
      ¬Fin15AnchoredAtom1980 chi ∧
      ¬Fin15AnchoredAtom1985 chi ∧
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
      ¬Fin15AnchoredAtom2530 chi ∧
      ¬Fin15AnchoredAtom2532 chi ∧
      ¬Fin15AnchoredAtom2534 chi ∧
      ¬Fin15AnchoredAtom2547 chi ∧
      ¬Fin15AnchoredAtom2549 chi ∧
      ¬Fin15AnchoredAtom2554 chi ∧
      ¬Fin15AnchoredAtom2568 chi ∧
      ¬Fin15AnchoredAtom2570 chi ∧
      ¬Fin15AnchoredAtom2575 chi ∧
      ¬Fin15AnchoredAtom2606 chi ∧
      ¬Fin15AnchoredAtom2708 chi ∧
      ¬Fin15AnchoredAtom2710 chi ∧
      ¬Fin15AnchoredAtom2715 chi ∧
      ¬Fin15AnchoredAtom2746 chi ∧
      ¬Fin15AnchoredAtom2781 chi ∧
      ¬Fin15AnchoredAtom3245 chi ∧
      ¬Fin15AnchoredAtom3247 chi ∧
      ¬Fin15AnchoredAtom3249 chi ∧
      ¬Fin15AnchoredAtom3262 chi ∧
      ¬Fin15AnchoredAtom3264 chi ∧
      ¬Fin15AnchoredAtom3269 chi ∧
      ¬Fin15AnchoredAtom3283 chi ∧
      ¬Fin15AnchoredAtom3285 chi ∧
      ¬Fin15AnchoredAtom3290 chi ∧
      ¬Fin15AnchoredAtom3321 chi ∧
      ¬Fin15AnchoredAtom3423 chi ∧
      ¬Fin15AnchoredAtom3425 chi ∧
      ¬Fin15AnchoredAtom3430 chi ∧
      ¬Fin15AnchoredAtom3461 chi ∧
      ¬Fin15AnchoredAtom3496 chi ∧
      ¬Fin15AnchoredAtom4458 chi ∧
      ¬Fin15AnchoredAtom4460 chi ∧
      ¬Fin15AnchoredAtom4465 chi ∧
      ¬Fin15AnchoredAtom4496 chi ∧
      ¬Fin15AnchoredAtom4531 chi ∧
      ¬Fin15AnchoredAtom4727 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 6, 7, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21715
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1951 Fin15AnchoredAtom1954 Fin15AnchoredAtom1956
    Fin15AnchoredAtom1958 Fin15AnchoredAtom1961 Fin15AnchoredAtom1963 Fin15AnchoredAtom1965
    Fin15AnchoredAtom1978 Fin15AnchoredAtom1980 Fin15AnchoredAtom1985 Fin15AnchoredAtom2025
    Fin15AnchoredAtom2027 Fin15AnchoredAtom2029 Fin15AnchoredAtom2042 Fin15AnchoredAtom2044
    Fin15AnchoredAtom2049 Fin15AnchoredAtom2063 Fin15AnchoredAtom2065 Fin15AnchoredAtom2070
    Fin15AnchoredAtom2101 Fin15AnchoredAtom2530 Fin15AnchoredAtom2532 Fin15AnchoredAtom2534
    Fin15AnchoredAtom2547 Fin15AnchoredAtom2549 Fin15AnchoredAtom2554 Fin15AnchoredAtom2568
    Fin15AnchoredAtom2570 Fin15AnchoredAtom2575 Fin15AnchoredAtom2606 Fin15AnchoredAtom2708
    Fin15AnchoredAtom2710 Fin15AnchoredAtom2715 Fin15AnchoredAtom2746 Fin15AnchoredAtom2781
    Fin15AnchoredAtom3245 Fin15AnchoredAtom3247 Fin15AnchoredAtom3249 Fin15AnchoredAtom3262
    Fin15AnchoredAtom3264 Fin15AnchoredAtom3269 Fin15AnchoredAtom3283 Fin15AnchoredAtom3285
    Fin15AnchoredAtom3290 Fin15AnchoredAtom3321 Fin15AnchoredAtom3423 Fin15AnchoredAtom3425
    Fin15AnchoredAtom3430 Fin15AnchoredAtom3461 Fin15AnchoredAtom3496 Fin15AnchoredAtom4458
    Fin15AnchoredAtom4460 Fin15AnchoredAtom4465 Fin15AnchoredAtom4496 Fin15AnchoredAtom4531
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

theorem fin15Anchored_clause31031 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom1979 chi ∧
      ¬Fin15AnchoredAtom1980 chi ∧
      ¬Fin15AnchoredAtom1986 chi ∧
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
      ¬Fin15AnchoredAtom2530 chi ∧
      ¬Fin15AnchoredAtom2533 chi ∧
      ¬Fin15AnchoredAtom2534 chi ∧
      ¬Fin15AnchoredAtom2548 chi ∧
      ¬Fin15AnchoredAtom2549 chi ∧
      ¬Fin15AnchoredAtom2555 chi ∧
      ¬Fin15AnchoredAtom2569 chi ∧
      ¬Fin15AnchoredAtom2570 chi ∧
      ¬Fin15AnchoredAtom2576 chi ∧
      ¬Fin15AnchoredAtom2607 chi ∧
      ¬Fin15AnchoredAtom2709 chi ∧
      ¬Fin15AnchoredAtom2710 chi ∧
      ¬Fin15AnchoredAtom2716 chi ∧
      ¬Fin15AnchoredAtom2747 chi ∧
      ¬Fin15AnchoredAtom2782 chi ∧
      ¬Fin15AnchoredAtom3245 chi ∧
      ¬Fin15AnchoredAtom3248 chi ∧
      ¬Fin15AnchoredAtom3249 chi ∧
      ¬Fin15AnchoredAtom3263 chi ∧
      ¬Fin15AnchoredAtom3264 chi ∧
      ¬Fin15AnchoredAtom3270 chi ∧
      ¬Fin15AnchoredAtom3284 chi ∧
      ¬Fin15AnchoredAtom3285 chi ∧
      ¬Fin15AnchoredAtom3291 chi ∧
      ¬Fin15AnchoredAtom3322 chi ∧
      ¬Fin15AnchoredAtom3424 chi ∧
      ¬Fin15AnchoredAtom3425 chi ∧
      ¬Fin15AnchoredAtom3431 chi ∧
      ¬Fin15AnchoredAtom3462 chi ∧
      ¬Fin15AnchoredAtom3497 chi ∧
      ¬Fin15AnchoredAtom4459 chi ∧
      ¬Fin15AnchoredAtom4460 chi ∧
      ¬Fin15AnchoredAtom4466 chi ∧
      ¬Fin15AnchoredAtom4497 chi ∧
      ¬Fin15AnchoredAtom4532 chi ∧
      ¬Fin15AnchoredAtom4728 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 6, 7, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25811
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1951 Fin15AnchoredAtom1954 Fin15AnchoredAtom1957
    Fin15AnchoredAtom1958 Fin15AnchoredAtom1961 Fin15AnchoredAtom1964 Fin15AnchoredAtom1965
    Fin15AnchoredAtom1979 Fin15AnchoredAtom1980 Fin15AnchoredAtom1986 Fin15AnchoredAtom2025
    Fin15AnchoredAtom2028 Fin15AnchoredAtom2029 Fin15AnchoredAtom2043 Fin15AnchoredAtom2044
    Fin15AnchoredAtom2050 Fin15AnchoredAtom2064 Fin15AnchoredAtom2065 Fin15AnchoredAtom2071
    Fin15AnchoredAtom2102 Fin15AnchoredAtom2530 Fin15AnchoredAtom2533 Fin15AnchoredAtom2534
    Fin15AnchoredAtom2548 Fin15AnchoredAtom2549 Fin15AnchoredAtom2555 Fin15AnchoredAtom2569
    Fin15AnchoredAtom2570 Fin15AnchoredAtom2576 Fin15AnchoredAtom2607 Fin15AnchoredAtom2709
    Fin15AnchoredAtom2710 Fin15AnchoredAtom2716 Fin15AnchoredAtom2747 Fin15AnchoredAtom2782
    Fin15AnchoredAtom3245 Fin15AnchoredAtom3248 Fin15AnchoredAtom3249 Fin15AnchoredAtom3263
    Fin15AnchoredAtom3264 Fin15AnchoredAtom3270 Fin15AnchoredAtom3284 Fin15AnchoredAtom3285
    Fin15AnchoredAtom3291 Fin15AnchoredAtom3322 Fin15AnchoredAtom3424 Fin15AnchoredAtom3425
    Fin15AnchoredAtom3431 Fin15AnchoredAtom3462 Fin15AnchoredAtom3497 Fin15AnchoredAtom4459
    Fin15AnchoredAtom4460 Fin15AnchoredAtom4466 Fin15AnchoredAtom4497 Fin15AnchoredAtom4532
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

theorem fin15Anchored_clause31032 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom1984 chi ∧
      ¬Fin15AnchoredAtom1985 chi ∧
      ¬Fin15AnchoredAtom1986 chi ∧
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
      ¬Fin15AnchoredAtom2532 chi ∧
      ¬Fin15AnchoredAtom2533 chi ∧
      ¬Fin15AnchoredAtom2534 chi ∧
      ¬Fin15AnchoredAtom2553 chi ∧
      ¬Fin15AnchoredAtom2554 chi ∧
      ¬Fin15AnchoredAtom2555 chi ∧
      ¬Fin15AnchoredAtom2574 chi ∧
      ¬Fin15AnchoredAtom2575 chi ∧
      ¬Fin15AnchoredAtom2576 chi ∧
      ¬Fin15AnchoredAtom2611 chi ∧
      ¬Fin15AnchoredAtom2714 chi ∧
      ¬Fin15AnchoredAtom2715 chi ∧
      ¬Fin15AnchoredAtom2716 chi ∧
      ¬Fin15AnchoredAtom2751 chi ∧
      ¬Fin15AnchoredAtom2786 chi ∧
      ¬Fin15AnchoredAtom3247 chi ∧
      ¬Fin15AnchoredAtom3248 chi ∧
      ¬Fin15AnchoredAtom3249 chi ∧
      ¬Fin15AnchoredAtom3268 chi ∧
      ¬Fin15AnchoredAtom3269 chi ∧
      ¬Fin15AnchoredAtom3270 chi ∧
      ¬Fin15AnchoredAtom3289 chi ∧
      ¬Fin15AnchoredAtom3290 chi ∧
      ¬Fin15AnchoredAtom3291 chi ∧
      ¬Fin15AnchoredAtom3326 chi ∧
      ¬Fin15AnchoredAtom3429 chi ∧
      ¬Fin15AnchoredAtom3430 chi ∧
      ¬Fin15AnchoredAtom3431 chi ∧
      ¬Fin15AnchoredAtom3466 chi ∧
      ¬Fin15AnchoredAtom3501 chi ∧
      ¬Fin15AnchoredAtom4464 chi ∧
      ¬Fin15AnchoredAtom4465 chi ∧
      ¬Fin15AnchoredAtom4466 chi ∧
      ¬Fin15AnchoredAtom4501 chi ∧
      ¬Fin15AnchoredAtom4536 chi ∧
      ¬Fin15AnchoredAtom4732 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 6, 7, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask28883
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1951 Fin15AnchoredAtom1956 Fin15AnchoredAtom1957
    Fin15AnchoredAtom1958 Fin15AnchoredAtom1963 Fin15AnchoredAtom1964 Fin15AnchoredAtom1965
    Fin15AnchoredAtom1984 Fin15AnchoredAtom1985 Fin15AnchoredAtom1986 Fin15AnchoredAtom2027
    Fin15AnchoredAtom2028 Fin15AnchoredAtom2029 Fin15AnchoredAtom2048 Fin15AnchoredAtom2049
    Fin15AnchoredAtom2050 Fin15AnchoredAtom2069 Fin15AnchoredAtom2070 Fin15AnchoredAtom2071
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2532 Fin15AnchoredAtom2533 Fin15AnchoredAtom2534
    Fin15AnchoredAtom2553 Fin15AnchoredAtom2554 Fin15AnchoredAtom2555 Fin15AnchoredAtom2574
    Fin15AnchoredAtom2575 Fin15AnchoredAtom2576 Fin15AnchoredAtom2611 Fin15AnchoredAtom2714
    Fin15AnchoredAtom2715 Fin15AnchoredAtom2716 Fin15AnchoredAtom2751 Fin15AnchoredAtom2786
    Fin15AnchoredAtom3247 Fin15AnchoredAtom3248 Fin15AnchoredAtom3249 Fin15AnchoredAtom3268
    Fin15AnchoredAtom3269 Fin15AnchoredAtom3270 Fin15AnchoredAtom3289 Fin15AnchoredAtom3290
    Fin15AnchoredAtom3291 Fin15AnchoredAtom3326 Fin15AnchoredAtom3429 Fin15AnchoredAtom3430
    Fin15AnchoredAtom3431 Fin15AnchoredAtom3466 Fin15AnchoredAtom3501 Fin15AnchoredAtom4464
    Fin15AnchoredAtom4465 Fin15AnchoredAtom4466 Fin15AnchoredAtom4501 Fin15AnchoredAtom4536
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

theorem fin15Anchored_clause31033 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1952 chi ∧
      ¬Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom1966 chi ∧
      ¬Fin15AnchoredAtom1967 chi ∧
      ¬Fin15AnchoredAtom1969 chi ∧
      ¬Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom1978 chi ∧
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
      ¬Fin15AnchoredAtom2535 chi ∧
      ¬Fin15AnchoredAtom2536 chi ∧
      ¬Fin15AnchoredAtom2538 chi ∧
      ¬Fin15AnchoredAtom2541 chi ∧
      ¬Fin15AnchoredAtom2543 chi ∧
      ¬Fin15AnchoredAtom2547 chi ∧
      ¬Fin15AnchoredAtom2577 chi ∧
      ¬Fin15AnchoredAtom2579 chi ∧
      ¬Fin15AnchoredAtom2583 chi ∧
      ¬Fin15AnchoredAtom2593 chi ∧
      ¬Fin15AnchoredAtom2717 chi ∧
      ¬Fin15AnchoredAtom2719 chi ∧
      ¬Fin15AnchoredAtom2723 chi ∧
      ¬Fin15AnchoredAtom2733 chi ∧
      ¬Fin15AnchoredAtom2788 chi ∧
      ¬Fin15AnchoredAtom3250 chi ∧
      ¬Fin15AnchoredAtom3251 chi ∧
      ¬Fin15AnchoredAtom3253 chi ∧
      ¬Fin15AnchoredAtom3256 chi ∧
      ¬Fin15AnchoredAtom3258 chi ∧
      ¬Fin15AnchoredAtom3262 chi ∧
      ¬Fin15AnchoredAtom3292 chi ∧
      ¬Fin15AnchoredAtom3294 chi ∧
      ¬Fin15AnchoredAtom3298 chi ∧
      ¬Fin15AnchoredAtom3308 chi ∧
      ¬Fin15AnchoredAtom3432 chi ∧
      ¬Fin15AnchoredAtom3434 chi ∧
      ¬Fin15AnchoredAtom3438 chi ∧
      ¬Fin15AnchoredAtom3448 chi ∧
      ¬Fin15AnchoredAtom3503 chi ∧
      ¬Fin15AnchoredAtom4467 chi ∧
      ¬Fin15AnchoredAtom4469 chi ∧
      ¬Fin15AnchoredAtom4473 chi ∧
      ¬Fin15AnchoredAtom4483 chi ∧
      ¬Fin15AnchoredAtom4538 chi ∧
      ¬Fin15AnchoredAtom4734 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 6, 8, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05971
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1952 Fin15AnchoredAtom1953 Fin15AnchoredAtom1954
    Fin15AnchoredAtom1956 Fin15AnchoredAtom1966 Fin15AnchoredAtom1967 Fin15AnchoredAtom1969
    Fin15AnchoredAtom1972 Fin15AnchoredAtom1974 Fin15AnchoredAtom1978 Fin15AnchoredAtom2030
    Fin15AnchoredAtom2031 Fin15AnchoredAtom2033 Fin15AnchoredAtom2036 Fin15AnchoredAtom2038
    Fin15AnchoredAtom2042 Fin15AnchoredAtom2072 Fin15AnchoredAtom2074 Fin15AnchoredAtom2078
    Fin15AnchoredAtom2088 Fin15AnchoredAtom2535 Fin15AnchoredAtom2536 Fin15AnchoredAtom2538
    Fin15AnchoredAtom2541 Fin15AnchoredAtom2543 Fin15AnchoredAtom2547 Fin15AnchoredAtom2577
    Fin15AnchoredAtom2579 Fin15AnchoredAtom2583 Fin15AnchoredAtom2593 Fin15AnchoredAtom2717
    Fin15AnchoredAtom2719 Fin15AnchoredAtom2723 Fin15AnchoredAtom2733 Fin15AnchoredAtom2788
    Fin15AnchoredAtom3250 Fin15AnchoredAtom3251 Fin15AnchoredAtom3253 Fin15AnchoredAtom3256
    Fin15AnchoredAtom3258 Fin15AnchoredAtom3262 Fin15AnchoredAtom3292 Fin15AnchoredAtom3294
    Fin15AnchoredAtom3298 Fin15AnchoredAtom3308 Fin15AnchoredAtom3432 Fin15AnchoredAtom3434
    Fin15AnchoredAtom3438 Fin15AnchoredAtom3448 Fin15AnchoredAtom3503 Fin15AnchoredAtom4467
    Fin15AnchoredAtom4469 Fin15AnchoredAtom4473 Fin15AnchoredAtom4483 Fin15AnchoredAtom4538
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

theorem fin15Anchored_clause31034 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1952 chi ∧
      ¬Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom1966 chi ∧
      ¬Fin15AnchoredAtom1967 chi ∧
      ¬Fin15AnchoredAtom1970 chi ∧
      ¬Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom1979 chi ∧
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
      ¬Fin15AnchoredAtom2535 chi ∧
      ¬Fin15AnchoredAtom2536 chi ∧
      ¬Fin15AnchoredAtom2539 chi ∧
      ¬Fin15AnchoredAtom2541 chi ∧
      ¬Fin15AnchoredAtom2544 chi ∧
      ¬Fin15AnchoredAtom2548 chi ∧
      ¬Fin15AnchoredAtom2577 chi ∧
      ¬Fin15AnchoredAtom2580 chi ∧
      ¬Fin15AnchoredAtom2584 chi ∧
      ¬Fin15AnchoredAtom2594 chi ∧
      ¬Fin15AnchoredAtom2717 chi ∧
      ¬Fin15AnchoredAtom2720 chi ∧
      ¬Fin15AnchoredAtom2724 chi ∧
      ¬Fin15AnchoredAtom2734 chi ∧
      ¬Fin15AnchoredAtom2789 chi ∧
      ¬Fin15AnchoredAtom3250 chi ∧
      ¬Fin15AnchoredAtom3251 chi ∧
      ¬Fin15AnchoredAtom3254 chi ∧
      ¬Fin15AnchoredAtom3256 chi ∧
      ¬Fin15AnchoredAtom3259 chi ∧
      ¬Fin15AnchoredAtom3263 chi ∧
      ¬Fin15AnchoredAtom3292 chi ∧
      ¬Fin15AnchoredAtom3295 chi ∧
      ¬Fin15AnchoredAtom3299 chi ∧
      ¬Fin15AnchoredAtom3309 chi ∧
      ¬Fin15AnchoredAtom3432 chi ∧
      ¬Fin15AnchoredAtom3435 chi ∧
      ¬Fin15AnchoredAtom3439 chi ∧
      ¬Fin15AnchoredAtom3449 chi ∧
      ¬Fin15AnchoredAtom3504 chi ∧
      ¬Fin15AnchoredAtom4467 chi ∧
      ¬Fin15AnchoredAtom4470 chi ∧
      ¬Fin15AnchoredAtom4474 chi ∧
      ¬Fin15AnchoredAtom4484 chi ∧
      ¬Fin15AnchoredAtom4539 chi ∧
      ¬Fin15AnchoredAtom4735 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 6, 8, 9, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask10067
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1952 Fin15AnchoredAtom1953 Fin15AnchoredAtom1954
    Fin15AnchoredAtom1957 Fin15AnchoredAtom1966 Fin15AnchoredAtom1967 Fin15AnchoredAtom1970
    Fin15AnchoredAtom1972 Fin15AnchoredAtom1975 Fin15AnchoredAtom1979 Fin15AnchoredAtom2030
    Fin15AnchoredAtom2031 Fin15AnchoredAtom2034 Fin15AnchoredAtom2036 Fin15AnchoredAtom2039
    Fin15AnchoredAtom2043 Fin15AnchoredAtom2072 Fin15AnchoredAtom2075 Fin15AnchoredAtom2079
    Fin15AnchoredAtom2089 Fin15AnchoredAtom2535 Fin15AnchoredAtom2536 Fin15AnchoredAtom2539
    Fin15AnchoredAtom2541 Fin15AnchoredAtom2544 Fin15AnchoredAtom2548 Fin15AnchoredAtom2577
    Fin15AnchoredAtom2580 Fin15AnchoredAtom2584 Fin15AnchoredAtom2594 Fin15AnchoredAtom2717
    Fin15AnchoredAtom2720 Fin15AnchoredAtom2724 Fin15AnchoredAtom2734 Fin15AnchoredAtom2789
    Fin15AnchoredAtom3250 Fin15AnchoredAtom3251 Fin15AnchoredAtom3254 Fin15AnchoredAtom3256
    Fin15AnchoredAtom3259 Fin15AnchoredAtom3263 Fin15AnchoredAtom3292 Fin15AnchoredAtom3295
    Fin15AnchoredAtom3299 Fin15AnchoredAtom3309 Fin15AnchoredAtom3432 Fin15AnchoredAtom3435
    Fin15AnchoredAtom3439 Fin15AnchoredAtom3449 Fin15AnchoredAtom3504 Fin15AnchoredAtom4467
    Fin15AnchoredAtom4470 Fin15AnchoredAtom4474 Fin15AnchoredAtom4484 Fin15AnchoredAtom4539
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

theorem fin15Anchored_clause31035 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1952 chi ∧
      ¬Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom1966 chi ∧
      ¬Fin15AnchoredAtom1969 chi ∧
      ¬Fin15AnchoredAtom1971 chi ∧
      ¬Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom1976 chi ∧
      ¬Fin15AnchoredAtom1985 chi ∧
      ¬Fin15AnchoredAtom2030 chi ∧
      ¬Fin15AnchoredAtom2033 chi ∧
      ¬Fin15AnchoredAtom2035 chi ∧
      ¬Fin15AnchoredAtom2038 chi ∧
      ¬Fin15AnchoredAtom2040 chi ∧
      ¬Fin15AnchoredAtom2049 chi ∧
      ¬Fin15AnchoredAtom2074 chi ∧
      ¬Fin15AnchoredAtom2076 chi ∧
      ¬Fin15AnchoredAtom2085 chi ∧
      ¬Fin15AnchoredAtom2095 chi ∧
      ¬Fin15AnchoredAtom2535 chi ∧
      ¬Fin15AnchoredAtom2538 chi ∧
      ¬Fin15AnchoredAtom2540 chi ∧
      ¬Fin15AnchoredAtom2543 chi ∧
      ¬Fin15AnchoredAtom2545 chi ∧
      ¬Fin15AnchoredAtom2554 chi ∧
      ¬Fin15AnchoredAtom2579 chi ∧
      ¬Fin15AnchoredAtom2581 chi ∧
      ¬Fin15AnchoredAtom2590 chi ∧
      ¬Fin15AnchoredAtom2600 chi ∧
      ¬Fin15AnchoredAtom2719 chi ∧
      ¬Fin15AnchoredAtom2721 chi ∧
      ¬Fin15AnchoredAtom2730 chi ∧
      ¬Fin15AnchoredAtom2740 chi ∧
      ¬Fin15AnchoredAtom2795 chi ∧
      ¬Fin15AnchoredAtom3250 chi ∧
      ¬Fin15AnchoredAtom3253 chi ∧
      ¬Fin15AnchoredAtom3255 chi ∧
      ¬Fin15AnchoredAtom3258 chi ∧
      ¬Fin15AnchoredAtom3260 chi ∧
      ¬Fin15AnchoredAtom3269 chi ∧
      ¬Fin15AnchoredAtom3294 chi ∧
      ¬Fin15AnchoredAtom3296 chi ∧
      ¬Fin15AnchoredAtom3305 chi ∧
      ¬Fin15AnchoredAtom3315 chi ∧
      ¬Fin15AnchoredAtom3434 chi ∧
      ¬Fin15AnchoredAtom3436 chi ∧
      ¬Fin15AnchoredAtom3445 chi ∧
      ¬Fin15AnchoredAtom3455 chi ∧
      ¬Fin15AnchoredAtom3510 chi ∧
      ¬Fin15AnchoredAtom4469 chi ∧
      ¬Fin15AnchoredAtom4471 chi ∧
      ¬Fin15AnchoredAtom4480 chi ∧
      ¬Fin15AnchoredAtom4490 chi ∧
      ¬Fin15AnchoredAtom4545 chi ∧
      ¬Fin15AnchoredAtom4741 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 6, 8, 9, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21331
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1952 Fin15AnchoredAtom1953 Fin15AnchoredAtom1956
    Fin15AnchoredAtom1958 Fin15AnchoredAtom1966 Fin15AnchoredAtom1969 Fin15AnchoredAtom1971
    Fin15AnchoredAtom1974 Fin15AnchoredAtom1976 Fin15AnchoredAtom1985 Fin15AnchoredAtom2030
    Fin15AnchoredAtom2033 Fin15AnchoredAtom2035 Fin15AnchoredAtom2038 Fin15AnchoredAtom2040
    Fin15AnchoredAtom2049 Fin15AnchoredAtom2074 Fin15AnchoredAtom2076 Fin15AnchoredAtom2085
    Fin15AnchoredAtom2095 Fin15AnchoredAtom2535 Fin15AnchoredAtom2538 Fin15AnchoredAtom2540
    Fin15AnchoredAtom2543 Fin15AnchoredAtom2545 Fin15AnchoredAtom2554 Fin15AnchoredAtom2579
    Fin15AnchoredAtom2581 Fin15AnchoredAtom2590 Fin15AnchoredAtom2600 Fin15AnchoredAtom2719
    Fin15AnchoredAtom2721 Fin15AnchoredAtom2730 Fin15AnchoredAtom2740 Fin15AnchoredAtom2795
    Fin15AnchoredAtom3250 Fin15AnchoredAtom3253 Fin15AnchoredAtom3255 Fin15AnchoredAtom3258
    Fin15AnchoredAtom3260 Fin15AnchoredAtom3269 Fin15AnchoredAtom3294 Fin15AnchoredAtom3296
    Fin15AnchoredAtom3305 Fin15AnchoredAtom3315 Fin15AnchoredAtom3434 Fin15AnchoredAtom3436
    Fin15AnchoredAtom3445 Fin15AnchoredAtom3455 Fin15AnchoredAtom3510 Fin15AnchoredAtom4469
    Fin15AnchoredAtom4471 Fin15AnchoredAtom4480 Fin15AnchoredAtom4490 Fin15AnchoredAtom4545
    Fin15AnchoredAtom4741 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31036 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1952 chi ∧
      ¬Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom1966 chi ∧
      ¬Fin15AnchoredAtom1970 chi ∧
      ¬Fin15AnchoredAtom1971 chi ∧
      ¬Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom1976 chi ∧
      ¬Fin15AnchoredAtom1986 chi ∧
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
      ¬Fin15AnchoredAtom2535 chi ∧
      ¬Fin15AnchoredAtom2539 chi ∧
      ¬Fin15AnchoredAtom2540 chi ∧
      ¬Fin15AnchoredAtom2544 chi ∧
      ¬Fin15AnchoredAtom2545 chi ∧
      ¬Fin15AnchoredAtom2555 chi ∧
      ¬Fin15AnchoredAtom2580 chi ∧
      ¬Fin15AnchoredAtom2581 chi ∧
      ¬Fin15AnchoredAtom2591 chi ∧
      ¬Fin15AnchoredAtom2601 chi ∧
      ¬Fin15AnchoredAtom2720 chi ∧
      ¬Fin15AnchoredAtom2721 chi ∧
      ¬Fin15AnchoredAtom2731 chi ∧
      ¬Fin15AnchoredAtom2741 chi ∧
      ¬Fin15AnchoredAtom2796 chi ∧
      ¬Fin15AnchoredAtom3250 chi ∧
      ¬Fin15AnchoredAtom3254 chi ∧
      ¬Fin15AnchoredAtom3255 chi ∧
      ¬Fin15AnchoredAtom3259 chi ∧
      ¬Fin15AnchoredAtom3260 chi ∧
      ¬Fin15AnchoredAtom3270 chi ∧
      ¬Fin15AnchoredAtom3295 chi ∧
      ¬Fin15AnchoredAtom3296 chi ∧
      ¬Fin15AnchoredAtom3306 chi ∧
      ¬Fin15AnchoredAtom3316 chi ∧
      ¬Fin15AnchoredAtom3435 chi ∧
      ¬Fin15AnchoredAtom3436 chi ∧
      ¬Fin15AnchoredAtom3446 chi ∧
      ¬Fin15AnchoredAtom3456 chi ∧
      ¬Fin15AnchoredAtom3511 chi ∧
      ¬Fin15AnchoredAtom4470 chi ∧
      ¬Fin15AnchoredAtom4471 chi ∧
      ¬Fin15AnchoredAtom4481 chi ∧
      ¬Fin15AnchoredAtom4491 chi ∧
      ¬Fin15AnchoredAtom4546 chi ∧
      ¬Fin15AnchoredAtom4742 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 6, 8, 9, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25427
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1952 Fin15AnchoredAtom1953 Fin15AnchoredAtom1957
    Fin15AnchoredAtom1958 Fin15AnchoredAtom1966 Fin15AnchoredAtom1970 Fin15AnchoredAtom1971
    Fin15AnchoredAtom1975 Fin15AnchoredAtom1976 Fin15AnchoredAtom1986 Fin15AnchoredAtom2030
    Fin15AnchoredAtom2034 Fin15AnchoredAtom2035 Fin15AnchoredAtom2039 Fin15AnchoredAtom2040
    Fin15AnchoredAtom2050 Fin15AnchoredAtom2075 Fin15AnchoredAtom2076 Fin15AnchoredAtom2086
    Fin15AnchoredAtom2096 Fin15AnchoredAtom2535 Fin15AnchoredAtom2539 Fin15AnchoredAtom2540
    Fin15AnchoredAtom2544 Fin15AnchoredAtom2545 Fin15AnchoredAtom2555 Fin15AnchoredAtom2580
    Fin15AnchoredAtom2581 Fin15AnchoredAtom2591 Fin15AnchoredAtom2601 Fin15AnchoredAtom2720
    Fin15AnchoredAtom2721 Fin15AnchoredAtom2731 Fin15AnchoredAtom2741 Fin15AnchoredAtom2796
    Fin15AnchoredAtom3250 Fin15AnchoredAtom3254 Fin15AnchoredAtom3255 Fin15AnchoredAtom3259
    Fin15AnchoredAtom3260 Fin15AnchoredAtom3270 Fin15AnchoredAtom3295 Fin15AnchoredAtom3296
    Fin15AnchoredAtom3306 Fin15AnchoredAtom3316 Fin15AnchoredAtom3435 Fin15AnchoredAtom3436
    Fin15AnchoredAtom3446 Fin15AnchoredAtom3456 Fin15AnchoredAtom3511 Fin15AnchoredAtom4470
    Fin15AnchoredAtom4471 Fin15AnchoredAtom4481 Fin15AnchoredAtom4491 Fin15AnchoredAtom4546
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

theorem fin15Anchored_clause31037 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1952 chi ∧
      ¬Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom1967 chi ∧
      ¬Fin15AnchoredAtom1969 chi ∧
      ¬Fin15AnchoredAtom1970 chi ∧
      ¬Fin15AnchoredAtom1978 chi ∧
      ¬Fin15AnchoredAtom1979 chi ∧
      ¬Fin15AnchoredAtom1984 chi ∧
      ¬Fin15AnchoredAtom2031 chi ∧
      ¬Fin15AnchoredAtom2033 chi ∧
      ¬Fin15AnchoredAtom2034 chi ∧
      ¬Fin15AnchoredAtom2042 chi ∧
      ¬Fin15AnchoredAtom2043 chi ∧
      ¬Fin15AnchoredAtom2048 chi ∧
      ¬Fin15AnchoredAtom2078 chi ∧
      ¬Fin15AnchoredAtom2079 chi ∧
      ¬Fin15AnchoredAtom2084 chi ∧
      ¬Fin15AnchoredAtom2100 chi ∧
      ¬Fin15AnchoredAtom2536 chi ∧
      ¬Fin15AnchoredAtom2538 chi ∧
      ¬Fin15AnchoredAtom2539 chi ∧
      ¬Fin15AnchoredAtom2547 chi ∧
      ¬Fin15AnchoredAtom2548 chi ∧
      ¬Fin15AnchoredAtom2553 chi ∧
      ¬Fin15AnchoredAtom2583 chi ∧
      ¬Fin15AnchoredAtom2584 chi ∧
      ¬Fin15AnchoredAtom2589 chi ∧
      ¬Fin15AnchoredAtom2605 chi ∧
      ¬Fin15AnchoredAtom2723 chi ∧
      ¬Fin15AnchoredAtom2724 chi ∧
      ¬Fin15AnchoredAtom2729 chi ∧
      ¬Fin15AnchoredAtom2745 chi ∧
      ¬Fin15AnchoredAtom2800 chi ∧
      ¬Fin15AnchoredAtom3251 chi ∧
      ¬Fin15AnchoredAtom3253 chi ∧
      ¬Fin15AnchoredAtom3254 chi ∧
      ¬Fin15AnchoredAtom3262 chi ∧
      ¬Fin15AnchoredAtom3263 chi ∧
      ¬Fin15AnchoredAtom3268 chi ∧
      ¬Fin15AnchoredAtom3298 chi ∧
      ¬Fin15AnchoredAtom3299 chi ∧
      ¬Fin15AnchoredAtom3304 chi ∧
      ¬Fin15AnchoredAtom3320 chi ∧
      ¬Fin15AnchoredAtom3438 chi ∧
      ¬Fin15AnchoredAtom3439 chi ∧
      ¬Fin15AnchoredAtom3444 chi ∧
      ¬Fin15AnchoredAtom3460 chi ∧
      ¬Fin15AnchoredAtom3515 chi ∧
      ¬Fin15AnchoredAtom4473 chi ∧
      ¬Fin15AnchoredAtom4474 chi ∧
      ¬Fin15AnchoredAtom4479 chi ∧
      ¬Fin15AnchoredAtom4495 chi ∧
      ¬Fin15AnchoredAtom4550 chi ∧
      ¬Fin15AnchoredAtom4746 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 6, 8, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13651
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1952 Fin15AnchoredAtom1954 Fin15AnchoredAtom1956
    Fin15AnchoredAtom1957 Fin15AnchoredAtom1967 Fin15AnchoredAtom1969 Fin15AnchoredAtom1970
    Fin15AnchoredAtom1978 Fin15AnchoredAtom1979 Fin15AnchoredAtom1984 Fin15AnchoredAtom2031
    Fin15AnchoredAtom2033 Fin15AnchoredAtom2034 Fin15AnchoredAtom2042 Fin15AnchoredAtom2043
    Fin15AnchoredAtom2048 Fin15AnchoredAtom2078 Fin15AnchoredAtom2079 Fin15AnchoredAtom2084
    Fin15AnchoredAtom2100 Fin15AnchoredAtom2536 Fin15AnchoredAtom2538 Fin15AnchoredAtom2539
    Fin15AnchoredAtom2547 Fin15AnchoredAtom2548 Fin15AnchoredAtom2553 Fin15AnchoredAtom2583
    Fin15AnchoredAtom2584 Fin15AnchoredAtom2589 Fin15AnchoredAtom2605 Fin15AnchoredAtom2723
    Fin15AnchoredAtom2724 Fin15AnchoredAtom2729 Fin15AnchoredAtom2745 Fin15AnchoredAtom2800
    Fin15AnchoredAtom3251 Fin15AnchoredAtom3253 Fin15AnchoredAtom3254 Fin15AnchoredAtom3262
    Fin15AnchoredAtom3263 Fin15AnchoredAtom3268 Fin15AnchoredAtom3298 Fin15AnchoredAtom3299
    Fin15AnchoredAtom3304 Fin15AnchoredAtom3320 Fin15AnchoredAtom3438 Fin15AnchoredAtom3439
    Fin15AnchoredAtom3444 Fin15AnchoredAtom3460 Fin15AnchoredAtom3515 Fin15AnchoredAtom4473
    Fin15AnchoredAtom4474 Fin15AnchoredAtom4479 Fin15AnchoredAtom4495 Fin15AnchoredAtom4550
    Fin15AnchoredAtom4746 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31038 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1952 chi ∧
      ¬Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom1967 chi ∧
      ¬Fin15AnchoredAtom1969 chi ∧
      ¬Fin15AnchoredAtom1971 chi ∧
      ¬Fin15AnchoredAtom1978 chi ∧
      ¬Fin15AnchoredAtom1980 chi ∧
      ¬Fin15AnchoredAtom1985 chi ∧
      ¬Fin15AnchoredAtom2031 chi ∧
      ¬Fin15AnchoredAtom2033 chi ∧
      ¬Fin15AnchoredAtom2035 chi ∧
      ¬Fin15AnchoredAtom2042 chi ∧
      ¬Fin15AnchoredAtom2044 chi ∧
      ¬Fin15AnchoredAtom2049 chi ∧
      ¬Fin15AnchoredAtom2078 chi ∧
      ¬Fin15AnchoredAtom2080 chi ∧
      ¬Fin15AnchoredAtom2085 chi ∧
      ¬Fin15AnchoredAtom2101 chi ∧
      ¬Fin15AnchoredAtom2536 chi ∧
      ¬Fin15AnchoredAtom2538 chi ∧
      ¬Fin15AnchoredAtom2540 chi ∧
      ¬Fin15AnchoredAtom2547 chi ∧
      ¬Fin15AnchoredAtom2549 chi ∧
      ¬Fin15AnchoredAtom2554 chi ∧
      ¬Fin15AnchoredAtom2583 chi ∧
      ¬Fin15AnchoredAtom2585 chi ∧
      ¬Fin15AnchoredAtom2590 chi ∧
      ¬Fin15AnchoredAtom2606 chi ∧
      ¬Fin15AnchoredAtom2723 chi ∧
      ¬Fin15AnchoredAtom2725 chi ∧
      ¬Fin15AnchoredAtom2730 chi ∧
      ¬Fin15AnchoredAtom2746 chi ∧
      ¬Fin15AnchoredAtom2801 chi ∧
      ¬Fin15AnchoredAtom3251 chi ∧
      ¬Fin15AnchoredAtom3253 chi ∧
      ¬Fin15AnchoredAtom3255 chi ∧
      ¬Fin15AnchoredAtom3262 chi ∧
      ¬Fin15AnchoredAtom3264 chi ∧
      ¬Fin15AnchoredAtom3269 chi ∧
      ¬Fin15AnchoredAtom3298 chi ∧
      ¬Fin15AnchoredAtom3300 chi ∧
      ¬Fin15AnchoredAtom3305 chi ∧
      ¬Fin15AnchoredAtom3321 chi ∧
      ¬Fin15AnchoredAtom3438 chi ∧
      ¬Fin15AnchoredAtom3440 chi ∧
      ¬Fin15AnchoredAtom3445 chi ∧
      ¬Fin15AnchoredAtom3461 chi ∧
      ¬Fin15AnchoredAtom3516 chi ∧
      ¬Fin15AnchoredAtom4473 chi ∧
      ¬Fin15AnchoredAtom4475 chi ∧
      ¬Fin15AnchoredAtom4480 chi ∧
      ¬Fin15AnchoredAtom4496 chi ∧
      ¬Fin15AnchoredAtom4551 chi ∧
      ¬Fin15AnchoredAtom4747 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 6, 8, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21843
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1952 Fin15AnchoredAtom1954 Fin15AnchoredAtom1956
    Fin15AnchoredAtom1958 Fin15AnchoredAtom1967 Fin15AnchoredAtom1969 Fin15AnchoredAtom1971
    Fin15AnchoredAtom1978 Fin15AnchoredAtom1980 Fin15AnchoredAtom1985 Fin15AnchoredAtom2031
    Fin15AnchoredAtom2033 Fin15AnchoredAtom2035 Fin15AnchoredAtom2042 Fin15AnchoredAtom2044
    Fin15AnchoredAtom2049 Fin15AnchoredAtom2078 Fin15AnchoredAtom2080 Fin15AnchoredAtom2085
    Fin15AnchoredAtom2101 Fin15AnchoredAtom2536 Fin15AnchoredAtom2538 Fin15AnchoredAtom2540
    Fin15AnchoredAtom2547 Fin15AnchoredAtom2549 Fin15AnchoredAtom2554 Fin15AnchoredAtom2583
    Fin15AnchoredAtom2585 Fin15AnchoredAtom2590 Fin15AnchoredAtom2606 Fin15AnchoredAtom2723
    Fin15AnchoredAtom2725 Fin15AnchoredAtom2730 Fin15AnchoredAtom2746 Fin15AnchoredAtom2801
    Fin15AnchoredAtom3251 Fin15AnchoredAtom3253 Fin15AnchoredAtom3255 Fin15AnchoredAtom3262
    Fin15AnchoredAtom3264 Fin15AnchoredAtom3269 Fin15AnchoredAtom3298 Fin15AnchoredAtom3300
    Fin15AnchoredAtom3305 Fin15AnchoredAtom3321 Fin15AnchoredAtom3438 Fin15AnchoredAtom3440
    Fin15AnchoredAtom3445 Fin15AnchoredAtom3461 Fin15AnchoredAtom3516 Fin15AnchoredAtom4473
    Fin15AnchoredAtom4475 Fin15AnchoredAtom4480 Fin15AnchoredAtom4496 Fin15AnchoredAtom4551
    Fin15AnchoredAtom4747 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31039 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1952 chi ∧
      ¬Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom1969 chi ∧
      ¬Fin15AnchoredAtom1970 chi ∧
      ¬Fin15AnchoredAtom1971 chi ∧
      ¬Fin15AnchoredAtom1984 chi ∧
      ¬Fin15AnchoredAtom1985 chi ∧
      ¬Fin15AnchoredAtom1986 chi ∧
      ¬Fin15AnchoredAtom2033 chi ∧
      ¬Fin15AnchoredAtom2034 chi ∧
      ¬Fin15AnchoredAtom2035 chi ∧
      ¬Fin15AnchoredAtom2048 chi ∧
      ¬Fin15AnchoredAtom2049 chi ∧
      ¬Fin15AnchoredAtom2050 chi ∧
      ¬Fin15AnchoredAtom2084 chi ∧
      ¬Fin15AnchoredAtom2085 chi ∧
      ¬Fin15AnchoredAtom2086 chi ∧
      ¬Fin15AnchoredAtom2106 chi ∧
      ¬Fin15AnchoredAtom2538 chi ∧
      ¬Fin15AnchoredAtom2539 chi ∧
      ¬Fin15AnchoredAtom2540 chi ∧
      ¬Fin15AnchoredAtom2553 chi ∧
      ¬Fin15AnchoredAtom2554 chi ∧
      ¬Fin15AnchoredAtom2555 chi ∧
      ¬Fin15AnchoredAtom2589 chi ∧
      ¬Fin15AnchoredAtom2590 chi ∧
      ¬Fin15AnchoredAtom2591 chi ∧
      ¬Fin15AnchoredAtom2611 chi ∧
      ¬Fin15AnchoredAtom2729 chi ∧
      ¬Fin15AnchoredAtom2730 chi ∧
      ¬Fin15AnchoredAtom2731 chi ∧
      ¬Fin15AnchoredAtom2751 chi ∧
      ¬Fin15AnchoredAtom2806 chi ∧
      ¬Fin15AnchoredAtom3253 chi ∧
      ¬Fin15AnchoredAtom3254 chi ∧
      ¬Fin15AnchoredAtom3255 chi ∧
      ¬Fin15AnchoredAtom3268 chi ∧
      ¬Fin15AnchoredAtom3269 chi ∧
      ¬Fin15AnchoredAtom3270 chi ∧
      ¬Fin15AnchoredAtom3304 chi ∧
      ¬Fin15AnchoredAtom3305 chi ∧
      ¬Fin15AnchoredAtom3306 chi ∧
      ¬Fin15AnchoredAtom3326 chi ∧
      ¬Fin15AnchoredAtom3444 chi ∧
      ¬Fin15AnchoredAtom3445 chi ∧
      ¬Fin15AnchoredAtom3446 chi ∧
      ¬Fin15AnchoredAtom3466 chi ∧
      ¬Fin15AnchoredAtom3521 chi ∧
      ¬Fin15AnchoredAtom4479 chi ∧
      ¬Fin15AnchoredAtom4480 chi ∧
      ¬Fin15AnchoredAtom4481 chi ∧
      ¬Fin15AnchoredAtom4501 chi ∧
      ¬Fin15AnchoredAtom4556 chi ∧
      ¬Fin15AnchoredAtom4752 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 6, 8, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29011
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1952 Fin15AnchoredAtom1956 Fin15AnchoredAtom1957
    Fin15AnchoredAtom1958 Fin15AnchoredAtom1969 Fin15AnchoredAtom1970 Fin15AnchoredAtom1971
    Fin15AnchoredAtom1984 Fin15AnchoredAtom1985 Fin15AnchoredAtom1986 Fin15AnchoredAtom2033
    Fin15AnchoredAtom2034 Fin15AnchoredAtom2035 Fin15AnchoredAtom2048 Fin15AnchoredAtom2049
    Fin15AnchoredAtom2050 Fin15AnchoredAtom2084 Fin15AnchoredAtom2085 Fin15AnchoredAtom2086
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2538 Fin15AnchoredAtom2539 Fin15AnchoredAtom2540
    Fin15AnchoredAtom2553 Fin15AnchoredAtom2554 Fin15AnchoredAtom2555 Fin15AnchoredAtom2589
    Fin15AnchoredAtom2590 Fin15AnchoredAtom2591 Fin15AnchoredAtom2611 Fin15AnchoredAtom2729
    Fin15AnchoredAtom2730 Fin15AnchoredAtom2731 Fin15AnchoredAtom2751 Fin15AnchoredAtom2806
    Fin15AnchoredAtom3253 Fin15AnchoredAtom3254 Fin15AnchoredAtom3255 Fin15AnchoredAtom3268
    Fin15AnchoredAtom3269 Fin15AnchoredAtom3270 Fin15AnchoredAtom3304 Fin15AnchoredAtom3305
    Fin15AnchoredAtom3306 Fin15AnchoredAtom3326 Fin15AnchoredAtom3444 Fin15AnchoredAtom3445
    Fin15AnchoredAtom3446 Fin15AnchoredAtom3466 Fin15AnchoredAtom3521 Fin15AnchoredAtom4479
    Fin15AnchoredAtom4480 Fin15AnchoredAtom4481 Fin15AnchoredAtom4501 Fin15AnchoredAtom4556
    Fin15AnchoredAtom4752 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31040 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom1978 chi ∧
      ¬Fin15AnchoredAtom1979 chi ∧
      ¬Fin15AnchoredAtom1984 chi ∧
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
      ¬Fin15AnchoredAtom2541 chi ∧
      ¬Fin15AnchoredAtom2543 chi ∧
      ¬Fin15AnchoredAtom2544 chi ∧
      ¬Fin15AnchoredAtom2547 chi ∧
      ¬Fin15AnchoredAtom2548 chi ∧
      ¬Fin15AnchoredAtom2553 chi ∧
      ¬Fin15AnchoredAtom2593 chi ∧
      ¬Fin15AnchoredAtom2594 chi ∧
      ¬Fin15AnchoredAtom2599 chi ∧
      ¬Fin15AnchoredAtom2605 chi ∧
      ¬Fin15AnchoredAtom2733 chi ∧
      ¬Fin15AnchoredAtom2734 chi ∧
      ¬Fin15AnchoredAtom2739 chi ∧
      ¬Fin15AnchoredAtom2745 chi ∧
      ¬Fin15AnchoredAtom2810 chi ∧
      ¬Fin15AnchoredAtom3256 chi ∧
      ¬Fin15AnchoredAtom3258 chi ∧
      ¬Fin15AnchoredAtom3259 chi ∧
      ¬Fin15AnchoredAtom3262 chi ∧
      ¬Fin15AnchoredAtom3263 chi ∧
      ¬Fin15AnchoredAtom3268 chi ∧
      ¬Fin15AnchoredAtom3308 chi ∧
      ¬Fin15AnchoredAtom3309 chi ∧
      ¬Fin15AnchoredAtom3314 chi ∧
      ¬Fin15AnchoredAtom3320 chi ∧
      ¬Fin15AnchoredAtom3448 chi ∧
      ¬Fin15AnchoredAtom3449 chi ∧
      ¬Fin15AnchoredAtom3454 chi ∧
      ¬Fin15AnchoredAtom3460 chi ∧
      ¬Fin15AnchoredAtom3525 chi ∧
      ¬Fin15AnchoredAtom4483 chi ∧
      ¬Fin15AnchoredAtom4484 chi ∧
      ¬Fin15AnchoredAtom4489 chi ∧
      ¬Fin15AnchoredAtom4495 chi ∧
      ¬Fin15AnchoredAtom4560 chi ∧
      ¬Fin15AnchoredAtom4756 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 6, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13907
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1953 Fin15AnchoredAtom1954 Fin15AnchoredAtom1956
    Fin15AnchoredAtom1957 Fin15AnchoredAtom1972 Fin15AnchoredAtom1974 Fin15AnchoredAtom1975
    Fin15AnchoredAtom1978 Fin15AnchoredAtom1979 Fin15AnchoredAtom1984 Fin15AnchoredAtom2036
    Fin15AnchoredAtom2038 Fin15AnchoredAtom2039 Fin15AnchoredAtom2042 Fin15AnchoredAtom2043
    Fin15AnchoredAtom2048 Fin15AnchoredAtom2088 Fin15AnchoredAtom2089 Fin15AnchoredAtom2094
    Fin15AnchoredAtom2100 Fin15AnchoredAtom2541 Fin15AnchoredAtom2543 Fin15AnchoredAtom2544
    Fin15AnchoredAtom2547 Fin15AnchoredAtom2548 Fin15AnchoredAtom2553 Fin15AnchoredAtom2593
    Fin15AnchoredAtom2594 Fin15AnchoredAtom2599 Fin15AnchoredAtom2605 Fin15AnchoredAtom2733
    Fin15AnchoredAtom2734 Fin15AnchoredAtom2739 Fin15AnchoredAtom2745 Fin15AnchoredAtom2810
    Fin15AnchoredAtom3256 Fin15AnchoredAtom3258 Fin15AnchoredAtom3259 Fin15AnchoredAtom3262
    Fin15AnchoredAtom3263 Fin15AnchoredAtom3268 Fin15AnchoredAtom3308 Fin15AnchoredAtom3309
    Fin15AnchoredAtom3314 Fin15AnchoredAtom3320 Fin15AnchoredAtom3448 Fin15AnchoredAtom3449
    Fin15AnchoredAtom3454 Fin15AnchoredAtom3460 Fin15AnchoredAtom3525 Fin15AnchoredAtom4483
    Fin15AnchoredAtom4484 Fin15AnchoredAtom4489 Fin15AnchoredAtom4495 Fin15AnchoredAtom4560
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

theorem fin15Anchored_clause31041 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom1976 chi ∧
      ¬Fin15AnchoredAtom1978 chi ∧
      ¬Fin15AnchoredAtom1980 chi ∧
      ¬Fin15AnchoredAtom1985 chi ∧
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
      ¬Fin15AnchoredAtom2541 chi ∧
      ¬Fin15AnchoredAtom2543 chi ∧
      ¬Fin15AnchoredAtom2545 chi ∧
      ¬Fin15AnchoredAtom2547 chi ∧
      ¬Fin15AnchoredAtom2549 chi ∧
      ¬Fin15AnchoredAtom2554 chi ∧
      ¬Fin15AnchoredAtom2593 chi ∧
      ¬Fin15AnchoredAtom2595 chi ∧
      ¬Fin15AnchoredAtom2600 chi ∧
      ¬Fin15AnchoredAtom2606 chi ∧
      ¬Fin15AnchoredAtom2733 chi ∧
      ¬Fin15AnchoredAtom2735 chi ∧
      ¬Fin15AnchoredAtom2740 chi ∧
      ¬Fin15AnchoredAtom2746 chi ∧
      ¬Fin15AnchoredAtom2811 chi ∧
      ¬Fin15AnchoredAtom3256 chi ∧
      ¬Fin15AnchoredAtom3258 chi ∧
      ¬Fin15AnchoredAtom3260 chi ∧
      ¬Fin15AnchoredAtom3262 chi ∧
      ¬Fin15AnchoredAtom3264 chi ∧
      ¬Fin15AnchoredAtom3269 chi ∧
      ¬Fin15AnchoredAtom3308 chi ∧
      ¬Fin15AnchoredAtom3310 chi ∧
      ¬Fin15AnchoredAtom3315 chi ∧
      ¬Fin15AnchoredAtom3321 chi ∧
      ¬Fin15AnchoredAtom3448 chi ∧
      ¬Fin15AnchoredAtom3450 chi ∧
      ¬Fin15AnchoredAtom3455 chi ∧
      ¬Fin15AnchoredAtom3461 chi ∧
      ¬Fin15AnchoredAtom3526 chi ∧
      ¬Fin15AnchoredAtom4483 chi ∧
      ¬Fin15AnchoredAtom4485 chi ∧
      ¬Fin15AnchoredAtom4490 chi ∧
      ¬Fin15AnchoredAtom4496 chi ∧
      ¬Fin15AnchoredAtom4561 chi ∧
      ¬Fin15AnchoredAtom4757 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 6, 9, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22099
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1953 Fin15AnchoredAtom1954 Fin15AnchoredAtom1956
    Fin15AnchoredAtom1958 Fin15AnchoredAtom1972 Fin15AnchoredAtom1974 Fin15AnchoredAtom1976
    Fin15AnchoredAtom1978 Fin15AnchoredAtom1980 Fin15AnchoredAtom1985 Fin15AnchoredAtom2036
    Fin15AnchoredAtom2038 Fin15AnchoredAtom2040 Fin15AnchoredAtom2042 Fin15AnchoredAtom2044
    Fin15AnchoredAtom2049 Fin15AnchoredAtom2088 Fin15AnchoredAtom2090 Fin15AnchoredAtom2095
    Fin15AnchoredAtom2101 Fin15AnchoredAtom2541 Fin15AnchoredAtom2543 Fin15AnchoredAtom2545
    Fin15AnchoredAtom2547 Fin15AnchoredAtom2549 Fin15AnchoredAtom2554 Fin15AnchoredAtom2593
    Fin15AnchoredAtom2595 Fin15AnchoredAtom2600 Fin15AnchoredAtom2606 Fin15AnchoredAtom2733
    Fin15AnchoredAtom2735 Fin15AnchoredAtom2740 Fin15AnchoredAtom2746 Fin15AnchoredAtom2811
    Fin15AnchoredAtom3256 Fin15AnchoredAtom3258 Fin15AnchoredAtom3260 Fin15AnchoredAtom3262
    Fin15AnchoredAtom3264 Fin15AnchoredAtom3269 Fin15AnchoredAtom3308 Fin15AnchoredAtom3310
    Fin15AnchoredAtom3315 Fin15AnchoredAtom3321 Fin15AnchoredAtom3448 Fin15AnchoredAtom3450
    Fin15AnchoredAtom3455 Fin15AnchoredAtom3461 Fin15AnchoredAtom3526 Fin15AnchoredAtom4483
    Fin15AnchoredAtom4485 Fin15AnchoredAtom4490 Fin15AnchoredAtom4496 Fin15AnchoredAtom4561
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

theorem fin15Anchored_clause31042 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom1976 chi ∧
      ¬Fin15AnchoredAtom1979 chi ∧
      ¬Fin15AnchoredAtom1980 chi ∧
      ¬Fin15AnchoredAtom1986 chi ∧
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
      ¬Fin15AnchoredAtom2541 chi ∧
      ¬Fin15AnchoredAtom2544 chi ∧
      ¬Fin15AnchoredAtom2545 chi ∧
      ¬Fin15AnchoredAtom2548 chi ∧
      ¬Fin15AnchoredAtom2549 chi ∧
      ¬Fin15AnchoredAtom2555 chi ∧
      ¬Fin15AnchoredAtom2594 chi ∧
      ¬Fin15AnchoredAtom2595 chi ∧
      ¬Fin15AnchoredAtom2601 chi ∧
      ¬Fin15AnchoredAtom2607 chi ∧
      ¬Fin15AnchoredAtom2734 chi ∧
      ¬Fin15AnchoredAtom2735 chi ∧
      ¬Fin15AnchoredAtom2741 chi ∧
      ¬Fin15AnchoredAtom2747 chi ∧
      ¬Fin15AnchoredAtom2812 chi ∧
      ¬Fin15AnchoredAtom3256 chi ∧
      ¬Fin15AnchoredAtom3259 chi ∧
      ¬Fin15AnchoredAtom3260 chi ∧
      ¬Fin15AnchoredAtom3263 chi ∧
      ¬Fin15AnchoredAtom3264 chi ∧
      ¬Fin15AnchoredAtom3270 chi ∧
      ¬Fin15AnchoredAtom3309 chi ∧
      ¬Fin15AnchoredAtom3310 chi ∧
      ¬Fin15AnchoredAtom3316 chi ∧
      ¬Fin15AnchoredAtom3322 chi ∧
      ¬Fin15AnchoredAtom3449 chi ∧
      ¬Fin15AnchoredAtom3450 chi ∧
      ¬Fin15AnchoredAtom3456 chi ∧
      ¬Fin15AnchoredAtom3462 chi ∧
      ¬Fin15AnchoredAtom3527 chi ∧
      ¬Fin15AnchoredAtom4484 chi ∧
      ¬Fin15AnchoredAtom4485 chi ∧
      ¬Fin15AnchoredAtom4491 chi ∧
      ¬Fin15AnchoredAtom4497 chi ∧
      ¬Fin15AnchoredAtom4562 chi ∧
      ¬Fin15AnchoredAtom4758 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 6, 9, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26195
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1953 Fin15AnchoredAtom1954 Fin15AnchoredAtom1957
    Fin15AnchoredAtom1958 Fin15AnchoredAtom1972 Fin15AnchoredAtom1975 Fin15AnchoredAtom1976
    Fin15AnchoredAtom1979 Fin15AnchoredAtom1980 Fin15AnchoredAtom1986 Fin15AnchoredAtom2036
    Fin15AnchoredAtom2039 Fin15AnchoredAtom2040 Fin15AnchoredAtom2043 Fin15AnchoredAtom2044
    Fin15AnchoredAtom2050 Fin15AnchoredAtom2089 Fin15AnchoredAtom2090 Fin15AnchoredAtom2096
    Fin15AnchoredAtom2102 Fin15AnchoredAtom2541 Fin15AnchoredAtom2544 Fin15AnchoredAtom2545
    Fin15AnchoredAtom2548 Fin15AnchoredAtom2549 Fin15AnchoredAtom2555 Fin15AnchoredAtom2594
    Fin15AnchoredAtom2595 Fin15AnchoredAtom2601 Fin15AnchoredAtom2607 Fin15AnchoredAtom2734
    Fin15AnchoredAtom2735 Fin15AnchoredAtom2741 Fin15AnchoredAtom2747 Fin15AnchoredAtom2812
    Fin15AnchoredAtom3256 Fin15AnchoredAtom3259 Fin15AnchoredAtom3260 Fin15AnchoredAtom3263
    Fin15AnchoredAtom3264 Fin15AnchoredAtom3270 Fin15AnchoredAtom3309 Fin15AnchoredAtom3310
    Fin15AnchoredAtom3316 Fin15AnchoredAtom3322 Fin15AnchoredAtom3449 Fin15AnchoredAtom3450
    Fin15AnchoredAtom3456 Fin15AnchoredAtom3462 Fin15AnchoredAtom3527 Fin15AnchoredAtom4484
    Fin15AnchoredAtom4485 Fin15AnchoredAtom4491 Fin15AnchoredAtom4497 Fin15AnchoredAtom4562
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

theorem fin15Anchored_clause31043 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom1976 chi ∧
      ¬Fin15AnchoredAtom1984 chi ∧
      ¬Fin15AnchoredAtom1985 chi ∧
      ¬Fin15AnchoredAtom1986 chi ∧
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
      ¬Fin15AnchoredAtom2543 chi ∧
      ¬Fin15AnchoredAtom2544 chi ∧
      ¬Fin15AnchoredAtom2545 chi ∧
      ¬Fin15AnchoredAtom2553 chi ∧
      ¬Fin15AnchoredAtom2554 chi ∧
      ¬Fin15AnchoredAtom2555 chi ∧
      ¬Fin15AnchoredAtom2599 chi ∧
      ¬Fin15AnchoredAtom2600 chi ∧
      ¬Fin15AnchoredAtom2601 chi ∧
      ¬Fin15AnchoredAtom2611 chi ∧
      ¬Fin15AnchoredAtom2739 chi ∧
      ¬Fin15AnchoredAtom2740 chi ∧
      ¬Fin15AnchoredAtom2741 chi ∧
      ¬Fin15AnchoredAtom2751 chi ∧
      ¬Fin15AnchoredAtom2816 chi ∧
      ¬Fin15AnchoredAtom3258 chi ∧
      ¬Fin15AnchoredAtom3259 chi ∧
      ¬Fin15AnchoredAtom3260 chi ∧
      ¬Fin15AnchoredAtom3268 chi ∧
      ¬Fin15AnchoredAtom3269 chi ∧
      ¬Fin15AnchoredAtom3270 chi ∧
      ¬Fin15AnchoredAtom3314 chi ∧
      ¬Fin15AnchoredAtom3315 chi ∧
      ¬Fin15AnchoredAtom3316 chi ∧
      ¬Fin15AnchoredAtom3326 chi ∧
      ¬Fin15AnchoredAtom3454 chi ∧
      ¬Fin15AnchoredAtom3455 chi ∧
      ¬Fin15AnchoredAtom3456 chi ∧
      ¬Fin15AnchoredAtom3466 chi ∧
      ¬Fin15AnchoredAtom3531 chi ∧
      ¬Fin15AnchoredAtom4489 chi ∧
      ¬Fin15AnchoredAtom4490 chi ∧
      ¬Fin15AnchoredAtom4491 chi ∧
      ¬Fin15AnchoredAtom4501 chi ∧
      ¬Fin15AnchoredAtom4566 chi ∧
      ¬Fin15AnchoredAtom4762 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 6, 9, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29267
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1953 Fin15AnchoredAtom1956 Fin15AnchoredAtom1957
    Fin15AnchoredAtom1958 Fin15AnchoredAtom1974 Fin15AnchoredAtom1975 Fin15AnchoredAtom1976
    Fin15AnchoredAtom1984 Fin15AnchoredAtom1985 Fin15AnchoredAtom1986 Fin15AnchoredAtom2038
    Fin15AnchoredAtom2039 Fin15AnchoredAtom2040 Fin15AnchoredAtom2048 Fin15AnchoredAtom2049
    Fin15AnchoredAtom2050 Fin15AnchoredAtom2094 Fin15AnchoredAtom2095 Fin15AnchoredAtom2096
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2543 Fin15AnchoredAtom2544 Fin15AnchoredAtom2545
    Fin15AnchoredAtom2553 Fin15AnchoredAtom2554 Fin15AnchoredAtom2555 Fin15AnchoredAtom2599
    Fin15AnchoredAtom2600 Fin15AnchoredAtom2601 Fin15AnchoredAtom2611 Fin15AnchoredAtom2739
    Fin15AnchoredAtom2740 Fin15AnchoredAtom2741 Fin15AnchoredAtom2751 Fin15AnchoredAtom2816
    Fin15AnchoredAtom3258 Fin15AnchoredAtom3259 Fin15AnchoredAtom3260 Fin15AnchoredAtom3268
    Fin15AnchoredAtom3269 Fin15AnchoredAtom3270 Fin15AnchoredAtom3314 Fin15AnchoredAtom3315
    Fin15AnchoredAtom3316 Fin15AnchoredAtom3326 Fin15AnchoredAtom3454 Fin15AnchoredAtom3455
    Fin15AnchoredAtom3456 Fin15AnchoredAtom3466 Fin15AnchoredAtom3531 Fin15AnchoredAtom4489
    Fin15AnchoredAtom4490 Fin15AnchoredAtom4491 Fin15AnchoredAtom4501 Fin15AnchoredAtom4566
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

theorem fin15Anchored_clause31044 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom1955 chi ∧
      ¬Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom1977 chi ∧
      ¬Fin15AnchoredAtom1978 chi ∧
      ¬Fin15AnchoredAtom1979 chi ∧
      ¬Fin15AnchoredAtom1981 chi ∧
      ¬Fin15AnchoredAtom1982 chi ∧
      ¬Fin15AnchoredAtom1984 chi ∧
      ¬Fin15AnchoredAtom2041 chi ∧
      ¬Fin15AnchoredAtom2042 chi ∧
      ¬Fin15AnchoredAtom2043 chi ∧
      ¬Fin15AnchoredAtom2045 chi ∧
      ¬Fin15AnchoredAtom2046 chi ∧
      ¬Fin15AnchoredAtom2048 chi ∧
      ¬Fin15AnchoredAtom2097 chi ∧
      ¬Fin15AnchoredAtom2098 chi ∧
      ¬Fin15AnchoredAtom2100 chi ∧
      ¬Fin15AnchoredAtom2103 chi ∧
      ¬Fin15AnchoredAtom2546 chi ∧
      ¬Fin15AnchoredAtom2547 chi ∧
      ¬Fin15AnchoredAtom2548 chi ∧
      ¬Fin15AnchoredAtom2550 chi ∧
      ¬Fin15AnchoredAtom2551 chi ∧
      ¬Fin15AnchoredAtom2553 chi ∧
      ¬Fin15AnchoredAtom2602 chi ∧
      ¬Fin15AnchoredAtom2603 chi ∧
      ¬Fin15AnchoredAtom2605 chi ∧
      ¬Fin15AnchoredAtom2608 chi ∧
      ¬Fin15AnchoredAtom2742 chi ∧
      ¬Fin15AnchoredAtom2743 chi ∧
      ¬Fin15AnchoredAtom2745 chi ∧
      ¬Fin15AnchoredAtom2748 chi ∧
      ¬Fin15AnchoredAtom2817 chi ∧
      ¬Fin15AnchoredAtom3261 chi ∧
      ¬Fin15AnchoredAtom3262 chi ∧
      ¬Fin15AnchoredAtom3263 chi ∧
      ¬Fin15AnchoredAtom3265 chi ∧
      ¬Fin15AnchoredAtom3266 chi ∧
      ¬Fin15AnchoredAtom3268 chi ∧
      ¬Fin15AnchoredAtom3317 chi ∧
      ¬Fin15AnchoredAtom3318 chi ∧
      ¬Fin15AnchoredAtom3320 chi ∧
      ¬Fin15AnchoredAtom3323 chi ∧
      ¬Fin15AnchoredAtom3457 chi ∧
      ¬Fin15AnchoredAtom3458 chi ∧
      ¬Fin15AnchoredAtom3460 chi ∧
      ¬Fin15AnchoredAtom3463 chi ∧
      ¬Fin15AnchoredAtom3532 chi ∧
      ¬Fin15AnchoredAtom4492 chi ∧
      ¬Fin15AnchoredAtom4493 chi ∧
      ¬Fin15AnchoredAtom4495 chi ∧
      ¬Fin15AnchoredAtom4498 chi ∧
      ¬Fin15AnchoredAtom4567 chi ∧
      ¬Fin15AnchoredAtom4763 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 6, 10, 11, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask15443
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1954 Fin15AnchoredAtom1955 Fin15AnchoredAtom1956
    Fin15AnchoredAtom1957 Fin15AnchoredAtom1977 Fin15AnchoredAtom1978 Fin15AnchoredAtom1979
    Fin15AnchoredAtom1981 Fin15AnchoredAtom1982 Fin15AnchoredAtom1984 Fin15AnchoredAtom2041
    Fin15AnchoredAtom2042 Fin15AnchoredAtom2043 Fin15AnchoredAtom2045 Fin15AnchoredAtom2046
    Fin15AnchoredAtom2048 Fin15AnchoredAtom2097 Fin15AnchoredAtom2098 Fin15AnchoredAtom2100
    Fin15AnchoredAtom2103 Fin15AnchoredAtom2546 Fin15AnchoredAtom2547 Fin15AnchoredAtom2548
    Fin15AnchoredAtom2550 Fin15AnchoredAtom2551 Fin15AnchoredAtom2553 Fin15AnchoredAtom2602
    Fin15AnchoredAtom2603 Fin15AnchoredAtom2605 Fin15AnchoredAtom2608 Fin15AnchoredAtom2742
    Fin15AnchoredAtom2743 Fin15AnchoredAtom2745 Fin15AnchoredAtom2748 Fin15AnchoredAtom2817
    Fin15AnchoredAtom3261 Fin15AnchoredAtom3262 Fin15AnchoredAtom3263 Fin15AnchoredAtom3265
    Fin15AnchoredAtom3266 Fin15AnchoredAtom3268 Fin15AnchoredAtom3317 Fin15AnchoredAtom3318
    Fin15AnchoredAtom3320 Fin15AnchoredAtom3323 Fin15AnchoredAtom3457 Fin15AnchoredAtom3458
    Fin15AnchoredAtom3460 Fin15AnchoredAtom3463 Fin15AnchoredAtom3532 Fin15AnchoredAtom4492
    Fin15AnchoredAtom4493 Fin15AnchoredAtom4495 Fin15AnchoredAtom4498 Fin15AnchoredAtom4567
    Fin15AnchoredAtom4763 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31045 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom1978 chi ∧
      ¬Fin15AnchoredAtom1979 chi ∧
      ¬Fin15AnchoredAtom1980 chi ∧
      ¬Fin15AnchoredAtom1984 chi ∧
      ¬Fin15AnchoredAtom1985 chi ∧
      ¬Fin15AnchoredAtom1986 chi ∧
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
      ¬Fin15AnchoredAtom2547 chi ∧
      ¬Fin15AnchoredAtom2548 chi ∧
      ¬Fin15AnchoredAtom2549 chi ∧
      ¬Fin15AnchoredAtom2553 chi ∧
      ¬Fin15AnchoredAtom2554 chi ∧
      ¬Fin15AnchoredAtom2555 chi ∧
      ¬Fin15AnchoredAtom2605 chi ∧
      ¬Fin15AnchoredAtom2606 chi ∧
      ¬Fin15AnchoredAtom2607 chi ∧
      ¬Fin15AnchoredAtom2611 chi ∧
      ¬Fin15AnchoredAtom2745 chi ∧
      ¬Fin15AnchoredAtom2746 chi ∧
      ¬Fin15AnchoredAtom2747 chi ∧
      ¬Fin15AnchoredAtom2751 chi ∧
      ¬Fin15AnchoredAtom2820 chi ∧
      ¬Fin15AnchoredAtom3262 chi ∧
      ¬Fin15AnchoredAtom3263 chi ∧
      ¬Fin15AnchoredAtom3264 chi ∧
      ¬Fin15AnchoredAtom3268 chi ∧
      ¬Fin15AnchoredAtom3269 chi ∧
      ¬Fin15AnchoredAtom3270 chi ∧
      ¬Fin15AnchoredAtom3320 chi ∧
      ¬Fin15AnchoredAtom3321 chi ∧
      ¬Fin15AnchoredAtom3322 chi ∧
      ¬Fin15AnchoredAtom3326 chi ∧
      ¬Fin15AnchoredAtom3460 chi ∧
      ¬Fin15AnchoredAtom3461 chi ∧
      ¬Fin15AnchoredAtom3462 chi ∧
      ¬Fin15AnchoredAtom3466 chi ∧
      ¬Fin15AnchoredAtom3535 chi ∧
      ¬Fin15AnchoredAtom4495 chi ∧
      ¬Fin15AnchoredAtom4496 chi ∧
      ¬Fin15AnchoredAtom4497 chi ∧
      ¬Fin15AnchoredAtom4501 chi ∧
      ¬Fin15AnchoredAtom4570 chi ∧
      ¬Fin15AnchoredAtom4766 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 6, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29779
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1954 Fin15AnchoredAtom1956 Fin15AnchoredAtom1957
    Fin15AnchoredAtom1958 Fin15AnchoredAtom1978 Fin15AnchoredAtom1979 Fin15AnchoredAtom1980
    Fin15AnchoredAtom1984 Fin15AnchoredAtom1985 Fin15AnchoredAtom1986 Fin15AnchoredAtom2042
    Fin15AnchoredAtom2043 Fin15AnchoredAtom2044 Fin15AnchoredAtom2048 Fin15AnchoredAtom2049
    Fin15AnchoredAtom2050 Fin15AnchoredAtom2100 Fin15AnchoredAtom2101 Fin15AnchoredAtom2102
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2547 Fin15AnchoredAtom2548 Fin15AnchoredAtom2549
    Fin15AnchoredAtom2553 Fin15AnchoredAtom2554 Fin15AnchoredAtom2555 Fin15AnchoredAtom2605
    Fin15AnchoredAtom2606 Fin15AnchoredAtom2607 Fin15AnchoredAtom2611 Fin15AnchoredAtom2745
    Fin15AnchoredAtom2746 Fin15AnchoredAtom2747 Fin15AnchoredAtom2751 Fin15AnchoredAtom2820
    Fin15AnchoredAtom3262 Fin15AnchoredAtom3263 Fin15AnchoredAtom3264 Fin15AnchoredAtom3268
    Fin15AnchoredAtom3269 Fin15AnchoredAtom3270 Fin15AnchoredAtom3320 Fin15AnchoredAtom3321
    Fin15AnchoredAtom3322 Fin15AnchoredAtom3326 Fin15AnchoredAtom3460 Fin15AnchoredAtom3461
    Fin15AnchoredAtom3462 Fin15AnchoredAtom3466 Fin15AnchoredAtom3535 Fin15AnchoredAtom4495
    Fin15AnchoredAtom4496 Fin15AnchoredAtom4497 Fin15AnchoredAtom4501 Fin15AnchoredAtom4570
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

theorem fin15Anchored_clause31046 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1959 chi ∧
      ¬Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom1966 chi ∧
      ¬Fin15AnchoredAtom1967 chi ∧
      ¬Fin15AnchoredAtom1969 chi ∧
      ¬Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom1978 chi ∧
      ¬Fin15AnchoredAtom2051 chi ∧
      ¬Fin15AnchoredAtom2052 chi ∧
      ¬Fin15AnchoredAtom2054 chi ∧
      ¬Fin15AnchoredAtom2057 chi ∧
      ¬Fin15AnchoredAtom2059 chi ∧
      ¬Fin15AnchoredAtom2063 chi ∧
      ¬Fin15AnchoredAtom2072 chi ∧
      ¬Fin15AnchoredAtom2074 chi ∧
      ¬Fin15AnchoredAtom2078 chi ∧
      ¬Fin15AnchoredAtom2088 chi ∧
      ¬Fin15AnchoredAtom2556 chi ∧
      ¬Fin15AnchoredAtom2557 chi ∧
      ¬Fin15AnchoredAtom2559 chi ∧
      ¬Fin15AnchoredAtom2562 chi ∧
      ¬Fin15AnchoredAtom2564 chi ∧
      ¬Fin15AnchoredAtom2568 chi ∧
      ¬Fin15AnchoredAtom2577 chi ∧
      ¬Fin15AnchoredAtom2579 chi ∧
      ¬Fin15AnchoredAtom2583 chi ∧
      ¬Fin15AnchoredAtom2593 chi ∧
      ¬Fin15AnchoredAtom2752 chi ∧
      ¬Fin15AnchoredAtom2754 chi ∧
      ¬Fin15AnchoredAtom2758 chi ∧
      ¬Fin15AnchoredAtom2768 chi ∧
      ¬Fin15AnchoredAtom2788 chi ∧
      ¬Fin15AnchoredAtom3271 chi ∧
      ¬Fin15AnchoredAtom3272 chi ∧
      ¬Fin15AnchoredAtom3274 chi ∧
      ¬Fin15AnchoredAtom3277 chi ∧
      ¬Fin15AnchoredAtom3279 chi ∧
      ¬Fin15AnchoredAtom3283 chi ∧
      ¬Fin15AnchoredAtom3292 chi ∧
      ¬Fin15AnchoredAtom3294 chi ∧
      ¬Fin15AnchoredAtom3298 chi ∧
      ¬Fin15AnchoredAtom3308 chi ∧
      ¬Fin15AnchoredAtom3467 chi ∧
      ¬Fin15AnchoredAtom3469 chi ∧
      ¬Fin15AnchoredAtom3473 chi ∧
      ¬Fin15AnchoredAtom3483 chi ∧
      ¬Fin15AnchoredAtom3503 chi ∧
      ¬Fin15AnchoredAtom4502 chi ∧
      ¬Fin15AnchoredAtom4504 chi ∧
      ¬Fin15AnchoredAtom4508 chi ∧
      ¬Fin15AnchoredAtom4518 chi ∧
      ¬Fin15AnchoredAtom4538 chi ∧
      ¬Fin15AnchoredAtom4769 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 7, 8, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask06035
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1959 Fin15AnchoredAtom1960 Fin15AnchoredAtom1961
    Fin15AnchoredAtom1963 Fin15AnchoredAtom1966 Fin15AnchoredAtom1967 Fin15AnchoredAtom1969
    Fin15AnchoredAtom1972 Fin15AnchoredAtom1974 Fin15AnchoredAtom1978 Fin15AnchoredAtom2051
    Fin15AnchoredAtom2052 Fin15AnchoredAtom2054 Fin15AnchoredAtom2057 Fin15AnchoredAtom2059
    Fin15AnchoredAtom2063 Fin15AnchoredAtom2072 Fin15AnchoredAtom2074 Fin15AnchoredAtom2078
    Fin15AnchoredAtom2088 Fin15AnchoredAtom2556 Fin15AnchoredAtom2557 Fin15AnchoredAtom2559
    Fin15AnchoredAtom2562 Fin15AnchoredAtom2564 Fin15AnchoredAtom2568 Fin15AnchoredAtom2577
    Fin15AnchoredAtom2579 Fin15AnchoredAtom2583 Fin15AnchoredAtom2593 Fin15AnchoredAtom2752
    Fin15AnchoredAtom2754 Fin15AnchoredAtom2758 Fin15AnchoredAtom2768 Fin15AnchoredAtom2788
    Fin15AnchoredAtom3271 Fin15AnchoredAtom3272 Fin15AnchoredAtom3274 Fin15AnchoredAtom3277
    Fin15AnchoredAtom3279 Fin15AnchoredAtom3283 Fin15AnchoredAtom3292 Fin15AnchoredAtom3294
    Fin15AnchoredAtom3298 Fin15AnchoredAtom3308 Fin15AnchoredAtom3467 Fin15AnchoredAtom3469
    Fin15AnchoredAtom3473 Fin15AnchoredAtom3483 Fin15AnchoredAtom3503 Fin15AnchoredAtom4502
    Fin15AnchoredAtom4504 Fin15AnchoredAtom4508 Fin15AnchoredAtom4518 Fin15AnchoredAtom4538
    Fin15AnchoredAtom4769 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31047 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1959 chi ∧
      ¬Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom1966 chi ∧
      ¬Fin15AnchoredAtom1967 chi ∧
      ¬Fin15AnchoredAtom1970 chi ∧
      ¬Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom1979 chi ∧
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
      ¬Fin15AnchoredAtom2556 chi ∧
      ¬Fin15AnchoredAtom2557 chi ∧
      ¬Fin15AnchoredAtom2560 chi ∧
      ¬Fin15AnchoredAtom2562 chi ∧
      ¬Fin15AnchoredAtom2565 chi ∧
      ¬Fin15AnchoredAtom2569 chi ∧
      ¬Fin15AnchoredAtom2577 chi ∧
      ¬Fin15AnchoredAtom2580 chi ∧
      ¬Fin15AnchoredAtom2584 chi ∧
      ¬Fin15AnchoredAtom2594 chi ∧
      ¬Fin15AnchoredAtom2752 chi ∧
      ¬Fin15AnchoredAtom2755 chi ∧
      ¬Fin15AnchoredAtom2759 chi ∧
      ¬Fin15AnchoredAtom2769 chi ∧
      ¬Fin15AnchoredAtom2789 chi ∧
      ¬Fin15AnchoredAtom3271 chi ∧
      ¬Fin15AnchoredAtom3272 chi ∧
      ¬Fin15AnchoredAtom3275 chi ∧
      ¬Fin15AnchoredAtom3277 chi ∧
      ¬Fin15AnchoredAtom3280 chi ∧
      ¬Fin15AnchoredAtom3284 chi ∧
      ¬Fin15AnchoredAtom3292 chi ∧
      ¬Fin15AnchoredAtom3295 chi ∧
      ¬Fin15AnchoredAtom3299 chi ∧
      ¬Fin15AnchoredAtom3309 chi ∧
      ¬Fin15AnchoredAtom3467 chi ∧
      ¬Fin15AnchoredAtom3470 chi ∧
      ¬Fin15AnchoredAtom3474 chi ∧
      ¬Fin15AnchoredAtom3484 chi ∧
      ¬Fin15AnchoredAtom3504 chi ∧
      ¬Fin15AnchoredAtom4502 chi ∧
      ¬Fin15AnchoredAtom4505 chi ∧
      ¬Fin15AnchoredAtom4509 chi ∧
      ¬Fin15AnchoredAtom4519 chi ∧
      ¬Fin15AnchoredAtom4539 chi ∧
      ¬Fin15AnchoredAtom4770 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 7, 8, 9, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask10131
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1959 Fin15AnchoredAtom1960 Fin15AnchoredAtom1961
    Fin15AnchoredAtom1964 Fin15AnchoredAtom1966 Fin15AnchoredAtom1967 Fin15AnchoredAtom1970
    Fin15AnchoredAtom1972 Fin15AnchoredAtom1975 Fin15AnchoredAtom1979 Fin15AnchoredAtom2051
    Fin15AnchoredAtom2052 Fin15AnchoredAtom2055 Fin15AnchoredAtom2057 Fin15AnchoredAtom2060
    Fin15AnchoredAtom2064 Fin15AnchoredAtom2072 Fin15AnchoredAtom2075 Fin15AnchoredAtom2079
    Fin15AnchoredAtom2089 Fin15AnchoredAtom2556 Fin15AnchoredAtom2557 Fin15AnchoredAtom2560
    Fin15AnchoredAtom2562 Fin15AnchoredAtom2565 Fin15AnchoredAtom2569 Fin15AnchoredAtom2577
    Fin15AnchoredAtom2580 Fin15AnchoredAtom2584 Fin15AnchoredAtom2594 Fin15AnchoredAtom2752
    Fin15AnchoredAtom2755 Fin15AnchoredAtom2759 Fin15AnchoredAtom2769 Fin15AnchoredAtom2789
    Fin15AnchoredAtom3271 Fin15AnchoredAtom3272 Fin15AnchoredAtom3275 Fin15AnchoredAtom3277
    Fin15AnchoredAtom3280 Fin15AnchoredAtom3284 Fin15AnchoredAtom3292 Fin15AnchoredAtom3295
    Fin15AnchoredAtom3299 Fin15AnchoredAtom3309 Fin15AnchoredAtom3467 Fin15AnchoredAtom3470
    Fin15AnchoredAtom3474 Fin15AnchoredAtom3484 Fin15AnchoredAtom3504 Fin15AnchoredAtom4502
    Fin15AnchoredAtom4505 Fin15AnchoredAtom4509 Fin15AnchoredAtom4519 Fin15AnchoredAtom4539
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

theorem fin15Anchored_clause31048 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1959 chi ∧
      ¬Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom1966 chi ∧
      ¬Fin15AnchoredAtom1969 chi ∧
      ¬Fin15AnchoredAtom1970 chi ∧
      ¬Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom1984 chi ∧
      ¬Fin15AnchoredAtom2051 chi ∧
      ¬Fin15AnchoredAtom2054 chi ∧
      ¬Fin15AnchoredAtom2055 chi ∧
      ¬Fin15AnchoredAtom2059 chi ∧
      ¬Fin15AnchoredAtom2060 chi ∧
      ¬Fin15AnchoredAtom2069 chi ∧
      ¬Fin15AnchoredAtom2074 chi ∧
      ¬Fin15AnchoredAtom2075 chi ∧
      ¬Fin15AnchoredAtom2084 chi ∧
      ¬Fin15AnchoredAtom2094 chi ∧
      ¬Fin15AnchoredAtom2556 chi ∧
      ¬Fin15AnchoredAtom2559 chi ∧
      ¬Fin15AnchoredAtom2560 chi ∧
      ¬Fin15AnchoredAtom2564 chi ∧
      ¬Fin15AnchoredAtom2565 chi ∧
      ¬Fin15AnchoredAtom2574 chi ∧
      ¬Fin15AnchoredAtom2579 chi ∧
      ¬Fin15AnchoredAtom2580 chi ∧
      ¬Fin15AnchoredAtom2589 chi ∧
      ¬Fin15AnchoredAtom2599 chi ∧
      ¬Fin15AnchoredAtom2754 chi ∧
      ¬Fin15AnchoredAtom2755 chi ∧
      ¬Fin15AnchoredAtom2764 chi ∧
      ¬Fin15AnchoredAtom2774 chi ∧
      ¬Fin15AnchoredAtom2794 chi ∧
      ¬Fin15AnchoredAtom3271 chi ∧
      ¬Fin15AnchoredAtom3274 chi ∧
      ¬Fin15AnchoredAtom3275 chi ∧
      ¬Fin15AnchoredAtom3279 chi ∧
      ¬Fin15AnchoredAtom3280 chi ∧
      ¬Fin15AnchoredAtom3289 chi ∧
      ¬Fin15AnchoredAtom3294 chi ∧
      ¬Fin15AnchoredAtom3295 chi ∧
      ¬Fin15AnchoredAtom3304 chi ∧
      ¬Fin15AnchoredAtom3314 chi ∧
      ¬Fin15AnchoredAtom3469 chi ∧
      ¬Fin15AnchoredAtom3470 chi ∧
      ¬Fin15AnchoredAtom3479 chi ∧
      ¬Fin15AnchoredAtom3489 chi ∧
      ¬Fin15AnchoredAtom3509 chi ∧
      ¬Fin15AnchoredAtom4504 chi ∧
      ¬Fin15AnchoredAtom4505 chi ∧
      ¬Fin15AnchoredAtom4514 chi ∧
      ¬Fin15AnchoredAtom4524 chi ∧
      ¬Fin15AnchoredAtom4544 chi ∧
      ¬Fin15AnchoredAtom4775 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 7, 8, 9, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13203
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1959 Fin15AnchoredAtom1960 Fin15AnchoredAtom1963
    Fin15AnchoredAtom1964 Fin15AnchoredAtom1966 Fin15AnchoredAtom1969 Fin15AnchoredAtom1970
    Fin15AnchoredAtom1974 Fin15AnchoredAtom1975 Fin15AnchoredAtom1984 Fin15AnchoredAtom2051
    Fin15AnchoredAtom2054 Fin15AnchoredAtom2055 Fin15AnchoredAtom2059 Fin15AnchoredAtom2060
    Fin15AnchoredAtom2069 Fin15AnchoredAtom2074 Fin15AnchoredAtom2075 Fin15AnchoredAtom2084
    Fin15AnchoredAtom2094 Fin15AnchoredAtom2556 Fin15AnchoredAtom2559 Fin15AnchoredAtom2560
    Fin15AnchoredAtom2564 Fin15AnchoredAtom2565 Fin15AnchoredAtom2574 Fin15AnchoredAtom2579
    Fin15AnchoredAtom2580 Fin15AnchoredAtom2589 Fin15AnchoredAtom2599 Fin15AnchoredAtom2754
    Fin15AnchoredAtom2755 Fin15AnchoredAtom2764 Fin15AnchoredAtom2774 Fin15AnchoredAtom2794
    Fin15AnchoredAtom3271 Fin15AnchoredAtom3274 Fin15AnchoredAtom3275 Fin15AnchoredAtom3279
    Fin15AnchoredAtom3280 Fin15AnchoredAtom3289 Fin15AnchoredAtom3294 Fin15AnchoredAtom3295
    Fin15AnchoredAtom3304 Fin15AnchoredAtom3314 Fin15AnchoredAtom3469 Fin15AnchoredAtom3470
    Fin15AnchoredAtom3479 Fin15AnchoredAtom3489 Fin15AnchoredAtom3509 Fin15AnchoredAtom4504
    Fin15AnchoredAtom4505 Fin15AnchoredAtom4514 Fin15AnchoredAtom4524 Fin15AnchoredAtom4544
    Fin15AnchoredAtom4775 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31049 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1959 chi ∧
      ¬Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom1966 chi ∧
      ¬Fin15AnchoredAtom1970 chi ∧
      ¬Fin15AnchoredAtom1971 chi ∧
      ¬Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom1976 chi ∧
      ¬Fin15AnchoredAtom1986 chi ∧
      ¬Fin15AnchoredAtom2051 chi ∧
      ¬Fin15AnchoredAtom2055 chi ∧
      ¬Fin15AnchoredAtom2056 chi ∧
      ¬Fin15AnchoredAtom2060 chi ∧
      ¬Fin15AnchoredAtom2061 chi ∧
      ¬Fin15AnchoredAtom2071 chi ∧
      ¬Fin15AnchoredAtom2075 chi ∧
      ¬Fin15AnchoredAtom2076 chi ∧
      ¬Fin15AnchoredAtom2086 chi ∧
      ¬Fin15AnchoredAtom2096 chi ∧
      ¬Fin15AnchoredAtom2556 chi ∧
      ¬Fin15AnchoredAtom2560 chi ∧
      ¬Fin15AnchoredAtom2561 chi ∧
      ¬Fin15AnchoredAtom2565 chi ∧
      ¬Fin15AnchoredAtom2566 chi ∧
      ¬Fin15AnchoredAtom2576 chi ∧
      ¬Fin15AnchoredAtom2580 chi ∧
      ¬Fin15AnchoredAtom2581 chi ∧
      ¬Fin15AnchoredAtom2591 chi ∧
      ¬Fin15AnchoredAtom2601 chi ∧
      ¬Fin15AnchoredAtom2755 chi ∧
      ¬Fin15AnchoredAtom2756 chi ∧
      ¬Fin15AnchoredAtom2766 chi ∧
      ¬Fin15AnchoredAtom2776 chi ∧
      ¬Fin15AnchoredAtom2796 chi ∧
      ¬Fin15AnchoredAtom3271 chi ∧
      ¬Fin15AnchoredAtom3275 chi ∧
      ¬Fin15AnchoredAtom3276 chi ∧
      ¬Fin15AnchoredAtom3280 chi ∧
      ¬Fin15AnchoredAtom3281 chi ∧
      ¬Fin15AnchoredAtom3291 chi ∧
      ¬Fin15AnchoredAtom3295 chi ∧
      ¬Fin15AnchoredAtom3296 chi ∧
      ¬Fin15AnchoredAtom3306 chi ∧
      ¬Fin15AnchoredAtom3316 chi ∧
      ¬Fin15AnchoredAtom3470 chi ∧
      ¬Fin15AnchoredAtom3471 chi ∧
      ¬Fin15AnchoredAtom3481 chi ∧
      ¬Fin15AnchoredAtom3491 chi ∧
      ¬Fin15AnchoredAtom3511 chi ∧
      ¬Fin15AnchoredAtom4505 chi ∧
      ¬Fin15AnchoredAtom4506 chi ∧
      ¬Fin15AnchoredAtom4516 chi ∧
      ¬Fin15AnchoredAtom4526 chi ∧
      ¬Fin15AnchoredAtom4546 chi ∧
      ¬Fin15AnchoredAtom4777 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 7, 8, 9, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25491
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1959 Fin15AnchoredAtom1960 Fin15AnchoredAtom1964
    Fin15AnchoredAtom1965 Fin15AnchoredAtom1966 Fin15AnchoredAtom1970 Fin15AnchoredAtom1971
    Fin15AnchoredAtom1975 Fin15AnchoredAtom1976 Fin15AnchoredAtom1986 Fin15AnchoredAtom2051
    Fin15AnchoredAtom2055 Fin15AnchoredAtom2056 Fin15AnchoredAtom2060 Fin15AnchoredAtom2061
    Fin15AnchoredAtom2071 Fin15AnchoredAtom2075 Fin15AnchoredAtom2076 Fin15AnchoredAtom2086
    Fin15AnchoredAtom2096 Fin15AnchoredAtom2556 Fin15AnchoredAtom2560 Fin15AnchoredAtom2561
    Fin15AnchoredAtom2565 Fin15AnchoredAtom2566 Fin15AnchoredAtom2576 Fin15AnchoredAtom2580
    Fin15AnchoredAtom2581 Fin15AnchoredAtom2591 Fin15AnchoredAtom2601 Fin15AnchoredAtom2755
    Fin15AnchoredAtom2756 Fin15AnchoredAtom2766 Fin15AnchoredAtom2776 Fin15AnchoredAtom2796
    Fin15AnchoredAtom3271 Fin15AnchoredAtom3275 Fin15AnchoredAtom3276 Fin15AnchoredAtom3280
    Fin15AnchoredAtom3281 Fin15AnchoredAtom3291 Fin15AnchoredAtom3295 Fin15AnchoredAtom3296
    Fin15AnchoredAtom3306 Fin15AnchoredAtom3316 Fin15AnchoredAtom3470 Fin15AnchoredAtom3471
    Fin15AnchoredAtom3481 Fin15AnchoredAtom3491 Fin15AnchoredAtom3511 Fin15AnchoredAtom4505
    Fin15AnchoredAtom4506 Fin15AnchoredAtom4516 Fin15AnchoredAtom4526 Fin15AnchoredAtom4546
    Fin15AnchoredAtom4777 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31050 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom1978 chi ∧
      ¬Fin15AnchoredAtom1979 chi ∧
      ¬Fin15AnchoredAtom1984 chi ∧
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
      ¬Fin15AnchoredAtom2562 chi ∧
      ¬Fin15AnchoredAtom2564 chi ∧
      ¬Fin15AnchoredAtom2565 chi ∧
      ¬Fin15AnchoredAtom2568 chi ∧
      ¬Fin15AnchoredAtom2569 chi ∧
      ¬Fin15AnchoredAtom2574 chi ∧
      ¬Fin15AnchoredAtom2593 chi ∧
      ¬Fin15AnchoredAtom2594 chi ∧
      ¬Fin15AnchoredAtom2599 chi ∧
      ¬Fin15AnchoredAtom2605 chi ∧
      ¬Fin15AnchoredAtom2768 chi ∧
      ¬Fin15AnchoredAtom2769 chi ∧
      ¬Fin15AnchoredAtom2774 chi ∧
      ¬Fin15AnchoredAtom2780 chi ∧
      ¬Fin15AnchoredAtom2810 chi ∧
      ¬Fin15AnchoredAtom3277 chi ∧
      ¬Fin15AnchoredAtom3279 chi ∧
      ¬Fin15AnchoredAtom3280 chi ∧
      ¬Fin15AnchoredAtom3283 chi ∧
      ¬Fin15AnchoredAtom3284 chi ∧
      ¬Fin15AnchoredAtom3289 chi ∧
      ¬Fin15AnchoredAtom3308 chi ∧
      ¬Fin15AnchoredAtom3309 chi ∧
      ¬Fin15AnchoredAtom3314 chi ∧
      ¬Fin15AnchoredAtom3320 chi ∧
      ¬Fin15AnchoredAtom3483 chi ∧
      ¬Fin15AnchoredAtom3484 chi ∧
      ¬Fin15AnchoredAtom3489 chi ∧
      ¬Fin15AnchoredAtom3495 chi ∧
      ¬Fin15AnchoredAtom3525 chi ∧
      ¬Fin15AnchoredAtom4518 chi ∧
      ¬Fin15AnchoredAtom4519 chi ∧
      ¬Fin15AnchoredAtom4524 chi ∧
      ¬Fin15AnchoredAtom4530 chi ∧
      ¬Fin15AnchoredAtom4560 chi ∧
      ¬Fin15AnchoredAtom4791 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 7, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13971
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1960 Fin15AnchoredAtom1961 Fin15AnchoredAtom1963
    Fin15AnchoredAtom1964 Fin15AnchoredAtom1972 Fin15AnchoredAtom1974 Fin15AnchoredAtom1975
    Fin15AnchoredAtom1978 Fin15AnchoredAtom1979 Fin15AnchoredAtom1984 Fin15AnchoredAtom2057
    Fin15AnchoredAtom2059 Fin15AnchoredAtom2060 Fin15AnchoredAtom2063 Fin15AnchoredAtom2064
    Fin15AnchoredAtom2069 Fin15AnchoredAtom2088 Fin15AnchoredAtom2089 Fin15AnchoredAtom2094
    Fin15AnchoredAtom2100 Fin15AnchoredAtom2562 Fin15AnchoredAtom2564 Fin15AnchoredAtom2565
    Fin15AnchoredAtom2568 Fin15AnchoredAtom2569 Fin15AnchoredAtom2574 Fin15AnchoredAtom2593
    Fin15AnchoredAtom2594 Fin15AnchoredAtom2599 Fin15AnchoredAtom2605 Fin15AnchoredAtom2768
    Fin15AnchoredAtom2769 Fin15AnchoredAtom2774 Fin15AnchoredAtom2780 Fin15AnchoredAtom2810
    Fin15AnchoredAtom3277 Fin15AnchoredAtom3279 Fin15AnchoredAtom3280 Fin15AnchoredAtom3283
    Fin15AnchoredAtom3284 Fin15AnchoredAtom3289 Fin15AnchoredAtom3308 Fin15AnchoredAtom3309
    Fin15AnchoredAtom3314 Fin15AnchoredAtom3320 Fin15AnchoredAtom3483 Fin15AnchoredAtom3484
    Fin15AnchoredAtom3489 Fin15AnchoredAtom3495 Fin15AnchoredAtom3525 Fin15AnchoredAtom4518
    Fin15AnchoredAtom4519 Fin15AnchoredAtom4524 Fin15AnchoredAtom4530 Fin15AnchoredAtom4560
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

theorem fin15Anchored_clause31051 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom1976 chi ∧
      ¬Fin15AnchoredAtom1978 chi ∧
      ¬Fin15AnchoredAtom1980 chi ∧
      ¬Fin15AnchoredAtom1985 chi ∧
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
      ¬Fin15AnchoredAtom2562 chi ∧
      ¬Fin15AnchoredAtom2564 chi ∧
      ¬Fin15AnchoredAtom2566 chi ∧
      ¬Fin15AnchoredAtom2568 chi ∧
      ¬Fin15AnchoredAtom2570 chi ∧
      ¬Fin15AnchoredAtom2575 chi ∧
      ¬Fin15AnchoredAtom2593 chi ∧
      ¬Fin15AnchoredAtom2595 chi ∧
      ¬Fin15AnchoredAtom2600 chi ∧
      ¬Fin15AnchoredAtom2606 chi ∧
      ¬Fin15AnchoredAtom2768 chi ∧
      ¬Fin15AnchoredAtom2770 chi ∧
      ¬Fin15AnchoredAtom2775 chi ∧
      ¬Fin15AnchoredAtom2781 chi ∧
      ¬Fin15AnchoredAtom2811 chi ∧
      ¬Fin15AnchoredAtom3277 chi ∧
      ¬Fin15AnchoredAtom3279 chi ∧
      ¬Fin15AnchoredAtom3281 chi ∧
      ¬Fin15AnchoredAtom3283 chi ∧
      ¬Fin15AnchoredAtom3285 chi ∧
      ¬Fin15AnchoredAtom3290 chi ∧
      ¬Fin15AnchoredAtom3308 chi ∧
      ¬Fin15AnchoredAtom3310 chi ∧
      ¬Fin15AnchoredAtom3315 chi ∧
      ¬Fin15AnchoredAtom3321 chi ∧
      ¬Fin15AnchoredAtom3483 chi ∧
      ¬Fin15AnchoredAtom3485 chi ∧
      ¬Fin15AnchoredAtom3490 chi ∧
      ¬Fin15AnchoredAtom3496 chi ∧
      ¬Fin15AnchoredAtom3526 chi ∧
      ¬Fin15AnchoredAtom4518 chi ∧
      ¬Fin15AnchoredAtom4520 chi ∧
      ¬Fin15AnchoredAtom4525 chi ∧
      ¬Fin15AnchoredAtom4531 chi ∧
      ¬Fin15AnchoredAtom4561 chi ∧
      ¬Fin15AnchoredAtom4792 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 7, 9, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22163
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1960 Fin15AnchoredAtom1961 Fin15AnchoredAtom1963
    Fin15AnchoredAtom1965 Fin15AnchoredAtom1972 Fin15AnchoredAtom1974 Fin15AnchoredAtom1976
    Fin15AnchoredAtom1978 Fin15AnchoredAtom1980 Fin15AnchoredAtom1985 Fin15AnchoredAtom2057
    Fin15AnchoredAtom2059 Fin15AnchoredAtom2061 Fin15AnchoredAtom2063 Fin15AnchoredAtom2065
    Fin15AnchoredAtom2070 Fin15AnchoredAtom2088 Fin15AnchoredAtom2090 Fin15AnchoredAtom2095
    Fin15AnchoredAtom2101 Fin15AnchoredAtom2562 Fin15AnchoredAtom2564 Fin15AnchoredAtom2566
    Fin15AnchoredAtom2568 Fin15AnchoredAtom2570 Fin15AnchoredAtom2575 Fin15AnchoredAtom2593
    Fin15AnchoredAtom2595 Fin15AnchoredAtom2600 Fin15AnchoredAtom2606 Fin15AnchoredAtom2768
    Fin15AnchoredAtom2770 Fin15AnchoredAtom2775 Fin15AnchoredAtom2781 Fin15AnchoredAtom2811
    Fin15AnchoredAtom3277 Fin15AnchoredAtom3279 Fin15AnchoredAtom3281 Fin15AnchoredAtom3283
    Fin15AnchoredAtom3285 Fin15AnchoredAtom3290 Fin15AnchoredAtom3308 Fin15AnchoredAtom3310
    Fin15AnchoredAtom3315 Fin15AnchoredAtom3321 Fin15AnchoredAtom3483 Fin15AnchoredAtom3485
    Fin15AnchoredAtom3490 Fin15AnchoredAtom3496 Fin15AnchoredAtom3526 Fin15AnchoredAtom4518
    Fin15AnchoredAtom4520 Fin15AnchoredAtom4525 Fin15AnchoredAtom4531 Fin15AnchoredAtom4561
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

theorem fin15Anchored_clause31052 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom1976 chi ∧
      ¬Fin15AnchoredAtom1979 chi ∧
      ¬Fin15AnchoredAtom1980 chi ∧
      ¬Fin15AnchoredAtom1986 chi ∧
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
      ¬Fin15AnchoredAtom2562 chi ∧
      ¬Fin15AnchoredAtom2565 chi ∧
      ¬Fin15AnchoredAtom2566 chi ∧
      ¬Fin15AnchoredAtom2569 chi ∧
      ¬Fin15AnchoredAtom2570 chi ∧
      ¬Fin15AnchoredAtom2576 chi ∧
      ¬Fin15AnchoredAtom2594 chi ∧
      ¬Fin15AnchoredAtom2595 chi ∧
      ¬Fin15AnchoredAtom2601 chi ∧
      ¬Fin15AnchoredAtom2607 chi ∧
      ¬Fin15AnchoredAtom2769 chi ∧
      ¬Fin15AnchoredAtom2770 chi ∧
      ¬Fin15AnchoredAtom2776 chi ∧
      ¬Fin15AnchoredAtom2782 chi ∧
      ¬Fin15AnchoredAtom2812 chi ∧
      ¬Fin15AnchoredAtom3277 chi ∧
      ¬Fin15AnchoredAtom3280 chi ∧
      ¬Fin15AnchoredAtom3281 chi ∧
      ¬Fin15AnchoredAtom3284 chi ∧
      ¬Fin15AnchoredAtom3285 chi ∧
      ¬Fin15AnchoredAtom3291 chi ∧
      ¬Fin15AnchoredAtom3309 chi ∧
      ¬Fin15AnchoredAtom3310 chi ∧
      ¬Fin15AnchoredAtom3316 chi ∧
      ¬Fin15AnchoredAtom3322 chi ∧
      ¬Fin15AnchoredAtom3484 chi ∧
      ¬Fin15AnchoredAtom3485 chi ∧
      ¬Fin15AnchoredAtom3491 chi ∧
      ¬Fin15AnchoredAtom3497 chi ∧
      ¬Fin15AnchoredAtom3527 chi ∧
      ¬Fin15AnchoredAtom4519 chi ∧
      ¬Fin15AnchoredAtom4520 chi ∧
      ¬Fin15AnchoredAtom4526 chi ∧
      ¬Fin15AnchoredAtom4532 chi ∧
      ¬Fin15AnchoredAtom4562 chi ∧
      ¬Fin15AnchoredAtom4793 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 7, 9, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26259
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1960 Fin15AnchoredAtom1961 Fin15AnchoredAtom1964
    Fin15AnchoredAtom1965 Fin15AnchoredAtom1972 Fin15AnchoredAtom1975 Fin15AnchoredAtom1976
    Fin15AnchoredAtom1979 Fin15AnchoredAtom1980 Fin15AnchoredAtom1986 Fin15AnchoredAtom2057
    Fin15AnchoredAtom2060 Fin15AnchoredAtom2061 Fin15AnchoredAtom2064 Fin15AnchoredAtom2065
    Fin15AnchoredAtom2071 Fin15AnchoredAtom2089 Fin15AnchoredAtom2090 Fin15AnchoredAtom2096
    Fin15AnchoredAtom2102 Fin15AnchoredAtom2562 Fin15AnchoredAtom2565 Fin15AnchoredAtom2566
    Fin15AnchoredAtom2569 Fin15AnchoredAtom2570 Fin15AnchoredAtom2576 Fin15AnchoredAtom2594
    Fin15AnchoredAtom2595 Fin15AnchoredAtom2601 Fin15AnchoredAtom2607 Fin15AnchoredAtom2769
    Fin15AnchoredAtom2770 Fin15AnchoredAtom2776 Fin15AnchoredAtom2782 Fin15AnchoredAtom2812
    Fin15AnchoredAtom3277 Fin15AnchoredAtom3280 Fin15AnchoredAtom3281 Fin15AnchoredAtom3284
    Fin15AnchoredAtom3285 Fin15AnchoredAtom3291 Fin15AnchoredAtom3309 Fin15AnchoredAtom3310
    Fin15AnchoredAtom3316 Fin15AnchoredAtom3322 Fin15AnchoredAtom3484 Fin15AnchoredAtom3485
    Fin15AnchoredAtom3491 Fin15AnchoredAtom3497 Fin15AnchoredAtom3527 Fin15AnchoredAtom4519
    Fin15AnchoredAtom4520 Fin15AnchoredAtom4526 Fin15AnchoredAtom4532 Fin15AnchoredAtom4562
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

theorem fin15Anchored_clause31053 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom1962 chi ∧
      ¬Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom1973 chi ∧
      ¬Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom1981 chi ∧
      ¬Fin15AnchoredAtom1982 chi ∧
      ¬Fin15AnchoredAtom1984 chi ∧
      ¬Fin15AnchoredAtom2058 chi ∧
      ¬Fin15AnchoredAtom2059 chi ∧
      ¬Fin15AnchoredAtom2060 chi ∧
      ¬Fin15AnchoredAtom2066 chi ∧
      ¬Fin15AnchoredAtom2067 chi ∧
      ¬Fin15AnchoredAtom2069 chi ∧
      ¬Fin15AnchoredAtom2091 chi ∧
      ¬Fin15AnchoredAtom2092 chi ∧
      ¬Fin15AnchoredAtom2094 chi ∧
      ¬Fin15AnchoredAtom2103 chi ∧
      ¬Fin15AnchoredAtom2563 chi ∧
      ¬Fin15AnchoredAtom2564 chi ∧
      ¬Fin15AnchoredAtom2565 chi ∧
      ¬Fin15AnchoredAtom2571 chi ∧
      ¬Fin15AnchoredAtom2572 chi ∧
      ¬Fin15AnchoredAtom2574 chi ∧
      ¬Fin15AnchoredAtom2596 chi ∧
      ¬Fin15AnchoredAtom2597 chi ∧
      ¬Fin15AnchoredAtom2599 chi ∧
      ¬Fin15AnchoredAtom2608 chi ∧
      ¬Fin15AnchoredAtom2771 chi ∧
      ¬Fin15AnchoredAtom2772 chi ∧
      ¬Fin15AnchoredAtom2774 chi ∧
      ¬Fin15AnchoredAtom2783 chi ∧
      ¬Fin15AnchoredAtom2813 chi ∧
      ¬Fin15AnchoredAtom3278 chi ∧
      ¬Fin15AnchoredAtom3279 chi ∧
      ¬Fin15AnchoredAtom3280 chi ∧
      ¬Fin15AnchoredAtom3286 chi ∧
      ¬Fin15AnchoredAtom3287 chi ∧
      ¬Fin15AnchoredAtom3289 chi ∧
      ¬Fin15AnchoredAtom3311 chi ∧
      ¬Fin15AnchoredAtom3312 chi ∧
      ¬Fin15AnchoredAtom3314 chi ∧
      ¬Fin15AnchoredAtom3323 chi ∧
      ¬Fin15AnchoredAtom3486 chi ∧
      ¬Fin15AnchoredAtom3487 chi ∧
      ¬Fin15AnchoredAtom3489 chi ∧
      ¬Fin15AnchoredAtom3498 chi ∧
      ¬Fin15AnchoredAtom3528 chi ∧
      ¬Fin15AnchoredAtom4521 chi ∧
      ¬Fin15AnchoredAtom4522 chi ∧
      ¬Fin15AnchoredAtom4524 chi ∧
      ¬Fin15AnchoredAtom4533 chi ∧
      ¬Fin15AnchoredAtom4563 chi ∧
      ¬Fin15AnchoredAtom4794 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 7, 9, 11, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask14995
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1960 Fin15AnchoredAtom1962 Fin15AnchoredAtom1963
    Fin15AnchoredAtom1964 Fin15AnchoredAtom1973 Fin15AnchoredAtom1974 Fin15AnchoredAtom1975
    Fin15AnchoredAtom1981 Fin15AnchoredAtom1982 Fin15AnchoredAtom1984 Fin15AnchoredAtom2058
    Fin15AnchoredAtom2059 Fin15AnchoredAtom2060 Fin15AnchoredAtom2066 Fin15AnchoredAtom2067
    Fin15AnchoredAtom2069 Fin15AnchoredAtom2091 Fin15AnchoredAtom2092 Fin15AnchoredAtom2094
    Fin15AnchoredAtom2103 Fin15AnchoredAtom2563 Fin15AnchoredAtom2564 Fin15AnchoredAtom2565
    Fin15AnchoredAtom2571 Fin15AnchoredAtom2572 Fin15AnchoredAtom2574 Fin15AnchoredAtom2596
    Fin15AnchoredAtom2597 Fin15AnchoredAtom2599 Fin15AnchoredAtom2608 Fin15AnchoredAtom2771
    Fin15AnchoredAtom2772 Fin15AnchoredAtom2774 Fin15AnchoredAtom2783 Fin15AnchoredAtom2813
    Fin15AnchoredAtom3278 Fin15AnchoredAtom3279 Fin15AnchoredAtom3280 Fin15AnchoredAtom3286
    Fin15AnchoredAtom3287 Fin15AnchoredAtom3289 Fin15AnchoredAtom3311 Fin15AnchoredAtom3312
    Fin15AnchoredAtom3314 Fin15AnchoredAtom3323 Fin15AnchoredAtom3486 Fin15AnchoredAtom3487
    Fin15AnchoredAtom3489 Fin15AnchoredAtom3498 Fin15AnchoredAtom3528 Fin15AnchoredAtom4521
    Fin15AnchoredAtom4522 Fin15AnchoredAtom4524 Fin15AnchoredAtom4533 Fin15AnchoredAtom4563
    Fin15AnchoredAtom4794 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31054 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom1962 chi ∧
      ¬Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom1973 chi ∧
      ¬Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom1976 chi ∧
      ¬Fin15AnchoredAtom1981 chi ∧
      ¬Fin15AnchoredAtom1983 chi ∧
      ¬Fin15AnchoredAtom1985 chi ∧
      ¬Fin15AnchoredAtom2058 chi ∧
      ¬Fin15AnchoredAtom2059 chi ∧
      ¬Fin15AnchoredAtom2061 chi ∧
      ¬Fin15AnchoredAtom2066 chi ∧
      ¬Fin15AnchoredAtom2068 chi ∧
      ¬Fin15AnchoredAtom2070 chi ∧
      ¬Fin15AnchoredAtom2091 chi ∧
      ¬Fin15AnchoredAtom2093 chi ∧
      ¬Fin15AnchoredAtom2095 chi ∧
      ¬Fin15AnchoredAtom2104 chi ∧
      ¬Fin15AnchoredAtom2563 chi ∧
      ¬Fin15AnchoredAtom2564 chi ∧
      ¬Fin15AnchoredAtom2566 chi ∧
      ¬Fin15AnchoredAtom2571 chi ∧
      ¬Fin15AnchoredAtom2573 chi ∧
      ¬Fin15AnchoredAtom2575 chi ∧
      ¬Fin15AnchoredAtom2596 chi ∧
      ¬Fin15AnchoredAtom2598 chi ∧
      ¬Fin15AnchoredAtom2600 chi ∧
      ¬Fin15AnchoredAtom2609 chi ∧
      ¬Fin15AnchoredAtom2771 chi ∧
      ¬Fin15AnchoredAtom2773 chi ∧
      ¬Fin15AnchoredAtom2775 chi ∧
      ¬Fin15AnchoredAtom2784 chi ∧
      ¬Fin15AnchoredAtom2814 chi ∧
      ¬Fin15AnchoredAtom3278 chi ∧
      ¬Fin15AnchoredAtom3279 chi ∧
      ¬Fin15AnchoredAtom3281 chi ∧
      ¬Fin15AnchoredAtom3286 chi ∧
      ¬Fin15AnchoredAtom3288 chi ∧
      ¬Fin15AnchoredAtom3290 chi ∧
      ¬Fin15AnchoredAtom3311 chi ∧
      ¬Fin15AnchoredAtom3313 chi ∧
      ¬Fin15AnchoredAtom3315 chi ∧
      ¬Fin15AnchoredAtom3324 chi ∧
      ¬Fin15AnchoredAtom3486 chi ∧
      ¬Fin15AnchoredAtom3488 chi ∧
      ¬Fin15AnchoredAtom3490 chi ∧
      ¬Fin15AnchoredAtom3499 chi ∧
      ¬Fin15AnchoredAtom3529 chi ∧
      ¬Fin15AnchoredAtom4521 chi ∧
      ¬Fin15AnchoredAtom4523 chi ∧
      ¬Fin15AnchoredAtom4525 chi ∧
      ¬Fin15AnchoredAtom4534 chi ∧
      ¬Fin15AnchoredAtom4564 chi ∧
      ¬Fin15AnchoredAtom4795 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 7, 9, 11, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask23187
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1960 Fin15AnchoredAtom1962 Fin15AnchoredAtom1963
    Fin15AnchoredAtom1965 Fin15AnchoredAtom1973 Fin15AnchoredAtom1974 Fin15AnchoredAtom1976
    Fin15AnchoredAtom1981 Fin15AnchoredAtom1983 Fin15AnchoredAtom1985 Fin15AnchoredAtom2058
    Fin15AnchoredAtom2059 Fin15AnchoredAtom2061 Fin15AnchoredAtom2066 Fin15AnchoredAtom2068
    Fin15AnchoredAtom2070 Fin15AnchoredAtom2091 Fin15AnchoredAtom2093 Fin15AnchoredAtom2095
    Fin15AnchoredAtom2104 Fin15AnchoredAtom2563 Fin15AnchoredAtom2564 Fin15AnchoredAtom2566
    Fin15AnchoredAtom2571 Fin15AnchoredAtom2573 Fin15AnchoredAtom2575 Fin15AnchoredAtom2596
    Fin15AnchoredAtom2598 Fin15AnchoredAtom2600 Fin15AnchoredAtom2609 Fin15AnchoredAtom2771
    Fin15AnchoredAtom2773 Fin15AnchoredAtom2775 Fin15AnchoredAtom2784 Fin15AnchoredAtom2814
    Fin15AnchoredAtom3278 Fin15AnchoredAtom3279 Fin15AnchoredAtom3281 Fin15AnchoredAtom3286
    Fin15AnchoredAtom3288 Fin15AnchoredAtom3290 Fin15AnchoredAtom3311 Fin15AnchoredAtom3313
    Fin15AnchoredAtom3315 Fin15AnchoredAtom3324 Fin15AnchoredAtom3486 Fin15AnchoredAtom3488
    Fin15AnchoredAtom3490 Fin15AnchoredAtom3499 Fin15AnchoredAtom3529 Fin15AnchoredAtom4521
    Fin15AnchoredAtom4523 Fin15AnchoredAtom4525 Fin15AnchoredAtom4534 Fin15AnchoredAtom4564
    Fin15AnchoredAtom4795 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31055 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom1976 chi ∧
      ¬Fin15AnchoredAtom1984 chi ∧
      ¬Fin15AnchoredAtom1985 chi ∧
      ¬Fin15AnchoredAtom1986 chi ∧
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
      ¬Fin15AnchoredAtom2564 chi ∧
      ¬Fin15AnchoredAtom2565 chi ∧
      ¬Fin15AnchoredAtom2566 chi ∧
      ¬Fin15AnchoredAtom2574 chi ∧
      ¬Fin15AnchoredAtom2575 chi ∧
      ¬Fin15AnchoredAtom2576 chi ∧
      ¬Fin15AnchoredAtom2599 chi ∧
      ¬Fin15AnchoredAtom2600 chi ∧
      ¬Fin15AnchoredAtom2601 chi ∧
      ¬Fin15AnchoredAtom2611 chi ∧
      ¬Fin15AnchoredAtom2774 chi ∧
      ¬Fin15AnchoredAtom2775 chi ∧
      ¬Fin15AnchoredAtom2776 chi ∧
      ¬Fin15AnchoredAtom2786 chi ∧
      ¬Fin15AnchoredAtom2816 chi ∧
      ¬Fin15AnchoredAtom3279 chi ∧
      ¬Fin15AnchoredAtom3280 chi ∧
      ¬Fin15AnchoredAtom3281 chi ∧
      ¬Fin15AnchoredAtom3289 chi ∧
      ¬Fin15AnchoredAtom3290 chi ∧
      ¬Fin15AnchoredAtom3291 chi ∧
      ¬Fin15AnchoredAtom3314 chi ∧
      ¬Fin15AnchoredAtom3315 chi ∧
      ¬Fin15AnchoredAtom3316 chi ∧
      ¬Fin15AnchoredAtom3326 chi ∧
      ¬Fin15AnchoredAtom3489 chi ∧
      ¬Fin15AnchoredAtom3490 chi ∧
      ¬Fin15AnchoredAtom3491 chi ∧
      ¬Fin15AnchoredAtom3501 chi ∧
      ¬Fin15AnchoredAtom3531 chi ∧
      ¬Fin15AnchoredAtom4524 chi ∧
      ¬Fin15AnchoredAtom4525 chi ∧
      ¬Fin15AnchoredAtom4526 chi ∧
      ¬Fin15AnchoredAtom4536 chi ∧
      ¬Fin15AnchoredAtom4566 chi ∧
      ¬Fin15AnchoredAtom4797 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 7, 9, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29331
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1960 Fin15AnchoredAtom1963 Fin15AnchoredAtom1964
    Fin15AnchoredAtom1965 Fin15AnchoredAtom1974 Fin15AnchoredAtom1975 Fin15AnchoredAtom1976
    Fin15AnchoredAtom1984 Fin15AnchoredAtom1985 Fin15AnchoredAtom1986 Fin15AnchoredAtom2059
    Fin15AnchoredAtom2060 Fin15AnchoredAtom2061 Fin15AnchoredAtom2069 Fin15AnchoredAtom2070
    Fin15AnchoredAtom2071 Fin15AnchoredAtom2094 Fin15AnchoredAtom2095 Fin15AnchoredAtom2096
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2564 Fin15AnchoredAtom2565 Fin15AnchoredAtom2566
    Fin15AnchoredAtom2574 Fin15AnchoredAtom2575 Fin15AnchoredAtom2576 Fin15AnchoredAtom2599
    Fin15AnchoredAtom2600 Fin15AnchoredAtom2601 Fin15AnchoredAtom2611 Fin15AnchoredAtom2774
    Fin15AnchoredAtom2775 Fin15AnchoredAtom2776 Fin15AnchoredAtom2786 Fin15AnchoredAtom2816
    Fin15AnchoredAtom3279 Fin15AnchoredAtom3280 Fin15AnchoredAtom3281 Fin15AnchoredAtom3289
    Fin15AnchoredAtom3290 Fin15AnchoredAtom3291 Fin15AnchoredAtom3314 Fin15AnchoredAtom3315
    Fin15AnchoredAtom3316 Fin15AnchoredAtom3326 Fin15AnchoredAtom3489 Fin15AnchoredAtom3490
    Fin15AnchoredAtom3491 Fin15AnchoredAtom3501 Fin15AnchoredAtom3531 Fin15AnchoredAtom4524
    Fin15AnchoredAtom4525 Fin15AnchoredAtom4526 Fin15AnchoredAtom4536 Fin15AnchoredAtom4566
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

theorem fin15Anchored_clause31056 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom1962 chi ∧
      ¬Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom1977 chi ∧
      ¬Fin15AnchoredAtom1978 chi ∧
      ¬Fin15AnchoredAtom1979 chi ∧
      ¬Fin15AnchoredAtom1981 chi ∧
      ¬Fin15AnchoredAtom1982 chi ∧
      ¬Fin15AnchoredAtom1984 chi ∧
      ¬Fin15AnchoredAtom2062 chi ∧
      ¬Fin15AnchoredAtom2063 chi ∧
      ¬Fin15AnchoredAtom2064 chi ∧
      ¬Fin15AnchoredAtom2066 chi ∧
      ¬Fin15AnchoredAtom2067 chi ∧
      ¬Fin15AnchoredAtom2069 chi ∧
      ¬Fin15AnchoredAtom2097 chi ∧
      ¬Fin15AnchoredAtom2098 chi ∧
      ¬Fin15AnchoredAtom2100 chi ∧
      ¬Fin15AnchoredAtom2103 chi ∧
      ¬Fin15AnchoredAtom2567 chi ∧
      ¬Fin15AnchoredAtom2568 chi ∧
      ¬Fin15AnchoredAtom2569 chi ∧
      ¬Fin15AnchoredAtom2571 chi ∧
      ¬Fin15AnchoredAtom2572 chi ∧
      ¬Fin15AnchoredAtom2574 chi ∧
      ¬Fin15AnchoredAtom2602 chi ∧
      ¬Fin15AnchoredAtom2603 chi ∧
      ¬Fin15AnchoredAtom2605 chi ∧
      ¬Fin15AnchoredAtom2608 chi ∧
      ¬Fin15AnchoredAtom2777 chi ∧
      ¬Fin15AnchoredAtom2778 chi ∧
      ¬Fin15AnchoredAtom2780 chi ∧
      ¬Fin15AnchoredAtom2783 chi ∧
      ¬Fin15AnchoredAtom2817 chi ∧
      ¬Fin15AnchoredAtom3282 chi ∧
      ¬Fin15AnchoredAtom3283 chi ∧
      ¬Fin15AnchoredAtom3284 chi ∧
      ¬Fin15AnchoredAtom3286 chi ∧
      ¬Fin15AnchoredAtom3287 chi ∧
      ¬Fin15AnchoredAtom3289 chi ∧
      ¬Fin15AnchoredAtom3317 chi ∧
      ¬Fin15AnchoredAtom3318 chi ∧
      ¬Fin15AnchoredAtom3320 chi ∧
      ¬Fin15AnchoredAtom3323 chi ∧
      ¬Fin15AnchoredAtom3492 chi ∧
      ¬Fin15AnchoredAtom3493 chi ∧
      ¬Fin15AnchoredAtom3495 chi ∧
      ¬Fin15AnchoredAtom3498 chi ∧
      ¬Fin15AnchoredAtom3532 chi ∧
      ¬Fin15AnchoredAtom4527 chi ∧
      ¬Fin15AnchoredAtom4528 chi ∧
      ¬Fin15AnchoredAtom4530 chi ∧
      ¬Fin15AnchoredAtom4533 chi ∧
      ¬Fin15AnchoredAtom4567 chi ∧
      ¬Fin15AnchoredAtom4798 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 7, 10, 11, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask15507
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1961 Fin15AnchoredAtom1962 Fin15AnchoredAtom1963
    Fin15AnchoredAtom1964 Fin15AnchoredAtom1977 Fin15AnchoredAtom1978 Fin15AnchoredAtom1979
    Fin15AnchoredAtom1981 Fin15AnchoredAtom1982 Fin15AnchoredAtom1984 Fin15AnchoredAtom2062
    Fin15AnchoredAtom2063 Fin15AnchoredAtom2064 Fin15AnchoredAtom2066 Fin15AnchoredAtom2067
    Fin15AnchoredAtom2069 Fin15AnchoredAtom2097 Fin15AnchoredAtom2098 Fin15AnchoredAtom2100
    Fin15AnchoredAtom2103 Fin15AnchoredAtom2567 Fin15AnchoredAtom2568 Fin15AnchoredAtom2569
    Fin15AnchoredAtom2571 Fin15AnchoredAtom2572 Fin15AnchoredAtom2574 Fin15AnchoredAtom2602
    Fin15AnchoredAtom2603 Fin15AnchoredAtom2605 Fin15AnchoredAtom2608 Fin15AnchoredAtom2777
    Fin15AnchoredAtom2778 Fin15AnchoredAtom2780 Fin15AnchoredAtom2783 Fin15AnchoredAtom2817
    Fin15AnchoredAtom3282 Fin15AnchoredAtom3283 Fin15AnchoredAtom3284 Fin15AnchoredAtom3286
    Fin15AnchoredAtom3287 Fin15AnchoredAtom3289 Fin15AnchoredAtom3317 Fin15AnchoredAtom3318
    Fin15AnchoredAtom3320 Fin15AnchoredAtom3323 Fin15AnchoredAtom3492 Fin15AnchoredAtom3493
    Fin15AnchoredAtom3495 Fin15AnchoredAtom3498 Fin15AnchoredAtom3532 Fin15AnchoredAtom4527
    Fin15AnchoredAtom4528 Fin15AnchoredAtom4530 Fin15AnchoredAtom4533 Fin15AnchoredAtom4567
    Fin15AnchoredAtom4798 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31057 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom1978 chi ∧
      ¬Fin15AnchoredAtom1979 chi ∧
      ¬Fin15AnchoredAtom1980 chi ∧
      ¬Fin15AnchoredAtom1984 chi ∧
      ¬Fin15AnchoredAtom1985 chi ∧
      ¬Fin15AnchoredAtom1986 chi ∧
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
      ¬Fin15AnchoredAtom2568 chi ∧
      ¬Fin15AnchoredAtom2569 chi ∧
      ¬Fin15AnchoredAtom2570 chi ∧
      ¬Fin15AnchoredAtom2574 chi ∧
      ¬Fin15AnchoredAtom2575 chi ∧
      ¬Fin15AnchoredAtom2576 chi ∧
      ¬Fin15AnchoredAtom2605 chi ∧
      ¬Fin15AnchoredAtom2606 chi ∧
      ¬Fin15AnchoredAtom2607 chi ∧
      ¬Fin15AnchoredAtom2611 chi ∧
      ¬Fin15AnchoredAtom2780 chi ∧
      ¬Fin15AnchoredAtom2781 chi ∧
      ¬Fin15AnchoredAtom2782 chi ∧
      ¬Fin15AnchoredAtom2786 chi ∧
      ¬Fin15AnchoredAtom2820 chi ∧
      ¬Fin15AnchoredAtom3283 chi ∧
      ¬Fin15AnchoredAtom3284 chi ∧
      ¬Fin15AnchoredAtom3285 chi ∧
      ¬Fin15AnchoredAtom3289 chi ∧
      ¬Fin15AnchoredAtom3290 chi ∧
      ¬Fin15AnchoredAtom3291 chi ∧
      ¬Fin15AnchoredAtom3320 chi ∧
      ¬Fin15AnchoredAtom3321 chi ∧
      ¬Fin15AnchoredAtom3322 chi ∧
      ¬Fin15AnchoredAtom3326 chi ∧
      ¬Fin15AnchoredAtom3495 chi ∧
      ¬Fin15AnchoredAtom3496 chi ∧
      ¬Fin15AnchoredAtom3497 chi ∧
      ¬Fin15AnchoredAtom3501 chi ∧
      ¬Fin15AnchoredAtom3535 chi ∧
      ¬Fin15AnchoredAtom4530 chi ∧
      ¬Fin15AnchoredAtom4531 chi ∧
      ¬Fin15AnchoredAtom4532 chi ∧
      ¬Fin15AnchoredAtom4536 chi ∧
      ¬Fin15AnchoredAtom4570 chi ∧
      ¬Fin15AnchoredAtom4801 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 7, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29843
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1961 Fin15AnchoredAtom1963 Fin15AnchoredAtom1964
    Fin15AnchoredAtom1965 Fin15AnchoredAtom1978 Fin15AnchoredAtom1979 Fin15AnchoredAtom1980
    Fin15AnchoredAtom1984 Fin15AnchoredAtom1985 Fin15AnchoredAtom1986 Fin15AnchoredAtom2063
    Fin15AnchoredAtom2064 Fin15AnchoredAtom2065 Fin15AnchoredAtom2069 Fin15AnchoredAtom2070
    Fin15AnchoredAtom2071 Fin15AnchoredAtom2100 Fin15AnchoredAtom2101 Fin15AnchoredAtom2102
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2568 Fin15AnchoredAtom2569 Fin15AnchoredAtom2570
    Fin15AnchoredAtom2574 Fin15AnchoredAtom2575 Fin15AnchoredAtom2576 Fin15AnchoredAtom2605
    Fin15AnchoredAtom2606 Fin15AnchoredAtom2607 Fin15AnchoredAtom2611 Fin15AnchoredAtom2780
    Fin15AnchoredAtom2781 Fin15AnchoredAtom2782 Fin15AnchoredAtom2786 Fin15AnchoredAtom2820
    Fin15AnchoredAtom3283 Fin15AnchoredAtom3284 Fin15AnchoredAtom3285 Fin15AnchoredAtom3289
    Fin15AnchoredAtom3290 Fin15AnchoredAtom3291 Fin15AnchoredAtom3320 Fin15AnchoredAtom3321
    Fin15AnchoredAtom3322 Fin15AnchoredAtom3326 Fin15AnchoredAtom3495 Fin15AnchoredAtom3496
    Fin15AnchoredAtom3497 Fin15AnchoredAtom3501 Fin15AnchoredAtom3535 Fin15AnchoredAtom4530
    Fin15AnchoredAtom4531 Fin15AnchoredAtom4532 Fin15AnchoredAtom4536 Fin15AnchoredAtom4570
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

theorem fin15Anchored_clause31058 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1966 chi ∧
      ¬Fin15AnchoredAtom1967 chi ∧
      ¬Fin15AnchoredAtom1969 chi ∧
      ¬Fin15AnchoredAtom1970 chi ∧
      ¬Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom1978 chi ∧
      ¬Fin15AnchoredAtom1979 chi ∧
      ¬Fin15AnchoredAtom1984 chi ∧
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
      ¬Fin15AnchoredAtom2577 chi ∧
      ¬Fin15AnchoredAtom2579 chi ∧
      ¬Fin15AnchoredAtom2580 chi ∧
      ¬Fin15AnchoredAtom2583 chi ∧
      ¬Fin15AnchoredAtom2584 chi ∧
      ¬Fin15AnchoredAtom2589 chi ∧
      ¬Fin15AnchoredAtom2593 chi ∧
      ¬Fin15AnchoredAtom2594 chi ∧
      ¬Fin15AnchoredAtom2599 chi ∧
      ¬Fin15AnchoredAtom2605 chi ∧
      ¬Fin15AnchoredAtom2788 chi ∧
      ¬Fin15AnchoredAtom2789 chi ∧
      ¬Fin15AnchoredAtom2794 chi ∧
      ¬Fin15AnchoredAtom2800 chi ∧
      ¬Fin15AnchoredAtom2810 chi ∧
      ¬Fin15AnchoredAtom3292 chi ∧
      ¬Fin15AnchoredAtom3294 chi ∧
      ¬Fin15AnchoredAtom3295 chi ∧
      ¬Fin15AnchoredAtom3298 chi ∧
      ¬Fin15AnchoredAtom3299 chi ∧
      ¬Fin15AnchoredAtom3304 chi ∧
      ¬Fin15AnchoredAtom3308 chi ∧
      ¬Fin15AnchoredAtom3309 chi ∧
      ¬Fin15AnchoredAtom3314 chi ∧
      ¬Fin15AnchoredAtom3320 chi ∧
      ¬Fin15AnchoredAtom3503 chi ∧
      ¬Fin15AnchoredAtom3504 chi ∧
      ¬Fin15AnchoredAtom3509 chi ∧
      ¬Fin15AnchoredAtom3515 chi ∧
      ¬Fin15AnchoredAtom3525 chi ∧
      ¬Fin15AnchoredAtom4538 chi ∧
      ¬Fin15AnchoredAtom4539 chi ∧
      ¬Fin15AnchoredAtom4544 chi ∧
      ¬Fin15AnchoredAtom4550 chi ∧
      ¬Fin15AnchoredAtom4560 chi ∧
      ¬Fin15AnchoredAtom4806 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 8, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask14099
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1966 Fin15AnchoredAtom1967 Fin15AnchoredAtom1969
    Fin15AnchoredAtom1970 Fin15AnchoredAtom1972 Fin15AnchoredAtom1974 Fin15AnchoredAtom1975
    Fin15AnchoredAtom1978 Fin15AnchoredAtom1979 Fin15AnchoredAtom1984 Fin15AnchoredAtom2072
    Fin15AnchoredAtom2074 Fin15AnchoredAtom2075 Fin15AnchoredAtom2078 Fin15AnchoredAtom2079
    Fin15AnchoredAtom2084 Fin15AnchoredAtom2088 Fin15AnchoredAtom2089 Fin15AnchoredAtom2094
    Fin15AnchoredAtom2100 Fin15AnchoredAtom2577 Fin15AnchoredAtom2579 Fin15AnchoredAtom2580
    Fin15AnchoredAtom2583 Fin15AnchoredAtom2584 Fin15AnchoredAtom2589 Fin15AnchoredAtom2593
    Fin15AnchoredAtom2594 Fin15AnchoredAtom2599 Fin15AnchoredAtom2605 Fin15AnchoredAtom2788
    Fin15AnchoredAtom2789 Fin15AnchoredAtom2794 Fin15AnchoredAtom2800 Fin15AnchoredAtom2810
    Fin15AnchoredAtom3292 Fin15AnchoredAtom3294 Fin15AnchoredAtom3295 Fin15AnchoredAtom3298
    Fin15AnchoredAtom3299 Fin15AnchoredAtom3304 Fin15AnchoredAtom3308 Fin15AnchoredAtom3309
    Fin15AnchoredAtom3314 Fin15AnchoredAtom3320 Fin15AnchoredAtom3503 Fin15AnchoredAtom3504
    Fin15AnchoredAtom3509 Fin15AnchoredAtom3515 Fin15AnchoredAtom3525 Fin15AnchoredAtom4538
    Fin15AnchoredAtom4539 Fin15AnchoredAtom4544 Fin15AnchoredAtom4550 Fin15AnchoredAtom4560
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

theorem fin15Anchored_clause31059 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1966 chi ∧
      ¬Fin15AnchoredAtom1969 chi ∧
      ¬Fin15AnchoredAtom1970 chi ∧
      ¬Fin15AnchoredAtom1971 chi ∧
      ¬Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom1976 chi ∧
      ¬Fin15AnchoredAtom1984 chi ∧
      ¬Fin15AnchoredAtom1985 chi ∧
      ¬Fin15AnchoredAtom1986 chi ∧
      ¬Fin15AnchoredAtom2074 chi ∧
      ¬Fin15AnchoredAtom2075 chi ∧
      ¬Fin15AnchoredAtom2076 chi ∧
      ¬Fin15AnchoredAtom2084 chi ∧
      ¬Fin15AnchoredAtom2085 chi ∧
      ¬Fin15AnchoredAtom2086 chi ∧
      ¬Fin15AnchoredAtom2094 chi ∧
      ¬Fin15AnchoredAtom2095 chi ∧
      ¬Fin15AnchoredAtom2096 chi ∧
      ¬Fin15AnchoredAtom2106 chi ∧
      ¬Fin15AnchoredAtom2579 chi ∧
      ¬Fin15AnchoredAtom2580 chi ∧
      ¬Fin15AnchoredAtom2581 chi ∧
      ¬Fin15AnchoredAtom2589 chi ∧
      ¬Fin15AnchoredAtom2590 chi ∧
      ¬Fin15AnchoredAtom2591 chi ∧
      ¬Fin15AnchoredAtom2599 chi ∧
      ¬Fin15AnchoredAtom2600 chi ∧
      ¬Fin15AnchoredAtom2601 chi ∧
      ¬Fin15AnchoredAtom2611 chi ∧
      ¬Fin15AnchoredAtom2794 chi ∧
      ¬Fin15AnchoredAtom2795 chi ∧
      ¬Fin15AnchoredAtom2796 chi ∧
      ¬Fin15AnchoredAtom2806 chi ∧
      ¬Fin15AnchoredAtom2816 chi ∧
      ¬Fin15AnchoredAtom3294 chi ∧
      ¬Fin15AnchoredAtom3295 chi ∧
      ¬Fin15AnchoredAtom3296 chi ∧
      ¬Fin15AnchoredAtom3304 chi ∧
      ¬Fin15AnchoredAtom3305 chi ∧
      ¬Fin15AnchoredAtom3306 chi ∧
      ¬Fin15AnchoredAtom3314 chi ∧
      ¬Fin15AnchoredAtom3315 chi ∧
      ¬Fin15AnchoredAtom3316 chi ∧
      ¬Fin15AnchoredAtom3326 chi ∧
      ¬Fin15AnchoredAtom3509 chi ∧
      ¬Fin15AnchoredAtom3510 chi ∧
      ¬Fin15AnchoredAtom3511 chi ∧
      ¬Fin15AnchoredAtom3521 chi ∧
      ¬Fin15AnchoredAtom3531 chi ∧
      ¬Fin15AnchoredAtom4544 chi ∧
      ¬Fin15AnchoredAtom4545 chi ∧
      ¬Fin15AnchoredAtom4546 chi ∧
      ¬Fin15AnchoredAtom4556 chi ∧
      ¬Fin15AnchoredAtom4566 chi ∧
      ¬Fin15AnchoredAtom4812 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 8, 9, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29459
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1966 Fin15AnchoredAtom1969 Fin15AnchoredAtom1970
    Fin15AnchoredAtom1971 Fin15AnchoredAtom1974 Fin15AnchoredAtom1975 Fin15AnchoredAtom1976
    Fin15AnchoredAtom1984 Fin15AnchoredAtom1985 Fin15AnchoredAtom1986 Fin15AnchoredAtom2074
    Fin15AnchoredAtom2075 Fin15AnchoredAtom2076 Fin15AnchoredAtom2084 Fin15AnchoredAtom2085
    Fin15AnchoredAtom2086 Fin15AnchoredAtom2094 Fin15AnchoredAtom2095 Fin15AnchoredAtom2096
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2579 Fin15AnchoredAtom2580 Fin15AnchoredAtom2581
    Fin15AnchoredAtom2589 Fin15AnchoredAtom2590 Fin15AnchoredAtom2591 Fin15AnchoredAtom2599
    Fin15AnchoredAtom2600 Fin15AnchoredAtom2601 Fin15AnchoredAtom2611 Fin15AnchoredAtom2794
    Fin15AnchoredAtom2795 Fin15AnchoredAtom2796 Fin15AnchoredAtom2806 Fin15AnchoredAtom2816
    Fin15AnchoredAtom3294 Fin15AnchoredAtom3295 Fin15AnchoredAtom3296 Fin15AnchoredAtom3304
    Fin15AnchoredAtom3305 Fin15AnchoredAtom3306 Fin15AnchoredAtom3314 Fin15AnchoredAtom3315
    Fin15AnchoredAtom3316 Fin15AnchoredAtom3326 Fin15AnchoredAtom3509 Fin15AnchoredAtom3510
    Fin15AnchoredAtom3511 Fin15AnchoredAtom3521 Fin15AnchoredAtom3531 Fin15AnchoredAtom4544
    Fin15AnchoredAtom4545 Fin15AnchoredAtom4546 Fin15AnchoredAtom4556 Fin15AnchoredAtom4566
    Fin15AnchoredAtom4812 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31060 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom1976 chi ∧
      ¬Fin15AnchoredAtom1978 chi ∧
      ¬Fin15AnchoredAtom1979 chi ∧
      ¬Fin15AnchoredAtom1980 chi ∧
      ¬Fin15AnchoredAtom1984 chi ∧
      ¬Fin15AnchoredAtom1985 chi ∧
      ¬Fin15AnchoredAtom1986 chi ∧
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
      ¬Fin15AnchoredAtom2593 chi ∧
      ¬Fin15AnchoredAtom2594 chi ∧
      ¬Fin15AnchoredAtom2595 chi ∧
      ¬Fin15AnchoredAtom2599 chi ∧
      ¬Fin15AnchoredAtom2600 chi ∧
      ¬Fin15AnchoredAtom2601 chi ∧
      ¬Fin15AnchoredAtom2605 chi ∧
      ¬Fin15AnchoredAtom2606 chi ∧
      ¬Fin15AnchoredAtom2607 chi ∧
      ¬Fin15AnchoredAtom2611 chi ∧
      ¬Fin15AnchoredAtom2810 chi ∧
      ¬Fin15AnchoredAtom2811 chi ∧
      ¬Fin15AnchoredAtom2812 chi ∧
      ¬Fin15AnchoredAtom2816 chi ∧
      ¬Fin15AnchoredAtom2820 chi ∧
      ¬Fin15AnchoredAtom3308 chi ∧
      ¬Fin15AnchoredAtom3309 chi ∧
      ¬Fin15AnchoredAtom3310 chi ∧
      ¬Fin15AnchoredAtom3314 chi ∧
      ¬Fin15AnchoredAtom3315 chi ∧
      ¬Fin15AnchoredAtom3316 chi ∧
      ¬Fin15AnchoredAtom3320 chi ∧
      ¬Fin15AnchoredAtom3321 chi ∧
      ¬Fin15AnchoredAtom3322 chi ∧
      ¬Fin15AnchoredAtom3326 chi ∧
      ¬Fin15AnchoredAtom3525 chi ∧
      ¬Fin15AnchoredAtom3526 chi ∧
      ¬Fin15AnchoredAtom3527 chi ∧
      ¬Fin15AnchoredAtom3531 chi ∧
      ¬Fin15AnchoredAtom3535 chi ∧
      ¬Fin15AnchoredAtom4560 chi ∧
      ¬Fin15AnchoredAtom4561 chi ∧
      ¬Fin15AnchoredAtom4562 chi ∧
      ¬Fin15AnchoredAtom4566 chi ∧
      ¬Fin15AnchoredAtom4570 chi ∧
      ¬Fin15AnchoredAtom4821 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 4, 9, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask30227
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1972 Fin15AnchoredAtom1974 Fin15AnchoredAtom1975
    Fin15AnchoredAtom1976 Fin15AnchoredAtom1978 Fin15AnchoredAtom1979 Fin15AnchoredAtom1980
    Fin15AnchoredAtom1984 Fin15AnchoredAtom1985 Fin15AnchoredAtom1986 Fin15AnchoredAtom2088
    Fin15AnchoredAtom2089 Fin15AnchoredAtom2090 Fin15AnchoredAtom2094 Fin15AnchoredAtom2095
    Fin15AnchoredAtom2096 Fin15AnchoredAtom2100 Fin15AnchoredAtom2101 Fin15AnchoredAtom2102
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2593 Fin15AnchoredAtom2594 Fin15AnchoredAtom2595
    Fin15AnchoredAtom2599 Fin15AnchoredAtom2600 Fin15AnchoredAtom2601 Fin15AnchoredAtom2605
    Fin15AnchoredAtom2606 Fin15AnchoredAtom2607 Fin15AnchoredAtom2611 Fin15AnchoredAtom2810
    Fin15AnchoredAtom2811 Fin15AnchoredAtom2812 Fin15AnchoredAtom2816 Fin15AnchoredAtom2820
    Fin15AnchoredAtom3308 Fin15AnchoredAtom3309 Fin15AnchoredAtom3310 Fin15AnchoredAtom3314
    Fin15AnchoredAtom3315 Fin15AnchoredAtom3316 Fin15AnchoredAtom3320 Fin15AnchoredAtom3321
    Fin15AnchoredAtom3322 Fin15AnchoredAtom3326 Fin15AnchoredAtom3525 Fin15AnchoredAtom3526
    Fin15AnchoredAtom3527 Fin15AnchoredAtom3531 Fin15AnchoredAtom3535 Fin15AnchoredAtom4560
    Fin15AnchoredAtom4561 Fin15AnchoredAtom4562 Fin15AnchoredAtom4566 Fin15AnchoredAtom4570
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

theorem fin15Anchored_clause31061 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1987 chi ∧
      ¬Fin15AnchoredAtom1988 chi ∧
      ¬Fin15AnchoredAtom1989 chi ∧
      ¬Fin15AnchoredAtom1990 chi ∧
      ¬Fin15AnchoredAtom1995 chi ∧
      ¬Fin15AnchoredAtom1996 chi ∧
      ¬Fin15AnchoredAtom1997 chi ∧
      ¬Fin15AnchoredAtom2002 chi ∧
      ¬Fin15AnchoredAtom2003 chi ∧
      ¬Fin15AnchoredAtom2008 chi ∧
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
      ¬Fin15AnchoredAtom2612 chi ∧
      ¬Fin15AnchoredAtom2613 chi ∧
      ¬Fin15AnchoredAtom2614 chi ∧
      ¬Fin15AnchoredAtom2619 chi ∧
      ¬Fin15AnchoredAtom2620 chi ∧
      ¬Fin15AnchoredAtom2625 chi ∧
      ¬Fin15AnchoredAtom2640 chi ∧
      ¬Fin15AnchoredAtom2641 chi ∧
      ¬Fin15AnchoredAtom2646 chi ∧
      ¬Fin15AnchoredAtom2661 chi ∧
      ¬Fin15AnchoredAtom2696 chi ∧
      ¬Fin15AnchoredAtom2697 chi ∧
      ¬Fin15AnchoredAtom2702 chi ∧
      ¬Fin15AnchoredAtom2717 chi ∧
      ¬Fin15AnchoredAtom2752 chi ∧
      ¬Fin15AnchoredAtom3327 chi ∧
      ¬Fin15AnchoredAtom3328 chi ∧
      ¬Fin15AnchoredAtom3329 chi ∧
      ¬Fin15AnchoredAtom3334 chi ∧
      ¬Fin15AnchoredAtom3335 chi ∧
      ¬Fin15AnchoredAtom3340 chi ∧
      ¬Fin15AnchoredAtom3355 chi ∧
      ¬Fin15AnchoredAtom3356 chi ∧
      ¬Fin15AnchoredAtom3361 chi ∧
      ¬Fin15AnchoredAtom3376 chi ∧
      ¬Fin15AnchoredAtom3411 chi ∧
      ¬Fin15AnchoredAtom3412 chi ∧
      ¬Fin15AnchoredAtom3417 chi ∧
      ¬Fin15AnchoredAtom3432 chi ∧
      ¬Fin15AnchoredAtom3467 chi ∧
      ¬Fin15AnchoredAtom4572 chi ∧
      ¬Fin15AnchoredAtom4573 chi ∧
      ¬Fin15AnchoredAtom4578 chi ∧
      ¬Fin15AnchoredAtom4593 chi ∧
      ¬Fin15AnchoredAtom4628 chi ∧
      ¬Fin15AnchoredAtom4698 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 5, 6, 7, 8, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask02019
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1987 Fin15AnchoredAtom1988 Fin15AnchoredAtom1989
    Fin15AnchoredAtom1990 Fin15AnchoredAtom1995 Fin15AnchoredAtom1996 Fin15AnchoredAtom1997
    Fin15AnchoredAtom2002 Fin15AnchoredAtom2003 Fin15AnchoredAtom2008 Fin15AnchoredAtom2023
    Fin15AnchoredAtom2024 Fin15AnchoredAtom2025 Fin15AnchoredAtom2030 Fin15AnchoredAtom2031
    Fin15AnchoredAtom2036 Fin15AnchoredAtom2051 Fin15AnchoredAtom2052 Fin15AnchoredAtom2057
    Fin15AnchoredAtom2072 Fin15AnchoredAtom2612 Fin15AnchoredAtom2613 Fin15AnchoredAtom2614
    Fin15AnchoredAtom2619 Fin15AnchoredAtom2620 Fin15AnchoredAtom2625 Fin15AnchoredAtom2640
    Fin15AnchoredAtom2641 Fin15AnchoredAtom2646 Fin15AnchoredAtom2661 Fin15AnchoredAtom2696
    Fin15AnchoredAtom2697 Fin15AnchoredAtom2702 Fin15AnchoredAtom2717 Fin15AnchoredAtom2752
    Fin15AnchoredAtom3327 Fin15AnchoredAtom3328 Fin15AnchoredAtom3329 Fin15AnchoredAtom3334
    Fin15AnchoredAtom3335 Fin15AnchoredAtom3340 Fin15AnchoredAtom3355 Fin15AnchoredAtom3356
    Fin15AnchoredAtom3361 Fin15AnchoredAtom3376 Fin15AnchoredAtom3411 Fin15AnchoredAtom3412
    Fin15AnchoredAtom3417 Fin15AnchoredAtom3432 Fin15AnchoredAtom3467 Fin15AnchoredAtom4572
    Fin15AnchoredAtom4573 Fin15AnchoredAtom4578 Fin15AnchoredAtom4593 Fin15AnchoredAtom4628
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

theorem fin15Anchored_clause31062 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1987 chi ∧
      ¬Fin15AnchoredAtom1988 chi ∧
      ¬Fin15AnchoredAtom1989 chi ∧
      ¬Fin15AnchoredAtom1992 chi ∧
      ¬Fin15AnchoredAtom1995 chi ∧
      ¬Fin15AnchoredAtom1996 chi ∧
      ¬Fin15AnchoredAtom1999 chi ∧
      ¬Fin15AnchoredAtom2002 chi ∧
      ¬Fin15AnchoredAtom2005 chi ∧
      ¬Fin15AnchoredAtom2010 chi ∧
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
      ¬Fin15AnchoredAtom2612 chi ∧
      ¬Fin15AnchoredAtom2613 chi ∧
      ¬Fin15AnchoredAtom2616 chi ∧
      ¬Fin15AnchoredAtom2619 chi ∧
      ¬Fin15AnchoredAtom2622 chi ∧
      ¬Fin15AnchoredAtom2627 chi ∧
      ¬Fin15AnchoredAtom2640 chi ∧
      ¬Fin15AnchoredAtom2643 chi ∧
      ¬Fin15AnchoredAtom2648 chi ∧
      ¬Fin15AnchoredAtom2663 chi ∧
      ¬Fin15AnchoredAtom2696 chi ∧
      ¬Fin15AnchoredAtom2699 chi ∧
      ¬Fin15AnchoredAtom2704 chi ∧
      ¬Fin15AnchoredAtom2719 chi ∧
      ¬Fin15AnchoredAtom2754 chi ∧
      ¬Fin15AnchoredAtom3327 chi ∧
      ¬Fin15AnchoredAtom3328 chi ∧
      ¬Fin15AnchoredAtom3331 chi ∧
      ¬Fin15AnchoredAtom3334 chi ∧
      ¬Fin15AnchoredAtom3337 chi ∧
      ¬Fin15AnchoredAtom3342 chi ∧
      ¬Fin15AnchoredAtom3355 chi ∧
      ¬Fin15AnchoredAtom3358 chi ∧
      ¬Fin15AnchoredAtom3363 chi ∧
      ¬Fin15AnchoredAtom3378 chi ∧
      ¬Fin15AnchoredAtom3411 chi ∧
      ¬Fin15AnchoredAtom3414 chi ∧
      ¬Fin15AnchoredAtom3419 chi ∧
      ¬Fin15AnchoredAtom3434 chi ∧
      ¬Fin15AnchoredAtom3469 chi ∧
      ¬Fin15AnchoredAtom4572 chi ∧
      ¬Fin15AnchoredAtom4575 chi ∧
      ¬Fin15AnchoredAtom4580 chi ∧
      ¬Fin15AnchoredAtom4595 chi ∧
      ¬Fin15AnchoredAtom4630 chi ∧
      ¬Fin15AnchoredAtom4700 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 5, 6, 7, 8, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05091
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1987 Fin15AnchoredAtom1988 Fin15AnchoredAtom1989
    Fin15AnchoredAtom1992 Fin15AnchoredAtom1995 Fin15AnchoredAtom1996 Fin15AnchoredAtom1999
    Fin15AnchoredAtom2002 Fin15AnchoredAtom2005 Fin15AnchoredAtom2010 Fin15AnchoredAtom2023
    Fin15AnchoredAtom2024 Fin15AnchoredAtom2027 Fin15AnchoredAtom2030 Fin15AnchoredAtom2033
    Fin15AnchoredAtom2038 Fin15AnchoredAtom2051 Fin15AnchoredAtom2054 Fin15AnchoredAtom2059
    Fin15AnchoredAtom2074 Fin15AnchoredAtom2612 Fin15AnchoredAtom2613 Fin15AnchoredAtom2616
    Fin15AnchoredAtom2619 Fin15AnchoredAtom2622 Fin15AnchoredAtom2627 Fin15AnchoredAtom2640
    Fin15AnchoredAtom2643 Fin15AnchoredAtom2648 Fin15AnchoredAtom2663 Fin15AnchoredAtom2696
    Fin15AnchoredAtom2699 Fin15AnchoredAtom2704 Fin15AnchoredAtom2719 Fin15AnchoredAtom2754
    Fin15AnchoredAtom3327 Fin15AnchoredAtom3328 Fin15AnchoredAtom3331 Fin15AnchoredAtom3334
    Fin15AnchoredAtom3337 Fin15AnchoredAtom3342 Fin15AnchoredAtom3355 Fin15AnchoredAtom3358
    Fin15AnchoredAtom3363 Fin15AnchoredAtom3378 Fin15AnchoredAtom3411 Fin15AnchoredAtom3414
    Fin15AnchoredAtom3419 Fin15AnchoredAtom3434 Fin15AnchoredAtom3469 Fin15AnchoredAtom4572
    Fin15AnchoredAtom4575 Fin15AnchoredAtom4580 Fin15AnchoredAtom4595 Fin15AnchoredAtom4630
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

theorem fin15Anchored_clause31063 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1987 chi ∧
      ¬Fin15AnchoredAtom1988 chi ∧
      ¬Fin15AnchoredAtom1989 chi ∧
      ¬Fin15AnchoredAtom1993 chi ∧
      ¬Fin15AnchoredAtom1995 chi ∧
      ¬Fin15AnchoredAtom1996 chi ∧
      ¬Fin15AnchoredAtom2000 chi ∧
      ¬Fin15AnchoredAtom2002 chi ∧
      ¬Fin15AnchoredAtom2006 chi ∧
      ¬Fin15AnchoredAtom2011 chi ∧
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
      ¬Fin15AnchoredAtom2612 chi ∧
      ¬Fin15AnchoredAtom2613 chi ∧
      ¬Fin15AnchoredAtom2617 chi ∧
      ¬Fin15AnchoredAtom2619 chi ∧
      ¬Fin15AnchoredAtom2623 chi ∧
      ¬Fin15AnchoredAtom2628 chi ∧
      ¬Fin15AnchoredAtom2640 chi ∧
      ¬Fin15AnchoredAtom2644 chi ∧
      ¬Fin15AnchoredAtom2649 chi ∧
      ¬Fin15AnchoredAtom2664 chi ∧
      ¬Fin15AnchoredAtom2696 chi ∧
      ¬Fin15AnchoredAtom2700 chi ∧
      ¬Fin15AnchoredAtom2705 chi ∧
      ¬Fin15AnchoredAtom2720 chi ∧
      ¬Fin15AnchoredAtom2755 chi ∧
      ¬Fin15AnchoredAtom3327 chi ∧
      ¬Fin15AnchoredAtom3328 chi ∧
      ¬Fin15AnchoredAtom3332 chi ∧
      ¬Fin15AnchoredAtom3334 chi ∧
      ¬Fin15AnchoredAtom3338 chi ∧
      ¬Fin15AnchoredAtom3343 chi ∧
      ¬Fin15AnchoredAtom3355 chi ∧
      ¬Fin15AnchoredAtom3359 chi ∧
      ¬Fin15AnchoredAtom3364 chi ∧
      ¬Fin15AnchoredAtom3379 chi ∧
      ¬Fin15AnchoredAtom3411 chi ∧
      ¬Fin15AnchoredAtom3415 chi ∧
      ¬Fin15AnchoredAtom3420 chi ∧
      ¬Fin15AnchoredAtom3435 chi ∧
      ¬Fin15AnchoredAtom3470 chi ∧
      ¬Fin15AnchoredAtom4572 chi ∧
      ¬Fin15AnchoredAtom4576 chi ∧
      ¬Fin15AnchoredAtom4581 chi ∧
      ¬Fin15AnchoredAtom4596 chi ∧
      ¬Fin15AnchoredAtom4631 chi ∧
      ¬Fin15AnchoredAtom4701 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 5, 6, 7, 8, 9, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09187
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1987 Fin15AnchoredAtom1988 Fin15AnchoredAtom1989
    Fin15AnchoredAtom1993 Fin15AnchoredAtom1995 Fin15AnchoredAtom1996 Fin15AnchoredAtom2000
    Fin15AnchoredAtom2002 Fin15AnchoredAtom2006 Fin15AnchoredAtom2011 Fin15AnchoredAtom2023
    Fin15AnchoredAtom2024 Fin15AnchoredAtom2028 Fin15AnchoredAtom2030 Fin15AnchoredAtom2034
    Fin15AnchoredAtom2039 Fin15AnchoredAtom2051 Fin15AnchoredAtom2055 Fin15AnchoredAtom2060
    Fin15AnchoredAtom2075 Fin15AnchoredAtom2612 Fin15AnchoredAtom2613 Fin15AnchoredAtom2617
    Fin15AnchoredAtom2619 Fin15AnchoredAtom2623 Fin15AnchoredAtom2628 Fin15AnchoredAtom2640
    Fin15AnchoredAtom2644 Fin15AnchoredAtom2649 Fin15AnchoredAtom2664 Fin15AnchoredAtom2696
    Fin15AnchoredAtom2700 Fin15AnchoredAtom2705 Fin15AnchoredAtom2720 Fin15AnchoredAtom2755
    Fin15AnchoredAtom3327 Fin15AnchoredAtom3328 Fin15AnchoredAtom3332 Fin15AnchoredAtom3334
    Fin15AnchoredAtom3338 Fin15AnchoredAtom3343 Fin15AnchoredAtom3355 Fin15AnchoredAtom3359
    Fin15AnchoredAtom3364 Fin15AnchoredAtom3379 Fin15AnchoredAtom3411 Fin15AnchoredAtom3415
    Fin15AnchoredAtom3420 Fin15AnchoredAtom3435 Fin15AnchoredAtom3470 Fin15AnchoredAtom4572
    Fin15AnchoredAtom4576 Fin15AnchoredAtom4581 Fin15AnchoredAtom4596 Fin15AnchoredAtom4631
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

theorem fin15Anchored_clause31064 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1987 chi ∧
      ¬Fin15AnchoredAtom1988 chi ∧
      ¬Fin15AnchoredAtom1990 chi ∧
      ¬Fin15AnchoredAtom1992 chi ∧
      ¬Fin15AnchoredAtom1995 chi ∧
      ¬Fin15AnchoredAtom1997 chi ∧
      ¬Fin15AnchoredAtom1999 chi ∧
      ¬Fin15AnchoredAtom2003 chi ∧
      ¬Fin15AnchoredAtom2005 chi ∧
      ¬Fin15AnchoredAtom2014 chi ∧
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
      ¬Fin15AnchoredAtom2612 chi ∧
      ¬Fin15AnchoredAtom2614 chi ∧
      ¬Fin15AnchoredAtom2616 chi ∧
      ¬Fin15AnchoredAtom2620 chi ∧
      ¬Fin15AnchoredAtom2622 chi ∧
      ¬Fin15AnchoredAtom2631 chi ∧
      ¬Fin15AnchoredAtom2641 chi ∧
      ¬Fin15AnchoredAtom2643 chi ∧
      ¬Fin15AnchoredAtom2652 chi ∧
      ¬Fin15AnchoredAtom2667 chi ∧
      ¬Fin15AnchoredAtom2697 chi ∧
      ¬Fin15AnchoredAtom2699 chi ∧
      ¬Fin15AnchoredAtom2708 chi ∧
      ¬Fin15AnchoredAtom2723 chi ∧
      ¬Fin15AnchoredAtom2758 chi ∧
      ¬Fin15AnchoredAtom3327 chi ∧
      ¬Fin15AnchoredAtom3329 chi ∧
      ¬Fin15AnchoredAtom3331 chi ∧
      ¬Fin15AnchoredAtom3335 chi ∧
      ¬Fin15AnchoredAtom3337 chi ∧
      ¬Fin15AnchoredAtom3346 chi ∧
      ¬Fin15AnchoredAtom3356 chi ∧
      ¬Fin15AnchoredAtom3358 chi ∧
      ¬Fin15AnchoredAtom3367 chi ∧
      ¬Fin15AnchoredAtom3382 chi ∧
      ¬Fin15AnchoredAtom3412 chi ∧
      ¬Fin15AnchoredAtom3414 chi ∧
      ¬Fin15AnchoredAtom3423 chi ∧
      ¬Fin15AnchoredAtom3438 chi ∧
      ¬Fin15AnchoredAtom3473 chi ∧
      ¬Fin15AnchoredAtom4573 chi ∧
      ¬Fin15AnchoredAtom4575 chi ∧
      ¬Fin15AnchoredAtom4584 chi ∧
      ¬Fin15AnchoredAtom4599 chi ∧
      ¬Fin15AnchoredAtom4634 chi ∧
      ¬Fin15AnchoredAtom4704 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 5, 6, 7, 8, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05603
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1987 Fin15AnchoredAtom1988 Fin15AnchoredAtom1990
    Fin15AnchoredAtom1992 Fin15AnchoredAtom1995 Fin15AnchoredAtom1997 Fin15AnchoredAtom1999
    Fin15AnchoredAtom2003 Fin15AnchoredAtom2005 Fin15AnchoredAtom2014 Fin15AnchoredAtom2023
    Fin15AnchoredAtom2025 Fin15AnchoredAtom2027 Fin15AnchoredAtom2031 Fin15AnchoredAtom2033
    Fin15AnchoredAtom2042 Fin15AnchoredAtom2052 Fin15AnchoredAtom2054 Fin15AnchoredAtom2063
    Fin15AnchoredAtom2078 Fin15AnchoredAtom2612 Fin15AnchoredAtom2614 Fin15AnchoredAtom2616
    Fin15AnchoredAtom2620 Fin15AnchoredAtom2622 Fin15AnchoredAtom2631 Fin15AnchoredAtom2641
    Fin15AnchoredAtom2643 Fin15AnchoredAtom2652 Fin15AnchoredAtom2667 Fin15AnchoredAtom2697
    Fin15AnchoredAtom2699 Fin15AnchoredAtom2708 Fin15AnchoredAtom2723 Fin15AnchoredAtom2758
    Fin15AnchoredAtom3327 Fin15AnchoredAtom3329 Fin15AnchoredAtom3331 Fin15AnchoredAtom3335
    Fin15AnchoredAtom3337 Fin15AnchoredAtom3346 Fin15AnchoredAtom3356 Fin15AnchoredAtom3358
    Fin15AnchoredAtom3367 Fin15AnchoredAtom3382 Fin15AnchoredAtom3412 Fin15AnchoredAtom3414
    Fin15AnchoredAtom3423 Fin15AnchoredAtom3438 Fin15AnchoredAtom3473 Fin15AnchoredAtom4573
    Fin15AnchoredAtom4575 Fin15AnchoredAtom4584 Fin15AnchoredAtom4599 Fin15AnchoredAtom4634
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

theorem fin15Anchored_clause31065 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1987 chi ∧
      ¬Fin15AnchoredAtom1988 chi ∧
      ¬Fin15AnchoredAtom1990 chi ∧
      ¬Fin15AnchoredAtom1993 chi ∧
      ¬Fin15AnchoredAtom1995 chi ∧
      ¬Fin15AnchoredAtom1997 chi ∧
      ¬Fin15AnchoredAtom2000 chi ∧
      ¬Fin15AnchoredAtom2003 chi ∧
      ¬Fin15AnchoredAtom2006 chi ∧
      ¬Fin15AnchoredAtom2015 chi ∧
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
      ¬Fin15AnchoredAtom2612 chi ∧
      ¬Fin15AnchoredAtom2614 chi ∧
      ¬Fin15AnchoredAtom2617 chi ∧
      ¬Fin15AnchoredAtom2620 chi ∧
      ¬Fin15AnchoredAtom2623 chi ∧
      ¬Fin15AnchoredAtom2632 chi ∧
      ¬Fin15AnchoredAtom2641 chi ∧
      ¬Fin15AnchoredAtom2644 chi ∧
      ¬Fin15AnchoredAtom2653 chi ∧
      ¬Fin15AnchoredAtom2668 chi ∧
      ¬Fin15AnchoredAtom2697 chi ∧
      ¬Fin15AnchoredAtom2700 chi ∧
      ¬Fin15AnchoredAtom2709 chi ∧
      ¬Fin15AnchoredAtom2724 chi ∧
      ¬Fin15AnchoredAtom2759 chi ∧
      ¬Fin15AnchoredAtom3327 chi ∧
      ¬Fin15AnchoredAtom3329 chi ∧
      ¬Fin15AnchoredAtom3332 chi ∧
      ¬Fin15AnchoredAtom3335 chi ∧
      ¬Fin15AnchoredAtom3338 chi ∧
      ¬Fin15AnchoredAtom3347 chi ∧
      ¬Fin15AnchoredAtom3356 chi ∧
      ¬Fin15AnchoredAtom3359 chi ∧
      ¬Fin15AnchoredAtom3368 chi ∧
      ¬Fin15AnchoredAtom3383 chi ∧
      ¬Fin15AnchoredAtom3412 chi ∧
      ¬Fin15AnchoredAtom3415 chi ∧
      ¬Fin15AnchoredAtom3424 chi ∧
      ¬Fin15AnchoredAtom3439 chi ∧
      ¬Fin15AnchoredAtom3474 chi ∧
      ¬Fin15AnchoredAtom4573 chi ∧
      ¬Fin15AnchoredAtom4576 chi ∧
      ¬Fin15AnchoredAtom4585 chi ∧
      ¬Fin15AnchoredAtom4600 chi ∧
      ¬Fin15AnchoredAtom4635 chi ∧
      ¬Fin15AnchoredAtom4705 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 5, 6, 7, 8, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09699
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1987 Fin15AnchoredAtom1988 Fin15AnchoredAtom1990
    Fin15AnchoredAtom1993 Fin15AnchoredAtom1995 Fin15AnchoredAtom1997 Fin15AnchoredAtom2000
    Fin15AnchoredAtom2003 Fin15AnchoredAtom2006 Fin15AnchoredAtom2015 Fin15AnchoredAtom2023
    Fin15AnchoredAtom2025 Fin15AnchoredAtom2028 Fin15AnchoredAtom2031 Fin15AnchoredAtom2034
    Fin15AnchoredAtom2043 Fin15AnchoredAtom2052 Fin15AnchoredAtom2055 Fin15AnchoredAtom2064
    Fin15AnchoredAtom2079 Fin15AnchoredAtom2612 Fin15AnchoredAtom2614 Fin15AnchoredAtom2617
    Fin15AnchoredAtom2620 Fin15AnchoredAtom2623 Fin15AnchoredAtom2632 Fin15AnchoredAtom2641
    Fin15AnchoredAtom2644 Fin15AnchoredAtom2653 Fin15AnchoredAtom2668 Fin15AnchoredAtom2697
    Fin15AnchoredAtom2700 Fin15AnchoredAtom2709 Fin15AnchoredAtom2724 Fin15AnchoredAtom2759
    Fin15AnchoredAtom3327 Fin15AnchoredAtom3329 Fin15AnchoredAtom3332 Fin15AnchoredAtom3335
    Fin15AnchoredAtom3338 Fin15AnchoredAtom3347 Fin15AnchoredAtom3356 Fin15AnchoredAtom3359
    Fin15AnchoredAtom3368 Fin15AnchoredAtom3383 Fin15AnchoredAtom3412 Fin15AnchoredAtom3415
    Fin15AnchoredAtom3424 Fin15AnchoredAtom3439 Fin15AnchoredAtom3474 Fin15AnchoredAtom4573
    Fin15AnchoredAtom4576 Fin15AnchoredAtom4585 Fin15AnchoredAtom4600 Fin15AnchoredAtom4635
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

theorem fin15Anchored_clause31066 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1987 chi ∧
      ¬Fin15AnchoredAtom1989 chi ∧
      ¬Fin15AnchoredAtom1990 chi ∧
      ¬Fin15AnchoredAtom1992 chi ∧
      ¬Fin15AnchoredAtom1996 chi ∧
      ¬Fin15AnchoredAtom1997 chi ∧
      ¬Fin15AnchoredAtom1999 chi ∧
      ¬Fin15AnchoredAtom2008 chi ∧
      ¬Fin15AnchoredAtom2010 chi ∧
      ¬Fin15AnchoredAtom2014 chi ∧
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
      ¬Fin15AnchoredAtom2613 chi ∧
      ¬Fin15AnchoredAtom2614 chi ∧
      ¬Fin15AnchoredAtom2616 chi ∧
      ¬Fin15AnchoredAtom2625 chi ∧
      ¬Fin15AnchoredAtom2627 chi ∧
      ¬Fin15AnchoredAtom2631 chi ∧
      ¬Fin15AnchoredAtom2646 chi ∧
      ¬Fin15AnchoredAtom2648 chi ∧
      ¬Fin15AnchoredAtom2652 chi ∧
      ¬Fin15AnchoredAtom2677 chi ∧
      ¬Fin15AnchoredAtom2702 chi ∧
      ¬Fin15AnchoredAtom2704 chi ∧
      ¬Fin15AnchoredAtom2708 chi ∧
      ¬Fin15AnchoredAtom2733 chi ∧
      ¬Fin15AnchoredAtom2768 chi ∧
      ¬Fin15AnchoredAtom3328 chi ∧
      ¬Fin15AnchoredAtom3329 chi ∧
      ¬Fin15AnchoredAtom3331 chi ∧
      ¬Fin15AnchoredAtom3340 chi ∧
      ¬Fin15AnchoredAtom3342 chi ∧
      ¬Fin15AnchoredAtom3346 chi ∧
      ¬Fin15AnchoredAtom3361 chi ∧
      ¬Fin15AnchoredAtom3363 chi ∧
      ¬Fin15AnchoredAtom3367 chi ∧
      ¬Fin15AnchoredAtom3392 chi ∧
      ¬Fin15AnchoredAtom3417 chi ∧
      ¬Fin15AnchoredAtom3419 chi ∧
      ¬Fin15AnchoredAtom3423 chi ∧
      ¬Fin15AnchoredAtom3448 chi ∧
      ¬Fin15AnchoredAtom3483 chi ∧
      ¬Fin15AnchoredAtom4578 chi ∧
      ¬Fin15AnchoredAtom4580 chi ∧
      ¬Fin15AnchoredAtom4584 chi ∧
      ¬Fin15AnchoredAtom4609 chi ∧
      ¬Fin15AnchoredAtom4644 chi ∧
      ¬Fin15AnchoredAtom4714 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 5, 6, 7, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05859
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1987 Fin15AnchoredAtom1989 Fin15AnchoredAtom1990
    Fin15AnchoredAtom1992 Fin15AnchoredAtom1996 Fin15AnchoredAtom1997 Fin15AnchoredAtom1999
    Fin15AnchoredAtom2008 Fin15AnchoredAtom2010 Fin15AnchoredAtom2014 Fin15AnchoredAtom2024
    Fin15AnchoredAtom2025 Fin15AnchoredAtom2027 Fin15AnchoredAtom2036 Fin15AnchoredAtom2038
    Fin15AnchoredAtom2042 Fin15AnchoredAtom2057 Fin15AnchoredAtom2059 Fin15AnchoredAtom2063
    Fin15AnchoredAtom2088 Fin15AnchoredAtom2613 Fin15AnchoredAtom2614 Fin15AnchoredAtom2616
    Fin15AnchoredAtom2625 Fin15AnchoredAtom2627 Fin15AnchoredAtom2631 Fin15AnchoredAtom2646
    Fin15AnchoredAtom2648 Fin15AnchoredAtom2652 Fin15AnchoredAtom2677 Fin15AnchoredAtom2702
    Fin15AnchoredAtom2704 Fin15AnchoredAtom2708 Fin15AnchoredAtom2733 Fin15AnchoredAtom2768
    Fin15AnchoredAtom3328 Fin15AnchoredAtom3329 Fin15AnchoredAtom3331 Fin15AnchoredAtom3340
    Fin15AnchoredAtom3342 Fin15AnchoredAtom3346 Fin15AnchoredAtom3361 Fin15AnchoredAtom3363
    Fin15AnchoredAtom3367 Fin15AnchoredAtom3392 Fin15AnchoredAtom3417 Fin15AnchoredAtom3419
    Fin15AnchoredAtom3423 Fin15AnchoredAtom3448 Fin15AnchoredAtom3483 Fin15AnchoredAtom4578
    Fin15AnchoredAtom4580 Fin15AnchoredAtom4584 Fin15AnchoredAtom4609 Fin15AnchoredAtom4644
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

theorem fin15Anchored_clause31067 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1987 chi ∧
      ¬Fin15AnchoredAtom1989 chi ∧
      ¬Fin15AnchoredAtom1990 chi ∧
      ¬Fin15AnchoredAtom1993 chi ∧
      ¬Fin15AnchoredAtom1996 chi ∧
      ¬Fin15AnchoredAtom1997 chi ∧
      ¬Fin15AnchoredAtom2000 chi ∧
      ¬Fin15AnchoredAtom2008 chi ∧
      ¬Fin15AnchoredAtom2011 chi ∧
      ¬Fin15AnchoredAtom2015 chi ∧
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
      ¬Fin15AnchoredAtom2613 chi ∧
      ¬Fin15AnchoredAtom2614 chi ∧
      ¬Fin15AnchoredAtom2617 chi ∧
      ¬Fin15AnchoredAtom2625 chi ∧
      ¬Fin15AnchoredAtom2628 chi ∧
      ¬Fin15AnchoredAtom2632 chi ∧
      ¬Fin15AnchoredAtom2646 chi ∧
      ¬Fin15AnchoredAtom2649 chi ∧
      ¬Fin15AnchoredAtom2653 chi ∧
      ¬Fin15AnchoredAtom2678 chi ∧
      ¬Fin15AnchoredAtom2702 chi ∧
      ¬Fin15AnchoredAtom2705 chi ∧
      ¬Fin15AnchoredAtom2709 chi ∧
      ¬Fin15AnchoredAtom2734 chi ∧
      ¬Fin15AnchoredAtom2769 chi ∧
      ¬Fin15AnchoredAtom3328 chi ∧
      ¬Fin15AnchoredAtom3329 chi ∧
      ¬Fin15AnchoredAtom3332 chi ∧
      ¬Fin15AnchoredAtom3340 chi ∧
      ¬Fin15AnchoredAtom3343 chi ∧
      ¬Fin15AnchoredAtom3347 chi ∧
      ¬Fin15AnchoredAtom3361 chi ∧
      ¬Fin15AnchoredAtom3364 chi ∧
      ¬Fin15AnchoredAtom3368 chi ∧
      ¬Fin15AnchoredAtom3393 chi ∧
      ¬Fin15AnchoredAtom3417 chi ∧
      ¬Fin15AnchoredAtom3420 chi ∧
      ¬Fin15AnchoredAtom3424 chi ∧
      ¬Fin15AnchoredAtom3449 chi ∧
      ¬Fin15AnchoredAtom3484 chi ∧
      ¬Fin15AnchoredAtom4578 chi ∧
      ¬Fin15AnchoredAtom4581 chi ∧
      ¬Fin15AnchoredAtom4585 chi ∧
      ¬Fin15AnchoredAtom4610 chi ∧
      ¬Fin15AnchoredAtom4645 chi ∧
      ¬Fin15AnchoredAtom4715 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 5, 6, 7, 9, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09955
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1987 Fin15AnchoredAtom1989 Fin15AnchoredAtom1990
    Fin15AnchoredAtom1993 Fin15AnchoredAtom1996 Fin15AnchoredAtom1997 Fin15AnchoredAtom2000
    Fin15AnchoredAtom2008 Fin15AnchoredAtom2011 Fin15AnchoredAtom2015 Fin15AnchoredAtom2024
    Fin15AnchoredAtom2025 Fin15AnchoredAtom2028 Fin15AnchoredAtom2036 Fin15AnchoredAtom2039
    Fin15AnchoredAtom2043 Fin15AnchoredAtom2057 Fin15AnchoredAtom2060 Fin15AnchoredAtom2064
    Fin15AnchoredAtom2089 Fin15AnchoredAtom2613 Fin15AnchoredAtom2614 Fin15AnchoredAtom2617
    Fin15AnchoredAtom2625 Fin15AnchoredAtom2628 Fin15AnchoredAtom2632 Fin15AnchoredAtom2646
    Fin15AnchoredAtom2649 Fin15AnchoredAtom2653 Fin15AnchoredAtom2678 Fin15AnchoredAtom2702
    Fin15AnchoredAtom2705 Fin15AnchoredAtom2709 Fin15AnchoredAtom2734 Fin15AnchoredAtom2769
    Fin15AnchoredAtom3328 Fin15AnchoredAtom3329 Fin15AnchoredAtom3332 Fin15AnchoredAtom3340
    Fin15AnchoredAtom3343 Fin15AnchoredAtom3347 Fin15AnchoredAtom3361 Fin15AnchoredAtom3364
    Fin15AnchoredAtom3368 Fin15AnchoredAtom3393 Fin15AnchoredAtom3417 Fin15AnchoredAtom3420
    Fin15AnchoredAtom3424 Fin15AnchoredAtom3449 Fin15AnchoredAtom3484 Fin15AnchoredAtom4578
    Fin15AnchoredAtom4581 Fin15AnchoredAtom4585 Fin15AnchoredAtom4610 Fin15AnchoredAtom4645
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

theorem fin15Anchored_clause31068 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1987 chi ∧
      ¬Fin15AnchoredAtom1989 chi ∧
      ¬Fin15AnchoredAtom1990 chi ∧
      ¬Fin15AnchoredAtom1994 chi ∧
      ¬Fin15AnchoredAtom1996 chi ∧
      ¬Fin15AnchoredAtom1997 chi ∧
      ¬Fin15AnchoredAtom2001 chi ∧
      ¬Fin15AnchoredAtom2008 chi ∧
      ¬Fin15AnchoredAtom2012 chi ∧
      ¬Fin15AnchoredAtom2016 chi ∧
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
      ¬Fin15AnchoredAtom2613 chi ∧
      ¬Fin15AnchoredAtom2614 chi ∧
      ¬Fin15AnchoredAtom2618 chi ∧
      ¬Fin15AnchoredAtom2625 chi ∧
      ¬Fin15AnchoredAtom2629 chi ∧
      ¬Fin15AnchoredAtom2633 chi ∧
      ¬Fin15AnchoredAtom2646 chi ∧
      ¬Fin15AnchoredAtom2650 chi ∧
      ¬Fin15AnchoredAtom2654 chi ∧
      ¬Fin15AnchoredAtom2679 chi ∧
      ¬Fin15AnchoredAtom2702 chi ∧
      ¬Fin15AnchoredAtom2706 chi ∧
      ¬Fin15AnchoredAtom2710 chi ∧
      ¬Fin15AnchoredAtom2735 chi ∧
      ¬Fin15AnchoredAtom2770 chi ∧
      ¬Fin15AnchoredAtom3328 chi ∧
      ¬Fin15AnchoredAtom3329 chi ∧
      ¬Fin15AnchoredAtom3333 chi ∧
      ¬Fin15AnchoredAtom3340 chi ∧
      ¬Fin15AnchoredAtom3344 chi ∧
      ¬Fin15AnchoredAtom3348 chi ∧
      ¬Fin15AnchoredAtom3361 chi ∧
      ¬Fin15AnchoredAtom3365 chi ∧
      ¬Fin15AnchoredAtom3369 chi ∧
      ¬Fin15AnchoredAtom3394 chi ∧
      ¬Fin15AnchoredAtom3417 chi ∧
      ¬Fin15AnchoredAtom3421 chi ∧
      ¬Fin15AnchoredAtom3425 chi ∧
      ¬Fin15AnchoredAtom3450 chi ∧
      ¬Fin15AnchoredAtom3485 chi ∧
      ¬Fin15AnchoredAtom4578 chi ∧
      ¬Fin15AnchoredAtom4582 chi ∧
      ¬Fin15AnchoredAtom4586 chi ∧
      ¬Fin15AnchoredAtom4611 chi ∧
      ¬Fin15AnchoredAtom4646 chi ∧
      ¬Fin15AnchoredAtom4716 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 5, 6, 7, 9, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask18147
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1987 Fin15AnchoredAtom1989 Fin15AnchoredAtom1990
    Fin15AnchoredAtom1994 Fin15AnchoredAtom1996 Fin15AnchoredAtom1997 Fin15AnchoredAtom2001
    Fin15AnchoredAtom2008 Fin15AnchoredAtom2012 Fin15AnchoredAtom2016 Fin15AnchoredAtom2024
    Fin15AnchoredAtom2025 Fin15AnchoredAtom2029 Fin15AnchoredAtom2036 Fin15AnchoredAtom2040
    Fin15AnchoredAtom2044 Fin15AnchoredAtom2057 Fin15AnchoredAtom2061 Fin15AnchoredAtom2065
    Fin15AnchoredAtom2090 Fin15AnchoredAtom2613 Fin15AnchoredAtom2614 Fin15AnchoredAtom2618
    Fin15AnchoredAtom2625 Fin15AnchoredAtom2629 Fin15AnchoredAtom2633 Fin15AnchoredAtom2646
    Fin15AnchoredAtom2650 Fin15AnchoredAtom2654 Fin15AnchoredAtom2679 Fin15AnchoredAtom2702
    Fin15AnchoredAtom2706 Fin15AnchoredAtom2710 Fin15AnchoredAtom2735 Fin15AnchoredAtom2770
    Fin15AnchoredAtom3328 Fin15AnchoredAtom3329 Fin15AnchoredAtom3333 Fin15AnchoredAtom3340
    Fin15AnchoredAtom3344 Fin15AnchoredAtom3348 Fin15AnchoredAtom3361 Fin15AnchoredAtom3365
    Fin15AnchoredAtom3369 Fin15AnchoredAtom3394 Fin15AnchoredAtom3417 Fin15AnchoredAtom3421
    Fin15AnchoredAtom3425 Fin15AnchoredAtom3450 Fin15AnchoredAtom3485 Fin15AnchoredAtom4578
    Fin15AnchoredAtom4582 Fin15AnchoredAtom4586 Fin15AnchoredAtom4611 Fin15AnchoredAtom4646
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

theorem fin15Anchored_clause31069 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1987 chi ∧
      ¬Fin15AnchoredAtom1989 chi ∧
      ¬Fin15AnchoredAtom1992 chi ∧
      ¬Fin15AnchoredAtom1993 chi ∧
      ¬Fin15AnchoredAtom1996 chi ∧
      ¬Fin15AnchoredAtom1999 chi ∧
      ¬Fin15AnchoredAtom2000 chi ∧
      ¬Fin15AnchoredAtom2010 chi ∧
      ¬Fin15AnchoredAtom2011 chi ∧
      ¬Fin15AnchoredAtom2020 chi ∧
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
      ¬Fin15AnchoredAtom2613 chi ∧
      ¬Fin15AnchoredAtom2616 chi ∧
      ¬Fin15AnchoredAtom2617 chi ∧
      ¬Fin15AnchoredAtom2627 chi ∧
      ¬Fin15AnchoredAtom2628 chi ∧
      ¬Fin15AnchoredAtom2637 chi ∧
      ¬Fin15AnchoredAtom2648 chi ∧
      ¬Fin15AnchoredAtom2649 chi ∧
      ¬Fin15AnchoredAtom2658 chi ∧
      ¬Fin15AnchoredAtom2683 chi ∧
      ¬Fin15AnchoredAtom2704 chi ∧
      ¬Fin15AnchoredAtom2705 chi ∧
      ¬Fin15AnchoredAtom2714 chi ∧
      ¬Fin15AnchoredAtom2739 chi ∧
      ¬Fin15AnchoredAtom2774 chi ∧
      ¬Fin15AnchoredAtom3328 chi ∧
      ¬Fin15AnchoredAtom3331 chi ∧
      ¬Fin15AnchoredAtom3332 chi ∧
      ¬Fin15AnchoredAtom3342 chi ∧
      ¬Fin15AnchoredAtom3343 chi ∧
      ¬Fin15AnchoredAtom3352 chi ∧
      ¬Fin15AnchoredAtom3363 chi ∧
      ¬Fin15AnchoredAtom3364 chi ∧
      ¬Fin15AnchoredAtom3373 chi ∧
      ¬Fin15AnchoredAtom3398 chi ∧
      ¬Fin15AnchoredAtom3419 chi ∧
      ¬Fin15AnchoredAtom3420 chi ∧
      ¬Fin15AnchoredAtom3429 chi ∧
      ¬Fin15AnchoredAtom3454 chi ∧
      ¬Fin15AnchoredAtom3489 chi ∧
      ¬Fin15AnchoredAtom4580 chi ∧
      ¬Fin15AnchoredAtom4581 chi ∧
      ¬Fin15AnchoredAtom4590 chi ∧
      ¬Fin15AnchoredAtom4615 chi ∧
      ¬Fin15AnchoredAtom4650 chi ∧
      ¬Fin15AnchoredAtom4720 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 5, 6, 7, 9, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13027
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1987 Fin15AnchoredAtom1989 Fin15AnchoredAtom1992
    Fin15AnchoredAtom1993 Fin15AnchoredAtom1996 Fin15AnchoredAtom1999 Fin15AnchoredAtom2000
    Fin15AnchoredAtom2010 Fin15AnchoredAtom2011 Fin15AnchoredAtom2020 Fin15AnchoredAtom2024
    Fin15AnchoredAtom2027 Fin15AnchoredAtom2028 Fin15AnchoredAtom2038 Fin15AnchoredAtom2039
    Fin15AnchoredAtom2048 Fin15AnchoredAtom2059 Fin15AnchoredAtom2060 Fin15AnchoredAtom2069
    Fin15AnchoredAtom2094 Fin15AnchoredAtom2613 Fin15AnchoredAtom2616 Fin15AnchoredAtom2617
    Fin15AnchoredAtom2627 Fin15AnchoredAtom2628 Fin15AnchoredAtom2637 Fin15AnchoredAtom2648
    Fin15AnchoredAtom2649 Fin15AnchoredAtom2658 Fin15AnchoredAtom2683 Fin15AnchoredAtom2704
    Fin15AnchoredAtom2705 Fin15AnchoredAtom2714 Fin15AnchoredAtom2739 Fin15AnchoredAtom2774
    Fin15AnchoredAtom3328 Fin15AnchoredAtom3331 Fin15AnchoredAtom3332 Fin15AnchoredAtom3342
    Fin15AnchoredAtom3343 Fin15AnchoredAtom3352 Fin15AnchoredAtom3363 Fin15AnchoredAtom3364
    Fin15AnchoredAtom3373 Fin15AnchoredAtom3398 Fin15AnchoredAtom3419 Fin15AnchoredAtom3420
    Fin15AnchoredAtom3429 Fin15AnchoredAtom3454 Fin15AnchoredAtom3489 Fin15AnchoredAtom4580
    Fin15AnchoredAtom4581 Fin15AnchoredAtom4590 Fin15AnchoredAtom4615 Fin15AnchoredAtom4650
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

theorem fin15Anchored_clause31070 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1987 chi ∧
      ¬Fin15AnchoredAtom1989 chi ∧
      ¬Fin15AnchoredAtom1992 chi ∧
      ¬Fin15AnchoredAtom1994 chi ∧
      ¬Fin15AnchoredAtom1996 chi ∧
      ¬Fin15AnchoredAtom1999 chi ∧
      ¬Fin15AnchoredAtom2001 chi ∧
      ¬Fin15AnchoredAtom2010 chi ∧
      ¬Fin15AnchoredAtom2012 chi ∧
      ¬Fin15AnchoredAtom2021 chi ∧
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
      ¬Fin15AnchoredAtom2613 chi ∧
      ¬Fin15AnchoredAtom2616 chi ∧
      ¬Fin15AnchoredAtom2618 chi ∧
      ¬Fin15AnchoredAtom2627 chi ∧
      ¬Fin15AnchoredAtom2629 chi ∧
      ¬Fin15AnchoredAtom2638 chi ∧
      ¬Fin15AnchoredAtom2648 chi ∧
      ¬Fin15AnchoredAtom2650 chi ∧
      ¬Fin15AnchoredAtom2659 chi ∧
      ¬Fin15AnchoredAtom2684 chi ∧
      ¬Fin15AnchoredAtom2704 chi ∧
      ¬Fin15AnchoredAtom2706 chi ∧
      ¬Fin15AnchoredAtom2715 chi ∧
      ¬Fin15AnchoredAtom2740 chi ∧
      ¬Fin15AnchoredAtom2775 chi ∧
      ¬Fin15AnchoredAtom3328 chi ∧
      ¬Fin15AnchoredAtom3331 chi ∧
      ¬Fin15AnchoredAtom3333 chi ∧
      ¬Fin15AnchoredAtom3342 chi ∧
      ¬Fin15AnchoredAtom3344 chi ∧
      ¬Fin15AnchoredAtom3353 chi ∧
      ¬Fin15AnchoredAtom3363 chi ∧
      ¬Fin15AnchoredAtom3365 chi ∧
      ¬Fin15AnchoredAtom3374 chi ∧
      ¬Fin15AnchoredAtom3399 chi ∧
      ¬Fin15AnchoredAtom3419 chi ∧
      ¬Fin15AnchoredAtom3421 chi ∧
      ¬Fin15AnchoredAtom3430 chi ∧
      ¬Fin15AnchoredAtom3455 chi ∧
      ¬Fin15AnchoredAtom3490 chi ∧
      ¬Fin15AnchoredAtom4580 chi ∧
      ¬Fin15AnchoredAtom4582 chi ∧
      ¬Fin15AnchoredAtom4591 chi ∧
      ¬Fin15AnchoredAtom4616 chi ∧
      ¬Fin15AnchoredAtom4651 chi ∧
      ¬Fin15AnchoredAtom4721 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 5, 6, 7, 9, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21219
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1987 Fin15AnchoredAtom1989 Fin15AnchoredAtom1992
    Fin15AnchoredAtom1994 Fin15AnchoredAtom1996 Fin15AnchoredAtom1999 Fin15AnchoredAtom2001
    Fin15AnchoredAtom2010 Fin15AnchoredAtom2012 Fin15AnchoredAtom2021 Fin15AnchoredAtom2024
    Fin15AnchoredAtom2027 Fin15AnchoredAtom2029 Fin15AnchoredAtom2038 Fin15AnchoredAtom2040
    Fin15AnchoredAtom2049 Fin15AnchoredAtom2059 Fin15AnchoredAtom2061 Fin15AnchoredAtom2070
    Fin15AnchoredAtom2095 Fin15AnchoredAtom2613 Fin15AnchoredAtom2616 Fin15AnchoredAtom2618
    Fin15AnchoredAtom2627 Fin15AnchoredAtom2629 Fin15AnchoredAtom2638 Fin15AnchoredAtom2648
    Fin15AnchoredAtom2650 Fin15AnchoredAtom2659 Fin15AnchoredAtom2684 Fin15AnchoredAtom2704
    Fin15AnchoredAtom2706 Fin15AnchoredAtom2715 Fin15AnchoredAtom2740 Fin15AnchoredAtom2775
    Fin15AnchoredAtom3328 Fin15AnchoredAtom3331 Fin15AnchoredAtom3333 Fin15AnchoredAtom3342
    Fin15AnchoredAtom3344 Fin15AnchoredAtom3353 Fin15AnchoredAtom3363 Fin15AnchoredAtom3365
    Fin15AnchoredAtom3374 Fin15AnchoredAtom3399 Fin15AnchoredAtom3419 Fin15AnchoredAtom3421
    Fin15AnchoredAtom3430 Fin15AnchoredAtom3455 Fin15AnchoredAtom3490 Fin15AnchoredAtom4580
    Fin15AnchoredAtom4582 Fin15AnchoredAtom4591 Fin15AnchoredAtom4616 Fin15AnchoredAtom4651
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

theorem fin15Anchored_clause31071 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1987 chi ∧
      ¬Fin15AnchoredAtom1989 chi ∧
      ¬Fin15AnchoredAtom1993 chi ∧
      ¬Fin15AnchoredAtom1994 chi ∧
      ¬Fin15AnchoredAtom1996 chi ∧
      ¬Fin15AnchoredAtom2000 chi ∧
      ¬Fin15AnchoredAtom2001 chi ∧
      ¬Fin15AnchoredAtom2011 chi ∧
      ¬Fin15AnchoredAtom2012 chi ∧
      ¬Fin15AnchoredAtom2022 chi ∧
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
      ¬Fin15AnchoredAtom2613 chi ∧
      ¬Fin15AnchoredAtom2617 chi ∧
      ¬Fin15AnchoredAtom2618 chi ∧
      ¬Fin15AnchoredAtom2628 chi ∧
      ¬Fin15AnchoredAtom2629 chi ∧
      ¬Fin15AnchoredAtom2639 chi ∧
      ¬Fin15AnchoredAtom2649 chi ∧
      ¬Fin15AnchoredAtom2650 chi ∧
      ¬Fin15AnchoredAtom2660 chi ∧
      ¬Fin15AnchoredAtom2685 chi ∧
      ¬Fin15AnchoredAtom2705 chi ∧
      ¬Fin15AnchoredAtom2706 chi ∧
      ¬Fin15AnchoredAtom2716 chi ∧
      ¬Fin15AnchoredAtom2741 chi ∧
      ¬Fin15AnchoredAtom2776 chi ∧
      ¬Fin15AnchoredAtom3328 chi ∧
      ¬Fin15AnchoredAtom3332 chi ∧
      ¬Fin15AnchoredAtom3333 chi ∧
      ¬Fin15AnchoredAtom3343 chi ∧
      ¬Fin15AnchoredAtom3344 chi ∧
      ¬Fin15AnchoredAtom3354 chi ∧
      ¬Fin15AnchoredAtom3364 chi ∧
      ¬Fin15AnchoredAtom3365 chi ∧
      ¬Fin15AnchoredAtom3375 chi ∧
      ¬Fin15AnchoredAtom3400 chi ∧
      ¬Fin15AnchoredAtom3420 chi ∧
      ¬Fin15AnchoredAtom3421 chi ∧
      ¬Fin15AnchoredAtom3431 chi ∧
      ¬Fin15AnchoredAtom3456 chi ∧
      ¬Fin15AnchoredAtom3491 chi ∧
      ¬Fin15AnchoredAtom4581 chi ∧
      ¬Fin15AnchoredAtom4582 chi ∧
      ¬Fin15AnchoredAtom4592 chi ∧
      ¬Fin15AnchoredAtom4617 chi ∧
      ¬Fin15AnchoredAtom4652 chi ∧
      ¬Fin15AnchoredAtom4722 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 5, 6, 7, 9, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25315
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1987 Fin15AnchoredAtom1989 Fin15AnchoredAtom1993
    Fin15AnchoredAtom1994 Fin15AnchoredAtom1996 Fin15AnchoredAtom2000 Fin15AnchoredAtom2001
    Fin15AnchoredAtom2011 Fin15AnchoredAtom2012 Fin15AnchoredAtom2022 Fin15AnchoredAtom2024
    Fin15AnchoredAtom2028 Fin15AnchoredAtom2029 Fin15AnchoredAtom2039 Fin15AnchoredAtom2040
    Fin15AnchoredAtom2050 Fin15AnchoredAtom2060 Fin15AnchoredAtom2061 Fin15AnchoredAtom2071
    Fin15AnchoredAtom2096 Fin15AnchoredAtom2613 Fin15AnchoredAtom2617 Fin15AnchoredAtom2618
    Fin15AnchoredAtom2628 Fin15AnchoredAtom2629 Fin15AnchoredAtom2639 Fin15AnchoredAtom2649
    Fin15AnchoredAtom2650 Fin15AnchoredAtom2660 Fin15AnchoredAtom2685 Fin15AnchoredAtom2705
    Fin15AnchoredAtom2706 Fin15AnchoredAtom2716 Fin15AnchoredAtom2741 Fin15AnchoredAtom2776
    Fin15AnchoredAtom3328 Fin15AnchoredAtom3332 Fin15AnchoredAtom3333 Fin15AnchoredAtom3343
    Fin15AnchoredAtom3344 Fin15AnchoredAtom3354 Fin15AnchoredAtom3364 Fin15AnchoredAtom3365
    Fin15AnchoredAtom3375 Fin15AnchoredAtom3400 Fin15AnchoredAtom3420 Fin15AnchoredAtom3421
    Fin15AnchoredAtom3431 Fin15AnchoredAtom3456 Fin15AnchoredAtom3491 Fin15AnchoredAtom4581
    Fin15AnchoredAtom4582 Fin15AnchoredAtom4592 Fin15AnchoredAtom4617 Fin15AnchoredAtom4652
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

theorem fin15Anchored_clause31072 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1987 chi ∧
      ¬Fin15AnchoredAtom1990 chi ∧
      ¬Fin15AnchoredAtom1992 chi ∧
      ¬Fin15AnchoredAtom1993 chi ∧
      ¬Fin15AnchoredAtom1997 chi ∧
      ¬Fin15AnchoredAtom1999 chi ∧
      ¬Fin15AnchoredAtom2000 chi ∧
      ¬Fin15AnchoredAtom2014 chi ∧
      ¬Fin15AnchoredAtom2015 chi ∧
      ¬Fin15AnchoredAtom2020 chi ∧
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
      ¬Fin15AnchoredAtom2614 chi ∧
      ¬Fin15AnchoredAtom2616 chi ∧
      ¬Fin15AnchoredAtom2617 chi ∧
      ¬Fin15AnchoredAtom2631 chi ∧
      ¬Fin15AnchoredAtom2632 chi ∧
      ¬Fin15AnchoredAtom2637 chi ∧
      ¬Fin15AnchoredAtom2652 chi ∧
      ¬Fin15AnchoredAtom2653 chi ∧
      ¬Fin15AnchoredAtom2658 chi ∧
      ¬Fin15AnchoredAtom2689 chi ∧
      ¬Fin15AnchoredAtom2708 chi ∧
      ¬Fin15AnchoredAtom2709 chi ∧
      ¬Fin15AnchoredAtom2714 chi ∧
      ¬Fin15AnchoredAtom2745 chi ∧
      ¬Fin15AnchoredAtom2780 chi ∧
      ¬Fin15AnchoredAtom3329 chi ∧
      ¬Fin15AnchoredAtom3331 chi ∧
      ¬Fin15AnchoredAtom3332 chi ∧
      ¬Fin15AnchoredAtom3346 chi ∧
      ¬Fin15AnchoredAtom3347 chi ∧
      ¬Fin15AnchoredAtom3352 chi ∧
      ¬Fin15AnchoredAtom3367 chi ∧
      ¬Fin15AnchoredAtom3368 chi ∧
      ¬Fin15AnchoredAtom3373 chi ∧
      ¬Fin15AnchoredAtom3404 chi ∧
      ¬Fin15AnchoredAtom3423 chi ∧
      ¬Fin15AnchoredAtom3424 chi ∧
      ¬Fin15AnchoredAtom3429 chi ∧
      ¬Fin15AnchoredAtom3460 chi ∧
      ¬Fin15AnchoredAtom3495 chi ∧
      ¬Fin15AnchoredAtom4584 chi ∧
      ¬Fin15AnchoredAtom4585 chi ∧
      ¬Fin15AnchoredAtom4590 chi ∧
      ¬Fin15AnchoredAtom4621 chi ∧
      ¬Fin15AnchoredAtom4656 chi ∧
      ¬Fin15AnchoredAtom4726 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 5, 6, 7, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13539
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1987 Fin15AnchoredAtom1990 Fin15AnchoredAtom1992
    Fin15AnchoredAtom1993 Fin15AnchoredAtom1997 Fin15AnchoredAtom1999 Fin15AnchoredAtom2000
    Fin15AnchoredAtom2014 Fin15AnchoredAtom2015 Fin15AnchoredAtom2020 Fin15AnchoredAtom2025
    Fin15AnchoredAtom2027 Fin15AnchoredAtom2028 Fin15AnchoredAtom2042 Fin15AnchoredAtom2043
    Fin15AnchoredAtom2048 Fin15AnchoredAtom2063 Fin15AnchoredAtom2064 Fin15AnchoredAtom2069
    Fin15AnchoredAtom2100 Fin15AnchoredAtom2614 Fin15AnchoredAtom2616 Fin15AnchoredAtom2617
    Fin15AnchoredAtom2631 Fin15AnchoredAtom2632 Fin15AnchoredAtom2637 Fin15AnchoredAtom2652
    Fin15AnchoredAtom2653 Fin15AnchoredAtom2658 Fin15AnchoredAtom2689 Fin15AnchoredAtom2708
    Fin15AnchoredAtom2709 Fin15AnchoredAtom2714 Fin15AnchoredAtom2745 Fin15AnchoredAtom2780
    Fin15AnchoredAtom3329 Fin15AnchoredAtom3331 Fin15AnchoredAtom3332 Fin15AnchoredAtom3346
    Fin15AnchoredAtom3347 Fin15AnchoredAtom3352 Fin15AnchoredAtom3367 Fin15AnchoredAtom3368
    Fin15AnchoredAtom3373 Fin15AnchoredAtom3404 Fin15AnchoredAtom3423 Fin15AnchoredAtom3424
    Fin15AnchoredAtom3429 Fin15AnchoredAtom3460 Fin15AnchoredAtom3495 Fin15AnchoredAtom4584
    Fin15AnchoredAtom4585 Fin15AnchoredAtom4590 Fin15AnchoredAtom4621 Fin15AnchoredAtom4656
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

theorem fin15Anchored_clause31073 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1987 chi ∧
      ¬Fin15AnchoredAtom1990 chi ∧
      ¬Fin15AnchoredAtom1992 chi ∧
      ¬Fin15AnchoredAtom1994 chi ∧
      ¬Fin15AnchoredAtom1997 chi ∧
      ¬Fin15AnchoredAtom1999 chi ∧
      ¬Fin15AnchoredAtom2001 chi ∧
      ¬Fin15AnchoredAtom2014 chi ∧
      ¬Fin15AnchoredAtom2016 chi ∧
      ¬Fin15AnchoredAtom2021 chi ∧
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
      ¬Fin15AnchoredAtom2614 chi ∧
      ¬Fin15AnchoredAtom2616 chi ∧
      ¬Fin15AnchoredAtom2618 chi ∧
      ¬Fin15AnchoredAtom2631 chi ∧
      ¬Fin15AnchoredAtom2633 chi ∧
      ¬Fin15AnchoredAtom2638 chi ∧
      ¬Fin15AnchoredAtom2652 chi ∧
      ¬Fin15AnchoredAtom2654 chi ∧
      ¬Fin15AnchoredAtom2659 chi ∧
      ¬Fin15AnchoredAtom2690 chi ∧
      ¬Fin15AnchoredAtom2708 chi ∧
      ¬Fin15AnchoredAtom2710 chi ∧
      ¬Fin15AnchoredAtom2715 chi ∧
      ¬Fin15AnchoredAtom2746 chi ∧
      ¬Fin15AnchoredAtom2781 chi ∧
      ¬Fin15AnchoredAtom3329 chi ∧
      ¬Fin15AnchoredAtom3331 chi ∧
      ¬Fin15AnchoredAtom3333 chi ∧
      ¬Fin15AnchoredAtom3346 chi ∧
      ¬Fin15AnchoredAtom3348 chi ∧
      ¬Fin15AnchoredAtom3353 chi ∧
      ¬Fin15AnchoredAtom3367 chi ∧
      ¬Fin15AnchoredAtom3369 chi ∧
      ¬Fin15AnchoredAtom3374 chi ∧
      ¬Fin15AnchoredAtom3405 chi ∧
      ¬Fin15AnchoredAtom3423 chi ∧
      ¬Fin15AnchoredAtom3425 chi ∧
      ¬Fin15AnchoredAtom3430 chi ∧
      ¬Fin15AnchoredAtom3461 chi ∧
      ¬Fin15AnchoredAtom3496 chi ∧
      ¬Fin15AnchoredAtom4584 chi ∧
      ¬Fin15AnchoredAtom4586 chi ∧
      ¬Fin15AnchoredAtom4591 chi ∧
      ¬Fin15AnchoredAtom4622 chi ∧
      ¬Fin15AnchoredAtom4657 chi ∧
      ¬Fin15AnchoredAtom4727 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 5, 6, 7, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21731
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1987 Fin15AnchoredAtom1990 Fin15AnchoredAtom1992
    Fin15AnchoredAtom1994 Fin15AnchoredAtom1997 Fin15AnchoredAtom1999 Fin15AnchoredAtom2001
    Fin15AnchoredAtom2014 Fin15AnchoredAtom2016 Fin15AnchoredAtom2021 Fin15AnchoredAtom2025
    Fin15AnchoredAtom2027 Fin15AnchoredAtom2029 Fin15AnchoredAtom2042 Fin15AnchoredAtom2044
    Fin15AnchoredAtom2049 Fin15AnchoredAtom2063 Fin15AnchoredAtom2065 Fin15AnchoredAtom2070
    Fin15AnchoredAtom2101 Fin15AnchoredAtom2614 Fin15AnchoredAtom2616 Fin15AnchoredAtom2618
    Fin15AnchoredAtom2631 Fin15AnchoredAtom2633 Fin15AnchoredAtom2638 Fin15AnchoredAtom2652
    Fin15AnchoredAtom2654 Fin15AnchoredAtom2659 Fin15AnchoredAtom2690 Fin15AnchoredAtom2708
    Fin15AnchoredAtom2710 Fin15AnchoredAtom2715 Fin15AnchoredAtom2746 Fin15AnchoredAtom2781
    Fin15AnchoredAtom3329 Fin15AnchoredAtom3331 Fin15AnchoredAtom3333 Fin15AnchoredAtom3346
    Fin15AnchoredAtom3348 Fin15AnchoredAtom3353 Fin15AnchoredAtom3367 Fin15AnchoredAtom3369
    Fin15AnchoredAtom3374 Fin15AnchoredAtom3405 Fin15AnchoredAtom3423 Fin15AnchoredAtom3425
    Fin15AnchoredAtom3430 Fin15AnchoredAtom3461 Fin15AnchoredAtom3496 Fin15AnchoredAtom4584
    Fin15AnchoredAtom4586 Fin15AnchoredAtom4591 Fin15AnchoredAtom4622 Fin15AnchoredAtom4657
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

theorem fin15Anchored_clause31074 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1987 chi ∧
      ¬Fin15AnchoredAtom1990 chi ∧
      ¬Fin15AnchoredAtom1993 chi ∧
      ¬Fin15AnchoredAtom1994 chi ∧
      ¬Fin15AnchoredAtom1997 chi ∧
      ¬Fin15AnchoredAtom2000 chi ∧
      ¬Fin15AnchoredAtom2001 chi ∧
      ¬Fin15AnchoredAtom2015 chi ∧
      ¬Fin15AnchoredAtom2016 chi ∧
      ¬Fin15AnchoredAtom2022 chi ∧
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
      ¬Fin15AnchoredAtom2614 chi ∧
      ¬Fin15AnchoredAtom2617 chi ∧
      ¬Fin15AnchoredAtom2618 chi ∧
      ¬Fin15AnchoredAtom2632 chi ∧
      ¬Fin15AnchoredAtom2633 chi ∧
      ¬Fin15AnchoredAtom2639 chi ∧
      ¬Fin15AnchoredAtom2653 chi ∧
      ¬Fin15AnchoredAtom2654 chi ∧
      ¬Fin15AnchoredAtom2660 chi ∧
      ¬Fin15AnchoredAtom2691 chi ∧
      ¬Fin15AnchoredAtom2709 chi ∧
      ¬Fin15AnchoredAtom2710 chi ∧
      ¬Fin15AnchoredAtom2716 chi ∧
      ¬Fin15AnchoredAtom2747 chi ∧
      ¬Fin15AnchoredAtom2782 chi ∧
      ¬Fin15AnchoredAtom3329 chi ∧
      ¬Fin15AnchoredAtom3332 chi ∧
      ¬Fin15AnchoredAtom3333 chi ∧
      ¬Fin15AnchoredAtom3347 chi ∧
      ¬Fin15AnchoredAtom3348 chi ∧
      ¬Fin15AnchoredAtom3354 chi ∧
      ¬Fin15AnchoredAtom3368 chi ∧
      ¬Fin15AnchoredAtom3369 chi ∧
      ¬Fin15AnchoredAtom3375 chi ∧
      ¬Fin15AnchoredAtom3406 chi ∧
      ¬Fin15AnchoredAtom3424 chi ∧
      ¬Fin15AnchoredAtom3425 chi ∧
      ¬Fin15AnchoredAtom3431 chi ∧
      ¬Fin15AnchoredAtom3462 chi ∧
      ¬Fin15AnchoredAtom3497 chi ∧
      ¬Fin15AnchoredAtom4585 chi ∧
      ¬Fin15AnchoredAtom4586 chi ∧
      ¬Fin15AnchoredAtom4592 chi ∧
      ¬Fin15AnchoredAtom4623 chi ∧
      ¬Fin15AnchoredAtom4658 chi ∧
      ¬Fin15AnchoredAtom4728 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 5, 6, 7, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25827
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1987 Fin15AnchoredAtom1990 Fin15AnchoredAtom1993
    Fin15AnchoredAtom1994 Fin15AnchoredAtom1997 Fin15AnchoredAtom2000 Fin15AnchoredAtom2001
    Fin15AnchoredAtom2015 Fin15AnchoredAtom2016 Fin15AnchoredAtom2022 Fin15AnchoredAtom2025
    Fin15AnchoredAtom2028 Fin15AnchoredAtom2029 Fin15AnchoredAtom2043 Fin15AnchoredAtom2044
    Fin15AnchoredAtom2050 Fin15AnchoredAtom2064 Fin15AnchoredAtom2065 Fin15AnchoredAtom2071
    Fin15AnchoredAtom2102 Fin15AnchoredAtom2614 Fin15AnchoredAtom2617 Fin15AnchoredAtom2618
    Fin15AnchoredAtom2632 Fin15AnchoredAtom2633 Fin15AnchoredAtom2639 Fin15AnchoredAtom2653
    Fin15AnchoredAtom2654 Fin15AnchoredAtom2660 Fin15AnchoredAtom2691 Fin15AnchoredAtom2709
    Fin15AnchoredAtom2710 Fin15AnchoredAtom2716 Fin15AnchoredAtom2747 Fin15AnchoredAtom2782
    Fin15AnchoredAtom3329 Fin15AnchoredAtom3332 Fin15AnchoredAtom3333 Fin15AnchoredAtom3347
    Fin15AnchoredAtom3348 Fin15AnchoredAtom3354 Fin15AnchoredAtom3368 Fin15AnchoredAtom3369
    Fin15AnchoredAtom3375 Fin15AnchoredAtom3406 Fin15AnchoredAtom3424 Fin15AnchoredAtom3425
    Fin15AnchoredAtom3431 Fin15AnchoredAtom3462 Fin15AnchoredAtom3497 Fin15AnchoredAtom4585
    Fin15AnchoredAtom4586 Fin15AnchoredAtom4592 Fin15AnchoredAtom4623 Fin15AnchoredAtom4658
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

theorem fin15Anchored_clause31075 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1987 chi ∧
      ¬Fin15AnchoredAtom1992 chi ∧
      ¬Fin15AnchoredAtom1993 chi ∧
      ¬Fin15AnchoredAtom1994 chi ∧
      ¬Fin15AnchoredAtom1999 chi ∧
      ¬Fin15AnchoredAtom2000 chi ∧
      ¬Fin15AnchoredAtom2001 chi ∧
      ¬Fin15AnchoredAtom2020 chi ∧
      ¬Fin15AnchoredAtom2021 chi ∧
      ¬Fin15AnchoredAtom2022 chi ∧
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
      ¬Fin15AnchoredAtom2616 chi ∧
      ¬Fin15AnchoredAtom2617 chi ∧
      ¬Fin15AnchoredAtom2618 chi ∧
      ¬Fin15AnchoredAtom2637 chi ∧
      ¬Fin15AnchoredAtom2638 chi ∧
      ¬Fin15AnchoredAtom2639 chi ∧
      ¬Fin15AnchoredAtom2658 chi ∧
      ¬Fin15AnchoredAtom2659 chi ∧
      ¬Fin15AnchoredAtom2660 chi ∧
      ¬Fin15AnchoredAtom2695 chi ∧
      ¬Fin15AnchoredAtom2714 chi ∧
      ¬Fin15AnchoredAtom2715 chi ∧
      ¬Fin15AnchoredAtom2716 chi ∧
      ¬Fin15AnchoredAtom2751 chi ∧
      ¬Fin15AnchoredAtom2786 chi ∧
      ¬Fin15AnchoredAtom3331 chi ∧
      ¬Fin15AnchoredAtom3332 chi ∧
      ¬Fin15AnchoredAtom3333 chi ∧
      ¬Fin15AnchoredAtom3352 chi ∧
      ¬Fin15AnchoredAtom3353 chi ∧
      ¬Fin15AnchoredAtom3354 chi ∧
      ¬Fin15AnchoredAtom3373 chi ∧
      ¬Fin15AnchoredAtom3374 chi ∧
      ¬Fin15AnchoredAtom3375 chi ∧
      ¬Fin15AnchoredAtom3410 chi ∧
      ¬Fin15AnchoredAtom3429 chi ∧
      ¬Fin15AnchoredAtom3430 chi ∧
      ¬Fin15AnchoredAtom3431 chi ∧
      ¬Fin15AnchoredAtom3466 chi ∧
      ¬Fin15AnchoredAtom3501 chi ∧
      ¬Fin15AnchoredAtom4590 chi ∧
      ¬Fin15AnchoredAtom4591 chi ∧
      ¬Fin15AnchoredAtom4592 chi ∧
      ¬Fin15AnchoredAtom4627 chi ∧
      ¬Fin15AnchoredAtom4662 chi ∧
      ¬Fin15AnchoredAtom4732 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 5, 6, 7, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask28899
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1987 Fin15AnchoredAtom1992 Fin15AnchoredAtom1993
    Fin15AnchoredAtom1994 Fin15AnchoredAtom1999 Fin15AnchoredAtom2000 Fin15AnchoredAtom2001
    Fin15AnchoredAtom2020 Fin15AnchoredAtom2021 Fin15AnchoredAtom2022 Fin15AnchoredAtom2027
    Fin15AnchoredAtom2028 Fin15AnchoredAtom2029 Fin15AnchoredAtom2048 Fin15AnchoredAtom2049
    Fin15AnchoredAtom2050 Fin15AnchoredAtom2069 Fin15AnchoredAtom2070 Fin15AnchoredAtom2071
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2616 Fin15AnchoredAtom2617 Fin15AnchoredAtom2618
    Fin15AnchoredAtom2637 Fin15AnchoredAtom2638 Fin15AnchoredAtom2639 Fin15AnchoredAtom2658
    Fin15AnchoredAtom2659 Fin15AnchoredAtom2660 Fin15AnchoredAtom2695 Fin15AnchoredAtom2714
    Fin15AnchoredAtom2715 Fin15AnchoredAtom2716 Fin15AnchoredAtom2751 Fin15AnchoredAtom2786
    Fin15AnchoredAtom3331 Fin15AnchoredAtom3332 Fin15AnchoredAtom3333 Fin15AnchoredAtom3352
    Fin15AnchoredAtom3353 Fin15AnchoredAtom3354 Fin15AnchoredAtom3373 Fin15AnchoredAtom3374
    Fin15AnchoredAtom3375 Fin15AnchoredAtom3410 Fin15AnchoredAtom3429 Fin15AnchoredAtom3430
    Fin15AnchoredAtom3431 Fin15AnchoredAtom3466 Fin15AnchoredAtom3501 Fin15AnchoredAtom4590
    Fin15AnchoredAtom4591 Fin15AnchoredAtom4592 Fin15AnchoredAtom4627 Fin15AnchoredAtom4662
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

theorem fin15Anchored_clause31076 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1988 chi ∧
      ¬Fin15AnchoredAtom1989 chi ∧
      ¬Fin15AnchoredAtom1990 chi ∧
      ¬Fin15AnchoredAtom1992 chi ∧
      ¬Fin15AnchoredAtom2002 chi ∧
      ¬Fin15AnchoredAtom2003 chi ∧
      ¬Fin15AnchoredAtom2005 chi ∧
      ¬Fin15AnchoredAtom2008 chi ∧
      ¬Fin15AnchoredAtom2010 chi ∧
      ¬Fin15AnchoredAtom2014 chi ∧
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
      ¬Fin15AnchoredAtom2619 chi ∧
      ¬Fin15AnchoredAtom2620 chi ∧
      ¬Fin15AnchoredAtom2622 chi ∧
      ¬Fin15AnchoredAtom2625 chi ∧
      ¬Fin15AnchoredAtom2627 chi ∧
      ¬Fin15AnchoredAtom2631 chi ∧
      ¬Fin15AnchoredAtom2661 chi ∧
      ¬Fin15AnchoredAtom2663 chi ∧
      ¬Fin15AnchoredAtom2667 chi ∧
      ¬Fin15AnchoredAtom2677 chi ∧
      ¬Fin15AnchoredAtom2717 chi ∧
      ¬Fin15AnchoredAtom2719 chi ∧
      ¬Fin15AnchoredAtom2723 chi ∧
      ¬Fin15AnchoredAtom2733 chi ∧
      ¬Fin15AnchoredAtom2788 chi ∧
      ¬Fin15AnchoredAtom3334 chi ∧
      ¬Fin15AnchoredAtom3335 chi ∧
      ¬Fin15AnchoredAtom3337 chi ∧
      ¬Fin15AnchoredAtom3340 chi ∧
      ¬Fin15AnchoredAtom3342 chi ∧
      ¬Fin15AnchoredAtom3346 chi ∧
      ¬Fin15AnchoredAtom3376 chi ∧
      ¬Fin15AnchoredAtom3378 chi ∧
      ¬Fin15AnchoredAtom3382 chi ∧
      ¬Fin15AnchoredAtom3392 chi ∧
      ¬Fin15AnchoredAtom3432 chi ∧
      ¬Fin15AnchoredAtom3434 chi ∧
      ¬Fin15AnchoredAtom3438 chi ∧
      ¬Fin15AnchoredAtom3448 chi ∧
      ¬Fin15AnchoredAtom3503 chi ∧
      ¬Fin15AnchoredAtom4593 chi ∧
      ¬Fin15AnchoredAtom4595 chi ∧
      ¬Fin15AnchoredAtom4599 chi ∧
      ¬Fin15AnchoredAtom4609 chi ∧
      ¬Fin15AnchoredAtom4664 chi ∧
      ¬Fin15AnchoredAtom4734 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 5, 6, 8, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05987
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1988 Fin15AnchoredAtom1989 Fin15AnchoredAtom1990
    Fin15AnchoredAtom1992 Fin15AnchoredAtom2002 Fin15AnchoredAtom2003 Fin15AnchoredAtom2005
    Fin15AnchoredAtom2008 Fin15AnchoredAtom2010 Fin15AnchoredAtom2014 Fin15AnchoredAtom2030
    Fin15AnchoredAtom2031 Fin15AnchoredAtom2033 Fin15AnchoredAtom2036 Fin15AnchoredAtom2038
    Fin15AnchoredAtom2042 Fin15AnchoredAtom2072 Fin15AnchoredAtom2074 Fin15AnchoredAtom2078
    Fin15AnchoredAtom2088 Fin15AnchoredAtom2619 Fin15AnchoredAtom2620 Fin15AnchoredAtom2622
    Fin15AnchoredAtom2625 Fin15AnchoredAtom2627 Fin15AnchoredAtom2631 Fin15AnchoredAtom2661
    Fin15AnchoredAtom2663 Fin15AnchoredAtom2667 Fin15AnchoredAtom2677 Fin15AnchoredAtom2717
    Fin15AnchoredAtom2719 Fin15AnchoredAtom2723 Fin15AnchoredAtom2733 Fin15AnchoredAtom2788
    Fin15AnchoredAtom3334 Fin15AnchoredAtom3335 Fin15AnchoredAtom3337 Fin15AnchoredAtom3340
    Fin15AnchoredAtom3342 Fin15AnchoredAtom3346 Fin15AnchoredAtom3376 Fin15AnchoredAtom3378
    Fin15AnchoredAtom3382 Fin15AnchoredAtom3392 Fin15AnchoredAtom3432 Fin15AnchoredAtom3434
    Fin15AnchoredAtom3438 Fin15AnchoredAtom3448 Fin15AnchoredAtom3503 Fin15AnchoredAtom4593
    Fin15AnchoredAtom4595 Fin15AnchoredAtom4599 Fin15AnchoredAtom4609 Fin15AnchoredAtom4664
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

theorem fin15Anchored_clause31077 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1988 chi ∧
      ¬Fin15AnchoredAtom1989 chi ∧
      ¬Fin15AnchoredAtom1992 chi ∧
      ¬Fin15AnchoredAtom1993 chi ∧
      ¬Fin15AnchoredAtom2002 chi ∧
      ¬Fin15AnchoredAtom2005 chi ∧
      ¬Fin15AnchoredAtom2006 chi ∧
      ¬Fin15AnchoredAtom2010 chi ∧
      ¬Fin15AnchoredAtom2011 chi ∧
      ¬Fin15AnchoredAtom2020 chi ∧
      ¬Fin15AnchoredAtom2030 chi ∧
      ¬Fin15AnchoredAtom2033 chi ∧
      ¬Fin15AnchoredAtom2034 chi ∧
      ¬Fin15AnchoredAtom2038 chi ∧
      ¬Fin15AnchoredAtom2039 chi ∧
      ¬Fin15AnchoredAtom2048 chi ∧
      ¬Fin15AnchoredAtom2074 chi ∧
      ¬Fin15AnchoredAtom2075 chi ∧
      ¬Fin15AnchoredAtom2084 chi ∧
      ¬Fin15AnchoredAtom2094 chi ∧
      ¬Fin15AnchoredAtom2619 chi ∧
      ¬Fin15AnchoredAtom2622 chi ∧
      ¬Fin15AnchoredAtom2623 chi ∧
      ¬Fin15AnchoredAtom2627 chi ∧
      ¬Fin15AnchoredAtom2628 chi ∧
      ¬Fin15AnchoredAtom2637 chi ∧
      ¬Fin15AnchoredAtom2663 chi ∧
      ¬Fin15AnchoredAtom2664 chi ∧
      ¬Fin15AnchoredAtom2673 chi ∧
      ¬Fin15AnchoredAtom2683 chi ∧
      ¬Fin15AnchoredAtom2719 chi ∧
      ¬Fin15AnchoredAtom2720 chi ∧
      ¬Fin15AnchoredAtom2729 chi ∧
      ¬Fin15AnchoredAtom2739 chi ∧
      ¬Fin15AnchoredAtom2794 chi ∧
      ¬Fin15AnchoredAtom3334 chi ∧
      ¬Fin15AnchoredAtom3337 chi ∧
      ¬Fin15AnchoredAtom3338 chi ∧
      ¬Fin15AnchoredAtom3342 chi ∧
      ¬Fin15AnchoredAtom3343 chi ∧
      ¬Fin15AnchoredAtom3352 chi ∧
      ¬Fin15AnchoredAtom3378 chi ∧
      ¬Fin15AnchoredAtom3379 chi ∧
      ¬Fin15AnchoredAtom3388 chi ∧
      ¬Fin15AnchoredAtom3398 chi ∧
      ¬Fin15AnchoredAtom3434 chi ∧
      ¬Fin15AnchoredAtom3435 chi ∧
      ¬Fin15AnchoredAtom3444 chi ∧
      ¬Fin15AnchoredAtom3454 chi ∧
      ¬Fin15AnchoredAtom3509 chi ∧
      ¬Fin15AnchoredAtom4595 chi ∧
      ¬Fin15AnchoredAtom4596 chi ∧
      ¬Fin15AnchoredAtom4605 chi ∧
      ¬Fin15AnchoredAtom4615 chi ∧
      ¬Fin15AnchoredAtom4670 chi ∧
      ¬Fin15AnchoredAtom4740 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 5, 6, 8, 9, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13155
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1988 Fin15AnchoredAtom1989 Fin15AnchoredAtom1992
    Fin15AnchoredAtom1993 Fin15AnchoredAtom2002 Fin15AnchoredAtom2005 Fin15AnchoredAtom2006
    Fin15AnchoredAtom2010 Fin15AnchoredAtom2011 Fin15AnchoredAtom2020 Fin15AnchoredAtom2030
    Fin15AnchoredAtom2033 Fin15AnchoredAtom2034 Fin15AnchoredAtom2038 Fin15AnchoredAtom2039
    Fin15AnchoredAtom2048 Fin15AnchoredAtom2074 Fin15AnchoredAtom2075 Fin15AnchoredAtom2084
    Fin15AnchoredAtom2094 Fin15AnchoredAtom2619 Fin15AnchoredAtom2622 Fin15AnchoredAtom2623
    Fin15AnchoredAtom2627 Fin15AnchoredAtom2628 Fin15AnchoredAtom2637 Fin15AnchoredAtom2663
    Fin15AnchoredAtom2664 Fin15AnchoredAtom2673 Fin15AnchoredAtom2683 Fin15AnchoredAtom2719
    Fin15AnchoredAtom2720 Fin15AnchoredAtom2729 Fin15AnchoredAtom2739 Fin15AnchoredAtom2794
    Fin15AnchoredAtom3334 Fin15AnchoredAtom3337 Fin15AnchoredAtom3338 Fin15AnchoredAtom3342
    Fin15AnchoredAtom3343 Fin15AnchoredAtom3352 Fin15AnchoredAtom3378 Fin15AnchoredAtom3379
    Fin15AnchoredAtom3388 Fin15AnchoredAtom3398 Fin15AnchoredAtom3434 Fin15AnchoredAtom3435
    Fin15AnchoredAtom3444 Fin15AnchoredAtom3454 Fin15AnchoredAtom3509 Fin15AnchoredAtom4595
    Fin15AnchoredAtom4596 Fin15AnchoredAtom4605 Fin15AnchoredAtom4615 Fin15AnchoredAtom4670
    Fin15AnchoredAtom4740 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31078 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1988 chi ∧
      ¬Fin15AnchoredAtom1990 chi ∧
      ¬Fin15AnchoredAtom1993 chi ∧
      ¬Fin15AnchoredAtom1994 chi ∧
      ¬Fin15AnchoredAtom2003 chi ∧
      ¬Fin15AnchoredAtom2006 chi ∧
      ¬Fin15AnchoredAtom2007 chi ∧
      ¬Fin15AnchoredAtom2015 chi ∧
      ¬Fin15AnchoredAtom2016 chi ∧
      ¬Fin15AnchoredAtom2022 chi ∧
      ¬Fin15AnchoredAtom2031 chi ∧
      ¬Fin15AnchoredAtom2034 chi ∧
      ¬Fin15AnchoredAtom2035 chi ∧
      ¬Fin15AnchoredAtom2043 chi ∧
      ¬Fin15AnchoredAtom2044 chi ∧
      ¬Fin15AnchoredAtom2050 chi ∧
      ¬Fin15AnchoredAtom2079 chi ∧
      ¬Fin15AnchoredAtom2080 chi ∧
      ¬Fin15AnchoredAtom2086 chi ∧
      ¬Fin15AnchoredAtom2102 chi ∧
      ¬Fin15AnchoredAtom2620 chi ∧
      ¬Fin15AnchoredAtom2623 chi ∧
      ¬Fin15AnchoredAtom2624 chi ∧
      ¬Fin15AnchoredAtom2632 chi ∧
      ¬Fin15AnchoredAtom2633 chi ∧
      ¬Fin15AnchoredAtom2639 chi ∧
      ¬Fin15AnchoredAtom2668 chi ∧
      ¬Fin15AnchoredAtom2669 chi ∧
      ¬Fin15AnchoredAtom2675 chi ∧
      ¬Fin15AnchoredAtom2691 chi ∧
      ¬Fin15AnchoredAtom2724 chi ∧
      ¬Fin15AnchoredAtom2725 chi ∧
      ¬Fin15AnchoredAtom2731 chi ∧
      ¬Fin15AnchoredAtom2747 chi ∧
      ¬Fin15AnchoredAtom2802 chi ∧
      ¬Fin15AnchoredAtom3335 chi ∧
      ¬Fin15AnchoredAtom3338 chi ∧
      ¬Fin15AnchoredAtom3339 chi ∧
      ¬Fin15AnchoredAtom3347 chi ∧
      ¬Fin15AnchoredAtom3348 chi ∧
      ¬Fin15AnchoredAtom3354 chi ∧
      ¬Fin15AnchoredAtom3383 chi ∧
      ¬Fin15AnchoredAtom3384 chi ∧
      ¬Fin15AnchoredAtom3390 chi ∧
      ¬Fin15AnchoredAtom3406 chi ∧
      ¬Fin15AnchoredAtom3439 chi ∧
      ¬Fin15AnchoredAtom3440 chi ∧
      ¬Fin15AnchoredAtom3446 chi ∧
      ¬Fin15AnchoredAtom3462 chi ∧
      ¬Fin15AnchoredAtom3517 chi ∧
      ¬Fin15AnchoredAtom4600 chi ∧
      ¬Fin15AnchoredAtom4601 chi ∧
      ¬Fin15AnchoredAtom4607 chi ∧
      ¬Fin15AnchoredAtom4623 chi ∧
      ¬Fin15AnchoredAtom4678 chi ∧
      ¬Fin15AnchoredAtom4748 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 5, 6, 8, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25955
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1988 Fin15AnchoredAtom1990 Fin15AnchoredAtom1993
    Fin15AnchoredAtom1994 Fin15AnchoredAtom2003 Fin15AnchoredAtom2006 Fin15AnchoredAtom2007
    Fin15AnchoredAtom2015 Fin15AnchoredAtom2016 Fin15AnchoredAtom2022 Fin15AnchoredAtom2031
    Fin15AnchoredAtom2034 Fin15AnchoredAtom2035 Fin15AnchoredAtom2043 Fin15AnchoredAtom2044
    Fin15AnchoredAtom2050 Fin15AnchoredAtom2079 Fin15AnchoredAtom2080 Fin15AnchoredAtom2086
    Fin15AnchoredAtom2102 Fin15AnchoredAtom2620 Fin15AnchoredAtom2623 Fin15AnchoredAtom2624
    Fin15AnchoredAtom2632 Fin15AnchoredAtom2633 Fin15AnchoredAtom2639 Fin15AnchoredAtom2668
    Fin15AnchoredAtom2669 Fin15AnchoredAtom2675 Fin15AnchoredAtom2691 Fin15AnchoredAtom2724
    Fin15AnchoredAtom2725 Fin15AnchoredAtom2731 Fin15AnchoredAtom2747 Fin15AnchoredAtom2802
    Fin15AnchoredAtom3335 Fin15AnchoredAtom3338 Fin15AnchoredAtom3339 Fin15AnchoredAtom3347
    Fin15AnchoredAtom3348 Fin15AnchoredAtom3354 Fin15AnchoredAtom3383 Fin15AnchoredAtom3384
    Fin15AnchoredAtom3390 Fin15AnchoredAtom3406 Fin15AnchoredAtom3439 Fin15AnchoredAtom3440
    Fin15AnchoredAtom3446 Fin15AnchoredAtom3462 Fin15AnchoredAtom3517 Fin15AnchoredAtom4600
    Fin15AnchoredAtom4601 Fin15AnchoredAtom4607 Fin15AnchoredAtom4623 Fin15AnchoredAtom4678
    Fin15AnchoredAtom4748 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31079 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1989 chi ∧
      ¬Fin15AnchoredAtom1990 chi ∧
      ¬Fin15AnchoredAtom1992 chi ∧
      ¬Fin15AnchoredAtom1993 chi ∧
      ¬Fin15AnchoredAtom2008 chi ∧
      ¬Fin15AnchoredAtom2010 chi ∧
      ¬Fin15AnchoredAtom2011 chi ∧
      ¬Fin15AnchoredAtom2014 chi ∧
      ¬Fin15AnchoredAtom2015 chi ∧
      ¬Fin15AnchoredAtom2020 chi ∧
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
      ¬Fin15AnchoredAtom2625 chi ∧
      ¬Fin15AnchoredAtom2627 chi ∧
      ¬Fin15AnchoredAtom2628 chi ∧
      ¬Fin15AnchoredAtom2631 chi ∧
      ¬Fin15AnchoredAtom2632 chi ∧
      ¬Fin15AnchoredAtom2637 chi ∧
      ¬Fin15AnchoredAtom2677 chi ∧
      ¬Fin15AnchoredAtom2678 chi ∧
      ¬Fin15AnchoredAtom2683 chi ∧
      ¬Fin15AnchoredAtom2689 chi ∧
      ¬Fin15AnchoredAtom2733 chi ∧
      ¬Fin15AnchoredAtom2734 chi ∧
      ¬Fin15AnchoredAtom2739 chi ∧
      ¬Fin15AnchoredAtom2745 chi ∧
      ¬Fin15AnchoredAtom2810 chi ∧
      ¬Fin15AnchoredAtom3340 chi ∧
      ¬Fin15AnchoredAtom3342 chi ∧
      ¬Fin15AnchoredAtom3343 chi ∧
      ¬Fin15AnchoredAtom3346 chi ∧
      ¬Fin15AnchoredAtom3347 chi ∧
      ¬Fin15AnchoredAtom3352 chi ∧
      ¬Fin15AnchoredAtom3392 chi ∧
      ¬Fin15AnchoredAtom3393 chi ∧
      ¬Fin15AnchoredAtom3398 chi ∧
      ¬Fin15AnchoredAtom3404 chi ∧
      ¬Fin15AnchoredAtom3448 chi ∧
      ¬Fin15AnchoredAtom3449 chi ∧
      ¬Fin15AnchoredAtom3454 chi ∧
      ¬Fin15AnchoredAtom3460 chi ∧
      ¬Fin15AnchoredAtom3525 chi ∧
      ¬Fin15AnchoredAtom4609 chi ∧
      ¬Fin15AnchoredAtom4610 chi ∧
      ¬Fin15AnchoredAtom4615 chi ∧
      ¬Fin15AnchoredAtom4621 chi ∧
      ¬Fin15AnchoredAtom4686 chi ∧
      ¬Fin15AnchoredAtom4756 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 5, 6, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13923
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1989 Fin15AnchoredAtom1990 Fin15AnchoredAtom1992
    Fin15AnchoredAtom1993 Fin15AnchoredAtom2008 Fin15AnchoredAtom2010 Fin15AnchoredAtom2011
    Fin15AnchoredAtom2014 Fin15AnchoredAtom2015 Fin15AnchoredAtom2020 Fin15AnchoredAtom2036
    Fin15AnchoredAtom2038 Fin15AnchoredAtom2039 Fin15AnchoredAtom2042 Fin15AnchoredAtom2043
    Fin15AnchoredAtom2048 Fin15AnchoredAtom2088 Fin15AnchoredAtom2089 Fin15AnchoredAtom2094
    Fin15AnchoredAtom2100 Fin15AnchoredAtom2625 Fin15AnchoredAtom2627 Fin15AnchoredAtom2628
    Fin15AnchoredAtom2631 Fin15AnchoredAtom2632 Fin15AnchoredAtom2637 Fin15AnchoredAtom2677
    Fin15AnchoredAtom2678 Fin15AnchoredAtom2683 Fin15AnchoredAtom2689 Fin15AnchoredAtom2733
    Fin15AnchoredAtom2734 Fin15AnchoredAtom2739 Fin15AnchoredAtom2745 Fin15AnchoredAtom2810
    Fin15AnchoredAtom3340 Fin15AnchoredAtom3342 Fin15AnchoredAtom3343 Fin15AnchoredAtom3346
    Fin15AnchoredAtom3347 Fin15AnchoredAtom3352 Fin15AnchoredAtom3392 Fin15AnchoredAtom3393
    Fin15AnchoredAtom3398 Fin15AnchoredAtom3404 Fin15AnchoredAtom3448 Fin15AnchoredAtom3449
    Fin15AnchoredAtom3454 Fin15AnchoredAtom3460 Fin15AnchoredAtom3525 Fin15AnchoredAtom4609
    Fin15AnchoredAtom4610 Fin15AnchoredAtom4615 Fin15AnchoredAtom4621 Fin15AnchoredAtom4686
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

theorem fin15Anchored_clause31080 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1989 chi ∧
      ¬Fin15AnchoredAtom1990 chi ∧
      ¬Fin15AnchoredAtom1992 chi ∧
      ¬Fin15AnchoredAtom1994 chi ∧
      ¬Fin15AnchoredAtom2008 chi ∧
      ¬Fin15AnchoredAtom2010 chi ∧
      ¬Fin15AnchoredAtom2012 chi ∧
      ¬Fin15AnchoredAtom2014 chi ∧
      ¬Fin15AnchoredAtom2016 chi ∧
      ¬Fin15AnchoredAtom2021 chi ∧
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
      ¬Fin15AnchoredAtom2625 chi ∧
      ¬Fin15AnchoredAtom2627 chi ∧
      ¬Fin15AnchoredAtom2629 chi ∧
      ¬Fin15AnchoredAtom2631 chi ∧
      ¬Fin15AnchoredAtom2633 chi ∧
      ¬Fin15AnchoredAtom2638 chi ∧
      ¬Fin15AnchoredAtom2677 chi ∧
      ¬Fin15AnchoredAtom2679 chi ∧
      ¬Fin15AnchoredAtom2684 chi ∧
      ¬Fin15AnchoredAtom2690 chi ∧
      ¬Fin15AnchoredAtom2733 chi ∧
      ¬Fin15AnchoredAtom2735 chi ∧
      ¬Fin15AnchoredAtom2740 chi ∧
      ¬Fin15AnchoredAtom2746 chi ∧
      ¬Fin15AnchoredAtom2811 chi ∧
      ¬Fin15AnchoredAtom3340 chi ∧
      ¬Fin15AnchoredAtom3342 chi ∧
      ¬Fin15AnchoredAtom3344 chi ∧
      ¬Fin15AnchoredAtom3346 chi ∧
      ¬Fin15AnchoredAtom3348 chi ∧
      ¬Fin15AnchoredAtom3353 chi ∧
      ¬Fin15AnchoredAtom3392 chi ∧
      ¬Fin15AnchoredAtom3394 chi ∧
      ¬Fin15AnchoredAtom3399 chi ∧
      ¬Fin15AnchoredAtom3405 chi ∧
      ¬Fin15AnchoredAtom3448 chi ∧
      ¬Fin15AnchoredAtom3450 chi ∧
      ¬Fin15AnchoredAtom3455 chi ∧
      ¬Fin15AnchoredAtom3461 chi ∧
      ¬Fin15AnchoredAtom3526 chi ∧
      ¬Fin15AnchoredAtom4609 chi ∧
      ¬Fin15AnchoredAtom4611 chi ∧
      ¬Fin15AnchoredAtom4616 chi ∧
      ¬Fin15AnchoredAtom4622 chi ∧
      ¬Fin15AnchoredAtom4687 chi ∧
      ¬Fin15AnchoredAtom4757 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 5, 6, 9, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22115
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1989 Fin15AnchoredAtom1990 Fin15AnchoredAtom1992
    Fin15AnchoredAtom1994 Fin15AnchoredAtom2008 Fin15AnchoredAtom2010 Fin15AnchoredAtom2012
    Fin15AnchoredAtom2014 Fin15AnchoredAtom2016 Fin15AnchoredAtom2021 Fin15AnchoredAtom2036
    Fin15AnchoredAtom2038 Fin15AnchoredAtom2040 Fin15AnchoredAtom2042 Fin15AnchoredAtom2044
    Fin15AnchoredAtom2049 Fin15AnchoredAtom2088 Fin15AnchoredAtom2090 Fin15AnchoredAtom2095
    Fin15AnchoredAtom2101 Fin15AnchoredAtom2625 Fin15AnchoredAtom2627 Fin15AnchoredAtom2629
    Fin15AnchoredAtom2631 Fin15AnchoredAtom2633 Fin15AnchoredAtom2638 Fin15AnchoredAtom2677
    Fin15AnchoredAtom2679 Fin15AnchoredAtom2684 Fin15AnchoredAtom2690 Fin15AnchoredAtom2733
    Fin15AnchoredAtom2735 Fin15AnchoredAtom2740 Fin15AnchoredAtom2746 Fin15AnchoredAtom2811
    Fin15AnchoredAtom3340 Fin15AnchoredAtom3342 Fin15AnchoredAtom3344 Fin15AnchoredAtom3346
    Fin15AnchoredAtom3348 Fin15AnchoredAtom3353 Fin15AnchoredAtom3392 Fin15AnchoredAtom3394
    Fin15AnchoredAtom3399 Fin15AnchoredAtom3405 Fin15AnchoredAtom3448 Fin15AnchoredAtom3450
    Fin15AnchoredAtom3455 Fin15AnchoredAtom3461 Fin15AnchoredAtom3526 Fin15AnchoredAtom4609
    Fin15AnchoredAtom4611 Fin15AnchoredAtom4616 Fin15AnchoredAtom4622 Fin15AnchoredAtom4687
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

theorem fin15Anchored_clause31081 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1989 chi ∧
      ¬Fin15AnchoredAtom1990 chi ∧
      ¬Fin15AnchoredAtom1993 chi ∧
      ¬Fin15AnchoredAtom1994 chi ∧
      ¬Fin15AnchoredAtom2008 chi ∧
      ¬Fin15AnchoredAtom2011 chi ∧
      ¬Fin15AnchoredAtom2012 chi ∧
      ¬Fin15AnchoredAtom2015 chi ∧
      ¬Fin15AnchoredAtom2016 chi ∧
      ¬Fin15AnchoredAtom2022 chi ∧
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
      ¬Fin15AnchoredAtom2625 chi ∧
      ¬Fin15AnchoredAtom2628 chi ∧
      ¬Fin15AnchoredAtom2629 chi ∧
      ¬Fin15AnchoredAtom2632 chi ∧
      ¬Fin15AnchoredAtom2633 chi ∧
      ¬Fin15AnchoredAtom2639 chi ∧
      ¬Fin15AnchoredAtom2678 chi ∧
      ¬Fin15AnchoredAtom2679 chi ∧
      ¬Fin15AnchoredAtom2685 chi ∧
      ¬Fin15AnchoredAtom2691 chi ∧
      ¬Fin15AnchoredAtom2734 chi ∧
      ¬Fin15AnchoredAtom2735 chi ∧
      ¬Fin15AnchoredAtom2741 chi ∧
      ¬Fin15AnchoredAtom2747 chi ∧
      ¬Fin15AnchoredAtom2812 chi ∧
      ¬Fin15AnchoredAtom3340 chi ∧
      ¬Fin15AnchoredAtom3343 chi ∧
      ¬Fin15AnchoredAtom3344 chi ∧
      ¬Fin15AnchoredAtom3347 chi ∧
      ¬Fin15AnchoredAtom3348 chi ∧
      ¬Fin15AnchoredAtom3354 chi ∧
      ¬Fin15AnchoredAtom3393 chi ∧
      ¬Fin15AnchoredAtom3394 chi ∧
      ¬Fin15AnchoredAtom3400 chi ∧
      ¬Fin15AnchoredAtom3406 chi ∧
      ¬Fin15AnchoredAtom3449 chi ∧
      ¬Fin15AnchoredAtom3450 chi ∧
      ¬Fin15AnchoredAtom3456 chi ∧
      ¬Fin15AnchoredAtom3462 chi ∧
      ¬Fin15AnchoredAtom3527 chi ∧
      ¬Fin15AnchoredAtom4610 chi ∧
      ¬Fin15AnchoredAtom4611 chi ∧
      ¬Fin15AnchoredAtom4617 chi ∧
      ¬Fin15AnchoredAtom4623 chi ∧
      ¬Fin15AnchoredAtom4688 chi ∧
      ¬Fin15AnchoredAtom4758 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 5, 6, 9, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26211
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1989 Fin15AnchoredAtom1990 Fin15AnchoredAtom1993
    Fin15AnchoredAtom1994 Fin15AnchoredAtom2008 Fin15AnchoredAtom2011 Fin15AnchoredAtom2012
    Fin15AnchoredAtom2015 Fin15AnchoredAtom2016 Fin15AnchoredAtom2022 Fin15AnchoredAtom2036
    Fin15AnchoredAtom2039 Fin15AnchoredAtom2040 Fin15AnchoredAtom2043 Fin15AnchoredAtom2044
    Fin15AnchoredAtom2050 Fin15AnchoredAtom2089 Fin15AnchoredAtom2090 Fin15AnchoredAtom2096
    Fin15AnchoredAtom2102 Fin15AnchoredAtom2625 Fin15AnchoredAtom2628 Fin15AnchoredAtom2629
    Fin15AnchoredAtom2632 Fin15AnchoredAtom2633 Fin15AnchoredAtom2639 Fin15AnchoredAtom2678
    Fin15AnchoredAtom2679 Fin15AnchoredAtom2685 Fin15AnchoredAtom2691 Fin15AnchoredAtom2734
    Fin15AnchoredAtom2735 Fin15AnchoredAtom2741 Fin15AnchoredAtom2747 Fin15AnchoredAtom2812
    Fin15AnchoredAtom3340 Fin15AnchoredAtom3343 Fin15AnchoredAtom3344 Fin15AnchoredAtom3347
    Fin15AnchoredAtom3348 Fin15AnchoredAtom3354 Fin15AnchoredAtom3393 Fin15AnchoredAtom3394
    Fin15AnchoredAtom3400 Fin15AnchoredAtom3406 Fin15AnchoredAtom3449 Fin15AnchoredAtom3450
    Fin15AnchoredAtom3456 Fin15AnchoredAtom3462 Fin15AnchoredAtom3527 Fin15AnchoredAtom4610
    Fin15AnchoredAtom4611 Fin15AnchoredAtom4617 Fin15AnchoredAtom4623 Fin15AnchoredAtom4688
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

theorem fin15Anchored_clause31082 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1989 chi ∧
      ¬Fin15AnchoredAtom1992 chi ∧
      ¬Fin15AnchoredAtom1993 chi ∧
      ¬Fin15AnchoredAtom1994 chi ∧
      ¬Fin15AnchoredAtom2010 chi ∧
      ¬Fin15AnchoredAtom2011 chi ∧
      ¬Fin15AnchoredAtom2012 chi ∧
      ¬Fin15AnchoredAtom2020 chi ∧
      ¬Fin15AnchoredAtom2021 chi ∧
      ¬Fin15AnchoredAtom2022 chi ∧
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
      ¬Fin15AnchoredAtom2627 chi ∧
      ¬Fin15AnchoredAtom2628 chi ∧
      ¬Fin15AnchoredAtom2629 chi ∧
      ¬Fin15AnchoredAtom2637 chi ∧
      ¬Fin15AnchoredAtom2638 chi ∧
      ¬Fin15AnchoredAtom2639 chi ∧
      ¬Fin15AnchoredAtom2683 chi ∧
      ¬Fin15AnchoredAtom2684 chi ∧
      ¬Fin15AnchoredAtom2685 chi ∧
      ¬Fin15AnchoredAtom2695 chi ∧
      ¬Fin15AnchoredAtom2739 chi ∧
      ¬Fin15AnchoredAtom2740 chi ∧
      ¬Fin15AnchoredAtom2741 chi ∧
      ¬Fin15AnchoredAtom2751 chi ∧
      ¬Fin15AnchoredAtom2816 chi ∧
      ¬Fin15AnchoredAtom3342 chi ∧
      ¬Fin15AnchoredAtom3343 chi ∧
      ¬Fin15AnchoredAtom3344 chi ∧
      ¬Fin15AnchoredAtom3352 chi ∧
      ¬Fin15AnchoredAtom3353 chi ∧
      ¬Fin15AnchoredAtom3354 chi ∧
      ¬Fin15AnchoredAtom3398 chi ∧
      ¬Fin15AnchoredAtom3399 chi ∧
      ¬Fin15AnchoredAtom3400 chi ∧
      ¬Fin15AnchoredAtom3410 chi ∧
      ¬Fin15AnchoredAtom3454 chi ∧
      ¬Fin15AnchoredAtom3455 chi ∧
      ¬Fin15AnchoredAtom3456 chi ∧
      ¬Fin15AnchoredAtom3466 chi ∧
      ¬Fin15AnchoredAtom3531 chi ∧
      ¬Fin15AnchoredAtom4615 chi ∧
      ¬Fin15AnchoredAtom4616 chi ∧
      ¬Fin15AnchoredAtom4617 chi ∧
      ¬Fin15AnchoredAtom4627 chi ∧
      ¬Fin15AnchoredAtom4692 chi ∧
      ¬Fin15AnchoredAtom4762 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 5, 6, 9, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29283
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1989 Fin15AnchoredAtom1992 Fin15AnchoredAtom1993
    Fin15AnchoredAtom1994 Fin15AnchoredAtom2010 Fin15AnchoredAtom2011 Fin15AnchoredAtom2012
    Fin15AnchoredAtom2020 Fin15AnchoredAtom2021 Fin15AnchoredAtom2022 Fin15AnchoredAtom2038
    Fin15AnchoredAtom2039 Fin15AnchoredAtom2040 Fin15AnchoredAtom2048 Fin15AnchoredAtom2049
    Fin15AnchoredAtom2050 Fin15AnchoredAtom2094 Fin15AnchoredAtom2095 Fin15AnchoredAtom2096
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2627 Fin15AnchoredAtom2628 Fin15AnchoredAtom2629
    Fin15AnchoredAtom2637 Fin15AnchoredAtom2638 Fin15AnchoredAtom2639 Fin15AnchoredAtom2683
    Fin15AnchoredAtom2684 Fin15AnchoredAtom2685 Fin15AnchoredAtom2695 Fin15AnchoredAtom2739
    Fin15AnchoredAtom2740 Fin15AnchoredAtom2741 Fin15AnchoredAtom2751 Fin15AnchoredAtom2816
    Fin15AnchoredAtom3342 Fin15AnchoredAtom3343 Fin15AnchoredAtom3344 Fin15AnchoredAtom3352
    Fin15AnchoredAtom3353 Fin15AnchoredAtom3354 Fin15AnchoredAtom3398 Fin15AnchoredAtom3399
    Fin15AnchoredAtom3400 Fin15AnchoredAtom3410 Fin15AnchoredAtom3454 Fin15AnchoredAtom3455
    Fin15AnchoredAtom3456 Fin15AnchoredAtom3466 Fin15AnchoredAtom3531 Fin15AnchoredAtom4615
    Fin15AnchoredAtom4616 Fin15AnchoredAtom4617 Fin15AnchoredAtom4627 Fin15AnchoredAtom4692
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

theorem fin15Anchored_clause31083 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1990 chi ∧
      ¬Fin15AnchoredAtom1992 chi ∧
      ¬Fin15AnchoredAtom1993 chi ∧
      ¬Fin15AnchoredAtom1994 chi ∧
      ¬Fin15AnchoredAtom2014 chi ∧
      ¬Fin15AnchoredAtom2015 chi ∧
      ¬Fin15AnchoredAtom2016 chi ∧
      ¬Fin15AnchoredAtom2020 chi ∧
      ¬Fin15AnchoredAtom2021 chi ∧
      ¬Fin15AnchoredAtom2022 chi ∧
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
      ¬Fin15AnchoredAtom2631 chi ∧
      ¬Fin15AnchoredAtom2632 chi ∧
      ¬Fin15AnchoredAtom2633 chi ∧
      ¬Fin15AnchoredAtom2637 chi ∧
      ¬Fin15AnchoredAtom2638 chi ∧
      ¬Fin15AnchoredAtom2639 chi ∧
      ¬Fin15AnchoredAtom2689 chi ∧
      ¬Fin15AnchoredAtom2690 chi ∧
      ¬Fin15AnchoredAtom2691 chi ∧
      ¬Fin15AnchoredAtom2695 chi ∧
      ¬Fin15AnchoredAtom2745 chi ∧
      ¬Fin15AnchoredAtom2746 chi ∧
      ¬Fin15AnchoredAtom2747 chi ∧
      ¬Fin15AnchoredAtom2751 chi ∧
      ¬Fin15AnchoredAtom2820 chi ∧
      ¬Fin15AnchoredAtom3346 chi ∧
      ¬Fin15AnchoredAtom3347 chi ∧
      ¬Fin15AnchoredAtom3348 chi ∧
      ¬Fin15AnchoredAtom3352 chi ∧
      ¬Fin15AnchoredAtom3353 chi ∧
      ¬Fin15AnchoredAtom3354 chi ∧
      ¬Fin15AnchoredAtom3404 chi ∧
      ¬Fin15AnchoredAtom3405 chi ∧
      ¬Fin15AnchoredAtom3406 chi ∧
      ¬Fin15AnchoredAtom3410 chi ∧
      ¬Fin15AnchoredAtom3460 chi ∧
      ¬Fin15AnchoredAtom3461 chi ∧
      ¬Fin15AnchoredAtom3462 chi ∧
      ¬Fin15AnchoredAtom3466 chi ∧
      ¬Fin15AnchoredAtom3535 chi ∧
      ¬Fin15AnchoredAtom4621 chi ∧
      ¬Fin15AnchoredAtom4622 chi ∧
      ¬Fin15AnchoredAtom4623 chi ∧
      ¬Fin15AnchoredAtom4627 chi ∧
      ¬Fin15AnchoredAtom4696 chi ∧
      ¬Fin15AnchoredAtom4766 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 5, 6, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29795
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1990 Fin15AnchoredAtom1992 Fin15AnchoredAtom1993
    Fin15AnchoredAtom1994 Fin15AnchoredAtom2014 Fin15AnchoredAtom2015 Fin15AnchoredAtom2016
    Fin15AnchoredAtom2020 Fin15AnchoredAtom2021 Fin15AnchoredAtom2022 Fin15AnchoredAtom2042
    Fin15AnchoredAtom2043 Fin15AnchoredAtom2044 Fin15AnchoredAtom2048 Fin15AnchoredAtom2049
    Fin15AnchoredAtom2050 Fin15AnchoredAtom2100 Fin15AnchoredAtom2101 Fin15AnchoredAtom2102
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2631 Fin15AnchoredAtom2632 Fin15AnchoredAtom2633
    Fin15AnchoredAtom2637 Fin15AnchoredAtom2638 Fin15AnchoredAtom2639 Fin15AnchoredAtom2689
    Fin15AnchoredAtom2690 Fin15AnchoredAtom2691 Fin15AnchoredAtom2695 Fin15AnchoredAtom2745
    Fin15AnchoredAtom2746 Fin15AnchoredAtom2747 Fin15AnchoredAtom2751 Fin15AnchoredAtom2820
    Fin15AnchoredAtom3346 Fin15AnchoredAtom3347 Fin15AnchoredAtom3348 Fin15AnchoredAtom3352
    Fin15AnchoredAtom3353 Fin15AnchoredAtom3354 Fin15AnchoredAtom3404 Fin15AnchoredAtom3405
    Fin15AnchoredAtom3406 Fin15AnchoredAtom3410 Fin15AnchoredAtom3460 Fin15AnchoredAtom3461
    Fin15AnchoredAtom3462 Fin15AnchoredAtom3466 Fin15AnchoredAtom3535 Fin15AnchoredAtom4621
    Fin15AnchoredAtom4622 Fin15AnchoredAtom4623 Fin15AnchoredAtom4627 Fin15AnchoredAtom4696
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

theorem fin15Anchored_clause31084 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1995 chi ∧
      ¬Fin15AnchoredAtom1996 chi ∧
      ¬Fin15AnchoredAtom1997 chi ∧
      ¬Fin15AnchoredAtom2000 chi ∧
      ¬Fin15AnchoredAtom2002 chi ∧
      ¬Fin15AnchoredAtom2003 chi ∧
      ¬Fin15AnchoredAtom2006 chi ∧
      ¬Fin15AnchoredAtom2008 chi ∧
      ¬Fin15AnchoredAtom2011 chi ∧
      ¬Fin15AnchoredAtom2015 chi ∧
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
      ¬Fin15AnchoredAtom2640 chi ∧
      ¬Fin15AnchoredAtom2641 chi ∧
      ¬Fin15AnchoredAtom2644 chi ∧
      ¬Fin15AnchoredAtom2646 chi ∧
      ¬Fin15AnchoredAtom2649 chi ∧
      ¬Fin15AnchoredAtom2653 chi ∧
      ¬Fin15AnchoredAtom2661 chi ∧
      ¬Fin15AnchoredAtom2664 chi ∧
      ¬Fin15AnchoredAtom2668 chi ∧
      ¬Fin15AnchoredAtom2678 chi ∧
      ¬Fin15AnchoredAtom2752 chi ∧
      ¬Fin15AnchoredAtom2755 chi ∧
      ¬Fin15AnchoredAtom2759 chi ∧
      ¬Fin15AnchoredAtom2769 chi ∧
      ¬Fin15AnchoredAtom2789 chi ∧
      ¬Fin15AnchoredAtom3355 chi ∧
      ¬Fin15AnchoredAtom3356 chi ∧
      ¬Fin15AnchoredAtom3359 chi ∧
      ¬Fin15AnchoredAtom3361 chi ∧
      ¬Fin15AnchoredAtom3364 chi ∧
      ¬Fin15AnchoredAtom3368 chi ∧
      ¬Fin15AnchoredAtom3376 chi ∧
      ¬Fin15AnchoredAtom3379 chi ∧
      ¬Fin15AnchoredAtom3383 chi ∧
      ¬Fin15AnchoredAtom3393 chi ∧
      ¬Fin15AnchoredAtom3467 chi ∧
      ¬Fin15AnchoredAtom3470 chi ∧
      ¬Fin15AnchoredAtom3474 chi ∧
      ¬Fin15AnchoredAtom3484 chi ∧
      ¬Fin15AnchoredAtom3504 chi ∧
      ¬Fin15AnchoredAtom4628 chi ∧
      ¬Fin15AnchoredAtom4631 chi ∧
      ¬Fin15AnchoredAtom4635 chi ∧
      ¬Fin15AnchoredAtom4645 chi ∧
      ¬Fin15AnchoredAtom4665 chi ∧
      ¬Fin15AnchoredAtom4770 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 5, 7, 8, 9, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask10147
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1995 Fin15AnchoredAtom1996 Fin15AnchoredAtom1997
    Fin15AnchoredAtom2000 Fin15AnchoredAtom2002 Fin15AnchoredAtom2003 Fin15AnchoredAtom2006
    Fin15AnchoredAtom2008 Fin15AnchoredAtom2011 Fin15AnchoredAtom2015 Fin15AnchoredAtom2051
    Fin15AnchoredAtom2052 Fin15AnchoredAtom2055 Fin15AnchoredAtom2057 Fin15AnchoredAtom2060
    Fin15AnchoredAtom2064 Fin15AnchoredAtom2072 Fin15AnchoredAtom2075 Fin15AnchoredAtom2079
    Fin15AnchoredAtom2089 Fin15AnchoredAtom2640 Fin15AnchoredAtom2641 Fin15AnchoredAtom2644
    Fin15AnchoredAtom2646 Fin15AnchoredAtom2649 Fin15AnchoredAtom2653 Fin15AnchoredAtom2661
    Fin15AnchoredAtom2664 Fin15AnchoredAtom2668 Fin15AnchoredAtom2678 Fin15AnchoredAtom2752
    Fin15AnchoredAtom2755 Fin15AnchoredAtom2759 Fin15AnchoredAtom2769 Fin15AnchoredAtom2789
    Fin15AnchoredAtom3355 Fin15AnchoredAtom3356 Fin15AnchoredAtom3359 Fin15AnchoredAtom3361
    Fin15AnchoredAtom3364 Fin15AnchoredAtom3368 Fin15AnchoredAtom3376 Fin15AnchoredAtom3379
    Fin15AnchoredAtom3383 Fin15AnchoredAtom3393 Fin15AnchoredAtom3467 Fin15AnchoredAtom3470
    Fin15AnchoredAtom3474 Fin15AnchoredAtom3484 Fin15AnchoredAtom3504 Fin15AnchoredAtom4628
    Fin15AnchoredAtom4631 Fin15AnchoredAtom4635 Fin15AnchoredAtom4645 Fin15AnchoredAtom4665
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

theorem fin15Anchored_clause31085 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1995 chi ∧
      ¬Fin15AnchoredAtom1997 chi ∧
      ¬Fin15AnchoredAtom1999 chi ∧
      ¬Fin15AnchoredAtom2000 chi ∧
      ¬Fin15AnchoredAtom2003 chi ∧
      ¬Fin15AnchoredAtom2005 chi ∧
      ¬Fin15AnchoredAtom2006 chi ∧
      ¬Fin15AnchoredAtom2014 chi ∧
      ¬Fin15AnchoredAtom2015 chi ∧
      ¬Fin15AnchoredAtom2020 chi ∧
      ¬Fin15AnchoredAtom2052 chi ∧
      ¬Fin15AnchoredAtom2054 chi ∧
      ¬Fin15AnchoredAtom2055 chi ∧
      ¬Fin15AnchoredAtom2063 chi ∧
      ¬Fin15AnchoredAtom2064 chi ∧
      ¬Fin15AnchoredAtom2069 chi ∧
      ¬Fin15AnchoredAtom2078 chi ∧
      ¬Fin15AnchoredAtom2079 chi ∧
      ¬Fin15AnchoredAtom2084 chi ∧
      ¬Fin15AnchoredAtom2100 chi ∧
      ¬Fin15AnchoredAtom2641 chi ∧
      ¬Fin15AnchoredAtom2643 chi ∧
      ¬Fin15AnchoredAtom2644 chi ∧
      ¬Fin15AnchoredAtom2652 chi ∧
      ¬Fin15AnchoredAtom2653 chi ∧
      ¬Fin15AnchoredAtom2658 chi ∧
      ¬Fin15AnchoredAtom2667 chi ∧
      ¬Fin15AnchoredAtom2668 chi ∧
      ¬Fin15AnchoredAtom2673 chi ∧
      ¬Fin15AnchoredAtom2689 chi ∧
      ¬Fin15AnchoredAtom2758 chi ∧
      ¬Fin15AnchoredAtom2759 chi ∧
      ¬Fin15AnchoredAtom2764 chi ∧
      ¬Fin15AnchoredAtom2780 chi ∧
      ¬Fin15AnchoredAtom2800 chi ∧
      ¬Fin15AnchoredAtom3356 chi ∧
      ¬Fin15AnchoredAtom3358 chi ∧
      ¬Fin15AnchoredAtom3359 chi ∧
      ¬Fin15AnchoredAtom3367 chi ∧
      ¬Fin15AnchoredAtom3368 chi ∧
      ¬Fin15AnchoredAtom3373 chi ∧
      ¬Fin15AnchoredAtom3382 chi ∧
      ¬Fin15AnchoredAtom3383 chi ∧
      ¬Fin15AnchoredAtom3388 chi ∧
      ¬Fin15AnchoredAtom3404 chi ∧
      ¬Fin15AnchoredAtom3473 chi ∧
      ¬Fin15AnchoredAtom3474 chi ∧
      ¬Fin15AnchoredAtom3479 chi ∧
      ¬Fin15AnchoredAtom3495 chi ∧
      ¬Fin15AnchoredAtom3515 chi ∧
      ¬Fin15AnchoredAtom4634 chi ∧
      ¬Fin15AnchoredAtom4635 chi ∧
      ¬Fin15AnchoredAtom4640 chi ∧
      ¬Fin15AnchoredAtom4656 chi ∧
      ¬Fin15AnchoredAtom4676 chi ∧
      ¬Fin15AnchoredAtom4781 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 5, 7, 8, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13731
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1995 Fin15AnchoredAtom1997 Fin15AnchoredAtom1999
    Fin15AnchoredAtom2000 Fin15AnchoredAtom2003 Fin15AnchoredAtom2005 Fin15AnchoredAtom2006
    Fin15AnchoredAtom2014 Fin15AnchoredAtom2015 Fin15AnchoredAtom2020 Fin15AnchoredAtom2052
    Fin15AnchoredAtom2054 Fin15AnchoredAtom2055 Fin15AnchoredAtom2063 Fin15AnchoredAtom2064
    Fin15AnchoredAtom2069 Fin15AnchoredAtom2078 Fin15AnchoredAtom2079 Fin15AnchoredAtom2084
    Fin15AnchoredAtom2100 Fin15AnchoredAtom2641 Fin15AnchoredAtom2643 Fin15AnchoredAtom2644
    Fin15AnchoredAtom2652 Fin15AnchoredAtom2653 Fin15AnchoredAtom2658 Fin15AnchoredAtom2667
    Fin15AnchoredAtom2668 Fin15AnchoredAtom2673 Fin15AnchoredAtom2689 Fin15AnchoredAtom2758
    Fin15AnchoredAtom2759 Fin15AnchoredAtom2764 Fin15AnchoredAtom2780 Fin15AnchoredAtom2800
    Fin15AnchoredAtom3356 Fin15AnchoredAtom3358 Fin15AnchoredAtom3359 Fin15AnchoredAtom3367
    Fin15AnchoredAtom3368 Fin15AnchoredAtom3373 Fin15AnchoredAtom3382 Fin15AnchoredAtom3383
    Fin15AnchoredAtom3388 Fin15AnchoredAtom3404 Fin15AnchoredAtom3473 Fin15AnchoredAtom3474
    Fin15AnchoredAtom3479 Fin15AnchoredAtom3495 Fin15AnchoredAtom3515 Fin15AnchoredAtom4634
    Fin15AnchoredAtom4635 Fin15AnchoredAtom4640 Fin15AnchoredAtom4656 Fin15AnchoredAtom4676
    Fin15AnchoredAtom4781 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31086 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1995 chi ∧
      ¬Fin15AnchoredAtom1997 chi ∧
      ¬Fin15AnchoredAtom2000 chi ∧
      ¬Fin15AnchoredAtom2001 chi ∧
      ¬Fin15AnchoredAtom2003 chi ∧
      ¬Fin15AnchoredAtom2006 chi ∧
      ¬Fin15AnchoredAtom2007 chi ∧
      ¬Fin15AnchoredAtom2015 chi ∧
      ¬Fin15AnchoredAtom2016 chi ∧
      ¬Fin15AnchoredAtom2022 chi ∧
      ¬Fin15AnchoredAtom2052 chi ∧
      ¬Fin15AnchoredAtom2055 chi ∧
      ¬Fin15AnchoredAtom2056 chi ∧
      ¬Fin15AnchoredAtom2064 chi ∧
      ¬Fin15AnchoredAtom2065 chi ∧
      ¬Fin15AnchoredAtom2071 chi ∧
      ¬Fin15AnchoredAtom2079 chi ∧
      ¬Fin15AnchoredAtom2080 chi ∧
      ¬Fin15AnchoredAtom2086 chi ∧
      ¬Fin15AnchoredAtom2102 chi ∧
      ¬Fin15AnchoredAtom2641 chi ∧
      ¬Fin15AnchoredAtom2644 chi ∧
      ¬Fin15AnchoredAtom2645 chi ∧
      ¬Fin15AnchoredAtom2653 chi ∧
      ¬Fin15AnchoredAtom2654 chi ∧
      ¬Fin15AnchoredAtom2660 chi ∧
      ¬Fin15AnchoredAtom2668 chi ∧
      ¬Fin15AnchoredAtom2669 chi ∧
      ¬Fin15AnchoredAtom2675 chi ∧
      ¬Fin15AnchoredAtom2691 chi ∧
      ¬Fin15AnchoredAtom2759 chi ∧
      ¬Fin15AnchoredAtom2760 chi ∧
      ¬Fin15AnchoredAtom2766 chi ∧
      ¬Fin15AnchoredAtom2782 chi ∧
      ¬Fin15AnchoredAtom2802 chi ∧
      ¬Fin15AnchoredAtom3356 chi ∧
      ¬Fin15AnchoredAtom3359 chi ∧
      ¬Fin15AnchoredAtom3360 chi ∧
      ¬Fin15AnchoredAtom3368 chi ∧
      ¬Fin15AnchoredAtom3369 chi ∧
      ¬Fin15AnchoredAtom3375 chi ∧
      ¬Fin15AnchoredAtom3383 chi ∧
      ¬Fin15AnchoredAtom3384 chi ∧
      ¬Fin15AnchoredAtom3390 chi ∧
      ¬Fin15AnchoredAtom3406 chi ∧
      ¬Fin15AnchoredAtom3474 chi ∧
      ¬Fin15AnchoredAtom3475 chi ∧
      ¬Fin15AnchoredAtom3481 chi ∧
      ¬Fin15AnchoredAtom3497 chi ∧
      ¬Fin15AnchoredAtom3517 chi ∧
      ¬Fin15AnchoredAtom4635 chi ∧
      ¬Fin15AnchoredAtom4636 chi ∧
      ¬Fin15AnchoredAtom4642 chi ∧
      ¬Fin15AnchoredAtom4658 chi ∧
      ¬Fin15AnchoredAtom4678 chi ∧
      ¬Fin15AnchoredAtom4783 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 5, 7, 8, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26019
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1995 Fin15AnchoredAtom1997 Fin15AnchoredAtom2000
    Fin15AnchoredAtom2001 Fin15AnchoredAtom2003 Fin15AnchoredAtom2006 Fin15AnchoredAtom2007
    Fin15AnchoredAtom2015 Fin15AnchoredAtom2016 Fin15AnchoredAtom2022 Fin15AnchoredAtom2052
    Fin15AnchoredAtom2055 Fin15AnchoredAtom2056 Fin15AnchoredAtom2064 Fin15AnchoredAtom2065
    Fin15AnchoredAtom2071 Fin15AnchoredAtom2079 Fin15AnchoredAtom2080 Fin15AnchoredAtom2086
    Fin15AnchoredAtom2102 Fin15AnchoredAtom2641 Fin15AnchoredAtom2644 Fin15AnchoredAtom2645
    Fin15AnchoredAtom2653 Fin15AnchoredAtom2654 Fin15AnchoredAtom2660 Fin15AnchoredAtom2668
    Fin15AnchoredAtom2669 Fin15AnchoredAtom2675 Fin15AnchoredAtom2691 Fin15AnchoredAtom2759
    Fin15AnchoredAtom2760 Fin15AnchoredAtom2766 Fin15AnchoredAtom2782 Fin15AnchoredAtom2802
    Fin15AnchoredAtom3356 Fin15AnchoredAtom3359 Fin15AnchoredAtom3360 Fin15AnchoredAtom3368
    Fin15AnchoredAtom3369 Fin15AnchoredAtom3375 Fin15AnchoredAtom3383 Fin15AnchoredAtom3384
    Fin15AnchoredAtom3390 Fin15AnchoredAtom3406 Fin15AnchoredAtom3474 Fin15AnchoredAtom3475
    Fin15AnchoredAtom3481 Fin15AnchoredAtom3497 Fin15AnchoredAtom3517 Fin15AnchoredAtom4635
    Fin15AnchoredAtom4636 Fin15AnchoredAtom4642 Fin15AnchoredAtom4658 Fin15AnchoredAtom4678
    Fin15AnchoredAtom4783 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31087 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1996 chi ∧
      ¬Fin15AnchoredAtom1997 chi ∧
      ¬Fin15AnchoredAtom1999 chi ∧
      ¬Fin15AnchoredAtom2000 chi ∧
      ¬Fin15AnchoredAtom2008 chi ∧
      ¬Fin15AnchoredAtom2010 chi ∧
      ¬Fin15AnchoredAtom2011 chi ∧
      ¬Fin15AnchoredAtom2014 chi ∧
      ¬Fin15AnchoredAtom2015 chi ∧
      ¬Fin15AnchoredAtom2020 chi ∧
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
      ¬Fin15AnchoredAtom2646 chi ∧
      ¬Fin15AnchoredAtom2648 chi ∧
      ¬Fin15AnchoredAtom2649 chi ∧
      ¬Fin15AnchoredAtom2652 chi ∧
      ¬Fin15AnchoredAtom2653 chi ∧
      ¬Fin15AnchoredAtom2658 chi ∧
      ¬Fin15AnchoredAtom2677 chi ∧
      ¬Fin15AnchoredAtom2678 chi ∧
      ¬Fin15AnchoredAtom2683 chi ∧
      ¬Fin15AnchoredAtom2689 chi ∧
      ¬Fin15AnchoredAtom2768 chi ∧
      ¬Fin15AnchoredAtom2769 chi ∧
      ¬Fin15AnchoredAtom2774 chi ∧
      ¬Fin15AnchoredAtom2780 chi ∧
      ¬Fin15AnchoredAtom2810 chi ∧
      ¬Fin15AnchoredAtom3361 chi ∧
      ¬Fin15AnchoredAtom3363 chi ∧
      ¬Fin15AnchoredAtom3364 chi ∧
      ¬Fin15AnchoredAtom3367 chi ∧
      ¬Fin15AnchoredAtom3368 chi ∧
      ¬Fin15AnchoredAtom3373 chi ∧
      ¬Fin15AnchoredAtom3392 chi ∧
      ¬Fin15AnchoredAtom3393 chi ∧
      ¬Fin15AnchoredAtom3398 chi ∧
      ¬Fin15AnchoredAtom3404 chi ∧
      ¬Fin15AnchoredAtom3483 chi ∧
      ¬Fin15AnchoredAtom3484 chi ∧
      ¬Fin15AnchoredAtom3489 chi ∧
      ¬Fin15AnchoredAtom3495 chi ∧
      ¬Fin15AnchoredAtom3525 chi ∧
      ¬Fin15AnchoredAtom4644 chi ∧
      ¬Fin15AnchoredAtom4645 chi ∧
      ¬Fin15AnchoredAtom4650 chi ∧
      ¬Fin15AnchoredAtom4656 chi ∧
      ¬Fin15AnchoredAtom4686 chi ∧
      ¬Fin15AnchoredAtom4791 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 5, 7, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13987
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1996 Fin15AnchoredAtom1997 Fin15AnchoredAtom1999
    Fin15AnchoredAtom2000 Fin15AnchoredAtom2008 Fin15AnchoredAtom2010 Fin15AnchoredAtom2011
    Fin15AnchoredAtom2014 Fin15AnchoredAtom2015 Fin15AnchoredAtom2020 Fin15AnchoredAtom2057
    Fin15AnchoredAtom2059 Fin15AnchoredAtom2060 Fin15AnchoredAtom2063 Fin15AnchoredAtom2064
    Fin15AnchoredAtom2069 Fin15AnchoredAtom2088 Fin15AnchoredAtom2089 Fin15AnchoredAtom2094
    Fin15AnchoredAtom2100 Fin15AnchoredAtom2646 Fin15AnchoredAtom2648 Fin15AnchoredAtom2649
    Fin15AnchoredAtom2652 Fin15AnchoredAtom2653 Fin15AnchoredAtom2658 Fin15AnchoredAtom2677
    Fin15AnchoredAtom2678 Fin15AnchoredAtom2683 Fin15AnchoredAtom2689 Fin15AnchoredAtom2768
    Fin15AnchoredAtom2769 Fin15AnchoredAtom2774 Fin15AnchoredAtom2780 Fin15AnchoredAtom2810
    Fin15AnchoredAtom3361 Fin15AnchoredAtom3363 Fin15AnchoredAtom3364 Fin15AnchoredAtom3367
    Fin15AnchoredAtom3368 Fin15AnchoredAtom3373 Fin15AnchoredAtom3392 Fin15AnchoredAtom3393
    Fin15AnchoredAtom3398 Fin15AnchoredAtom3404 Fin15AnchoredAtom3483 Fin15AnchoredAtom3484
    Fin15AnchoredAtom3489 Fin15AnchoredAtom3495 Fin15AnchoredAtom3525 Fin15AnchoredAtom4644
    Fin15AnchoredAtom4645 Fin15AnchoredAtom4650 Fin15AnchoredAtom4656 Fin15AnchoredAtom4686
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

theorem fin15Anchored_clause31088 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1996 chi ∧
      ¬Fin15AnchoredAtom1997 chi ∧
      ¬Fin15AnchoredAtom1999 chi ∧
      ¬Fin15AnchoredAtom2001 chi ∧
      ¬Fin15AnchoredAtom2008 chi ∧
      ¬Fin15AnchoredAtom2010 chi ∧
      ¬Fin15AnchoredAtom2012 chi ∧
      ¬Fin15AnchoredAtom2014 chi ∧
      ¬Fin15AnchoredAtom2016 chi ∧
      ¬Fin15AnchoredAtom2021 chi ∧
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
      ¬Fin15AnchoredAtom2646 chi ∧
      ¬Fin15AnchoredAtom2648 chi ∧
      ¬Fin15AnchoredAtom2650 chi ∧
      ¬Fin15AnchoredAtom2652 chi ∧
      ¬Fin15AnchoredAtom2654 chi ∧
      ¬Fin15AnchoredAtom2659 chi ∧
      ¬Fin15AnchoredAtom2677 chi ∧
      ¬Fin15AnchoredAtom2679 chi ∧
      ¬Fin15AnchoredAtom2684 chi ∧
      ¬Fin15AnchoredAtom2690 chi ∧
      ¬Fin15AnchoredAtom2768 chi ∧
      ¬Fin15AnchoredAtom2770 chi ∧
      ¬Fin15AnchoredAtom2775 chi ∧
      ¬Fin15AnchoredAtom2781 chi ∧
      ¬Fin15AnchoredAtom2811 chi ∧
      ¬Fin15AnchoredAtom3361 chi ∧
      ¬Fin15AnchoredAtom3363 chi ∧
      ¬Fin15AnchoredAtom3365 chi ∧
      ¬Fin15AnchoredAtom3367 chi ∧
      ¬Fin15AnchoredAtom3369 chi ∧
      ¬Fin15AnchoredAtom3374 chi ∧
      ¬Fin15AnchoredAtom3392 chi ∧
      ¬Fin15AnchoredAtom3394 chi ∧
      ¬Fin15AnchoredAtom3399 chi ∧
      ¬Fin15AnchoredAtom3405 chi ∧
      ¬Fin15AnchoredAtom3483 chi ∧
      ¬Fin15AnchoredAtom3485 chi ∧
      ¬Fin15AnchoredAtom3490 chi ∧
      ¬Fin15AnchoredAtom3496 chi ∧
      ¬Fin15AnchoredAtom3526 chi ∧
      ¬Fin15AnchoredAtom4644 chi ∧
      ¬Fin15AnchoredAtom4646 chi ∧
      ¬Fin15AnchoredAtom4651 chi ∧
      ¬Fin15AnchoredAtom4657 chi ∧
      ¬Fin15AnchoredAtom4687 chi ∧
      ¬Fin15AnchoredAtom4792 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 5, 7, 9, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22179
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1996 Fin15AnchoredAtom1997 Fin15AnchoredAtom1999
    Fin15AnchoredAtom2001 Fin15AnchoredAtom2008 Fin15AnchoredAtom2010 Fin15AnchoredAtom2012
    Fin15AnchoredAtom2014 Fin15AnchoredAtom2016 Fin15AnchoredAtom2021 Fin15AnchoredAtom2057
    Fin15AnchoredAtom2059 Fin15AnchoredAtom2061 Fin15AnchoredAtom2063 Fin15AnchoredAtom2065
    Fin15AnchoredAtom2070 Fin15AnchoredAtom2088 Fin15AnchoredAtom2090 Fin15AnchoredAtom2095
    Fin15AnchoredAtom2101 Fin15AnchoredAtom2646 Fin15AnchoredAtom2648 Fin15AnchoredAtom2650
    Fin15AnchoredAtom2652 Fin15AnchoredAtom2654 Fin15AnchoredAtom2659 Fin15AnchoredAtom2677
    Fin15AnchoredAtom2679 Fin15AnchoredAtom2684 Fin15AnchoredAtom2690 Fin15AnchoredAtom2768
    Fin15AnchoredAtom2770 Fin15AnchoredAtom2775 Fin15AnchoredAtom2781 Fin15AnchoredAtom2811
    Fin15AnchoredAtom3361 Fin15AnchoredAtom3363 Fin15AnchoredAtom3365 Fin15AnchoredAtom3367
    Fin15AnchoredAtom3369 Fin15AnchoredAtom3374 Fin15AnchoredAtom3392 Fin15AnchoredAtom3394
    Fin15AnchoredAtom3399 Fin15AnchoredAtom3405 Fin15AnchoredAtom3483 Fin15AnchoredAtom3485
    Fin15AnchoredAtom3490 Fin15AnchoredAtom3496 Fin15AnchoredAtom3526 Fin15AnchoredAtom4644
    Fin15AnchoredAtom4646 Fin15AnchoredAtom4651 Fin15AnchoredAtom4657 Fin15AnchoredAtom4687
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

theorem fin15Anchored_clause31089 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1996 chi ∧
      ¬Fin15AnchoredAtom1997 chi ∧
      ¬Fin15AnchoredAtom2000 chi ∧
      ¬Fin15AnchoredAtom2001 chi ∧
      ¬Fin15AnchoredAtom2008 chi ∧
      ¬Fin15AnchoredAtom2011 chi ∧
      ¬Fin15AnchoredAtom2012 chi ∧
      ¬Fin15AnchoredAtom2015 chi ∧
      ¬Fin15AnchoredAtom2016 chi ∧
      ¬Fin15AnchoredAtom2022 chi ∧
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
      ¬Fin15AnchoredAtom2646 chi ∧
      ¬Fin15AnchoredAtom2649 chi ∧
      ¬Fin15AnchoredAtom2650 chi ∧
      ¬Fin15AnchoredAtom2653 chi ∧
      ¬Fin15AnchoredAtom2654 chi ∧
      ¬Fin15AnchoredAtom2660 chi ∧
      ¬Fin15AnchoredAtom2678 chi ∧
      ¬Fin15AnchoredAtom2679 chi ∧
      ¬Fin15AnchoredAtom2685 chi ∧
      ¬Fin15AnchoredAtom2691 chi ∧
      ¬Fin15AnchoredAtom2769 chi ∧
      ¬Fin15AnchoredAtom2770 chi ∧
      ¬Fin15AnchoredAtom2776 chi ∧
      ¬Fin15AnchoredAtom2782 chi ∧
      ¬Fin15AnchoredAtom2812 chi ∧
      ¬Fin15AnchoredAtom3361 chi ∧
      ¬Fin15AnchoredAtom3364 chi ∧
      ¬Fin15AnchoredAtom3365 chi ∧
      ¬Fin15AnchoredAtom3368 chi ∧
      ¬Fin15AnchoredAtom3369 chi ∧
      ¬Fin15AnchoredAtom3375 chi ∧
      ¬Fin15AnchoredAtom3393 chi ∧
      ¬Fin15AnchoredAtom3394 chi ∧
      ¬Fin15AnchoredAtom3400 chi ∧
      ¬Fin15AnchoredAtom3406 chi ∧
      ¬Fin15AnchoredAtom3484 chi ∧
      ¬Fin15AnchoredAtom3485 chi ∧
      ¬Fin15AnchoredAtom3491 chi ∧
      ¬Fin15AnchoredAtom3497 chi ∧
      ¬Fin15AnchoredAtom3527 chi ∧
      ¬Fin15AnchoredAtom4645 chi ∧
      ¬Fin15AnchoredAtom4646 chi ∧
      ¬Fin15AnchoredAtom4652 chi ∧
      ¬Fin15AnchoredAtom4658 chi ∧
      ¬Fin15AnchoredAtom4688 chi ∧
      ¬Fin15AnchoredAtom4793 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 5, 7, 9, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26275
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1996 Fin15AnchoredAtom1997 Fin15AnchoredAtom2000
    Fin15AnchoredAtom2001 Fin15AnchoredAtom2008 Fin15AnchoredAtom2011 Fin15AnchoredAtom2012
    Fin15AnchoredAtom2015 Fin15AnchoredAtom2016 Fin15AnchoredAtom2022 Fin15AnchoredAtom2057
    Fin15AnchoredAtom2060 Fin15AnchoredAtom2061 Fin15AnchoredAtom2064 Fin15AnchoredAtom2065
    Fin15AnchoredAtom2071 Fin15AnchoredAtom2089 Fin15AnchoredAtom2090 Fin15AnchoredAtom2096
    Fin15AnchoredAtom2102 Fin15AnchoredAtom2646 Fin15AnchoredAtom2649 Fin15AnchoredAtom2650
    Fin15AnchoredAtom2653 Fin15AnchoredAtom2654 Fin15AnchoredAtom2660 Fin15AnchoredAtom2678
    Fin15AnchoredAtom2679 Fin15AnchoredAtom2685 Fin15AnchoredAtom2691 Fin15AnchoredAtom2769
    Fin15AnchoredAtom2770 Fin15AnchoredAtom2776 Fin15AnchoredAtom2782 Fin15AnchoredAtom2812
    Fin15AnchoredAtom3361 Fin15AnchoredAtom3364 Fin15AnchoredAtom3365 Fin15AnchoredAtom3368
    Fin15AnchoredAtom3369 Fin15AnchoredAtom3375 Fin15AnchoredAtom3393 Fin15AnchoredAtom3394
    Fin15AnchoredAtom3400 Fin15AnchoredAtom3406 Fin15AnchoredAtom3484 Fin15AnchoredAtom3485
    Fin15AnchoredAtom3491 Fin15AnchoredAtom3497 Fin15AnchoredAtom3527 Fin15AnchoredAtom4645
    Fin15AnchoredAtom4646 Fin15AnchoredAtom4652 Fin15AnchoredAtom4658 Fin15AnchoredAtom4688
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

theorem fin15Anchored_clause31090 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1996 chi ∧
      ¬Fin15AnchoredAtom1999 chi ∧
      ¬Fin15AnchoredAtom2000 chi ∧
      ¬Fin15AnchoredAtom2001 chi ∧
      ¬Fin15AnchoredAtom2010 chi ∧
      ¬Fin15AnchoredAtom2011 chi ∧
      ¬Fin15AnchoredAtom2012 chi ∧
      ¬Fin15AnchoredAtom2020 chi ∧
      ¬Fin15AnchoredAtom2021 chi ∧
      ¬Fin15AnchoredAtom2022 chi ∧
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
      ¬Fin15AnchoredAtom2648 chi ∧
      ¬Fin15AnchoredAtom2649 chi ∧
      ¬Fin15AnchoredAtom2650 chi ∧
      ¬Fin15AnchoredAtom2658 chi ∧
      ¬Fin15AnchoredAtom2659 chi ∧
      ¬Fin15AnchoredAtom2660 chi ∧
      ¬Fin15AnchoredAtom2683 chi ∧
      ¬Fin15AnchoredAtom2684 chi ∧
      ¬Fin15AnchoredAtom2685 chi ∧
      ¬Fin15AnchoredAtom2695 chi ∧
      ¬Fin15AnchoredAtom2774 chi ∧
      ¬Fin15AnchoredAtom2775 chi ∧
      ¬Fin15AnchoredAtom2776 chi ∧
      ¬Fin15AnchoredAtom2786 chi ∧
      ¬Fin15AnchoredAtom2816 chi ∧
      ¬Fin15AnchoredAtom3363 chi ∧
      ¬Fin15AnchoredAtom3364 chi ∧
      ¬Fin15AnchoredAtom3365 chi ∧
      ¬Fin15AnchoredAtom3373 chi ∧
      ¬Fin15AnchoredAtom3374 chi ∧
      ¬Fin15AnchoredAtom3375 chi ∧
      ¬Fin15AnchoredAtom3398 chi ∧
      ¬Fin15AnchoredAtom3399 chi ∧
      ¬Fin15AnchoredAtom3400 chi ∧
      ¬Fin15AnchoredAtom3410 chi ∧
      ¬Fin15AnchoredAtom3489 chi ∧
      ¬Fin15AnchoredAtom3490 chi ∧
      ¬Fin15AnchoredAtom3491 chi ∧
      ¬Fin15AnchoredAtom3501 chi ∧
      ¬Fin15AnchoredAtom3531 chi ∧
      ¬Fin15AnchoredAtom4650 chi ∧
      ¬Fin15AnchoredAtom4651 chi ∧
      ¬Fin15AnchoredAtom4652 chi ∧
      ¬Fin15AnchoredAtom4662 chi ∧
      ¬Fin15AnchoredAtom4692 chi ∧
      ¬Fin15AnchoredAtom4797 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 5, 7, 9, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29347
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1996 Fin15AnchoredAtom1999 Fin15AnchoredAtom2000
    Fin15AnchoredAtom2001 Fin15AnchoredAtom2010 Fin15AnchoredAtom2011 Fin15AnchoredAtom2012
    Fin15AnchoredAtom2020 Fin15AnchoredAtom2021 Fin15AnchoredAtom2022 Fin15AnchoredAtom2059
    Fin15AnchoredAtom2060 Fin15AnchoredAtom2061 Fin15AnchoredAtom2069 Fin15AnchoredAtom2070
    Fin15AnchoredAtom2071 Fin15AnchoredAtom2094 Fin15AnchoredAtom2095 Fin15AnchoredAtom2096
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2648 Fin15AnchoredAtom2649 Fin15AnchoredAtom2650
    Fin15AnchoredAtom2658 Fin15AnchoredAtom2659 Fin15AnchoredAtom2660 Fin15AnchoredAtom2683
    Fin15AnchoredAtom2684 Fin15AnchoredAtom2685 Fin15AnchoredAtom2695 Fin15AnchoredAtom2774
    Fin15AnchoredAtom2775 Fin15AnchoredAtom2776 Fin15AnchoredAtom2786 Fin15AnchoredAtom2816
    Fin15AnchoredAtom3363 Fin15AnchoredAtom3364 Fin15AnchoredAtom3365 Fin15AnchoredAtom3373
    Fin15AnchoredAtom3374 Fin15AnchoredAtom3375 Fin15AnchoredAtom3398 Fin15AnchoredAtom3399
    Fin15AnchoredAtom3400 Fin15AnchoredAtom3410 Fin15AnchoredAtom3489 Fin15AnchoredAtom3490
    Fin15AnchoredAtom3491 Fin15AnchoredAtom3501 Fin15AnchoredAtom3531 Fin15AnchoredAtom4650
    Fin15AnchoredAtom4651 Fin15AnchoredAtom4652 Fin15AnchoredAtom4662 Fin15AnchoredAtom4692
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

theorem fin15Anchored_clause31091 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1997 chi ∧
      ¬Fin15AnchoredAtom1999 chi ∧
      ¬Fin15AnchoredAtom2000 chi ∧
      ¬Fin15AnchoredAtom2001 chi ∧
      ¬Fin15AnchoredAtom2014 chi ∧
      ¬Fin15AnchoredAtom2015 chi ∧
      ¬Fin15AnchoredAtom2016 chi ∧
      ¬Fin15AnchoredAtom2020 chi ∧
      ¬Fin15AnchoredAtom2021 chi ∧
      ¬Fin15AnchoredAtom2022 chi ∧
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
      ¬Fin15AnchoredAtom2652 chi ∧
      ¬Fin15AnchoredAtom2653 chi ∧
      ¬Fin15AnchoredAtom2654 chi ∧
      ¬Fin15AnchoredAtom2658 chi ∧
      ¬Fin15AnchoredAtom2659 chi ∧
      ¬Fin15AnchoredAtom2660 chi ∧
      ¬Fin15AnchoredAtom2689 chi ∧
      ¬Fin15AnchoredAtom2690 chi ∧
      ¬Fin15AnchoredAtom2691 chi ∧
      ¬Fin15AnchoredAtom2695 chi ∧
      ¬Fin15AnchoredAtom2780 chi ∧
      ¬Fin15AnchoredAtom2781 chi ∧
      ¬Fin15AnchoredAtom2782 chi ∧
      ¬Fin15AnchoredAtom2786 chi ∧
      ¬Fin15AnchoredAtom2820 chi ∧
      ¬Fin15AnchoredAtom3367 chi ∧
      ¬Fin15AnchoredAtom3368 chi ∧
      ¬Fin15AnchoredAtom3369 chi ∧
      ¬Fin15AnchoredAtom3373 chi ∧
      ¬Fin15AnchoredAtom3374 chi ∧
      ¬Fin15AnchoredAtom3375 chi ∧
      ¬Fin15AnchoredAtom3404 chi ∧
      ¬Fin15AnchoredAtom3405 chi ∧
      ¬Fin15AnchoredAtom3406 chi ∧
      ¬Fin15AnchoredAtom3410 chi ∧
      ¬Fin15AnchoredAtom3495 chi ∧
      ¬Fin15AnchoredAtom3496 chi ∧
      ¬Fin15AnchoredAtom3497 chi ∧
      ¬Fin15AnchoredAtom3501 chi ∧
      ¬Fin15AnchoredAtom3535 chi ∧
      ¬Fin15AnchoredAtom4656 chi ∧
      ¬Fin15AnchoredAtom4657 chi ∧
      ¬Fin15AnchoredAtom4658 chi ∧
      ¬Fin15AnchoredAtom4662 chi ∧
      ¬Fin15AnchoredAtom4696 chi ∧
      ¬Fin15AnchoredAtom4801 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 5, 7, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29859
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1997 Fin15AnchoredAtom1999 Fin15AnchoredAtom2000
    Fin15AnchoredAtom2001 Fin15AnchoredAtom2014 Fin15AnchoredAtom2015 Fin15AnchoredAtom2016
    Fin15AnchoredAtom2020 Fin15AnchoredAtom2021 Fin15AnchoredAtom2022 Fin15AnchoredAtom2063
    Fin15AnchoredAtom2064 Fin15AnchoredAtom2065 Fin15AnchoredAtom2069 Fin15AnchoredAtom2070
    Fin15AnchoredAtom2071 Fin15AnchoredAtom2100 Fin15AnchoredAtom2101 Fin15AnchoredAtom2102
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2652 Fin15AnchoredAtom2653 Fin15AnchoredAtom2654
    Fin15AnchoredAtom2658 Fin15AnchoredAtom2659 Fin15AnchoredAtom2660 Fin15AnchoredAtom2689
    Fin15AnchoredAtom2690 Fin15AnchoredAtom2691 Fin15AnchoredAtom2695 Fin15AnchoredAtom2780
    Fin15AnchoredAtom2781 Fin15AnchoredAtom2782 Fin15AnchoredAtom2786 Fin15AnchoredAtom2820
    Fin15AnchoredAtom3367 Fin15AnchoredAtom3368 Fin15AnchoredAtom3369 Fin15AnchoredAtom3373
    Fin15AnchoredAtom3374 Fin15AnchoredAtom3375 Fin15AnchoredAtom3404 Fin15AnchoredAtom3405
    Fin15AnchoredAtom3406 Fin15AnchoredAtom3410 Fin15AnchoredAtom3495 Fin15AnchoredAtom3496
    Fin15AnchoredAtom3497 Fin15AnchoredAtom3501 Fin15AnchoredAtom3535 Fin15AnchoredAtom4656
    Fin15AnchoredAtom4657 Fin15AnchoredAtom4658 Fin15AnchoredAtom4662 Fin15AnchoredAtom4696
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

theorem fin15Anchored_clause31092 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2002 chi ∧
      ¬Fin15AnchoredAtom2003 chi ∧
      ¬Fin15AnchoredAtom2005 chi ∧
      ¬Fin15AnchoredAtom2007 chi ∧
      ¬Fin15AnchoredAtom2008 chi ∧
      ¬Fin15AnchoredAtom2010 chi ∧
      ¬Fin15AnchoredAtom2012 chi ∧
      ¬Fin15AnchoredAtom2014 chi ∧
      ¬Fin15AnchoredAtom2016 chi ∧
      ¬Fin15AnchoredAtom2021 chi ∧
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
      ¬Fin15AnchoredAtom2661 chi ∧
      ¬Fin15AnchoredAtom2663 chi ∧
      ¬Fin15AnchoredAtom2665 chi ∧
      ¬Fin15AnchoredAtom2667 chi ∧
      ¬Fin15AnchoredAtom2669 chi ∧
      ¬Fin15AnchoredAtom2674 chi ∧
      ¬Fin15AnchoredAtom2677 chi ∧
      ¬Fin15AnchoredAtom2679 chi ∧
      ¬Fin15AnchoredAtom2684 chi ∧
      ¬Fin15AnchoredAtom2690 chi ∧
      ¬Fin15AnchoredAtom2788 chi ∧
      ¬Fin15AnchoredAtom2790 chi ∧
      ¬Fin15AnchoredAtom2795 chi ∧
      ¬Fin15AnchoredAtom2801 chi ∧
      ¬Fin15AnchoredAtom2811 chi ∧
      ¬Fin15AnchoredAtom3376 chi ∧
      ¬Fin15AnchoredAtom3378 chi ∧
      ¬Fin15AnchoredAtom3380 chi ∧
      ¬Fin15AnchoredAtom3382 chi ∧
      ¬Fin15AnchoredAtom3384 chi ∧
      ¬Fin15AnchoredAtom3389 chi ∧
      ¬Fin15AnchoredAtom3392 chi ∧
      ¬Fin15AnchoredAtom3394 chi ∧
      ¬Fin15AnchoredAtom3399 chi ∧
      ¬Fin15AnchoredAtom3405 chi ∧
      ¬Fin15AnchoredAtom3503 chi ∧
      ¬Fin15AnchoredAtom3505 chi ∧
      ¬Fin15AnchoredAtom3510 chi ∧
      ¬Fin15AnchoredAtom3516 chi ∧
      ¬Fin15AnchoredAtom3526 chi ∧
      ¬Fin15AnchoredAtom4664 chi ∧
      ¬Fin15AnchoredAtom4666 chi ∧
      ¬Fin15AnchoredAtom4671 chi ∧
      ¬Fin15AnchoredAtom4677 chi ∧
      ¬Fin15AnchoredAtom4687 chi ∧
      ¬Fin15AnchoredAtom4807 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 5, 8, 9, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22307
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2002 Fin15AnchoredAtom2003 Fin15AnchoredAtom2005
    Fin15AnchoredAtom2007 Fin15AnchoredAtom2008 Fin15AnchoredAtom2010 Fin15AnchoredAtom2012
    Fin15AnchoredAtom2014 Fin15AnchoredAtom2016 Fin15AnchoredAtom2021 Fin15AnchoredAtom2072
    Fin15AnchoredAtom2074 Fin15AnchoredAtom2076 Fin15AnchoredAtom2078 Fin15AnchoredAtom2080
    Fin15AnchoredAtom2085 Fin15AnchoredAtom2088 Fin15AnchoredAtom2090 Fin15AnchoredAtom2095
    Fin15AnchoredAtom2101 Fin15AnchoredAtom2661 Fin15AnchoredAtom2663 Fin15AnchoredAtom2665
    Fin15AnchoredAtom2667 Fin15AnchoredAtom2669 Fin15AnchoredAtom2674 Fin15AnchoredAtom2677
    Fin15AnchoredAtom2679 Fin15AnchoredAtom2684 Fin15AnchoredAtom2690 Fin15AnchoredAtom2788
    Fin15AnchoredAtom2790 Fin15AnchoredAtom2795 Fin15AnchoredAtom2801 Fin15AnchoredAtom2811
    Fin15AnchoredAtom3376 Fin15AnchoredAtom3378 Fin15AnchoredAtom3380 Fin15AnchoredAtom3382
    Fin15AnchoredAtom3384 Fin15AnchoredAtom3389 Fin15AnchoredAtom3392 Fin15AnchoredAtom3394
    Fin15AnchoredAtom3399 Fin15AnchoredAtom3405 Fin15AnchoredAtom3503 Fin15AnchoredAtom3505
    Fin15AnchoredAtom3510 Fin15AnchoredAtom3516 Fin15AnchoredAtom3526 Fin15AnchoredAtom4664
    Fin15AnchoredAtom4666 Fin15AnchoredAtom4671 Fin15AnchoredAtom4677 Fin15AnchoredAtom4687
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

theorem fin15Anchored_clause31093 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2003 chi ∧
      ¬Fin15AnchoredAtom2005 chi ∧
      ¬Fin15AnchoredAtom2006 chi ∧
      ¬Fin15AnchoredAtom2007 chi ∧
      ¬Fin15AnchoredAtom2014 chi ∧
      ¬Fin15AnchoredAtom2015 chi ∧
      ¬Fin15AnchoredAtom2016 chi ∧
      ¬Fin15AnchoredAtom2020 chi ∧
      ¬Fin15AnchoredAtom2021 chi ∧
      ¬Fin15AnchoredAtom2022 chi ∧
      ¬Fin15AnchoredAtom2078 chi ∧
      ¬Fin15AnchoredAtom2079 chi ∧
      ¬Fin15AnchoredAtom2080 chi ∧
      ¬Fin15AnchoredAtom2084 chi ∧
      ¬Fin15AnchoredAtom2085 chi ∧
      ¬Fin15AnchoredAtom2086 chi ∧
      ¬Fin15AnchoredAtom2100 chi ∧
      ¬Fin15AnchoredAtom2101 chi ∧
      ¬Fin15AnchoredAtom2102 chi ∧
      ¬Fin15AnchoredAtom2106 chi ∧
      ¬Fin15AnchoredAtom2667 chi ∧
      ¬Fin15AnchoredAtom2668 chi ∧
      ¬Fin15AnchoredAtom2669 chi ∧
      ¬Fin15AnchoredAtom2673 chi ∧
      ¬Fin15AnchoredAtom2674 chi ∧
      ¬Fin15AnchoredAtom2675 chi ∧
      ¬Fin15AnchoredAtom2689 chi ∧
      ¬Fin15AnchoredAtom2690 chi ∧
      ¬Fin15AnchoredAtom2691 chi ∧
      ¬Fin15AnchoredAtom2695 chi ∧
      ¬Fin15AnchoredAtom2800 chi ∧
      ¬Fin15AnchoredAtom2801 chi ∧
      ¬Fin15AnchoredAtom2802 chi ∧
      ¬Fin15AnchoredAtom2806 chi ∧
      ¬Fin15AnchoredAtom2820 chi ∧
      ¬Fin15AnchoredAtom3382 chi ∧
      ¬Fin15AnchoredAtom3383 chi ∧
      ¬Fin15AnchoredAtom3384 chi ∧
      ¬Fin15AnchoredAtom3388 chi ∧
      ¬Fin15AnchoredAtom3389 chi ∧
      ¬Fin15AnchoredAtom3390 chi ∧
      ¬Fin15AnchoredAtom3404 chi ∧
      ¬Fin15AnchoredAtom3405 chi ∧
      ¬Fin15AnchoredAtom3406 chi ∧
      ¬Fin15AnchoredAtom3410 chi ∧
      ¬Fin15AnchoredAtom3515 chi ∧
      ¬Fin15AnchoredAtom3516 chi ∧
      ¬Fin15AnchoredAtom3517 chi ∧
      ¬Fin15AnchoredAtom3521 chi ∧
      ¬Fin15AnchoredAtom3535 chi ∧
      ¬Fin15AnchoredAtom4676 chi ∧
      ¬Fin15AnchoredAtom4677 chi ∧
      ¬Fin15AnchoredAtom4678 chi ∧
      ¬Fin15AnchoredAtom4682 chi ∧
      ¬Fin15AnchoredAtom4696 chi ∧
      ¬Fin15AnchoredAtom4816 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 5, 8, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29987
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2003 Fin15AnchoredAtom2005 Fin15AnchoredAtom2006
    Fin15AnchoredAtom2007 Fin15AnchoredAtom2014 Fin15AnchoredAtom2015 Fin15AnchoredAtom2016
    Fin15AnchoredAtom2020 Fin15AnchoredAtom2021 Fin15AnchoredAtom2022 Fin15AnchoredAtom2078
    Fin15AnchoredAtom2079 Fin15AnchoredAtom2080 Fin15AnchoredAtom2084 Fin15AnchoredAtom2085
    Fin15AnchoredAtom2086 Fin15AnchoredAtom2100 Fin15AnchoredAtom2101 Fin15AnchoredAtom2102
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2667 Fin15AnchoredAtom2668 Fin15AnchoredAtom2669
    Fin15AnchoredAtom2673 Fin15AnchoredAtom2674 Fin15AnchoredAtom2675 Fin15AnchoredAtom2689
    Fin15AnchoredAtom2690 Fin15AnchoredAtom2691 Fin15AnchoredAtom2695 Fin15AnchoredAtom2800
    Fin15AnchoredAtom2801 Fin15AnchoredAtom2802 Fin15AnchoredAtom2806 Fin15AnchoredAtom2820
    Fin15AnchoredAtom3382 Fin15AnchoredAtom3383 Fin15AnchoredAtom3384 Fin15AnchoredAtom3388
    Fin15AnchoredAtom3389 Fin15AnchoredAtom3390 Fin15AnchoredAtom3404 Fin15AnchoredAtom3405
    Fin15AnchoredAtom3406 Fin15AnchoredAtom3410 Fin15AnchoredAtom3515 Fin15AnchoredAtom3516
    Fin15AnchoredAtom3517 Fin15AnchoredAtom3521 Fin15AnchoredAtom3535 Fin15AnchoredAtom4676
    Fin15AnchoredAtom4677 Fin15AnchoredAtom4678 Fin15AnchoredAtom4682 Fin15AnchoredAtom4696
    Fin15AnchoredAtom4816 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31094 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2008 chi ∧
      ¬Fin15AnchoredAtom2010 chi ∧
      ¬Fin15AnchoredAtom2011 chi ∧
      ¬Fin15AnchoredAtom2012 chi ∧
      ¬Fin15AnchoredAtom2014 chi ∧
      ¬Fin15AnchoredAtom2015 chi ∧
      ¬Fin15AnchoredAtom2016 chi ∧
      ¬Fin15AnchoredAtom2020 chi ∧
      ¬Fin15AnchoredAtom2021 chi ∧
      ¬Fin15AnchoredAtom2022 chi ∧
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
      ¬Fin15AnchoredAtom2677 chi ∧
      ¬Fin15AnchoredAtom2678 chi ∧
      ¬Fin15AnchoredAtom2679 chi ∧
      ¬Fin15AnchoredAtom2683 chi ∧
      ¬Fin15AnchoredAtom2684 chi ∧
      ¬Fin15AnchoredAtom2685 chi ∧
      ¬Fin15AnchoredAtom2689 chi ∧
      ¬Fin15AnchoredAtom2690 chi ∧
      ¬Fin15AnchoredAtom2691 chi ∧
      ¬Fin15AnchoredAtom2695 chi ∧
      ¬Fin15AnchoredAtom2810 chi ∧
      ¬Fin15AnchoredAtom2811 chi ∧
      ¬Fin15AnchoredAtom2812 chi ∧
      ¬Fin15AnchoredAtom2816 chi ∧
      ¬Fin15AnchoredAtom2820 chi ∧
      ¬Fin15AnchoredAtom3392 chi ∧
      ¬Fin15AnchoredAtom3393 chi ∧
      ¬Fin15AnchoredAtom3394 chi ∧
      ¬Fin15AnchoredAtom3398 chi ∧
      ¬Fin15AnchoredAtom3399 chi ∧
      ¬Fin15AnchoredAtom3400 chi ∧
      ¬Fin15AnchoredAtom3404 chi ∧
      ¬Fin15AnchoredAtom3405 chi ∧
      ¬Fin15AnchoredAtom3406 chi ∧
      ¬Fin15AnchoredAtom3410 chi ∧
      ¬Fin15AnchoredAtom3525 chi ∧
      ¬Fin15AnchoredAtom3526 chi ∧
      ¬Fin15AnchoredAtom3527 chi ∧
      ¬Fin15AnchoredAtom3531 chi ∧
      ¬Fin15AnchoredAtom3535 chi ∧
      ¬Fin15AnchoredAtom4686 chi ∧
      ¬Fin15AnchoredAtom4687 chi ∧
      ¬Fin15AnchoredAtom4688 chi ∧
      ¬Fin15AnchoredAtom4692 chi ∧
      ¬Fin15AnchoredAtom4696 chi ∧
      ¬Fin15AnchoredAtom4821 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 5, 9, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask30243
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2008 Fin15AnchoredAtom2010 Fin15AnchoredAtom2011
    Fin15AnchoredAtom2012 Fin15AnchoredAtom2014 Fin15AnchoredAtom2015 Fin15AnchoredAtom2016
    Fin15AnchoredAtom2020 Fin15AnchoredAtom2021 Fin15AnchoredAtom2022 Fin15AnchoredAtom2088
    Fin15AnchoredAtom2089 Fin15AnchoredAtom2090 Fin15AnchoredAtom2094 Fin15AnchoredAtom2095
    Fin15AnchoredAtom2096 Fin15AnchoredAtom2100 Fin15AnchoredAtom2101 Fin15AnchoredAtom2102
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2677 Fin15AnchoredAtom2678 Fin15AnchoredAtom2679
    Fin15AnchoredAtom2683 Fin15AnchoredAtom2684 Fin15AnchoredAtom2685 Fin15AnchoredAtom2689
    Fin15AnchoredAtom2690 Fin15AnchoredAtom2691 Fin15AnchoredAtom2695 Fin15AnchoredAtom2810
    Fin15AnchoredAtom2811 Fin15AnchoredAtom2812 Fin15AnchoredAtom2816 Fin15AnchoredAtom2820
    Fin15AnchoredAtom3392 Fin15AnchoredAtom3393 Fin15AnchoredAtom3394 Fin15AnchoredAtom3398
    Fin15AnchoredAtom3399 Fin15AnchoredAtom3400 Fin15AnchoredAtom3404 Fin15AnchoredAtom3405
    Fin15AnchoredAtom3406 Fin15AnchoredAtom3410 Fin15AnchoredAtom3525 Fin15AnchoredAtom3526
    Fin15AnchoredAtom3527 Fin15AnchoredAtom3531 Fin15AnchoredAtom3535 Fin15AnchoredAtom4686
    Fin15AnchoredAtom4687 Fin15AnchoredAtom4688 Fin15AnchoredAtom4692 Fin15AnchoredAtom4696
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

theorem fin15Anchored_clause31095 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2023 chi ∧
      ¬Fin15AnchoredAtom2024 chi ∧
      ¬Fin15AnchoredAtom2025 chi ∧
      ¬Fin15AnchoredAtom2027 chi ∧
      ¬Fin15AnchoredAtom2030 chi ∧
      ¬Fin15AnchoredAtom2031 chi ∧
      ¬Fin15AnchoredAtom2033 chi ∧
      ¬Fin15AnchoredAtom2036 chi ∧
      ¬Fin15AnchoredAtom2038 chi ∧
      ¬Fin15AnchoredAtom2042 chi ∧
      ¬Fin15AnchoredAtom2051 chi ∧
      ¬Fin15AnchoredAtom2052 chi ∧
      ¬Fin15AnchoredAtom2054 chi ∧
      ¬Fin15AnchoredAtom2057 chi ∧
      ¬Fin15AnchoredAtom2059 chi ∧
      ¬Fin15AnchoredAtom2063 chi ∧
      ¬Fin15AnchoredAtom2072 chi ∧
      ¬Fin15AnchoredAtom2074 chi ∧
      ¬Fin15AnchoredAtom2078 chi ∧
      ¬Fin15AnchoredAtom2088 chi ∧
      ¬Fin15AnchoredAtom2696 chi ∧
      ¬Fin15AnchoredAtom2697 chi ∧
      ¬Fin15AnchoredAtom2699 chi ∧
      ¬Fin15AnchoredAtom2702 chi ∧
      ¬Fin15AnchoredAtom2704 chi ∧
      ¬Fin15AnchoredAtom2708 chi ∧
      ¬Fin15AnchoredAtom2717 chi ∧
      ¬Fin15AnchoredAtom2719 chi ∧
      ¬Fin15AnchoredAtom2723 chi ∧
      ¬Fin15AnchoredAtom2733 chi ∧
      ¬Fin15AnchoredAtom2752 chi ∧
      ¬Fin15AnchoredAtom2754 chi ∧
      ¬Fin15AnchoredAtom2758 chi ∧
      ¬Fin15AnchoredAtom2768 chi ∧
      ¬Fin15AnchoredAtom2788 chi ∧
      ¬Fin15AnchoredAtom3411 chi ∧
      ¬Fin15AnchoredAtom3412 chi ∧
      ¬Fin15AnchoredAtom3414 chi ∧
      ¬Fin15AnchoredAtom3417 chi ∧
      ¬Fin15AnchoredAtom3419 chi ∧
      ¬Fin15AnchoredAtom3423 chi ∧
      ¬Fin15AnchoredAtom3432 chi ∧
      ¬Fin15AnchoredAtom3434 chi ∧
      ¬Fin15AnchoredAtom3438 chi ∧
      ¬Fin15AnchoredAtom3448 chi ∧
      ¬Fin15AnchoredAtom3467 chi ∧
      ¬Fin15AnchoredAtom3469 chi ∧
      ¬Fin15AnchoredAtom3473 chi ∧
      ¬Fin15AnchoredAtom3483 chi ∧
      ¬Fin15AnchoredAtom3503 chi ∧
      ¬Fin15AnchoredAtom4698 chi ∧
      ¬Fin15AnchoredAtom4700 chi ∧
      ¬Fin15AnchoredAtom4704 chi ∧
      ¬Fin15AnchoredAtom4714 chi ∧
      ¬Fin15AnchoredAtom4734 chi ∧
      ¬Fin15AnchoredAtom4769 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 6, 7, 8, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask06083
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2023 Fin15AnchoredAtom2024 Fin15AnchoredAtom2025
    Fin15AnchoredAtom2027 Fin15AnchoredAtom2030 Fin15AnchoredAtom2031 Fin15AnchoredAtom2033
    Fin15AnchoredAtom2036 Fin15AnchoredAtom2038 Fin15AnchoredAtom2042 Fin15AnchoredAtom2051
    Fin15AnchoredAtom2052 Fin15AnchoredAtom2054 Fin15AnchoredAtom2057 Fin15AnchoredAtom2059
    Fin15AnchoredAtom2063 Fin15AnchoredAtom2072 Fin15AnchoredAtom2074 Fin15AnchoredAtom2078
    Fin15AnchoredAtom2088 Fin15AnchoredAtom2696 Fin15AnchoredAtom2697 Fin15AnchoredAtom2699
    Fin15AnchoredAtom2702 Fin15AnchoredAtom2704 Fin15AnchoredAtom2708 Fin15AnchoredAtom2717
    Fin15AnchoredAtom2719 Fin15AnchoredAtom2723 Fin15AnchoredAtom2733 Fin15AnchoredAtom2752
    Fin15AnchoredAtom2754 Fin15AnchoredAtom2758 Fin15AnchoredAtom2768 Fin15AnchoredAtom2788
    Fin15AnchoredAtom3411 Fin15AnchoredAtom3412 Fin15AnchoredAtom3414 Fin15AnchoredAtom3417
    Fin15AnchoredAtom3419 Fin15AnchoredAtom3423 Fin15AnchoredAtom3432 Fin15AnchoredAtom3434
    Fin15AnchoredAtom3438 Fin15AnchoredAtom3448 Fin15AnchoredAtom3467 Fin15AnchoredAtom3469
    Fin15AnchoredAtom3473 Fin15AnchoredAtom3483 Fin15AnchoredAtom3503 Fin15AnchoredAtom4698
    Fin15AnchoredAtom4700 Fin15AnchoredAtom4704 Fin15AnchoredAtom4714 Fin15AnchoredAtom4734
    Fin15AnchoredAtom4769 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31096 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2023 chi ∧
      ¬Fin15AnchoredAtom2024 chi ∧
      ¬Fin15AnchoredAtom2025 chi ∧
      ¬Fin15AnchoredAtom2028 chi ∧
      ¬Fin15AnchoredAtom2030 chi ∧
      ¬Fin15AnchoredAtom2031 chi ∧
      ¬Fin15AnchoredAtom2034 chi ∧
      ¬Fin15AnchoredAtom2036 chi ∧
      ¬Fin15AnchoredAtom2039 chi ∧
      ¬Fin15AnchoredAtom2043 chi ∧
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
      ¬Fin15AnchoredAtom2696 chi ∧
      ¬Fin15AnchoredAtom2697 chi ∧
      ¬Fin15AnchoredAtom2700 chi ∧
      ¬Fin15AnchoredAtom2702 chi ∧
      ¬Fin15AnchoredAtom2705 chi ∧
      ¬Fin15AnchoredAtom2709 chi ∧
      ¬Fin15AnchoredAtom2717 chi ∧
      ¬Fin15AnchoredAtom2720 chi ∧
      ¬Fin15AnchoredAtom2724 chi ∧
      ¬Fin15AnchoredAtom2734 chi ∧
      ¬Fin15AnchoredAtom2752 chi ∧
      ¬Fin15AnchoredAtom2755 chi ∧
      ¬Fin15AnchoredAtom2759 chi ∧
      ¬Fin15AnchoredAtom2769 chi ∧
      ¬Fin15AnchoredAtom2789 chi ∧
      ¬Fin15AnchoredAtom3411 chi ∧
      ¬Fin15AnchoredAtom3412 chi ∧
      ¬Fin15AnchoredAtom3415 chi ∧
      ¬Fin15AnchoredAtom3417 chi ∧
      ¬Fin15AnchoredAtom3420 chi ∧
      ¬Fin15AnchoredAtom3424 chi ∧
      ¬Fin15AnchoredAtom3432 chi ∧
      ¬Fin15AnchoredAtom3435 chi ∧
      ¬Fin15AnchoredAtom3439 chi ∧
      ¬Fin15AnchoredAtom3449 chi ∧
      ¬Fin15AnchoredAtom3467 chi ∧
      ¬Fin15AnchoredAtom3470 chi ∧
      ¬Fin15AnchoredAtom3474 chi ∧
      ¬Fin15AnchoredAtom3484 chi ∧
      ¬Fin15AnchoredAtom3504 chi ∧
      ¬Fin15AnchoredAtom4698 chi ∧
      ¬Fin15AnchoredAtom4701 chi ∧
      ¬Fin15AnchoredAtom4705 chi ∧
      ¬Fin15AnchoredAtom4715 chi ∧
      ¬Fin15AnchoredAtom4735 chi ∧
      ¬Fin15AnchoredAtom4770 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 6, 7, 8, 9, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask10179
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2023 Fin15AnchoredAtom2024 Fin15AnchoredAtom2025
    Fin15AnchoredAtom2028 Fin15AnchoredAtom2030 Fin15AnchoredAtom2031 Fin15AnchoredAtom2034
    Fin15AnchoredAtom2036 Fin15AnchoredAtom2039 Fin15AnchoredAtom2043 Fin15AnchoredAtom2051
    Fin15AnchoredAtom2052 Fin15AnchoredAtom2055 Fin15AnchoredAtom2057 Fin15AnchoredAtom2060
    Fin15AnchoredAtom2064 Fin15AnchoredAtom2072 Fin15AnchoredAtom2075 Fin15AnchoredAtom2079
    Fin15AnchoredAtom2089 Fin15AnchoredAtom2696 Fin15AnchoredAtom2697 Fin15AnchoredAtom2700
    Fin15AnchoredAtom2702 Fin15AnchoredAtom2705 Fin15AnchoredAtom2709 Fin15AnchoredAtom2717
    Fin15AnchoredAtom2720 Fin15AnchoredAtom2724 Fin15AnchoredAtom2734 Fin15AnchoredAtom2752
    Fin15AnchoredAtom2755 Fin15AnchoredAtom2759 Fin15AnchoredAtom2769 Fin15AnchoredAtom2789
    Fin15AnchoredAtom3411 Fin15AnchoredAtom3412 Fin15AnchoredAtom3415 Fin15AnchoredAtom3417
    Fin15AnchoredAtom3420 Fin15AnchoredAtom3424 Fin15AnchoredAtom3432 Fin15AnchoredAtom3435
    Fin15AnchoredAtom3439 Fin15AnchoredAtom3449 Fin15AnchoredAtom3467 Fin15AnchoredAtom3470
    Fin15AnchoredAtom3474 Fin15AnchoredAtom3484 Fin15AnchoredAtom3504 Fin15AnchoredAtom4698
    Fin15AnchoredAtom4701 Fin15AnchoredAtom4705 Fin15AnchoredAtom4715 Fin15AnchoredAtom4735
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

theorem fin15Anchored_clause31097 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2023 chi ∧
      ¬Fin15AnchoredAtom2024 chi ∧
      ¬Fin15AnchoredAtom2025 chi ∧
      ¬Fin15AnchoredAtom2029 chi ∧
      ¬Fin15AnchoredAtom2030 chi ∧
      ¬Fin15AnchoredAtom2031 chi ∧
      ¬Fin15AnchoredAtom2035 chi ∧
      ¬Fin15AnchoredAtom2036 chi ∧
      ¬Fin15AnchoredAtom2040 chi ∧
      ¬Fin15AnchoredAtom2044 chi ∧
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
      ¬Fin15AnchoredAtom2696 chi ∧
      ¬Fin15AnchoredAtom2697 chi ∧
      ¬Fin15AnchoredAtom2701 chi ∧
      ¬Fin15AnchoredAtom2702 chi ∧
      ¬Fin15AnchoredAtom2706 chi ∧
      ¬Fin15AnchoredAtom2710 chi ∧
      ¬Fin15AnchoredAtom2717 chi ∧
      ¬Fin15AnchoredAtom2721 chi ∧
      ¬Fin15AnchoredAtom2725 chi ∧
      ¬Fin15AnchoredAtom2735 chi ∧
      ¬Fin15AnchoredAtom2752 chi ∧
      ¬Fin15AnchoredAtom2756 chi ∧
      ¬Fin15AnchoredAtom2760 chi ∧
      ¬Fin15AnchoredAtom2770 chi ∧
      ¬Fin15AnchoredAtom2790 chi ∧
      ¬Fin15AnchoredAtom3411 chi ∧
      ¬Fin15AnchoredAtom3412 chi ∧
      ¬Fin15AnchoredAtom3416 chi ∧
      ¬Fin15AnchoredAtom3417 chi ∧
      ¬Fin15AnchoredAtom3421 chi ∧
      ¬Fin15AnchoredAtom3425 chi ∧
      ¬Fin15AnchoredAtom3432 chi ∧
      ¬Fin15AnchoredAtom3436 chi ∧
      ¬Fin15AnchoredAtom3440 chi ∧
      ¬Fin15AnchoredAtom3450 chi ∧
      ¬Fin15AnchoredAtom3467 chi ∧
      ¬Fin15AnchoredAtom3471 chi ∧
      ¬Fin15AnchoredAtom3475 chi ∧
      ¬Fin15AnchoredAtom3485 chi ∧
      ¬Fin15AnchoredAtom3505 chi ∧
      ¬Fin15AnchoredAtom4698 chi ∧
      ¬Fin15AnchoredAtom4702 chi ∧
      ¬Fin15AnchoredAtom4706 chi ∧
      ¬Fin15AnchoredAtom4716 chi ∧
      ¬Fin15AnchoredAtom4736 chi ∧
      ¬Fin15AnchoredAtom4771 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 6, 7, 8, 9, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask18371
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2023 Fin15AnchoredAtom2024 Fin15AnchoredAtom2025
    Fin15AnchoredAtom2029 Fin15AnchoredAtom2030 Fin15AnchoredAtom2031 Fin15AnchoredAtom2035
    Fin15AnchoredAtom2036 Fin15AnchoredAtom2040 Fin15AnchoredAtom2044 Fin15AnchoredAtom2051
    Fin15AnchoredAtom2052 Fin15AnchoredAtom2056 Fin15AnchoredAtom2057 Fin15AnchoredAtom2061
    Fin15AnchoredAtom2065 Fin15AnchoredAtom2072 Fin15AnchoredAtom2076 Fin15AnchoredAtom2080
    Fin15AnchoredAtom2090 Fin15AnchoredAtom2696 Fin15AnchoredAtom2697 Fin15AnchoredAtom2701
    Fin15AnchoredAtom2702 Fin15AnchoredAtom2706 Fin15AnchoredAtom2710 Fin15AnchoredAtom2717
    Fin15AnchoredAtom2721 Fin15AnchoredAtom2725 Fin15AnchoredAtom2735 Fin15AnchoredAtom2752
    Fin15AnchoredAtom2756 Fin15AnchoredAtom2760 Fin15AnchoredAtom2770 Fin15AnchoredAtom2790
    Fin15AnchoredAtom3411 Fin15AnchoredAtom3412 Fin15AnchoredAtom3416 Fin15AnchoredAtom3417
    Fin15AnchoredAtom3421 Fin15AnchoredAtom3425 Fin15AnchoredAtom3432 Fin15AnchoredAtom3436
    Fin15AnchoredAtom3440 Fin15AnchoredAtom3450 Fin15AnchoredAtom3467 Fin15AnchoredAtom3471
    Fin15AnchoredAtom3475 Fin15AnchoredAtom3485 Fin15AnchoredAtom3505 Fin15AnchoredAtom4698
    Fin15AnchoredAtom4702 Fin15AnchoredAtom4706 Fin15AnchoredAtom4716 Fin15AnchoredAtom4736
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

theorem fin15Anchored_clause31098 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2023 chi ∧
      ¬Fin15AnchoredAtom2024 chi ∧
      ¬Fin15AnchoredAtom2027 chi ∧
      ¬Fin15AnchoredAtom2028 chi ∧
      ¬Fin15AnchoredAtom2030 chi ∧
      ¬Fin15AnchoredAtom2033 chi ∧
      ¬Fin15AnchoredAtom2034 chi ∧
      ¬Fin15AnchoredAtom2038 chi ∧
      ¬Fin15AnchoredAtom2039 chi ∧
      ¬Fin15AnchoredAtom2048 chi ∧
      ¬Fin15AnchoredAtom2051 chi ∧
      ¬Fin15AnchoredAtom2054 chi ∧
      ¬Fin15AnchoredAtom2055 chi ∧
      ¬Fin15AnchoredAtom2059 chi ∧
      ¬Fin15AnchoredAtom2060 chi ∧
      ¬Fin15AnchoredAtom2069 chi ∧
      ¬Fin15AnchoredAtom2074 chi ∧
      ¬Fin15AnchoredAtom2075 chi ∧
      ¬Fin15AnchoredAtom2084 chi ∧
      ¬Fin15AnchoredAtom2094 chi ∧
      ¬Fin15AnchoredAtom2696 chi ∧
      ¬Fin15AnchoredAtom2699 chi ∧
      ¬Fin15AnchoredAtom2700 chi ∧
      ¬Fin15AnchoredAtom2704 chi ∧
      ¬Fin15AnchoredAtom2705 chi ∧
      ¬Fin15AnchoredAtom2714 chi ∧
      ¬Fin15AnchoredAtom2719 chi ∧
      ¬Fin15AnchoredAtom2720 chi ∧
      ¬Fin15AnchoredAtom2729 chi ∧
      ¬Fin15AnchoredAtom2739 chi ∧
      ¬Fin15AnchoredAtom2754 chi ∧
      ¬Fin15AnchoredAtom2755 chi ∧
      ¬Fin15AnchoredAtom2764 chi ∧
      ¬Fin15AnchoredAtom2774 chi ∧
      ¬Fin15AnchoredAtom2794 chi ∧
      ¬Fin15AnchoredAtom3411 chi ∧
      ¬Fin15AnchoredAtom3414 chi ∧
      ¬Fin15AnchoredAtom3415 chi ∧
      ¬Fin15AnchoredAtom3419 chi ∧
      ¬Fin15AnchoredAtom3420 chi ∧
      ¬Fin15AnchoredAtom3429 chi ∧
      ¬Fin15AnchoredAtom3434 chi ∧
      ¬Fin15AnchoredAtom3435 chi ∧
      ¬Fin15AnchoredAtom3444 chi ∧
      ¬Fin15AnchoredAtom3454 chi ∧
      ¬Fin15AnchoredAtom3469 chi ∧
      ¬Fin15AnchoredAtom3470 chi ∧
      ¬Fin15AnchoredAtom3479 chi ∧
      ¬Fin15AnchoredAtom3489 chi ∧
      ¬Fin15AnchoredAtom3509 chi ∧
      ¬Fin15AnchoredAtom4700 chi ∧
      ¬Fin15AnchoredAtom4701 chi ∧
      ¬Fin15AnchoredAtom4710 chi ∧
      ¬Fin15AnchoredAtom4720 chi ∧
      ¬Fin15AnchoredAtom4740 chi ∧
      ¬Fin15AnchoredAtom4775 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 6, 7, 8, 9, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13251
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2023 Fin15AnchoredAtom2024 Fin15AnchoredAtom2027
    Fin15AnchoredAtom2028 Fin15AnchoredAtom2030 Fin15AnchoredAtom2033 Fin15AnchoredAtom2034
    Fin15AnchoredAtom2038 Fin15AnchoredAtom2039 Fin15AnchoredAtom2048 Fin15AnchoredAtom2051
    Fin15AnchoredAtom2054 Fin15AnchoredAtom2055 Fin15AnchoredAtom2059 Fin15AnchoredAtom2060
    Fin15AnchoredAtom2069 Fin15AnchoredAtom2074 Fin15AnchoredAtom2075 Fin15AnchoredAtom2084
    Fin15AnchoredAtom2094 Fin15AnchoredAtom2696 Fin15AnchoredAtom2699 Fin15AnchoredAtom2700
    Fin15AnchoredAtom2704 Fin15AnchoredAtom2705 Fin15AnchoredAtom2714 Fin15AnchoredAtom2719
    Fin15AnchoredAtom2720 Fin15AnchoredAtom2729 Fin15AnchoredAtom2739 Fin15AnchoredAtom2754
    Fin15AnchoredAtom2755 Fin15AnchoredAtom2764 Fin15AnchoredAtom2774 Fin15AnchoredAtom2794
    Fin15AnchoredAtom3411 Fin15AnchoredAtom3414 Fin15AnchoredAtom3415 Fin15AnchoredAtom3419
    Fin15AnchoredAtom3420 Fin15AnchoredAtom3429 Fin15AnchoredAtom3434 Fin15AnchoredAtom3435
    Fin15AnchoredAtom3444 Fin15AnchoredAtom3454 Fin15AnchoredAtom3469 Fin15AnchoredAtom3470
    Fin15AnchoredAtom3479 Fin15AnchoredAtom3489 Fin15AnchoredAtom3509 Fin15AnchoredAtom4700
    Fin15AnchoredAtom4701 Fin15AnchoredAtom4710 Fin15AnchoredAtom4720 Fin15AnchoredAtom4740
    Fin15AnchoredAtom4775 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31099 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2023 chi ∧
      ¬Fin15AnchoredAtom2024 chi ∧
      ¬Fin15AnchoredAtom2027 chi ∧
      ¬Fin15AnchoredAtom2029 chi ∧
      ¬Fin15AnchoredAtom2030 chi ∧
      ¬Fin15AnchoredAtom2033 chi ∧
      ¬Fin15AnchoredAtom2035 chi ∧
      ¬Fin15AnchoredAtom2038 chi ∧
      ¬Fin15AnchoredAtom2040 chi ∧
      ¬Fin15AnchoredAtom2049 chi ∧
      ¬Fin15AnchoredAtom2051 chi ∧
      ¬Fin15AnchoredAtom2054 chi ∧
      ¬Fin15AnchoredAtom2056 chi ∧
      ¬Fin15AnchoredAtom2059 chi ∧
      ¬Fin15AnchoredAtom2061 chi ∧
      ¬Fin15AnchoredAtom2070 chi ∧
      ¬Fin15AnchoredAtom2074 chi ∧
      ¬Fin15AnchoredAtom2076 chi ∧
      ¬Fin15AnchoredAtom2085 chi ∧
      ¬Fin15AnchoredAtom2095 chi ∧
      ¬Fin15AnchoredAtom2696 chi ∧
      ¬Fin15AnchoredAtom2699 chi ∧
      ¬Fin15AnchoredAtom2701 chi ∧
      ¬Fin15AnchoredAtom2704 chi ∧
      ¬Fin15AnchoredAtom2706 chi ∧
      ¬Fin15AnchoredAtom2715 chi ∧
      ¬Fin15AnchoredAtom2719 chi ∧
      ¬Fin15AnchoredAtom2721 chi ∧
      ¬Fin15AnchoredAtom2730 chi ∧
      ¬Fin15AnchoredAtom2740 chi ∧
      ¬Fin15AnchoredAtom2754 chi ∧
      ¬Fin15AnchoredAtom2756 chi ∧
      ¬Fin15AnchoredAtom2765 chi ∧
      ¬Fin15AnchoredAtom2775 chi ∧
      ¬Fin15AnchoredAtom2795 chi ∧
      ¬Fin15AnchoredAtom3411 chi ∧
      ¬Fin15AnchoredAtom3414 chi ∧
      ¬Fin15AnchoredAtom3416 chi ∧
      ¬Fin15AnchoredAtom3419 chi ∧
      ¬Fin15AnchoredAtom3421 chi ∧
      ¬Fin15AnchoredAtom3430 chi ∧
      ¬Fin15AnchoredAtom3434 chi ∧
      ¬Fin15AnchoredAtom3436 chi ∧
      ¬Fin15AnchoredAtom3445 chi ∧
      ¬Fin15AnchoredAtom3455 chi ∧
      ¬Fin15AnchoredAtom3469 chi ∧
      ¬Fin15AnchoredAtom3471 chi ∧
      ¬Fin15AnchoredAtom3480 chi ∧
      ¬Fin15AnchoredAtom3490 chi ∧
      ¬Fin15AnchoredAtom3510 chi ∧
      ¬Fin15AnchoredAtom4700 chi ∧
      ¬Fin15AnchoredAtom4702 chi ∧
      ¬Fin15AnchoredAtom4711 chi ∧
      ¬Fin15AnchoredAtom4721 chi ∧
      ¬Fin15AnchoredAtom4741 chi ∧
      ¬Fin15AnchoredAtom4776 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 6, 7, 8, 9, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21443
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2023 Fin15AnchoredAtom2024 Fin15AnchoredAtom2027
    Fin15AnchoredAtom2029 Fin15AnchoredAtom2030 Fin15AnchoredAtom2033 Fin15AnchoredAtom2035
    Fin15AnchoredAtom2038 Fin15AnchoredAtom2040 Fin15AnchoredAtom2049 Fin15AnchoredAtom2051
    Fin15AnchoredAtom2054 Fin15AnchoredAtom2056 Fin15AnchoredAtom2059 Fin15AnchoredAtom2061
    Fin15AnchoredAtom2070 Fin15AnchoredAtom2074 Fin15AnchoredAtom2076 Fin15AnchoredAtom2085
    Fin15AnchoredAtom2095 Fin15AnchoredAtom2696 Fin15AnchoredAtom2699 Fin15AnchoredAtom2701
    Fin15AnchoredAtom2704 Fin15AnchoredAtom2706 Fin15AnchoredAtom2715 Fin15AnchoredAtom2719
    Fin15AnchoredAtom2721 Fin15AnchoredAtom2730 Fin15AnchoredAtom2740 Fin15AnchoredAtom2754
    Fin15AnchoredAtom2756 Fin15AnchoredAtom2765 Fin15AnchoredAtom2775 Fin15AnchoredAtom2795
    Fin15AnchoredAtom3411 Fin15AnchoredAtom3414 Fin15AnchoredAtom3416 Fin15AnchoredAtom3419
    Fin15AnchoredAtom3421 Fin15AnchoredAtom3430 Fin15AnchoredAtom3434 Fin15AnchoredAtom3436
    Fin15AnchoredAtom3445 Fin15AnchoredAtom3455 Fin15AnchoredAtom3469 Fin15AnchoredAtom3471
    Fin15AnchoredAtom3480 Fin15AnchoredAtom3490 Fin15AnchoredAtom3510 Fin15AnchoredAtom4700
    Fin15AnchoredAtom4702 Fin15AnchoredAtom4711 Fin15AnchoredAtom4721 Fin15AnchoredAtom4741
    Fin15AnchoredAtom4776 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31100 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2023 chi ∧
      ¬Fin15AnchoredAtom2024 chi ∧
      ¬Fin15AnchoredAtom2028 chi ∧
      ¬Fin15AnchoredAtom2029 chi ∧
      ¬Fin15AnchoredAtom2030 chi ∧
      ¬Fin15AnchoredAtom2034 chi ∧
      ¬Fin15AnchoredAtom2035 chi ∧
      ¬Fin15AnchoredAtom2039 chi ∧
      ¬Fin15AnchoredAtom2040 chi ∧
      ¬Fin15AnchoredAtom2050 chi ∧
      ¬Fin15AnchoredAtom2051 chi ∧
      ¬Fin15AnchoredAtom2055 chi ∧
      ¬Fin15AnchoredAtom2056 chi ∧
      ¬Fin15AnchoredAtom2060 chi ∧
      ¬Fin15AnchoredAtom2061 chi ∧
      ¬Fin15AnchoredAtom2071 chi ∧
      ¬Fin15AnchoredAtom2075 chi ∧
      ¬Fin15AnchoredAtom2076 chi ∧
      ¬Fin15AnchoredAtom2086 chi ∧
      ¬Fin15AnchoredAtom2096 chi ∧
      ¬Fin15AnchoredAtom2696 chi ∧
      ¬Fin15AnchoredAtom2700 chi ∧
      ¬Fin15AnchoredAtom2701 chi ∧
      ¬Fin15AnchoredAtom2705 chi ∧
      ¬Fin15AnchoredAtom2706 chi ∧
      ¬Fin15AnchoredAtom2716 chi ∧
      ¬Fin15AnchoredAtom2720 chi ∧
      ¬Fin15AnchoredAtom2721 chi ∧
      ¬Fin15AnchoredAtom2731 chi ∧
      ¬Fin15AnchoredAtom2741 chi ∧
      ¬Fin15AnchoredAtom2755 chi ∧
      ¬Fin15AnchoredAtom2756 chi ∧
      ¬Fin15AnchoredAtom2766 chi ∧
      ¬Fin15AnchoredAtom2776 chi ∧
      ¬Fin15AnchoredAtom2796 chi ∧
      ¬Fin15AnchoredAtom3411 chi ∧
      ¬Fin15AnchoredAtom3415 chi ∧
      ¬Fin15AnchoredAtom3416 chi ∧
      ¬Fin15AnchoredAtom3420 chi ∧
      ¬Fin15AnchoredAtom3421 chi ∧
      ¬Fin15AnchoredAtom3431 chi ∧
      ¬Fin15AnchoredAtom3435 chi ∧
      ¬Fin15AnchoredAtom3436 chi ∧
      ¬Fin15AnchoredAtom3446 chi ∧
      ¬Fin15AnchoredAtom3456 chi ∧
      ¬Fin15AnchoredAtom3470 chi ∧
      ¬Fin15AnchoredAtom3471 chi ∧
      ¬Fin15AnchoredAtom3481 chi ∧
      ¬Fin15AnchoredAtom3491 chi ∧
      ¬Fin15AnchoredAtom3511 chi ∧
      ¬Fin15AnchoredAtom4701 chi ∧
      ¬Fin15AnchoredAtom4702 chi ∧
      ¬Fin15AnchoredAtom4712 chi ∧
      ¬Fin15AnchoredAtom4722 chi ∧
      ¬Fin15AnchoredAtom4742 chi ∧
      ¬Fin15AnchoredAtom4777 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 6, 7, 8, 9, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25539
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2023 Fin15AnchoredAtom2024 Fin15AnchoredAtom2028
    Fin15AnchoredAtom2029 Fin15AnchoredAtom2030 Fin15AnchoredAtom2034 Fin15AnchoredAtom2035
    Fin15AnchoredAtom2039 Fin15AnchoredAtom2040 Fin15AnchoredAtom2050 Fin15AnchoredAtom2051
    Fin15AnchoredAtom2055 Fin15AnchoredAtom2056 Fin15AnchoredAtom2060 Fin15AnchoredAtom2061
    Fin15AnchoredAtom2071 Fin15AnchoredAtom2075 Fin15AnchoredAtom2076 Fin15AnchoredAtom2086
    Fin15AnchoredAtom2096 Fin15AnchoredAtom2696 Fin15AnchoredAtom2700 Fin15AnchoredAtom2701
    Fin15AnchoredAtom2705 Fin15AnchoredAtom2706 Fin15AnchoredAtom2716 Fin15AnchoredAtom2720
    Fin15AnchoredAtom2721 Fin15AnchoredAtom2731 Fin15AnchoredAtom2741 Fin15AnchoredAtom2755
    Fin15AnchoredAtom2756 Fin15AnchoredAtom2766 Fin15AnchoredAtom2776 Fin15AnchoredAtom2796
    Fin15AnchoredAtom3411 Fin15AnchoredAtom3415 Fin15AnchoredAtom3416 Fin15AnchoredAtom3420
    Fin15AnchoredAtom3421 Fin15AnchoredAtom3431 Fin15AnchoredAtom3435 Fin15AnchoredAtom3436
    Fin15AnchoredAtom3446 Fin15AnchoredAtom3456 Fin15AnchoredAtom3470 Fin15AnchoredAtom3471
    Fin15AnchoredAtom3481 Fin15AnchoredAtom3491 Fin15AnchoredAtom3511 Fin15AnchoredAtom4701
    Fin15AnchoredAtom4702 Fin15AnchoredAtom4712 Fin15AnchoredAtom4722 Fin15AnchoredAtom4742
    Fin15AnchoredAtom4777 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31101 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2023 chi ∧
      ¬Fin15AnchoredAtom2025 chi ∧
      ¬Fin15AnchoredAtom2027 chi ∧
      ¬Fin15AnchoredAtom2028 chi ∧
      ¬Fin15AnchoredAtom2031 chi ∧
      ¬Fin15AnchoredAtom2033 chi ∧
      ¬Fin15AnchoredAtom2034 chi ∧
      ¬Fin15AnchoredAtom2042 chi ∧
      ¬Fin15AnchoredAtom2043 chi ∧
      ¬Fin15AnchoredAtom2048 chi ∧
      ¬Fin15AnchoredAtom2052 chi ∧
      ¬Fin15AnchoredAtom2054 chi ∧
      ¬Fin15AnchoredAtom2055 chi ∧
      ¬Fin15AnchoredAtom2063 chi ∧
      ¬Fin15AnchoredAtom2064 chi ∧
      ¬Fin15AnchoredAtom2069 chi ∧
      ¬Fin15AnchoredAtom2078 chi ∧
      ¬Fin15AnchoredAtom2079 chi ∧
      ¬Fin15AnchoredAtom2084 chi ∧
      ¬Fin15AnchoredAtom2100 chi ∧
      ¬Fin15AnchoredAtom2697 chi ∧
      ¬Fin15AnchoredAtom2699 chi ∧
      ¬Fin15AnchoredAtom2700 chi ∧
      ¬Fin15AnchoredAtom2708 chi ∧
      ¬Fin15AnchoredAtom2709 chi ∧
      ¬Fin15AnchoredAtom2714 chi ∧
      ¬Fin15AnchoredAtom2723 chi ∧
      ¬Fin15AnchoredAtom2724 chi ∧
      ¬Fin15AnchoredAtom2729 chi ∧
      ¬Fin15AnchoredAtom2745 chi ∧
      ¬Fin15AnchoredAtom2758 chi ∧
      ¬Fin15AnchoredAtom2759 chi ∧
      ¬Fin15AnchoredAtom2764 chi ∧
      ¬Fin15AnchoredAtom2780 chi ∧
      ¬Fin15AnchoredAtom2800 chi ∧
      ¬Fin15AnchoredAtom3412 chi ∧
      ¬Fin15AnchoredAtom3414 chi ∧
      ¬Fin15AnchoredAtom3415 chi ∧
      ¬Fin15AnchoredAtom3423 chi ∧
      ¬Fin15AnchoredAtom3424 chi ∧
      ¬Fin15AnchoredAtom3429 chi ∧
      ¬Fin15AnchoredAtom3438 chi ∧
      ¬Fin15AnchoredAtom3439 chi ∧
      ¬Fin15AnchoredAtom3444 chi ∧
      ¬Fin15AnchoredAtom3460 chi ∧
      ¬Fin15AnchoredAtom3473 chi ∧
      ¬Fin15AnchoredAtom3474 chi ∧
      ¬Fin15AnchoredAtom3479 chi ∧
      ¬Fin15AnchoredAtom3495 chi ∧
      ¬Fin15AnchoredAtom3515 chi ∧
      ¬Fin15AnchoredAtom4704 chi ∧
      ¬Fin15AnchoredAtom4705 chi ∧
      ¬Fin15AnchoredAtom4710 chi ∧
      ¬Fin15AnchoredAtom4726 chi ∧
      ¬Fin15AnchoredAtom4746 chi ∧
      ¬Fin15AnchoredAtom4781 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 6, 7, 8, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13763
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2023 Fin15AnchoredAtom2025 Fin15AnchoredAtom2027
    Fin15AnchoredAtom2028 Fin15AnchoredAtom2031 Fin15AnchoredAtom2033 Fin15AnchoredAtom2034
    Fin15AnchoredAtom2042 Fin15AnchoredAtom2043 Fin15AnchoredAtom2048 Fin15AnchoredAtom2052
    Fin15AnchoredAtom2054 Fin15AnchoredAtom2055 Fin15AnchoredAtom2063 Fin15AnchoredAtom2064
    Fin15AnchoredAtom2069 Fin15AnchoredAtom2078 Fin15AnchoredAtom2079 Fin15AnchoredAtom2084
    Fin15AnchoredAtom2100 Fin15AnchoredAtom2697 Fin15AnchoredAtom2699 Fin15AnchoredAtom2700
    Fin15AnchoredAtom2708 Fin15AnchoredAtom2709 Fin15AnchoredAtom2714 Fin15AnchoredAtom2723
    Fin15AnchoredAtom2724 Fin15AnchoredAtom2729 Fin15AnchoredAtom2745 Fin15AnchoredAtom2758
    Fin15AnchoredAtom2759 Fin15AnchoredAtom2764 Fin15AnchoredAtom2780 Fin15AnchoredAtom2800
    Fin15AnchoredAtom3412 Fin15AnchoredAtom3414 Fin15AnchoredAtom3415 Fin15AnchoredAtom3423
    Fin15AnchoredAtom3424 Fin15AnchoredAtom3429 Fin15AnchoredAtom3438 Fin15AnchoredAtom3439
    Fin15AnchoredAtom3444 Fin15AnchoredAtom3460 Fin15AnchoredAtom3473 Fin15AnchoredAtom3474
    Fin15AnchoredAtom3479 Fin15AnchoredAtom3495 Fin15AnchoredAtom3515 Fin15AnchoredAtom4704
    Fin15AnchoredAtom4705 Fin15AnchoredAtom4710 Fin15AnchoredAtom4726 Fin15AnchoredAtom4746
    Fin15AnchoredAtom4781 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31102 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2023 chi ∧
      ¬Fin15AnchoredAtom2027 chi ∧
      ¬Fin15AnchoredAtom2028 chi ∧
      ¬Fin15AnchoredAtom2029 chi ∧
      ¬Fin15AnchoredAtom2033 chi ∧
      ¬Fin15AnchoredAtom2034 chi ∧
      ¬Fin15AnchoredAtom2035 chi ∧
      ¬Fin15AnchoredAtom2048 chi ∧
      ¬Fin15AnchoredAtom2049 chi ∧
      ¬Fin15AnchoredAtom2050 chi ∧
      ¬Fin15AnchoredAtom2054 chi ∧
      ¬Fin15AnchoredAtom2055 chi ∧
      ¬Fin15AnchoredAtom2056 chi ∧
      ¬Fin15AnchoredAtom2069 chi ∧
      ¬Fin15AnchoredAtom2070 chi ∧
      ¬Fin15AnchoredAtom2071 chi ∧
      ¬Fin15AnchoredAtom2084 chi ∧
      ¬Fin15AnchoredAtom2085 chi ∧
      ¬Fin15AnchoredAtom2086 chi ∧
      ¬Fin15AnchoredAtom2106 chi ∧
      ¬Fin15AnchoredAtom2699 chi ∧
      ¬Fin15AnchoredAtom2700 chi ∧
      ¬Fin15AnchoredAtom2701 chi ∧
      ¬Fin15AnchoredAtom2714 chi ∧
      ¬Fin15AnchoredAtom2715 chi ∧
      ¬Fin15AnchoredAtom2716 chi ∧
      ¬Fin15AnchoredAtom2729 chi ∧
      ¬Fin15AnchoredAtom2730 chi ∧
      ¬Fin15AnchoredAtom2731 chi ∧
      ¬Fin15AnchoredAtom2751 chi ∧
      ¬Fin15AnchoredAtom2764 chi ∧
      ¬Fin15AnchoredAtom2765 chi ∧
      ¬Fin15AnchoredAtom2766 chi ∧
      ¬Fin15AnchoredAtom2786 chi ∧
      ¬Fin15AnchoredAtom2806 chi ∧
      ¬Fin15AnchoredAtom3414 chi ∧
      ¬Fin15AnchoredAtom3415 chi ∧
      ¬Fin15AnchoredAtom3416 chi ∧
      ¬Fin15AnchoredAtom3429 chi ∧
      ¬Fin15AnchoredAtom3430 chi ∧
      ¬Fin15AnchoredAtom3431 chi ∧
      ¬Fin15AnchoredAtom3444 chi ∧
      ¬Fin15AnchoredAtom3445 chi ∧
      ¬Fin15AnchoredAtom3446 chi ∧
      ¬Fin15AnchoredAtom3466 chi ∧
      ¬Fin15AnchoredAtom3479 chi ∧
      ¬Fin15AnchoredAtom3480 chi ∧
      ¬Fin15AnchoredAtom3481 chi ∧
      ¬Fin15AnchoredAtom3501 chi ∧
      ¬Fin15AnchoredAtom3521 chi ∧
      ¬Fin15AnchoredAtom4710 chi ∧
      ¬Fin15AnchoredAtom4711 chi ∧
      ¬Fin15AnchoredAtom4712 chi ∧
      ¬Fin15AnchoredAtom4732 chi ∧
      ¬Fin15AnchoredAtom4752 chi ∧
      ¬Fin15AnchoredAtom4787 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 6, 7, 8, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29123
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2023 Fin15AnchoredAtom2027 Fin15AnchoredAtom2028
    Fin15AnchoredAtom2029 Fin15AnchoredAtom2033 Fin15AnchoredAtom2034 Fin15AnchoredAtom2035
    Fin15AnchoredAtom2048 Fin15AnchoredAtom2049 Fin15AnchoredAtom2050 Fin15AnchoredAtom2054
    Fin15AnchoredAtom2055 Fin15AnchoredAtom2056 Fin15AnchoredAtom2069 Fin15AnchoredAtom2070
    Fin15AnchoredAtom2071 Fin15AnchoredAtom2084 Fin15AnchoredAtom2085 Fin15AnchoredAtom2086
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2699 Fin15AnchoredAtom2700 Fin15AnchoredAtom2701
    Fin15AnchoredAtom2714 Fin15AnchoredAtom2715 Fin15AnchoredAtom2716 Fin15AnchoredAtom2729
    Fin15AnchoredAtom2730 Fin15AnchoredAtom2731 Fin15AnchoredAtom2751 Fin15AnchoredAtom2764
    Fin15AnchoredAtom2765 Fin15AnchoredAtom2766 Fin15AnchoredAtom2786 Fin15AnchoredAtom2806
    Fin15AnchoredAtom3414 Fin15AnchoredAtom3415 Fin15AnchoredAtom3416 Fin15AnchoredAtom3429
    Fin15AnchoredAtom3430 Fin15AnchoredAtom3431 Fin15AnchoredAtom3444 Fin15AnchoredAtom3445
    Fin15AnchoredAtom3446 Fin15AnchoredAtom3466 Fin15AnchoredAtom3479 Fin15AnchoredAtom3480
    Fin15AnchoredAtom3481 Fin15AnchoredAtom3501 Fin15AnchoredAtom3521 Fin15AnchoredAtom4710
    Fin15AnchoredAtom4711 Fin15AnchoredAtom4712 Fin15AnchoredAtom4732 Fin15AnchoredAtom4752
    Fin15AnchoredAtom4787 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31103 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2024 chi ∧
      ¬Fin15AnchoredAtom2025 chi ∧
      ¬Fin15AnchoredAtom2027 chi ∧
      ¬Fin15AnchoredAtom2028 chi ∧
      ¬Fin15AnchoredAtom2036 chi ∧
      ¬Fin15AnchoredAtom2038 chi ∧
      ¬Fin15AnchoredAtom2039 chi ∧
      ¬Fin15AnchoredAtom2042 chi ∧
      ¬Fin15AnchoredAtom2043 chi ∧
      ¬Fin15AnchoredAtom2048 chi ∧
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
      ¬Fin15AnchoredAtom2702 chi ∧
      ¬Fin15AnchoredAtom2704 chi ∧
      ¬Fin15AnchoredAtom2705 chi ∧
      ¬Fin15AnchoredAtom2708 chi ∧
      ¬Fin15AnchoredAtom2709 chi ∧
      ¬Fin15AnchoredAtom2714 chi ∧
      ¬Fin15AnchoredAtom2733 chi ∧
      ¬Fin15AnchoredAtom2734 chi ∧
      ¬Fin15AnchoredAtom2739 chi ∧
      ¬Fin15AnchoredAtom2745 chi ∧
      ¬Fin15AnchoredAtom2768 chi ∧
      ¬Fin15AnchoredAtom2769 chi ∧
      ¬Fin15AnchoredAtom2774 chi ∧
      ¬Fin15AnchoredAtom2780 chi ∧
      ¬Fin15AnchoredAtom2810 chi ∧
      ¬Fin15AnchoredAtom3417 chi ∧
      ¬Fin15AnchoredAtom3419 chi ∧
      ¬Fin15AnchoredAtom3420 chi ∧
      ¬Fin15AnchoredAtom3423 chi ∧
      ¬Fin15AnchoredAtom3424 chi ∧
      ¬Fin15AnchoredAtom3429 chi ∧
      ¬Fin15AnchoredAtom3448 chi ∧
      ¬Fin15AnchoredAtom3449 chi ∧
      ¬Fin15AnchoredAtom3454 chi ∧
      ¬Fin15AnchoredAtom3460 chi ∧
      ¬Fin15AnchoredAtom3483 chi ∧
      ¬Fin15AnchoredAtom3484 chi ∧
      ¬Fin15AnchoredAtom3489 chi ∧
      ¬Fin15AnchoredAtom3495 chi ∧
      ¬Fin15AnchoredAtom3525 chi ∧
      ¬Fin15AnchoredAtom4714 chi ∧
      ¬Fin15AnchoredAtom4715 chi ∧
      ¬Fin15AnchoredAtom4720 chi ∧
      ¬Fin15AnchoredAtom4726 chi ∧
      ¬Fin15AnchoredAtom4756 chi ∧
      ¬Fin15AnchoredAtom4791 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 6, 7, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask14019
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2024 Fin15AnchoredAtom2025 Fin15AnchoredAtom2027
    Fin15AnchoredAtom2028 Fin15AnchoredAtom2036 Fin15AnchoredAtom2038 Fin15AnchoredAtom2039
    Fin15AnchoredAtom2042 Fin15AnchoredAtom2043 Fin15AnchoredAtom2048 Fin15AnchoredAtom2057
    Fin15AnchoredAtom2059 Fin15AnchoredAtom2060 Fin15AnchoredAtom2063 Fin15AnchoredAtom2064
    Fin15AnchoredAtom2069 Fin15AnchoredAtom2088 Fin15AnchoredAtom2089 Fin15AnchoredAtom2094
    Fin15AnchoredAtom2100 Fin15AnchoredAtom2702 Fin15AnchoredAtom2704 Fin15AnchoredAtom2705
    Fin15AnchoredAtom2708 Fin15AnchoredAtom2709 Fin15AnchoredAtom2714 Fin15AnchoredAtom2733
    Fin15AnchoredAtom2734 Fin15AnchoredAtom2739 Fin15AnchoredAtom2745 Fin15AnchoredAtom2768
    Fin15AnchoredAtom2769 Fin15AnchoredAtom2774 Fin15AnchoredAtom2780 Fin15AnchoredAtom2810
    Fin15AnchoredAtom3417 Fin15AnchoredAtom3419 Fin15AnchoredAtom3420 Fin15AnchoredAtom3423
    Fin15AnchoredAtom3424 Fin15AnchoredAtom3429 Fin15AnchoredAtom3448 Fin15AnchoredAtom3449
    Fin15AnchoredAtom3454 Fin15AnchoredAtom3460 Fin15AnchoredAtom3483 Fin15AnchoredAtom3484
    Fin15AnchoredAtom3489 Fin15AnchoredAtom3495 Fin15AnchoredAtom3525 Fin15AnchoredAtom4714
    Fin15AnchoredAtom4715 Fin15AnchoredAtom4720 Fin15AnchoredAtom4726 Fin15AnchoredAtom4756
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

end ErdosSzekeres

end
