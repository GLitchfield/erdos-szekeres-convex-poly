module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 246. -/

theorem fin15Anchored_clause31488 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2380 chi ∧
      ¬Fin15AnchoredAtom2382 chi ∧
      ¬Fin15AnchoredAtom2384 chi ∧
      ¬Fin15AnchoredAtom2386 chi ∧
      ¬Fin15AnchoredAtom2388 chi ∧
      ¬Fin15AnchoredAtom2390 chi ∧
      ¬Fin15AnchoredAtom2392 chi ∧
      ¬Fin15AnchoredAtom2399 chi ∧
      ¬Fin15AnchoredAtom2401 chi ∧
      ¬Fin15AnchoredAtom2406 chi ∧
      ¬Fin15AnchoredAtom2437 chi ∧
      ¬Fin15AnchoredAtom2439 chi ∧
      ¬Fin15AnchoredAtom2441 chi ∧
      ¬Fin15AnchoredAtom2448 chi ∧
      ¬Fin15AnchoredAtom2450 chi ∧
      ¬Fin15AnchoredAtom2455 chi ∧
      ¬Fin15AnchoredAtom2463 chi ∧
      ¬Fin15AnchoredAtom2465 chi ∧
      ¬Fin15AnchoredAtom2470 chi ∧
      ¬Fin15AnchoredAtom2486 chi ∧
      ¬Fin15AnchoredAtom2641 chi ∧
      ¬Fin15AnchoredAtom2643 chi ∧
      ¬Fin15AnchoredAtom2645 chi ∧
      ¬Fin15AnchoredAtom2652 chi ∧
      ¬Fin15AnchoredAtom2654 chi ∧
      ¬Fin15AnchoredAtom2659 chi ∧
      ¬Fin15AnchoredAtom2667 chi ∧
      ¬Fin15AnchoredAtom2669 chi ∧
      ¬Fin15AnchoredAtom2674 chi ∧
      ¬Fin15AnchoredAtom2690 chi ∧
      ¬Fin15AnchoredAtom2758 chi ∧
      ¬Fin15AnchoredAtom2760 chi ∧
      ¬Fin15AnchoredAtom2765 chi ∧
      ¬Fin15AnchoredAtom2781 chi ∧
      ¬Fin15AnchoredAtom2801 chi ∧
      ¬Fin15AnchoredAtom4181 chi ∧
      ¬Fin15AnchoredAtom4183 chi ∧
      ¬Fin15AnchoredAtom4185 chi ∧
      ¬Fin15AnchoredAtom4192 chi ∧
      ¬Fin15AnchoredAtom4194 chi ∧
      ¬Fin15AnchoredAtom4199 chi ∧
      ¬Fin15AnchoredAtom4207 chi ∧
      ¬Fin15AnchoredAtom4209 chi ∧
      ¬Fin15AnchoredAtom4214 chi ∧
      ¬Fin15AnchoredAtom4230 chi ∧
      ¬Fin15AnchoredAtom4298 chi ∧
      ¬Fin15AnchoredAtom4300 chi ∧
      ¬Fin15AnchoredAtom4305 chi ∧
      ¬Fin15AnchoredAtom4321 chi ∧
      ¬Fin15AnchoredAtom4341 chi ∧
      ¬Fin15AnchoredAtom4634 chi ∧
      ¬Fin15AnchoredAtom4636 chi ∧
      ¬Fin15AnchoredAtom4641 chi ∧
      ¬Fin15AnchoredAtom4657 chi ∧
      ¬Fin15AnchoredAtom4677 chi ∧
      ¬Fin15AnchoredAtom4782 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 5, 7, 8, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21929
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2380 Fin15AnchoredAtom2382 Fin15AnchoredAtom2384
    Fin15AnchoredAtom2386 Fin15AnchoredAtom2388 Fin15AnchoredAtom2390 Fin15AnchoredAtom2392
    Fin15AnchoredAtom2399 Fin15AnchoredAtom2401 Fin15AnchoredAtom2406 Fin15AnchoredAtom2437
    Fin15AnchoredAtom2439 Fin15AnchoredAtom2441 Fin15AnchoredAtom2448 Fin15AnchoredAtom2450
    Fin15AnchoredAtom2455 Fin15AnchoredAtom2463 Fin15AnchoredAtom2465 Fin15AnchoredAtom2470
    Fin15AnchoredAtom2486 Fin15AnchoredAtom2641 Fin15AnchoredAtom2643 Fin15AnchoredAtom2645
    Fin15AnchoredAtom2652 Fin15AnchoredAtom2654 Fin15AnchoredAtom2659 Fin15AnchoredAtom2667
    Fin15AnchoredAtom2669 Fin15AnchoredAtom2674 Fin15AnchoredAtom2690 Fin15AnchoredAtom2758
    Fin15AnchoredAtom2760 Fin15AnchoredAtom2765 Fin15AnchoredAtom2781 Fin15AnchoredAtom2801
    Fin15AnchoredAtom4181 Fin15AnchoredAtom4183 Fin15AnchoredAtom4185 Fin15AnchoredAtom4192
    Fin15AnchoredAtom4194 Fin15AnchoredAtom4199 Fin15AnchoredAtom4207 Fin15AnchoredAtom4209
    Fin15AnchoredAtom4214 Fin15AnchoredAtom4230 Fin15AnchoredAtom4298 Fin15AnchoredAtom4300
    Fin15AnchoredAtom4305 Fin15AnchoredAtom4321 Fin15AnchoredAtom4341 Fin15AnchoredAtom4634
    Fin15AnchoredAtom4636 Fin15AnchoredAtom4641 Fin15AnchoredAtom4657 Fin15AnchoredAtom4677
    Fin15AnchoredAtom4782 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31489 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2380 chi ∧
      ¬Fin15AnchoredAtom2382 chi ∧
      ¬Fin15AnchoredAtom2385 chi ∧
      ¬Fin15AnchoredAtom2386 chi ∧
      ¬Fin15AnchoredAtom2388 chi ∧
      ¬Fin15AnchoredAtom2391 chi ∧
      ¬Fin15AnchoredAtom2392 chi ∧
      ¬Fin15AnchoredAtom2400 chi ∧
      ¬Fin15AnchoredAtom2401 chi ∧
      ¬Fin15AnchoredAtom2407 chi ∧
      ¬Fin15AnchoredAtom2437 chi ∧
      ¬Fin15AnchoredAtom2440 chi ∧
      ¬Fin15AnchoredAtom2441 chi ∧
      ¬Fin15AnchoredAtom2449 chi ∧
      ¬Fin15AnchoredAtom2450 chi ∧
      ¬Fin15AnchoredAtom2456 chi ∧
      ¬Fin15AnchoredAtom2464 chi ∧
      ¬Fin15AnchoredAtom2465 chi ∧
      ¬Fin15AnchoredAtom2471 chi ∧
      ¬Fin15AnchoredAtom2487 chi ∧
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
      ¬Fin15AnchoredAtom4181 chi ∧
      ¬Fin15AnchoredAtom4184 chi ∧
      ¬Fin15AnchoredAtom4185 chi ∧
      ¬Fin15AnchoredAtom4193 chi ∧
      ¬Fin15AnchoredAtom4194 chi ∧
      ¬Fin15AnchoredAtom4200 chi ∧
      ¬Fin15AnchoredAtom4208 chi ∧
      ¬Fin15AnchoredAtom4209 chi ∧
      ¬Fin15AnchoredAtom4215 chi ∧
      ¬Fin15AnchoredAtom4231 chi ∧
      ¬Fin15AnchoredAtom4299 chi ∧
      ¬Fin15AnchoredAtom4300 chi ∧
      ¬Fin15AnchoredAtom4306 chi ∧
      ¬Fin15AnchoredAtom4322 chi ∧
      ¬Fin15AnchoredAtom4342 chi ∧
      ¬Fin15AnchoredAtom4635 chi ∧
      ¬Fin15AnchoredAtom4636 chi ∧
      ¬Fin15AnchoredAtom4642 chi ∧
      ¬Fin15AnchoredAtom4658 chi ∧
      ¬Fin15AnchoredAtom4678 chi ∧
      ¬Fin15AnchoredAtom4783 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 5, 7, 8, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26025
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2380 Fin15AnchoredAtom2382 Fin15AnchoredAtom2385
    Fin15AnchoredAtom2386 Fin15AnchoredAtom2388 Fin15AnchoredAtom2391 Fin15AnchoredAtom2392
    Fin15AnchoredAtom2400 Fin15AnchoredAtom2401 Fin15AnchoredAtom2407 Fin15AnchoredAtom2437
    Fin15AnchoredAtom2440 Fin15AnchoredAtom2441 Fin15AnchoredAtom2449 Fin15AnchoredAtom2450
    Fin15AnchoredAtom2456 Fin15AnchoredAtom2464 Fin15AnchoredAtom2465 Fin15AnchoredAtom2471
    Fin15AnchoredAtom2487 Fin15AnchoredAtom2641 Fin15AnchoredAtom2644 Fin15AnchoredAtom2645
    Fin15AnchoredAtom2653 Fin15AnchoredAtom2654 Fin15AnchoredAtom2660 Fin15AnchoredAtom2668
    Fin15AnchoredAtom2669 Fin15AnchoredAtom2675 Fin15AnchoredAtom2691 Fin15AnchoredAtom2759
    Fin15AnchoredAtom2760 Fin15AnchoredAtom2766 Fin15AnchoredAtom2782 Fin15AnchoredAtom2802
    Fin15AnchoredAtom4181 Fin15AnchoredAtom4184 Fin15AnchoredAtom4185 Fin15AnchoredAtom4193
    Fin15AnchoredAtom4194 Fin15AnchoredAtom4200 Fin15AnchoredAtom4208 Fin15AnchoredAtom4209
    Fin15AnchoredAtom4215 Fin15AnchoredAtom4231 Fin15AnchoredAtom4299 Fin15AnchoredAtom4300
    Fin15AnchoredAtom4306 Fin15AnchoredAtom4322 Fin15AnchoredAtom4342 Fin15AnchoredAtom4635
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

theorem fin15Anchored_clause31490 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2381 chi ∧
      ¬Fin15AnchoredAtom2382 chi ∧
      ¬Fin15AnchoredAtom2384 chi ∧
      ¬Fin15AnchoredAtom2385 chi ∧
      ¬Fin15AnchoredAtom2393 chi ∧
      ¬Fin15AnchoredAtom2395 chi ∧
      ¬Fin15AnchoredAtom2396 chi ∧
      ¬Fin15AnchoredAtom2399 chi ∧
      ¬Fin15AnchoredAtom2400 chi ∧
      ¬Fin15AnchoredAtom2405 chi ∧
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
      ¬Fin15AnchoredAtom4186 chi ∧
      ¬Fin15AnchoredAtom4188 chi ∧
      ¬Fin15AnchoredAtom4189 chi ∧
      ¬Fin15AnchoredAtom4192 chi ∧
      ¬Fin15AnchoredAtom4193 chi ∧
      ¬Fin15AnchoredAtom4198 chi ∧
      ¬Fin15AnchoredAtom4217 chi ∧
      ¬Fin15AnchoredAtom4218 chi ∧
      ¬Fin15AnchoredAtom4223 chi ∧
      ¬Fin15AnchoredAtom4229 chi ∧
      ¬Fin15AnchoredAtom4308 chi ∧
      ¬Fin15AnchoredAtom4309 chi ∧
      ¬Fin15AnchoredAtom4314 chi ∧
      ¬Fin15AnchoredAtom4320 chi ∧
      ¬Fin15AnchoredAtom4350 chi ∧
      ¬Fin15AnchoredAtom4644 chi ∧
      ¬Fin15AnchoredAtom4645 chi ∧
      ¬Fin15AnchoredAtom4650 chi ∧
      ¬Fin15AnchoredAtom4656 chi ∧
      ¬Fin15AnchoredAtom4686 chi ∧
      ¬Fin15AnchoredAtom4791 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 5, 7, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13993
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2381 Fin15AnchoredAtom2382 Fin15AnchoredAtom2384
    Fin15AnchoredAtom2385 Fin15AnchoredAtom2393 Fin15AnchoredAtom2395 Fin15AnchoredAtom2396
    Fin15AnchoredAtom2399 Fin15AnchoredAtom2400 Fin15AnchoredAtom2405 Fin15AnchoredAtom2442
    Fin15AnchoredAtom2444 Fin15AnchoredAtom2445 Fin15AnchoredAtom2448 Fin15AnchoredAtom2449
    Fin15AnchoredAtom2454 Fin15AnchoredAtom2473 Fin15AnchoredAtom2474 Fin15AnchoredAtom2479
    Fin15AnchoredAtom2485 Fin15AnchoredAtom2646 Fin15AnchoredAtom2648 Fin15AnchoredAtom2649
    Fin15AnchoredAtom2652 Fin15AnchoredAtom2653 Fin15AnchoredAtom2658 Fin15AnchoredAtom2677
    Fin15AnchoredAtom2678 Fin15AnchoredAtom2683 Fin15AnchoredAtom2689 Fin15AnchoredAtom2768
    Fin15AnchoredAtom2769 Fin15AnchoredAtom2774 Fin15AnchoredAtom2780 Fin15AnchoredAtom2810
    Fin15AnchoredAtom4186 Fin15AnchoredAtom4188 Fin15AnchoredAtom4189 Fin15AnchoredAtom4192
    Fin15AnchoredAtom4193 Fin15AnchoredAtom4198 Fin15AnchoredAtom4217 Fin15AnchoredAtom4218
    Fin15AnchoredAtom4223 Fin15AnchoredAtom4229 Fin15AnchoredAtom4308 Fin15AnchoredAtom4309
    Fin15AnchoredAtom4314 Fin15AnchoredAtom4320 Fin15AnchoredAtom4350 Fin15AnchoredAtom4644
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

theorem fin15Anchored_clause31491 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2381 chi ∧
      ¬Fin15AnchoredAtom2382 chi ∧
      ¬Fin15AnchoredAtom2384 chi ∧
      ¬Fin15AnchoredAtom2386 chi ∧
      ¬Fin15AnchoredAtom2393 chi ∧
      ¬Fin15AnchoredAtom2395 chi ∧
      ¬Fin15AnchoredAtom2397 chi ∧
      ¬Fin15AnchoredAtom2399 chi ∧
      ¬Fin15AnchoredAtom2401 chi ∧
      ¬Fin15AnchoredAtom2406 chi ∧
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
      ¬Fin15AnchoredAtom4186 chi ∧
      ¬Fin15AnchoredAtom4188 chi ∧
      ¬Fin15AnchoredAtom4190 chi ∧
      ¬Fin15AnchoredAtom4192 chi ∧
      ¬Fin15AnchoredAtom4194 chi ∧
      ¬Fin15AnchoredAtom4199 chi ∧
      ¬Fin15AnchoredAtom4217 chi ∧
      ¬Fin15AnchoredAtom4219 chi ∧
      ¬Fin15AnchoredAtom4224 chi ∧
      ¬Fin15AnchoredAtom4230 chi ∧
      ¬Fin15AnchoredAtom4308 chi ∧
      ¬Fin15AnchoredAtom4310 chi ∧
      ¬Fin15AnchoredAtom4315 chi ∧
      ¬Fin15AnchoredAtom4321 chi ∧
      ¬Fin15AnchoredAtom4351 chi ∧
      ¬Fin15AnchoredAtom4644 chi ∧
      ¬Fin15AnchoredAtom4646 chi ∧
      ¬Fin15AnchoredAtom4651 chi ∧
      ¬Fin15AnchoredAtom4657 chi ∧
      ¬Fin15AnchoredAtom4687 chi ∧
      ¬Fin15AnchoredAtom4792 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 5, 7, 9, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22185
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2381 Fin15AnchoredAtom2382 Fin15AnchoredAtom2384
    Fin15AnchoredAtom2386 Fin15AnchoredAtom2393 Fin15AnchoredAtom2395 Fin15AnchoredAtom2397
    Fin15AnchoredAtom2399 Fin15AnchoredAtom2401 Fin15AnchoredAtom2406 Fin15AnchoredAtom2442
    Fin15AnchoredAtom2444 Fin15AnchoredAtom2446 Fin15AnchoredAtom2448 Fin15AnchoredAtom2450
    Fin15AnchoredAtom2455 Fin15AnchoredAtom2473 Fin15AnchoredAtom2475 Fin15AnchoredAtom2480
    Fin15AnchoredAtom2486 Fin15AnchoredAtom2646 Fin15AnchoredAtom2648 Fin15AnchoredAtom2650
    Fin15AnchoredAtom2652 Fin15AnchoredAtom2654 Fin15AnchoredAtom2659 Fin15AnchoredAtom2677
    Fin15AnchoredAtom2679 Fin15AnchoredAtom2684 Fin15AnchoredAtom2690 Fin15AnchoredAtom2768
    Fin15AnchoredAtom2770 Fin15AnchoredAtom2775 Fin15AnchoredAtom2781 Fin15AnchoredAtom2811
    Fin15AnchoredAtom4186 Fin15AnchoredAtom4188 Fin15AnchoredAtom4190 Fin15AnchoredAtom4192
    Fin15AnchoredAtom4194 Fin15AnchoredAtom4199 Fin15AnchoredAtom4217 Fin15AnchoredAtom4219
    Fin15AnchoredAtom4224 Fin15AnchoredAtom4230 Fin15AnchoredAtom4308 Fin15AnchoredAtom4310
    Fin15AnchoredAtom4315 Fin15AnchoredAtom4321 Fin15AnchoredAtom4351 Fin15AnchoredAtom4644
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

theorem fin15Anchored_clause31492 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2381 chi ∧
      ¬Fin15AnchoredAtom2382 chi ∧
      ¬Fin15AnchoredAtom2385 chi ∧
      ¬Fin15AnchoredAtom2386 chi ∧
      ¬Fin15AnchoredAtom2393 chi ∧
      ¬Fin15AnchoredAtom2396 chi ∧
      ¬Fin15AnchoredAtom2397 chi ∧
      ¬Fin15AnchoredAtom2400 chi ∧
      ¬Fin15AnchoredAtom2401 chi ∧
      ¬Fin15AnchoredAtom2407 chi ∧
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
      ¬Fin15AnchoredAtom4186 chi ∧
      ¬Fin15AnchoredAtom4189 chi ∧
      ¬Fin15AnchoredAtom4190 chi ∧
      ¬Fin15AnchoredAtom4193 chi ∧
      ¬Fin15AnchoredAtom4194 chi ∧
      ¬Fin15AnchoredAtom4200 chi ∧
      ¬Fin15AnchoredAtom4218 chi ∧
      ¬Fin15AnchoredAtom4219 chi ∧
      ¬Fin15AnchoredAtom4225 chi ∧
      ¬Fin15AnchoredAtom4231 chi ∧
      ¬Fin15AnchoredAtom4309 chi ∧
      ¬Fin15AnchoredAtom4310 chi ∧
      ¬Fin15AnchoredAtom4316 chi ∧
      ¬Fin15AnchoredAtom4322 chi ∧
      ¬Fin15AnchoredAtom4352 chi ∧
      ¬Fin15AnchoredAtom4645 chi ∧
      ¬Fin15AnchoredAtom4646 chi ∧
      ¬Fin15AnchoredAtom4652 chi ∧
      ¬Fin15AnchoredAtom4658 chi ∧
      ¬Fin15AnchoredAtom4688 chi ∧
      ¬Fin15AnchoredAtom4793 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 5, 7, 9, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26281
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2381 Fin15AnchoredAtom2382 Fin15AnchoredAtom2385
    Fin15AnchoredAtom2386 Fin15AnchoredAtom2393 Fin15AnchoredAtom2396 Fin15AnchoredAtom2397
    Fin15AnchoredAtom2400 Fin15AnchoredAtom2401 Fin15AnchoredAtom2407 Fin15AnchoredAtom2442
    Fin15AnchoredAtom2445 Fin15AnchoredAtom2446 Fin15AnchoredAtom2449 Fin15AnchoredAtom2450
    Fin15AnchoredAtom2456 Fin15AnchoredAtom2474 Fin15AnchoredAtom2475 Fin15AnchoredAtom2481
    Fin15AnchoredAtom2487 Fin15AnchoredAtom2646 Fin15AnchoredAtom2649 Fin15AnchoredAtom2650
    Fin15AnchoredAtom2653 Fin15AnchoredAtom2654 Fin15AnchoredAtom2660 Fin15AnchoredAtom2678
    Fin15AnchoredAtom2679 Fin15AnchoredAtom2685 Fin15AnchoredAtom2691 Fin15AnchoredAtom2769
    Fin15AnchoredAtom2770 Fin15AnchoredAtom2776 Fin15AnchoredAtom2782 Fin15AnchoredAtom2812
    Fin15AnchoredAtom4186 Fin15AnchoredAtom4189 Fin15AnchoredAtom4190 Fin15AnchoredAtom4193
    Fin15AnchoredAtom4194 Fin15AnchoredAtom4200 Fin15AnchoredAtom4218 Fin15AnchoredAtom4219
    Fin15AnchoredAtom4225 Fin15AnchoredAtom4231 Fin15AnchoredAtom4309 Fin15AnchoredAtom4310
    Fin15AnchoredAtom4316 Fin15AnchoredAtom4322 Fin15AnchoredAtom4352 Fin15AnchoredAtom4645
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

theorem fin15Anchored_clause31493 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2381 chi ∧
      ¬Fin15AnchoredAtom2384 chi ∧
      ¬Fin15AnchoredAtom2385 chi ∧
      ¬Fin15AnchoredAtom2386 chi ∧
      ¬Fin15AnchoredAtom2395 chi ∧
      ¬Fin15AnchoredAtom2396 chi ∧
      ¬Fin15AnchoredAtom2397 chi ∧
      ¬Fin15AnchoredAtom2405 chi ∧
      ¬Fin15AnchoredAtom2406 chi ∧
      ¬Fin15AnchoredAtom2407 chi ∧
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
      ¬Fin15AnchoredAtom4188 chi ∧
      ¬Fin15AnchoredAtom4189 chi ∧
      ¬Fin15AnchoredAtom4190 chi ∧
      ¬Fin15AnchoredAtom4198 chi ∧
      ¬Fin15AnchoredAtom4199 chi ∧
      ¬Fin15AnchoredAtom4200 chi ∧
      ¬Fin15AnchoredAtom4223 chi ∧
      ¬Fin15AnchoredAtom4224 chi ∧
      ¬Fin15AnchoredAtom4225 chi ∧
      ¬Fin15AnchoredAtom4235 chi ∧
      ¬Fin15AnchoredAtom4314 chi ∧
      ¬Fin15AnchoredAtom4315 chi ∧
      ¬Fin15AnchoredAtom4316 chi ∧
      ¬Fin15AnchoredAtom4326 chi ∧
      ¬Fin15AnchoredAtom4356 chi ∧
      ¬Fin15AnchoredAtom4650 chi ∧
      ¬Fin15AnchoredAtom4651 chi ∧
      ¬Fin15AnchoredAtom4652 chi ∧
      ¬Fin15AnchoredAtom4662 chi ∧
      ¬Fin15AnchoredAtom4692 chi ∧
      ¬Fin15AnchoredAtom4797 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 5, 7, 9, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29353
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2381 Fin15AnchoredAtom2384 Fin15AnchoredAtom2385
    Fin15AnchoredAtom2386 Fin15AnchoredAtom2395 Fin15AnchoredAtom2396 Fin15AnchoredAtom2397
    Fin15AnchoredAtom2405 Fin15AnchoredAtom2406 Fin15AnchoredAtom2407 Fin15AnchoredAtom2444
    Fin15AnchoredAtom2445 Fin15AnchoredAtom2446 Fin15AnchoredAtom2454 Fin15AnchoredAtom2455
    Fin15AnchoredAtom2456 Fin15AnchoredAtom2479 Fin15AnchoredAtom2480 Fin15AnchoredAtom2481
    Fin15AnchoredAtom2491 Fin15AnchoredAtom2648 Fin15AnchoredAtom2649 Fin15AnchoredAtom2650
    Fin15AnchoredAtom2658 Fin15AnchoredAtom2659 Fin15AnchoredAtom2660 Fin15AnchoredAtom2683
    Fin15AnchoredAtom2684 Fin15AnchoredAtom2685 Fin15AnchoredAtom2695 Fin15AnchoredAtom2774
    Fin15AnchoredAtom2775 Fin15AnchoredAtom2776 Fin15AnchoredAtom2786 Fin15AnchoredAtom2816
    Fin15AnchoredAtom4188 Fin15AnchoredAtom4189 Fin15AnchoredAtom4190 Fin15AnchoredAtom4198
    Fin15AnchoredAtom4199 Fin15AnchoredAtom4200 Fin15AnchoredAtom4223 Fin15AnchoredAtom4224
    Fin15AnchoredAtom4225 Fin15AnchoredAtom4235 Fin15AnchoredAtom4314 Fin15AnchoredAtom4315
    Fin15AnchoredAtom4316 Fin15AnchoredAtom4326 Fin15AnchoredAtom4356 Fin15AnchoredAtom4650
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

theorem fin15Anchored_clause31494 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2382 chi ∧
      ¬Fin15AnchoredAtom2383 chi ∧
      ¬Fin15AnchoredAtom2384 chi ∧
      ¬Fin15AnchoredAtom2385 chi ∧
      ¬Fin15AnchoredAtom2398 chi ∧
      ¬Fin15AnchoredAtom2399 chi ∧
      ¬Fin15AnchoredAtom2400 chi ∧
      ¬Fin15AnchoredAtom2402 chi ∧
      ¬Fin15AnchoredAtom2403 chi ∧
      ¬Fin15AnchoredAtom2405 chi ∧
      ¬Fin15AnchoredAtom2447 chi ∧
      ¬Fin15AnchoredAtom2448 chi ∧
      ¬Fin15AnchoredAtom2449 chi ∧
      ¬Fin15AnchoredAtom2451 chi ∧
      ¬Fin15AnchoredAtom2452 chi ∧
      ¬Fin15AnchoredAtom2454 chi ∧
      ¬Fin15AnchoredAtom2482 chi ∧
      ¬Fin15AnchoredAtom2483 chi ∧
      ¬Fin15AnchoredAtom2485 chi ∧
      ¬Fin15AnchoredAtom2488 chi ∧
      ¬Fin15AnchoredAtom2651 chi ∧
      ¬Fin15AnchoredAtom2652 chi ∧
      ¬Fin15AnchoredAtom2653 chi ∧
      ¬Fin15AnchoredAtom2655 chi ∧
      ¬Fin15AnchoredAtom2656 chi ∧
      ¬Fin15AnchoredAtom2658 chi ∧
      ¬Fin15AnchoredAtom2686 chi ∧
      ¬Fin15AnchoredAtom2687 chi ∧
      ¬Fin15AnchoredAtom2689 chi ∧
      ¬Fin15AnchoredAtom2692 chi ∧
      ¬Fin15AnchoredAtom2777 chi ∧
      ¬Fin15AnchoredAtom2778 chi ∧
      ¬Fin15AnchoredAtom2780 chi ∧
      ¬Fin15AnchoredAtom2783 chi ∧
      ¬Fin15AnchoredAtom2817 chi ∧
      ¬Fin15AnchoredAtom4191 chi ∧
      ¬Fin15AnchoredAtom4192 chi ∧
      ¬Fin15AnchoredAtom4193 chi ∧
      ¬Fin15AnchoredAtom4195 chi ∧
      ¬Fin15AnchoredAtom4196 chi ∧
      ¬Fin15AnchoredAtom4198 chi ∧
      ¬Fin15AnchoredAtom4226 chi ∧
      ¬Fin15AnchoredAtom4227 chi ∧
      ¬Fin15AnchoredAtom4229 chi ∧
      ¬Fin15AnchoredAtom4232 chi ∧
      ¬Fin15AnchoredAtom4317 chi ∧
      ¬Fin15AnchoredAtom4318 chi ∧
      ¬Fin15AnchoredAtom4320 chi ∧
      ¬Fin15AnchoredAtom4323 chi ∧
      ¬Fin15AnchoredAtom4357 chi ∧
      ¬Fin15AnchoredAtom4653 chi ∧
      ¬Fin15AnchoredAtom4654 chi ∧
      ¬Fin15AnchoredAtom4656 chi ∧
      ¬Fin15AnchoredAtom4659 chi ∧
      ¬Fin15AnchoredAtom4693 chi ∧
      ¬Fin15AnchoredAtom4798 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 5, 7, 10, 11, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask15529
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2382 Fin15AnchoredAtom2383 Fin15AnchoredAtom2384
    Fin15AnchoredAtom2385 Fin15AnchoredAtom2398 Fin15AnchoredAtom2399 Fin15AnchoredAtom2400
    Fin15AnchoredAtom2402 Fin15AnchoredAtom2403 Fin15AnchoredAtom2405 Fin15AnchoredAtom2447
    Fin15AnchoredAtom2448 Fin15AnchoredAtom2449 Fin15AnchoredAtom2451 Fin15AnchoredAtom2452
    Fin15AnchoredAtom2454 Fin15AnchoredAtom2482 Fin15AnchoredAtom2483 Fin15AnchoredAtom2485
    Fin15AnchoredAtom2488 Fin15AnchoredAtom2651 Fin15AnchoredAtom2652 Fin15AnchoredAtom2653
    Fin15AnchoredAtom2655 Fin15AnchoredAtom2656 Fin15AnchoredAtom2658 Fin15AnchoredAtom2686
    Fin15AnchoredAtom2687 Fin15AnchoredAtom2689 Fin15AnchoredAtom2692 Fin15AnchoredAtom2777
    Fin15AnchoredAtom2778 Fin15AnchoredAtom2780 Fin15AnchoredAtom2783 Fin15AnchoredAtom2817
    Fin15AnchoredAtom4191 Fin15AnchoredAtom4192 Fin15AnchoredAtom4193 Fin15AnchoredAtom4195
    Fin15AnchoredAtom4196 Fin15AnchoredAtom4198 Fin15AnchoredAtom4226 Fin15AnchoredAtom4227
    Fin15AnchoredAtom4229 Fin15AnchoredAtom4232 Fin15AnchoredAtom4317 Fin15AnchoredAtom4318
    Fin15AnchoredAtom4320 Fin15AnchoredAtom4323 Fin15AnchoredAtom4357 Fin15AnchoredAtom4653
    Fin15AnchoredAtom4654 Fin15AnchoredAtom4656 Fin15AnchoredAtom4659 Fin15AnchoredAtom4693
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

theorem fin15Anchored_clause31495 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2382 chi ∧
      ¬Fin15AnchoredAtom2384 chi ∧
      ¬Fin15AnchoredAtom2385 chi ∧
      ¬Fin15AnchoredAtom2386 chi ∧
      ¬Fin15AnchoredAtom2399 chi ∧
      ¬Fin15AnchoredAtom2400 chi ∧
      ¬Fin15AnchoredAtom2401 chi ∧
      ¬Fin15AnchoredAtom2405 chi ∧
      ¬Fin15AnchoredAtom2406 chi ∧
      ¬Fin15AnchoredAtom2407 chi ∧
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
      ¬Fin15AnchoredAtom4192 chi ∧
      ¬Fin15AnchoredAtom4193 chi ∧
      ¬Fin15AnchoredAtom4194 chi ∧
      ¬Fin15AnchoredAtom4198 chi ∧
      ¬Fin15AnchoredAtom4199 chi ∧
      ¬Fin15AnchoredAtom4200 chi ∧
      ¬Fin15AnchoredAtom4229 chi ∧
      ¬Fin15AnchoredAtom4230 chi ∧
      ¬Fin15AnchoredAtom4231 chi ∧
      ¬Fin15AnchoredAtom4235 chi ∧
      ¬Fin15AnchoredAtom4320 chi ∧
      ¬Fin15AnchoredAtom4321 chi ∧
      ¬Fin15AnchoredAtom4322 chi ∧
      ¬Fin15AnchoredAtom4326 chi ∧
      ¬Fin15AnchoredAtom4360 chi ∧
      ¬Fin15AnchoredAtom4656 chi ∧
      ¬Fin15AnchoredAtom4657 chi ∧
      ¬Fin15AnchoredAtom4658 chi ∧
      ¬Fin15AnchoredAtom4662 chi ∧
      ¬Fin15AnchoredAtom4696 chi ∧
      ¬Fin15AnchoredAtom4801 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 5, 7, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29865
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2382 Fin15AnchoredAtom2384 Fin15AnchoredAtom2385
    Fin15AnchoredAtom2386 Fin15AnchoredAtom2399 Fin15AnchoredAtom2400 Fin15AnchoredAtom2401
    Fin15AnchoredAtom2405 Fin15AnchoredAtom2406 Fin15AnchoredAtom2407 Fin15AnchoredAtom2448
    Fin15AnchoredAtom2449 Fin15AnchoredAtom2450 Fin15AnchoredAtom2454 Fin15AnchoredAtom2455
    Fin15AnchoredAtom2456 Fin15AnchoredAtom2485 Fin15AnchoredAtom2486 Fin15AnchoredAtom2487
    Fin15AnchoredAtom2491 Fin15AnchoredAtom2652 Fin15AnchoredAtom2653 Fin15AnchoredAtom2654
    Fin15AnchoredAtom2658 Fin15AnchoredAtom2659 Fin15AnchoredAtom2660 Fin15AnchoredAtom2689
    Fin15AnchoredAtom2690 Fin15AnchoredAtom2691 Fin15AnchoredAtom2695 Fin15AnchoredAtom2780
    Fin15AnchoredAtom2781 Fin15AnchoredAtom2782 Fin15AnchoredAtom2786 Fin15AnchoredAtom2820
    Fin15AnchoredAtom4192 Fin15AnchoredAtom4193 Fin15AnchoredAtom4194 Fin15AnchoredAtom4198
    Fin15AnchoredAtom4199 Fin15AnchoredAtom4200 Fin15AnchoredAtom4229 Fin15AnchoredAtom4230
    Fin15AnchoredAtom4231 Fin15AnchoredAtom4235 Fin15AnchoredAtom4320 Fin15AnchoredAtom4321
    Fin15AnchoredAtom4322 Fin15AnchoredAtom4326 Fin15AnchoredAtom4360 Fin15AnchoredAtom4656
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

theorem fin15Anchored_clause31496 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2387 chi ∧
      ¬Fin15AnchoredAtom2388 chi ∧
      ¬Fin15AnchoredAtom2390 chi ∧
      ¬Fin15AnchoredAtom2391 chi ∧
      ¬Fin15AnchoredAtom2393 chi ∧
      ¬Fin15AnchoredAtom2395 chi ∧
      ¬Fin15AnchoredAtom2396 chi ∧
      ¬Fin15AnchoredAtom2399 chi ∧
      ¬Fin15AnchoredAtom2400 chi ∧
      ¬Fin15AnchoredAtom2405 chi ∧
      ¬Fin15AnchoredAtom2457 chi ∧
      ¬Fin15AnchoredAtom2459 chi ∧
      ¬Fin15AnchoredAtom2460 chi ∧
      ¬Fin15AnchoredAtom2463 chi ∧
      ¬Fin15AnchoredAtom2464 chi ∧
      ¬Fin15AnchoredAtom2469 chi ∧
      ¬Fin15AnchoredAtom2473 chi ∧
      ¬Fin15AnchoredAtom2474 chi ∧
      ¬Fin15AnchoredAtom2479 chi ∧
      ¬Fin15AnchoredAtom2485 chi ∧
      ¬Fin15AnchoredAtom2661 chi ∧
      ¬Fin15AnchoredAtom2663 chi ∧
      ¬Fin15AnchoredAtom2664 chi ∧
      ¬Fin15AnchoredAtom2667 chi ∧
      ¬Fin15AnchoredAtom2668 chi ∧
      ¬Fin15AnchoredAtom2673 chi ∧
      ¬Fin15AnchoredAtom2677 chi ∧
      ¬Fin15AnchoredAtom2678 chi ∧
      ¬Fin15AnchoredAtom2683 chi ∧
      ¬Fin15AnchoredAtom2689 chi ∧
      ¬Fin15AnchoredAtom2788 chi ∧
      ¬Fin15AnchoredAtom2789 chi ∧
      ¬Fin15AnchoredAtom2794 chi ∧
      ¬Fin15AnchoredAtom2800 chi ∧
      ¬Fin15AnchoredAtom2810 chi ∧
      ¬Fin15AnchoredAtom4201 chi ∧
      ¬Fin15AnchoredAtom4203 chi ∧
      ¬Fin15AnchoredAtom4204 chi ∧
      ¬Fin15AnchoredAtom4207 chi ∧
      ¬Fin15AnchoredAtom4208 chi ∧
      ¬Fin15AnchoredAtom4213 chi ∧
      ¬Fin15AnchoredAtom4217 chi ∧
      ¬Fin15AnchoredAtom4218 chi ∧
      ¬Fin15AnchoredAtom4223 chi ∧
      ¬Fin15AnchoredAtom4229 chi ∧
      ¬Fin15AnchoredAtom4328 chi ∧
      ¬Fin15AnchoredAtom4329 chi ∧
      ¬Fin15AnchoredAtom4334 chi ∧
      ¬Fin15AnchoredAtom4340 chi ∧
      ¬Fin15AnchoredAtom4350 chi ∧
      ¬Fin15AnchoredAtom4664 chi ∧
      ¬Fin15AnchoredAtom4665 chi ∧
      ¬Fin15AnchoredAtom4670 chi ∧
      ¬Fin15AnchoredAtom4676 chi ∧
      ¬Fin15AnchoredAtom4686 chi ∧
      ¬Fin15AnchoredAtom4806 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 5, 8, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask14121
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2387 Fin15AnchoredAtom2388 Fin15AnchoredAtom2390
    Fin15AnchoredAtom2391 Fin15AnchoredAtom2393 Fin15AnchoredAtom2395 Fin15AnchoredAtom2396
    Fin15AnchoredAtom2399 Fin15AnchoredAtom2400 Fin15AnchoredAtom2405 Fin15AnchoredAtom2457
    Fin15AnchoredAtom2459 Fin15AnchoredAtom2460 Fin15AnchoredAtom2463 Fin15AnchoredAtom2464
    Fin15AnchoredAtom2469 Fin15AnchoredAtom2473 Fin15AnchoredAtom2474 Fin15AnchoredAtom2479
    Fin15AnchoredAtom2485 Fin15AnchoredAtom2661 Fin15AnchoredAtom2663 Fin15AnchoredAtom2664
    Fin15AnchoredAtom2667 Fin15AnchoredAtom2668 Fin15AnchoredAtom2673 Fin15AnchoredAtom2677
    Fin15AnchoredAtom2678 Fin15AnchoredAtom2683 Fin15AnchoredAtom2689 Fin15AnchoredAtom2788
    Fin15AnchoredAtom2789 Fin15AnchoredAtom2794 Fin15AnchoredAtom2800 Fin15AnchoredAtom2810
    Fin15AnchoredAtom4201 Fin15AnchoredAtom4203 Fin15AnchoredAtom4204 Fin15AnchoredAtom4207
    Fin15AnchoredAtom4208 Fin15AnchoredAtom4213 Fin15AnchoredAtom4217 Fin15AnchoredAtom4218
    Fin15AnchoredAtom4223 Fin15AnchoredAtom4229 Fin15AnchoredAtom4328 Fin15AnchoredAtom4329
    Fin15AnchoredAtom4334 Fin15AnchoredAtom4340 Fin15AnchoredAtom4350 Fin15AnchoredAtom4664
    Fin15AnchoredAtom4665 Fin15AnchoredAtom4670 Fin15AnchoredAtom4676 Fin15AnchoredAtom4686
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

theorem fin15Anchored_clause31497 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2387 chi ∧
      ¬Fin15AnchoredAtom2388 chi ∧
      ¬Fin15AnchoredAtom2390 chi ∧
      ¬Fin15AnchoredAtom2392 chi ∧
      ¬Fin15AnchoredAtom2393 chi ∧
      ¬Fin15AnchoredAtom2395 chi ∧
      ¬Fin15AnchoredAtom2397 chi ∧
      ¬Fin15AnchoredAtom2399 chi ∧
      ¬Fin15AnchoredAtom2401 chi ∧
      ¬Fin15AnchoredAtom2406 chi ∧
      ¬Fin15AnchoredAtom2457 chi ∧
      ¬Fin15AnchoredAtom2459 chi ∧
      ¬Fin15AnchoredAtom2461 chi ∧
      ¬Fin15AnchoredAtom2463 chi ∧
      ¬Fin15AnchoredAtom2465 chi ∧
      ¬Fin15AnchoredAtom2470 chi ∧
      ¬Fin15AnchoredAtom2473 chi ∧
      ¬Fin15AnchoredAtom2475 chi ∧
      ¬Fin15AnchoredAtom2480 chi ∧
      ¬Fin15AnchoredAtom2486 chi ∧
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
      ¬Fin15AnchoredAtom4201 chi ∧
      ¬Fin15AnchoredAtom4203 chi ∧
      ¬Fin15AnchoredAtom4205 chi ∧
      ¬Fin15AnchoredAtom4207 chi ∧
      ¬Fin15AnchoredAtom4209 chi ∧
      ¬Fin15AnchoredAtom4214 chi ∧
      ¬Fin15AnchoredAtom4217 chi ∧
      ¬Fin15AnchoredAtom4219 chi ∧
      ¬Fin15AnchoredAtom4224 chi ∧
      ¬Fin15AnchoredAtom4230 chi ∧
      ¬Fin15AnchoredAtom4328 chi ∧
      ¬Fin15AnchoredAtom4330 chi ∧
      ¬Fin15AnchoredAtom4335 chi ∧
      ¬Fin15AnchoredAtom4341 chi ∧
      ¬Fin15AnchoredAtom4351 chi ∧
      ¬Fin15AnchoredAtom4664 chi ∧
      ¬Fin15AnchoredAtom4666 chi ∧
      ¬Fin15AnchoredAtom4671 chi ∧
      ¬Fin15AnchoredAtom4677 chi ∧
      ¬Fin15AnchoredAtom4687 chi ∧
      ¬Fin15AnchoredAtom4807 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 5, 8, 9, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22313
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2387 Fin15AnchoredAtom2388 Fin15AnchoredAtom2390
    Fin15AnchoredAtom2392 Fin15AnchoredAtom2393 Fin15AnchoredAtom2395 Fin15AnchoredAtom2397
    Fin15AnchoredAtom2399 Fin15AnchoredAtom2401 Fin15AnchoredAtom2406 Fin15AnchoredAtom2457
    Fin15AnchoredAtom2459 Fin15AnchoredAtom2461 Fin15AnchoredAtom2463 Fin15AnchoredAtom2465
    Fin15AnchoredAtom2470 Fin15AnchoredAtom2473 Fin15AnchoredAtom2475 Fin15AnchoredAtom2480
    Fin15AnchoredAtom2486 Fin15AnchoredAtom2661 Fin15AnchoredAtom2663 Fin15AnchoredAtom2665
    Fin15AnchoredAtom2667 Fin15AnchoredAtom2669 Fin15AnchoredAtom2674 Fin15AnchoredAtom2677
    Fin15AnchoredAtom2679 Fin15AnchoredAtom2684 Fin15AnchoredAtom2690 Fin15AnchoredAtom2788
    Fin15AnchoredAtom2790 Fin15AnchoredAtom2795 Fin15AnchoredAtom2801 Fin15AnchoredAtom2811
    Fin15AnchoredAtom4201 Fin15AnchoredAtom4203 Fin15AnchoredAtom4205 Fin15AnchoredAtom4207
    Fin15AnchoredAtom4209 Fin15AnchoredAtom4214 Fin15AnchoredAtom4217 Fin15AnchoredAtom4219
    Fin15AnchoredAtom4224 Fin15AnchoredAtom4230 Fin15AnchoredAtom4328 Fin15AnchoredAtom4330
    Fin15AnchoredAtom4335 Fin15AnchoredAtom4341 Fin15AnchoredAtom4351 Fin15AnchoredAtom4664
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

theorem fin15Anchored_clause31498 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2393 chi ∧
      ¬Fin15AnchoredAtom2395 chi ∧
      ¬Fin15AnchoredAtom2396 chi ∧
      ¬Fin15AnchoredAtom2397 chi ∧
      ¬Fin15AnchoredAtom2399 chi ∧
      ¬Fin15AnchoredAtom2400 chi ∧
      ¬Fin15AnchoredAtom2401 chi ∧
      ¬Fin15AnchoredAtom2405 chi ∧
      ¬Fin15AnchoredAtom2406 chi ∧
      ¬Fin15AnchoredAtom2407 chi ∧
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
      ¬Fin15AnchoredAtom4217 chi ∧
      ¬Fin15AnchoredAtom4218 chi ∧
      ¬Fin15AnchoredAtom4219 chi ∧
      ¬Fin15AnchoredAtom4223 chi ∧
      ¬Fin15AnchoredAtom4224 chi ∧
      ¬Fin15AnchoredAtom4225 chi ∧
      ¬Fin15AnchoredAtom4229 chi ∧
      ¬Fin15AnchoredAtom4230 chi ∧
      ¬Fin15AnchoredAtom4231 chi ∧
      ¬Fin15AnchoredAtom4235 chi ∧
      ¬Fin15AnchoredAtom4350 chi ∧
      ¬Fin15AnchoredAtom4351 chi ∧
      ¬Fin15AnchoredAtom4352 chi ∧
      ¬Fin15AnchoredAtom4356 chi ∧
      ¬Fin15AnchoredAtom4360 chi ∧
      ¬Fin15AnchoredAtom4686 chi ∧
      ¬Fin15AnchoredAtom4687 chi ∧
      ¬Fin15AnchoredAtom4688 chi ∧
      ¬Fin15AnchoredAtom4692 chi ∧
      ¬Fin15AnchoredAtom4696 chi ∧
      ¬Fin15AnchoredAtom4821 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 5, 9, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask30249
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2393 Fin15AnchoredAtom2395 Fin15AnchoredAtom2396
    Fin15AnchoredAtom2397 Fin15AnchoredAtom2399 Fin15AnchoredAtom2400 Fin15AnchoredAtom2401
    Fin15AnchoredAtom2405 Fin15AnchoredAtom2406 Fin15AnchoredAtom2407 Fin15AnchoredAtom2473
    Fin15AnchoredAtom2474 Fin15AnchoredAtom2475 Fin15AnchoredAtom2479 Fin15AnchoredAtom2480
    Fin15AnchoredAtom2481 Fin15AnchoredAtom2485 Fin15AnchoredAtom2486 Fin15AnchoredAtom2487
    Fin15AnchoredAtom2491 Fin15AnchoredAtom2677 Fin15AnchoredAtom2678 Fin15AnchoredAtom2679
    Fin15AnchoredAtom2683 Fin15AnchoredAtom2684 Fin15AnchoredAtom2685 Fin15AnchoredAtom2689
    Fin15AnchoredAtom2690 Fin15AnchoredAtom2691 Fin15AnchoredAtom2695 Fin15AnchoredAtom2810
    Fin15AnchoredAtom2811 Fin15AnchoredAtom2812 Fin15AnchoredAtom2816 Fin15AnchoredAtom2820
    Fin15AnchoredAtom4217 Fin15AnchoredAtom4218 Fin15AnchoredAtom4219 Fin15AnchoredAtom4223
    Fin15AnchoredAtom4224 Fin15AnchoredAtom4225 Fin15AnchoredAtom4229 Fin15AnchoredAtom4230
    Fin15AnchoredAtom4231 Fin15AnchoredAtom4235 Fin15AnchoredAtom4350 Fin15AnchoredAtom4351
    Fin15AnchoredAtom4352 Fin15AnchoredAtom4356 Fin15AnchoredAtom4360 Fin15AnchoredAtom4686
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

theorem fin15Anchored_clause31499 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2408 chi ∧
      ¬Fin15AnchoredAtom2409 chi ∧
      ¬Fin15AnchoredAtom2410 chi ∧
      ¬Fin15AnchoredAtom2412 chi ∧
      ¬Fin15AnchoredAtom2415 chi ∧
      ¬Fin15AnchoredAtom2416 chi ∧
      ¬Fin15AnchoredAtom2418 chi ∧
      ¬Fin15AnchoredAtom2421 chi ∧
      ¬Fin15AnchoredAtom2423 chi ∧
      ¬Fin15AnchoredAtom2427 chi ∧
      ¬Fin15AnchoredAtom2436 chi ∧
      ¬Fin15AnchoredAtom2437 chi ∧
      ¬Fin15AnchoredAtom2439 chi ∧
      ¬Fin15AnchoredAtom2442 chi ∧
      ¬Fin15AnchoredAtom2444 chi ∧
      ¬Fin15AnchoredAtom2448 chi ∧
      ¬Fin15AnchoredAtom2457 chi ∧
      ¬Fin15AnchoredAtom2459 chi ∧
      ¬Fin15AnchoredAtom2463 chi ∧
      ¬Fin15AnchoredAtom2473 chi ∧
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
      ¬Fin15AnchoredAtom4236 chi ∧
      ¬Fin15AnchoredAtom4237 chi ∧
      ¬Fin15AnchoredAtom4239 chi ∧
      ¬Fin15AnchoredAtom4242 chi ∧
      ¬Fin15AnchoredAtom4244 chi ∧
      ¬Fin15AnchoredAtom4248 chi ∧
      ¬Fin15AnchoredAtom4257 chi ∧
      ¬Fin15AnchoredAtom4259 chi ∧
      ¬Fin15AnchoredAtom4263 chi ∧
      ¬Fin15AnchoredAtom4273 chi ∧
      ¬Fin15AnchoredAtom4292 chi ∧
      ¬Fin15AnchoredAtom4294 chi ∧
      ¬Fin15AnchoredAtom4298 chi ∧
      ¬Fin15AnchoredAtom4308 chi ∧
      ¬Fin15AnchoredAtom4328 chi ∧
      ¬Fin15AnchoredAtom4698 chi ∧
      ¬Fin15AnchoredAtom4700 chi ∧
      ¬Fin15AnchoredAtom4704 chi ∧
      ¬Fin15AnchoredAtom4714 chi ∧
      ¬Fin15AnchoredAtom4734 chi ∧
      ¬Fin15AnchoredAtom4769 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 6, 7, 8, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask06089
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2408 Fin15AnchoredAtom2409 Fin15AnchoredAtom2410
    Fin15AnchoredAtom2412 Fin15AnchoredAtom2415 Fin15AnchoredAtom2416 Fin15AnchoredAtom2418
    Fin15AnchoredAtom2421 Fin15AnchoredAtom2423 Fin15AnchoredAtom2427 Fin15AnchoredAtom2436
    Fin15AnchoredAtom2437 Fin15AnchoredAtom2439 Fin15AnchoredAtom2442 Fin15AnchoredAtom2444
    Fin15AnchoredAtom2448 Fin15AnchoredAtom2457 Fin15AnchoredAtom2459 Fin15AnchoredAtom2463
    Fin15AnchoredAtom2473 Fin15AnchoredAtom2696 Fin15AnchoredAtom2697 Fin15AnchoredAtom2699
    Fin15AnchoredAtom2702 Fin15AnchoredAtom2704 Fin15AnchoredAtom2708 Fin15AnchoredAtom2717
    Fin15AnchoredAtom2719 Fin15AnchoredAtom2723 Fin15AnchoredAtom2733 Fin15AnchoredAtom2752
    Fin15AnchoredAtom2754 Fin15AnchoredAtom2758 Fin15AnchoredAtom2768 Fin15AnchoredAtom2788
    Fin15AnchoredAtom4236 Fin15AnchoredAtom4237 Fin15AnchoredAtom4239 Fin15AnchoredAtom4242
    Fin15AnchoredAtom4244 Fin15AnchoredAtom4248 Fin15AnchoredAtom4257 Fin15AnchoredAtom4259
    Fin15AnchoredAtom4263 Fin15AnchoredAtom4273 Fin15AnchoredAtom4292 Fin15AnchoredAtom4294
    Fin15AnchoredAtom4298 Fin15AnchoredAtom4308 Fin15AnchoredAtom4328 Fin15AnchoredAtom4698
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

theorem fin15Anchored_clause31500 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2408 chi ∧
      ¬Fin15AnchoredAtom2409 chi ∧
      ¬Fin15AnchoredAtom2410 chi ∧
      ¬Fin15AnchoredAtom2413 chi ∧
      ¬Fin15AnchoredAtom2415 chi ∧
      ¬Fin15AnchoredAtom2416 chi ∧
      ¬Fin15AnchoredAtom2419 chi ∧
      ¬Fin15AnchoredAtom2421 chi ∧
      ¬Fin15AnchoredAtom2424 chi ∧
      ¬Fin15AnchoredAtom2428 chi ∧
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
      ¬Fin15AnchoredAtom4236 chi ∧
      ¬Fin15AnchoredAtom4237 chi ∧
      ¬Fin15AnchoredAtom4240 chi ∧
      ¬Fin15AnchoredAtom4242 chi ∧
      ¬Fin15AnchoredAtom4245 chi ∧
      ¬Fin15AnchoredAtom4249 chi ∧
      ¬Fin15AnchoredAtom4257 chi ∧
      ¬Fin15AnchoredAtom4260 chi ∧
      ¬Fin15AnchoredAtom4264 chi ∧
      ¬Fin15AnchoredAtom4274 chi ∧
      ¬Fin15AnchoredAtom4292 chi ∧
      ¬Fin15AnchoredAtom4295 chi ∧
      ¬Fin15AnchoredAtom4299 chi ∧
      ¬Fin15AnchoredAtom4309 chi ∧
      ¬Fin15AnchoredAtom4329 chi ∧
      ¬Fin15AnchoredAtom4698 chi ∧
      ¬Fin15AnchoredAtom4701 chi ∧
      ¬Fin15AnchoredAtom4705 chi ∧
      ¬Fin15AnchoredAtom4715 chi ∧
      ¬Fin15AnchoredAtom4735 chi ∧
      ¬Fin15AnchoredAtom4770 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 6, 7, 8, 9, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask10185
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2408 Fin15AnchoredAtom2409 Fin15AnchoredAtom2410
    Fin15AnchoredAtom2413 Fin15AnchoredAtom2415 Fin15AnchoredAtom2416 Fin15AnchoredAtom2419
    Fin15AnchoredAtom2421 Fin15AnchoredAtom2424 Fin15AnchoredAtom2428 Fin15AnchoredAtom2436
    Fin15AnchoredAtom2437 Fin15AnchoredAtom2440 Fin15AnchoredAtom2442 Fin15AnchoredAtom2445
    Fin15AnchoredAtom2449 Fin15AnchoredAtom2457 Fin15AnchoredAtom2460 Fin15AnchoredAtom2464
    Fin15AnchoredAtom2474 Fin15AnchoredAtom2696 Fin15AnchoredAtom2697 Fin15AnchoredAtom2700
    Fin15AnchoredAtom2702 Fin15AnchoredAtom2705 Fin15AnchoredAtom2709 Fin15AnchoredAtom2717
    Fin15AnchoredAtom2720 Fin15AnchoredAtom2724 Fin15AnchoredAtom2734 Fin15AnchoredAtom2752
    Fin15AnchoredAtom2755 Fin15AnchoredAtom2759 Fin15AnchoredAtom2769 Fin15AnchoredAtom2789
    Fin15AnchoredAtom4236 Fin15AnchoredAtom4237 Fin15AnchoredAtom4240 Fin15AnchoredAtom4242
    Fin15AnchoredAtom4245 Fin15AnchoredAtom4249 Fin15AnchoredAtom4257 Fin15AnchoredAtom4260
    Fin15AnchoredAtom4264 Fin15AnchoredAtom4274 Fin15AnchoredAtom4292 Fin15AnchoredAtom4295
    Fin15AnchoredAtom4299 Fin15AnchoredAtom4309 Fin15AnchoredAtom4329 Fin15AnchoredAtom4698
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

theorem fin15Anchored_clause31501 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2408 chi ∧
      ¬Fin15AnchoredAtom2409 chi ∧
      ¬Fin15AnchoredAtom2410 chi ∧
      ¬Fin15AnchoredAtom2414 chi ∧
      ¬Fin15AnchoredAtom2415 chi ∧
      ¬Fin15AnchoredAtom2416 chi ∧
      ¬Fin15AnchoredAtom2420 chi ∧
      ¬Fin15AnchoredAtom2421 chi ∧
      ¬Fin15AnchoredAtom2425 chi ∧
      ¬Fin15AnchoredAtom2429 chi ∧
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
      ¬Fin15AnchoredAtom4236 chi ∧
      ¬Fin15AnchoredAtom4237 chi ∧
      ¬Fin15AnchoredAtom4241 chi ∧
      ¬Fin15AnchoredAtom4242 chi ∧
      ¬Fin15AnchoredAtom4246 chi ∧
      ¬Fin15AnchoredAtom4250 chi ∧
      ¬Fin15AnchoredAtom4257 chi ∧
      ¬Fin15AnchoredAtom4261 chi ∧
      ¬Fin15AnchoredAtom4265 chi ∧
      ¬Fin15AnchoredAtom4275 chi ∧
      ¬Fin15AnchoredAtom4292 chi ∧
      ¬Fin15AnchoredAtom4296 chi ∧
      ¬Fin15AnchoredAtom4300 chi ∧
      ¬Fin15AnchoredAtom4310 chi ∧
      ¬Fin15AnchoredAtom4330 chi ∧
      ¬Fin15AnchoredAtom4698 chi ∧
      ¬Fin15AnchoredAtom4702 chi ∧
      ¬Fin15AnchoredAtom4706 chi ∧
      ¬Fin15AnchoredAtom4716 chi ∧
      ¬Fin15AnchoredAtom4736 chi ∧
      ¬Fin15AnchoredAtom4771 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 6, 7, 8, 9, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask18377
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2408 Fin15AnchoredAtom2409 Fin15AnchoredAtom2410
    Fin15AnchoredAtom2414 Fin15AnchoredAtom2415 Fin15AnchoredAtom2416 Fin15AnchoredAtom2420
    Fin15AnchoredAtom2421 Fin15AnchoredAtom2425 Fin15AnchoredAtom2429 Fin15AnchoredAtom2436
    Fin15AnchoredAtom2437 Fin15AnchoredAtom2441 Fin15AnchoredAtom2442 Fin15AnchoredAtom2446
    Fin15AnchoredAtom2450 Fin15AnchoredAtom2457 Fin15AnchoredAtom2461 Fin15AnchoredAtom2465
    Fin15AnchoredAtom2475 Fin15AnchoredAtom2696 Fin15AnchoredAtom2697 Fin15AnchoredAtom2701
    Fin15AnchoredAtom2702 Fin15AnchoredAtom2706 Fin15AnchoredAtom2710 Fin15AnchoredAtom2717
    Fin15AnchoredAtom2721 Fin15AnchoredAtom2725 Fin15AnchoredAtom2735 Fin15AnchoredAtom2752
    Fin15AnchoredAtom2756 Fin15AnchoredAtom2760 Fin15AnchoredAtom2770 Fin15AnchoredAtom2790
    Fin15AnchoredAtom4236 Fin15AnchoredAtom4237 Fin15AnchoredAtom4241 Fin15AnchoredAtom4242
    Fin15AnchoredAtom4246 Fin15AnchoredAtom4250 Fin15AnchoredAtom4257 Fin15AnchoredAtom4261
    Fin15AnchoredAtom4265 Fin15AnchoredAtom4275 Fin15AnchoredAtom4292 Fin15AnchoredAtom4296
    Fin15AnchoredAtom4300 Fin15AnchoredAtom4310 Fin15AnchoredAtom4330 Fin15AnchoredAtom4698
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

theorem fin15Anchored_clause31502 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2408 chi ∧
      ¬Fin15AnchoredAtom2409 chi ∧
      ¬Fin15AnchoredAtom2412 chi ∧
      ¬Fin15AnchoredAtom2413 chi ∧
      ¬Fin15AnchoredAtom2415 chi ∧
      ¬Fin15AnchoredAtom2418 chi ∧
      ¬Fin15AnchoredAtom2419 chi ∧
      ¬Fin15AnchoredAtom2423 chi ∧
      ¬Fin15AnchoredAtom2424 chi ∧
      ¬Fin15AnchoredAtom2433 chi ∧
      ¬Fin15AnchoredAtom2436 chi ∧
      ¬Fin15AnchoredAtom2439 chi ∧
      ¬Fin15AnchoredAtom2440 chi ∧
      ¬Fin15AnchoredAtom2444 chi ∧
      ¬Fin15AnchoredAtom2445 chi ∧
      ¬Fin15AnchoredAtom2454 chi ∧
      ¬Fin15AnchoredAtom2459 chi ∧
      ¬Fin15AnchoredAtom2460 chi ∧
      ¬Fin15AnchoredAtom2469 chi ∧
      ¬Fin15AnchoredAtom2479 chi ∧
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
      ¬Fin15AnchoredAtom4236 chi ∧
      ¬Fin15AnchoredAtom4239 chi ∧
      ¬Fin15AnchoredAtom4240 chi ∧
      ¬Fin15AnchoredAtom4244 chi ∧
      ¬Fin15AnchoredAtom4245 chi ∧
      ¬Fin15AnchoredAtom4254 chi ∧
      ¬Fin15AnchoredAtom4259 chi ∧
      ¬Fin15AnchoredAtom4260 chi ∧
      ¬Fin15AnchoredAtom4269 chi ∧
      ¬Fin15AnchoredAtom4279 chi ∧
      ¬Fin15AnchoredAtom4294 chi ∧
      ¬Fin15AnchoredAtom4295 chi ∧
      ¬Fin15AnchoredAtom4304 chi ∧
      ¬Fin15AnchoredAtom4314 chi ∧
      ¬Fin15AnchoredAtom4334 chi ∧
      ¬Fin15AnchoredAtom4700 chi ∧
      ¬Fin15AnchoredAtom4701 chi ∧
      ¬Fin15AnchoredAtom4710 chi ∧
      ¬Fin15AnchoredAtom4720 chi ∧
      ¬Fin15AnchoredAtom4740 chi ∧
      ¬Fin15AnchoredAtom4775 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 6, 7, 8, 9, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13257
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2408 Fin15AnchoredAtom2409 Fin15AnchoredAtom2412
    Fin15AnchoredAtom2413 Fin15AnchoredAtom2415 Fin15AnchoredAtom2418 Fin15AnchoredAtom2419
    Fin15AnchoredAtom2423 Fin15AnchoredAtom2424 Fin15AnchoredAtom2433 Fin15AnchoredAtom2436
    Fin15AnchoredAtom2439 Fin15AnchoredAtom2440 Fin15AnchoredAtom2444 Fin15AnchoredAtom2445
    Fin15AnchoredAtom2454 Fin15AnchoredAtom2459 Fin15AnchoredAtom2460 Fin15AnchoredAtom2469
    Fin15AnchoredAtom2479 Fin15AnchoredAtom2696 Fin15AnchoredAtom2699 Fin15AnchoredAtom2700
    Fin15AnchoredAtom2704 Fin15AnchoredAtom2705 Fin15AnchoredAtom2714 Fin15AnchoredAtom2719
    Fin15AnchoredAtom2720 Fin15AnchoredAtom2729 Fin15AnchoredAtom2739 Fin15AnchoredAtom2754
    Fin15AnchoredAtom2755 Fin15AnchoredAtom2764 Fin15AnchoredAtom2774 Fin15AnchoredAtom2794
    Fin15AnchoredAtom4236 Fin15AnchoredAtom4239 Fin15AnchoredAtom4240 Fin15AnchoredAtom4244
    Fin15AnchoredAtom4245 Fin15AnchoredAtom4254 Fin15AnchoredAtom4259 Fin15AnchoredAtom4260
    Fin15AnchoredAtom4269 Fin15AnchoredAtom4279 Fin15AnchoredAtom4294 Fin15AnchoredAtom4295
    Fin15AnchoredAtom4304 Fin15AnchoredAtom4314 Fin15AnchoredAtom4334 Fin15AnchoredAtom4700
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

theorem fin15Anchored_clause31503 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2408 chi ∧
      ¬Fin15AnchoredAtom2409 chi ∧
      ¬Fin15AnchoredAtom2412 chi ∧
      ¬Fin15AnchoredAtom2414 chi ∧
      ¬Fin15AnchoredAtom2415 chi ∧
      ¬Fin15AnchoredAtom2418 chi ∧
      ¬Fin15AnchoredAtom2420 chi ∧
      ¬Fin15AnchoredAtom2423 chi ∧
      ¬Fin15AnchoredAtom2425 chi ∧
      ¬Fin15AnchoredAtom2434 chi ∧
      ¬Fin15AnchoredAtom2436 chi ∧
      ¬Fin15AnchoredAtom2439 chi ∧
      ¬Fin15AnchoredAtom2441 chi ∧
      ¬Fin15AnchoredAtom2444 chi ∧
      ¬Fin15AnchoredAtom2446 chi ∧
      ¬Fin15AnchoredAtom2455 chi ∧
      ¬Fin15AnchoredAtom2459 chi ∧
      ¬Fin15AnchoredAtom2461 chi ∧
      ¬Fin15AnchoredAtom2470 chi ∧
      ¬Fin15AnchoredAtom2480 chi ∧
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
      ¬Fin15AnchoredAtom4236 chi ∧
      ¬Fin15AnchoredAtom4239 chi ∧
      ¬Fin15AnchoredAtom4241 chi ∧
      ¬Fin15AnchoredAtom4244 chi ∧
      ¬Fin15AnchoredAtom4246 chi ∧
      ¬Fin15AnchoredAtom4255 chi ∧
      ¬Fin15AnchoredAtom4259 chi ∧
      ¬Fin15AnchoredAtom4261 chi ∧
      ¬Fin15AnchoredAtom4270 chi ∧
      ¬Fin15AnchoredAtom4280 chi ∧
      ¬Fin15AnchoredAtom4294 chi ∧
      ¬Fin15AnchoredAtom4296 chi ∧
      ¬Fin15AnchoredAtom4305 chi ∧
      ¬Fin15AnchoredAtom4315 chi ∧
      ¬Fin15AnchoredAtom4335 chi ∧
      ¬Fin15AnchoredAtom4700 chi ∧
      ¬Fin15AnchoredAtom4702 chi ∧
      ¬Fin15AnchoredAtom4711 chi ∧
      ¬Fin15AnchoredAtom4721 chi ∧
      ¬Fin15AnchoredAtom4741 chi ∧
      ¬Fin15AnchoredAtom4776 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 6, 7, 8, 9, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21449
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2408 Fin15AnchoredAtom2409 Fin15AnchoredAtom2412
    Fin15AnchoredAtom2414 Fin15AnchoredAtom2415 Fin15AnchoredAtom2418 Fin15AnchoredAtom2420
    Fin15AnchoredAtom2423 Fin15AnchoredAtom2425 Fin15AnchoredAtom2434 Fin15AnchoredAtom2436
    Fin15AnchoredAtom2439 Fin15AnchoredAtom2441 Fin15AnchoredAtom2444 Fin15AnchoredAtom2446
    Fin15AnchoredAtom2455 Fin15AnchoredAtom2459 Fin15AnchoredAtom2461 Fin15AnchoredAtom2470
    Fin15AnchoredAtom2480 Fin15AnchoredAtom2696 Fin15AnchoredAtom2699 Fin15AnchoredAtom2701
    Fin15AnchoredAtom2704 Fin15AnchoredAtom2706 Fin15AnchoredAtom2715 Fin15AnchoredAtom2719
    Fin15AnchoredAtom2721 Fin15AnchoredAtom2730 Fin15AnchoredAtom2740 Fin15AnchoredAtom2754
    Fin15AnchoredAtom2756 Fin15AnchoredAtom2765 Fin15AnchoredAtom2775 Fin15AnchoredAtom2795
    Fin15AnchoredAtom4236 Fin15AnchoredAtom4239 Fin15AnchoredAtom4241 Fin15AnchoredAtom4244
    Fin15AnchoredAtom4246 Fin15AnchoredAtom4255 Fin15AnchoredAtom4259 Fin15AnchoredAtom4261
    Fin15AnchoredAtom4270 Fin15AnchoredAtom4280 Fin15AnchoredAtom4294 Fin15AnchoredAtom4296
    Fin15AnchoredAtom4305 Fin15AnchoredAtom4315 Fin15AnchoredAtom4335 Fin15AnchoredAtom4700
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

theorem fin15Anchored_clause31504 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2408 chi ∧
      ¬Fin15AnchoredAtom2410 chi ∧
      ¬Fin15AnchoredAtom2412 chi ∧
      ¬Fin15AnchoredAtom2413 chi ∧
      ¬Fin15AnchoredAtom2416 chi ∧
      ¬Fin15AnchoredAtom2418 chi ∧
      ¬Fin15AnchoredAtom2419 chi ∧
      ¬Fin15AnchoredAtom2427 chi ∧
      ¬Fin15AnchoredAtom2428 chi ∧
      ¬Fin15AnchoredAtom2433 chi ∧
      ¬Fin15AnchoredAtom2437 chi ∧
      ¬Fin15AnchoredAtom2439 chi ∧
      ¬Fin15AnchoredAtom2440 chi ∧
      ¬Fin15AnchoredAtom2448 chi ∧
      ¬Fin15AnchoredAtom2449 chi ∧
      ¬Fin15AnchoredAtom2454 chi ∧
      ¬Fin15AnchoredAtom2463 chi ∧
      ¬Fin15AnchoredAtom2464 chi ∧
      ¬Fin15AnchoredAtom2469 chi ∧
      ¬Fin15AnchoredAtom2485 chi ∧
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
      ¬Fin15AnchoredAtom4237 chi ∧
      ¬Fin15AnchoredAtom4239 chi ∧
      ¬Fin15AnchoredAtom4240 chi ∧
      ¬Fin15AnchoredAtom4248 chi ∧
      ¬Fin15AnchoredAtom4249 chi ∧
      ¬Fin15AnchoredAtom4254 chi ∧
      ¬Fin15AnchoredAtom4263 chi ∧
      ¬Fin15AnchoredAtom4264 chi ∧
      ¬Fin15AnchoredAtom4269 chi ∧
      ¬Fin15AnchoredAtom4285 chi ∧
      ¬Fin15AnchoredAtom4298 chi ∧
      ¬Fin15AnchoredAtom4299 chi ∧
      ¬Fin15AnchoredAtom4304 chi ∧
      ¬Fin15AnchoredAtom4320 chi ∧
      ¬Fin15AnchoredAtom4340 chi ∧
      ¬Fin15AnchoredAtom4704 chi ∧
      ¬Fin15AnchoredAtom4705 chi ∧
      ¬Fin15AnchoredAtom4710 chi ∧
      ¬Fin15AnchoredAtom4726 chi ∧
      ¬Fin15AnchoredAtom4746 chi ∧
      ¬Fin15AnchoredAtom4781 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 6, 7, 8, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13769
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2408 Fin15AnchoredAtom2410 Fin15AnchoredAtom2412
    Fin15AnchoredAtom2413 Fin15AnchoredAtom2416 Fin15AnchoredAtom2418 Fin15AnchoredAtom2419
    Fin15AnchoredAtom2427 Fin15AnchoredAtom2428 Fin15AnchoredAtom2433 Fin15AnchoredAtom2437
    Fin15AnchoredAtom2439 Fin15AnchoredAtom2440 Fin15AnchoredAtom2448 Fin15AnchoredAtom2449
    Fin15AnchoredAtom2454 Fin15AnchoredAtom2463 Fin15AnchoredAtom2464 Fin15AnchoredAtom2469
    Fin15AnchoredAtom2485 Fin15AnchoredAtom2697 Fin15AnchoredAtom2699 Fin15AnchoredAtom2700
    Fin15AnchoredAtom2708 Fin15AnchoredAtom2709 Fin15AnchoredAtom2714 Fin15AnchoredAtom2723
    Fin15AnchoredAtom2724 Fin15AnchoredAtom2729 Fin15AnchoredAtom2745 Fin15AnchoredAtom2758
    Fin15AnchoredAtom2759 Fin15AnchoredAtom2764 Fin15AnchoredAtom2780 Fin15AnchoredAtom2800
    Fin15AnchoredAtom4237 Fin15AnchoredAtom4239 Fin15AnchoredAtom4240 Fin15AnchoredAtom4248
    Fin15AnchoredAtom4249 Fin15AnchoredAtom4254 Fin15AnchoredAtom4263 Fin15AnchoredAtom4264
    Fin15AnchoredAtom4269 Fin15AnchoredAtom4285 Fin15AnchoredAtom4298 Fin15AnchoredAtom4299
    Fin15AnchoredAtom4304 Fin15AnchoredAtom4320 Fin15AnchoredAtom4340 Fin15AnchoredAtom4704
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

theorem fin15Anchored_clause31505 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2408 chi ∧
      ¬Fin15AnchoredAtom2410 chi ∧
      ¬Fin15AnchoredAtom2412 chi ∧
      ¬Fin15AnchoredAtom2414 chi ∧
      ¬Fin15AnchoredAtom2416 chi ∧
      ¬Fin15AnchoredAtom2418 chi ∧
      ¬Fin15AnchoredAtom2420 chi ∧
      ¬Fin15AnchoredAtom2427 chi ∧
      ¬Fin15AnchoredAtom2429 chi ∧
      ¬Fin15AnchoredAtom2434 chi ∧
      ¬Fin15AnchoredAtom2437 chi ∧
      ¬Fin15AnchoredAtom2439 chi ∧
      ¬Fin15AnchoredAtom2441 chi ∧
      ¬Fin15AnchoredAtom2448 chi ∧
      ¬Fin15AnchoredAtom2450 chi ∧
      ¬Fin15AnchoredAtom2455 chi ∧
      ¬Fin15AnchoredAtom2463 chi ∧
      ¬Fin15AnchoredAtom2465 chi ∧
      ¬Fin15AnchoredAtom2470 chi ∧
      ¬Fin15AnchoredAtom2486 chi ∧
      ¬Fin15AnchoredAtom2697 chi ∧
      ¬Fin15AnchoredAtom2699 chi ∧
      ¬Fin15AnchoredAtom2701 chi ∧
      ¬Fin15AnchoredAtom2708 chi ∧
      ¬Fin15AnchoredAtom2710 chi ∧
      ¬Fin15AnchoredAtom2715 chi ∧
      ¬Fin15AnchoredAtom2723 chi ∧
      ¬Fin15AnchoredAtom2725 chi ∧
      ¬Fin15AnchoredAtom2730 chi ∧
      ¬Fin15AnchoredAtom2746 chi ∧
      ¬Fin15AnchoredAtom2758 chi ∧
      ¬Fin15AnchoredAtom2760 chi ∧
      ¬Fin15AnchoredAtom2765 chi ∧
      ¬Fin15AnchoredAtom2781 chi ∧
      ¬Fin15AnchoredAtom2801 chi ∧
      ¬Fin15AnchoredAtom4237 chi ∧
      ¬Fin15AnchoredAtom4239 chi ∧
      ¬Fin15AnchoredAtom4241 chi ∧
      ¬Fin15AnchoredAtom4248 chi ∧
      ¬Fin15AnchoredAtom4250 chi ∧
      ¬Fin15AnchoredAtom4255 chi ∧
      ¬Fin15AnchoredAtom4263 chi ∧
      ¬Fin15AnchoredAtom4265 chi ∧
      ¬Fin15AnchoredAtom4270 chi ∧
      ¬Fin15AnchoredAtom4286 chi ∧
      ¬Fin15AnchoredAtom4298 chi ∧
      ¬Fin15AnchoredAtom4300 chi ∧
      ¬Fin15AnchoredAtom4305 chi ∧
      ¬Fin15AnchoredAtom4321 chi ∧
      ¬Fin15AnchoredAtom4341 chi ∧
      ¬Fin15AnchoredAtom4704 chi ∧
      ¬Fin15AnchoredAtom4706 chi ∧
      ¬Fin15AnchoredAtom4711 chi ∧
      ¬Fin15AnchoredAtom4727 chi ∧
      ¬Fin15AnchoredAtom4747 chi ∧
      ¬Fin15AnchoredAtom4782 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 6, 7, 8, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21961
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2408 Fin15AnchoredAtom2410 Fin15AnchoredAtom2412
    Fin15AnchoredAtom2414 Fin15AnchoredAtom2416 Fin15AnchoredAtom2418 Fin15AnchoredAtom2420
    Fin15AnchoredAtom2427 Fin15AnchoredAtom2429 Fin15AnchoredAtom2434 Fin15AnchoredAtom2437
    Fin15AnchoredAtom2439 Fin15AnchoredAtom2441 Fin15AnchoredAtom2448 Fin15AnchoredAtom2450
    Fin15AnchoredAtom2455 Fin15AnchoredAtom2463 Fin15AnchoredAtom2465 Fin15AnchoredAtom2470
    Fin15AnchoredAtom2486 Fin15AnchoredAtom2697 Fin15AnchoredAtom2699 Fin15AnchoredAtom2701
    Fin15AnchoredAtom2708 Fin15AnchoredAtom2710 Fin15AnchoredAtom2715 Fin15AnchoredAtom2723
    Fin15AnchoredAtom2725 Fin15AnchoredAtom2730 Fin15AnchoredAtom2746 Fin15AnchoredAtom2758
    Fin15AnchoredAtom2760 Fin15AnchoredAtom2765 Fin15AnchoredAtom2781 Fin15AnchoredAtom2801
    Fin15AnchoredAtom4237 Fin15AnchoredAtom4239 Fin15AnchoredAtom4241 Fin15AnchoredAtom4248
    Fin15AnchoredAtom4250 Fin15AnchoredAtom4255 Fin15AnchoredAtom4263 Fin15AnchoredAtom4265
    Fin15AnchoredAtom4270 Fin15AnchoredAtom4286 Fin15AnchoredAtom4298 Fin15AnchoredAtom4300
    Fin15AnchoredAtom4305 Fin15AnchoredAtom4321 Fin15AnchoredAtom4341 Fin15AnchoredAtom4704
    Fin15AnchoredAtom4706 Fin15AnchoredAtom4711 Fin15AnchoredAtom4727 Fin15AnchoredAtom4747
    Fin15AnchoredAtom4782 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31506 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2409 chi ∧
      ¬Fin15AnchoredAtom2410 chi ∧
      ¬Fin15AnchoredAtom2412 chi ∧
      ¬Fin15AnchoredAtom2413 chi ∧
      ¬Fin15AnchoredAtom2421 chi ∧
      ¬Fin15AnchoredAtom2423 chi ∧
      ¬Fin15AnchoredAtom2424 chi ∧
      ¬Fin15AnchoredAtom2427 chi ∧
      ¬Fin15AnchoredAtom2428 chi ∧
      ¬Fin15AnchoredAtom2433 chi ∧
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
      ¬Fin15AnchoredAtom4242 chi ∧
      ¬Fin15AnchoredAtom4244 chi ∧
      ¬Fin15AnchoredAtom4245 chi ∧
      ¬Fin15AnchoredAtom4248 chi ∧
      ¬Fin15AnchoredAtom4249 chi ∧
      ¬Fin15AnchoredAtom4254 chi ∧
      ¬Fin15AnchoredAtom4273 chi ∧
      ¬Fin15AnchoredAtom4274 chi ∧
      ¬Fin15AnchoredAtom4279 chi ∧
      ¬Fin15AnchoredAtom4285 chi ∧
      ¬Fin15AnchoredAtom4308 chi ∧
      ¬Fin15AnchoredAtom4309 chi ∧
      ¬Fin15AnchoredAtom4314 chi ∧
      ¬Fin15AnchoredAtom4320 chi ∧
      ¬Fin15AnchoredAtom4350 chi ∧
      ¬Fin15AnchoredAtom4714 chi ∧
      ¬Fin15AnchoredAtom4715 chi ∧
      ¬Fin15AnchoredAtom4720 chi ∧
      ¬Fin15AnchoredAtom4726 chi ∧
      ¬Fin15AnchoredAtom4756 chi ∧
      ¬Fin15AnchoredAtom4791 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 6, 7, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask14025
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2409 Fin15AnchoredAtom2410 Fin15AnchoredAtom2412
    Fin15AnchoredAtom2413 Fin15AnchoredAtom2421 Fin15AnchoredAtom2423 Fin15AnchoredAtom2424
    Fin15AnchoredAtom2427 Fin15AnchoredAtom2428 Fin15AnchoredAtom2433 Fin15AnchoredAtom2442
    Fin15AnchoredAtom2444 Fin15AnchoredAtom2445 Fin15AnchoredAtom2448 Fin15AnchoredAtom2449
    Fin15AnchoredAtom2454 Fin15AnchoredAtom2473 Fin15AnchoredAtom2474 Fin15AnchoredAtom2479
    Fin15AnchoredAtom2485 Fin15AnchoredAtom2702 Fin15AnchoredAtom2704 Fin15AnchoredAtom2705
    Fin15AnchoredAtom2708 Fin15AnchoredAtom2709 Fin15AnchoredAtom2714 Fin15AnchoredAtom2733
    Fin15AnchoredAtom2734 Fin15AnchoredAtom2739 Fin15AnchoredAtom2745 Fin15AnchoredAtom2768
    Fin15AnchoredAtom2769 Fin15AnchoredAtom2774 Fin15AnchoredAtom2780 Fin15AnchoredAtom2810
    Fin15AnchoredAtom4242 Fin15AnchoredAtom4244 Fin15AnchoredAtom4245 Fin15AnchoredAtom4248
    Fin15AnchoredAtom4249 Fin15AnchoredAtom4254 Fin15AnchoredAtom4273 Fin15AnchoredAtom4274
    Fin15AnchoredAtom4279 Fin15AnchoredAtom4285 Fin15AnchoredAtom4308 Fin15AnchoredAtom4309
    Fin15AnchoredAtom4314 Fin15AnchoredAtom4320 Fin15AnchoredAtom4350 Fin15AnchoredAtom4714
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

theorem fin15Anchored_clause31507 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2409 chi ∧
      ¬Fin15AnchoredAtom2410 chi ∧
      ¬Fin15AnchoredAtom2412 chi ∧
      ¬Fin15AnchoredAtom2414 chi ∧
      ¬Fin15AnchoredAtom2421 chi ∧
      ¬Fin15AnchoredAtom2423 chi ∧
      ¬Fin15AnchoredAtom2425 chi ∧
      ¬Fin15AnchoredAtom2427 chi ∧
      ¬Fin15AnchoredAtom2429 chi ∧
      ¬Fin15AnchoredAtom2434 chi ∧
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
      ¬Fin15AnchoredAtom4242 chi ∧
      ¬Fin15AnchoredAtom4244 chi ∧
      ¬Fin15AnchoredAtom4246 chi ∧
      ¬Fin15AnchoredAtom4248 chi ∧
      ¬Fin15AnchoredAtom4250 chi ∧
      ¬Fin15AnchoredAtom4255 chi ∧
      ¬Fin15AnchoredAtom4273 chi ∧
      ¬Fin15AnchoredAtom4275 chi ∧
      ¬Fin15AnchoredAtom4280 chi ∧
      ¬Fin15AnchoredAtom4286 chi ∧
      ¬Fin15AnchoredAtom4308 chi ∧
      ¬Fin15AnchoredAtom4310 chi ∧
      ¬Fin15AnchoredAtom4315 chi ∧
      ¬Fin15AnchoredAtom4321 chi ∧
      ¬Fin15AnchoredAtom4351 chi ∧
      ¬Fin15AnchoredAtom4714 chi ∧
      ¬Fin15AnchoredAtom4716 chi ∧
      ¬Fin15AnchoredAtom4721 chi ∧
      ¬Fin15AnchoredAtom4727 chi ∧
      ¬Fin15AnchoredAtom4757 chi ∧
      ¬Fin15AnchoredAtom4792 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 6, 7, 9, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22217
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2409 Fin15AnchoredAtom2410 Fin15AnchoredAtom2412
    Fin15AnchoredAtom2414 Fin15AnchoredAtom2421 Fin15AnchoredAtom2423 Fin15AnchoredAtom2425
    Fin15AnchoredAtom2427 Fin15AnchoredAtom2429 Fin15AnchoredAtom2434 Fin15AnchoredAtom2442
    Fin15AnchoredAtom2444 Fin15AnchoredAtom2446 Fin15AnchoredAtom2448 Fin15AnchoredAtom2450
    Fin15AnchoredAtom2455 Fin15AnchoredAtom2473 Fin15AnchoredAtom2475 Fin15AnchoredAtom2480
    Fin15AnchoredAtom2486 Fin15AnchoredAtom2702 Fin15AnchoredAtom2704 Fin15AnchoredAtom2706
    Fin15AnchoredAtom2708 Fin15AnchoredAtom2710 Fin15AnchoredAtom2715 Fin15AnchoredAtom2733
    Fin15AnchoredAtom2735 Fin15AnchoredAtom2740 Fin15AnchoredAtom2746 Fin15AnchoredAtom2768
    Fin15AnchoredAtom2770 Fin15AnchoredAtom2775 Fin15AnchoredAtom2781 Fin15AnchoredAtom2811
    Fin15AnchoredAtom4242 Fin15AnchoredAtom4244 Fin15AnchoredAtom4246 Fin15AnchoredAtom4248
    Fin15AnchoredAtom4250 Fin15AnchoredAtom4255 Fin15AnchoredAtom4273 Fin15AnchoredAtom4275
    Fin15AnchoredAtom4280 Fin15AnchoredAtom4286 Fin15AnchoredAtom4308 Fin15AnchoredAtom4310
    Fin15AnchoredAtom4315 Fin15AnchoredAtom4321 Fin15AnchoredAtom4351 Fin15AnchoredAtom4714
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

theorem fin15Anchored_clause31508 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2409 chi ∧
      ¬Fin15AnchoredAtom2410 chi ∧
      ¬Fin15AnchoredAtom2413 chi ∧
      ¬Fin15AnchoredAtom2414 chi ∧
      ¬Fin15AnchoredAtom2421 chi ∧
      ¬Fin15AnchoredAtom2424 chi ∧
      ¬Fin15AnchoredAtom2425 chi ∧
      ¬Fin15AnchoredAtom2428 chi ∧
      ¬Fin15AnchoredAtom2429 chi ∧
      ¬Fin15AnchoredAtom2435 chi ∧
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
      ¬Fin15AnchoredAtom4242 chi ∧
      ¬Fin15AnchoredAtom4245 chi ∧
      ¬Fin15AnchoredAtom4246 chi ∧
      ¬Fin15AnchoredAtom4249 chi ∧
      ¬Fin15AnchoredAtom4250 chi ∧
      ¬Fin15AnchoredAtom4256 chi ∧
      ¬Fin15AnchoredAtom4274 chi ∧
      ¬Fin15AnchoredAtom4275 chi ∧
      ¬Fin15AnchoredAtom4281 chi ∧
      ¬Fin15AnchoredAtom4287 chi ∧
      ¬Fin15AnchoredAtom4309 chi ∧
      ¬Fin15AnchoredAtom4310 chi ∧
      ¬Fin15AnchoredAtom4316 chi ∧
      ¬Fin15AnchoredAtom4322 chi ∧
      ¬Fin15AnchoredAtom4352 chi ∧
      ¬Fin15AnchoredAtom4715 chi ∧
      ¬Fin15AnchoredAtom4716 chi ∧
      ¬Fin15AnchoredAtom4722 chi ∧
      ¬Fin15AnchoredAtom4728 chi ∧
      ¬Fin15AnchoredAtom4758 chi ∧
      ¬Fin15AnchoredAtom4793 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 6, 7, 9, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26313
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2409 Fin15AnchoredAtom2410 Fin15AnchoredAtom2413
    Fin15AnchoredAtom2414 Fin15AnchoredAtom2421 Fin15AnchoredAtom2424 Fin15AnchoredAtom2425
    Fin15AnchoredAtom2428 Fin15AnchoredAtom2429 Fin15AnchoredAtom2435 Fin15AnchoredAtom2442
    Fin15AnchoredAtom2445 Fin15AnchoredAtom2446 Fin15AnchoredAtom2449 Fin15AnchoredAtom2450
    Fin15AnchoredAtom2456 Fin15AnchoredAtom2474 Fin15AnchoredAtom2475 Fin15AnchoredAtom2481
    Fin15AnchoredAtom2487 Fin15AnchoredAtom2702 Fin15AnchoredAtom2705 Fin15AnchoredAtom2706
    Fin15AnchoredAtom2709 Fin15AnchoredAtom2710 Fin15AnchoredAtom2716 Fin15AnchoredAtom2734
    Fin15AnchoredAtom2735 Fin15AnchoredAtom2741 Fin15AnchoredAtom2747 Fin15AnchoredAtom2769
    Fin15AnchoredAtom2770 Fin15AnchoredAtom2776 Fin15AnchoredAtom2782 Fin15AnchoredAtom2812
    Fin15AnchoredAtom4242 Fin15AnchoredAtom4245 Fin15AnchoredAtom4246 Fin15AnchoredAtom4249
    Fin15AnchoredAtom4250 Fin15AnchoredAtom4256 Fin15AnchoredAtom4274 Fin15AnchoredAtom4275
    Fin15AnchoredAtom4281 Fin15AnchoredAtom4287 Fin15AnchoredAtom4309 Fin15AnchoredAtom4310
    Fin15AnchoredAtom4316 Fin15AnchoredAtom4322 Fin15AnchoredAtom4352 Fin15AnchoredAtom4715
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

theorem fin15Anchored_clause31509 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2409 chi ∧
      ¬Fin15AnchoredAtom2412 chi ∧
      ¬Fin15AnchoredAtom2413 chi ∧
      ¬Fin15AnchoredAtom2414 chi ∧
      ¬Fin15AnchoredAtom2423 chi ∧
      ¬Fin15AnchoredAtom2424 chi ∧
      ¬Fin15AnchoredAtom2425 chi ∧
      ¬Fin15AnchoredAtom2433 chi ∧
      ¬Fin15AnchoredAtom2434 chi ∧
      ¬Fin15AnchoredAtom2435 chi ∧
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
      ¬Fin15AnchoredAtom4244 chi ∧
      ¬Fin15AnchoredAtom4245 chi ∧
      ¬Fin15AnchoredAtom4246 chi ∧
      ¬Fin15AnchoredAtom4254 chi ∧
      ¬Fin15AnchoredAtom4255 chi ∧
      ¬Fin15AnchoredAtom4256 chi ∧
      ¬Fin15AnchoredAtom4279 chi ∧
      ¬Fin15AnchoredAtom4280 chi ∧
      ¬Fin15AnchoredAtom4281 chi ∧
      ¬Fin15AnchoredAtom4291 chi ∧
      ¬Fin15AnchoredAtom4314 chi ∧
      ¬Fin15AnchoredAtom4315 chi ∧
      ¬Fin15AnchoredAtom4316 chi ∧
      ¬Fin15AnchoredAtom4326 chi ∧
      ¬Fin15AnchoredAtom4356 chi ∧
      ¬Fin15AnchoredAtom4720 chi ∧
      ¬Fin15AnchoredAtom4721 chi ∧
      ¬Fin15AnchoredAtom4722 chi ∧
      ¬Fin15AnchoredAtom4732 chi ∧
      ¬Fin15AnchoredAtom4762 chi ∧
      ¬Fin15AnchoredAtom4797 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 6, 7, 9, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29385
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2409 Fin15AnchoredAtom2412 Fin15AnchoredAtom2413
    Fin15AnchoredAtom2414 Fin15AnchoredAtom2423 Fin15AnchoredAtom2424 Fin15AnchoredAtom2425
    Fin15AnchoredAtom2433 Fin15AnchoredAtom2434 Fin15AnchoredAtom2435 Fin15AnchoredAtom2444
    Fin15AnchoredAtom2445 Fin15AnchoredAtom2446 Fin15AnchoredAtom2454 Fin15AnchoredAtom2455
    Fin15AnchoredAtom2456 Fin15AnchoredAtom2479 Fin15AnchoredAtom2480 Fin15AnchoredAtom2481
    Fin15AnchoredAtom2491 Fin15AnchoredAtom2704 Fin15AnchoredAtom2705 Fin15AnchoredAtom2706
    Fin15AnchoredAtom2714 Fin15AnchoredAtom2715 Fin15AnchoredAtom2716 Fin15AnchoredAtom2739
    Fin15AnchoredAtom2740 Fin15AnchoredAtom2741 Fin15AnchoredAtom2751 Fin15AnchoredAtom2774
    Fin15AnchoredAtom2775 Fin15AnchoredAtom2776 Fin15AnchoredAtom2786 Fin15AnchoredAtom2816
    Fin15AnchoredAtom4244 Fin15AnchoredAtom4245 Fin15AnchoredAtom4246 Fin15AnchoredAtom4254
    Fin15AnchoredAtom4255 Fin15AnchoredAtom4256 Fin15AnchoredAtom4279 Fin15AnchoredAtom4280
    Fin15AnchoredAtom4281 Fin15AnchoredAtom4291 Fin15AnchoredAtom4314 Fin15AnchoredAtom4315
    Fin15AnchoredAtom4316 Fin15AnchoredAtom4326 Fin15AnchoredAtom4356 Fin15AnchoredAtom4720
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

theorem fin15Anchored_clause31510 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2410 chi ∧
      ¬Fin15AnchoredAtom2412 chi ∧
      ¬Fin15AnchoredAtom2413 chi ∧
      ¬Fin15AnchoredAtom2414 chi ∧
      ¬Fin15AnchoredAtom2427 chi ∧
      ¬Fin15AnchoredAtom2428 chi ∧
      ¬Fin15AnchoredAtom2429 chi ∧
      ¬Fin15AnchoredAtom2433 chi ∧
      ¬Fin15AnchoredAtom2434 chi ∧
      ¬Fin15AnchoredAtom2435 chi ∧
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
      ¬Fin15AnchoredAtom4248 chi ∧
      ¬Fin15AnchoredAtom4249 chi ∧
      ¬Fin15AnchoredAtom4250 chi ∧
      ¬Fin15AnchoredAtom4254 chi ∧
      ¬Fin15AnchoredAtom4255 chi ∧
      ¬Fin15AnchoredAtom4256 chi ∧
      ¬Fin15AnchoredAtom4285 chi ∧
      ¬Fin15AnchoredAtom4286 chi ∧
      ¬Fin15AnchoredAtom4287 chi ∧
      ¬Fin15AnchoredAtom4291 chi ∧
      ¬Fin15AnchoredAtom4320 chi ∧
      ¬Fin15AnchoredAtom4321 chi ∧
      ¬Fin15AnchoredAtom4322 chi ∧
      ¬Fin15AnchoredAtom4326 chi ∧
      ¬Fin15AnchoredAtom4360 chi ∧
      ¬Fin15AnchoredAtom4726 chi ∧
      ¬Fin15AnchoredAtom4727 chi ∧
      ¬Fin15AnchoredAtom4728 chi ∧
      ¬Fin15AnchoredAtom4732 chi ∧
      ¬Fin15AnchoredAtom4766 chi ∧
      ¬Fin15AnchoredAtom4801 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 6, 7, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29897
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2410 Fin15AnchoredAtom2412 Fin15AnchoredAtom2413
    Fin15AnchoredAtom2414 Fin15AnchoredAtom2427 Fin15AnchoredAtom2428 Fin15AnchoredAtom2429
    Fin15AnchoredAtom2433 Fin15AnchoredAtom2434 Fin15AnchoredAtom2435 Fin15AnchoredAtom2448
    Fin15AnchoredAtom2449 Fin15AnchoredAtom2450 Fin15AnchoredAtom2454 Fin15AnchoredAtom2455
    Fin15AnchoredAtom2456 Fin15AnchoredAtom2485 Fin15AnchoredAtom2486 Fin15AnchoredAtom2487
    Fin15AnchoredAtom2491 Fin15AnchoredAtom2708 Fin15AnchoredAtom2709 Fin15AnchoredAtom2710
    Fin15AnchoredAtom2714 Fin15AnchoredAtom2715 Fin15AnchoredAtom2716 Fin15AnchoredAtom2745
    Fin15AnchoredAtom2746 Fin15AnchoredAtom2747 Fin15AnchoredAtom2751 Fin15AnchoredAtom2780
    Fin15AnchoredAtom2781 Fin15AnchoredAtom2782 Fin15AnchoredAtom2786 Fin15AnchoredAtom2820
    Fin15AnchoredAtom4248 Fin15AnchoredAtom4249 Fin15AnchoredAtom4250 Fin15AnchoredAtom4254
    Fin15AnchoredAtom4255 Fin15AnchoredAtom4256 Fin15AnchoredAtom4285 Fin15AnchoredAtom4286
    Fin15AnchoredAtom4287 Fin15AnchoredAtom4291 Fin15AnchoredAtom4320 Fin15AnchoredAtom4321
    Fin15AnchoredAtom4322 Fin15AnchoredAtom4326 Fin15AnchoredAtom4360 Fin15AnchoredAtom4726
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

theorem fin15Anchored_clause31511 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2415 chi ∧
      ¬Fin15AnchoredAtom2416 chi ∧
      ¬Fin15AnchoredAtom2418 chi ∧
      ¬Fin15AnchoredAtom2419 chi ∧
      ¬Fin15AnchoredAtom2421 chi ∧
      ¬Fin15AnchoredAtom2423 chi ∧
      ¬Fin15AnchoredAtom2424 chi ∧
      ¬Fin15AnchoredAtom2427 chi ∧
      ¬Fin15AnchoredAtom2428 chi ∧
      ¬Fin15AnchoredAtom2433 chi ∧
      ¬Fin15AnchoredAtom2457 chi ∧
      ¬Fin15AnchoredAtom2459 chi ∧
      ¬Fin15AnchoredAtom2460 chi ∧
      ¬Fin15AnchoredAtom2463 chi ∧
      ¬Fin15AnchoredAtom2464 chi ∧
      ¬Fin15AnchoredAtom2469 chi ∧
      ¬Fin15AnchoredAtom2473 chi ∧
      ¬Fin15AnchoredAtom2474 chi ∧
      ¬Fin15AnchoredAtom2479 chi ∧
      ¬Fin15AnchoredAtom2485 chi ∧
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
      ¬Fin15AnchoredAtom4257 chi ∧
      ¬Fin15AnchoredAtom4259 chi ∧
      ¬Fin15AnchoredAtom4260 chi ∧
      ¬Fin15AnchoredAtom4263 chi ∧
      ¬Fin15AnchoredAtom4264 chi ∧
      ¬Fin15AnchoredAtom4269 chi ∧
      ¬Fin15AnchoredAtom4273 chi ∧
      ¬Fin15AnchoredAtom4274 chi ∧
      ¬Fin15AnchoredAtom4279 chi ∧
      ¬Fin15AnchoredAtom4285 chi ∧
      ¬Fin15AnchoredAtom4328 chi ∧
      ¬Fin15AnchoredAtom4329 chi ∧
      ¬Fin15AnchoredAtom4334 chi ∧
      ¬Fin15AnchoredAtom4340 chi ∧
      ¬Fin15AnchoredAtom4350 chi ∧
      ¬Fin15AnchoredAtom4734 chi ∧
      ¬Fin15AnchoredAtom4735 chi ∧
      ¬Fin15AnchoredAtom4740 chi ∧
      ¬Fin15AnchoredAtom4746 chi ∧
      ¬Fin15AnchoredAtom4756 chi ∧
      ¬Fin15AnchoredAtom4806 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 6, 8, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask14153
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2415 Fin15AnchoredAtom2416 Fin15AnchoredAtom2418
    Fin15AnchoredAtom2419 Fin15AnchoredAtom2421 Fin15AnchoredAtom2423 Fin15AnchoredAtom2424
    Fin15AnchoredAtom2427 Fin15AnchoredAtom2428 Fin15AnchoredAtom2433 Fin15AnchoredAtom2457
    Fin15AnchoredAtom2459 Fin15AnchoredAtom2460 Fin15AnchoredAtom2463 Fin15AnchoredAtom2464
    Fin15AnchoredAtom2469 Fin15AnchoredAtom2473 Fin15AnchoredAtom2474 Fin15AnchoredAtom2479
    Fin15AnchoredAtom2485 Fin15AnchoredAtom2717 Fin15AnchoredAtom2719 Fin15AnchoredAtom2720
    Fin15AnchoredAtom2723 Fin15AnchoredAtom2724 Fin15AnchoredAtom2729 Fin15AnchoredAtom2733
    Fin15AnchoredAtom2734 Fin15AnchoredAtom2739 Fin15AnchoredAtom2745 Fin15AnchoredAtom2788
    Fin15AnchoredAtom2789 Fin15AnchoredAtom2794 Fin15AnchoredAtom2800 Fin15AnchoredAtom2810
    Fin15AnchoredAtom4257 Fin15AnchoredAtom4259 Fin15AnchoredAtom4260 Fin15AnchoredAtom4263
    Fin15AnchoredAtom4264 Fin15AnchoredAtom4269 Fin15AnchoredAtom4273 Fin15AnchoredAtom4274
    Fin15AnchoredAtom4279 Fin15AnchoredAtom4285 Fin15AnchoredAtom4328 Fin15AnchoredAtom4329
    Fin15AnchoredAtom4334 Fin15AnchoredAtom4340 Fin15AnchoredAtom4350 Fin15AnchoredAtom4734
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

theorem fin15Anchored_clause31512 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2415 chi ∧
      ¬Fin15AnchoredAtom2416 chi ∧
      ¬Fin15AnchoredAtom2418 chi ∧
      ¬Fin15AnchoredAtom2420 chi ∧
      ¬Fin15AnchoredAtom2421 chi ∧
      ¬Fin15AnchoredAtom2423 chi ∧
      ¬Fin15AnchoredAtom2425 chi ∧
      ¬Fin15AnchoredAtom2427 chi ∧
      ¬Fin15AnchoredAtom2429 chi ∧
      ¬Fin15AnchoredAtom2434 chi ∧
      ¬Fin15AnchoredAtom2457 chi ∧
      ¬Fin15AnchoredAtom2459 chi ∧
      ¬Fin15AnchoredAtom2461 chi ∧
      ¬Fin15AnchoredAtom2463 chi ∧
      ¬Fin15AnchoredAtom2465 chi ∧
      ¬Fin15AnchoredAtom2470 chi ∧
      ¬Fin15AnchoredAtom2473 chi ∧
      ¬Fin15AnchoredAtom2475 chi ∧
      ¬Fin15AnchoredAtom2480 chi ∧
      ¬Fin15AnchoredAtom2486 chi ∧
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
      ¬Fin15AnchoredAtom4257 chi ∧
      ¬Fin15AnchoredAtom4259 chi ∧
      ¬Fin15AnchoredAtom4261 chi ∧
      ¬Fin15AnchoredAtom4263 chi ∧
      ¬Fin15AnchoredAtom4265 chi ∧
      ¬Fin15AnchoredAtom4270 chi ∧
      ¬Fin15AnchoredAtom4273 chi ∧
      ¬Fin15AnchoredAtom4275 chi ∧
      ¬Fin15AnchoredAtom4280 chi ∧
      ¬Fin15AnchoredAtom4286 chi ∧
      ¬Fin15AnchoredAtom4328 chi ∧
      ¬Fin15AnchoredAtom4330 chi ∧
      ¬Fin15AnchoredAtom4335 chi ∧
      ¬Fin15AnchoredAtom4341 chi ∧
      ¬Fin15AnchoredAtom4351 chi ∧
      ¬Fin15AnchoredAtom4734 chi ∧
      ¬Fin15AnchoredAtom4736 chi ∧
      ¬Fin15AnchoredAtom4741 chi ∧
      ¬Fin15AnchoredAtom4747 chi ∧
      ¬Fin15AnchoredAtom4757 chi ∧
      ¬Fin15AnchoredAtom4807 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 6, 8, 9, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22345
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2415 Fin15AnchoredAtom2416 Fin15AnchoredAtom2418
    Fin15AnchoredAtom2420 Fin15AnchoredAtom2421 Fin15AnchoredAtom2423 Fin15AnchoredAtom2425
    Fin15AnchoredAtom2427 Fin15AnchoredAtom2429 Fin15AnchoredAtom2434 Fin15AnchoredAtom2457
    Fin15AnchoredAtom2459 Fin15AnchoredAtom2461 Fin15AnchoredAtom2463 Fin15AnchoredAtom2465
    Fin15AnchoredAtom2470 Fin15AnchoredAtom2473 Fin15AnchoredAtom2475 Fin15AnchoredAtom2480
    Fin15AnchoredAtom2486 Fin15AnchoredAtom2717 Fin15AnchoredAtom2719 Fin15AnchoredAtom2721
    Fin15AnchoredAtom2723 Fin15AnchoredAtom2725 Fin15AnchoredAtom2730 Fin15AnchoredAtom2733
    Fin15AnchoredAtom2735 Fin15AnchoredAtom2740 Fin15AnchoredAtom2746 Fin15AnchoredAtom2788
    Fin15AnchoredAtom2790 Fin15AnchoredAtom2795 Fin15AnchoredAtom2801 Fin15AnchoredAtom2811
    Fin15AnchoredAtom4257 Fin15AnchoredAtom4259 Fin15AnchoredAtom4261 Fin15AnchoredAtom4263
    Fin15AnchoredAtom4265 Fin15AnchoredAtom4270 Fin15AnchoredAtom4273 Fin15AnchoredAtom4275
    Fin15AnchoredAtom4280 Fin15AnchoredAtom4286 Fin15AnchoredAtom4328 Fin15AnchoredAtom4330
    Fin15AnchoredAtom4335 Fin15AnchoredAtom4341 Fin15AnchoredAtom4351 Fin15AnchoredAtom4734
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

theorem fin15Anchored_clause31513 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2415 chi ∧
      ¬Fin15AnchoredAtom2416 chi ∧
      ¬Fin15AnchoredAtom2419 chi ∧
      ¬Fin15AnchoredAtom2420 chi ∧
      ¬Fin15AnchoredAtom2421 chi ∧
      ¬Fin15AnchoredAtom2424 chi ∧
      ¬Fin15AnchoredAtom2425 chi ∧
      ¬Fin15AnchoredAtom2428 chi ∧
      ¬Fin15AnchoredAtom2429 chi ∧
      ¬Fin15AnchoredAtom2435 chi ∧
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
      ¬Fin15AnchoredAtom2717 chi ∧
      ¬Fin15AnchoredAtom2720 chi ∧
      ¬Fin15AnchoredAtom2721 chi ∧
      ¬Fin15AnchoredAtom2724 chi ∧
      ¬Fin15AnchoredAtom2725 chi ∧
      ¬Fin15AnchoredAtom2731 chi ∧
      ¬Fin15AnchoredAtom2734 chi ∧
      ¬Fin15AnchoredAtom2735 chi ∧
      ¬Fin15AnchoredAtom2741 chi ∧
      ¬Fin15AnchoredAtom2747 chi ∧
      ¬Fin15AnchoredAtom2789 chi ∧
      ¬Fin15AnchoredAtom2790 chi ∧
      ¬Fin15AnchoredAtom2796 chi ∧
      ¬Fin15AnchoredAtom2802 chi ∧
      ¬Fin15AnchoredAtom2812 chi ∧
      ¬Fin15AnchoredAtom4257 chi ∧
      ¬Fin15AnchoredAtom4260 chi ∧
      ¬Fin15AnchoredAtom4261 chi ∧
      ¬Fin15AnchoredAtom4264 chi ∧
      ¬Fin15AnchoredAtom4265 chi ∧
      ¬Fin15AnchoredAtom4271 chi ∧
      ¬Fin15AnchoredAtom4274 chi ∧
      ¬Fin15AnchoredAtom4275 chi ∧
      ¬Fin15AnchoredAtom4281 chi ∧
      ¬Fin15AnchoredAtom4287 chi ∧
      ¬Fin15AnchoredAtom4329 chi ∧
      ¬Fin15AnchoredAtom4330 chi ∧
      ¬Fin15AnchoredAtom4336 chi ∧
      ¬Fin15AnchoredAtom4342 chi ∧
      ¬Fin15AnchoredAtom4352 chi ∧
      ¬Fin15AnchoredAtom4735 chi ∧
      ¬Fin15AnchoredAtom4736 chi ∧
      ¬Fin15AnchoredAtom4742 chi ∧
      ¬Fin15AnchoredAtom4748 chi ∧
      ¬Fin15AnchoredAtom4758 chi ∧
      ¬Fin15AnchoredAtom4808 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 6, 8, 9, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26441
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2415 Fin15AnchoredAtom2416 Fin15AnchoredAtom2419
    Fin15AnchoredAtom2420 Fin15AnchoredAtom2421 Fin15AnchoredAtom2424 Fin15AnchoredAtom2425
    Fin15AnchoredAtom2428 Fin15AnchoredAtom2429 Fin15AnchoredAtom2435 Fin15AnchoredAtom2457
    Fin15AnchoredAtom2460 Fin15AnchoredAtom2461 Fin15AnchoredAtom2464 Fin15AnchoredAtom2465
    Fin15AnchoredAtom2471 Fin15AnchoredAtom2474 Fin15AnchoredAtom2475 Fin15AnchoredAtom2481
    Fin15AnchoredAtom2487 Fin15AnchoredAtom2717 Fin15AnchoredAtom2720 Fin15AnchoredAtom2721
    Fin15AnchoredAtom2724 Fin15AnchoredAtom2725 Fin15AnchoredAtom2731 Fin15AnchoredAtom2734
    Fin15AnchoredAtom2735 Fin15AnchoredAtom2741 Fin15AnchoredAtom2747 Fin15AnchoredAtom2789
    Fin15AnchoredAtom2790 Fin15AnchoredAtom2796 Fin15AnchoredAtom2802 Fin15AnchoredAtom2812
    Fin15AnchoredAtom4257 Fin15AnchoredAtom4260 Fin15AnchoredAtom4261 Fin15AnchoredAtom4264
    Fin15AnchoredAtom4265 Fin15AnchoredAtom4271 Fin15AnchoredAtom4274 Fin15AnchoredAtom4275
    Fin15AnchoredAtom4281 Fin15AnchoredAtom4287 Fin15AnchoredAtom4329 Fin15AnchoredAtom4330
    Fin15AnchoredAtom4336 Fin15AnchoredAtom4342 Fin15AnchoredAtom4352 Fin15AnchoredAtom4735
    Fin15AnchoredAtom4736 Fin15AnchoredAtom4742 Fin15AnchoredAtom4748 Fin15AnchoredAtom4758
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

theorem fin15Anchored_clause31514 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2421 chi ∧
      ¬Fin15AnchoredAtom2423 chi ∧
      ¬Fin15AnchoredAtom2424 chi ∧
      ¬Fin15AnchoredAtom2425 chi ∧
      ¬Fin15AnchoredAtom2427 chi ∧
      ¬Fin15AnchoredAtom2428 chi ∧
      ¬Fin15AnchoredAtom2429 chi ∧
      ¬Fin15AnchoredAtom2433 chi ∧
      ¬Fin15AnchoredAtom2434 chi ∧
      ¬Fin15AnchoredAtom2435 chi ∧
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
      ¬Fin15AnchoredAtom4273 chi ∧
      ¬Fin15AnchoredAtom4274 chi ∧
      ¬Fin15AnchoredAtom4275 chi ∧
      ¬Fin15AnchoredAtom4279 chi ∧
      ¬Fin15AnchoredAtom4280 chi ∧
      ¬Fin15AnchoredAtom4281 chi ∧
      ¬Fin15AnchoredAtom4285 chi ∧
      ¬Fin15AnchoredAtom4286 chi ∧
      ¬Fin15AnchoredAtom4287 chi ∧
      ¬Fin15AnchoredAtom4291 chi ∧
      ¬Fin15AnchoredAtom4350 chi ∧
      ¬Fin15AnchoredAtom4351 chi ∧
      ¬Fin15AnchoredAtom4352 chi ∧
      ¬Fin15AnchoredAtom4356 chi ∧
      ¬Fin15AnchoredAtom4360 chi ∧
      ¬Fin15AnchoredAtom4756 chi ∧
      ¬Fin15AnchoredAtom4757 chi ∧
      ¬Fin15AnchoredAtom4758 chi ∧
      ¬Fin15AnchoredAtom4762 chi ∧
      ¬Fin15AnchoredAtom4766 chi ∧
      ¬Fin15AnchoredAtom4821 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 6, 9, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask30281
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2421 Fin15AnchoredAtom2423 Fin15AnchoredAtom2424
    Fin15AnchoredAtom2425 Fin15AnchoredAtom2427 Fin15AnchoredAtom2428 Fin15AnchoredAtom2429
    Fin15AnchoredAtom2433 Fin15AnchoredAtom2434 Fin15AnchoredAtom2435 Fin15AnchoredAtom2473
    Fin15AnchoredAtom2474 Fin15AnchoredAtom2475 Fin15AnchoredAtom2479 Fin15AnchoredAtom2480
    Fin15AnchoredAtom2481 Fin15AnchoredAtom2485 Fin15AnchoredAtom2486 Fin15AnchoredAtom2487
    Fin15AnchoredAtom2491 Fin15AnchoredAtom2733 Fin15AnchoredAtom2734 Fin15AnchoredAtom2735
    Fin15AnchoredAtom2739 Fin15AnchoredAtom2740 Fin15AnchoredAtom2741 Fin15AnchoredAtom2745
    Fin15AnchoredAtom2746 Fin15AnchoredAtom2747 Fin15AnchoredAtom2751 Fin15AnchoredAtom2810
    Fin15AnchoredAtom2811 Fin15AnchoredAtom2812 Fin15AnchoredAtom2816 Fin15AnchoredAtom2820
    Fin15AnchoredAtom4273 Fin15AnchoredAtom4274 Fin15AnchoredAtom4275 Fin15AnchoredAtom4279
    Fin15AnchoredAtom4280 Fin15AnchoredAtom4281 Fin15AnchoredAtom4285 Fin15AnchoredAtom4286
    Fin15AnchoredAtom4287 Fin15AnchoredAtom4291 Fin15AnchoredAtom4350 Fin15AnchoredAtom4351
    Fin15AnchoredAtom4352 Fin15AnchoredAtom4356 Fin15AnchoredAtom4360 Fin15AnchoredAtom4756
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

theorem fin15Anchored_clause31515 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2436 chi ∧
      ¬Fin15AnchoredAtom2437 chi ∧
      ¬Fin15AnchoredAtom2439 chi ∧
      ¬Fin15AnchoredAtom2440 chi ∧
      ¬Fin15AnchoredAtom2442 chi ∧
      ¬Fin15AnchoredAtom2444 chi ∧
      ¬Fin15AnchoredAtom2445 chi ∧
      ¬Fin15AnchoredAtom2448 chi ∧
      ¬Fin15AnchoredAtom2449 chi ∧
      ¬Fin15AnchoredAtom2454 chi ∧
      ¬Fin15AnchoredAtom2457 chi ∧
      ¬Fin15AnchoredAtom2459 chi ∧
      ¬Fin15AnchoredAtom2460 chi ∧
      ¬Fin15AnchoredAtom2463 chi ∧
      ¬Fin15AnchoredAtom2464 chi ∧
      ¬Fin15AnchoredAtom2469 chi ∧
      ¬Fin15AnchoredAtom2473 chi ∧
      ¬Fin15AnchoredAtom2474 chi ∧
      ¬Fin15AnchoredAtom2479 chi ∧
      ¬Fin15AnchoredAtom2485 chi ∧
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
      ¬Fin15AnchoredAtom4292 chi ∧
      ¬Fin15AnchoredAtom4294 chi ∧
      ¬Fin15AnchoredAtom4295 chi ∧
      ¬Fin15AnchoredAtom4298 chi ∧
      ¬Fin15AnchoredAtom4299 chi ∧
      ¬Fin15AnchoredAtom4304 chi ∧
      ¬Fin15AnchoredAtom4308 chi ∧
      ¬Fin15AnchoredAtom4309 chi ∧
      ¬Fin15AnchoredAtom4314 chi ∧
      ¬Fin15AnchoredAtom4320 chi ∧
      ¬Fin15AnchoredAtom4328 chi ∧
      ¬Fin15AnchoredAtom4329 chi ∧
      ¬Fin15AnchoredAtom4334 chi ∧
      ¬Fin15AnchoredAtom4340 chi ∧
      ¬Fin15AnchoredAtom4350 chi ∧
      ¬Fin15AnchoredAtom4769 chi ∧
      ¬Fin15AnchoredAtom4770 chi ∧
      ¬Fin15AnchoredAtom4775 chi ∧
      ¬Fin15AnchoredAtom4781 chi ∧
      ¬Fin15AnchoredAtom4791 chi ∧
      ¬Fin15AnchoredAtom4806 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 7, 8, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask14217
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2436 Fin15AnchoredAtom2437 Fin15AnchoredAtom2439
    Fin15AnchoredAtom2440 Fin15AnchoredAtom2442 Fin15AnchoredAtom2444 Fin15AnchoredAtom2445
    Fin15AnchoredAtom2448 Fin15AnchoredAtom2449 Fin15AnchoredAtom2454 Fin15AnchoredAtom2457
    Fin15AnchoredAtom2459 Fin15AnchoredAtom2460 Fin15AnchoredAtom2463 Fin15AnchoredAtom2464
    Fin15AnchoredAtom2469 Fin15AnchoredAtom2473 Fin15AnchoredAtom2474 Fin15AnchoredAtom2479
    Fin15AnchoredAtom2485 Fin15AnchoredAtom2752 Fin15AnchoredAtom2754 Fin15AnchoredAtom2755
    Fin15AnchoredAtom2758 Fin15AnchoredAtom2759 Fin15AnchoredAtom2764 Fin15AnchoredAtom2768
    Fin15AnchoredAtom2769 Fin15AnchoredAtom2774 Fin15AnchoredAtom2780 Fin15AnchoredAtom2788
    Fin15AnchoredAtom2789 Fin15AnchoredAtom2794 Fin15AnchoredAtom2800 Fin15AnchoredAtom2810
    Fin15AnchoredAtom4292 Fin15AnchoredAtom4294 Fin15AnchoredAtom4295 Fin15AnchoredAtom4298
    Fin15AnchoredAtom4299 Fin15AnchoredAtom4304 Fin15AnchoredAtom4308 Fin15AnchoredAtom4309
    Fin15AnchoredAtom4314 Fin15AnchoredAtom4320 Fin15AnchoredAtom4328 Fin15AnchoredAtom4329
    Fin15AnchoredAtom4334 Fin15AnchoredAtom4340 Fin15AnchoredAtom4350 Fin15AnchoredAtom4769
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

theorem fin15Anchored_clause31516 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2436 chi ∧
      ¬Fin15AnchoredAtom2437 chi ∧
      ¬Fin15AnchoredAtom2439 chi ∧
      ¬Fin15AnchoredAtom2441 chi ∧
      ¬Fin15AnchoredAtom2442 chi ∧
      ¬Fin15AnchoredAtom2444 chi ∧
      ¬Fin15AnchoredAtom2446 chi ∧
      ¬Fin15AnchoredAtom2448 chi ∧
      ¬Fin15AnchoredAtom2450 chi ∧
      ¬Fin15AnchoredAtom2455 chi ∧
      ¬Fin15AnchoredAtom2457 chi ∧
      ¬Fin15AnchoredAtom2459 chi ∧
      ¬Fin15AnchoredAtom2461 chi ∧
      ¬Fin15AnchoredAtom2463 chi ∧
      ¬Fin15AnchoredAtom2465 chi ∧
      ¬Fin15AnchoredAtom2470 chi ∧
      ¬Fin15AnchoredAtom2473 chi ∧
      ¬Fin15AnchoredAtom2475 chi ∧
      ¬Fin15AnchoredAtom2480 chi ∧
      ¬Fin15AnchoredAtom2486 chi ∧
      ¬Fin15AnchoredAtom2752 chi ∧
      ¬Fin15AnchoredAtom2754 chi ∧
      ¬Fin15AnchoredAtom2756 chi ∧
      ¬Fin15AnchoredAtom2758 chi ∧
      ¬Fin15AnchoredAtom2760 chi ∧
      ¬Fin15AnchoredAtom2765 chi ∧
      ¬Fin15AnchoredAtom2768 chi ∧
      ¬Fin15AnchoredAtom2770 chi ∧
      ¬Fin15AnchoredAtom2775 chi ∧
      ¬Fin15AnchoredAtom2781 chi ∧
      ¬Fin15AnchoredAtom2788 chi ∧
      ¬Fin15AnchoredAtom2790 chi ∧
      ¬Fin15AnchoredAtom2795 chi ∧
      ¬Fin15AnchoredAtom2801 chi ∧
      ¬Fin15AnchoredAtom2811 chi ∧
      ¬Fin15AnchoredAtom4292 chi ∧
      ¬Fin15AnchoredAtom4294 chi ∧
      ¬Fin15AnchoredAtom4296 chi ∧
      ¬Fin15AnchoredAtom4298 chi ∧
      ¬Fin15AnchoredAtom4300 chi ∧
      ¬Fin15AnchoredAtom4305 chi ∧
      ¬Fin15AnchoredAtom4308 chi ∧
      ¬Fin15AnchoredAtom4310 chi ∧
      ¬Fin15AnchoredAtom4315 chi ∧
      ¬Fin15AnchoredAtom4321 chi ∧
      ¬Fin15AnchoredAtom4328 chi ∧
      ¬Fin15AnchoredAtom4330 chi ∧
      ¬Fin15AnchoredAtom4335 chi ∧
      ¬Fin15AnchoredAtom4341 chi ∧
      ¬Fin15AnchoredAtom4351 chi ∧
      ¬Fin15AnchoredAtom4769 chi ∧
      ¬Fin15AnchoredAtom4771 chi ∧
      ¬Fin15AnchoredAtom4776 chi ∧
      ¬Fin15AnchoredAtom4782 chi ∧
      ¬Fin15AnchoredAtom4792 chi ∧
      ¬Fin15AnchoredAtom4807 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 7, 8, 9, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22409
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2436 Fin15AnchoredAtom2437 Fin15AnchoredAtom2439
    Fin15AnchoredAtom2441 Fin15AnchoredAtom2442 Fin15AnchoredAtom2444 Fin15AnchoredAtom2446
    Fin15AnchoredAtom2448 Fin15AnchoredAtom2450 Fin15AnchoredAtom2455 Fin15AnchoredAtom2457
    Fin15AnchoredAtom2459 Fin15AnchoredAtom2461 Fin15AnchoredAtom2463 Fin15AnchoredAtom2465
    Fin15AnchoredAtom2470 Fin15AnchoredAtom2473 Fin15AnchoredAtom2475 Fin15AnchoredAtom2480
    Fin15AnchoredAtom2486 Fin15AnchoredAtom2752 Fin15AnchoredAtom2754 Fin15AnchoredAtom2756
    Fin15AnchoredAtom2758 Fin15AnchoredAtom2760 Fin15AnchoredAtom2765 Fin15AnchoredAtom2768
    Fin15AnchoredAtom2770 Fin15AnchoredAtom2775 Fin15AnchoredAtom2781 Fin15AnchoredAtom2788
    Fin15AnchoredAtom2790 Fin15AnchoredAtom2795 Fin15AnchoredAtom2801 Fin15AnchoredAtom2811
    Fin15AnchoredAtom4292 Fin15AnchoredAtom4294 Fin15AnchoredAtom4296 Fin15AnchoredAtom4298
    Fin15AnchoredAtom4300 Fin15AnchoredAtom4305 Fin15AnchoredAtom4308 Fin15AnchoredAtom4310
    Fin15AnchoredAtom4315 Fin15AnchoredAtom4321 Fin15AnchoredAtom4328 Fin15AnchoredAtom4330
    Fin15AnchoredAtom4335 Fin15AnchoredAtom4341 Fin15AnchoredAtom4351 Fin15AnchoredAtom4769
    Fin15AnchoredAtom4771 Fin15AnchoredAtom4776 Fin15AnchoredAtom4782 Fin15AnchoredAtom4792
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

theorem fin15Anchored_clause31517 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2436 chi ∧
      ¬Fin15AnchoredAtom2437 chi ∧
      ¬Fin15AnchoredAtom2440 chi ∧
      ¬Fin15AnchoredAtom2441 chi ∧
      ¬Fin15AnchoredAtom2442 chi ∧
      ¬Fin15AnchoredAtom2445 chi ∧
      ¬Fin15AnchoredAtom2446 chi ∧
      ¬Fin15AnchoredAtom2449 chi ∧
      ¬Fin15AnchoredAtom2450 chi ∧
      ¬Fin15AnchoredAtom2456 chi ∧
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
      ¬Fin15AnchoredAtom2752 chi ∧
      ¬Fin15AnchoredAtom2755 chi ∧
      ¬Fin15AnchoredAtom2756 chi ∧
      ¬Fin15AnchoredAtom2759 chi ∧
      ¬Fin15AnchoredAtom2760 chi ∧
      ¬Fin15AnchoredAtom2766 chi ∧
      ¬Fin15AnchoredAtom2769 chi ∧
      ¬Fin15AnchoredAtom2770 chi ∧
      ¬Fin15AnchoredAtom2776 chi ∧
      ¬Fin15AnchoredAtom2782 chi ∧
      ¬Fin15AnchoredAtom2789 chi ∧
      ¬Fin15AnchoredAtom2790 chi ∧
      ¬Fin15AnchoredAtom2796 chi ∧
      ¬Fin15AnchoredAtom2802 chi ∧
      ¬Fin15AnchoredAtom2812 chi ∧
      ¬Fin15AnchoredAtom4292 chi ∧
      ¬Fin15AnchoredAtom4295 chi ∧
      ¬Fin15AnchoredAtom4296 chi ∧
      ¬Fin15AnchoredAtom4299 chi ∧
      ¬Fin15AnchoredAtom4300 chi ∧
      ¬Fin15AnchoredAtom4306 chi ∧
      ¬Fin15AnchoredAtom4309 chi ∧
      ¬Fin15AnchoredAtom4310 chi ∧
      ¬Fin15AnchoredAtom4316 chi ∧
      ¬Fin15AnchoredAtom4322 chi ∧
      ¬Fin15AnchoredAtom4329 chi ∧
      ¬Fin15AnchoredAtom4330 chi ∧
      ¬Fin15AnchoredAtom4336 chi ∧
      ¬Fin15AnchoredAtom4342 chi ∧
      ¬Fin15AnchoredAtom4352 chi ∧
      ¬Fin15AnchoredAtom4770 chi ∧
      ¬Fin15AnchoredAtom4771 chi ∧
      ¬Fin15AnchoredAtom4777 chi ∧
      ¬Fin15AnchoredAtom4783 chi ∧
      ¬Fin15AnchoredAtom4793 chi ∧
      ¬Fin15AnchoredAtom4808 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 7, 8, 9, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26505
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2436 Fin15AnchoredAtom2437 Fin15AnchoredAtom2440
    Fin15AnchoredAtom2441 Fin15AnchoredAtom2442 Fin15AnchoredAtom2445 Fin15AnchoredAtom2446
    Fin15AnchoredAtom2449 Fin15AnchoredAtom2450 Fin15AnchoredAtom2456 Fin15AnchoredAtom2457
    Fin15AnchoredAtom2460 Fin15AnchoredAtom2461 Fin15AnchoredAtom2464 Fin15AnchoredAtom2465
    Fin15AnchoredAtom2471 Fin15AnchoredAtom2474 Fin15AnchoredAtom2475 Fin15AnchoredAtom2481
    Fin15AnchoredAtom2487 Fin15AnchoredAtom2752 Fin15AnchoredAtom2755 Fin15AnchoredAtom2756
    Fin15AnchoredAtom2759 Fin15AnchoredAtom2760 Fin15AnchoredAtom2766 Fin15AnchoredAtom2769
    Fin15AnchoredAtom2770 Fin15AnchoredAtom2776 Fin15AnchoredAtom2782 Fin15AnchoredAtom2789
    Fin15AnchoredAtom2790 Fin15AnchoredAtom2796 Fin15AnchoredAtom2802 Fin15AnchoredAtom2812
    Fin15AnchoredAtom4292 Fin15AnchoredAtom4295 Fin15AnchoredAtom4296 Fin15AnchoredAtom4299
    Fin15AnchoredAtom4300 Fin15AnchoredAtom4306 Fin15AnchoredAtom4309 Fin15AnchoredAtom4310
    Fin15AnchoredAtom4316 Fin15AnchoredAtom4322 Fin15AnchoredAtom4329 Fin15AnchoredAtom4330
    Fin15AnchoredAtom4336 Fin15AnchoredAtom4342 Fin15AnchoredAtom4352 Fin15AnchoredAtom4770
    Fin15AnchoredAtom4771 Fin15AnchoredAtom4777 Fin15AnchoredAtom4783 Fin15AnchoredAtom4793
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

theorem fin15Anchored_clause31518 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2437 chi ∧
      ¬Fin15AnchoredAtom2439 chi ∧
      ¬Fin15AnchoredAtom2440 chi ∧
      ¬Fin15AnchoredAtom2441 chi ∧
      ¬Fin15AnchoredAtom2448 chi ∧
      ¬Fin15AnchoredAtom2449 chi ∧
      ¬Fin15AnchoredAtom2450 chi ∧
      ¬Fin15AnchoredAtom2454 chi ∧
      ¬Fin15AnchoredAtom2455 chi ∧
      ¬Fin15AnchoredAtom2456 chi ∧
      ¬Fin15AnchoredAtom2463 chi ∧
      ¬Fin15AnchoredAtom2464 chi ∧
      ¬Fin15AnchoredAtom2465 chi ∧
      ¬Fin15AnchoredAtom2469 chi ∧
      ¬Fin15AnchoredAtom2470 chi ∧
      ¬Fin15AnchoredAtom2471 chi ∧
      ¬Fin15AnchoredAtom2485 chi ∧
      ¬Fin15AnchoredAtom2486 chi ∧
      ¬Fin15AnchoredAtom2487 chi ∧
      ¬Fin15AnchoredAtom2491 chi ∧
      ¬Fin15AnchoredAtom2758 chi ∧
      ¬Fin15AnchoredAtom2759 chi ∧
      ¬Fin15AnchoredAtom2760 chi ∧
      ¬Fin15AnchoredAtom2764 chi ∧
      ¬Fin15AnchoredAtom2765 chi ∧
      ¬Fin15AnchoredAtom2766 chi ∧
      ¬Fin15AnchoredAtom2780 chi ∧
      ¬Fin15AnchoredAtom2781 chi ∧
      ¬Fin15AnchoredAtom2782 chi ∧
      ¬Fin15AnchoredAtom2786 chi ∧
      ¬Fin15AnchoredAtom2800 chi ∧
      ¬Fin15AnchoredAtom2801 chi ∧
      ¬Fin15AnchoredAtom2802 chi ∧
      ¬Fin15AnchoredAtom2806 chi ∧
      ¬Fin15AnchoredAtom2820 chi ∧
      ¬Fin15AnchoredAtom4298 chi ∧
      ¬Fin15AnchoredAtom4299 chi ∧
      ¬Fin15AnchoredAtom4300 chi ∧
      ¬Fin15AnchoredAtom4304 chi ∧
      ¬Fin15AnchoredAtom4305 chi ∧
      ¬Fin15AnchoredAtom4306 chi ∧
      ¬Fin15AnchoredAtom4320 chi ∧
      ¬Fin15AnchoredAtom4321 chi ∧
      ¬Fin15AnchoredAtom4322 chi ∧
      ¬Fin15AnchoredAtom4326 chi ∧
      ¬Fin15AnchoredAtom4340 chi ∧
      ¬Fin15AnchoredAtom4341 chi ∧
      ¬Fin15AnchoredAtom4342 chi ∧
      ¬Fin15AnchoredAtom4346 chi ∧
      ¬Fin15AnchoredAtom4360 chi ∧
      ¬Fin15AnchoredAtom4781 chi ∧
      ¬Fin15AnchoredAtom4782 chi ∧
      ¬Fin15AnchoredAtom4783 chi ∧
      ¬Fin15AnchoredAtom4787 chi ∧
      ¬Fin15AnchoredAtom4801 chi ∧
      ¬Fin15AnchoredAtom4816 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 7, 8, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask30089
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2437 Fin15AnchoredAtom2439 Fin15AnchoredAtom2440
    Fin15AnchoredAtom2441 Fin15AnchoredAtom2448 Fin15AnchoredAtom2449 Fin15AnchoredAtom2450
    Fin15AnchoredAtom2454 Fin15AnchoredAtom2455 Fin15AnchoredAtom2456 Fin15AnchoredAtom2463
    Fin15AnchoredAtom2464 Fin15AnchoredAtom2465 Fin15AnchoredAtom2469 Fin15AnchoredAtom2470
    Fin15AnchoredAtom2471 Fin15AnchoredAtom2485 Fin15AnchoredAtom2486 Fin15AnchoredAtom2487
    Fin15AnchoredAtom2491 Fin15AnchoredAtom2758 Fin15AnchoredAtom2759 Fin15AnchoredAtom2760
    Fin15AnchoredAtom2764 Fin15AnchoredAtom2765 Fin15AnchoredAtom2766 Fin15AnchoredAtom2780
    Fin15AnchoredAtom2781 Fin15AnchoredAtom2782 Fin15AnchoredAtom2786 Fin15AnchoredAtom2800
    Fin15AnchoredAtom2801 Fin15AnchoredAtom2802 Fin15AnchoredAtom2806 Fin15AnchoredAtom2820
    Fin15AnchoredAtom4298 Fin15AnchoredAtom4299 Fin15AnchoredAtom4300 Fin15AnchoredAtom4304
    Fin15AnchoredAtom4305 Fin15AnchoredAtom4306 Fin15AnchoredAtom4320 Fin15AnchoredAtom4321
    Fin15AnchoredAtom4322 Fin15AnchoredAtom4326 Fin15AnchoredAtom4340 Fin15AnchoredAtom4341
    Fin15AnchoredAtom4342 Fin15AnchoredAtom4346 Fin15AnchoredAtom4360 Fin15AnchoredAtom4781
    Fin15AnchoredAtom4782 Fin15AnchoredAtom4783 Fin15AnchoredAtom4787 Fin15AnchoredAtom4801
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

theorem fin15Anchored_clause31519 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2442 chi ∧
      ¬Fin15AnchoredAtom2444 chi ∧
      ¬Fin15AnchoredAtom2445 chi ∧
      ¬Fin15AnchoredAtom2446 chi ∧
      ¬Fin15AnchoredAtom2448 chi ∧
      ¬Fin15AnchoredAtom2449 chi ∧
      ¬Fin15AnchoredAtom2450 chi ∧
      ¬Fin15AnchoredAtom2454 chi ∧
      ¬Fin15AnchoredAtom2455 chi ∧
      ¬Fin15AnchoredAtom2456 chi ∧
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
      ¬Fin15AnchoredAtom4308 chi ∧
      ¬Fin15AnchoredAtom4309 chi ∧
      ¬Fin15AnchoredAtom4310 chi ∧
      ¬Fin15AnchoredAtom4314 chi ∧
      ¬Fin15AnchoredAtom4315 chi ∧
      ¬Fin15AnchoredAtom4316 chi ∧
      ¬Fin15AnchoredAtom4320 chi ∧
      ¬Fin15AnchoredAtom4321 chi ∧
      ¬Fin15AnchoredAtom4322 chi ∧
      ¬Fin15AnchoredAtom4326 chi ∧
      ¬Fin15AnchoredAtom4350 chi ∧
      ¬Fin15AnchoredAtom4351 chi ∧
      ¬Fin15AnchoredAtom4352 chi ∧
      ¬Fin15AnchoredAtom4356 chi ∧
      ¬Fin15AnchoredAtom4360 chi ∧
      ¬Fin15AnchoredAtom4791 chi ∧
      ¬Fin15AnchoredAtom4792 chi ∧
      ¬Fin15AnchoredAtom4793 chi ∧
      ¬Fin15AnchoredAtom4797 chi ∧
      ¬Fin15AnchoredAtom4801 chi ∧
      ¬Fin15AnchoredAtom4821 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 7, 9, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask30345
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2442 Fin15AnchoredAtom2444 Fin15AnchoredAtom2445
    Fin15AnchoredAtom2446 Fin15AnchoredAtom2448 Fin15AnchoredAtom2449 Fin15AnchoredAtom2450
    Fin15AnchoredAtom2454 Fin15AnchoredAtom2455 Fin15AnchoredAtom2456 Fin15AnchoredAtom2473
    Fin15AnchoredAtom2474 Fin15AnchoredAtom2475 Fin15AnchoredAtom2479 Fin15AnchoredAtom2480
    Fin15AnchoredAtom2481 Fin15AnchoredAtom2485 Fin15AnchoredAtom2486 Fin15AnchoredAtom2487
    Fin15AnchoredAtom2491 Fin15AnchoredAtom2768 Fin15AnchoredAtom2769 Fin15AnchoredAtom2770
    Fin15AnchoredAtom2774 Fin15AnchoredAtom2775 Fin15AnchoredAtom2776 Fin15AnchoredAtom2780
    Fin15AnchoredAtom2781 Fin15AnchoredAtom2782 Fin15AnchoredAtom2786 Fin15AnchoredAtom2810
    Fin15AnchoredAtom2811 Fin15AnchoredAtom2812 Fin15AnchoredAtom2816 Fin15AnchoredAtom2820
    Fin15AnchoredAtom4308 Fin15AnchoredAtom4309 Fin15AnchoredAtom4310 Fin15AnchoredAtom4314
    Fin15AnchoredAtom4315 Fin15AnchoredAtom4316 Fin15AnchoredAtom4320 Fin15AnchoredAtom4321
    Fin15AnchoredAtom4322 Fin15AnchoredAtom4326 Fin15AnchoredAtom4350 Fin15AnchoredAtom4351
    Fin15AnchoredAtom4352 Fin15AnchoredAtom4356 Fin15AnchoredAtom4360 Fin15AnchoredAtom4791
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

theorem fin15Anchored_clause31520 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2492 chi ∧
      ¬Fin15AnchoredAtom2493 chi ∧
      ¬Fin15AnchoredAtom2494 chi ∧
      ¬Fin15AnchoredAtom2495 chi ∧
      ¬Fin15AnchoredAtom2500 chi ∧
      ¬Fin15AnchoredAtom2501 chi ∧
      ¬Fin15AnchoredAtom2502 chi ∧
      ¬Fin15AnchoredAtom2507 chi ∧
      ¬Fin15AnchoredAtom2508 chi ∧
      ¬Fin15AnchoredAtom2513 chi ∧
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
      ¬Fin15AnchoredAtom4362 chi ∧
      ¬Fin15AnchoredAtom4363 chi ∧
      ¬Fin15AnchoredAtom4364 chi ∧
      ¬Fin15AnchoredAtom4369 chi ∧
      ¬Fin15AnchoredAtom4370 chi ∧
      ¬Fin15AnchoredAtom4375 chi ∧
      ¬Fin15AnchoredAtom4390 chi ∧
      ¬Fin15AnchoredAtom4391 chi ∧
      ¬Fin15AnchoredAtom4396 chi ∧
      ¬Fin15AnchoredAtom4411 chi ∧
      ¬Fin15AnchoredAtom4446 chi ∧
      ¬Fin15AnchoredAtom4447 chi ∧
      ¬Fin15AnchoredAtom4452 chi ∧
      ¬Fin15AnchoredAtom4467 chi ∧
      ¬Fin15AnchoredAtom4502 chi ∧
      ¬Fin15AnchoredAtom4572 chi ∧
      ¬Fin15AnchoredAtom4573 chi ∧
      ¬Fin15AnchoredAtom4578 chi ∧
      ¬Fin15AnchoredAtom4593 chi ∧
      ¬Fin15AnchoredAtom4628 chi ∧
      ¬Fin15AnchoredAtom4698 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 5, 6, 7, 8, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask02033
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2492 Fin15AnchoredAtom2493 Fin15AnchoredAtom2494
    Fin15AnchoredAtom2495 Fin15AnchoredAtom2500 Fin15AnchoredAtom2501 Fin15AnchoredAtom2502
    Fin15AnchoredAtom2507 Fin15AnchoredAtom2508 Fin15AnchoredAtom2513 Fin15AnchoredAtom2528
    Fin15AnchoredAtom2529 Fin15AnchoredAtom2530 Fin15AnchoredAtom2535 Fin15AnchoredAtom2536
    Fin15AnchoredAtom2541 Fin15AnchoredAtom2556 Fin15AnchoredAtom2557 Fin15AnchoredAtom2562
    Fin15AnchoredAtom2577 Fin15AnchoredAtom2612 Fin15AnchoredAtom2613 Fin15AnchoredAtom2614
    Fin15AnchoredAtom2619 Fin15AnchoredAtom2620 Fin15AnchoredAtom2625 Fin15AnchoredAtom2640
    Fin15AnchoredAtom2641 Fin15AnchoredAtom2646 Fin15AnchoredAtom2661 Fin15AnchoredAtom2696
    Fin15AnchoredAtom2697 Fin15AnchoredAtom2702 Fin15AnchoredAtom2717 Fin15AnchoredAtom2752
    Fin15AnchoredAtom4362 Fin15AnchoredAtom4363 Fin15AnchoredAtom4364 Fin15AnchoredAtom4369
    Fin15AnchoredAtom4370 Fin15AnchoredAtom4375 Fin15AnchoredAtom4390 Fin15AnchoredAtom4391
    Fin15AnchoredAtom4396 Fin15AnchoredAtom4411 Fin15AnchoredAtom4446 Fin15AnchoredAtom4447
    Fin15AnchoredAtom4452 Fin15AnchoredAtom4467 Fin15AnchoredAtom4502 Fin15AnchoredAtom4572
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

theorem fin15Anchored_clause31521 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2492 chi ∧
      ¬Fin15AnchoredAtom2493 chi ∧
      ¬Fin15AnchoredAtom2494 chi ∧
      ¬Fin15AnchoredAtom2497 chi ∧
      ¬Fin15AnchoredAtom2500 chi ∧
      ¬Fin15AnchoredAtom2501 chi ∧
      ¬Fin15AnchoredAtom2504 chi ∧
      ¬Fin15AnchoredAtom2507 chi ∧
      ¬Fin15AnchoredAtom2510 chi ∧
      ¬Fin15AnchoredAtom2515 chi ∧
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
      ¬Fin15AnchoredAtom4362 chi ∧
      ¬Fin15AnchoredAtom4363 chi ∧
      ¬Fin15AnchoredAtom4366 chi ∧
      ¬Fin15AnchoredAtom4369 chi ∧
      ¬Fin15AnchoredAtom4372 chi ∧
      ¬Fin15AnchoredAtom4377 chi ∧
      ¬Fin15AnchoredAtom4390 chi ∧
      ¬Fin15AnchoredAtom4393 chi ∧
      ¬Fin15AnchoredAtom4398 chi ∧
      ¬Fin15AnchoredAtom4413 chi ∧
      ¬Fin15AnchoredAtom4446 chi ∧
      ¬Fin15AnchoredAtom4449 chi ∧
      ¬Fin15AnchoredAtom4454 chi ∧
      ¬Fin15AnchoredAtom4469 chi ∧
      ¬Fin15AnchoredAtom4504 chi ∧
      ¬Fin15AnchoredAtom4572 chi ∧
      ¬Fin15AnchoredAtom4575 chi ∧
      ¬Fin15AnchoredAtom4580 chi ∧
      ¬Fin15AnchoredAtom4595 chi ∧
      ¬Fin15AnchoredAtom4630 chi ∧
      ¬Fin15AnchoredAtom4700 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 5, 6, 7, 8, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05105
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2492 Fin15AnchoredAtom2493 Fin15AnchoredAtom2494
    Fin15AnchoredAtom2497 Fin15AnchoredAtom2500 Fin15AnchoredAtom2501 Fin15AnchoredAtom2504
    Fin15AnchoredAtom2507 Fin15AnchoredAtom2510 Fin15AnchoredAtom2515 Fin15AnchoredAtom2528
    Fin15AnchoredAtom2529 Fin15AnchoredAtom2532 Fin15AnchoredAtom2535 Fin15AnchoredAtom2538
    Fin15AnchoredAtom2543 Fin15AnchoredAtom2556 Fin15AnchoredAtom2559 Fin15AnchoredAtom2564
    Fin15AnchoredAtom2579 Fin15AnchoredAtom2612 Fin15AnchoredAtom2613 Fin15AnchoredAtom2616
    Fin15AnchoredAtom2619 Fin15AnchoredAtom2622 Fin15AnchoredAtom2627 Fin15AnchoredAtom2640
    Fin15AnchoredAtom2643 Fin15AnchoredAtom2648 Fin15AnchoredAtom2663 Fin15AnchoredAtom2696
    Fin15AnchoredAtom2699 Fin15AnchoredAtom2704 Fin15AnchoredAtom2719 Fin15AnchoredAtom2754
    Fin15AnchoredAtom4362 Fin15AnchoredAtom4363 Fin15AnchoredAtom4366 Fin15AnchoredAtom4369
    Fin15AnchoredAtom4372 Fin15AnchoredAtom4377 Fin15AnchoredAtom4390 Fin15AnchoredAtom4393
    Fin15AnchoredAtom4398 Fin15AnchoredAtom4413 Fin15AnchoredAtom4446 Fin15AnchoredAtom4449
    Fin15AnchoredAtom4454 Fin15AnchoredAtom4469 Fin15AnchoredAtom4504 Fin15AnchoredAtom4572
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

theorem fin15Anchored_clause31522 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2492 chi ∧
      ¬Fin15AnchoredAtom2493 chi ∧
      ¬Fin15AnchoredAtom2494 chi ∧
      ¬Fin15AnchoredAtom2498 chi ∧
      ¬Fin15AnchoredAtom2500 chi ∧
      ¬Fin15AnchoredAtom2501 chi ∧
      ¬Fin15AnchoredAtom2505 chi ∧
      ¬Fin15AnchoredAtom2507 chi ∧
      ¬Fin15AnchoredAtom2511 chi ∧
      ¬Fin15AnchoredAtom2516 chi ∧
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
      ¬Fin15AnchoredAtom4362 chi ∧
      ¬Fin15AnchoredAtom4363 chi ∧
      ¬Fin15AnchoredAtom4367 chi ∧
      ¬Fin15AnchoredAtom4369 chi ∧
      ¬Fin15AnchoredAtom4373 chi ∧
      ¬Fin15AnchoredAtom4378 chi ∧
      ¬Fin15AnchoredAtom4390 chi ∧
      ¬Fin15AnchoredAtom4394 chi ∧
      ¬Fin15AnchoredAtom4399 chi ∧
      ¬Fin15AnchoredAtom4414 chi ∧
      ¬Fin15AnchoredAtom4446 chi ∧
      ¬Fin15AnchoredAtom4450 chi ∧
      ¬Fin15AnchoredAtom4455 chi ∧
      ¬Fin15AnchoredAtom4470 chi ∧
      ¬Fin15AnchoredAtom4505 chi ∧
      ¬Fin15AnchoredAtom4572 chi ∧
      ¬Fin15AnchoredAtom4576 chi ∧
      ¬Fin15AnchoredAtom4581 chi ∧
      ¬Fin15AnchoredAtom4596 chi ∧
      ¬Fin15AnchoredAtom4631 chi ∧
      ¬Fin15AnchoredAtom4701 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 5, 6, 7, 8, 9, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09201
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2492 Fin15AnchoredAtom2493 Fin15AnchoredAtom2494
    Fin15AnchoredAtom2498 Fin15AnchoredAtom2500 Fin15AnchoredAtom2501 Fin15AnchoredAtom2505
    Fin15AnchoredAtom2507 Fin15AnchoredAtom2511 Fin15AnchoredAtom2516 Fin15AnchoredAtom2528
    Fin15AnchoredAtom2529 Fin15AnchoredAtom2533 Fin15AnchoredAtom2535 Fin15AnchoredAtom2539
    Fin15AnchoredAtom2544 Fin15AnchoredAtom2556 Fin15AnchoredAtom2560 Fin15AnchoredAtom2565
    Fin15AnchoredAtom2580 Fin15AnchoredAtom2612 Fin15AnchoredAtom2613 Fin15AnchoredAtom2617
    Fin15AnchoredAtom2619 Fin15AnchoredAtom2623 Fin15AnchoredAtom2628 Fin15AnchoredAtom2640
    Fin15AnchoredAtom2644 Fin15AnchoredAtom2649 Fin15AnchoredAtom2664 Fin15AnchoredAtom2696
    Fin15AnchoredAtom2700 Fin15AnchoredAtom2705 Fin15AnchoredAtom2720 Fin15AnchoredAtom2755
    Fin15AnchoredAtom4362 Fin15AnchoredAtom4363 Fin15AnchoredAtom4367 Fin15AnchoredAtom4369
    Fin15AnchoredAtom4373 Fin15AnchoredAtom4378 Fin15AnchoredAtom4390 Fin15AnchoredAtom4394
    Fin15AnchoredAtom4399 Fin15AnchoredAtom4414 Fin15AnchoredAtom4446 Fin15AnchoredAtom4450
    Fin15AnchoredAtom4455 Fin15AnchoredAtom4470 Fin15AnchoredAtom4505 Fin15AnchoredAtom4572
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

theorem fin15Anchored_clause31523 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2492 chi ∧
      ¬Fin15AnchoredAtom2493 chi ∧
      ¬Fin15AnchoredAtom2495 chi ∧
      ¬Fin15AnchoredAtom2497 chi ∧
      ¬Fin15AnchoredAtom2500 chi ∧
      ¬Fin15AnchoredAtom2502 chi ∧
      ¬Fin15AnchoredAtom2504 chi ∧
      ¬Fin15AnchoredAtom2508 chi ∧
      ¬Fin15AnchoredAtom2510 chi ∧
      ¬Fin15AnchoredAtom2519 chi ∧
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
      ¬Fin15AnchoredAtom4362 chi ∧
      ¬Fin15AnchoredAtom4364 chi ∧
      ¬Fin15AnchoredAtom4366 chi ∧
      ¬Fin15AnchoredAtom4370 chi ∧
      ¬Fin15AnchoredAtom4372 chi ∧
      ¬Fin15AnchoredAtom4381 chi ∧
      ¬Fin15AnchoredAtom4391 chi ∧
      ¬Fin15AnchoredAtom4393 chi ∧
      ¬Fin15AnchoredAtom4402 chi ∧
      ¬Fin15AnchoredAtom4417 chi ∧
      ¬Fin15AnchoredAtom4447 chi ∧
      ¬Fin15AnchoredAtom4449 chi ∧
      ¬Fin15AnchoredAtom4458 chi ∧
      ¬Fin15AnchoredAtom4473 chi ∧
      ¬Fin15AnchoredAtom4508 chi ∧
      ¬Fin15AnchoredAtom4573 chi ∧
      ¬Fin15AnchoredAtom4575 chi ∧
      ¬Fin15AnchoredAtom4584 chi ∧
      ¬Fin15AnchoredAtom4599 chi ∧
      ¬Fin15AnchoredAtom4634 chi ∧
      ¬Fin15AnchoredAtom4704 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 5, 6, 7, 8, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05617
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2492 Fin15AnchoredAtom2493 Fin15AnchoredAtom2495
    Fin15AnchoredAtom2497 Fin15AnchoredAtom2500 Fin15AnchoredAtom2502 Fin15AnchoredAtom2504
    Fin15AnchoredAtom2508 Fin15AnchoredAtom2510 Fin15AnchoredAtom2519 Fin15AnchoredAtom2528
    Fin15AnchoredAtom2530 Fin15AnchoredAtom2532 Fin15AnchoredAtom2536 Fin15AnchoredAtom2538
    Fin15AnchoredAtom2547 Fin15AnchoredAtom2557 Fin15AnchoredAtom2559 Fin15AnchoredAtom2568
    Fin15AnchoredAtom2583 Fin15AnchoredAtom2612 Fin15AnchoredAtom2614 Fin15AnchoredAtom2616
    Fin15AnchoredAtom2620 Fin15AnchoredAtom2622 Fin15AnchoredAtom2631 Fin15AnchoredAtom2641
    Fin15AnchoredAtom2643 Fin15AnchoredAtom2652 Fin15AnchoredAtom2667 Fin15AnchoredAtom2697
    Fin15AnchoredAtom2699 Fin15AnchoredAtom2708 Fin15AnchoredAtom2723 Fin15AnchoredAtom2758
    Fin15AnchoredAtom4362 Fin15AnchoredAtom4364 Fin15AnchoredAtom4366 Fin15AnchoredAtom4370
    Fin15AnchoredAtom4372 Fin15AnchoredAtom4381 Fin15AnchoredAtom4391 Fin15AnchoredAtom4393
    Fin15AnchoredAtom4402 Fin15AnchoredAtom4417 Fin15AnchoredAtom4447 Fin15AnchoredAtom4449
    Fin15AnchoredAtom4458 Fin15AnchoredAtom4473 Fin15AnchoredAtom4508 Fin15AnchoredAtom4573
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

theorem fin15Anchored_clause31524 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2492 chi ∧
      ¬Fin15AnchoredAtom2493 chi ∧
      ¬Fin15AnchoredAtom2495 chi ∧
      ¬Fin15AnchoredAtom2498 chi ∧
      ¬Fin15AnchoredAtom2500 chi ∧
      ¬Fin15AnchoredAtom2502 chi ∧
      ¬Fin15AnchoredAtom2505 chi ∧
      ¬Fin15AnchoredAtom2508 chi ∧
      ¬Fin15AnchoredAtom2511 chi ∧
      ¬Fin15AnchoredAtom2520 chi ∧
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
      ¬Fin15AnchoredAtom4362 chi ∧
      ¬Fin15AnchoredAtom4364 chi ∧
      ¬Fin15AnchoredAtom4367 chi ∧
      ¬Fin15AnchoredAtom4370 chi ∧
      ¬Fin15AnchoredAtom4373 chi ∧
      ¬Fin15AnchoredAtom4382 chi ∧
      ¬Fin15AnchoredAtom4391 chi ∧
      ¬Fin15AnchoredAtom4394 chi ∧
      ¬Fin15AnchoredAtom4403 chi ∧
      ¬Fin15AnchoredAtom4418 chi ∧
      ¬Fin15AnchoredAtom4447 chi ∧
      ¬Fin15AnchoredAtom4450 chi ∧
      ¬Fin15AnchoredAtom4459 chi ∧
      ¬Fin15AnchoredAtom4474 chi ∧
      ¬Fin15AnchoredAtom4509 chi ∧
      ¬Fin15AnchoredAtom4573 chi ∧
      ¬Fin15AnchoredAtom4576 chi ∧
      ¬Fin15AnchoredAtom4585 chi ∧
      ¬Fin15AnchoredAtom4600 chi ∧
      ¬Fin15AnchoredAtom4635 chi ∧
      ¬Fin15AnchoredAtom4705 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 5, 6, 7, 8, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09713
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2492 Fin15AnchoredAtom2493 Fin15AnchoredAtom2495
    Fin15AnchoredAtom2498 Fin15AnchoredAtom2500 Fin15AnchoredAtom2502 Fin15AnchoredAtom2505
    Fin15AnchoredAtom2508 Fin15AnchoredAtom2511 Fin15AnchoredAtom2520 Fin15AnchoredAtom2528
    Fin15AnchoredAtom2530 Fin15AnchoredAtom2533 Fin15AnchoredAtom2536 Fin15AnchoredAtom2539
    Fin15AnchoredAtom2548 Fin15AnchoredAtom2557 Fin15AnchoredAtom2560 Fin15AnchoredAtom2569
    Fin15AnchoredAtom2584 Fin15AnchoredAtom2612 Fin15AnchoredAtom2614 Fin15AnchoredAtom2617
    Fin15AnchoredAtom2620 Fin15AnchoredAtom2623 Fin15AnchoredAtom2632 Fin15AnchoredAtom2641
    Fin15AnchoredAtom2644 Fin15AnchoredAtom2653 Fin15AnchoredAtom2668 Fin15AnchoredAtom2697
    Fin15AnchoredAtom2700 Fin15AnchoredAtom2709 Fin15AnchoredAtom2724 Fin15AnchoredAtom2759
    Fin15AnchoredAtom4362 Fin15AnchoredAtom4364 Fin15AnchoredAtom4367 Fin15AnchoredAtom4370
    Fin15AnchoredAtom4373 Fin15AnchoredAtom4382 Fin15AnchoredAtom4391 Fin15AnchoredAtom4394
    Fin15AnchoredAtom4403 Fin15AnchoredAtom4418 Fin15AnchoredAtom4447 Fin15AnchoredAtom4450
    Fin15AnchoredAtom4459 Fin15AnchoredAtom4474 Fin15AnchoredAtom4509 Fin15AnchoredAtom4573
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

theorem fin15Anchored_clause31525 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2492 chi ∧
      ¬Fin15AnchoredAtom2493 chi ∧
      ¬Fin15AnchoredAtom2495 chi ∧
      ¬Fin15AnchoredAtom2499 chi ∧
      ¬Fin15AnchoredAtom2500 chi ∧
      ¬Fin15AnchoredAtom2502 chi ∧
      ¬Fin15AnchoredAtom2506 chi ∧
      ¬Fin15AnchoredAtom2508 chi ∧
      ¬Fin15AnchoredAtom2512 chi ∧
      ¬Fin15AnchoredAtom2521 chi ∧
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
      ¬Fin15AnchoredAtom2612 chi ∧
      ¬Fin15AnchoredAtom2614 chi ∧
      ¬Fin15AnchoredAtom2618 chi ∧
      ¬Fin15AnchoredAtom2620 chi ∧
      ¬Fin15AnchoredAtom2624 chi ∧
      ¬Fin15AnchoredAtom2633 chi ∧
      ¬Fin15AnchoredAtom2641 chi ∧
      ¬Fin15AnchoredAtom2645 chi ∧
      ¬Fin15AnchoredAtom2654 chi ∧
      ¬Fin15AnchoredAtom2669 chi ∧
      ¬Fin15AnchoredAtom2697 chi ∧
      ¬Fin15AnchoredAtom2701 chi ∧
      ¬Fin15AnchoredAtom2710 chi ∧
      ¬Fin15AnchoredAtom2725 chi ∧
      ¬Fin15AnchoredAtom2760 chi ∧
      ¬Fin15AnchoredAtom4362 chi ∧
      ¬Fin15AnchoredAtom4364 chi ∧
      ¬Fin15AnchoredAtom4368 chi ∧
      ¬Fin15AnchoredAtom4370 chi ∧
      ¬Fin15AnchoredAtom4374 chi ∧
      ¬Fin15AnchoredAtom4383 chi ∧
      ¬Fin15AnchoredAtom4391 chi ∧
      ¬Fin15AnchoredAtom4395 chi ∧
      ¬Fin15AnchoredAtom4404 chi ∧
      ¬Fin15AnchoredAtom4419 chi ∧
      ¬Fin15AnchoredAtom4447 chi ∧
      ¬Fin15AnchoredAtom4451 chi ∧
      ¬Fin15AnchoredAtom4460 chi ∧
      ¬Fin15AnchoredAtom4475 chi ∧
      ¬Fin15AnchoredAtom4510 chi ∧
      ¬Fin15AnchoredAtom4573 chi ∧
      ¬Fin15AnchoredAtom4577 chi ∧
      ¬Fin15AnchoredAtom4586 chi ∧
      ¬Fin15AnchoredAtom4601 chi ∧
      ¬Fin15AnchoredAtom4636 chi ∧
      ¬Fin15AnchoredAtom4706 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 5, 6, 7, 8, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17905
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2492 Fin15AnchoredAtom2493 Fin15AnchoredAtom2495
    Fin15AnchoredAtom2499 Fin15AnchoredAtom2500 Fin15AnchoredAtom2502 Fin15AnchoredAtom2506
    Fin15AnchoredAtom2508 Fin15AnchoredAtom2512 Fin15AnchoredAtom2521 Fin15AnchoredAtom2528
    Fin15AnchoredAtom2530 Fin15AnchoredAtom2534 Fin15AnchoredAtom2536 Fin15AnchoredAtom2540
    Fin15AnchoredAtom2549 Fin15AnchoredAtom2557 Fin15AnchoredAtom2561 Fin15AnchoredAtom2570
    Fin15AnchoredAtom2585 Fin15AnchoredAtom2612 Fin15AnchoredAtom2614 Fin15AnchoredAtom2618
    Fin15AnchoredAtom2620 Fin15AnchoredAtom2624 Fin15AnchoredAtom2633 Fin15AnchoredAtom2641
    Fin15AnchoredAtom2645 Fin15AnchoredAtom2654 Fin15AnchoredAtom2669 Fin15AnchoredAtom2697
    Fin15AnchoredAtom2701 Fin15AnchoredAtom2710 Fin15AnchoredAtom2725 Fin15AnchoredAtom2760
    Fin15AnchoredAtom4362 Fin15AnchoredAtom4364 Fin15AnchoredAtom4368 Fin15AnchoredAtom4370
    Fin15AnchoredAtom4374 Fin15AnchoredAtom4383 Fin15AnchoredAtom4391 Fin15AnchoredAtom4395
    Fin15AnchoredAtom4404 Fin15AnchoredAtom4419 Fin15AnchoredAtom4447 Fin15AnchoredAtom4451
    Fin15AnchoredAtom4460 Fin15AnchoredAtom4475 Fin15AnchoredAtom4510 Fin15AnchoredAtom4573
    Fin15AnchoredAtom4577 Fin15AnchoredAtom4586 Fin15AnchoredAtom4601 Fin15AnchoredAtom4636
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

theorem fin15Anchored_clause31526 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2492 chi ∧
      ¬Fin15AnchoredAtom2493 chi ∧
      ¬Fin15AnchoredAtom2497 chi ∧
      ¬Fin15AnchoredAtom2499 chi ∧
      ¬Fin15AnchoredAtom2500 chi ∧
      ¬Fin15AnchoredAtom2504 chi ∧
      ¬Fin15AnchoredAtom2506 chi ∧
      ¬Fin15AnchoredAtom2510 chi ∧
      ¬Fin15AnchoredAtom2512 chi ∧
      ¬Fin15AnchoredAtom2526 chi ∧
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
      ¬Fin15AnchoredAtom2612 chi ∧
      ¬Fin15AnchoredAtom2616 chi ∧
      ¬Fin15AnchoredAtom2618 chi ∧
      ¬Fin15AnchoredAtom2622 chi ∧
      ¬Fin15AnchoredAtom2624 chi ∧
      ¬Fin15AnchoredAtom2638 chi ∧
      ¬Fin15AnchoredAtom2643 chi ∧
      ¬Fin15AnchoredAtom2645 chi ∧
      ¬Fin15AnchoredAtom2659 chi ∧
      ¬Fin15AnchoredAtom2674 chi ∧
      ¬Fin15AnchoredAtom2699 chi ∧
      ¬Fin15AnchoredAtom2701 chi ∧
      ¬Fin15AnchoredAtom2715 chi ∧
      ¬Fin15AnchoredAtom2730 chi ∧
      ¬Fin15AnchoredAtom2765 chi ∧
      ¬Fin15AnchoredAtom4362 chi ∧
      ¬Fin15AnchoredAtom4366 chi ∧
      ¬Fin15AnchoredAtom4368 chi ∧
      ¬Fin15AnchoredAtom4372 chi ∧
      ¬Fin15AnchoredAtom4374 chi ∧
      ¬Fin15AnchoredAtom4388 chi ∧
      ¬Fin15AnchoredAtom4393 chi ∧
      ¬Fin15AnchoredAtom4395 chi ∧
      ¬Fin15AnchoredAtom4409 chi ∧
      ¬Fin15AnchoredAtom4424 chi ∧
      ¬Fin15AnchoredAtom4449 chi ∧
      ¬Fin15AnchoredAtom4451 chi ∧
      ¬Fin15AnchoredAtom4465 chi ∧
      ¬Fin15AnchoredAtom4480 chi ∧
      ¬Fin15AnchoredAtom4515 chi ∧
      ¬Fin15AnchoredAtom4575 chi ∧
      ¬Fin15AnchoredAtom4577 chi ∧
      ¬Fin15AnchoredAtom4591 chi ∧
      ¬Fin15AnchoredAtom4606 chi ∧
      ¬Fin15AnchoredAtom4641 chi ∧
      ¬Fin15AnchoredAtom4711 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 5, 6, 7, 8, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask20977
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2492 Fin15AnchoredAtom2493 Fin15AnchoredAtom2497
    Fin15AnchoredAtom2499 Fin15AnchoredAtom2500 Fin15AnchoredAtom2504 Fin15AnchoredAtom2506
    Fin15AnchoredAtom2510 Fin15AnchoredAtom2512 Fin15AnchoredAtom2526 Fin15AnchoredAtom2528
    Fin15AnchoredAtom2532 Fin15AnchoredAtom2534 Fin15AnchoredAtom2538 Fin15AnchoredAtom2540
    Fin15AnchoredAtom2554 Fin15AnchoredAtom2559 Fin15AnchoredAtom2561 Fin15AnchoredAtom2575
    Fin15AnchoredAtom2590 Fin15AnchoredAtom2612 Fin15AnchoredAtom2616 Fin15AnchoredAtom2618
    Fin15AnchoredAtom2622 Fin15AnchoredAtom2624 Fin15AnchoredAtom2638 Fin15AnchoredAtom2643
    Fin15AnchoredAtom2645 Fin15AnchoredAtom2659 Fin15AnchoredAtom2674 Fin15AnchoredAtom2699
    Fin15AnchoredAtom2701 Fin15AnchoredAtom2715 Fin15AnchoredAtom2730 Fin15AnchoredAtom2765
    Fin15AnchoredAtom4362 Fin15AnchoredAtom4366 Fin15AnchoredAtom4368 Fin15AnchoredAtom4372
    Fin15AnchoredAtom4374 Fin15AnchoredAtom4388 Fin15AnchoredAtom4393 Fin15AnchoredAtom4395
    Fin15AnchoredAtom4409 Fin15AnchoredAtom4424 Fin15AnchoredAtom4449 Fin15AnchoredAtom4451
    Fin15AnchoredAtom4465 Fin15AnchoredAtom4480 Fin15AnchoredAtom4515 Fin15AnchoredAtom4575
    Fin15AnchoredAtom4577 Fin15AnchoredAtom4591 Fin15AnchoredAtom4606 Fin15AnchoredAtom4641
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

theorem fin15Anchored_clause31527 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2492 chi ∧
      ¬Fin15AnchoredAtom2493 chi ∧
      ¬Fin15AnchoredAtom2498 chi ∧
      ¬Fin15AnchoredAtom2499 chi ∧
      ¬Fin15AnchoredAtom2500 chi ∧
      ¬Fin15AnchoredAtom2505 chi ∧
      ¬Fin15AnchoredAtom2506 chi ∧
      ¬Fin15AnchoredAtom2511 chi ∧
      ¬Fin15AnchoredAtom2512 chi ∧
      ¬Fin15AnchoredAtom2527 chi ∧
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
      ¬Fin15AnchoredAtom2612 chi ∧
      ¬Fin15AnchoredAtom2617 chi ∧
      ¬Fin15AnchoredAtom2618 chi ∧
      ¬Fin15AnchoredAtom2623 chi ∧
      ¬Fin15AnchoredAtom2624 chi ∧
      ¬Fin15AnchoredAtom2639 chi ∧
      ¬Fin15AnchoredAtom2644 chi ∧
      ¬Fin15AnchoredAtom2645 chi ∧
      ¬Fin15AnchoredAtom2660 chi ∧
      ¬Fin15AnchoredAtom2675 chi ∧
      ¬Fin15AnchoredAtom2700 chi ∧
      ¬Fin15AnchoredAtom2701 chi ∧
      ¬Fin15AnchoredAtom2716 chi ∧
      ¬Fin15AnchoredAtom2731 chi ∧
      ¬Fin15AnchoredAtom2766 chi ∧
      ¬Fin15AnchoredAtom4362 chi ∧
      ¬Fin15AnchoredAtom4367 chi ∧
      ¬Fin15AnchoredAtom4368 chi ∧
      ¬Fin15AnchoredAtom4373 chi ∧
      ¬Fin15AnchoredAtom4374 chi ∧
      ¬Fin15AnchoredAtom4389 chi ∧
      ¬Fin15AnchoredAtom4394 chi ∧
      ¬Fin15AnchoredAtom4395 chi ∧
      ¬Fin15AnchoredAtom4410 chi ∧
      ¬Fin15AnchoredAtom4425 chi ∧
      ¬Fin15AnchoredAtom4450 chi ∧
      ¬Fin15AnchoredAtom4451 chi ∧
      ¬Fin15AnchoredAtom4466 chi ∧
      ¬Fin15AnchoredAtom4481 chi ∧
      ¬Fin15AnchoredAtom4516 chi ∧
      ¬Fin15AnchoredAtom4576 chi ∧
      ¬Fin15AnchoredAtom4577 chi ∧
      ¬Fin15AnchoredAtom4592 chi ∧
      ¬Fin15AnchoredAtom4607 chi ∧
      ¬Fin15AnchoredAtom4642 chi ∧
      ¬Fin15AnchoredAtom4712 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 5, 6, 7, 8, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25073
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2492 Fin15AnchoredAtom2493 Fin15AnchoredAtom2498
    Fin15AnchoredAtom2499 Fin15AnchoredAtom2500 Fin15AnchoredAtom2505 Fin15AnchoredAtom2506
    Fin15AnchoredAtom2511 Fin15AnchoredAtom2512 Fin15AnchoredAtom2527 Fin15AnchoredAtom2528
    Fin15AnchoredAtom2533 Fin15AnchoredAtom2534 Fin15AnchoredAtom2539 Fin15AnchoredAtom2540
    Fin15AnchoredAtom2555 Fin15AnchoredAtom2560 Fin15AnchoredAtom2561 Fin15AnchoredAtom2576
    Fin15AnchoredAtom2591 Fin15AnchoredAtom2612 Fin15AnchoredAtom2617 Fin15AnchoredAtom2618
    Fin15AnchoredAtom2623 Fin15AnchoredAtom2624 Fin15AnchoredAtom2639 Fin15AnchoredAtom2644
    Fin15AnchoredAtom2645 Fin15AnchoredAtom2660 Fin15AnchoredAtom2675 Fin15AnchoredAtom2700
    Fin15AnchoredAtom2701 Fin15AnchoredAtom2716 Fin15AnchoredAtom2731 Fin15AnchoredAtom2766
    Fin15AnchoredAtom4362 Fin15AnchoredAtom4367 Fin15AnchoredAtom4368 Fin15AnchoredAtom4373
    Fin15AnchoredAtom4374 Fin15AnchoredAtom4389 Fin15AnchoredAtom4394 Fin15AnchoredAtom4395
    Fin15AnchoredAtom4410 Fin15AnchoredAtom4425 Fin15AnchoredAtom4450 Fin15AnchoredAtom4451
    Fin15AnchoredAtom4466 Fin15AnchoredAtom4481 Fin15AnchoredAtom4516 Fin15AnchoredAtom4576
    Fin15AnchoredAtom4577 Fin15AnchoredAtom4592 Fin15AnchoredAtom4607 Fin15AnchoredAtom4642
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

theorem fin15Anchored_clause31528 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2492 chi ∧
      ¬Fin15AnchoredAtom2494 chi ∧
      ¬Fin15AnchoredAtom2495 chi ∧
      ¬Fin15AnchoredAtom2497 chi ∧
      ¬Fin15AnchoredAtom2501 chi ∧
      ¬Fin15AnchoredAtom2502 chi ∧
      ¬Fin15AnchoredAtom2504 chi ∧
      ¬Fin15AnchoredAtom2513 chi ∧
      ¬Fin15AnchoredAtom2515 chi ∧
      ¬Fin15AnchoredAtom2519 chi ∧
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
      ¬Fin15AnchoredAtom4363 chi ∧
      ¬Fin15AnchoredAtom4364 chi ∧
      ¬Fin15AnchoredAtom4366 chi ∧
      ¬Fin15AnchoredAtom4375 chi ∧
      ¬Fin15AnchoredAtom4377 chi ∧
      ¬Fin15AnchoredAtom4381 chi ∧
      ¬Fin15AnchoredAtom4396 chi ∧
      ¬Fin15AnchoredAtom4398 chi ∧
      ¬Fin15AnchoredAtom4402 chi ∧
      ¬Fin15AnchoredAtom4427 chi ∧
      ¬Fin15AnchoredAtom4452 chi ∧
      ¬Fin15AnchoredAtom4454 chi ∧
      ¬Fin15AnchoredAtom4458 chi ∧
      ¬Fin15AnchoredAtom4483 chi ∧
      ¬Fin15AnchoredAtom4518 chi ∧
      ¬Fin15AnchoredAtom4578 chi ∧
      ¬Fin15AnchoredAtom4580 chi ∧
      ¬Fin15AnchoredAtom4584 chi ∧
      ¬Fin15AnchoredAtom4609 chi ∧
      ¬Fin15AnchoredAtom4644 chi ∧
      ¬Fin15AnchoredAtom4714 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 5, 6, 7, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05873
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2492 Fin15AnchoredAtom2494 Fin15AnchoredAtom2495
    Fin15AnchoredAtom2497 Fin15AnchoredAtom2501 Fin15AnchoredAtom2502 Fin15AnchoredAtom2504
    Fin15AnchoredAtom2513 Fin15AnchoredAtom2515 Fin15AnchoredAtom2519 Fin15AnchoredAtom2529
    Fin15AnchoredAtom2530 Fin15AnchoredAtom2532 Fin15AnchoredAtom2541 Fin15AnchoredAtom2543
    Fin15AnchoredAtom2547 Fin15AnchoredAtom2562 Fin15AnchoredAtom2564 Fin15AnchoredAtom2568
    Fin15AnchoredAtom2593 Fin15AnchoredAtom2613 Fin15AnchoredAtom2614 Fin15AnchoredAtom2616
    Fin15AnchoredAtom2625 Fin15AnchoredAtom2627 Fin15AnchoredAtom2631 Fin15AnchoredAtom2646
    Fin15AnchoredAtom2648 Fin15AnchoredAtom2652 Fin15AnchoredAtom2677 Fin15AnchoredAtom2702
    Fin15AnchoredAtom2704 Fin15AnchoredAtom2708 Fin15AnchoredAtom2733 Fin15AnchoredAtom2768
    Fin15AnchoredAtom4363 Fin15AnchoredAtom4364 Fin15AnchoredAtom4366 Fin15AnchoredAtom4375
    Fin15AnchoredAtom4377 Fin15AnchoredAtom4381 Fin15AnchoredAtom4396 Fin15AnchoredAtom4398
    Fin15AnchoredAtom4402 Fin15AnchoredAtom4427 Fin15AnchoredAtom4452 Fin15AnchoredAtom4454
    Fin15AnchoredAtom4458 Fin15AnchoredAtom4483 Fin15AnchoredAtom4518 Fin15AnchoredAtom4578
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

theorem fin15Anchored_clause31529 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2492 chi ∧
      ¬Fin15AnchoredAtom2494 chi ∧
      ¬Fin15AnchoredAtom2495 chi ∧
      ¬Fin15AnchoredAtom2498 chi ∧
      ¬Fin15AnchoredAtom2501 chi ∧
      ¬Fin15AnchoredAtom2502 chi ∧
      ¬Fin15AnchoredAtom2505 chi ∧
      ¬Fin15AnchoredAtom2513 chi ∧
      ¬Fin15AnchoredAtom2516 chi ∧
      ¬Fin15AnchoredAtom2520 chi ∧
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
      ¬Fin15AnchoredAtom4363 chi ∧
      ¬Fin15AnchoredAtom4364 chi ∧
      ¬Fin15AnchoredAtom4367 chi ∧
      ¬Fin15AnchoredAtom4375 chi ∧
      ¬Fin15AnchoredAtom4378 chi ∧
      ¬Fin15AnchoredAtom4382 chi ∧
      ¬Fin15AnchoredAtom4396 chi ∧
      ¬Fin15AnchoredAtom4399 chi ∧
      ¬Fin15AnchoredAtom4403 chi ∧
      ¬Fin15AnchoredAtom4428 chi ∧
      ¬Fin15AnchoredAtom4452 chi ∧
      ¬Fin15AnchoredAtom4455 chi ∧
      ¬Fin15AnchoredAtom4459 chi ∧
      ¬Fin15AnchoredAtom4484 chi ∧
      ¬Fin15AnchoredAtom4519 chi ∧
      ¬Fin15AnchoredAtom4578 chi ∧
      ¬Fin15AnchoredAtom4581 chi ∧
      ¬Fin15AnchoredAtom4585 chi ∧
      ¬Fin15AnchoredAtom4610 chi ∧
      ¬Fin15AnchoredAtom4645 chi ∧
      ¬Fin15AnchoredAtom4715 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 5, 6, 7, 9, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09969
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2492 Fin15AnchoredAtom2494 Fin15AnchoredAtom2495
    Fin15AnchoredAtom2498 Fin15AnchoredAtom2501 Fin15AnchoredAtom2502 Fin15AnchoredAtom2505
    Fin15AnchoredAtom2513 Fin15AnchoredAtom2516 Fin15AnchoredAtom2520 Fin15AnchoredAtom2529
    Fin15AnchoredAtom2530 Fin15AnchoredAtom2533 Fin15AnchoredAtom2541 Fin15AnchoredAtom2544
    Fin15AnchoredAtom2548 Fin15AnchoredAtom2562 Fin15AnchoredAtom2565 Fin15AnchoredAtom2569
    Fin15AnchoredAtom2594 Fin15AnchoredAtom2613 Fin15AnchoredAtom2614 Fin15AnchoredAtom2617
    Fin15AnchoredAtom2625 Fin15AnchoredAtom2628 Fin15AnchoredAtom2632 Fin15AnchoredAtom2646
    Fin15AnchoredAtom2649 Fin15AnchoredAtom2653 Fin15AnchoredAtom2678 Fin15AnchoredAtom2702
    Fin15AnchoredAtom2705 Fin15AnchoredAtom2709 Fin15AnchoredAtom2734 Fin15AnchoredAtom2769
    Fin15AnchoredAtom4363 Fin15AnchoredAtom4364 Fin15AnchoredAtom4367 Fin15AnchoredAtom4375
    Fin15AnchoredAtom4378 Fin15AnchoredAtom4382 Fin15AnchoredAtom4396 Fin15AnchoredAtom4399
    Fin15AnchoredAtom4403 Fin15AnchoredAtom4428 Fin15AnchoredAtom4452 Fin15AnchoredAtom4455
    Fin15AnchoredAtom4459 Fin15AnchoredAtom4484 Fin15AnchoredAtom4519 Fin15AnchoredAtom4578
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

theorem fin15Anchored_clause31530 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2492 chi ∧
      ¬Fin15AnchoredAtom2494 chi ∧
      ¬Fin15AnchoredAtom2495 chi ∧
      ¬Fin15AnchoredAtom2499 chi ∧
      ¬Fin15AnchoredAtom2501 chi ∧
      ¬Fin15AnchoredAtom2502 chi ∧
      ¬Fin15AnchoredAtom2506 chi ∧
      ¬Fin15AnchoredAtom2513 chi ∧
      ¬Fin15AnchoredAtom2517 chi ∧
      ¬Fin15AnchoredAtom2521 chi ∧
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
      ¬Fin15AnchoredAtom4363 chi ∧
      ¬Fin15AnchoredAtom4364 chi ∧
      ¬Fin15AnchoredAtom4368 chi ∧
      ¬Fin15AnchoredAtom4375 chi ∧
      ¬Fin15AnchoredAtom4379 chi ∧
      ¬Fin15AnchoredAtom4383 chi ∧
      ¬Fin15AnchoredAtom4396 chi ∧
      ¬Fin15AnchoredAtom4400 chi ∧
      ¬Fin15AnchoredAtom4404 chi ∧
      ¬Fin15AnchoredAtom4429 chi ∧
      ¬Fin15AnchoredAtom4452 chi ∧
      ¬Fin15AnchoredAtom4456 chi ∧
      ¬Fin15AnchoredAtom4460 chi ∧
      ¬Fin15AnchoredAtom4485 chi ∧
      ¬Fin15AnchoredAtom4520 chi ∧
      ¬Fin15AnchoredAtom4578 chi ∧
      ¬Fin15AnchoredAtom4582 chi ∧
      ¬Fin15AnchoredAtom4586 chi ∧
      ¬Fin15AnchoredAtom4611 chi ∧
      ¬Fin15AnchoredAtom4646 chi ∧
      ¬Fin15AnchoredAtom4716 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 5, 6, 7, 9, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask18161
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2492 Fin15AnchoredAtom2494 Fin15AnchoredAtom2495
    Fin15AnchoredAtom2499 Fin15AnchoredAtom2501 Fin15AnchoredAtom2502 Fin15AnchoredAtom2506
    Fin15AnchoredAtom2513 Fin15AnchoredAtom2517 Fin15AnchoredAtom2521 Fin15AnchoredAtom2529
    Fin15AnchoredAtom2530 Fin15AnchoredAtom2534 Fin15AnchoredAtom2541 Fin15AnchoredAtom2545
    Fin15AnchoredAtom2549 Fin15AnchoredAtom2562 Fin15AnchoredAtom2566 Fin15AnchoredAtom2570
    Fin15AnchoredAtom2595 Fin15AnchoredAtom2613 Fin15AnchoredAtom2614 Fin15AnchoredAtom2618
    Fin15AnchoredAtom2625 Fin15AnchoredAtom2629 Fin15AnchoredAtom2633 Fin15AnchoredAtom2646
    Fin15AnchoredAtom2650 Fin15AnchoredAtom2654 Fin15AnchoredAtom2679 Fin15AnchoredAtom2702
    Fin15AnchoredAtom2706 Fin15AnchoredAtom2710 Fin15AnchoredAtom2735 Fin15AnchoredAtom2770
    Fin15AnchoredAtom4363 Fin15AnchoredAtom4364 Fin15AnchoredAtom4368 Fin15AnchoredAtom4375
    Fin15AnchoredAtom4379 Fin15AnchoredAtom4383 Fin15AnchoredAtom4396 Fin15AnchoredAtom4400
    Fin15AnchoredAtom4404 Fin15AnchoredAtom4429 Fin15AnchoredAtom4452 Fin15AnchoredAtom4456
    Fin15AnchoredAtom4460 Fin15AnchoredAtom4485 Fin15AnchoredAtom4520 Fin15AnchoredAtom4578
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

theorem fin15Anchored_clause31531 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2492 chi ∧
      ¬Fin15AnchoredAtom2494 chi ∧
      ¬Fin15AnchoredAtom2497 chi ∧
      ¬Fin15AnchoredAtom2498 chi ∧
      ¬Fin15AnchoredAtom2501 chi ∧
      ¬Fin15AnchoredAtom2504 chi ∧
      ¬Fin15AnchoredAtom2505 chi ∧
      ¬Fin15AnchoredAtom2515 chi ∧
      ¬Fin15AnchoredAtom2516 chi ∧
      ¬Fin15AnchoredAtom2525 chi ∧
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
      ¬Fin15AnchoredAtom4363 chi ∧
      ¬Fin15AnchoredAtom4366 chi ∧
      ¬Fin15AnchoredAtom4367 chi ∧
      ¬Fin15AnchoredAtom4377 chi ∧
      ¬Fin15AnchoredAtom4378 chi ∧
      ¬Fin15AnchoredAtom4387 chi ∧
      ¬Fin15AnchoredAtom4398 chi ∧
      ¬Fin15AnchoredAtom4399 chi ∧
      ¬Fin15AnchoredAtom4408 chi ∧
      ¬Fin15AnchoredAtom4433 chi ∧
      ¬Fin15AnchoredAtom4454 chi ∧
      ¬Fin15AnchoredAtom4455 chi ∧
      ¬Fin15AnchoredAtom4464 chi ∧
      ¬Fin15AnchoredAtom4489 chi ∧
      ¬Fin15AnchoredAtom4524 chi ∧
      ¬Fin15AnchoredAtom4580 chi ∧
      ¬Fin15AnchoredAtom4581 chi ∧
      ¬Fin15AnchoredAtom4590 chi ∧
      ¬Fin15AnchoredAtom4615 chi ∧
      ¬Fin15AnchoredAtom4650 chi ∧
      ¬Fin15AnchoredAtom4720 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 5, 6, 7, 9, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13041
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2492 Fin15AnchoredAtom2494 Fin15AnchoredAtom2497
    Fin15AnchoredAtom2498 Fin15AnchoredAtom2501 Fin15AnchoredAtom2504 Fin15AnchoredAtom2505
    Fin15AnchoredAtom2515 Fin15AnchoredAtom2516 Fin15AnchoredAtom2525 Fin15AnchoredAtom2529
    Fin15AnchoredAtom2532 Fin15AnchoredAtom2533 Fin15AnchoredAtom2543 Fin15AnchoredAtom2544
    Fin15AnchoredAtom2553 Fin15AnchoredAtom2564 Fin15AnchoredAtom2565 Fin15AnchoredAtom2574
    Fin15AnchoredAtom2599 Fin15AnchoredAtom2613 Fin15AnchoredAtom2616 Fin15AnchoredAtom2617
    Fin15AnchoredAtom2627 Fin15AnchoredAtom2628 Fin15AnchoredAtom2637 Fin15AnchoredAtom2648
    Fin15AnchoredAtom2649 Fin15AnchoredAtom2658 Fin15AnchoredAtom2683 Fin15AnchoredAtom2704
    Fin15AnchoredAtom2705 Fin15AnchoredAtom2714 Fin15AnchoredAtom2739 Fin15AnchoredAtom2774
    Fin15AnchoredAtom4363 Fin15AnchoredAtom4366 Fin15AnchoredAtom4367 Fin15AnchoredAtom4377
    Fin15AnchoredAtom4378 Fin15AnchoredAtom4387 Fin15AnchoredAtom4398 Fin15AnchoredAtom4399
    Fin15AnchoredAtom4408 Fin15AnchoredAtom4433 Fin15AnchoredAtom4454 Fin15AnchoredAtom4455
    Fin15AnchoredAtom4464 Fin15AnchoredAtom4489 Fin15AnchoredAtom4524 Fin15AnchoredAtom4580
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

theorem fin15Anchored_clause31532 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2492 chi ∧
      ¬Fin15AnchoredAtom2494 chi ∧
      ¬Fin15AnchoredAtom2497 chi ∧
      ¬Fin15AnchoredAtom2499 chi ∧
      ¬Fin15AnchoredAtom2501 chi ∧
      ¬Fin15AnchoredAtom2504 chi ∧
      ¬Fin15AnchoredAtom2506 chi ∧
      ¬Fin15AnchoredAtom2515 chi ∧
      ¬Fin15AnchoredAtom2517 chi ∧
      ¬Fin15AnchoredAtom2526 chi ∧
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
      ¬Fin15AnchoredAtom4363 chi ∧
      ¬Fin15AnchoredAtom4366 chi ∧
      ¬Fin15AnchoredAtom4368 chi ∧
      ¬Fin15AnchoredAtom4377 chi ∧
      ¬Fin15AnchoredAtom4379 chi ∧
      ¬Fin15AnchoredAtom4388 chi ∧
      ¬Fin15AnchoredAtom4398 chi ∧
      ¬Fin15AnchoredAtom4400 chi ∧
      ¬Fin15AnchoredAtom4409 chi ∧
      ¬Fin15AnchoredAtom4434 chi ∧
      ¬Fin15AnchoredAtom4454 chi ∧
      ¬Fin15AnchoredAtom4456 chi ∧
      ¬Fin15AnchoredAtom4465 chi ∧
      ¬Fin15AnchoredAtom4490 chi ∧
      ¬Fin15AnchoredAtom4525 chi ∧
      ¬Fin15AnchoredAtom4580 chi ∧
      ¬Fin15AnchoredAtom4582 chi ∧
      ¬Fin15AnchoredAtom4591 chi ∧
      ¬Fin15AnchoredAtom4616 chi ∧
      ¬Fin15AnchoredAtom4651 chi ∧
      ¬Fin15AnchoredAtom4721 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 5, 6, 7, 9, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21233
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2492 Fin15AnchoredAtom2494 Fin15AnchoredAtom2497
    Fin15AnchoredAtom2499 Fin15AnchoredAtom2501 Fin15AnchoredAtom2504 Fin15AnchoredAtom2506
    Fin15AnchoredAtom2515 Fin15AnchoredAtom2517 Fin15AnchoredAtom2526 Fin15AnchoredAtom2529
    Fin15AnchoredAtom2532 Fin15AnchoredAtom2534 Fin15AnchoredAtom2543 Fin15AnchoredAtom2545
    Fin15AnchoredAtom2554 Fin15AnchoredAtom2564 Fin15AnchoredAtom2566 Fin15AnchoredAtom2575
    Fin15AnchoredAtom2600 Fin15AnchoredAtom2613 Fin15AnchoredAtom2616 Fin15AnchoredAtom2618
    Fin15AnchoredAtom2627 Fin15AnchoredAtom2629 Fin15AnchoredAtom2638 Fin15AnchoredAtom2648
    Fin15AnchoredAtom2650 Fin15AnchoredAtom2659 Fin15AnchoredAtom2684 Fin15AnchoredAtom2704
    Fin15AnchoredAtom2706 Fin15AnchoredAtom2715 Fin15AnchoredAtom2740 Fin15AnchoredAtom2775
    Fin15AnchoredAtom4363 Fin15AnchoredAtom4366 Fin15AnchoredAtom4368 Fin15AnchoredAtom4377
    Fin15AnchoredAtom4379 Fin15AnchoredAtom4388 Fin15AnchoredAtom4398 Fin15AnchoredAtom4400
    Fin15AnchoredAtom4409 Fin15AnchoredAtom4434 Fin15AnchoredAtom4454 Fin15AnchoredAtom4456
    Fin15AnchoredAtom4465 Fin15AnchoredAtom4490 Fin15AnchoredAtom4525 Fin15AnchoredAtom4580
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

theorem fin15Anchored_clause31533 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2492 chi ∧
      ¬Fin15AnchoredAtom2494 chi ∧
      ¬Fin15AnchoredAtom2498 chi ∧
      ¬Fin15AnchoredAtom2499 chi ∧
      ¬Fin15AnchoredAtom2501 chi ∧
      ¬Fin15AnchoredAtom2505 chi ∧
      ¬Fin15AnchoredAtom2506 chi ∧
      ¬Fin15AnchoredAtom2516 chi ∧
      ¬Fin15AnchoredAtom2517 chi ∧
      ¬Fin15AnchoredAtom2527 chi ∧
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
      ¬Fin15AnchoredAtom4363 chi ∧
      ¬Fin15AnchoredAtom4367 chi ∧
      ¬Fin15AnchoredAtom4368 chi ∧
      ¬Fin15AnchoredAtom4378 chi ∧
      ¬Fin15AnchoredAtom4379 chi ∧
      ¬Fin15AnchoredAtom4389 chi ∧
      ¬Fin15AnchoredAtom4399 chi ∧
      ¬Fin15AnchoredAtom4400 chi ∧
      ¬Fin15AnchoredAtom4410 chi ∧
      ¬Fin15AnchoredAtom4435 chi ∧
      ¬Fin15AnchoredAtom4455 chi ∧
      ¬Fin15AnchoredAtom4456 chi ∧
      ¬Fin15AnchoredAtom4466 chi ∧
      ¬Fin15AnchoredAtom4491 chi ∧
      ¬Fin15AnchoredAtom4526 chi ∧
      ¬Fin15AnchoredAtom4581 chi ∧
      ¬Fin15AnchoredAtom4582 chi ∧
      ¬Fin15AnchoredAtom4592 chi ∧
      ¬Fin15AnchoredAtom4617 chi ∧
      ¬Fin15AnchoredAtom4652 chi ∧
      ¬Fin15AnchoredAtom4722 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 5, 6, 7, 9, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25329
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2492 Fin15AnchoredAtom2494 Fin15AnchoredAtom2498
    Fin15AnchoredAtom2499 Fin15AnchoredAtom2501 Fin15AnchoredAtom2505 Fin15AnchoredAtom2506
    Fin15AnchoredAtom2516 Fin15AnchoredAtom2517 Fin15AnchoredAtom2527 Fin15AnchoredAtom2529
    Fin15AnchoredAtom2533 Fin15AnchoredAtom2534 Fin15AnchoredAtom2544 Fin15AnchoredAtom2545
    Fin15AnchoredAtom2555 Fin15AnchoredAtom2565 Fin15AnchoredAtom2566 Fin15AnchoredAtom2576
    Fin15AnchoredAtom2601 Fin15AnchoredAtom2613 Fin15AnchoredAtom2617 Fin15AnchoredAtom2618
    Fin15AnchoredAtom2628 Fin15AnchoredAtom2629 Fin15AnchoredAtom2639 Fin15AnchoredAtom2649
    Fin15AnchoredAtom2650 Fin15AnchoredAtom2660 Fin15AnchoredAtom2685 Fin15AnchoredAtom2705
    Fin15AnchoredAtom2706 Fin15AnchoredAtom2716 Fin15AnchoredAtom2741 Fin15AnchoredAtom2776
    Fin15AnchoredAtom4363 Fin15AnchoredAtom4367 Fin15AnchoredAtom4368 Fin15AnchoredAtom4378
    Fin15AnchoredAtom4379 Fin15AnchoredAtom4389 Fin15AnchoredAtom4399 Fin15AnchoredAtom4400
    Fin15AnchoredAtom4410 Fin15AnchoredAtom4435 Fin15AnchoredAtom4455 Fin15AnchoredAtom4456
    Fin15AnchoredAtom4466 Fin15AnchoredAtom4491 Fin15AnchoredAtom4526 Fin15AnchoredAtom4581
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

theorem fin15Anchored_clause31534 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2492 chi ∧
      ¬Fin15AnchoredAtom2495 chi ∧
      ¬Fin15AnchoredAtom2496 chi ∧
      ¬Fin15AnchoredAtom2497 chi ∧
      ¬Fin15AnchoredAtom2502 chi ∧
      ¬Fin15AnchoredAtom2503 chi ∧
      ¬Fin15AnchoredAtom2504 chi ∧
      ¬Fin15AnchoredAtom2518 chi ∧
      ¬Fin15AnchoredAtom2519 chi ∧
      ¬Fin15AnchoredAtom2522 chi ∧
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
      ¬Fin15AnchoredAtom2614 chi ∧
      ¬Fin15AnchoredAtom2615 chi ∧
      ¬Fin15AnchoredAtom2616 chi ∧
      ¬Fin15AnchoredAtom2630 chi ∧
      ¬Fin15AnchoredAtom2631 chi ∧
      ¬Fin15AnchoredAtom2634 chi ∧
      ¬Fin15AnchoredAtom2651 chi ∧
      ¬Fin15AnchoredAtom2652 chi ∧
      ¬Fin15AnchoredAtom2655 chi ∧
      ¬Fin15AnchoredAtom2686 chi ∧
      ¬Fin15AnchoredAtom2707 chi ∧
      ¬Fin15AnchoredAtom2708 chi ∧
      ¬Fin15AnchoredAtom2711 chi ∧
      ¬Fin15AnchoredAtom2742 chi ∧
      ¬Fin15AnchoredAtom2777 chi ∧
      ¬Fin15AnchoredAtom4364 chi ∧
      ¬Fin15AnchoredAtom4365 chi ∧
      ¬Fin15AnchoredAtom4366 chi ∧
      ¬Fin15AnchoredAtom4380 chi ∧
      ¬Fin15AnchoredAtom4381 chi ∧
      ¬Fin15AnchoredAtom4384 chi ∧
      ¬Fin15AnchoredAtom4401 chi ∧
      ¬Fin15AnchoredAtom4402 chi ∧
      ¬Fin15AnchoredAtom4405 chi ∧
      ¬Fin15AnchoredAtom4436 chi ∧
      ¬Fin15AnchoredAtom4457 chi ∧
      ¬Fin15AnchoredAtom4458 chi ∧
      ¬Fin15AnchoredAtom4461 chi ∧
      ¬Fin15AnchoredAtom4492 chi ∧
      ¬Fin15AnchoredAtom4527 chi ∧
      ¬Fin15AnchoredAtom4583 chi ∧
      ¬Fin15AnchoredAtom4584 chi ∧
      ¬Fin15AnchoredAtom4587 chi ∧
      ¬Fin15AnchoredAtom4618 chi ∧
      ¬Fin15AnchoredAtom4653 chi ∧
      ¬Fin15AnchoredAtom4723 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 5, 6, 7, 10, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask07409
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2492 Fin15AnchoredAtom2495 Fin15AnchoredAtom2496
    Fin15AnchoredAtom2497 Fin15AnchoredAtom2502 Fin15AnchoredAtom2503 Fin15AnchoredAtom2504
    Fin15AnchoredAtom2518 Fin15AnchoredAtom2519 Fin15AnchoredAtom2522 Fin15AnchoredAtom2530
    Fin15AnchoredAtom2531 Fin15AnchoredAtom2532 Fin15AnchoredAtom2546 Fin15AnchoredAtom2547
    Fin15AnchoredAtom2550 Fin15AnchoredAtom2567 Fin15AnchoredAtom2568 Fin15AnchoredAtom2571
    Fin15AnchoredAtom2602 Fin15AnchoredAtom2614 Fin15AnchoredAtom2615 Fin15AnchoredAtom2616
    Fin15AnchoredAtom2630 Fin15AnchoredAtom2631 Fin15AnchoredAtom2634 Fin15AnchoredAtom2651
    Fin15AnchoredAtom2652 Fin15AnchoredAtom2655 Fin15AnchoredAtom2686 Fin15AnchoredAtom2707
    Fin15AnchoredAtom2708 Fin15AnchoredAtom2711 Fin15AnchoredAtom2742 Fin15AnchoredAtom2777
    Fin15AnchoredAtom4364 Fin15AnchoredAtom4365 Fin15AnchoredAtom4366 Fin15AnchoredAtom4380
    Fin15AnchoredAtom4381 Fin15AnchoredAtom4384 Fin15AnchoredAtom4401 Fin15AnchoredAtom4402
    Fin15AnchoredAtom4405 Fin15AnchoredAtom4436 Fin15AnchoredAtom4457 Fin15AnchoredAtom4458
    Fin15AnchoredAtom4461 Fin15AnchoredAtom4492 Fin15AnchoredAtom4527 Fin15AnchoredAtom4583
    Fin15AnchoredAtom4584 Fin15AnchoredAtom4587 Fin15AnchoredAtom4618 Fin15AnchoredAtom4653
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

theorem fin15Anchored_clause31535 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2492 chi ∧
      ¬Fin15AnchoredAtom2495 chi ∧
      ¬Fin15AnchoredAtom2497 chi ∧
      ¬Fin15AnchoredAtom2498 chi ∧
      ¬Fin15AnchoredAtom2502 chi ∧
      ¬Fin15AnchoredAtom2504 chi ∧
      ¬Fin15AnchoredAtom2505 chi ∧
      ¬Fin15AnchoredAtom2519 chi ∧
      ¬Fin15AnchoredAtom2520 chi ∧
      ¬Fin15AnchoredAtom2525 chi ∧
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
      ¬Fin15AnchoredAtom4364 chi ∧
      ¬Fin15AnchoredAtom4366 chi ∧
      ¬Fin15AnchoredAtom4367 chi ∧
      ¬Fin15AnchoredAtom4381 chi ∧
      ¬Fin15AnchoredAtom4382 chi ∧
      ¬Fin15AnchoredAtom4387 chi ∧
      ¬Fin15AnchoredAtom4402 chi ∧
      ¬Fin15AnchoredAtom4403 chi ∧
      ¬Fin15AnchoredAtom4408 chi ∧
      ¬Fin15AnchoredAtom4439 chi ∧
      ¬Fin15AnchoredAtom4458 chi ∧
      ¬Fin15AnchoredAtom4459 chi ∧
      ¬Fin15AnchoredAtom4464 chi ∧
      ¬Fin15AnchoredAtom4495 chi ∧
      ¬Fin15AnchoredAtom4530 chi ∧
      ¬Fin15AnchoredAtom4584 chi ∧
      ¬Fin15AnchoredAtom4585 chi ∧
      ¬Fin15AnchoredAtom4590 chi ∧
      ¬Fin15AnchoredAtom4621 chi ∧
      ¬Fin15AnchoredAtom4656 chi ∧
      ¬Fin15AnchoredAtom4726 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 5, 6, 7, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13553
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2492 Fin15AnchoredAtom2495 Fin15AnchoredAtom2497
    Fin15AnchoredAtom2498 Fin15AnchoredAtom2502 Fin15AnchoredAtom2504 Fin15AnchoredAtom2505
    Fin15AnchoredAtom2519 Fin15AnchoredAtom2520 Fin15AnchoredAtom2525 Fin15AnchoredAtom2530
    Fin15AnchoredAtom2532 Fin15AnchoredAtom2533 Fin15AnchoredAtom2547 Fin15AnchoredAtom2548
    Fin15AnchoredAtom2553 Fin15AnchoredAtom2568 Fin15AnchoredAtom2569 Fin15AnchoredAtom2574
    Fin15AnchoredAtom2605 Fin15AnchoredAtom2614 Fin15AnchoredAtom2616 Fin15AnchoredAtom2617
    Fin15AnchoredAtom2631 Fin15AnchoredAtom2632 Fin15AnchoredAtom2637 Fin15AnchoredAtom2652
    Fin15AnchoredAtom2653 Fin15AnchoredAtom2658 Fin15AnchoredAtom2689 Fin15AnchoredAtom2708
    Fin15AnchoredAtom2709 Fin15AnchoredAtom2714 Fin15AnchoredAtom2745 Fin15AnchoredAtom2780
    Fin15AnchoredAtom4364 Fin15AnchoredAtom4366 Fin15AnchoredAtom4367 Fin15AnchoredAtom4381
    Fin15AnchoredAtom4382 Fin15AnchoredAtom4387 Fin15AnchoredAtom4402 Fin15AnchoredAtom4403
    Fin15AnchoredAtom4408 Fin15AnchoredAtom4439 Fin15AnchoredAtom4458 Fin15AnchoredAtom4459
    Fin15AnchoredAtom4464 Fin15AnchoredAtom4495 Fin15AnchoredAtom4530 Fin15AnchoredAtom4584
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

theorem fin15Anchored_clause31536 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2492 chi ∧
      ¬Fin15AnchoredAtom2495 chi ∧
      ¬Fin15AnchoredAtom2497 chi ∧
      ¬Fin15AnchoredAtom2499 chi ∧
      ¬Fin15AnchoredAtom2502 chi ∧
      ¬Fin15AnchoredAtom2504 chi ∧
      ¬Fin15AnchoredAtom2506 chi ∧
      ¬Fin15AnchoredAtom2519 chi ∧
      ¬Fin15AnchoredAtom2521 chi ∧
      ¬Fin15AnchoredAtom2526 chi ∧
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
      ¬Fin15AnchoredAtom4364 chi ∧
      ¬Fin15AnchoredAtom4366 chi ∧
      ¬Fin15AnchoredAtom4368 chi ∧
      ¬Fin15AnchoredAtom4381 chi ∧
      ¬Fin15AnchoredAtom4383 chi ∧
      ¬Fin15AnchoredAtom4388 chi ∧
      ¬Fin15AnchoredAtom4402 chi ∧
      ¬Fin15AnchoredAtom4404 chi ∧
      ¬Fin15AnchoredAtom4409 chi ∧
      ¬Fin15AnchoredAtom4440 chi ∧
      ¬Fin15AnchoredAtom4458 chi ∧
      ¬Fin15AnchoredAtom4460 chi ∧
      ¬Fin15AnchoredAtom4465 chi ∧
      ¬Fin15AnchoredAtom4496 chi ∧
      ¬Fin15AnchoredAtom4531 chi ∧
      ¬Fin15AnchoredAtom4584 chi ∧
      ¬Fin15AnchoredAtom4586 chi ∧
      ¬Fin15AnchoredAtom4591 chi ∧
      ¬Fin15AnchoredAtom4622 chi ∧
      ¬Fin15AnchoredAtom4657 chi ∧
      ¬Fin15AnchoredAtom4727 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 5, 6, 7, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21745
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2492 Fin15AnchoredAtom2495 Fin15AnchoredAtom2497
    Fin15AnchoredAtom2499 Fin15AnchoredAtom2502 Fin15AnchoredAtom2504 Fin15AnchoredAtom2506
    Fin15AnchoredAtom2519 Fin15AnchoredAtom2521 Fin15AnchoredAtom2526 Fin15AnchoredAtom2530
    Fin15AnchoredAtom2532 Fin15AnchoredAtom2534 Fin15AnchoredAtom2547 Fin15AnchoredAtom2549
    Fin15AnchoredAtom2554 Fin15AnchoredAtom2568 Fin15AnchoredAtom2570 Fin15AnchoredAtom2575
    Fin15AnchoredAtom2606 Fin15AnchoredAtom2614 Fin15AnchoredAtom2616 Fin15AnchoredAtom2618
    Fin15AnchoredAtom2631 Fin15AnchoredAtom2633 Fin15AnchoredAtom2638 Fin15AnchoredAtom2652
    Fin15AnchoredAtom2654 Fin15AnchoredAtom2659 Fin15AnchoredAtom2690 Fin15AnchoredAtom2708
    Fin15AnchoredAtom2710 Fin15AnchoredAtom2715 Fin15AnchoredAtom2746 Fin15AnchoredAtom2781
    Fin15AnchoredAtom4364 Fin15AnchoredAtom4366 Fin15AnchoredAtom4368 Fin15AnchoredAtom4381
    Fin15AnchoredAtom4383 Fin15AnchoredAtom4388 Fin15AnchoredAtom4402 Fin15AnchoredAtom4404
    Fin15AnchoredAtom4409 Fin15AnchoredAtom4440 Fin15AnchoredAtom4458 Fin15AnchoredAtom4460
    Fin15AnchoredAtom4465 Fin15AnchoredAtom4496 Fin15AnchoredAtom4531 Fin15AnchoredAtom4584
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

theorem fin15Anchored_clause31537 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2492 chi ∧
      ¬Fin15AnchoredAtom2495 chi ∧
      ¬Fin15AnchoredAtom2498 chi ∧
      ¬Fin15AnchoredAtom2499 chi ∧
      ¬Fin15AnchoredAtom2502 chi ∧
      ¬Fin15AnchoredAtom2505 chi ∧
      ¬Fin15AnchoredAtom2506 chi ∧
      ¬Fin15AnchoredAtom2520 chi ∧
      ¬Fin15AnchoredAtom2521 chi ∧
      ¬Fin15AnchoredAtom2527 chi ∧
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
      ¬Fin15AnchoredAtom4364 chi ∧
      ¬Fin15AnchoredAtom4367 chi ∧
      ¬Fin15AnchoredAtom4368 chi ∧
      ¬Fin15AnchoredAtom4382 chi ∧
      ¬Fin15AnchoredAtom4383 chi ∧
      ¬Fin15AnchoredAtom4389 chi ∧
      ¬Fin15AnchoredAtom4403 chi ∧
      ¬Fin15AnchoredAtom4404 chi ∧
      ¬Fin15AnchoredAtom4410 chi ∧
      ¬Fin15AnchoredAtom4441 chi ∧
      ¬Fin15AnchoredAtom4459 chi ∧
      ¬Fin15AnchoredAtom4460 chi ∧
      ¬Fin15AnchoredAtom4466 chi ∧
      ¬Fin15AnchoredAtom4497 chi ∧
      ¬Fin15AnchoredAtom4532 chi ∧
      ¬Fin15AnchoredAtom4585 chi ∧
      ¬Fin15AnchoredAtom4586 chi ∧
      ¬Fin15AnchoredAtom4592 chi ∧
      ¬Fin15AnchoredAtom4623 chi ∧
      ¬Fin15AnchoredAtom4658 chi ∧
      ¬Fin15AnchoredAtom4728 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 5, 6, 7, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25841
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2492 Fin15AnchoredAtom2495 Fin15AnchoredAtom2498
    Fin15AnchoredAtom2499 Fin15AnchoredAtom2502 Fin15AnchoredAtom2505 Fin15AnchoredAtom2506
    Fin15AnchoredAtom2520 Fin15AnchoredAtom2521 Fin15AnchoredAtom2527 Fin15AnchoredAtom2530
    Fin15AnchoredAtom2533 Fin15AnchoredAtom2534 Fin15AnchoredAtom2548 Fin15AnchoredAtom2549
    Fin15AnchoredAtom2555 Fin15AnchoredAtom2569 Fin15AnchoredAtom2570 Fin15AnchoredAtom2576
    Fin15AnchoredAtom2607 Fin15AnchoredAtom2614 Fin15AnchoredAtom2617 Fin15AnchoredAtom2618
    Fin15AnchoredAtom2632 Fin15AnchoredAtom2633 Fin15AnchoredAtom2639 Fin15AnchoredAtom2653
    Fin15AnchoredAtom2654 Fin15AnchoredAtom2660 Fin15AnchoredAtom2691 Fin15AnchoredAtom2709
    Fin15AnchoredAtom2710 Fin15AnchoredAtom2716 Fin15AnchoredAtom2747 Fin15AnchoredAtom2782
    Fin15AnchoredAtom4364 Fin15AnchoredAtom4367 Fin15AnchoredAtom4368 Fin15AnchoredAtom4382
    Fin15AnchoredAtom4383 Fin15AnchoredAtom4389 Fin15AnchoredAtom4403 Fin15AnchoredAtom4404
    Fin15AnchoredAtom4410 Fin15AnchoredAtom4441 Fin15AnchoredAtom4459 Fin15AnchoredAtom4460
    Fin15AnchoredAtom4466 Fin15AnchoredAtom4497 Fin15AnchoredAtom4532 Fin15AnchoredAtom4585
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

theorem fin15Anchored_clause31538 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2492 chi ∧
      ¬Fin15AnchoredAtom2497 chi ∧
      ¬Fin15AnchoredAtom2498 chi ∧
      ¬Fin15AnchoredAtom2499 chi ∧
      ¬Fin15AnchoredAtom2504 chi ∧
      ¬Fin15AnchoredAtom2505 chi ∧
      ¬Fin15AnchoredAtom2506 chi ∧
      ¬Fin15AnchoredAtom2525 chi ∧
      ¬Fin15AnchoredAtom2526 chi ∧
      ¬Fin15AnchoredAtom2527 chi ∧
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
      ¬Fin15AnchoredAtom4366 chi ∧
      ¬Fin15AnchoredAtom4367 chi ∧
      ¬Fin15AnchoredAtom4368 chi ∧
      ¬Fin15AnchoredAtom4387 chi ∧
      ¬Fin15AnchoredAtom4388 chi ∧
      ¬Fin15AnchoredAtom4389 chi ∧
      ¬Fin15AnchoredAtom4408 chi ∧
      ¬Fin15AnchoredAtom4409 chi ∧
      ¬Fin15AnchoredAtom4410 chi ∧
      ¬Fin15AnchoredAtom4445 chi ∧
      ¬Fin15AnchoredAtom4464 chi ∧
      ¬Fin15AnchoredAtom4465 chi ∧
      ¬Fin15AnchoredAtom4466 chi ∧
      ¬Fin15AnchoredAtom4501 chi ∧
      ¬Fin15AnchoredAtom4536 chi ∧
      ¬Fin15AnchoredAtom4590 chi ∧
      ¬Fin15AnchoredAtom4591 chi ∧
      ¬Fin15AnchoredAtom4592 chi ∧
      ¬Fin15AnchoredAtom4627 chi ∧
      ¬Fin15AnchoredAtom4662 chi ∧
      ¬Fin15AnchoredAtom4732 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 5, 6, 7, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask28913
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2492 Fin15AnchoredAtom2497 Fin15AnchoredAtom2498
    Fin15AnchoredAtom2499 Fin15AnchoredAtom2504 Fin15AnchoredAtom2505 Fin15AnchoredAtom2506
    Fin15AnchoredAtom2525 Fin15AnchoredAtom2526 Fin15AnchoredAtom2527 Fin15AnchoredAtom2532
    Fin15AnchoredAtom2533 Fin15AnchoredAtom2534 Fin15AnchoredAtom2553 Fin15AnchoredAtom2554
    Fin15AnchoredAtom2555 Fin15AnchoredAtom2574 Fin15AnchoredAtom2575 Fin15AnchoredAtom2576
    Fin15AnchoredAtom2611 Fin15AnchoredAtom2616 Fin15AnchoredAtom2617 Fin15AnchoredAtom2618
    Fin15AnchoredAtom2637 Fin15AnchoredAtom2638 Fin15AnchoredAtom2639 Fin15AnchoredAtom2658
    Fin15AnchoredAtom2659 Fin15AnchoredAtom2660 Fin15AnchoredAtom2695 Fin15AnchoredAtom2714
    Fin15AnchoredAtom2715 Fin15AnchoredAtom2716 Fin15AnchoredAtom2751 Fin15AnchoredAtom2786
    Fin15AnchoredAtom4366 Fin15AnchoredAtom4367 Fin15AnchoredAtom4368 Fin15AnchoredAtom4387
    Fin15AnchoredAtom4388 Fin15AnchoredAtom4389 Fin15AnchoredAtom4408 Fin15AnchoredAtom4409
    Fin15AnchoredAtom4410 Fin15AnchoredAtom4445 Fin15AnchoredAtom4464 Fin15AnchoredAtom4465
    Fin15AnchoredAtom4466 Fin15AnchoredAtom4501 Fin15AnchoredAtom4536 Fin15AnchoredAtom4590
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

theorem fin15Anchored_clause31539 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2493 chi ∧
      ¬Fin15AnchoredAtom2494 chi ∧
      ¬Fin15AnchoredAtom2495 chi ∧
      ¬Fin15AnchoredAtom2497 chi ∧
      ¬Fin15AnchoredAtom2507 chi ∧
      ¬Fin15AnchoredAtom2508 chi ∧
      ¬Fin15AnchoredAtom2510 chi ∧
      ¬Fin15AnchoredAtom2513 chi ∧
      ¬Fin15AnchoredAtom2515 chi ∧
      ¬Fin15AnchoredAtom2519 chi ∧
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
      ¬Fin15AnchoredAtom4369 chi ∧
      ¬Fin15AnchoredAtom4370 chi ∧
      ¬Fin15AnchoredAtom4372 chi ∧
      ¬Fin15AnchoredAtom4375 chi ∧
      ¬Fin15AnchoredAtom4377 chi ∧
      ¬Fin15AnchoredAtom4381 chi ∧
      ¬Fin15AnchoredAtom4411 chi ∧
      ¬Fin15AnchoredAtom4413 chi ∧
      ¬Fin15AnchoredAtom4417 chi ∧
      ¬Fin15AnchoredAtom4427 chi ∧
      ¬Fin15AnchoredAtom4467 chi ∧
      ¬Fin15AnchoredAtom4469 chi ∧
      ¬Fin15AnchoredAtom4473 chi ∧
      ¬Fin15AnchoredAtom4483 chi ∧
      ¬Fin15AnchoredAtom4538 chi ∧
      ¬Fin15AnchoredAtom4593 chi ∧
      ¬Fin15AnchoredAtom4595 chi ∧
      ¬Fin15AnchoredAtom4599 chi ∧
      ¬Fin15AnchoredAtom4609 chi ∧
      ¬Fin15AnchoredAtom4664 chi ∧
      ¬Fin15AnchoredAtom4734 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 5, 6, 8, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask06001
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2493 Fin15AnchoredAtom2494 Fin15AnchoredAtom2495
    Fin15AnchoredAtom2497 Fin15AnchoredAtom2507 Fin15AnchoredAtom2508 Fin15AnchoredAtom2510
    Fin15AnchoredAtom2513 Fin15AnchoredAtom2515 Fin15AnchoredAtom2519 Fin15AnchoredAtom2535
    Fin15AnchoredAtom2536 Fin15AnchoredAtom2538 Fin15AnchoredAtom2541 Fin15AnchoredAtom2543
    Fin15AnchoredAtom2547 Fin15AnchoredAtom2577 Fin15AnchoredAtom2579 Fin15AnchoredAtom2583
    Fin15AnchoredAtom2593 Fin15AnchoredAtom2619 Fin15AnchoredAtom2620 Fin15AnchoredAtom2622
    Fin15AnchoredAtom2625 Fin15AnchoredAtom2627 Fin15AnchoredAtom2631 Fin15AnchoredAtom2661
    Fin15AnchoredAtom2663 Fin15AnchoredAtom2667 Fin15AnchoredAtom2677 Fin15AnchoredAtom2717
    Fin15AnchoredAtom2719 Fin15AnchoredAtom2723 Fin15AnchoredAtom2733 Fin15AnchoredAtom2788
    Fin15AnchoredAtom4369 Fin15AnchoredAtom4370 Fin15AnchoredAtom4372 Fin15AnchoredAtom4375
    Fin15AnchoredAtom4377 Fin15AnchoredAtom4381 Fin15AnchoredAtom4411 Fin15AnchoredAtom4413
    Fin15AnchoredAtom4417 Fin15AnchoredAtom4427 Fin15AnchoredAtom4467 Fin15AnchoredAtom4469
    Fin15AnchoredAtom4473 Fin15AnchoredAtom4483 Fin15AnchoredAtom4538 Fin15AnchoredAtom4593
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

theorem fin15Anchored_clause31540 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2493 chi ∧
      ¬Fin15AnchoredAtom2494 chi ∧
      ¬Fin15AnchoredAtom2495 chi ∧
      ¬Fin15AnchoredAtom2498 chi ∧
      ¬Fin15AnchoredAtom2507 chi ∧
      ¬Fin15AnchoredAtom2508 chi ∧
      ¬Fin15AnchoredAtom2511 chi ∧
      ¬Fin15AnchoredAtom2513 chi ∧
      ¬Fin15AnchoredAtom2516 chi ∧
      ¬Fin15AnchoredAtom2520 chi ∧
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
      ¬Fin15AnchoredAtom2619 chi ∧
      ¬Fin15AnchoredAtom2620 chi ∧
      ¬Fin15AnchoredAtom2623 chi ∧
      ¬Fin15AnchoredAtom2625 chi ∧
      ¬Fin15AnchoredAtom2628 chi ∧
      ¬Fin15AnchoredAtom2632 chi ∧
      ¬Fin15AnchoredAtom2661 chi ∧
      ¬Fin15AnchoredAtom2664 chi ∧
      ¬Fin15AnchoredAtom2668 chi ∧
      ¬Fin15AnchoredAtom2678 chi ∧
      ¬Fin15AnchoredAtom2717 chi ∧
      ¬Fin15AnchoredAtom2720 chi ∧
      ¬Fin15AnchoredAtom2724 chi ∧
      ¬Fin15AnchoredAtom2734 chi ∧
      ¬Fin15AnchoredAtom2789 chi ∧
      ¬Fin15AnchoredAtom4369 chi ∧
      ¬Fin15AnchoredAtom4370 chi ∧
      ¬Fin15AnchoredAtom4373 chi ∧
      ¬Fin15AnchoredAtom4375 chi ∧
      ¬Fin15AnchoredAtom4378 chi ∧
      ¬Fin15AnchoredAtom4382 chi ∧
      ¬Fin15AnchoredAtom4411 chi ∧
      ¬Fin15AnchoredAtom4414 chi ∧
      ¬Fin15AnchoredAtom4418 chi ∧
      ¬Fin15AnchoredAtom4428 chi ∧
      ¬Fin15AnchoredAtom4467 chi ∧
      ¬Fin15AnchoredAtom4470 chi ∧
      ¬Fin15AnchoredAtom4474 chi ∧
      ¬Fin15AnchoredAtom4484 chi ∧
      ¬Fin15AnchoredAtom4539 chi ∧
      ¬Fin15AnchoredAtom4593 chi ∧
      ¬Fin15AnchoredAtom4596 chi ∧
      ¬Fin15AnchoredAtom4600 chi ∧
      ¬Fin15AnchoredAtom4610 chi ∧
      ¬Fin15AnchoredAtom4665 chi ∧
      ¬Fin15AnchoredAtom4735 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 5, 6, 8, 9, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask10097
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2493 Fin15AnchoredAtom2494 Fin15AnchoredAtom2495
    Fin15AnchoredAtom2498 Fin15AnchoredAtom2507 Fin15AnchoredAtom2508 Fin15AnchoredAtom2511
    Fin15AnchoredAtom2513 Fin15AnchoredAtom2516 Fin15AnchoredAtom2520 Fin15AnchoredAtom2535
    Fin15AnchoredAtom2536 Fin15AnchoredAtom2539 Fin15AnchoredAtom2541 Fin15AnchoredAtom2544
    Fin15AnchoredAtom2548 Fin15AnchoredAtom2577 Fin15AnchoredAtom2580 Fin15AnchoredAtom2584
    Fin15AnchoredAtom2594 Fin15AnchoredAtom2619 Fin15AnchoredAtom2620 Fin15AnchoredAtom2623
    Fin15AnchoredAtom2625 Fin15AnchoredAtom2628 Fin15AnchoredAtom2632 Fin15AnchoredAtom2661
    Fin15AnchoredAtom2664 Fin15AnchoredAtom2668 Fin15AnchoredAtom2678 Fin15AnchoredAtom2717
    Fin15AnchoredAtom2720 Fin15AnchoredAtom2724 Fin15AnchoredAtom2734 Fin15AnchoredAtom2789
    Fin15AnchoredAtom4369 Fin15AnchoredAtom4370 Fin15AnchoredAtom4373 Fin15AnchoredAtom4375
    Fin15AnchoredAtom4378 Fin15AnchoredAtom4382 Fin15AnchoredAtom4411 Fin15AnchoredAtom4414
    Fin15AnchoredAtom4418 Fin15AnchoredAtom4428 Fin15AnchoredAtom4467 Fin15AnchoredAtom4470
    Fin15AnchoredAtom4474 Fin15AnchoredAtom4484 Fin15AnchoredAtom4539 Fin15AnchoredAtom4593
    Fin15AnchoredAtom4596 Fin15AnchoredAtom4600 Fin15AnchoredAtom4610 Fin15AnchoredAtom4665
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

theorem fin15Anchored_clause31541 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2493 chi ∧
      ¬Fin15AnchoredAtom2494 chi ∧
      ¬Fin15AnchoredAtom2495 chi ∧
      ¬Fin15AnchoredAtom2499 chi ∧
      ¬Fin15AnchoredAtom2507 chi ∧
      ¬Fin15AnchoredAtom2508 chi ∧
      ¬Fin15AnchoredAtom2512 chi ∧
      ¬Fin15AnchoredAtom2513 chi ∧
      ¬Fin15AnchoredAtom2517 chi ∧
      ¬Fin15AnchoredAtom2521 chi ∧
      ¬Fin15AnchoredAtom2535 chi ∧
      ¬Fin15AnchoredAtom2536 chi ∧
      ¬Fin15AnchoredAtom2540 chi ∧
      ¬Fin15AnchoredAtom2541 chi ∧
      ¬Fin15AnchoredAtom2545 chi ∧
      ¬Fin15AnchoredAtom2549 chi ∧
      ¬Fin15AnchoredAtom2577 chi ∧
      ¬Fin15AnchoredAtom2581 chi ∧
      ¬Fin15AnchoredAtom2585 chi ∧
      ¬Fin15AnchoredAtom2595 chi ∧
      ¬Fin15AnchoredAtom2619 chi ∧
      ¬Fin15AnchoredAtom2620 chi ∧
      ¬Fin15AnchoredAtom2624 chi ∧
      ¬Fin15AnchoredAtom2625 chi ∧
      ¬Fin15AnchoredAtom2629 chi ∧
      ¬Fin15AnchoredAtom2633 chi ∧
      ¬Fin15AnchoredAtom2661 chi ∧
      ¬Fin15AnchoredAtom2665 chi ∧
      ¬Fin15AnchoredAtom2669 chi ∧
      ¬Fin15AnchoredAtom2679 chi ∧
      ¬Fin15AnchoredAtom2717 chi ∧
      ¬Fin15AnchoredAtom2721 chi ∧
      ¬Fin15AnchoredAtom2725 chi ∧
      ¬Fin15AnchoredAtom2735 chi ∧
      ¬Fin15AnchoredAtom2790 chi ∧
      ¬Fin15AnchoredAtom4369 chi ∧
      ¬Fin15AnchoredAtom4370 chi ∧
      ¬Fin15AnchoredAtom4374 chi ∧
      ¬Fin15AnchoredAtom4375 chi ∧
      ¬Fin15AnchoredAtom4379 chi ∧
      ¬Fin15AnchoredAtom4383 chi ∧
      ¬Fin15AnchoredAtom4411 chi ∧
      ¬Fin15AnchoredAtom4415 chi ∧
      ¬Fin15AnchoredAtom4419 chi ∧
      ¬Fin15AnchoredAtom4429 chi ∧
      ¬Fin15AnchoredAtom4467 chi ∧
      ¬Fin15AnchoredAtom4471 chi ∧
      ¬Fin15AnchoredAtom4475 chi ∧
      ¬Fin15AnchoredAtom4485 chi ∧
      ¬Fin15AnchoredAtom4540 chi ∧
      ¬Fin15AnchoredAtom4593 chi ∧
      ¬Fin15AnchoredAtom4597 chi ∧
      ¬Fin15AnchoredAtom4601 chi ∧
      ¬Fin15AnchoredAtom4611 chi ∧
      ¬Fin15AnchoredAtom4666 chi ∧
      ¬Fin15AnchoredAtom4736 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 5, 6, 8, 9, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask18289
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2493 Fin15AnchoredAtom2494 Fin15AnchoredAtom2495
    Fin15AnchoredAtom2499 Fin15AnchoredAtom2507 Fin15AnchoredAtom2508 Fin15AnchoredAtom2512
    Fin15AnchoredAtom2513 Fin15AnchoredAtom2517 Fin15AnchoredAtom2521 Fin15AnchoredAtom2535
    Fin15AnchoredAtom2536 Fin15AnchoredAtom2540 Fin15AnchoredAtom2541 Fin15AnchoredAtom2545
    Fin15AnchoredAtom2549 Fin15AnchoredAtom2577 Fin15AnchoredAtom2581 Fin15AnchoredAtom2585
    Fin15AnchoredAtom2595 Fin15AnchoredAtom2619 Fin15AnchoredAtom2620 Fin15AnchoredAtom2624
    Fin15AnchoredAtom2625 Fin15AnchoredAtom2629 Fin15AnchoredAtom2633 Fin15AnchoredAtom2661
    Fin15AnchoredAtom2665 Fin15AnchoredAtom2669 Fin15AnchoredAtom2679 Fin15AnchoredAtom2717
    Fin15AnchoredAtom2721 Fin15AnchoredAtom2725 Fin15AnchoredAtom2735 Fin15AnchoredAtom2790
    Fin15AnchoredAtom4369 Fin15AnchoredAtom4370 Fin15AnchoredAtom4374 Fin15AnchoredAtom4375
    Fin15AnchoredAtom4379 Fin15AnchoredAtom4383 Fin15AnchoredAtom4411 Fin15AnchoredAtom4415
    Fin15AnchoredAtom4419 Fin15AnchoredAtom4429 Fin15AnchoredAtom4467 Fin15AnchoredAtom4471
    Fin15AnchoredAtom4475 Fin15AnchoredAtom4485 Fin15AnchoredAtom4540 Fin15AnchoredAtom4593
    Fin15AnchoredAtom4597 Fin15AnchoredAtom4601 Fin15AnchoredAtom4611 Fin15AnchoredAtom4666
    Fin15AnchoredAtom4736 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31542 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2493 chi ∧
      ¬Fin15AnchoredAtom2494 chi ∧
      ¬Fin15AnchoredAtom2497 chi ∧
      ¬Fin15AnchoredAtom2498 chi ∧
      ¬Fin15AnchoredAtom2507 chi ∧
      ¬Fin15AnchoredAtom2510 chi ∧
      ¬Fin15AnchoredAtom2511 chi ∧
      ¬Fin15AnchoredAtom2515 chi ∧
      ¬Fin15AnchoredAtom2516 chi ∧
      ¬Fin15AnchoredAtom2525 chi ∧
      ¬Fin15AnchoredAtom2535 chi ∧
      ¬Fin15AnchoredAtom2538 chi ∧
      ¬Fin15AnchoredAtom2539 chi ∧
      ¬Fin15AnchoredAtom2543 chi ∧
      ¬Fin15AnchoredAtom2544 chi ∧
      ¬Fin15AnchoredAtom2553 chi ∧
      ¬Fin15AnchoredAtom2579 chi ∧
      ¬Fin15AnchoredAtom2580 chi ∧
      ¬Fin15AnchoredAtom2589 chi ∧
      ¬Fin15AnchoredAtom2599 chi ∧
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
      ¬Fin15AnchoredAtom4369 chi ∧
      ¬Fin15AnchoredAtom4372 chi ∧
      ¬Fin15AnchoredAtom4373 chi ∧
      ¬Fin15AnchoredAtom4377 chi ∧
      ¬Fin15AnchoredAtom4378 chi ∧
      ¬Fin15AnchoredAtom4387 chi ∧
      ¬Fin15AnchoredAtom4413 chi ∧
      ¬Fin15AnchoredAtom4414 chi ∧
      ¬Fin15AnchoredAtom4423 chi ∧
      ¬Fin15AnchoredAtom4433 chi ∧
      ¬Fin15AnchoredAtom4469 chi ∧
      ¬Fin15AnchoredAtom4470 chi ∧
      ¬Fin15AnchoredAtom4479 chi ∧
      ¬Fin15AnchoredAtom4489 chi ∧
      ¬Fin15AnchoredAtom4544 chi ∧
      ¬Fin15AnchoredAtom4595 chi ∧
      ¬Fin15AnchoredAtom4596 chi ∧
      ¬Fin15AnchoredAtom4605 chi ∧
      ¬Fin15AnchoredAtom4615 chi ∧
      ¬Fin15AnchoredAtom4670 chi ∧
      ¬Fin15AnchoredAtom4740 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 5, 6, 8, 9, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13169
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2493 Fin15AnchoredAtom2494 Fin15AnchoredAtom2497
    Fin15AnchoredAtom2498 Fin15AnchoredAtom2507 Fin15AnchoredAtom2510 Fin15AnchoredAtom2511
    Fin15AnchoredAtom2515 Fin15AnchoredAtom2516 Fin15AnchoredAtom2525 Fin15AnchoredAtom2535
    Fin15AnchoredAtom2538 Fin15AnchoredAtom2539 Fin15AnchoredAtom2543 Fin15AnchoredAtom2544
    Fin15AnchoredAtom2553 Fin15AnchoredAtom2579 Fin15AnchoredAtom2580 Fin15AnchoredAtom2589
    Fin15AnchoredAtom2599 Fin15AnchoredAtom2619 Fin15AnchoredAtom2622 Fin15AnchoredAtom2623
    Fin15AnchoredAtom2627 Fin15AnchoredAtom2628 Fin15AnchoredAtom2637 Fin15AnchoredAtom2663
    Fin15AnchoredAtom2664 Fin15AnchoredAtom2673 Fin15AnchoredAtom2683 Fin15AnchoredAtom2719
    Fin15AnchoredAtom2720 Fin15AnchoredAtom2729 Fin15AnchoredAtom2739 Fin15AnchoredAtom2794
    Fin15AnchoredAtom4369 Fin15AnchoredAtom4372 Fin15AnchoredAtom4373 Fin15AnchoredAtom4377
    Fin15AnchoredAtom4378 Fin15AnchoredAtom4387 Fin15AnchoredAtom4413 Fin15AnchoredAtom4414
    Fin15AnchoredAtom4423 Fin15AnchoredAtom4433 Fin15AnchoredAtom4469 Fin15AnchoredAtom4470
    Fin15AnchoredAtom4479 Fin15AnchoredAtom4489 Fin15AnchoredAtom4544 Fin15AnchoredAtom4595
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

theorem fin15Anchored_clause31543 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2493 chi ∧
      ¬Fin15AnchoredAtom2494 chi ∧
      ¬Fin15AnchoredAtom2498 chi ∧
      ¬Fin15AnchoredAtom2499 chi ∧
      ¬Fin15AnchoredAtom2507 chi ∧
      ¬Fin15AnchoredAtom2511 chi ∧
      ¬Fin15AnchoredAtom2512 chi ∧
      ¬Fin15AnchoredAtom2516 chi ∧
      ¬Fin15AnchoredAtom2517 chi ∧
      ¬Fin15AnchoredAtom2527 chi ∧
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
      ¬Fin15AnchoredAtom2619 chi ∧
      ¬Fin15AnchoredAtom2623 chi ∧
      ¬Fin15AnchoredAtom2624 chi ∧
      ¬Fin15AnchoredAtom2628 chi ∧
      ¬Fin15AnchoredAtom2629 chi ∧
      ¬Fin15AnchoredAtom2639 chi ∧
      ¬Fin15AnchoredAtom2664 chi ∧
      ¬Fin15AnchoredAtom2665 chi ∧
      ¬Fin15AnchoredAtom2675 chi ∧
      ¬Fin15AnchoredAtom2685 chi ∧
      ¬Fin15AnchoredAtom2720 chi ∧
      ¬Fin15AnchoredAtom2721 chi ∧
      ¬Fin15AnchoredAtom2731 chi ∧
      ¬Fin15AnchoredAtom2741 chi ∧
      ¬Fin15AnchoredAtom2796 chi ∧
      ¬Fin15AnchoredAtom4369 chi ∧
      ¬Fin15AnchoredAtom4373 chi ∧
      ¬Fin15AnchoredAtom4374 chi ∧
      ¬Fin15AnchoredAtom4378 chi ∧
      ¬Fin15AnchoredAtom4379 chi ∧
      ¬Fin15AnchoredAtom4389 chi ∧
      ¬Fin15AnchoredAtom4414 chi ∧
      ¬Fin15AnchoredAtom4415 chi ∧
      ¬Fin15AnchoredAtom4425 chi ∧
      ¬Fin15AnchoredAtom4435 chi ∧
      ¬Fin15AnchoredAtom4470 chi ∧
      ¬Fin15AnchoredAtom4471 chi ∧
      ¬Fin15AnchoredAtom4481 chi ∧
      ¬Fin15AnchoredAtom4491 chi ∧
      ¬Fin15AnchoredAtom4546 chi ∧
      ¬Fin15AnchoredAtom4596 chi ∧
      ¬Fin15AnchoredAtom4597 chi ∧
      ¬Fin15AnchoredAtom4607 chi ∧
      ¬Fin15AnchoredAtom4617 chi ∧
      ¬Fin15AnchoredAtom4672 chi ∧
      ¬Fin15AnchoredAtom4742 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 5, 6, 8, 9, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25457
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2493 Fin15AnchoredAtom2494 Fin15AnchoredAtom2498
    Fin15AnchoredAtom2499 Fin15AnchoredAtom2507 Fin15AnchoredAtom2511 Fin15AnchoredAtom2512
    Fin15AnchoredAtom2516 Fin15AnchoredAtom2517 Fin15AnchoredAtom2527 Fin15AnchoredAtom2535
    Fin15AnchoredAtom2539 Fin15AnchoredAtom2540 Fin15AnchoredAtom2544 Fin15AnchoredAtom2545
    Fin15AnchoredAtom2555 Fin15AnchoredAtom2580 Fin15AnchoredAtom2581 Fin15AnchoredAtom2591
    Fin15AnchoredAtom2601 Fin15AnchoredAtom2619 Fin15AnchoredAtom2623 Fin15AnchoredAtom2624
    Fin15AnchoredAtom2628 Fin15AnchoredAtom2629 Fin15AnchoredAtom2639 Fin15AnchoredAtom2664
    Fin15AnchoredAtom2665 Fin15AnchoredAtom2675 Fin15AnchoredAtom2685 Fin15AnchoredAtom2720
    Fin15AnchoredAtom2721 Fin15AnchoredAtom2731 Fin15AnchoredAtom2741 Fin15AnchoredAtom2796
    Fin15AnchoredAtom4369 Fin15AnchoredAtom4373 Fin15AnchoredAtom4374 Fin15AnchoredAtom4378
    Fin15AnchoredAtom4379 Fin15AnchoredAtom4389 Fin15AnchoredAtom4414 Fin15AnchoredAtom4415
    Fin15AnchoredAtom4425 Fin15AnchoredAtom4435 Fin15AnchoredAtom4470 Fin15AnchoredAtom4471
    Fin15AnchoredAtom4481 Fin15AnchoredAtom4491 Fin15AnchoredAtom4546 Fin15AnchoredAtom4596
    Fin15AnchoredAtom4597 Fin15AnchoredAtom4607 Fin15AnchoredAtom4617 Fin15AnchoredAtom4672
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

theorem fin15Anchored_clause31544 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2493 chi ∧
      ¬Fin15AnchoredAtom2495 chi ∧
      ¬Fin15AnchoredAtom2497 chi ∧
      ¬Fin15AnchoredAtom2498 chi ∧
      ¬Fin15AnchoredAtom2508 chi ∧
      ¬Fin15AnchoredAtom2510 chi ∧
      ¬Fin15AnchoredAtom2511 chi ∧
      ¬Fin15AnchoredAtom2519 chi ∧
      ¬Fin15AnchoredAtom2520 chi ∧
      ¬Fin15AnchoredAtom2525 chi ∧
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
      ¬Fin15AnchoredAtom2620 chi ∧
      ¬Fin15AnchoredAtom2622 chi ∧
      ¬Fin15AnchoredAtom2623 chi ∧
      ¬Fin15AnchoredAtom2631 chi ∧
      ¬Fin15AnchoredAtom2632 chi ∧
      ¬Fin15AnchoredAtom2637 chi ∧
      ¬Fin15AnchoredAtom2667 chi ∧
      ¬Fin15AnchoredAtom2668 chi ∧
      ¬Fin15AnchoredAtom2673 chi ∧
      ¬Fin15AnchoredAtom2689 chi ∧
      ¬Fin15AnchoredAtom2723 chi ∧
      ¬Fin15AnchoredAtom2724 chi ∧
      ¬Fin15AnchoredAtom2729 chi ∧
      ¬Fin15AnchoredAtom2745 chi ∧
      ¬Fin15AnchoredAtom2800 chi ∧
      ¬Fin15AnchoredAtom4370 chi ∧
      ¬Fin15AnchoredAtom4372 chi ∧
      ¬Fin15AnchoredAtom4373 chi ∧
      ¬Fin15AnchoredAtom4381 chi ∧
      ¬Fin15AnchoredAtom4382 chi ∧
      ¬Fin15AnchoredAtom4387 chi ∧
      ¬Fin15AnchoredAtom4417 chi ∧
      ¬Fin15AnchoredAtom4418 chi ∧
      ¬Fin15AnchoredAtom4423 chi ∧
      ¬Fin15AnchoredAtom4439 chi ∧
      ¬Fin15AnchoredAtom4473 chi ∧
      ¬Fin15AnchoredAtom4474 chi ∧
      ¬Fin15AnchoredAtom4479 chi ∧
      ¬Fin15AnchoredAtom4495 chi ∧
      ¬Fin15AnchoredAtom4550 chi ∧
      ¬Fin15AnchoredAtom4599 chi ∧
      ¬Fin15AnchoredAtom4600 chi ∧
      ¬Fin15AnchoredAtom4605 chi ∧
      ¬Fin15AnchoredAtom4621 chi ∧
      ¬Fin15AnchoredAtom4676 chi ∧
      ¬Fin15AnchoredAtom4746 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 5, 6, 8, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13681
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2493 Fin15AnchoredAtom2495 Fin15AnchoredAtom2497
    Fin15AnchoredAtom2498 Fin15AnchoredAtom2508 Fin15AnchoredAtom2510 Fin15AnchoredAtom2511
    Fin15AnchoredAtom2519 Fin15AnchoredAtom2520 Fin15AnchoredAtom2525 Fin15AnchoredAtom2536
    Fin15AnchoredAtom2538 Fin15AnchoredAtom2539 Fin15AnchoredAtom2547 Fin15AnchoredAtom2548
    Fin15AnchoredAtom2553 Fin15AnchoredAtom2583 Fin15AnchoredAtom2584 Fin15AnchoredAtom2589
    Fin15AnchoredAtom2605 Fin15AnchoredAtom2620 Fin15AnchoredAtom2622 Fin15AnchoredAtom2623
    Fin15AnchoredAtom2631 Fin15AnchoredAtom2632 Fin15AnchoredAtom2637 Fin15AnchoredAtom2667
    Fin15AnchoredAtom2668 Fin15AnchoredAtom2673 Fin15AnchoredAtom2689 Fin15AnchoredAtom2723
    Fin15AnchoredAtom2724 Fin15AnchoredAtom2729 Fin15AnchoredAtom2745 Fin15AnchoredAtom2800
    Fin15AnchoredAtom4370 Fin15AnchoredAtom4372 Fin15AnchoredAtom4373 Fin15AnchoredAtom4381
    Fin15AnchoredAtom4382 Fin15AnchoredAtom4387 Fin15AnchoredAtom4417 Fin15AnchoredAtom4418
    Fin15AnchoredAtom4423 Fin15AnchoredAtom4439 Fin15AnchoredAtom4473 Fin15AnchoredAtom4474
    Fin15AnchoredAtom4479 Fin15AnchoredAtom4495 Fin15AnchoredAtom4550 Fin15AnchoredAtom4599
    Fin15AnchoredAtom4600 Fin15AnchoredAtom4605 Fin15AnchoredAtom4621 Fin15AnchoredAtom4676
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

theorem fin15Anchored_clause31545 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2493 chi ∧
      ¬Fin15AnchoredAtom2495 chi ∧
      ¬Fin15AnchoredAtom2497 chi ∧
      ¬Fin15AnchoredAtom2499 chi ∧
      ¬Fin15AnchoredAtom2508 chi ∧
      ¬Fin15AnchoredAtom2510 chi ∧
      ¬Fin15AnchoredAtom2512 chi ∧
      ¬Fin15AnchoredAtom2519 chi ∧
      ¬Fin15AnchoredAtom2521 chi ∧
      ¬Fin15AnchoredAtom2526 chi ∧
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
      ¬Fin15AnchoredAtom2620 chi ∧
      ¬Fin15AnchoredAtom2622 chi ∧
      ¬Fin15AnchoredAtom2624 chi ∧
      ¬Fin15AnchoredAtom2631 chi ∧
      ¬Fin15AnchoredAtom2633 chi ∧
      ¬Fin15AnchoredAtom2638 chi ∧
      ¬Fin15AnchoredAtom2667 chi ∧
      ¬Fin15AnchoredAtom2669 chi ∧
      ¬Fin15AnchoredAtom2674 chi ∧
      ¬Fin15AnchoredAtom2690 chi ∧
      ¬Fin15AnchoredAtom2723 chi ∧
      ¬Fin15AnchoredAtom2725 chi ∧
      ¬Fin15AnchoredAtom2730 chi ∧
      ¬Fin15AnchoredAtom2746 chi ∧
      ¬Fin15AnchoredAtom2801 chi ∧
      ¬Fin15AnchoredAtom4370 chi ∧
      ¬Fin15AnchoredAtom4372 chi ∧
      ¬Fin15AnchoredAtom4374 chi ∧
      ¬Fin15AnchoredAtom4381 chi ∧
      ¬Fin15AnchoredAtom4383 chi ∧
      ¬Fin15AnchoredAtom4388 chi ∧
      ¬Fin15AnchoredAtom4417 chi ∧
      ¬Fin15AnchoredAtom4419 chi ∧
      ¬Fin15AnchoredAtom4424 chi ∧
      ¬Fin15AnchoredAtom4440 chi ∧
      ¬Fin15AnchoredAtom4473 chi ∧
      ¬Fin15AnchoredAtom4475 chi ∧
      ¬Fin15AnchoredAtom4480 chi ∧
      ¬Fin15AnchoredAtom4496 chi ∧
      ¬Fin15AnchoredAtom4551 chi ∧
      ¬Fin15AnchoredAtom4599 chi ∧
      ¬Fin15AnchoredAtom4601 chi ∧
      ¬Fin15AnchoredAtom4606 chi ∧
      ¬Fin15AnchoredAtom4622 chi ∧
      ¬Fin15AnchoredAtom4677 chi ∧
      ¬Fin15AnchoredAtom4747 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 5, 6, 8, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21873
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2493 Fin15AnchoredAtom2495 Fin15AnchoredAtom2497
    Fin15AnchoredAtom2499 Fin15AnchoredAtom2508 Fin15AnchoredAtom2510 Fin15AnchoredAtom2512
    Fin15AnchoredAtom2519 Fin15AnchoredAtom2521 Fin15AnchoredAtom2526 Fin15AnchoredAtom2536
    Fin15AnchoredAtom2538 Fin15AnchoredAtom2540 Fin15AnchoredAtom2547 Fin15AnchoredAtom2549
    Fin15AnchoredAtom2554 Fin15AnchoredAtom2583 Fin15AnchoredAtom2585 Fin15AnchoredAtom2590
    Fin15AnchoredAtom2606 Fin15AnchoredAtom2620 Fin15AnchoredAtom2622 Fin15AnchoredAtom2624
    Fin15AnchoredAtom2631 Fin15AnchoredAtom2633 Fin15AnchoredAtom2638 Fin15AnchoredAtom2667
    Fin15AnchoredAtom2669 Fin15AnchoredAtom2674 Fin15AnchoredAtom2690 Fin15AnchoredAtom2723
    Fin15AnchoredAtom2725 Fin15AnchoredAtom2730 Fin15AnchoredAtom2746 Fin15AnchoredAtom2801
    Fin15AnchoredAtom4370 Fin15AnchoredAtom4372 Fin15AnchoredAtom4374 Fin15AnchoredAtom4381
    Fin15AnchoredAtom4383 Fin15AnchoredAtom4388 Fin15AnchoredAtom4417 Fin15AnchoredAtom4419
    Fin15AnchoredAtom4424 Fin15AnchoredAtom4440 Fin15AnchoredAtom4473 Fin15AnchoredAtom4475
    Fin15AnchoredAtom4480 Fin15AnchoredAtom4496 Fin15AnchoredAtom4551 Fin15AnchoredAtom4599
    Fin15AnchoredAtom4601 Fin15AnchoredAtom4606 Fin15AnchoredAtom4622 Fin15AnchoredAtom4677
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

theorem fin15Anchored_clause31546 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2493 chi ∧
      ¬Fin15AnchoredAtom2495 chi ∧
      ¬Fin15AnchoredAtom2498 chi ∧
      ¬Fin15AnchoredAtom2499 chi ∧
      ¬Fin15AnchoredAtom2508 chi ∧
      ¬Fin15AnchoredAtom2511 chi ∧
      ¬Fin15AnchoredAtom2512 chi ∧
      ¬Fin15AnchoredAtom2520 chi ∧
      ¬Fin15AnchoredAtom2521 chi ∧
      ¬Fin15AnchoredAtom2527 chi ∧
      ¬Fin15AnchoredAtom2536 chi ∧
      ¬Fin15AnchoredAtom2539 chi ∧
      ¬Fin15AnchoredAtom2540 chi ∧
      ¬Fin15AnchoredAtom2548 chi ∧
      ¬Fin15AnchoredAtom2549 chi ∧
      ¬Fin15AnchoredAtom2555 chi ∧
      ¬Fin15AnchoredAtom2584 chi ∧
      ¬Fin15AnchoredAtom2585 chi ∧
      ¬Fin15AnchoredAtom2591 chi ∧
      ¬Fin15AnchoredAtom2607 chi ∧
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
      ¬Fin15AnchoredAtom4370 chi ∧
      ¬Fin15AnchoredAtom4373 chi ∧
      ¬Fin15AnchoredAtom4374 chi ∧
      ¬Fin15AnchoredAtom4382 chi ∧
      ¬Fin15AnchoredAtom4383 chi ∧
      ¬Fin15AnchoredAtom4389 chi ∧
      ¬Fin15AnchoredAtom4418 chi ∧
      ¬Fin15AnchoredAtom4419 chi ∧
      ¬Fin15AnchoredAtom4425 chi ∧
      ¬Fin15AnchoredAtom4441 chi ∧
      ¬Fin15AnchoredAtom4474 chi ∧
      ¬Fin15AnchoredAtom4475 chi ∧
      ¬Fin15AnchoredAtom4481 chi ∧
      ¬Fin15AnchoredAtom4497 chi ∧
      ¬Fin15AnchoredAtom4552 chi ∧
      ¬Fin15AnchoredAtom4600 chi ∧
      ¬Fin15AnchoredAtom4601 chi ∧
      ¬Fin15AnchoredAtom4607 chi ∧
      ¬Fin15AnchoredAtom4623 chi ∧
      ¬Fin15AnchoredAtom4678 chi ∧
      ¬Fin15AnchoredAtom4748 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 5, 6, 8, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25969
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2493 Fin15AnchoredAtom2495 Fin15AnchoredAtom2498
    Fin15AnchoredAtom2499 Fin15AnchoredAtom2508 Fin15AnchoredAtom2511 Fin15AnchoredAtom2512
    Fin15AnchoredAtom2520 Fin15AnchoredAtom2521 Fin15AnchoredAtom2527 Fin15AnchoredAtom2536
    Fin15AnchoredAtom2539 Fin15AnchoredAtom2540 Fin15AnchoredAtom2548 Fin15AnchoredAtom2549
    Fin15AnchoredAtom2555 Fin15AnchoredAtom2584 Fin15AnchoredAtom2585 Fin15AnchoredAtom2591
    Fin15AnchoredAtom2607 Fin15AnchoredAtom2620 Fin15AnchoredAtom2623 Fin15AnchoredAtom2624
    Fin15AnchoredAtom2632 Fin15AnchoredAtom2633 Fin15AnchoredAtom2639 Fin15AnchoredAtom2668
    Fin15AnchoredAtom2669 Fin15AnchoredAtom2675 Fin15AnchoredAtom2691 Fin15AnchoredAtom2724
    Fin15AnchoredAtom2725 Fin15AnchoredAtom2731 Fin15AnchoredAtom2747 Fin15AnchoredAtom2802
    Fin15AnchoredAtom4370 Fin15AnchoredAtom4373 Fin15AnchoredAtom4374 Fin15AnchoredAtom4382
    Fin15AnchoredAtom4383 Fin15AnchoredAtom4389 Fin15AnchoredAtom4418 Fin15AnchoredAtom4419
    Fin15AnchoredAtom4425 Fin15AnchoredAtom4441 Fin15AnchoredAtom4474 Fin15AnchoredAtom4475
    Fin15AnchoredAtom4481 Fin15AnchoredAtom4497 Fin15AnchoredAtom4552 Fin15AnchoredAtom4600
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

theorem fin15Anchored_clause31547 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2494 chi ∧
      ¬Fin15AnchoredAtom2495 chi ∧
      ¬Fin15AnchoredAtom2497 chi ∧
      ¬Fin15AnchoredAtom2498 chi ∧
      ¬Fin15AnchoredAtom2513 chi ∧
      ¬Fin15AnchoredAtom2515 chi ∧
      ¬Fin15AnchoredAtom2516 chi ∧
      ¬Fin15AnchoredAtom2519 chi ∧
      ¬Fin15AnchoredAtom2520 chi ∧
      ¬Fin15AnchoredAtom2525 chi ∧
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
      ¬Fin15AnchoredAtom4375 chi ∧
      ¬Fin15AnchoredAtom4377 chi ∧
      ¬Fin15AnchoredAtom4378 chi ∧
      ¬Fin15AnchoredAtom4381 chi ∧
      ¬Fin15AnchoredAtom4382 chi ∧
      ¬Fin15AnchoredAtom4387 chi ∧
      ¬Fin15AnchoredAtom4427 chi ∧
      ¬Fin15AnchoredAtom4428 chi ∧
      ¬Fin15AnchoredAtom4433 chi ∧
      ¬Fin15AnchoredAtom4439 chi ∧
      ¬Fin15AnchoredAtom4483 chi ∧
      ¬Fin15AnchoredAtom4484 chi ∧
      ¬Fin15AnchoredAtom4489 chi ∧
      ¬Fin15AnchoredAtom4495 chi ∧
      ¬Fin15AnchoredAtom4560 chi ∧
      ¬Fin15AnchoredAtom4609 chi ∧
      ¬Fin15AnchoredAtom4610 chi ∧
      ¬Fin15AnchoredAtom4615 chi ∧
      ¬Fin15AnchoredAtom4621 chi ∧
      ¬Fin15AnchoredAtom4686 chi ∧
      ¬Fin15AnchoredAtom4756 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 5, 6, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13937
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2494 Fin15AnchoredAtom2495 Fin15AnchoredAtom2497
    Fin15AnchoredAtom2498 Fin15AnchoredAtom2513 Fin15AnchoredAtom2515 Fin15AnchoredAtom2516
    Fin15AnchoredAtom2519 Fin15AnchoredAtom2520 Fin15AnchoredAtom2525 Fin15AnchoredAtom2541
    Fin15AnchoredAtom2543 Fin15AnchoredAtom2544 Fin15AnchoredAtom2547 Fin15AnchoredAtom2548
    Fin15AnchoredAtom2553 Fin15AnchoredAtom2593 Fin15AnchoredAtom2594 Fin15AnchoredAtom2599
    Fin15AnchoredAtom2605 Fin15AnchoredAtom2625 Fin15AnchoredAtom2627 Fin15AnchoredAtom2628
    Fin15AnchoredAtom2631 Fin15AnchoredAtom2632 Fin15AnchoredAtom2637 Fin15AnchoredAtom2677
    Fin15AnchoredAtom2678 Fin15AnchoredAtom2683 Fin15AnchoredAtom2689 Fin15AnchoredAtom2733
    Fin15AnchoredAtom2734 Fin15AnchoredAtom2739 Fin15AnchoredAtom2745 Fin15AnchoredAtom2810
    Fin15AnchoredAtom4375 Fin15AnchoredAtom4377 Fin15AnchoredAtom4378 Fin15AnchoredAtom4381
    Fin15AnchoredAtom4382 Fin15AnchoredAtom4387 Fin15AnchoredAtom4427 Fin15AnchoredAtom4428
    Fin15AnchoredAtom4433 Fin15AnchoredAtom4439 Fin15AnchoredAtom4483 Fin15AnchoredAtom4484
    Fin15AnchoredAtom4489 Fin15AnchoredAtom4495 Fin15AnchoredAtom4560 Fin15AnchoredAtom4609
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

theorem fin15Anchored_clause31548 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2494 chi ∧
      ¬Fin15AnchoredAtom2495 chi ∧
      ¬Fin15AnchoredAtom2497 chi ∧
      ¬Fin15AnchoredAtom2499 chi ∧
      ¬Fin15AnchoredAtom2513 chi ∧
      ¬Fin15AnchoredAtom2515 chi ∧
      ¬Fin15AnchoredAtom2517 chi ∧
      ¬Fin15AnchoredAtom2519 chi ∧
      ¬Fin15AnchoredAtom2521 chi ∧
      ¬Fin15AnchoredAtom2526 chi ∧
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
      ¬Fin15AnchoredAtom4375 chi ∧
      ¬Fin15AnchoredAtom4377 chi ∧
      ¬Fin15AnchoredAtom4379 chi ∧
      ¬Fin15AnchoredAtom4381 chi ∧
      ¬Fin15AnchoredAtom4383 chi ∧
      ¬Fin15AnchoredAtom4388 chi ∧
      ¬Fin15AnchoredAtom4427 chi ∧
      ¬Fin15AnchoredAtom4429 chi ∧
      ¬Fin15AnchoredAtom4434 chi ∧
      ¬Fin15AnchoredAtom4440 chi ∧
      ¬Fin15AnchoredAtom4483 chi ∧
      ¬Fin15AnchoredAtom4485 chi ∧
      ¬Fin15AnchoredAtom4490 chi ∧
      ¬Fin15AnchoredAtom4496 chi ∧
      ¬Fin15AnchoredAtom4561 chi ∧
      ¬Fin15AnchoredAtom4609 chi ∧
      ¬Fin15AnchoredAtom4611 chi ∧
      ¬Fin15AnchoredAtom4616 chi ∧
      ¬Fin15AnchoredAtom4622 chi ∧
      ¬Fin15AnchoredAtom4687 chi ∧
      ¬Fin15AnchoredAtom4757 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 5, 6, 9, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22129
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2494 Fin15AnchoredAtom2495 Fin15AnchoredAtom2497
    Fin15AnchoredAtom2499 Fin15AnchoredAtom2513 Fin15AnchoredAtom2515 Fin15AnchoredAtom2517
    Fin15AnchoredAtom2519 Fin15AnchoredAtom2521 Fin15AnchoredAtom2526 Fin15AnchoredAtom2541
    Fin15AnchoredAtom2543 Fin15AnchoredAtom2545 Fin15AnchoredAtom2547 Fin15AnchoredAtom2549
    Fin15AnchoredAtom2554 Fin15AnchoredAtom2593 Fin15AnchoredAtom2595 Fin15AnchoredAtom2600
    Fin15AnchoredAtom2606 Fin15AnchoredAtom2625 Fin15AnchoredAtom2627 Fin15AnchoredAtom2629
    Fin15AnchoredAtom2631 Fin15AnchoredAtom2633 Fin15AnchoredAtom2638 Fin15AnchoredAtom2677
    Fin15AnchoredAtom2679 Fin15AnchoredAtom2684 Fin15AnchoredAtom2690 Fin15AnchoredAtom2733
    Fin15AnchoredAtom2735 Fin15AnchoredAtom2740 Fin15AnchoredAtom2746 Fin15AnchoredAtom2811
    Fin15AnchoredAtom4375 Fin15AnchoredAtom4377 Fin15AnchoredAtom4379 Fin15AnchoredAtom4381
    Fin15AnchoredAtom4383 Fin15AnchoredAtom4388 Fin15AnchoredAtom4427 Fin15AnchoredAtom4429
    Fin15AnchoredAtom4434 Fin15AnchoredAtom4440 Fin15AnchoredAtom4483 Fin15AnchoredAtom4485
    Fin15AnchoredAtom4490 Fin15AnchoredAtom4496 Fin15AnchoredAtom4561 Fin15AnchoredAtom4609
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

theorem fin15Anchored_clause31549 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2494 chi ∧
      ¬Fin15AnchoredAtom2495 chi ∧
      ¬Fin15AnchoredAtom2498 chi ∧
      ¬Fin15AnchoredAtom2499 chi ∧
      ¬Fin15AnchoredAtom2513 chi ∧
      ¬Fin15AnchoredAtom2516 chi ∧
      ¬Fin15AnchoredAtom2517 chi ∧
      ¬Fin15AnchoredAtom2520 chi ∧
      ¬Fin15AnchoredAtom2521 chi ∧
      ¬Fin15AnchoredAtom2527 chi ∧
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
      ¬Fin15AnchoredAtom4375 chi ∧
      ¬Fin15AnchoredAtom4378 chi ∧
      ¬Fin15AnchoredAtom4379 chi ∧
      ¬Fin15AnchoredAtom4382 chi ∧
      ¬Fin15AnchoredAtom4383 chi ∧
      ¬Fin15AnchoredAtom4389 chi ∧
      ¬Fin15AnchoredAtom4428 chi ∧
      ¬Fin15AnchoredAtom4429 chi ∧
      ¬Fin15AnchoredAtom4435 chi ∧
      ¬Fin15AnchoredAtom4441 chi ∧
      ¬Fin15AnchoredAtom4484 chi ∧
      ¬Fin15AnchoredAtom4485 chi ∧
      ¬Fin15AnchoredAtom4491 chi ∧
      ¬Fin15AnchoredAtom4497 chi ∧
      ¬Fin15AnchoredAtom4562 chi ∧
      ¬Fin15AnchoredAtom4610 chi ∧
      ¬Fin15AnchoredAtom4611 chi ∧
      ¬Fin15AnchoredAtom4617 chi ∧
      ¬Fin15AnchoredAtom4623 chi ∧
      ¬Fin15AnchoredAtom4688 chi ∧
      ¬Fin15AnchoredAtom4758 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 5, 6, 9, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26225
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2494 Fin15AnchoredAtom2495 Fin15AnchoredAtom2498
    Fin15AnchoredAtom2499 Fin15AnchoredAtom2513 Fin15AnchoredAtom2516 Fin15AnchoredAtom2517
    Fin15AnchoredAtom2520 Fin15AnchoredAtom2521 Fin15AnchoredAtom2527 Fin15AnchoredAtom2541
    Fin15AnchoredAtom2544 Fin15AnchoredAtom2545 Fin15AnchoredAtom2548 Fin15AnchoredAtom2549
    Fin15AnchoredAtom2555 Fin15AnchoredAtom2594 Fin15AnchoredAtom2595 Fin15AnchoredAtom2601
    Fin15AnchoredAtom2607 Fin15AnchoredAtom2625 Fin15AnchoredAtom2628 Fin15AnchoredAtom2629
    Fin15AnchoredAtom2632 Fin15AnchoredAtom2633 Fin15AnchoredAtom2639 Fin15AnchoredAtom2678
    Fin15AnchoredAtom2679 Fin15AnchoredAtom2685 Fin15AnchoredAtom2691 Fin15AnchoredAtom2734
    Fin15AnchoredAtom2735 Fin15AnchoredAtom2741 Fin15AnchoredAtom2747 Fin15AnchoredAtom2812
    Fin15AnchoredAtom4375 Fin15AnchoredAtom4378 Fin15AnchoredAtom4379 Fin15AnchoredAtom4382
    Fin15AnchoredAtom4383 Fin15AnchoredAtom4389 Fin15AnchoredAtom4428 Fin15AnchoredAtom4429
    Fin15AnchoredAtom4435 Fin15AnchoredAtom4441 Fin15AnchoredAtom4484 Fin15AnchoredAtom4485
    Fin15AnchoredAtom4491 Fin15AnchoredAtom4497 Fin15AnchoredAtom4562 Fin15AnchoredAtom4610
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

theorem fin15Anchored_clause31550 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2494 chi ∧
      ¬Fin15AnchoredAtom2497 chi ∧
      ¬Fin15AnchoredAtom2498 chi ∧
      ¬Fin15AnchoredAtom2499 chi ∧
      ¬Fin15AnchoredAtom2515 chi ∧
      ¬Fin15AnchoredAtom2516 chi ∧
      ¬Fin15AnchoredAtom2517 chi ∧
      ¬Fin15AnchoredAtom2525 chi ∧
      ¬Fin15AnchoredAtom2526 chi ∧
      ¬Fin15AnchoredAtom2527 chi ∧
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
      ¬Fin15AnchoredAtom4377 chi ∧
      ¬Fin15AnchoredAtom4378 chi ∧
      ¬Fin15AnchoredAtom4379 chi ∧
      ¬Fin15AnchoredAtom4387 chi ∧
      ¬Fin15AnchoredAtom4388 chi ∧
      ¬Fin15AnchoredAtom4389 chi ∧
      ¬Fin15AnchoredAtom4433 chi ∧
      ¬Fin15AnchoredAtom4434 chi ∧
      ¬Fin15AnchoredAtom4435 chi ∧
      ¬Fin15AnchoredAtom4445 chi ∧
      ¬Fin15AnchoredAtom4489 chi ∧
      ¬Fin15AnchoredAtom4490 chi ∧
      ¬Fin15AnchoredAtom4491 chi ∧
      ¬Fin15AnchoredAtom4501 chi ∧
      ¬Fin15AnchoredAtom4566 chi ∧
      ¬Fin15AnchoredAtom4615 chi ∧
      ¬Fin15AnchoredAtom4616 chi ∧
      ¬Fin15AnchoredAtom4617 chi ∧
      ¬Fin15AnchoredAtom4627 chi ∧
      ¬Fin15AnchoredAtom4692 chi ∧
      ¬Fin15AnchoredAtom4762 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 5, 6, 9, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29297
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2494 Fin15AnchoredAtom2497 Fin15AnchoredAtom2498
    Fin15AnchoredAtom2499 Fin15AnchoredAtom2515 Fin15AnchoredAtom2516 Fin15AnchoredAtom2517
    Fin15AnchoredAtom2525 Fin15AnchoredAtom2526 Fin15AnchoredAtom2527 Fin15AnchoredAtom2543
    Fin15AnchoredAtom2544 Fin15AnchoredAtom2545 Fin15AnchoredAtom2553 Fin15AnchoredAtom2554
    Fin15AnchoredAtom2555 Fin15AnchoredAtom2599 Fin15AnchoredAtom2600 Fin15AnchoredAtom2601
    Fin15AnchoredAtom2611 Fin15AnchoredAtom2627 Fin15AnchoredAtom2628 Fin15AnchoredAtom2629
    Fin15AnchoredAtom2637 Fin15AnchoredAtom2638 Fin15AnchoredAtom2639 Fin15AnchoredAtom2683
    Fin15AnchoredAtom2684 Fin15AnchoredAtom2685 Fin15AnchoredAtom2695 Fin15AnchoredAtom2739
    Fin15AnchoredAtom2740 Fin15AnchoredAtom2741 Fin15AnchoredAtom2751 Fin15AnchoredAtom2816
    Fin15AnchoredAtom4377 Fin15AnchoredAtom4378 Fin15AnchoredAtom4379 Fin15AnchoredAtom4387
    Fin15AnchoredAtom4388 Fin15AnchoredAtom4389 Fin15AnchoredAtom4433 Fin15AnchoredAtom4434
    Fin15AnchoredAtom4435 Fin15AnchoredAtom4445 Fin15AnchoredAtom4489 Fin15AnchoredAtom4490
    Fin15AnchoredAtom4491 Fin15AnchoredAtom4501 Fin15AnchoredAtom4566 Fin15AnchoredAtom4615
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

theorem fin15Anchored_clause31551 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2495 chi ∧
      ¬Fin15AnchoredAtom2497 chi ∧
      ¬Fin15AnchoredAtom2498 chi ∧
      ¬Fin15AnchoredAtom2499 chi ∧
      ¬Fin15AnchoredAtom2519 chi ∧
      ¬Fin15AnchoredAtom2520 chi ∧
      ¬Fin15AnchoredAtom2521 chi ∧
      ¬Fin15AnchoredAtom2525 chi ∧
      ¬Fin15AnchoredAtom2526 chi ∧
      ¬Fin15AnchoredAtom2527 chi ∧
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
      ¬Fin15AnchoredAtom4381 chi ∧
      ¬Fin15AnchoredAtom4382 chi ∧
      ¬Fin15AnchoredAtom4383 chi ∧
      ¬Fin15AnchoredAtom4387 chi ∧
      ¬Fin15AnchoredAtom4388 chi ∧
      ¬Fin15AnchoredAtom4389 chi ∧
      ¬Fin15AnchoredAtom4439 chi ∧
      ¬Fin15AnchoredAtom4440 chi ∧
      ¬Fin15AnchoredAtom4441 chi ∧
      ¬Fin15AnchoredAtom4445 chi ∧
      ¬Fin15AnchoredAtom4495 chi ∧
      ¬Fin15AnchoredAtom4496 chi ∧
      ¬Fin15AnchoredAtom4497 chi ∧
      ¬Fin15AnchoredAtom4501 chi ∧
      ¬Fin15AnchoredAtom4570 chi ∧
      ¬Fin15AnchoredAtom4621 chi ∧
      ¬Fin15AnchoredAtom4622 chi ∧
      ¬Fin15AnchoredAtom4623 chi ∧
      ¬Fin15AnchoredAtom4627 chi ∧
      ¬Fin15AnchoredAtom4696 chi ∧
      ¬Fin15AnchoredAtom4766 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 5, 6, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29809
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2495 Fin15AnchoredAtom2497 Fin15AnchoredAtom2498
    Fin15AnchoredAtom2499 Fin15AnchoredAtom2519 Fin15AnchoredAtom2520 Fin15AnchoredAtom2521
    Fin15AnchoredAtom2525 Fin15AnchoredAtom2526 Fin15AnchoredAtom2527 Fin15AnchoredAtom2547
    Fin15AnchoredAtom2548 Fin15AnchoredAtom2549 Fin15AnchoredAtom2553 Fin15AnchoredAtom2554
    Fin15AnchoredAtom2555 Fin15AnchoredAtom2605 Fin15AnchoredAtom2606 Fin15AnchoredAtom2607
    Fin15AnchoredAtom2611 Fin15AnchoredAtom2631 Fin15AnchoredAtom2632 Fin15AnchoredAtom2633
    Fin15AnchoredAtom2637 Fin15AnchoredAtom2638 Fin15AnchoredAtom2639 Fin15AnchoredAtom2689
    Fin15AnchoredAtom2690 Fin15AnchoredAtom2691 Fin15AnchoredAtom2695 Fin15AnchoredAtom2745
    Fin15AnchoredAtom2746 Fin15AnchoredAtom2747 Fin15AnchoredAtom2751 Fin15AnchoredAtom2820
    Fin15AnchoredAtom4381 Fin15AnchoredAtom4382 Fin15AnchoredAtom4383 Fin15AnchoredAtom4387
    Fin15AnchoredAtom4388 Fin15AnchoredAtom4389 Fin15AnchoredAtom4439 Fin15AnchoredAtom4440
    Fin15AnchoredAtom4441 Fin15AnchoredAtom4445 Fin15AnchoredAtom4495 Fin15AnchoredAtom4496
    Fin15AnchoredAtom4497 Fin15AnchoredAtom4501 Fin15AnchoredAtom4570 Fin15AnchoredAtom4621
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

theorem fin15Anchored_clause31552 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2500 chi ∧
      ¬Fin15AnchoredAtom2501 chi ∧
      ¬Fin15AnchoredAtom2502 chi ∧
      ¬Fin15AnchoredAtom2504 chi ∧
      ¬Fin15AnchoredAtom2507 chi ∧
      ¬Fin15AnchoredAtom2508 chi ∧
      ¬Fin15AnchoredAtom2510 chi ∧
      ¬Fin15AnchoredAtom2513 chi ∧
      ¬Fin15AnchoredAtom2515 chi ∧
      ¬Fin15AnchoredAtom2519 chi ∧
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
      ¬Fin15AnchoredAtom2640 chi ∧
      ¬Fin15AnchoredAtom2641 chi ∧
      ¬Fin15AnchoredAtom2643 chi ∧
      ¬Fin15AnchoredAtom2646 chi ∧
      ¬Fin15AnchoredAtom2648 chi ∧
      ¬Fin15AnchoredAtom2652 chi ∧
      ¬Fin15AnchoredAtom2661 chi ∧
      ¬Fin15AnchoredAtom2663 chi ∧
      ¬Fin15AnchoredAtom2667 chi ∧
      ¬Fin15AnchoredAtom2677 chi ∧
      ¬Fin15AnchoredAtom2752 chi ∧
      ¬Fin15AnchoredAtom2754 chi ∧
      ¬Fin15AnchoredAtom2758 chi ∧
      ¬Fin15AnchoredAtom2768 chi ∧
      ¬Fin15AnchoredAtom2788 chi ∧
      ¬Fin15AnchoredAtom4390 chi ∧
      ¬Fin15AnchoredAtom4391 chi ∧
      ¬Fin15AnchoredAtom4393 chi ∧
      ¬Fin15AnchoredAtom4396 chi ∧
      ¬Fin15AnchoredAtom4398 chi ∧
      ¬Fin15AnchoredAtom4402 chi ∧
      ¬Fin15AnchoredAtom4411 chi ∧
      ¬Fin15AnchoredAtom4413 chi ∧
      ¬Fin15AnchoredAtom4417 chi ∧
      ¬Fin15AnchoredAtom4427 chi ∧
      ¬Fin15AnchoredAtom4502 chi ∧
      ¬Fin15AnchoredAtom4504 chi ∧
      ¬Fin15AnchoredAtom4508 chi ∧
      ¬Fin15AnchoredAtom4518 chi ∧
      ¬Fin15AnchoredAtom4538 chi ∧
      ¬Fin15AnchoredAtom4628 chi ∧
      ¬Fin15AnchoredAtom4630 chi ∧
      ¬Fin15AnchoredAtom4634 chi ∧
      ¬Fin15AnchoredAtom4644 chi ∧
      ¬Fin15AnchoredAtom4664 chi ∧
      ¬Fin15AnchoredAtom4769 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 5, 7, 8, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask06065
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2500 Fin15AnchoredAtom2501 Fin15AnchoredAtom2502
    Fin15AnchoredAtom2504 Fin15AnchoredAtom2507 Fin15AnchoredAtom2508 Fin15AnchoredAtom2510
    Fin15AnchoredAtom2513 Fin15AnchoredAtom2515 Fin15AnchoredAtom2519 Fin15AnchoredAtom2556
    Fin15AnchoredAtom2557 Fin15AnchoredAtom2559 Fin15AnchoredAtom2562 Fin15AnchoredAtom2564
    Fin15AnchoredAtom2568 Fin15AnchoredAtom2577 Fin15AnchoredAtom2579 Fin15AnchoredAtom2583
    Fin15AnchoredAtom2593 Fin15AnchoredAtom2640 Fin15AnchoredAtom2641 Fin15AnchoredAtom2643
    Fin15AnchoredAtom2646 Fin15AnchoredAtom2648 Fin15AnchoredAtom2652 Fin15AnchoredAtom2661
    Fin15AnchoredAtom2663 Fin15AnchoredAtom2667 Fin15AnchoredAtom2677 Fin15AnchoredAtom2752
    Fin15AnchoredAtom2754 Fin15AnchoredAtom2758 Fin15AnchoredAtom2768 Fin15AnchoredAtom2788
    Fin15AnchoredAtom4390 Fin15AnchoredAtom4391 Fin15AnchoredAtom4393 Fin15AnchoredAtom4396
    Fin15AnchoredAtom4398 Fin15AnchoredAtom4402 Fin15AnchoredAtom4411 Fin15AnchoredAtom4413
    Fin15AnchoredAtom4417 Fin15AnchoredAtom4427 Fin15AnchoredAtom4502 Fin15AnchoredAtom4504
    Fin15AnchoredAtom4508 Fin15AnchoredAtom4518 Fin15AnchoredAtom4538 Fin15AnchoredAtom4628
    Fin15AnchoredAtom4630 Fin15AnchoredAtom4634 Fin15AnchoredAtom4644 Fin15AnchoredAtom4664
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

theorem fin15Anchored_clause31553 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2500 chi ∧
      ¬Fin15AnchoredAtom2501 chi ∧
      ¬Fin15AnchoredAtom2502 chi ∧
      ¬Fin15AnchoredAtom2505 chi ∧
      ¬Fin15AnchoredAtom2507 chi ∧
      ¬Fin15AnchoredAtom2508 chi ∧
      ¬Fin15AnchoredAtom2511 chi ∧
      ¬Fin15AnchoredAtom2513 chi ∧
      ¬Fin15AnchoredAtom2516 chi ∧
      ¬Fin15AnchoredAtom2520 chi ∧
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
      ¬Fin15AnchoredAtom4390 chi ∧
      ¬Fin15AnchoredAtom4391 chi ∧
      ¬Fin15AnchoredAtom4394 chi ∧
      ¬Fin15AnchoredAtom4396 chi ∧
      ¬Fin15AnchoredAtom4399 chi ∧
      ¬Fin15AnchoredAtom4403 chi ∧
      ¬Fin15AnchoredAtom4411 chi ∧
      ¬Fin15AnchoredAtom4414 chi ∧
      ¬Fin15AnchoredAtom4418 chi ∧
      ¬Fin15AnchoredAtom4428 chi ∧
      ¬Fin15AnchoredAtom4502 chi ∧
      ¬Fin15AnchoredAtom4505 chi ∧
      ¬Fin15AnchoredAtom4509 chi ∧
      ¬Fin15AnchoredAtom4519 chi ∧
      ¬Fin15AnchoredAtom4539 chi ∧
      ¬Fin15AnchoredAtom4628 chi ∧
      ¬Fin15AnchoredAtom4631 chi ∧
      ¬Fin15AnchoredAtom4635 chi ∧
      ¬Fin15AnchoredAtom4645 chi ∧
      ¬Fin15AnchoredAtom4665 chi ∧
      ¬Fin15AnchoredAtom4770 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 5, 7, 8, 9, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask10161
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2500 Fin15AnchoredAtom2501 Fin15AnchoredAtom2502
    Fin15AnchoredAtom2505 Fin15AnchoredAtom2507 Fin15AnchoredAtom2508 Fin15AnchoredAtom2511
    Fin15AnchoredAtom2513 Fin15AnchoredAtom2516 Fin15AnchoredAtom2520 Fin15AnchoredAtom2556
    Fin15AnchoredAtom2557 Fin15AnchoredAtom2560 Fin15AnchoredAtom2562 Fin15AnchoredAtom2565
    Fin15AnchoredAtom2569 Fin15AnchoredAtom2577 Fin15AnchoredAtom2580 Fin15AnchoredAtom2584
    Fin15AnchoredAtom2594 Fin15AnchoredAtom2640 Fin15AnchoredAtom2641 Fin15AnchoredAtom2644
    Fin15AnchoredAtom2646 Fin15AnchoredAtom2649 Fin15AnchoredAtom2653 Fin15AnchoredAtom2661
    Fin15AnchoredAtom2664 Fin15AnchoredAtom2668 Fin15AnchoredAtom2678 Fin15AnchoredAtom2752
    Fin15AnchoredAtom2755 Fin15AnchoredAtom2759 Fin15AnchoredAtom2769 Fin15AnchoredAtom2789
    Fin15AnchoredAtom4390 Fin15AnchoredAtom4391 Fin15AnchoredAtom4394 Fin15AnchoredAtom4396
    Fin15AnchoredAtom4399 Fin15AnchoredAtom4403 Fin15AnchoredAtom4411 Fin15AnchoredAtom4414
    Fin15AnchoredAtom4418 Fin15AnchoredAtom4428 Fin15AnchoredAtom4502 Fin15AnchoredAtom4505
    Fin15AnchoredAtom4509 Fin15AnchoredAtom4519 Fin15AnchoredAtom4539 Fin15AnchoredAtom4628
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

theorem fin15Anchored_clause31554 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2500 chi ∧
      ¬Fin15AnchoredAtom2501 chi ∧
      ¬Fin15AnchoredAtom2502 chi ∧
      ¬Fin15AnchoredAtom2506 chi ∧
      ¬Fin15AnchoredAtom2507 chi ∧
      ¬Fin15AnchoredAtom2508 chi ∧
      ¬Fin15AnchoredAtom2512 chi ∧
      ¬Fin15AnchoredAtom2513 chi ∧
      ¬Fin15AnchoredAtom2517 chi ∧
      ¬Fin15AnchoredAtom2521 chi ∧
      ¬Fin15AnchoredAtom2556 chi ∧
      ¬Fin15AnchoredAtom2557 chi ∧
      ¬Fin15AnchoredAtom2561 chi ∧
      ¬Fin15AnchoredAtom2562 chi ∧
      ¬Fin15AnchoredAtom2566 chi ∧
      ¬Fin15AnchoredAtom2570 chi ∧
      ¬Fin15AnchoredAtom2577 chi ∧
      ¬Fin15AnchoredAtom2581 chi ∧
      ¬Fin15AnchoredAtom2585 chi ∧
      ¬Fin15AnchoredAtom2595 chi ∧
      ¬Fin15AnchoredAtom2640 chi ∧
      ¬Fin15AnchoredAtom2641 chi ∧
      ¬Fin15AnchoredAtom2645 chi ∧
      ¬Fin15AnchoredAtom2646 chi ∧
      ¬Fin15AnchoredAtom2650 chi ∧
      ¬Fin15AnchoredAtom2654 chi ∧
      ¬Fin15AnchoredAtom2661 chi ∧
      ¬Fin15AnchoredAtom2665 chi ∧
      ¬Fin15AnchoredAtom2669 chi ∧
      ¬Fin15AnchoredAtom2679 chi ∧
      ¬Fin15AnchoredAtom2752 chi ∧
      ¬Fin15AnchoredAtom2756 chi ∧
      ¬Fin15AnchoredAtom2760 chi ∧
      ¬Fin15AnchoredAtom2770 chi ∧
      ¬Fin15AnchoredAtom2790 chi ∧
      ¬Fin15AnchoredAtom4390 chi ∧
      ¬Fin15AnchoredAtom4391 chi ∧
      ¬Fin15AnchoredAtom4395 chi ∧
      ¬Fin15AnchoredAtom4396 chi ∧
      ¬Fin15AnchoredAtom4400 chi ∧
      ¬Fin15AnchoredAtom4404 chi ∧
      ¬Fin15AnchoredAtom4411 chi ∧
      ¬Fin15AnchoredAtom4415 chi ∧
      ¬Fin15AnchoredAtom4419 chi ∧
      ¬Fin15AnchoredAtom4429 chi ∧
      ¬Fin15AnchoredAtom4502 chi ∧
      ¬Fin15AnchoredAtom4506 chi ∧
      ¬Fin15AnchoredAtom4510 chi ∧
      ¬Fin15AnchoredAtom4520 chi ∧
      ¬Fin15AnchoredAtom4540 chi ∧
      ¬Fin15AnchoredAtom4628 chi ∧
      ¬Fin15AnchoredAtom4632 chi ∧
      ¬Fin15AnchoredAtom4636 chi ∧
      ¬Fin15AnchoredAtom4646 chi ∧
      ¬Fin15AnchoredAtom4666 chi ∧
      ¬Fin15AnchoredAtom4771 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 5, 7, 8, 9, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask18353
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2500 Fin15AnchoredAtom2501 Fin15AnchoredAtom2502
    Fin15AnchoredAtom2506 Fin15AnchoredAtom2507 Fin15AnchoredAtom2508 Fin15AnchoredAtom2512
    Fin15AnchoredAtom2513 Fin15AnchoredAtom2517 Fin15AnchoredAtom2521 Fin15AnchoredAtom2556
    Fin15AnchoredAtom2557 Fin15AnchoredAtom2561 Fin15AnchoredAtom2562 Fin15AnchoredAtom2566
    Fin15AnchoredAtom2570 Fin15AnchoredAtom2577 Fin15AnchoredAtom2581 Fin15AnchoredAtom2585
    Fin15AnchoredAtom2595 Fin15AnchoredAtom2640 Fin15AnchoredAtom2641 Fin15AnchoredAtom2645
    Fin15AnchoredAtom2646 Fin15AnchoredAtom2650 Fin15AnchoredAtom2654 Fin15AnchoredAtom2661
    Fin15AnchoredAtom2665 Fin15AnchoredAtom2669 Fin15AnchoredAtom2679 Fin15AnchoredAtom2752
    Fin15AnchoredAtom2756 Fin15AnchoredAtom2760 Fin15AnchoredAtom2770 Fin15AnchoredAtom2790
    Fin15AnchoredAtom4390 Fin15AnchoredAtom4391 Fin15AnchoredAtom4395 Fin15AnchoredAtom4396
    Fin15AnchoredAtom4400 Fin15AnchoredAtom4404 Fin15AnchoredAtom4411 Fin15AnchoredAtom4415
    Fin15AnchoredAtom4419 Fin15AnchoredAtom4429 Fin15AnchoredAtom4502 Fin15AnchoredAtom4506
    Fin15AnchoredAtom4510 Fin15AnchoredAtom4520 Fin15AnchoredAtom4540 Fin15AnchoredAtom4628
    Fin15AnchoredAtom4632 Fin15AnchoredAtom4636 Fin15AnchoredAtom4646 Fin15AnchoredAtom4666
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

theorem fin15Anchored_clause31555 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2500 chi ∧
      ¬Fin15AnchoredAtom2501 chi ∧
      ¬Fin15AnchoredAtom2504 chi ∧
      ¬Fin15AnchoredAtom2505 chi ∧
      ¬Fin15AnchoredAtom2507 chi ∧
      ¬Fin15AnchoredAtom2510 chi ∧
      ¬Fin15AnchoredAtom2511 chi ∧
      ¬Fin15AnchoredAtom2515 chi ∧
      ¬Fin15AnchoredAtom2516 chi ∧
      ¬Fin15AnchoredAtom2525 chi ∧
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
      ¬Fin15AnchoredAtom2640 chi ∧
      ¬Fin15AnchoredAtom2643 chi ∧
      ¬Fin15AnchoredAtom2644 chi ∧
      ¬Fin15AnchoredAtom2648 chi ∧
      ¬Fin15AnchoredAtom2649 chi ∧
      ¬Fin15AnchoredAtom2658 chi ∧
      ¬Fin15AnchoredAtom2663 chi ∧
      ¬Fin15AnchoredAtom2664 chi ∧
      ¬Fin15AnchoredAtom2673 chi ∧
      ¬Fin15AnchoredAtom2683 chi ∧
      ¬Fin15AnchoredAtom2754 chi ∧
      ¬Fin15AnchoredAtom2755 chi ∧
      ¬Fin15AnchoredAtom2764 chi ∧
      ¬Fin15AnchoredAtom2774 chi ∧
      ¬Fin15AnchoredAtom2794 chi ∧
      ¬Fin15AnchoredAtom4390 chi ∧
      ¬Fin15AnchoredAtom4393 chi ∧
      ¬Fin15AnchoredAtom4394 chi ∧
      ¬Fin15AnchoredAtom4398 chi ∧
      ¬Fin15AnchoredAtom4399 chi ∧
      ¬Fin15AnchoredAtom4408 chi ∧
      ¬Fin15AnchoredAtom4413 chi ∧
      ¬Fin15AnchoredAtom4414 chi ∧
      ¬Fin15AnchoredAtom4423 chi ∧
      ¬Fin15AnchoredAtom4433 chi ∧
      ¬Fin15AnchoredAtom4504 chi ∧
      ¬Fin15AnchoredAtom4505 chi ∧
      ¬Fin15AnchoredAtom4514 chi ∧
      ¬Fin15AnchoredAtom4524 chi ∧
      ¬Fin15AnchoredAtom4544 chi ∧
      ¬Fin15AnchoredAtom4630 chi ∧
      ¬Fin15AnchoredAtom4631 chi ∧
      ¬Fin15AnchoredAtom4640 chi ∧
      ¬Fin15AnchoredAtom4650 chi ∧
      ¬Fin15AnchoredAtom4670 chi ∧
      ¬Fin15AnchoredAtom4775 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 5, 7, 8, 9, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13233
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2500 Fin15AnchoredAtom2501 Fin15AnchoredAtom2504
    Fin15AnchoredAtom2505 Fin15AnchoredAtom2507 Fin15AnchoredAtom2510 Fin15AnchoredAtom2511
    Fin15AnchoredAtom2515 Fin15AnchoredAtom2516 Fin15AnchoredAtom2525 Fin15AnchoredAtom2556
    Fin15AnchoredAtom2559 Fin15AnchoredAtom2560 Fin15AnchoredAtom2564 Fin15AnchoredAtom2565
    Fin15AnchoredAtom2574 Fin15AnchoredAtom2579 Fin15AnchoredAtom2580 Fin15AnchoredAtom2589
    Fin15AnchoredAtom2599 Fin15AnchoredAtom2640 Fin15AnchoredAtom2643 Fin15AnchoredAtom2644
    Fin15AnchoredAtom2648 Fin15AnchoredAtom2649 Fin15AnchoredAtom2658 Fin15AnchoredAtom2663
    Fin15AnchoredAtom2664 Fin15AnchoredAtom2673 Fin15AnchoredAtom2683 Fin15AnchoredAtom2754
    Fin15AnchoredAtom2755 Fin15AnchoredAtom2764 Fin15AnchoredAtom2774 Fin15AnchoredAtom2794
    Fin15AnchoredAtom4390 Fin15AnchoredAtom4393 Fin15AnchoredAtom4394 Fin15AnchoredAtom4398
    Fin15AnchoredAtom4399 Fin15AnchoredAtom4408 Fin15AnchoredAtom4413 Fin15AnchoredAtom4414
    Fin15AnchoredAtom4423 Fin15AnchoredAtom4433 Fin15AnchoredAtom4504 Fin15AnchoredAtom4505
    Fin15AnchoredAtom4514 Fin15AnchoredAtom4524 Fin15AnchoredAtom4544 Fin15AnchoredAtom4630
    Fin15AnchoredAtom4631 Fin15AnchoredAtom4640 Fin15AnchoredAtom4650 Fin15AnchoredAtom4670
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

theorem fin15Anchored_clause31556 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2500 chi ∧
      ¬Fin15AnchoredAtom2501 chi ∧
      ¬Fin15AnchoredAtom2504 chi ∧
      ¬Fin15AnchoredAtom2506 chi ∧
      ¬Fin15AnchoredAtom2507 chi ∧
      ¬Fin15AnchoredAtom2510 chi ∧
      ¬Fin15AnchoredAtom2512 chi ∧
      ¬Fin15AnchoredAtom2515 chi ∧
      ¬Fin15AnchoredAtom2517 chi ∧
      ¬Fin15AnchoredAtom2526 chi ∧
      ¬Fin15AnchoredAtom2556 chi ∧
      ¬Fin15AnchoredAtom2559 chi ∧
      ¬Fin15AnchoredAtom2561 chi ∧
      ¬Fin15AnchoredAtom2564 chi ∧
      ¬Fin15AnchoredAtom2566 chi ∧
      ¬Fin15AnchoredAtom2575 chi ∧
      ¬Fin15AnchoredAtom2579 chi ∧
      ¬Fin15AnchoredAtom2581 chi ∧
      ¬Fin15AnchoredAtom2590 chi ∧
      ¬Fin15AnchoredAtom2600 chi ∧
      ¬Fin15AnchoredAtom2640 chi ∧
      ¬Fin15AnchoredAtom2643 chi ∧
      ¬Fin15AnchoredAtom2645 chi ∧
      ¬Fin15AnchoredAtom2648 chi ∧
      ¬Fin15AnchoredAtom2650 chi ∧
      ¬Fin15AnchoredAtom2659 chi ∧
      ¬Fin15AnchoredAtom2663 chi ∧
      ¬Fin15AnchoredAtom2665 chi ∧
      ¬Fin15AnchoredAtom2674 chi ∧
      ¬Fin15AnchoredAtom2684 chi ∧
      ¬Fin15AnchoredAtom2754 chi ∧
      ¬Fin15AnchoredAtom2756 chi ∧
      ¬Fin15AnchoredAtom2765 chi ∧
      ¬Fin15AnchoredAtom2775 chi ∧
      ¬Fin15AnchoredAtom2795 chi ∧
      ¬Fin15AnchoredAtom4390 chi ∧
      ¬Fin15AnchoredAtom4393 chi ∧
      ¬Fin15AnchoredAtom4395 chi ∧
      ¬Fin15AnchoredAtom4398 chi ∧
      ¬Fin15AnchoredAtom4400 chi ∧
      ¬Fin15AnchoredAtom4409 chi ∧
      ¬Fin15AnchoredAtom4413 chi ∧
      ¬Fin15AnchoredAtom4415 chi ∧
      ¬Fin15AnchoredAtom4424 chi ∧
      ¬Fin15AnchoredAtom4434 chi ∧
      ¬Fin15AnchoredAtom4504 chi ∧
      ¬Fin15AnchoredAtom4506 chi ∧
      ¬Fin15AnchoredAtom4515 chi ∧
      ¬Fin15AnchoredAtom4525 chi ∧
      ¬Fin15AnchoredAtom4545 chi ∧
      ¬Fin15AnchoredAtom4630 chi ∧
      ¬Fin15AnchoredAtom4632 chi ∧
      ¬Fin15AnchoredAtom4641 chi ∧
      ¬Fin15AnchoredAtom4651 chi ∧
      ¬Fin15AnchoredAtom4671 chi ∧
      ¬Fin15AnchoredAtom4776 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 5, 7, 8, 9, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21425
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2500 Fin15AnchoredAtom2501 Fin15AnchoredAtom2504
    Fin15AnchoredAtom2506 Fin15AnchoredAtom2507 Fin15AnchoredAtom2510 Fin15AnchoredAtom2512
    Fin15AnchoredAtom2515 Fin15AnchoredAtom2517 Fin15AnchoredAtom2526 Fin15AnchoredAtom2556
    Fin15AnchoredAtom2559 Fin15AnchoredAtom2561 Fin15AnchoredAtom2564 Fin15AnchoredAtom2566
    Fin15AnchoredAtom2575 Fin15AnchoredAtom2579 Fin15AnchoredAtom2581 Fin15AnchoredAtom2590
    Fin15AnchoredAtom2600 Fin15AnchoredAtom2640 Fin15AnchoredAtom2643 Fin15AnchoredAtom2645
    Fin15AnchoredAtom2648 Fin15AnchoredAtom2650 Fin15AnchoredAtom2659 Fin15AnchoredAtom2663
    Fin15AnchoredAtom2665 Fin15AnchoredAtom2674 Fin15AnchoredAtom2684 Fin15AnchoredAtom2754
    Fin15AnchoredAtom2756 Fin15AnchoredAtom2765 Fin15AnchoredAtom2775 Fin15AnchoredAtom2795
    Fin15AnchoredAtom4390 Fin15AnchoredAtom4393 Fin15AnchoredAtom4395 Fin15AnchoredAtom4398
    Fin15AnchoredAtom4400 Fin15AnchoredAtom4409 Fin15AnchoredAtom4413 Fin15AnchoredAtom4415
    Fin15AnchoredAtom4424 Fin15AnchoredAtom4434 Fin15AnchoredAtom4504 Fin15AnchoredAtom4506
    Fin15AnchoredAtom4515 Fin15AnchoredAtom4525 Fin15AnchoredAtom4545 Fin15AnchoredAtom4630
    Fin15AnchoredAtom4632 Fin15AnchoredAtom4641 Fin15AnchoredAtom4651 Fin15AnchoredAtom4671
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

theorem fin15Anchored_clause31557 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2500 chi ∧
      ¬Fin15AnchoredAtom2501 chi ∧
      ¬Fin15AnchoredAtom2505 chi ∧
      ¬Fin15AnchoredAtom2506 chi ∧
      ¬Fin15AnchoredAtom2507 chi ∧
      ¬Fin15AnchoredAtom2511 chi ∧
      ¬Fin15AnchoredAtom2512 chi ∧
      ¬Fin15AnchoredAtom2516 chi ∧
      ¬Fin15AnchoredAtom2517 chi ∧
      ¬Fin15AnchoredAtom2527 chi ∧
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
      ¬Fin15AnchoredAtom2640 chi ∧
      ¬Fin15AnchoredAtom2644 chi ∧
      ¬Fin15AnchoredAtom2645 chi ∧
      ¬Fin15AnchoredAtom2649 chi ∧
      ¬Fin15AnchoredAtom2650 chi ∧
      ¬Fin15AnchoredAtom2660 chi ∧
      ¬Fin15AnchoredAtom2664 chi ∧
      ¬Fin15AnchoredAtom2665 chi ∧
      ¬Fin15AnchoredAtom2675 chi ∧
      ¬Fin15AnchoredAtom2685 chi ∧
      ¬Fin15AnchoredAtom2755 chi ∧
      ¬Fin15AnchoredAtom2756 chi ∧
      ¬Fin15AnchoredAtom2766 chi ∧
      ¬Fin15AnchoredAtom2776 chi ∧
      ¬Fin15AnchoredAtom2796 chi ∧
      ¬Fin15AnchoredAtom4390 chi ∧
      ¬Fin15AnchoredAtom4394 chi ∧
      ¬Fin15AnchoredAtom4395 chi ∧
      ¬Fin15AnchoredAtom4399 chi ∧
      ¬Fin15AnchoredAtom4400 chi ∧
      ¬Fin15AnchoredAtom4410 chi ∧
      ¬Fin15AnchoredAtom4414 chi ∧
      ¬Fin15AnchoredAtom4415 chi ∧
      ¬Fin15AnchoredAtom4425 chi ∧
      ¬Fin15AnchoredAtom4435 chi ∧
      ¬Fin15AnchoredAtom4505 chi ∧
      ¬Fin15AnchoredAtom4506 chi ∧
      ¬Fin15AnchoredAtom4516 chi ∧
      ¬Fin15AnchoredAtom4526 chi ∧
      ¬Fin15AnchoredAtom4546 chi ∧
      ¬Fin15AnchoredAtom4631 chi ∧
      ¬Fin15AnchoredAtom4632 chi ∧
      ¬Fin15AnchoredAtom4642 chi ∧
      ¬Fin15AnchoredAtom4652 chi ∧
      ¬Fin15AnchoredAtom4672 chi ∧
      ¬Fin15AnchoredAtom4777 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 5, 7, 8, 9, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25521
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2500 Fin15AnchoredAtom2501 Fin15AnchoredAtom2505
    Fin15AnchoredAtom2506 Fin15AnchoredAtom2507 Fin15AnchoredAtom2511 Fin15AnchoredAtom2512
    Fin15AnchoredAtom2516 Fin15AnchoredAtom2517 Fin15AnchoredAtom2527 Fin15AnchoredAtom2556
    Fin15AnchoredAtom2560 Fin15AnchoredAtom2561 Fin15AnchoredAtom2565 Fin15AnchoredAtom2566
    Fin15AnchoredAtom2576 Fin15AnchoredAtom2580 Fin15AnchoredAtom2581 Fin15AnchoredAtom2591
    Fin15AnchoredAtom2601 Fin15AnchoredAtom2640 Fin15AnchoredAtom2644 Fin15AnchoredAtom2645
    Fin15AnchoredAtom2649 Fin15AnchoredAtom2650 Fin15AnchoredAtom2660 Fin15AnchoredAtom2664
    Fin15AnchoredAtom2665 Fin15AnchoredAtom2675 Fin15AnchoredAtom2685 Fin15AnchoredAtom2755
    Fin15AnchoredAtom2756 Fin15AnchoredAtom2766 Fin15AnchoredAtom2776 Fin15AnchoredAtom2796
    Fin15AnchoredAtom4390 Fin15AnchoredAtom4394 Fin15AnchoredAtom4395 Fin15AnchoredAtom4399
    Fin15AnchoredAtom4400 Fin15AnchoredAtom4410 Fin15AnchoredAtom4414 Fin15AnchoredAtom4415
    Fin15AnchoredAtom4425 Fin15AnchoredAtom4435 Fin15AnchoredAtom4505 Fin15AnchoredAtom4506
    Fin15AnchoredAtom4516 Fin15AnchoredAtom4526 Fin15AnchoredAtom4546 Fin15AnchoredAtom4631
    Fin15AnchoredAtom4632 Fin15AnchoredAtom4642 Fin15AnchoredAtom4652 Fin15AnchoredAtom4672
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

theorem fin15Anchored_clause31558 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2500 chi ∧
      ¬Fin15AnchoredAtom2502 chi ∧
      ¬Fin15AnchoredAtom2504 chi ∧
      ¬Fin15AnchoredAtom2506 chi ∧
      ¬Fin15AnchoredAtom2508 chi ∧
      ¬Fin15AnchoredAtom2510 chi ∧
      ¬Fin15AnchoredAtom2512 chi ∧
      ¬Fin15AnchoredAtom2519 chi ∧
      ¬Fin15AnchoredAtom2521 chi ∧
      ¬Fin15AnchoredAtom2526 chi ∧
      ¬Fin15AnchoredAtom2557 chi ∧
      ¬Fin15AnchoredAtom2559 chi ∧
      ¬Fin15AnchoredAtom2561 chi ∧
      ¬Fin15AnchoredAtom2568 chi ∧
      ¬Fin15AnchoredAtom2570 chi ∧
      ¬Fin15AnchoredAtom2575 chi ∧
      ¬Fin15AnchoredAtom2583 chi ∧
      ¬Fin15AnchoredAtom2585 chi ∧
      ¬Fin15AnchoredAtom2590 chi ∧
      ¬Fin15AnchoredAtom2606 chi ∧
      ¬Fin15AnchoredAtom2641 chi ∧
      ¬Fin15AnchoredAtom2643 chi ∧
      ¬Fin15AnchoredAtom2645 chi ∧
      ¬Fin15AnchoredAtom2652 chi ∧
      ¬Fin15AnchoredAtom2654 chi ∧
      ¬Fin15AnchoredAtom2659 chi ∧
      ¬Fin15AnchoredAtom2667 chi ∧
      ¬Fin15AnchoredAtom2669 chi ∧
      ¬Fin15AnchoredAtom2674 chi ∧
      ¬Fin15AnchoredAtom2690 chi ∧
      ¬Fin15AnchoredAtom2758 chi ∧
      ¬Fin15AnchoredAtom2760 chi ∧
      ¬Fin15AnchoredAtom2765 chi ∧
      ¬Fin15AnchoredAtom2781 chi ∧
      ¬Fin15AnchoredAtom2801 chi ∧
      ¬Fin15AnchoredAtom4391 chi ∧
      ¬Fin15AnchoredAtom4393 chi ∧
      ¬Fin15AnchoredAtom4395 chi ∧
      ¬Fin15AnchoredAtom4402 chi ∧
      ¬Fin15AnchoredAtom4404 chi ∧
      ¬Fin15AnchoredAtom4409 chi ∧
      ¬Fin15AnchoredAtom4417 chi ∧
      ¬Fin15AnchoredAtom4419 chi ∧
      ¬Fin15AnchoredAtom4424 chi ∧
      ¬Fin15AnchoredAtom4440 chi ∧
      ¬Fin15AnchoredAtom4508 chi ∧
      ¬Fin15AnchoredAtom4510 chi ∧
      ¬Fin15AnchoredAtom4515 chi ∧
      ¬Fin15AnchoredAtom4531 chi ∧
      ¬Fin15AnchoredAtom4551 chi ∧
      ¬Fin15AnchoredAtom4634 chi ∧
      ¬Fin15AnchoredAtom4636 chi ∧
      ¬Fin15AnchoredAtom4641 chi ∧
      ¬Fin15AnchoredAtom4657 chi ∧
      ¬Fin15AnchoredAtom4677 chi ∧
      ¬Fin15AnchoredAtom4782 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 5, 7, 8, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21937
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2500 Fin15AnchoredAtom2502 Fin15AnchoredAtom2504
    Fin15AnchoredAtom2506 Fin15AnchoredAtom2508 Fin15AnchoredAtom2510 Fin15AnchoredAtom2512
    Fin15AnchoredAtom2519 Fin15AnchoredAtom2521 Fin15AnchoredAtom2526 Fin15AnchoredAtom2557
    Fin15AnchoredAtom2559 Fin15AnchoredAtom2561 Fin15AnchoredAtom2568 Fin15AnchoredAtom2570
    Fin15AnchoredAtom2575 Fin15AnchoredAtom2583 Fin15AnchoredAtom2585 Fin15AnchoredAtom2590
    Fin15AnchoredAtom2606 Fin15AnchoredAtom2641 Fin15AnchoredAtom2643 Fin15AnchoredAtom2645
    Fin15AnchoredAtom2652 Fin15AnchoredAtom2654 Fin15AnchoredAtom2659 Fin15AnchoredAtom2667
    Fin15AnchoredAtom2669 Fin15AnchoredAtom2674 Fin15AnchoredAtom2690 Fin15AnchoredAtom2758
    Fin15AnchoredAtom2760 Fin15AnchoredAtom2765 Fin15AnchoredAtom2781 Fin15AnchoredAtom2801
    Fin15AnchoredAtom4391 Fin15AnchoredAtom4393 Fin15AnchoredAtom4395 Fin15AnchoredAtom4402
    Fin15AnchoredAtom4404 Fin15AnchoredAtom4409 Fin15AnchoredAtom4417 Fin15AnchoredAtom4419
    Fin15AnchoredAtom4424 Fin15AnchoredAtom4440 Fin15AnchoredAtom4508 Fin15AnchoredAtom4510
    Fin15AnchoredAtom4515 Fin15AnchoredAtom4531 Fin15AnchoredAtom4551 Fin15AnchoredAtom4634
    Fin15AnchoredAtom4636 Fin15AnchoredAtom4641 Fin15AnchoredAtom4657 Fin15AnchoredAtom4677
    Fin15AnchoredAtom4782 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31559 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2501 chi ∧
      ¬Fin15AnchoredAtom2502 chi ∧
      ¬Fin15AnchoredAtom2504 chi ∧
      ¬Fin15AnchoredAtom2505 chi ∧
      ¬Fin15AnchoredAtom2513 chi ∧
      ¬Fin15AnchoredAtom2515 chi ∧
      ¬Fin15AnchoredAtom2516 chi ∧
      ¬Fin15AnchoredAtom2519 chi ∧
      ¬Fin15AnchoredAtom2520 chi ∧
      ¬Fin15AnchoredAtom2525 chi ∧
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
      ¬Fin15AnchoredAtom4396 chi ∧
      ¬Fin15AnchoredAtom4398 chi ∧
      ¬Fin15AnchoredAtom4399 chi ∧
      ¬Fin15AnchoredAtom4402 chi ∧
      ¬Fin15AnchoredAtom4403 chi ∧
      ¬Fin15AnchoredAtom4408 chi ∧
      ¬Fin15AnchoredAtom4427 chi ∧
      ¬Fin15AnchoredAtom4428 chi ∧
      ¬Fin15AnchoredAtom4433 chi ∧
      ¬Fin15AnchoredAtom4439 chi ∧
      ¬Fin15AnchoredAtom4518 chi ∧
      ¬Fin15AnchoredAtom4519 chi ∧
      ¬Fin15AnchoredAtom4524 chi ∧
      ¬Fin15AnchoredAtom4530 chi ∧
      ¬Fin15AnchoredAtom4560 chi ∧
      ¬Fin15AnchoredAtom4644 chi ∧
      ¬Fin15AnchoredAtom4645 chi ∧
      ¬Fin15AnchoredAtom4650 chi ∧
      ¬Fin15AnchoredAtom4656 chi ∧
      ¬Fin15AnchoredAtom4686 chi ∧
      ¬Fin15AnchoredAtom4791 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 5, 7, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask14001
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2501 Fin15AnchoredAtom2502 Fin15AnchoredAtom2504
    Fin15AnchoredAtom2505 Fin15AnchoredAtom2513 Fin15AnchoredAtom2515 Fin15AnchoredAtom2516
    Fin15AnchoredAtom2519 Fin15AnchoredAtom2520 Fin15AnchoredAtom2525 Fin15AnchoredAtom2562
    Fin15AnchoredAtom2564 Fin15AnchoredAtom2565 Fin15AnchoredAtom2568 Fin15AnchoredAtom2569
    Fin15AnchoredAtom2574 Fin15AnchoredAtom2593 Fin15AnchoredAtom2594 Fin15AnchoredAtom2599
    Fin15AnchoredAtom2605 Fin15AnchoredAtom2646 Fin15AnchoredAtom2648 Fin15AnchoredAtom2649
    Fin15AnchoredAtom2652 Fin15AnchoredAtom2653 Fin15AnchoredAtom2658 Fin15AnchoredAtom2677
    Fin15AnchoredAtom2678 Fin15AnchoredAtom2683 Fin15AnchoredAtom2689 Fin15AnchoredAtom2768
    Fin15AnchoredAtom2769 Fin15AnchoredAtom2774 Fin15AnchoredAtom2780 Fin15AnchoredAtom2810
    Fin15AnchoredAtom4396 Fin15AnchoredAtom4398 Fin15AnchoredAtom4399 Fin15AnchoredAtom4402
    Fin15AnchoredAtom4403 Fin15AnchoredAtom4408 Fin15AnchoredAtom4427 Fin15AnchoredAtom4428
    Fin15AnchoredAtom4433 Fin15AnchoredAtom4439 Fin15AnchoredAtom4518 Fin15AnchoredAtom4519
    Fin15AnchoredAtom4524 Fin15AnchoredAtom4530 Fin15AnchoredAtom4560 Fin15AnchoredAtom4644
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

theorem fin15Anchored_clause31560 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2501 chi ∧
      ¬Fin15AnchoredAtom2502 chi ∧
      ¬Fin15AnchoredAtom2504 chi ∧
      ¬Fin15AnchoredAtom2506 chi ∧
      ¬Fin15AnchoredAtom2513 chi ∧
      ¬Fin15AnchoredAtom2515 chi ∧
      ¬Fin15AnchoredAtom2517 chi ∧
      ¬Fin15AnchoredAtom2519 chi ∧
      ¬Fin15AnchoredAtom2521 chi ∧
      ¬Fin15AnchoredAtom2526 chi ∧
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
      ¬Fin15AnchoredAtom4396 chi ∧
      ¬Fin15AnchoredAtom4398 chi ∧
      ¬Fin15AnchoredAtom4400 chi ∧
      ¬Fin15AnchoredAtom4402 chi ∧
      ¬Fin15AnchoredAtom4404 chi ∧
      ¬Fin15AnchoredAtom4409 chi ∧
      ¬Fin15AnchoredAtom4427 chi ∧
      ¬Fin15AnchoredAtom4429 chi ∧
      ¬Fin15AnchoredAtom4434 chi ∧
      ¬Fin15AnchoredAtom4440 chi ∧
      ¬Fin15AnchoredAtom4518 chi ∧
      ¬Fin15AnchoredAtom4520 chi ∧
      ¬Fin15AnchoredAtom4525 chi ∧
      ¬Fin15AnchoredAtom4531 chi ∧
      ¬Fin15AnchoredAtom4561 chi ∧
      ¬Fin15AnchoredAtom4644 chi ∧
      ¬Fin15AnchoredAtom4646 chi ∧
      ¬Fin15AnchoredAtom4651 chi ∧
      ¬Fin15AnchoredAtom4657 chi ∧
      ¬Fin15AnchoredAtom4687 chi ∧
      ¬Fin15AnchoredAtom4792 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 5, 7, 9, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22193
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2501 Fin15AnchoredAtom2502 Fin15AnchoredAtom2504
    Fin15AnchoredAtom2506 Fin15AnchoredAtom2513 Fin15AnchoredAtom2515 Fin15AnchoredAtom2517
    Fin15AnchoredAtom2519 Fin15AnchoredAtom2521 Fin15AnchoredAtom2526 Fin15AnchoredAtom2562
    Fin15AnchoredAtom2564 Fin15AnchoredAtom2566 Fin15AnchoredAtom2568 Fin15AnchoredAtom2570
    Fin15AnchoredAtom2575 Fin15AnchoredAtom2593 Fin15AnchoredAtom2595 Fin15AnchoredAtom2600
    Fin15AnchoredAtom2606 Fin15AnchoredAtom2646 Fin15AnchoredAtom2648 Fin15AnchoredAtom2650
    Fin15AnchoredAtom2652 Fin15AnchoredAtom2654 Fin15AnchoredAtom2659 Fin15AnchoredAtom2677
    Fin15AnchoredAtom2679 Fin15AnchoredAtom2684 Fin15AnchoredAtom2690 Fin15AnchoredAtom2768
    Fin15AnchoredAtom2770 Fin15AnchoredAtom2775 Fin15AnchoredAtom2781 Fin15AnchoredAtom2811
    Fin15AnchoredAtom4396 Fin15AnchoredAtom4398 Fin15AnchoredAtom4400 Fin15AnchoredAtom4402
    Fin15AnchoredAtom4404 Fin15AnchoredAtom4409 Fin15AnchoredAtom4427 Fin15AnchoredAtom4429
    Fin15AnchoredAtom4434 Fin15AnchoredAtom4440 Fin15AnchoredAtom4518 Fin15AnchoredAtom4520
    Fin15AnchoredAtom4525 Fin15AnchoredAtom4531 Fin15AnchoredAtom4561 Fin15AnchoredAtom4644
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

theorem fin15Anchored_clause31561 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2501 chi ∧
      ¬Fin15AnchoredAtom2502 chi ∧
      ¬Fin15AnchoredAtom2505 chi ∧
      ¬Fin15AnchoredAtom2506 chi ∧
      ¬Fin15AnchoredAtom2513 chi ∧
      ¬Fin15AnchoredAtom2516 chi ∧
      ¬Fin15AnchoredAtom2517 chi ∧
      ¬Fin15AnchoredAtom2520 chi ∧
      ¬Fin15AnchoredAtom2521 chi ∧
      ¬Fin15AnchoredAtom2527 chi ∧
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
      ¬Fin15AnchoredAtom4396 chi ∧
      ¬Fin15AnchoredAtom4399 chi ∧
      ¬Fin15AnchoredAtom4400 chi ∧
      ¬Fin15AnchoredAtom4403 chi ∧
      ¬Fin15AnchoredAtom4404 chi ∧
      ¬Fin15AnchoredAtom4410 chi ∧
      ¬Fin15AnchoredAtom4428 chi ∧
      ¬Fin15AnchoredAtom4429 chi ∧
      ¬Fin15AnchoredAtom4435 chi ∧
      ¬Fin15AnchoredAtom4441 chi ∧
      ¬Fin15AnchoredAtom4519 chi ∧
      ¬Fin15AnchoredAtom4520 chi ∧
      ¬Fin15AnchoredAtom4526 chi ∧
      ¬Fin15AnchoredAtom4532 chi ∧
      ¬Fin15AnchoredAtom4562 chi ∧
      ¬Fin15AnchoredAtom4645 chi ∧
      ¬Fin15AnchoredAtom4646 chi ∧
      ¬Fin15AnchoredAtom4652 chi ∧
      ¬Fin15AnchoredAtom4658 chi ∧
      ¬Fin15AnchoredAtom4688 chi ∧
      ¬Fin15AnchoredAtom4793 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 5, 7, 9, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26289
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2501 Fin15AnchoredAtom2502 Fin15AnchoredAtom2505
    Fin15AnchoredAtom2506 Fin15AnchoredAtom2513 Fin15AnchoredAtom2516 Fin15AnchoredAtom2517
    Fin15AnchoredAtom2520 Fin15AnchoredAtom2521 Fin15AnchoredAtom2527 Fin15AnchoredAtom2562
    Fin15AnchoredAtom2565 Fin15AnchoredAtom2566 Fin15AnchoredAtom2569 Fin15AnchoredAtom2570
    Fin15AnchoredAtom2576 Fin15AnchoredAtom2594 Fin15AnchoredAtom2595 Fin15AnchoredAtom2601
    Fin15AnchoredAtom2607 Fin15AnchoredAtom2646 Fin15AnchoredAtom2649 Fin15AnchoredAtom2650
    Fin15AnchoredAtom2653 Fin15AnchoredAtom2654 Fin15AnchoredAtom2660 Fin15AnchoredAtom2678
    Fin15AnchoredAtom2679 Fin15AnchoredAtom2685 Fin15AnchoredAtom2691 Fin15AnchoredAtom2769
    Fin15AnchoredAtom2770 Fin15AnchoredAtom2776 Fin15AnchoredAtom2782 Fin15AnchoredAtom2812
    Fin15AnchoredAtom4396 Fin15AnchoredAtom4399 Fin15AnchoredAtom4400 Fin15AnchoredAtom4403
    Fin15AnchoredAtom4404 Fin15AnchoredAtom4410 Fin15AnchoredAtom4428 Fin15AnchoredAtom4429
    Fin15AnchoredAtom4435 Fin15AnchoredAtom4441 Fin15AnchoredAtom4519 Fin15AnchoredAtom4520
    Fin15AnchoredAtom4526 Fin15AnchoredAtom4532 Fin15AnchoredAtom4562 Fin15AnchoredAtom4645
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

theorem fin15Anchored_clause31562 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2501 chi ∧
      ¬Fin15AnchoredAtom2504 chi ∧
      ¬Fin15AnchoredAtom2505 chi ∧
      ¬Fin15AnchoredAtom2506 chi ∧
      ¬Fin15AnchoredAtom2515 chi ∧
      ¬Fin15AnchoredAtom2516 chi ∧
      ¬Fin15AnchoredAtom2517 chi ∧
      ¬Fin15AnchoredAtom2525 chi ∧
      ¬Fin15AnchoredAtom2526 chi ∧
      ¬Fin15AnchoredAtom2527 chi ∧
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
      ¬Fin15AnchoredAtom4398 chi ∧
      ¬Fin15AnchoredAtom4399 chi ∧
      ¬Fin15AnchoredAtom4400 chi ∧
      ¬Fin15AnchoredAtom4408 chi ∧
      ¬Fin15AnchoredAtom4409 chi ∧
      ¬Fin15AnchoredAtom4410 chi ∧
      ¬Fin15AnchoredAtom4433 chi ∧
      ¬Fin15AnchoredAtom4434 chi ∧
      ¬Fin15AnchoredAtom4435 chi ∧
      ¬Fin15AnchoredAtom4445 chi ∧
      ¬Fin15AnchoredAtom4524 chi ∧
      ¬Fin15AnchoredAtom4525 chi ∧
      ¬Fin15AnchoredAtom4526 chi ∧
      ¬Fin15AnchoredAtom4536 chi ∧
      ¬Fin15AnchoredAtom4566 chi ∧
      ¬Fin15AnchoredAtom4650 chi ∧
      ¬Fin15AnchoredAtom4651 chi ∧
      ¬Fin15AnchoredAtom4652 chi ∧
      ¬Fin15AnchoredAtom4662 chi ∧
      ¬Fin15AnchoredAtom4692 chi ∧
      ¬Fin15AnchoredAtom4797 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 5, 7, 9, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29361
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2501 Fin15AnchoredAtom2504 Fin15AnchoredAtom2505
    Fin15AnchoredAtom2506 Fin15AnchoredAtom2515 Fin15AnchoredAtom2516 Fin15AnchoredAtom2517
    Fin15AnchoredAtom2525 Fin15AnchoredAtom2526 Fin15AnchoredAtom2527 Fin15AnchoredAtom2564
    Fin15AnchoredAtom2565 Fin15AnchoredAtom2566 Fin15AnchoredAtom2574 Fin15AnchoredAtom2575
    Fin15AnchoredAtom2576 Fin15AnchoredAtom2599 Fin15AnchoredAtom2600 Fin15AnchoredAtom2601
    Fin15AnchoredAtom2611 Fin15AnchoredAtom2648 Fin15AnchoredAtom2649 Fin15AnchoredAtom2650
    Fin15AnchoredAtom2658 Fin15AnchoredAtom2659 Fin15AnchoredAtom2660 Fin15AnchoredAtom2683
    Fin15AnchoredAtom2684 Fin15AnchoredAtom2685 Fin15AnchoredAtom2695 Fin15AnchoredAtom2774
    Fin15AnchoredAtom2775 Fin15AnchoredAtom2776 Fin15AnchoredAtom2786 Fin15AnchoredAtom2816
    Fin15AnchoredAtom4398 Fin15AnchoredAtom4399 Fin15AnchoredAtom4400 Fin15AnchoredAtom4408
    Fin15AnchoredAtom4409 Fin15AnchoredAtom4410 Fin15AnchoredAtom4433 Fin15AnchoredAtom4434
    Fin15AnchoredAtom4435 Fin15AnchoredAtom4445 Fin15AnchoredAtom4524 Fin15AnchoredAtom4525
    Fin15AnchoredAtom4526 Fin15AnchoredAtom4536 Fin15AnchoredAtom4566 Fin15AnchoredAtom4650
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

theorem fin15Anchored_clause31563 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2502 chi ∧
      ¬Fin15AnchoredAtom2504 chi ∧
      ¬Fin15AnchoredAtom2505 chi ∧
      ¬Fin15AnchoredAtom2506 chi ∧
      ¬Fin15AnchoredAtom2519 chi ∧
      ¬Fin15AnchoredAtom2520 chi ∧
      ¬Fin15AnchoredAtom2521 chi ∧
      ¬Fin15AnchoredAtom2525 chi ∧
      ¬Fin15AnchoredAtom2526 chi ∧
      ¬Fin15AnchoredAtom2527 chi ∧
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
      ¬Fin15AnchoredAtom4402 chi ∧
      ¬Fin15AnchoredAtom4403 chi ∧
      ¬Fin15AnchoredAtom4404 chi ∧
      ¬Fin15AnchoredAtom4408 chi ∧
      ¬Fin15AnchoredAtom4409 chi ∧
      ¬Fin15AnchoredAtom4410 chi ∧
      ¬Fin15AnchoredAtom4439 chi ∧
      ¬Fin15AnchoredAtom4440 chi ∧
      ¬Fin15AnchoredAtom4441 chi ∧
      ¬Fin15AnchoredAtom4445 chi ∧
      ¬Fin15AnchoredAtom4530 chi ∧
      ¬Fin15AnchoredAtom4531 chi ∧
      ¬Fin15AnchoredAtom4532 chi ∧
      ¬Fin15AnchoredAtom4536 chi ∧
      ¬Fin15AnchoredAtom4570 chi ∧
      ¬Fin15AnchoredAtom4656 chi ∧
      ¬Fin15AnchoredAtom4657 chi ∧
      ¬Fin15AnchoredAtom4658 chi ∧
      ¬Fin15AnchoredAtom4662 chi ∧
      ¬Fin15AnchoredAtom4696 chi ∧
      ¬Fin15AnchoredAtom4801 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 5, 7, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29873
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2502 Fin15AnchoredAtom2504 Fin15AnchoredAtom2505
    Fin15AnchoredAtom2506 Fin15AnchoredAtom2519 Fin15AnchoredAtom2520 Fin15AnchoredAtom2521
    Fin15AnchoredAtom2525 Fin15AnchoredAtom2526 Fin15AnchoredAtom2527 Fin15AnchoredAtom2568
    Fin15AnchoredAtom2569 Fin15AnchoredAtom2570 Fin15AnchoredAtom2574 Fin15AnchoredAtom2575
    Fin15AnchoredAtom2576 Fin15AnchoredAtom2605 Fin15AnchoredAtom2606 Fin15AnchoredAtom2607
    Fin15AnchoredAtom2611 Fin15AnchoredAtom2652 Fin15AnchoredAtom2653 Fin15AnchoredAtom2654
    Fin15AnchoredAtom2658 Fin15AnchoredAtom2659 Fin15AnchoredAtom2660 Fin15AnchoredAtom2689
    Fin15AnchoredAtom2690 Fin15AnchoredAtom2691 Fin15AnchoredAtom2695 Fin15AnchoredAtom2780
    Fin15AnchoredAtom2781 Fin15AnchoredAtom2782 Fin15AnchoredAtom2786 Fin15AnchoredAtom2820
    Fin15AnchoredAtom4402 Fin15AnchoredAtom4403 Fin15AnchoredAtom4404 Fin15AnchoredAtom4408
    Fin15AnchoredAtom4409 Fin15AnchoredAtom4410 Fin15AnchoredAtom4439 Fin15AnchoredAtom4440
    Fin15AnchoredAtom4441 Fin15AnchoredAtom4445 Fin15AnchoredAtom4530 Fin15AnchoredAtom4531
    Fin15AnchoredAtom4532 Fin15AnchoredAtom4536 Fin15AnchoredAtom4570 Fin15AnchoredAtom4656
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

theorem fin15Anchored_clause31564 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2507 chi ∧
      ¬Fin15AnchoredAtom2508 chi ∧
      ¬Fin15AnchoredAtom2510 chi ∧
      ¬Fin15AnchoredAtom2511 chi ∧
      ¬Fin15AnchoredAtom2513 chi ∧
      ¬Fin15AnchoredAtom2515 chi ∧
      ¬Fin15AnchoredAtom2516 chi ∧
      ¬Fin15AnchoredAtom2519 chi ∧
      ¬Fin15AnchoredAtom2520 chi ∧
      ¬Fin15AnchoredAtom2525 chi ∧
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
      ¬Fin15AnchoredAtom2661 chi ∧
      ¬Fin15AnchoredAtom2663 chi ∧
      ¬Fin15AnchoredAtom2664 chi ∧
      ¬Fin15AnchoredAtom2667 chi ∧
      ¬Fin15AnchoredAtom2668 chi ∧
      ¬Fin15AnchoredAtom2673 chi ∧
      ¬Fin15AnchoredAtom2677 chi ∧
      ¬Fin15AnchoredAtom2678 chi ∧
      ¬Fin15AnchoredAtom2683 chi ∧
      ¬Fin15AnchoredAtom2689 chi ∧
      ¬Fin15AnchoredAtom2788 chi ∧
      ¬Fin15AnchoredAtom2789 chi ∧
      ¬Fin15AnchoredAtom2794 chi ∧
      ¬Fin15AnchoredAtom2800 chi ∧
      ¬Fin15AnchoredAtom2810 chi ∧
      ¬Fin15AnchoredAtom4411 chi ∧
      ¬Fin15AnchoredAtom4413 chi ∧
      ¬Fin15AnchoredAtom4414 chi ∧
      ¬Fin15AnchoredAtom4417 chi ∧
      ¬Fin15AnchoredAtom4418 chi ∧
      ¬Fin15AnchoredAtom4423 chi ∧
      ¬Fin15AnchoredAtom4427 chi ∧
      ¬Fin15AnchoredAtom4428 chi ∧
      ¬Fin15AnchoredAtom4433 chi ∧
      ¬Fin15AnchoredAtom4439 chi ∧
      ¬Fin15AnchoredAtom4538 chi ∧
      ¬Fin15AnchoredAtom4539 chi ∧
      ¬Fin15AnchoredAtom4544 chi ∧
      ¬Fin15AnchoredAtom4550 chi ∧
      ¬Fin15AnchoredAtom4560 chi ∧
      ¬Fin15AnchoredAtom4664 chi ∧
      ¬Fin15AnchoredAtom4665 chi ∧
      ¬Fin15AnchoredAtom4670 chi ∧
      ¬Fin15AnchoredAtom4676 chi ∧
      ¬Fin15AnchoredAtom4686 chi ∧
      ¬Fin15AnchoredAtom4806 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 5, 8, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask14129
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2507 Fin15AnchoredAtom2508 Fin15AnchoredAtom2510
    Fin15AnchoredAtom2511 Fin15AnchoredAtom2513 Fin15AnchoredAtom2515 Fin15AnchoredAtom2516
    Fin15AnchoredAtom2519 Fin15AnchoredAtom2520 Fin15AnchoredAtom2525 Fin15AnchoredAtom2577
    Fin15AnchoredAtom2579 Fin15AnchoredAtom2580 Fin15AnchoredAtom2583 Fin15AnchoredAtom2584
    Fin15AnchoredAtom2589 Fin15AnchoredAtom2593 Fin15AnchoredAtom2594 Fin15AnchoredAtom2599
    Fin15AnchoredAtom2605 Fin15AnchoredAtom2661 Fin15AnchoredAtom2663 Fin15AnchoredAtom2664
    Fin15AnchoredAtom2667 Fin15AnchoredAtom2668 Fin15AnchoredAtom2673 Fin15AnchoredAtom2677
    Fin15AnchoredAtom2678 Fin15AnchoredAtom2683 Fin15AnchoredAtom2689 Fin15AnchoredAtom2788
    Fin15AnchoredAtom2789 Fin15AnchoredAtom2794 Fin15AnchoredAtom2800 Fin15AnchoredAtom2810
    Fin15AnchoredAtom4411 Fin15AnchoredAtom4413 Fin15AnchoredAtom4414 Fin15AnchoredAtom4417
    Fin15AnchoredAtom4418 Fin15AnchoredAtom4423 Fin15AnchoredAtom4427 Fin15AnchoredAtom4428
    Fin15AnchoredAtom4433 Fin15AnchoredAtom4439 Fin15AnchoredAtom4538 Fin15AnchoredAtom4539
    Fin15AnchoredAtom4544 Fin15AnchoredAtom4550 Fin15AnchoredAtom4560 Fin15AnchoredAtom4664
    Fin15AnchoredAtom4665 Fin15AnchoredAtom4670 Fin15AnchoredAtom4676 Fin15AnchoredAtom4686
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

theorem fin15Anchored_clause31565 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2507 chi ∧
      ¬Fin15AnchoredAtom2508 chi ∧
      ¬Fin15AnchoredAtom2511 chi ∧
      ¬Fin15AnchoredAtom2512 chi ∧
      ¬Fin15AnchoredAtom2513 chi ∧
      ¬Fin15AnchoredAtom2516 chi ∧
      ¬Fin15AnchoredAtom2517 chi ∧
      ¬Fin15AnchoredAtom2520 chi ∧
      ¬Fin15AnchoredAtom2521 chi ∧
      ¬Fin15AnchoredAtom2527 chi ∧
      ¬Fin15AnchoredAtom2577 chi ∧
      ¬Fin15AnchoredAtom2580 chi ∧
      ¬Fin15AnchoredAtom2581 chi ∧
      ¬Fin15AnchoredAtom2584 chi ∧
      ¬Fin15AnchoredAtom2585 chi ∧
      ¬Fin15AnchoredAtom2591 chi ∧
      ¬Fin15AnchoredAtom2594 chi ∧
      ¬Fin15AnchoredAtom2595 chi ∧
      ¬Fin15AnchoredAtom2601 chi ∧
      ¬Fin15AnchoredAtom2607 chi ∧
      ¬Fin15AnchoredAtom2661 chi ∧
      ¬Fin15AnchoredAtom2664 chi ∧
      ¬Fin15AnchoredAtom2665 chi ∧
      ¬Fin15AnchoredAtom2668 chi ∧
      ¬Fin15AnchoredAtom2669 chi ∧
      ¬Fin15AnchoredAtom2675 chi ∧
      ¬Fin15AnchoredAtom2678 chi ∧
      ¬Fin15AnchoredAtom2679 chi ∧
      ¬Fin15AnchoredAtom2685 chi ∧
      ¬Fin15AnchoredAtom2691 chi ∧
      ¬Fin15AnchoredAtom2789 chi ∧
      ¬Fin15AnchoredAtom2790 chi ∧
      ¬Fin15AnchoredAtom2796 chi ∧
      ¬Fin15AnchoredAtom2802 chi ∧
      ¬Fin15AnchoredAtom2812 chi ∧
      ¬Fin15AnchoredAtom4411 chi ∧
      ¬Fin15AnchoredAtom4414 chi ∧
      ¬Fin15AnchoredAtom4415 chi ∧
      ¬Fin15AnchoredAtom4418 chi ∧
      ¬Fin15AnchoredAtom4419 chi ∧
      ¬Fin15AnchoredAtom4425 chi ∧
      ¬Fin15AnchoredAtom4428 chi ∧
      ¬Fin15AnchoredAtom4429 chi ∧
      ¬Fin15AnchoredAtom4435 chi ∧
      ¬Fin15AnchoredAtom4441 chi ∧
      ¬Fin15AnchoredAtom4539 chi ∧
      ¬Fin15AnchoredAtom4540 chi ∧
      ¬Fin15AnchoredAtom4546 chi ∧
      ¬Fin15AnchoredAtom4552 chi ∧
      ¬Fin15AnchoredAtom4562 chi ∧
      ¬Fin15AnchoredAtom4665 chi ∧
      ¬Fin15AnchoredAtom4666 chi ∧
      ¬Fin15AnchoredAtom4672 chi ∧
      ¬Fin15AnchoredAtom4678 chi ∧
      ¬Fin15AnchoredAtom4688 chi ∧
      ¬Fin15AnchoredAtom4808 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 5, 8, 9, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26417
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2507 Fin15AnchoredAtom2508 Fin15AnchoredAtom2511
    Fin15AnchoredAtom2512 Fin15AnchoredAtom2513 Fin15AnchoredAtom2516 Fin15AnchoredAtom2517
    Fin15AnchoredAtom2520 Fin15AnchoredAtom2521 Fin15AnchoredAtom2527 Fin15AnchoredAtom2577
    Fin15AnchoredAtom2580 Fin15AnchoredAtom2581 Fin15AnchoredAtom2584 Fin15AnchoredAtom2585
    Fin15AnchoredAtom2591 Fin15AnchoredAtom2594 Fin15AnchoredAtom2595 Fin15AnchoredAtom2601
    Fin15AnchoredAtom2607 Fin15AnchoredAtom2661 Fin15AnchoredAtom2664 Fin15AnchoredAtom2665
    Fin15AnchoredAtom2668 Fin15AnchoredAtom2669 Fin15AnchoredAtom2675 Fin15AnchoredAtom2678
    Fin15AnchoredAtom2679 Fin15AnchoredAtom2685 Fin15AnchoredAtom2691 Fin15AnchoredAtom2789
    Fin15AnchoredAtom2790 Fin15AnchoredAtom2796 Fin15AnchoredAtom2802 Fin15AnchoredAtom2812
    Fin15AnchoredAtom4411 Fin15AnchoredAtom4414 Fin15AnchoredAtom4415 Fin15AnchoredAtom4418
    Fin15AnchoredAtom4419 Fin15AnchoredAtom4425 Fin15AnchoredAtom4428 Fin15AnchoredAtom4429
    Fin15AnchoredAtom4435 Fin15AnchoredAtom4441 Fin15AnchoredAtom4539 Fin15AnchoredAtom4540
    Fin15AnchoredAtom4546 Fin15AnchoredAtom4552 Fin15AnchoredAtom4562 Fin15AnchoredAtom4665
    Fin15AnchoredAtom4666 Fin15AnchoredAtom4672 Fin15AnchoredAtom4678 Fin15AnchoredAtom4688
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

theorem fin15Anchored_clause31566 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2508 chi ∧
      ¬Fin15AnchoredAtom2510 chi ∧
      ¬Fin15AnchoredAtom2511 chi ∧
      ¬Fin15AnchoredAtom2512 chi ∧
      ¬Fin15AnchoredAtom2519 chi ∧
      ¬Fin15AnchoredAtom2520 chi ∧
      ¬Fin15AnchoredAtom2521 chi ∧
      ¬Fin15AnchoredAtom2525 chi ∧
      ¬Fin15AnchoredAtom2526 chi ∧
      ¬Fin15AnchoredAtom2527 chi ∧
      ¬Fin15AnchoredAtom2583 chi ∧
      ¬Fin15AnchoredAtom2584 chi ∧
      ¬Fin15AnchoredAtom2585 chi ∧
      ¬Fin15AnchoredAtom2589 chi ∧
      ¬Fin15AnchoredAtom2590 chi ∧
      ¬Fin15AnchoredAtom2591 chi ∧
      ¬Fin15AnchoredAtom2605 chi ∧
      ¬Fin15AnchoredAtom2606 chi ∧
      ¬Fin15AnchoredAtom2607 chi ∧
      ¬Fin15AnchoredAtom2611 chi ∧
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
      ¬Fin15AnchoredAtom4417 chi ∧
      ¬Fin15AnchoredAtom4418 chi ∧
      ¬Fin15AnchoredAtom4419 chi ∧
      ¬Fin15AnchoredAtom4423 chi ∧
      ¬Fin15AnchoredAtom4424 chi ∧
      ¬Fin15AnchoredAtom4425 chi ∧
      ¬Fin15AnchoredAtom4439 chi ∧
      ¬Fin15AnchoredAtom4440 chi ∧
      ¬Fin15AnchoredAtom4441 chi ∧
      ¬Fin15AnchoredAtom4445 chi ∧
      ¬Fin15AnchoredAtom4550 chi ∧
      ¬Fin15AnchoredAtom4551 chi ∧
      ¬Fin15AnchoredAtom4552 chi ∧
      ¬Fin15AnchoredAtom4556 chi ∧
      ¬Fin15AnchoredAtom4570 chi ∧
      ¬Fin15AnchoredAtom4676 chi ∧
      ¬Fin15AnchoredAtom4677 chi ∧
      ¬Fin15AnchoredAtom4678 chi ∧
      ¬Fin15AnchoredAtom4682 chi ∧
      ¬Fin15AnchoredAtom4696 chi ∧
      ¬Fin15AnchoredAtom4816 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 5, 8, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask30001
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2508 Fin15AnchoredAtom2510 Fin15AnchoredAtom2511
    Fin15AnchoredAtom2512 Fin15AnchoredAtom2519 Fin15AnchoredAtom2520 Fin15AnchoredAtom2521
    Fin15AnchoredAtom2525 Fin15AnchoredAtom2526 Fin15AnchoredAtom2527 Fin15AnchoredAtom2583
    Fin15AnchoredAtom2584 Fin15AnchoredAtom2585 Fin15AnchoredAtom2589 Fin15AnchoredAtom2590
    Fin15AnchoredAtom2591 Fin15AnchoredAtom2605 Fin15AnchoredAtom2606 Fin15AnchoredAtom2607
    Fin15AnchoredAtom2611 Fin15AnchoredAtom2667 Fin15AnchoredAtom2668 Fin15AnchoredAtom2669
    Fin15AnchoredAtom2673 Fin15AnchoredAtom2674 Fin15AnchoredAtom2675 Fin15AnchoredAtom2689
    Fin15AnchoredAtom2690 Fin15AnchoredAtom2691 Fin15AnchoredAtom2695 Fin15AnchoredAtom2800
    Fin15AnchoredAtom2801 Fin15AnchoredAtom2802 Fin15AnchoredAtom2806 Fin15AnchoredAtom2820
    Fin15AnchoredAtom4417 Fin15AnchoredAtom4418 Fin15AnchoredAtom4419 Fin15AnchoredAtom4423
    Fin15AnchoredAtom4424 Fin15AnchoredAtom4425 Fin15AnchoredAtom4439 Fin15AnchoredAtom4440
    Fin15AnchoredAtom4441 Fin15AnchoredAtom4445 Fin15AnchoredAtom4550 Fin15AnchoredAtom4551
    Fin15AnchoredAtom4552 Fin15AnchoredAtom4556 Fin15AnchoredAtom4570 Fin15AnchoredAtom4676
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

theorem fin15Anchored_clause31567 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2513 chi ∧
      ¬Fin15AnchoredAtom2515 chi ∧
      ¬Fin15AnchoredAtom2516 chi ∧
      ¬Fin15AnchoredAtom2517 chi ∧
      ¬Fin15AnchoredAtom2519 chi ∧
      ¬Fin15AnchoredAtom2520 chi ∧
      ¬Fin15AnchoredAtom2521 chi ∧
      ¬Fin15AnchoredAtom2525 chi ∧
      ¬Fin15AnchoredAtom2526 chi ∧
      ¬Fin15AnchoredAtom2527 chi ∧
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
      ¬Fin15AnchoredAtom4427 chi ∧
      ¬Fin15AnchoredAtom4428 chi ∧
      ¬Fin15AnchoredAtom4429 chi ∧
      ¬Fin15AnchoredAtom4433 chi ∧
      ¬Fin15AnchoredAtom4434 chi ∧
      ¬Fin15AnchoredAtom4435 chi ∧
      ¬Fin15AnchoredAtom4439 chi ∧
      ¬Fin15AnchoredAtom4440 chi ∧
      ¬Fin15AnchoredAtom4441 chi ∧
      ¬Fin15AnchoredAtom4445 chi ∧
      ¬Fin15AnchoredAtom4560 chi ∧
      ¬Fin15AnchoredAtom4561 chi ∧
      ¬Fin15AnchoredAtom4562 chi ∧
      ¬Fin15AnchoredAtom4566 chi ∧
      ¬Fin15AnchoredAtom4570 chi ∧
      ¬Fin15AnchoredAtom4686 chi ∧
      ¬Fin15AnchoredAtom4687 chi ∧
      ¬Fin15AnchoredAtom4688 chi ∧
      ¬Fin15AnchoredAtom4692 chi ∧
      ¬Fin15AnchoredAtom4696 chi ∧
      ¬Fin15AnchoredAtom4821 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 5, 9, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask30257
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2513 Fin15AnchoredAtom2515 Fin15AnchoredAtom2516
    Fin15AnchoredAtom2517 Fin15AnchoredAtom2519 Fin15AnchoredAtom2520 Fin15AnchoredAtom2521
    Fin15AnchoredAtom2525 Fin15AnchoredAtom2526 Fin15AnchoredAtom2527 Fin15AnchoredAtom2593
    Fin15AnchoredAtom2594 Fin15AnchoredAtom2595 Fin15AnchoredAtom2599 Fin15AnchoredAtom2600
    Fin15AnchoredAtom2601 Fin15AnchoredAtom2605 Fin15AnchoredAtom2606 Fin15AnchoredAtom2607
    Fin15AnchoredAtom2611 Fin15AnchoredAtom2677 Fin15AnchoredAtom2678 Fin15AnchoredAtom2679
    Fin15AnchoredAtom2683 Fin15AnchoredAtom2684 Fin15AnchoredAtom2685 Fin15AnchoredAtom2689
    Fin15AnchoredAtom2690 Fin15AnchoredAtom2691 Fin15AnchoredAtom2695 Fin15AnchoredAtom2810
    Fin15AnchoredAtom2811 Fin15AnchoredAtom2812 Fin15AnchoredAtom2816 Fin15AnchoredAtom2820
    Fin15AnchoredAtom4427 Fin15AnchoredAtom4428 Fin15AnchoredAtom4429 Fin15AnchoredAtom4433
    Fin15AnchoredAtom4434 Fin15AnchoredAtom4435 Fin15AnchoredAtom4439 Fin15AnchoredAtom4440
    Fin15AnchoredAtom4441 Fin15AnchoredAtom4445 Fin15AnchoredAtom4560 Fin15AnchoredAtom4561
    Fin15AnchoredAtom4562 Fin15AnchoredAtom4566 Fin15AnchoredAtom4570 Fin15AnchoredAtom4686
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

theorem fin15Anchored_clause31568 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2528 chi ∧
      ¬Fin15AnchoredAtom2529 chi ∧
      ¬Fin15AnchoredAtom2530 chi ∧
      ¬Fin15AnchoredAtom2532 chi ∧
      ¬Fin15AnchoredAtom2535 chi ∧
      ¬Fin15AnchoredAtom2536 chi ∧
      ¬Fin15AnchoredAtom2538 chi ∧
      ¬Fin15AnchoredAtom2541 chi ∧
      ¬Fin15AnchoredAtom2543 chi ∧
      ¬Fin15AnchoredAtom2547 chi ∧
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
      ¬Fin15AnchoredAtom4446 chi ∧
      ¬Fin15AnchoredAtom4447 chi ∧
      ¬Fin15AnchoredAtom4449 chi ∧
      ¬Fin15AnchoredAtom4452 chi ∧
      ¬Fin15AnchoredAtom4454 chi ∧
      ¬Fin15AnchoredAtom4458 chi ∧
      ¬Fin15AnchoredAtom4467 chi ∧
      ¬Fin15AnchoredAtom4469 chi ∧
      ¬Fin15AnchoredAtom4473 chi ∧
      ¬Fin15AnchoredAtom4483 chi ∧
      ¬Fin15AnchoredAtom4502 chi ∧
      ¬Fin15AnchoredAtom4504 chi ∧
      ¬Fin15AnchoredAtom4508 chi ∧
      ¬Fin15AnchoredAtom4518 chi ∧
      ¬Fin15AnchoredAtom4538 chi ∧
      ¬Fin15AnchoredAtom4698 chi ∧
      ¬Fin15AnchoredAtom4700 chi ∧
      ¬Fin15AnchoredAtom4704 chi ∧
      ¬Fin15AnchoredAtom4714 chi ∧
      ¬Fin15AnchoredAtom4734 chi ∧
      ¬Fin15AnchoredAtom4769 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 6, 7, 8, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask06097
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2528 Fin15AnchoredAtom2529 Fin15AnchoredAtom2530
    Fin15AnchoredAtom2532 Fin15AnchoredAtom2535 Fin15AnchoredAtom2536 Fin15AnchoredAtom2538
    Fin15AnchoredAtom2541 Fin15AnchoredAtom2543 Fin15AnchoredAtom2547 Fin15AnchoredAtom2556
    Fin15AnchoredAtom2557 Fin15AnchoredAtom2559 Fin15AnchoredAtom2562 Fin15AnchoredAtom2564
    Fin15AnchoredAtom2568 Fin15AnchoredAtom2577 Fin15AnchoredAtom2579 Fin15AnchoredAtom2583
    Fin15AnchoredAtom2593 Fin15AnchoredAtom2696 Fin15AnchoredAtom2697 Fin15AnchoredAtom2699
    Fin15AnchoredAtom2702 Fin15AnchoredAtom2704 Fin15AnchoredAtom2708 Fin15AnchoredAtom2717
    Fin15AnchoredAtom2719 Fin15AnchoredAtom2723 Fin15AnchoredAtom2733 Fin15AnchoredAtom2752
    Fin15AnchoredAtom2754 Fin15AnchoredAtom2758 Fin15AnchoredAtom2768 Fin15AnchoredAtom2788
    Fin15AnchoredAtom4446 Fin15AnchoredAtom4447 Fin15AnchoredAtom4449 Fin15AnchoredAtom4452
    Fin15AnchoredAtom4454 Fin15AnchoredAtom4458 Fin15AnchoredAtom4467 Fin15AnchoredAtom4469
    Fin15AnchoredAtom4473 Fin15AnchoredAtom4483 Fin15AnchoredAtom4502 Fin15AnchoredAtom4504
    Fin15AnchoredAtom4508 Fin15AnchoredAtom4518 Fin15AnchoredAtom4538 Fin15AnchoredAtom4698
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

theorem fin15Anchored_clause31569 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2528 chi ∧
      ¬Fin15AnchoredAtom2529 chi ∧
      ¬Fin15AnchoredAtom2530 chi ∧
      ¬Fin15AnchoredAtom2533 chi ∧
      ¬Fin15AnchoredAtom2535 chi ∧
      ¬Fin15AnchoredAtom2536 chi ∧
      ¬Fin15AnchoredAtom2539 chi ∧
      ¬Fin15AnchoredAtom2541 chi ∧
      ¬Fin15AnchoredAtom2544 chi ∧
      ¬Fin15AnchoredAtom2548 chi ∧
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
      ¬Fin15AnchoredAtom4446 chi ∧
      ¬Fin15AnchoredAtom4447 chi ∧
      ¬Fin15AnchoredAtom4450 chi ∧
      ¬Fin15AnchoredAtom4452 chi ∧
      ¬Fin15AnchoredAtom4455 chi ∧
      ¬Fin15AnchoredAtom4459 chi ∧
      ¬Fin15AnchoredAtom4467 chi ∧
      ¬Fin15AnchoredAtom4470 chi ∧
      ¬Fin15AnchoredAtom4474 chi ∧
      ¬Fin15AnchoredAtom4484 chi ∧
      ¬Fin15AnchoredAtom4502 chi ∧
      ¬Fin15AnchoredAtom4505 chi ∧
      ¬Fin15AnchoredAtom4509 chi ∧
      ¬Fin15AnchoredAtom4519 chi ∧
      ¬Fin15AnchoredAtom4539 chi ∧
      ¬Fin15AnchoredAtom4698 chi ∧
      ¬Fin15AnchoredAtom4701 chi ∧
      ¬Fin15AnchoredAtom4705 chi ∧
      ¬Fin15AnchoredAtom4715 chi ∧
      ¬Fin15AnchoredAtom4735 chi ∧
      ¬Fin15AnchoredAtom4770 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 6, 7, 8, 9, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask10193
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2528 Fin15AnchoredAtom2529 Fin15AnchoredAtom2530
    Fin15AnchoredAtom2533 Fin15AnchoredAtom2535 Fin15AnchoredAtom2536 Fin15AnchoredAtom2539
    Fin15AnchoredAtom2541 Fin15AnchoredAtom2544 Fin15AnchoredAtom2548 Fin15AnchoredAtom2556
    Fin15AnchoredAtom2557 Fin15AnchoredAtom2560 Fin15AnchoredAtom2562 Fin15AnchoredAtom2565
    Fin15AnchoredAtom2569 Fin15AnchoredAtom2577 Fin15AnchoredAtom2580 Fin15AnchoredAtom2584
    Fin15AnchoredAtom2594 Fin15AnchoredAtom2696 Fin15AnchoredAtom2697 Fin15AnchoredAtom2700
    Fin15AnchoredAtom2702 Fin15AnchoredAtom2705 Fin15AnchoredAtom2709 Fin15AnchoredAtom2717
    Fin15AnchoredAtom2720 Fin15AnchoredAtom2724 Fin15AnchoredAtom2734 Fin15AnchoredAtom2752
    Fin15AnchoredAtom2755 Fin15AnchoredAtom2759 Fin15AnchoredAtom2769 Fin15AnchoredAtom2789
    Fin15AnchoredAtom4446 Fin15AnchoredAtom4447 Fin15AnchoredAtom4450 Fin15AnchoredAtom4452
    Fin15AnchoredAtom4455 Fin15AnchoredAtom4459 Fin15AnchoredAtom4467 Fin15AnchoredAtom4470
    Fin15AnchoredAtom4474 Fin15AnchoredAtom4484 Fin15AnchoredAtom4502 Fin15AnchoredAtom4505
    Fin15AnchoredAtom4509 Fin15AnchoredAtom4519 Fin15AnchoredAtom4539 Fin15AnchoredAtom4698
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

theorem fin15Anchored_clause31570 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2528 chi ∧
      ¬Fin15AnchoredAtom2529 chi ∧
      ¬Fin15AnchoredAtom2530 chi ∧
      ¬Fin15AnchoredAtom2534 chi ∧
      ¬Fin15AnchoredAtom2535 chi ∧
      ¬Fin15AnchoredAtom2536 chi ∧
      ¬Fin15AnchoredAtom2540 chi ∧
      ¬Fin15AnchoredAtom2541 chi ∧
      ¬Fin15AnchoredAtom2545 chi ∧
      ¬Fin15AnchoredAtom2549 chi ∧
      ¬Fin15AnchoredAtom2556 chi ∧
      ¬Fin15AnchoredAtom2557 chi ∧
      ¬Fin15AnchoredAtom2561 chi ∧
      ¬Fin15AnchoredAtom2562 chi ∧
      ¬Fin15AnchoredAtom2566 chi ∧
      ¬Fin15AnchoredAtom2570 chi ∧
      ¬Fin15AnchoredAtom2577 chi ∧
      ¬Fin15AnchoredAtom2581 chi ∧
      ¬Fin15AnchoredAtom2585 chi ∧
      ¬Fin15AnchoredAtom2595 chi ∧
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
      ¬Fin15AnchoredAtom4446 chi ∧
      ¬Fin15AnchoredAtom4447 chi ∧
      ¬Fin15AnchoredAtom4451 chi ∧
      ¬Fin15AnchoredAtom4452 chi ∧
      ¬Fin15AnchoredAtom4456 chi ∧
      ¬Fin15AnchoredAtom4460 chi ∧
      ¬Fin15AnchoredAtom4467 chi ∧
      ¬Fin15AnchoredAtom4471 chi ∧
      ¬Fin15AnchoredAtom4475 chi ∧
      ¬Fin15AnchoredAtom4485 chi ∧
      ¬Fin15AnchoredAtom4502 chi ∧
      ¬Fin15AnchoredAtom4506 chi ∧
      ¬Fin15AnchoredAtom4510 chi ∧
      ¬Fin15AnchoredAtom4520 chi ∧
      ¬Fin15AnchoredAtom4540 chi ∧
      ¬Fin15AnchoredAtom4698 chi ∧
      ¬Fin15AnchoredAtom4702 chi ∧
      ¬Fin15AnchoredAtom4706 chi ∧
      ¬Fin15AnchoredAtom4716 chi ∧
      ¬Fin15AnchoredAtom4736 chi ∧
      ¬Fin15AnchoredAtom4771 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 6, 7, 8, 9, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask18385
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2528 Fin15AnchoredAtom2529 Fin15AnchoredAtom2530
    Fin15AnchoredAtom2534 Fin15AnchoredAtom2535 Fin15AnchoredAtom2536 Fin15AnchoredAtom2540
    Fin15AnchoredAtom2541 Fin15AnchoredAtom2545 Fin15AnchoredAtom2549 Fin15AnchoredAtom2556
    Fin15AnchoredAtom2557 Fin15AnchoredAtom2561 Fin15AnchoredAtom2562 Fin15AnchoredAtom2566
    Fin15AnchoredAtom2570 Fin15AnchoredAtom2577 Fin15AnchoredAtom2581 Fin15AnchoredAtom2585
    Fin15AnchoredAtom2595 Fin15AnchoredAtom2696 Fin15AnchoredAtom2697 Fin15AnchoredAtom2701
    Fin15AnchoredAtom2702 Fin15AnchoredAtom2706 Fin15AnchoredAtom2710 Fin15AnchoredAtom2717
    Fin15AnchoredAtom2721 Fin15AnchoredAtom2725 Fin15AnchoredAtom2735 Fin15AnchoredAtom2752
    Fin15AnchoredAtom2756 Fin15AnchoredAtom2760 Fin15AnchoredAtom2770 Fin15AnchoredAtom2790
    Fin15AnchoredAtom4446 Fin15AnchoredAtom4447 Fin15AnchoredAtom4451 Fin15AnchoredAtom4452
    Fin15AnchoredAtom4456 Fin15AnchoredAtom4460 Fin15AnchoredAtom4467 Fin15AnchoredAtom4471
    Fin15AnchoredAtom4475 Fin15AnchoredAtom4485 Fin15AnchoredAtom4502 Fin15AnchoredAtom4506
    Fin15AnchoredAtom4510 Fin15AnchoredAtom4520 Fin15AnchoredAtom4540 Fin15AnchoredAtom4698
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

theorem fin15Anchored_clause31571 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2528 chi ∧
      ¬Fin15AnchoredAtom2529 chi ∧
      ¬Fin15AnchoredAtom2532 chi ∧
      ¬Fin15AnchoredAtom2533 chi ∧
      ¬Fin15AnchoredAtom2535 chi ∧
      ¬Fin15AnchoredAtom2538 chi ∧
      ¬Fin15AnchoredAtom2539 chi ∧
      ¬Fin15AnchoredAtom2543 chi ∧
      ¬Fin15AnchoredAtom2544 chi ∧
      ¬Fin15AnchoredAtom2553 chi ∧
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
      ¬Fin15AnchoredAtom4446 chi ∧
      ¬Fin15AnchoredAtom4449 chi ∧
      ¬Fin15AnchoredAtom4450 chi ∧
      ¬Fin15AnchoredAtom4454 chi ∧
      ¬Fin15AnchoredAtom4455 chi ∧
      ¬Fin15AnchoredAtom4464 chi ∧
      ¬Fin15AnchoredAtom4469 chi ∧
      ¬Fin15AnchoredAtom4470 chi ∧
      ¬Fin15AnchoredAtom4479 chi ∧
      ¬Fin15AnchoredAtom4489 chi ∧
      ¬Fin15AnchoredAtom4504 chi ∧
      ¬Fin15AnchoredAtom4505 chi ∧
      ¬Fin15AnchoredAtom4514 chi ∧
      ¬Fin15AnchoredAtom4524 chi ∧
      ¬Fin15AnchoredAtom4544 chi ∧
      ¬Fin15AnchoredAtom4700 chi ∧
      ¬Fin15AnchoredAtom4701 chi ∧
      ¬Fin15AnchoredAtom4710 chi ∧
      ¬Fin15AnchoredAtom4720 chi ∧
      ¬Fin15AnchoredAtom4740 chi ∧
      ¬Fin15AnchoredAtom4775 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 6, 7, 8, 9, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13265
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2528 Fin15AnchoredAtom2529 Fin15AnchoredAtom2532
    Fin15AnchoredAtom2533 Fin15AnchoredAtom2535 Fin15AnchoredAtom2538 Fin15AnchoredAtom2539
    Fin15AnchoredAtom2543 Fin15AnchoredAtom2544 Fin15AnchoredAtom2553 Fin15AnchoredAtom2556
    Fin15AnchoredAtom2559 Fin15AnchoredAtom2560 Fin15AnchoredAtom2564 Fin15AnchoredAtom2565
    Fin15AnchoredAtom2574 Fin15AnchoredAtom2579 Fin15AnchoredAtom2580 Fin15AnchoredAtom2589
    Fin15AnchoredAtom2599 Fin15AnchoredAtom2696 Fin15AnchoredAtom2699 Fin15AnchoredAtom2700
    Fin15AnchoredAtom2704 Fin15AnchoredAtom2705 Fin15AnchoredAtom2714 Fin15AnchoredAtom2719
    Fin15AnchoredAtom2720 Fin15AnchoredAtom2729 Fin15AnchoredAtom2739 Fin15AnchoredAtom2754
    Fin15AnchoredAtom2755 Fin15AnchoredAtom2764 Fin15AnchoredAtom2774 Fin15AnchoredAtom2794
    Fin15AnchoredAtom4446 Fin15AnchoredAtom4449 Fin15AnchoredAtom4450 Fin15AnchoredAtom4454
    Fin15AnchoredAtom4455 Fin15AnchoredAtom4464 Fin15AnchoredAtom4469 Fin15AnchoredAtom4470
    Fin15AnchoredAtom4479 Fin15AnchoredAtom4489 Fin15AnchoredAtom4504 Fin15AnchoredAtom4505
    Fin15AnchoredAtom4514 Fin15AnchoredAtom4524 Fin15AnchoredAtom4544 Fin15AnchoredAtom4700
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

theorem fin15Anchored_clause31572 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2528 chi ∧
      ¬Fin15AnchoredAtom2529 chi ∧
      ¬Fin15AnchoredAtom2532 chi ∧
      ¬Fin15AnchoredAtom2534 chi ∧
      ¬Fin15AnchoredAtom2535 chi ∧
      ¬Fin15AnchoredAtom2538 chi ∧
      ¬Fin15AnchoredAtom2540 chi ∧
      ¬Fin15AnchoredAtom2543 chi ∧
      ¬Fin15AnchoredAtom2545 chi ∧
      ¬Fin15AnchoredAtom2554 chi ∧
      ¬Fin15AnchoredAtom2556 chi ∧
      ¬Fin15AnchoredAtom2559 chi ∧
      ¬Fin15AnchoredAtom2561 chi ∧
      ¬Fin15AnchoredAtom2564 chi ∧
      ¬Fin15AnchoredAtom2566 chi ∧
      ¬Fin15AnchoredAtom2575 chi ∧
      ¬Fin15AnchoredAtom2579 chi ∧
      ¬Fin15AnchoredAtom2581 chi ∧
      ¬Fin15AnchoredAtom2590 chi ∧
      ¬Fin15AnchoredAtom2600 chi ∧
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
      ¬Fin15AnchoredAtom4446 chi ∧
      ¬Fin15AnchoredAtom4449 chi ∧
      ¬Fin15AnchoredAtom4451 chi ∧
      ¬Fin15AnchoredAtom4454 chi ∧
      ¬Fin15AnchoredAtom4456 chi ∧
      ¬Fin15AnchoredAtom4465 chi ∧
      ¬Fin15AnchoredAtom4469 chi ∧
      ¬Fin15AnchoredAtom4471 chi ∧
      ¬Fin15AnchoredAtom4480 chi ∧
      ¬Fin15AnchoredAtom4490 chi ∧
      ¬Fin15AnchoredAtom4504 chi ∧
      ¬Fin15AnchoredAtom4506 chi ∧
      ¬Fin15AnchoredAtom4515 chi ∧
      ¬Fin15AnchoredAtom4525 chi ∧
      ¬Fin15AnchoredAtom4545 chi ∧
      ¬Fin15AnchoredAtom4700 chi ∧
      ¬Fin15AnchoredAtom4702 chi ∧
      ¬Fin15AnchoredAtom4711 chi ∧
      ¬Fin15AnchoredAtom4721 chi ∧
      ¬Fin15AnchoredAtom4741 chi ∧
      ¬Fin15AnchoredAtom4776 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 6, 7, 8, 9, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21457
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2528 Fin15AnchoredAtom2529 Fin15AnchoredAtom2532
    Fin15AnchoredAtom2534 Fin15AnchoredAtom2535 Fin15AnchoredAtom2538 Fin15AnchoredAtom2540
    Fin15AnchoredAtom2543 Fin15AnchoredAtom2545 Fin15AnchoredAtom2554 Fin15AnchoredAtom2556
    Fin15AnchoredAtom2559 Fin15AnchoredAtom2561 Fin15AnchoredAtom2564 Fin15AnchoredAtom2566
    Fin15AnchoredAtom2575 Fin15AnchoredAtom2579 Fin15AnchoredAtom2581 Fin15AnchoredAtom2590
    Fin15AnchoredAtom2600 Fin15AnchoredAtom2696 Fin15AnchoredAtom2699 Fin15AnchoredAtom2701
    Fin15AnchoredAtom2704 Fin15AnchoredAtom2706 Fin15AnchoredAtom2715 Fin15AnchoredAtom2719
    Fin15AnchoredAtom2721 Fin15AnchoredAtom2730 Fin15AnchoredAtom2740 Fin15AnchoredAtom2754
    Fin15AnchoredAtom2756 Fin15AnchoredAtom2765 Fin15AnchoredAtom2775 Fin15AnchoredAtom2795
    Fin15AnchoredAtom4446 Fin15AnchoredAtom4449 Fin15AnchoredAtom4451 Fin15AnchoredAtom4454
    Fin15AnchoredAtom4456 Fin15AnchoredAtom4465 Fin15AnchoredAtom4469 Fin15AnchoredAtom4471
    Fin15AnchoredAtom4480 Fin15AnchoredAtom4490 Fin15AnchoredAtom4504 Fin15AnchoredAtom4506
    Fin15AnchoredAtom4515 Fin15AnchoredAtom4525 Fin15AnchoredAtom4545 Fin15AnchoredAtom4700
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

theorem fin15Anchored_clause31573 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2528 chi ∧
      ¬Fin15AnchoredAtom2529 chi ∧
      ¬Fin15AnchoredAtom2533 chi ∧
      ¬Fin15AnchoredAtom2534 chi ∧
      ¬Fin15AnchoredAtom2535 chi ∧
      ¬Fin15AnchoredAtom2539 chi ∧
      ¬Fin15AnchoredAtom2540 chi ∧
      ¬Fin15AnchoredAtom2544 chi ∧
      ¬Fin15AnchoredAtom2545 chi ∧
      ¬Fin15AnchoredAtom2555 chi ∧
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
      ¬Fin15AnchoredAtom4446 chi ∧
      ¬Fin15AnchoredAtom4450 chi ∧
      ¬Fin15AnchoredAtom4451 chi ∧
      ¬Fin15AnchoredAtom4455 chi ∧
      ¬Fin15AnchoredAtom4456 chi ∧
      ¬Fin15AnchoredAtom4466 chi ∧
      ¬Fin15AnchoredAtom4470 chi ∧
      ¬Fin15AnchoredAtom4471 chi ∧
      ¬Fin15AnchoredAtom4481 chi ∧
      ¬Fin15AnchoredAtom4491 chi ∧
      ¬Fin15AnchoredAtom4505 chi ∧
      ¬Fin15AnchoredAtom4506 chi ∧
      ¬Fin15AnchoredAtom4516 chi ∧
      ¬Fin15AnchoredAtom4526 chi ∧
      ¬Fin15AnchoredAtom4546 chi ∧
      ¬Fin15AnchoredAtom4701 chi ∧
      ¬Fin15AnchoredAtom4702 chi ∧
      ¬Fin15AnchoredAtom4712 chi ∧
      ¬Fin15AnchoredAtom4722 chi ∧
      ¬Fin15AnchoredAtom4742 chi ∧
      ¬Fin15AnchoredAtom4777 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 6, 7, 8, 9, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25553
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2528 Fin15AnchoredAtom2529 Fin15AnchoredAtom2533
    Fin15AnchoredAtom2534 Fin15AnchoredAtom2535 Fin15AnchoredAtom2539 Fin15AnchoredAtom2540
    Fin15AnchoredAtom2544 Fin15AnchoredAtom2545 Fin15AnchoredAtom2555 Fin15AnchoredAtom2556
    Fin15AnchoredAtom2560 Fin15AnchoredAtom2561 Fin15AnchoredAtom2565 Fin15AnchoredAtom2566
    Fin15AnchoredAtom2576 Fin15AnchoredAtom2580 Fin15AnchoredAtom2581 Fin15AnchoredAtom2591
    Fin15AnchoredAtom2601 Fin15AnchoredAtom2696 Fin15AnchoredAtom2700 Fin15AnchoredAtom2701
    Fin15AnchoredAtom2705 Fin15AnchoredAtom2706 Fin15AnchoredAtom2716 Fin15AnchoredAtom2720
    Fin15AnchoredAtom2721 Fin15AnchoredAtom2731 Fin15AnchoredAtom2741 Fin15AnchoredAtom2755
    Fin15AnchoredAtom2756 Fin15AnchoredAtom2766 Fin15AnchoredAtom2776 Fin15AnchoredAtom2796
    Fin15AnchoredAtom4446 Fin15AnchoredAtom4450 Fin15AnchoredAtom4451 Fin15AnchoredAtom4455
    Fin15AnchoredAtom4456 Fin15AnchoredAtom4466 Fin15AnchoredAtom4470 Fin15AnchoredAtom4471
    Fin15AnchoredAtom4481 Fin15AnchoredAtom4491 Fin15AnchoredAtom4505 Fin15AnchoredAtom4506
    Fin15AnchoredAtom4516 Fin15AnchoredAtom4526 Fin15AnchoredAtom4546 Fin15AnchoredAtom4701
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

theorem fin15Anchored_clause31574 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2528 chi ∧
      ¬Fin15AnchoredAtom2530 chi ∧
      ¬Fin15AnchoredAtom2532 chi ∧
      ¬Fin15AnchoredAtom2533 chi ∧
      ¬Fin15AnchoredAtom2536 chi ∧
      ¬Fin15AnchoredAtom2538 chi ∧
      ¬Fin15AnchoredAtom2539 chi ∧
      ¬Fin15AnchoredAtom2547 chi ∧
      ¬Fin15AnchoredAtom2548 chi ∧
      ¬Fin15AnchoredAtom2553 chi ∧
      ¬Fin15AnchoredAtom2557 chi ∧
      ¬Fin15AnchoredAtom2559 chi ∧
      ¬Fin15AnchoredAtom2560 chi ∧
      ¬Fin15AnchoredAtom2568 chi ∧
      ¬Fin15AnchoredAtom2569 chi ∧
      ¬Fin15AnchoredAtom2574 chi ∧
      ¬Fin15AnchoredAtom2583 chi ∧
      ¬Fin15AnchoredAtom2584 chi ∧
      ¬Fin15AnchoredAtom2589 chi ∧
      ¬Fin15AnchoredAtom2605 chi ∧
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
      ¬Fin15AnchoredAtom4447 chi ∧
      ¬Fin15AnchoredAtom4449 chi ∧
      ¬Fin15AnchoredAtom4450 chi ∧
      ¬Fin15AnchoredAtom4458 chi ∧
      ¬Fin15AnchoredAtom4459 chi ∧
      ¬Fin15AnchoredAtom4464 chi ∧
      ¬Fin15AnchoredAtom4473 chi ∧
      ¬Fin15AnchoredAtom4474 chi ∧
      ¬Fin15AnchoredAtom4479 chi ∧
      ¬Fin15AnchoredAtom4495 chi ∧
      ¬Fin15AnchoredAtom4508 chi ∧
      ¬Fin15AnchoredAtom4509 chi ∧
      ¬Fin15AnchoredAtom4514 chi ∧
      ¬Fin15AnchoredAtom4530 chi ∧
      ¬Fin15AnchoredAtom4550 chi ∧
      ¬Fin15AnchoredAtom4704 chi ∧
      ¬Fin15AnchoredAtom4705 chi ∧
      ¬Fin15AnchoredAtom4710 chi ∧
      ¬Fin15AnchoredAtom4726 chi ∧
      ¬Fin15AnchoredAtom4746 chi ∧
      ¬Fin15AnchoredAtom4781 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 6, 7, 8, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13777
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2528 Fin15AnchoredAtom2530 Fin15AnchoredAtom2532
    Fin15AnchoredAtom2533 Fin15AnchoredAtom2536 Fin15AnchoredAtom2538 Fin15AnchoredAtom2539
    Fin15AnchoredAtom2547 Fin15AnchoredAtom2548 Fin15AnchoredAtom2553 Fin15AnchoredAtom2557
    Fin15AnchoredAtom2559 Fin15AnchoredAtom2560 Fin15AnchoredAtom2568 Fin15AnchoredAtom2569
    Fin15AnchoredAtom2574 Fin15AnchoredAtom2583 Fin15AnchoredAtom2584 Fin15AnchoredAtom2589
    Fin15AnchoredAtom2605 Fin15AnchoredAtom2697 Fin15AnchoredAtom2699 Fin15AnchoredAtom2700
    Fin15AnchoredAtom2708 Fin15AnchoredAtom2709 Fin15AnchoredAtom2714 Fin15AnchoredAtom2723
    Fin15AnchoredAtom2724 Fin15AnchoredAtom2729 Fin15AnchoredAtom2745 Fin15AnchoredAtom2758
    Fin15AnchoredAtom2759 Fin15AnchoredAtom2764 Fin15AnchoredAtom2780 Fin15AnchoredAtom2800
    Fin15AnchoredAtom4447 Fin15AnchoredAtom4449 Fin15AnchoredAtom4450 Fin15AnchoredAtom4458
    Fin15AnchoredAtom4459 Fin15AnchoredAtom4464 Fin15AnchoredAtom4473 Fin15AnchoredAtom4474
    Fin15AnchoredAtom4479 Fin15AnchoredAtom4495 Fin15AnchoredAtom4508 Fin15AnchoredAtom4509
    Fin15AnchoredAtom4514 Fin15AnchoredAtom4530 Fin15AnchoredAtom4550 Fin15AnchoredAtom4704
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

theorem fin15Anchored_clause31575 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2528 chi ∧
      ¬Fin15AnchoredAtom2530 chi ∧
      ¬Fin15AnchoredAtom2532 chi ∧
      ¬Fin15AnchoredAtom2534 chi ∧
      ¬Fin15AnchoredAtom2536 chi ∧
      ¬Fin15AnchoredAtom2538 chi ∧
      ¬Fin15AnchoredAtom2540 chi ∧
      ¬Fin15AnchoredAtom2547 chi ∧
      ¬Fin15AnchoredAtom2549 chi ∧
      ¬Fin15AnchoredAtom2554 chi ∧
      ¬Fin15AnchoredAtom2557 chi ∧
      ¬Fin15AnchoredAtom2559 chi ∧
      ¬Fin15AnchoredAtom2561 chi ∧
      ¬Fin15AnchoredAtom2568 chi ∧
      ¬Fin15AnchoredAtom2570 chi ∧
      ¬Fin15AnchoredAtom2575 chi ∧
      ¬Fin15AnchoredAtom2583 chi ∧
      ¬Fin15AnchoredAtom2585 chi ∧
      ¬Fin15AnchoredAtom2590 chi ∧
      ¬Fin15AnchoredAtom2606 chi ∧
      ¬Fin15AnchoredAtom2697 chi ∧
      ¬Fin15AnchoredAtom2699 chi ∧
      ¬Fin15AnchoredAtom2701 chi ∧
      ¬Fin15AnchoredAtom2708 chi ∧
      ¬Fin15AnchoredAtom2710 chi ∧
      ¬Fin15AnchoredAtom2715 chi ∧
      ¬Fin15AnchoredAtom2723 chi ∧
      ¬Fin15AnchoredAtom2725 chi ∧
      ¬Fin15AnchoredAtom2730 chi ∧
      ¬Fin15AnchoredAtom2746 chi ∧
      ¬Fin15AnchoredAtom2758 chi ∧
      ¬Fin15AnchoredAtom2760 chi ∧
      ¬Fin15AnchoredAtom2765 chi ∧
      ¬Fin15AnchoredAtom2781 chi ∧
      ¬Fin15AnchoredAtom2801 chi ∧
      ¬Fin15AnchoredAtom4447 chi ∧
      ¬Fin15AnchoredAtom4449 chi ∧
      ¬Fin15AnchoredAtom4451 chi ∧
      ¬Fin15AnchoredAtom4458 chi ∧
      ¬Fin15AnchoredAtom4460 chi ∧
      ¬Fin15AnchoredAtom4465 chi ∧
      ¬Fin15AnchoredAtom4473 chi ∧
      ¬Fin15AnchoredAtom4475 chi ∧
      ¬Fin15AnchoredAtom4480 chi ∧
      ¬Fin15AnchoredAtom4496 chi ∧
      ¬Fin15AnchoredAtom4508 chi ∧
      ¬Fin15AnchoredAtom4510 chi ∧
      ¬Fin15AnchoredAtom4515 chi ∧
      ¬Fin15AnchoredAtom4531 chi ∧
      ¬Fin15AnchoredAtom4551 chi ∧
      ¬Fin15AnchoredAtom4704 chi ∧
      ¬Fin15AnchoredAtom4706 chi ∧
      ¬Fin15AnchoredAtom4711 chi ∧
      ¬Fin15AnchoredAtom4727 chi ∧
      ¬Fin15AnchoredAtom4747 chi ∧
      ¬Fin15AnchoredAtom4782 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 6, 7, 8, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21969
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2528 Fin15AnchoredAtom2530 Fin15AnchoredAtom2532
    Fin15AnchoredAtom2534 Fin15AnchoredAtom2536 Fin15AnchoredAtom2538 Fin15AnchoredAtom2540
    Fin15AnchoredAtom2547 Fin15AnchoredAtom2549 Fin15AnchoredAtom2554 Fin15AnchoredAtom2557
    Fin15AnchoredAtom2559 Fin15AnchoredAtom2561 Fin15AnchoredAtom2568 Fin15AnchoredAtom2570
    Fin15AnchoredAtom2575 Fin15AnchoredAtom2583 Fin15AnchoredAtom2585 Fin15AnchoredAtom2590
    Fin15AnchoredAtom2606 Fin15AnchoredAtom2697 Fin15AnchoredAtom2699 Fin15AnchoredAtom2701
    Fin15AnchoredAtom2708 Fin15AnchoredAtom2710 Fin15AnchoredAtom2715 Fin15AnchoredAtom2723
    Fin15AnchoredAtom2725 Fin15AnchoredAtom2730 Fin15AnchoredAtom2746 Fin15AnchoredAtom2758
    Fin15AnchoredAtom2760 Fin15AnchoredAtom2765 Fin15AnchoredAtom2781 Fin15AnchoredAtom2801
    Fin15AnchoredAtom4447 Fin15AnchoredAtom4449 Fin15AnchoredAtom4451 Fin15AnchoredAtom4458
    Fin15AnchoredAtom4460 Fin15AnchoredAtom4465 Fin15AnchoredAtom4473 Fin15AnchoredAtom4475
    Fin15AnchoredAtom4480 Fin15AnchoredAtom4496 Fin15AnchoredAtom4508 Fin15AnchoredAtom4510
    Fin15AnchoredAtom4515 Fin15AnchoredAtom4531 Fin15AnchoredAtom4551 Fin15AnchoredAtom4704
    Fin15AnchoredAtom4706 Fin15AnchoredAtom4711 Fin15AnchoredAtom4727 Fin15AnchoredAtom4747
    Fin15AnchoredAtom4782 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31576 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2528 chi ∧
      ¬Fin15AnchoredAtom2530 chi ∧
      ¬Fin15AnchoredAtom2533 chi ∧
      ¬Fin15AnchoredAtom2534 chi ∧
      ¬Fin15AnchoredAtom2536 chi ∧
      ¬Fin15AnchoredAtom2539 chi ∧
      ¬Fin15AnchoredAtom2540 chi ∧
      ¬Fin15AnchoredAtom2548 chi ∧
      ¬Fin15AnchoredAtom2549 chi ∧
      ¬Fin15AnchoredAtom2555 chi ∧
      ¬Fin15AnchoredAtom2557 chi ∧
      ¬Fin15AnchoredAtom2560 chi ∧
      ¬Fin15AnchoredAtom2561 chi ∧
      ¬Fin15AnchoredAtom2569 chi ∧
      ¬Fin15AnchoredAtom2570 chi ∧
      ¬Fin15AnchoredAtom2576 chi ∧
      ¬Fin15AnchoredAtom2584 chi ∧
      ¬Fin15AnchoredAtom2585 chi ∧
      ¬Fin15AnchoredAtom2591 chi ∧
      ¬Fin15AnchoredAtom2607 chi ∧
      ¬Fin15AnchoredAtom2697 chi ∧
      ¬Fin15AnchoredAtom2700 chi ∧
      ¬Fin15AnchoredAtom2701 chi ∧
      ¬Fin15AnchoredAtom2709 chi ∧
      ¬Fin15AnchoredAtom2710 chi ∧
      ¬Fin15AnchoredAtom2716 chi ∧
      ¬Fin15AnchoredAtom2724 chi ∧
      ¬Fin15AnchoredAtom2725 chi ∧
      ¬Fin15AnchoredAtom2731 chi ∧
      ¬Fin15AnchoredAtom2747 chi ∧
      ¬Fin15AnchoredAtom2759 chi ∧
      ¬Fin15AnchoredAtom2760 chi ∧
      ¬Fin15AnchoredAtom2766 chi ∧
      ¬Fin15AnchoredAtom2782 chi ∧
      ¬Fin15AnchoredAtom2802 chi ∧
      ¬Fin15AnchoredAtom4447 chi ∧
      ¬Fin15AnchoredAtom4450 chi ∧
      ¬Fin15AnchoredAtom4451 chi ∧
      ¬Fin15AnchoredAtom4459 chi ∧
      ¬Fin15AnchoredAtom4460 chi ∧
      ¬Fin15AnchoredAtom4466 chi ∧
      ¬Fin15AnchoredAtom4474 chi ∧
      ¬Fin15AnchoredAtom4475 chi ∧
      ¬Fin15AnchoredAtom4481 chi ∧
      ¬Fin15AnchoredAtom4497 chi ∧
      ¬Fin15AnchoredAtom4509 chi ∧
      ¬Fin15AnchoredAtom4510 chi ∧
      ¬Fin15AnchoredAtom4516 chi ∧
      ¬Fin15AnchoredAtom4532 chi ∧
      ¬Fin15AnchoredAtom4552 chi ∧
      ¬Fin15AnchoredAtom4705 chi ∧
      ¬Fin15AnchoredAtom4706 chi ∧
      ¬Fin15AnchoredAtom4712 chi ∧
      ¬Fin15AnchoredAtom4728 chi ∧
      ¬Fin15AnchoredAtom4748 chi ∧
      ¬Fin15AnchoredAtom4783 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 6, 7, 8, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26065
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2528 Fin15AnchoredAtom2530 Fin15AnchoredAtom2533
    Fin15AnchoredAtom2534 Fin15AnchoredAtom2536 Fin15AnchoredAtom2539 Fin15AnchoredAtom2540
    Fin15AnchoredAtom2548 Fin15AnchoredAtom2549 Fin15AnchoredAtom2555 Fin15AnchoredAtom2557
    Fin15AnchoredAtom2560 Fin15AnchoredAtom2561 Fin15AnchoredAtom2569 Fin15AnchoredAtom2570
    Fin15AnchoredAtom2576 Fin15AnchoredAtom2584 Fin15AnchoredAtom2585 Fin15AnchoredAtom2591
    Fin15AnchoredAtom2607 Fin15AnchoredAtom2697 Fin15AnchoredAtom2700 Fin15AnchoredAtom2701
    Fin15AnchoredAtom2709 Fin15AnchoredAtom2710 Fin15AnchoredAtom2716 Fin15AnchoredAtom2724
    Fin15AnchoredAtom2725 Fin15AnchoredAtom2731 Fin15AnchoredAtom2747 Fin15AnchoredAtom2759
    Fin15AnchoredAtom2760 Fin15AnchoredAtom2766 Fin15AnchoredAtom2782 Fin15AnchoredAtom2802
    Fin15AnchoredAtom4447 Fin15AnchoredAtom4450 Fin15AnchoredAtom4451 Fin15AnchoredAtom4459
    Fin15AnchoredAtom4460 Fin15AnchoredAtom4466 Fin15AnchoredAtom4474 Fin15AnchoredAtom4475
    Fin15AnchoredAtom4481 Fin15AnchoredAtom4497 Fin15AnchoredAtom4509 Fin15AnchoredAtom4510
    Fin15AnchoredAtom4516 Fin15AnchoredAtom4532 Fin15AnchoredAtom4552 Fin15AnchoredAtom4705
    Fin15AnchoredAtom4706 Fin15AnchoredAtom4712 Fin15AnchoredAtom4728 Fin15AnchoredAtom4748
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

theorem fin15Anchored_clause31577 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2529 chi ∧
      ¬Fin15AnchoredAtom2530 chi ∧
      ¬Fin15AnchoredAtom2531 chi ∧
      ¬Fin15AnchoredAtom2534 chi ∧
      ¬Fin15AnchoredAtom2541 chi ∧
      ¬Fin15AnchoredAtom2542 chi ∧
      ¬Fin15AnchoredAtom2545 chi ∧
      ¬Fin15AnchoredAtom2546 chi ∧
      ¬Fin15AnchoredAtom2549 chi ∧
      ¬Fin15AnchoredAtom2552 chi ∧
      ¬Fin15AnchoredAtom2562 chi ∧
      ¬Fin15AnchoredAtom2563 chi ∧
      ¬Fin15AnchoredAtom2566 chi ∧
      ¬Fin15AnchoredAtom2567 chi ∧
      ¬Fin15AnchoredAtom2570 chi ∧
      ¬Fin15AnchoredAtom2573 chi ∧
      ¬Fin15AnchoredAtom2592 chi ∧
      ¬Fin15AnchoredAtom2595 chi ∧
      ¬Fin15AnchoredAtom2598 chi ∧
      ¬Fin15AnchoredAtom2604 chi ∧
      ¬Fin15AnchoredAtom2702 chi ∧
      ¬Fin15AnchoredAtom2703 chi ∧
      ¬Fin15AnchoredAtom2706 chi ∧
      ¬Fin15AnchoredAtom2707 chi ∧
      ¬Fin15AnchoredAtom2710 chi ∧
      ¬Fin15AnchoredAtom2713 chi ∧
      ¬Fin15AnchoredAtom2732 chi ∧
      ¬Fin15AnchoredAtom2735 chi ∧
      ¬Fin15AnchoredAtom2738 chi ∧
      ¬Fin15AnchoredAtom2744 chi ∧
      ¬Fin15AnchoredAtom2767 chi ∧
      ¬Fin15AnchoredAtom2770 chi ∧
      ¬Fin15AnchoredAtom2773 chi ∧
      ¬Fin15AnchoredAtom2779 chi ∧
      ¬Fin15AnchoredAtom2809 chi ∧
      ¬Fin15AnchoredAtom4452 chi ∧
      ¬Fin15AnchoredAtom4453 chi ∧
      ¬Fin15AnchoredAtom4456 chi ∧
      ¬Fin15AnchoredAtom4457 chi ∧
      ¬Fin15AnchoredAtom4460 chi ∧
      ¬Fin15AnchoredAtom4463 chi ∧
      ¬Fin15AnchoredAtom4482 chi ∧
      ¬Fin15AnchoredAtom4485 chi ∧
      ¬Fin15AnchoredAtom4488 chi ∧
      ¬Fin15AnchoredAtom4494 chi ∧
      ¬Fin15AnchoredAtom4517 chi ∧
      ¬Fin15AnchoredAtom4520 chi ∧
      ¬Fin15AnchoredAtom4523 chi ∧
      ¬Fin15AnchoredAtom4529 chi ∧
      ¬Fin15AnchoredAtom4559 chi ∧
      ¬Fin15AnchoredAtom4713 chi ∧
      ¬Fin15AnchoredAtom4716 chi ∧
      ¬Fin15AnchoredAtom4719 chi ∧
      ¬Fin15AnchoredAtom4725 chi ∧
      ¬Fin15AnchoredAtom4755 chi ∧
      ¬Fin15AnchoredAtom4790 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 6, 7, 9, 10, 11, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask20177
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2529 Fin15AnchoredAtom2530 Fin15AnchoredAtom2531
    Fin15AnchoredAtom2534 Fin15AnchoredAtom2541 Fin15AnchoredAtom2542 Fin15AnchoredAtom2545
    Fin15AnchoredAtom2546 Fin15AnchoredAtom2549 Fin15AnchoredAtom2552 Fin15AnchoredAtom2562
    Fin15AnchoredAtom2563 Fin15AnchoredAtom2566 Fin15AnchoredAtom2567 Fin15AnchoredAtom2570
    Fin15AnchoredAtom2573 Fin15AnchoredAtom2592 Fin15AnchoredAtom2595 Fin15AnchoredAtom2598
    Fin15AnchoredAtom2604 Fin15AnchoredAtom2702 Fin15AnchoredAtom2703 Fin15AnchoredAtom2706
    Fin15AnchoredAtom2707 Fin15AnchoredAtom2710 Fin15AnchoredAtom2713 Fin15AnchoredAtom2732
    Fin15AnchoredAtom2735 Fin15AnchoredAtom2738 Fin15AnchoredAtom2744 Fin15AnchoredAtom2767
    Fin15AnchoredAtom2770 Fin15AnchoredAtom2773 Fin15AnchoredAtom2779 Fin15AnchoredAtom2809
    Fin15AnchoredAtom4452 Fin15AnchoredAtom4453 Fin15AnchoredAtom4456 Fin15AnchoredAtom4457
    Fin15AnchoredAtom4460 Fin15AnchoredAtom4463 Fin15AnchoredAtom4482 Fin15AnchoredAtom4485
    Fin15AnchoredAtom4488 Fin15AnchoredAtom4494 Fin15AnchoredAtom4517 Fin15AnchoredAtom4520
    Fin15AnchoredAtom4523 Fin15AnchoredAtom4529 Fin15AnchoredAtom4559 Fin15AnchoredAtom4713
    Fin15AnchoredAtom4716 Fin15AnchoredAtom4719 Fin15AnchoredAtom4725 Fin15AnchoredAtom4755
    Fin15AnchoredAtom4790 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31578 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2529 chi ∧
      ¬Fin15AnchoredAtom2530 chi ∧
      ¬Fin15AnchoredAtom2532 chi ∧
      ¬Fin15AnchoredAtom2533 chi ∧
      ¬Fin15AnchoredAtom2541 chi ∧
      ¬Fin15AnchoredAtom2543 chi ∧
      ¬Fin15AnchoredAtom2544 chi ∧
      ¬Fin15AnchoredAtom2547 chi ∧
      ¬Fin15AnchoredAtom2548 chi ∧
      ¬Fin15AnchoredAtom2553 chi ∧
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
      ¬Fin15AnchoredAtom4452 chi ∧
      ¬Fin15AnchoredAtom4454 chi ∧
      ¬Fin15AnchoredAtom4455 chi ∧
      ¬Fin15AnchoredAtom4458 chi ∧
      ¬Fin15AnchoredAtom4459 chi ∧
      ¬Fin15AnchoredAtom4464 chi ∧
      ¬Fin15AnchoredAtom4483 chi ∧
      ¬Fin15AnchoredAtom4484 chi ∧
      ¬Fin15AnchoredAtom4489 chi ∧
      ¬Fin15AnchoredAtom4495 chi ∧
      ¬Fin15AnchoredAtom4518 chi ∧
      ¬Fin15AnchoredAtom4519 chi ∧
      ¬Fin15AnchoredAtom4524 chi ∧
      ¬Fin15AnchoredAtom4530 chi ∧
      ¬Fin15AnchoredAtom4560 chi ∧
      ¬Fin15AnchoredAtom4714 chi ∧
      ¬Fin15AnchoredAtom4715 chi ∧
      ¬Fin15AnchoredAtom4720 chi ∧
      ¬Fin15AnchoredAtom4726 chi ∧
      ¬Fin15AnchoredAtom4756 chi ∧
      ¬Fin15AnchoredAtom4791 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 6, 7, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask14033
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2529 Fin15AnchoredAtom2530 Fin15AnchoredAtom2532
    Fin15AnchoredAtom2533 Fin15AnchoredAtom2541 Fin15AnchoredAtom2543 Fin15AnchoredAtom2544
    Fin15AnchoredAtom2547 Fin15AnchoredAtom2548 Fin15AnchoredAtom2553 Fin15AnchoredAtom2562
    Fin15AnchoredAtom2564 Fin15AnchoredAtom2565 Fin15AnchoredAtom2568 Fin15AnchoredAtom2569
    Fin15AnchoredAtom2574 Fin15AnchoredAtom2593 Fin15AnchoredAtom2594 Fin15AnchoredAtom2599
    Fin15AnchoredAtom2605 Fin15AnchoredAtom2702 Fin15AnchoredAtom2704 Fin15AnchoredAtom2705
    Fin15AnchoredAtom2708 Fin15AnchoredAtom2709 Fin15AnchoredAtom2714 Fin15AnchoredAtom2733
    Fin15AnchoredAtom2734 Fin15AnchoredAtom2739 Fin15AnchoredAtom2745 Fin15AnchoredAtom2768
    Fin15AnchoredAtom2769 Fin15AnchoredAtom2774 Fin15AnchoredAtom2780 Fin15AnchoredAtom2810
    Fin15AnchoredAtom4452 Fin15AnchoredAtom4454 Fin15AnchoredAtom4455 Fin15AnchoredAtom4458
    Fin15AnchoredAtom4459 Fin15AnchoredAtom4464 Fin15AnchoredAtom4483 Fin15AnchoredAtom4484
    Fin15AnchoredAtom4489 Fin15AnchoredAtom4495 Fin15AnchoredAtom4518 Fin15AnchoredAtom4519
    Fin15AnchoredAtom4524 Fin15AnchoredAtom4530 Fin15AnchoredAtom4560 Fin15AnchoredAtom4714
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

theorem fin15Anchored_clause31579 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2529 chi ∧
      ¬Fin15AnchoredAtom2530 chi ∧
      ¬Fin15AnchoredAtom2532 chi ∧
      ¬Fin15AnchoredAtom2534 chi ∧
      ¬Fin15AnchoredAtom2541 chi ∧
      ¬Fin15AnchoredAtom2543 chi ∧
      ¬Fin15AnchoredAtom2545 chi ∧
      ¬Fin15AnchoredAtom2547 chi ∧
      ¬Fin15AnchoredAtom2549 chi ∧
      ¬Fin15AnchoredAtom2554 chi ∧
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
      ¬Fin15AnchoredAtom4452 chi ∧
      ¬Fin15AnchoredAtom4454 chi ∧
      ¬Fin15AnchoredAtom4456 chi ∧
      ¬Fin15AnchoredAtom4458 chi ∧
      ¬Fin15AnchoredAtom4460 chi ∧
      ¬Fin15AnchoredAtom4465 chi ∧
      ¬Fin15AnchoredAtom4483 chi ∧
      ¬Fin15AnchoredAtom4485 chi ∧
      ¬Fin15AnchoredAtom4490 chi ∧
      ¬Fin15AnchoredAtom4496 chi ∧
      ¬Fin15AnchoredAtom4518 chi ∧
      ¬Fin15AnchoredAtom4520 chi ∧
      ¬Fin15AnchoredAtom4525 chi ∧
      ¬Fin15AnchoredAtom4531 chi ∧
      ¬Fin15AnchoredAtom4561 chi ∧
      ¬Fin15AnchoredAtom4714 chi ∧
      ¬Fin15AnchoredAtom4716 chi ∧
      ¬Fin15AnchoredAtom4721 chi ∧
      ¬Fin15AnchoredAtom4727 chi ∧
      ¬Fin15AnchoredAtom4757 chi ∧
      ¬Fin15AnchoredAtom4792 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 6, 7, 9, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22225
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2529 Fin15AnchoredAtom2530 Fin15AnchoredAtom2532
    Fin15AnchoredAtom2534 Fin15AnchoredAtom2541 Fin15AnchoredAtom2543 Fin15AnchoredAtom2545
    Fin15AnchoredAtom2547 Fin15AnchoredAtom2549 Fin15AnchoredAtom2554 Fin15AnchoredAtom2562
    Fin15AnchoredAtom2564 Fin15AnchoredAtom2566 Fin15AnchoredAtom2568 Fin15AnchoredAtom2570
    Fin15AnchoredAtom2575 Fin15AnchoredAtom2593 Fin15AnchoredAtom2595 Fin15AnchoredAtom2600
    Fin15AnchoredAtom2606 Fin15AnchoredAtom2702 Fin15AnchoredAtom2704 Fin15AnchoredAtom2706
    Fin15AnchoredAtom2708 Fin15AnchoredAtom2710 Fin15AnchoredAtom2715 Fin15AnchoredAtom2733
    Fin15AnchoredAtom2735 Fin15AnchoredAtom2740 Fin15AnchoredAtom2746 Fin15AnchoredAtom2768
    Fin15AnchoredAtom2770 Fin15AnchoredAtom2775 Fin15AnchoredAtom2781 Fin15AnchoredAtom2811
    Fin15AnchoredAtom4452 Fin15AnchoredAtom4454 Fin15AnchoredAtom4456 Fin15AnchoredAtom4458
    Fin15AnchoredAtom4460 Fin15AnchoredAtom4465 Fin15AnchoredAtom4483 Fin15AnchoredAtom4485
    Fin15AnchoredAtom4490 Fin15AnchoredAtom4496 Fin15AnchoredAtom4518 Fin15AnchoredAtom4520
    Fin15AnchoredAtom4525 Fin15AnchoredAtom4531 Fin15AnchoredAtom4561 Fin15AnchoredAtom4714
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

theorem fin15Anchored_clause31580 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2529 chi ∧
      ¬Fin15AnchoredAtom2530 chi ∧
      ¬Fin15AnchoredAtom2533 chi ∧
      ¬Fin15AnchoredAtom2534 chi ∧
      ¬Fin15AnchoredAtom2541 chi ∧
      ¬Fin15AnchoredAtom2544 chi ∧
      ¬Fin15AnchoredAtom2545 chi ∧
      ¬Fin15AnchoredAtom2548 chi ∧
      ¬Fin15AnchoredAtom2549 chi ∧
      ¬Fin15AnchoredAtom2555 chi ∧
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
      ¬Fin15AnchoredAtom4452 chi ∧
      ¬Fin15AnchoredAtom4455 chi ∧
      ¬Fin15AnchoredAtom4456 chi ∧
      ¬Fin15AnchoredAtom4459 chi ∧
      ¬Fin15AnchoredAtom4460 chi ∧
      ¬Fin15AnchoredAtom4466 chi ∧
      ¬Fin15AnchoredAtom4484 chi ∧
      ¬Fin15AnchoredAtom4485 chi ∧
      ¬Fin15AnchoredAtom4491 chi ∧
      ¬Fin15AnchoredAtom4497 chi ∧
      ¬Fin15AnchoredAtom4519 chi ∧
      ¬Fin15AnchoredAtom4520 chi ∧
      ¬Fin15AnchoredAtom4526 chi ∧
      ¬Fin15AnchoredAtom4532 chi ∧
      ¬Fin15AnchoredAtom4562 chi ∧
      ¬Fin15AnchoredAtom4715 chi ∧
      ¬Fin15AnchoredAtom4716 chi ∧
      ¬Fin15AnchoredAtom4722 chi ∧
      ¬Fin15AnchoredAtom4728 chi ∧
      ¬Fin15AnchoredAtom4758 chi ∧
      ¬Fin15AnchoredAtom4793 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 6, 7, 9, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26321
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2529 Fin15AnchoredAtom2530 Fin15AnchoredAtom2533
    Fin15AnchoredAtom2534 Fin15AnchoredAtom2541 Fin15AnchoredAtom2544 Fin15AnchoredAtom2545
    Fin15AnchoredAtom2548 Fin15AnchoredAtom2549 Fin15AnchoredAtom2555 Fin15AnchoredAtom2562
    Fin15AnchoredAtom2565 Fin15AnchoredAtom2566 Fin15AnchoredAtom2569 Fin15AnchoredAtom2570
    Fin15AnchoredAtom2576 Fin15AnchoredAtom2594 Fin15AnchoredAtom2595 Fin15AnchoredAtom2601
    Fin15AnchoredAtom2607 Fin15AnchoredAtom2702 Fin15AnchoredAtom2705 Fin15AnchoredAtom2706
    Fin15AnchoredAtom2709 Fin15AnchoredAtom2710 Fin15AnchoredAtom2716 Fin15AnchoredAtom2734
    Fin15AnchoredAtom2735 Fin15AnchoredAtom2741 Fin15AnchoredAtom2747 Fin15AnchoredAtom2769
    Fin15AnchoredAtom2770 Fin15AnchoredAtom2776 Fin15AnchoredAtom2782 Fin15AnchoredAtom2812
    Fin15AnchoredAtom4452 Fin15AnchoredAtom4455 Fin15AnchoredAtom4456 Fin15AnchoredAtom4459
    Fin15AnchoredAtom4460 Fin15AnchoredAtom4466 Fin15AnchoredAtom4484 Fin15AnchoredAtom4485
    Fin15AnchoredAtom4491 Fin15AnchoredAtom4497 Fin15AnchoredAtom4519 Fin15AnchoredAtom4520
    Fin15AnchoredAtom4526 Fin15AnchoredAtom4532 Fin15AnchoredAtom4562 Fin15AnchoredAtom4715
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

theorem fin15Anchored_clause31581 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2529 chi ∧
      ¬Fin15AnchoredAtom2532 chi ∧
      ¬Fin15AnchoredAtom2533 chi ∧
      ¬Fin15AnchoredAtom2534 chi ∧
      ¬Fin15AnchoredAtom2543 chi ∧
      ¬Fin15AnchoredAtom2544 chi ∧
      ¬Fin15AnchoredAtom2545 chi ∧
      ¬Fin15AnchoredAtom2553 chi ∧
      ¬Fin15AnchoredAtom2554 chi ∧
      ¬Fin15AnchoredAtom2555 chi ∧
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
      ¬Fin15AnchoredAtom4454 chi ∧
      ¬Fin15AnchoredAtom4455 chi ∧
      ¬Fin15AnchoredAtom4456 chi ∧
      ¬Fin15AnchoredAtom4464 chi ∧
      ¬Fin15AnchoredAtom4465 chi ∧
      ¬Fin15AnchoredAtom4466 chi ∧
      ¬Fin15AnchoredAtom4489 chi ∧
      ¬Fin15AnchoredAtom4490 chi ∧
      ¬Fin15AnchoredAtom4491 chi ∧
      ¬Fin15AnchoredAtom4501 chi ∧
      ¬Fin15AnchoredAtom4524 chi ∧
      ¬Fin15AnchoredAtom4525 chi ∧
      ¬Fin15AnchoredAtom4526 chi ∧
      ¬Fin15AnchoredAtom4536 chi ∧
      ¬Fin15AnchoredAtom4566 chi ∧
      ¬Fin15AnchoredAtom4720 chi ∧
      ¬Fin15AnchoredAtom4721 chi ∧
      ¬Fin15AnchoredAtom4722 chi ∧
      ¬Fin15AnchoredAtom4732 chi ∧
      ¬Fin15AnchoredAtom4762 chi ∧
      ¬Fin15AnchoredAtom4797 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 6, 7, 9, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29393
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2529 Fin15AnchoredAtom2532 Fin15AnchoredAtom2533
    Fin15AnchoredAtom2534 Fin15AnchoredAtom2543 Fin15AnchoredAtom2544 Fin15AnchoredAtom2545
    Fin15AnchoredAtom2553 Fin15AnchoredAtom2554 Fin15AnchoredAtom2555 Fin15AnchoredAtom2564
    Fin15AnchoredAtom2565 Fin15AnchoredAtom2566 Fin15AnchoredAtom2574 Fin15AnchoredAtom2575
    Fin15AnchoredAtom2576 Fin15AnchoredAtom2599 Fin15AnchoredAtom2600 Fin15AnchoredAtom2601
    Fin15AnchoredAtom2611 Fin15AnchoredAtom2704 Fin15AnchoredAtom2705 Fin15AnchoredAtom2706
    Fin15AnchoredAtom2714 Fin15AnchoredAtom2715 Fin15AnchoredAtom2716 Fin15AnchoredAtom2739
    Fin15AnchoredAtom2740 Fin15AnchoredAtom2741 Fin15AnchoredAtom2751 Fin15AnchoredAtom2774
    Fin15AnchoredAtom2775 Fin15AnchoredAtom2776 Fin15AnchoredAtom2786 Fin15AnchoredAtom2816
    Fin15AnchoredAtom4454 Fin15AnchoredAtom4455 Fin15AnchoredAtom4456 Fin15AnchoredAtom4464
    Fin15AnchoredAtom4465 Fin15AnchoredAtom4466 Fin15AnchoredAtom4489 Fin15AnchoredAtom4490
    Fin15AnchoredAtom4491 Fin15AnchoredAtom4501 Fin15AnchoredAtom4524 Fin15AnchoredAtom4525
    Fin15AnchoredAtom4526 Fin15AnchoredAtom4536 Fin15AnchoredAtom4566 Fin15AnchoredAtom4720
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

theorem fin15Anchored_clause31582 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2530 chi ∧
      ¬Fin15AnchoredAtom2532 chi ∧
      ¬Fin15AnchoredAtom2533 chi ∧
      ¬Fin15AnchoredAtom2534 chi ∧
      ¬Fin15AnchoredAtom2547 chi ∧
      ¬Fin15AnchoredAtom2548 chi ∧
      ¬Fin15AnchoredAtom2549 chi ∧
      ¬Fin15AnchoredAtom2553 chi ∧
      ¬Fin15AnchoredAtom2554 chi ∧
      ¬Fin15AnchoredAtom2555 chi ∧
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
      ¬Fin15AnchoredAtom4458 chi ∧
      ¬Fin15AnchoredAtom4459 chi ∧
      ¬Fin15AnchoredAtom4460 chi ∧
      ¬Fin15AnchoredAtom4464 chi ∧
      ¬Fin15AnchoredAtom4465 chi ∧
      ¬Fin15AnchoredAtom4466 chi ∧
      ¬Fin15AnchoredAtom4495 chi ∧
      ¬Fin15AnchoredAtom4496 chi ∧
      ¬Fin15AnchoredAtom4497 chi ∧
      ¬Fin15AnchoredAtom4501 chi ∧
      ¬Fin15AnchoredAtom4530 chi ∧
      ¬Fin15AnchoredAtom4531 chi ∧
      ¬Fin15AnchoredAtom4532 chi ∧
      ¬Fin15AnchoredAtom4536 chi ∧
      ¬Fin15AnchoredAtom4570 chi ∧
      ¬Fin15AnchoredAtom4726 chi ∧
      ¬Fin15AnchoredAtom4727 chi ∧
      ¬Fin15AnchoredAtom4728 chi ∧
      ¬Fin15AnchoredAtom4732 chi ∧
      ¬Fin15AnchoredAtom4766 chi ∧
      ¬Fin15AnchoredAtom4801 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 6, 7, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29905
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2530 Fin15AnchoredAtom2532 Fin15AnchoredAtom2533
    Fin15AnchoredAtom2534 Fin15AnchoredAtom2547 Fin15AnchoredAtom2548 Fin15AnchoredAtom2549
    Fin15AnchoredAtom2553 Fin15AnchoredAtom2554 Fin15AnchoredAtom2555 Fin15AnchoredAtom2568
    Fin15AnchoredAtom2569 Fin15AnchoredAtom2570 Fin15AnchoredAtom2574 Fin15AnchoredAtom2575
    Fin15AnchoredAtom2576 Fin15AnchoredAtom2605 Fin15AnchoredAtom2606 Fin15AnchoredAtom2607
    Fin15AnchoredAtom2611 Fin15AnchoredAtom2708 Fin15AnchoredAtom2709 Fin15AnchoredAtom2710
    Fin15AnchoredAtom2714 Fin15AnchoredAtom2715 Fin15AnchoredAtom2716 Fin15AnchoredAtom2745
    Fin15AnchoredAtom2746 Fin15AnchoredAtom2747 Fin15AnchoredAtom2751 Fin15AnchoredAtom2780
    Fin15AnchoredAtom2781 Fin15AnchoredAtom2782 Fin15AnchoredAtom2786 Fin15AnchoredAtom2820
    Fin15AnchoredAtom4458 Fin15AnchoredAtom4459 Fin15AnchoredAtom4460 Fin15AnchoredAtom4464
    Fin15AnchoredAtom4465 Fin15AnchoredAtom4466 Fin15AnchoredAtom4495 Fin15AnchoredAtom4496
    Fin15AnchoredAtom4497 Fin15AnchoredAtom4501 Fin15AnchoredAtom4530 Fin15AnchoredAtom4531
    Fin15AnchoredAtom4532 Fin15AnchoredAtom4536 Fin15AnchoredAtom4570 Fin15AnchoredAtom4726
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

theorem fin15Anchored_clause31583 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2535 chi ∧
      ¬Fin15AnchoredAtom2536 chi ∧
      ¬Fin15AnchoredAtom2538 chi ∧
      ¬Fin15AnchoredAtom2539 chi ∧
      ¬Fin15AnchoredAtom2541 chi ∧
      ¬Fin15AnchoredAtom2543 chi ∧
      ¬Fin15AnchoredAtom2544 chi ∧
      ¬Fin15AnchoredAtom2547 chi ∧
      ¬Fin15AnchoredAtom2548 chi ∧
      ¬Fin15AnchoredAtom2553 chi ∧
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
      ¬Fin15AnchoredAtom4467 chi ∧
      ¬Fin15AnchoredAtom4469 chi ∧
      ¬Fin15AnchoredAtom4470 chi ∧
      ¬Fin15AnchoredAtom4473 chi ∧
      ¬Fin15AnchoredAtom4474 chi ∧
      ¬Fin15AnchoredAtom4479 chi ∧
      ¬Fin15AnchoredAtom4483 chi ∧
      ¬Fin15AnchoredAtom4484 chi ∧
      ¬Fin15AnchoredAtom4489 chi ∧
      ¬Fin15AnchoredAtom4495 chi ∧
      ¬Fin15AnchoredAtom4538 chi ∧
      ¬Fin15AnchoredAtom4539 chi ∧
      ¬Fin15AnchoredAtom4544 chi ∧
      ¬Fin15AnchoredAtom4550 chi ∧
      ¬Fin15AnchoredAtom4560 chi ∧
      ¬Fin15AnchoredAtom4734 chi ∧
      ¬Fin15AnchoredAtom4735 chi ∧
      ¬Fin15AnchoredAtom4740 chi ∧
      ¬Fin15AnchoredAtom4746 chi ∧
      ¬Fin15AnchoredAtom4756 chi ∧
      ¬Fin15AnchoredAtom4806 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 6, 8, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask14161
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2535 Fin15AnchoredAtom2536 Fin15AnchoredAtom2538
    Fin15AnchoredAtom2539 Fin15AnchoredAtom2541 Fin15AnchoredAtom2543 Fin15AnchoredAtom2544
    Fin15AnchoredAtom2547 Fin15AnchoredAtom2548 Fin15AnchoredAtom2553 Fin15AnchoredAtom2577
    Fin15AnchoredAtom2579 Fin15AnchoredAtom2580 Fin15AnchoredAtom2583 Fin15AnchoredAtom2584
    Fin15AnchoredAtom2589 Fin15AnchoredAtom2593 Fin15AnchoredAtom2594 Fin15AnchoredAtom2599
    Fin15AnchoredAtom2605 Fin15AnchoredAtom2717 Fin15AnchoredAtom2719 Fin15AnchoredAtom2720
    Fin15AnchoredAtom2723 Fin15AnchoredAtom2724 Fin15AnchoredAtom2729 Fin15AnchoredAtom2733
    Fin15AnchoredAtom2734 Fin15AnchoredAtom2739 Fin15AnchoredAtom2745 Fin15AnchoredAtom2788
    Fin15AnchoredAtom2789 Fin15AnchoredAtom2794 Fin15AnchoredAtom2800 Fin15AnchoredAtom2810
    Fin15AnchoredAtom4467 Fin15AnchoredAtom4469 Fin15AnchoredAtom4470 Fin15AnchoredAtom4473
    Fin15AnchoredAtom4474 Fin15AnchoredAtom4479 Fin15AnchoredAtom4483 Fin15AnchoredAtom4484
    Fin15AnchoredAtom4489 Fin15AnchoredAtom4495 Fin15AnchoredAtom4538 Fin15AnchoredAtom4539
    Fin15AnchoredAtom4544 Fin15AnchoredAtom4550 Fin15AnchoredAtom4560 Fin15AnchoredAtom4734
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

theorem fin15Anchored_clause31584 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2535 chi ∧
      ¬Fin15AnchoredAtom2536 chi ∧
      ¬Fin15AnchoredAtom2538 chi ∧
      ¬Fin15AnchoredAtom2540 chi ∧
      ¬Fin15AnchoredAtom2541 chi ∧
      ¬Fin15AnchoredAtom2543 chi ∧
      ¬Fin15AnchoredAtom2545 chi ∧
      ¬Fin15AnchoredAtom2547 chi ∧
      ¬Fin15AnchoredAtom2549 chi ∧
      ¬Fin15AnchoredAtom2554 chi ∧
      ¬Fin15AnchoredAtom2577 chi ∧
      ¬Fin15AnchoredAtom2579 chi ∧
      ¬Fin15AnchoredAtom2581 chi ∧
      ¬Fin15AnchoredAtom2583 chi ∧
      ¬Fin15AnchoredAtom2585 chi ∧
      ¬Fin15AnchoredAtom2590 chi ∧
      ¬Fin15AnchoredAtom2593 chi ∧
      ¬Fin15AnchoredAtom2595 chi ∧
      ¬Fin15AnchoredAtom2600 chi ∧
      ¬Fin15AnchoredAtom2606 chi ∧
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
      ¬Fin15AnchoredAtom4467 chi ∧
      ¬Fin15AnchoredAtom4469 chi ∧
      ¬Fin15AnchoredAtom4471 chi ∧
      ¬Fin15AnchoredAtom4473 chi ∧
      ¬Fin15AnchoredAtom4475 chi ∧
      ¬Fin15AnchoredAtom4480 chi ∧
      ¬Fin15AnchoredAtom4483 chi ∧
      ¬Fin15AnchoredAtom4485 chi ∧
      ¬Fin15AnchoredAtom4490 chi ∧
      ¬Fin15AnchoredAtom4496 chi ∧
      ¬Fin15AnchoredAtom4538 chi ∧
      ¬Fin15AnchoredAtom4540 chi ∧
      ¬Fin15AnchoredAtom4545 chi ∧
      ¬Fin15AnchoredAtom4551 chi ∧
      ¬Fin15AnchoredAtom4561 chi ∧
      ¬Fin15AnchoredAtom4734 chi ∧
      ¬Fin15AnchoredAtom4736 chi ∧
      ¬Fin15AnchoredAtom4741 chi ∧
      ¬Fin15AnchoredAtom4747 chi ∧
      ¬Fin15AnchoredAtom4757 chi ∧
      ¬Fin15AnchoredAtom4807 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 6, 8, 9, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22353
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2535 Fin15AnchoredAtom2536 Fin15AnchoredAtom2538
    Fin15AnchoredAtom2540 Fin15AnchoredAtom2541 Fin15AnchoredAtom2543 Fin15AnchoredAtom2545
    Fin15AnchoredAtom2547 Fin15AnchoredAtom2549 Fin15AnchoredAtom2554 Fin15AnchoredAtom2577
    Fin15AnchoredAtom2579 Fin15AnchoredAtom2581 Fin15AnchoredAtom2583 Fin15AnchoredAtom2585
    Fin15AnchoredAtom2590 Fin15AnchoredAtom2593 Fin15AnchoredAtom2595 Fin15AnchoredAtom2600
    Fin15AnchoredAtom2606 Fin15AnchoredAtom2717 Fin15AnchoredAtom2719 Fin15AnchoredAtom2721
    Fin15AnchoredAtom2723 Fin15AnchoredAtom2725 Fin15AnchoredAtom2730 Fin15AnchoredAtom2733
    Fin15AnchoredAtom2735 Fin15AnchoredAtom2740 Fin15AnchoredAtom2746 Fin15AnchoredAtom2788
    Fin15AnchoredAtom2790 Fin15AnchoredAtom2795 Fin15AnchoredAtom2801 Fin15AnchoredAtom2811
    Fin15AnchoredAtom4467 Fin15AnchoredAtom4469 Fin15AnchoredAtom4471 Fin15AnchoredAtom4473
    Fin15AnchoredAtom4475 Fin15AnchoredAtom4480 Fin15AnchoredAtom4483 Fin15AnchoredAtom4485
    Fin15AnchoredAtom4490 Fin15AnchoredAtom4496 Fin15AnchoredAtom4538 Fin15AnchoredAtom4540
    Fin15AnchoredAtom4545 Fin15AnchoredAtom4551 Fin15AnchoredAtom4561 Fin15AnchoredAtom4734
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

theorem fin15Anchored_clause31585 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2535 chi ∧
      ¬Fin15AnchoredAtom2536 chi ∧
      ¬Fin15AnchoredAtom2539 chi ∧
      ¬Fin15AnchoredAtom2540 chi ∧
      ¬Fin15AnchoredAtom2541 chi ∧
      ¬Fin15AnchoredAtom2544 chi ∧
      ¬Fin15AnchoredAtom2545 chi ∧
      ¬Fin15AnchoredAtom2548 chi ∧
      ¬Fin15AnchoredAtom2549 chi ∧
      ¬Fin15AnchoredAtom2555 chi ∧
      ¬Fin15AnchoredAtom2577 chi ∧
      ¬Fin15AnchoredAtom2580 chi ∧
      ¬Fin15AnchoredAtom2581 chi ∧
      ¬Fin15AnchoredAtom2584 chi ∧
      ¬Fin15AnchoredAtom2585 chi ∧
      ¬Fin15AnchoredAtom2591 chi ∧
      ¬Fin15AnchoredAtom2594 chi ∧
      ¬Fin15AnchoredAtom2595 chi ∧
      ¬Fin15AnchoredAtom2601 chi ∧
      ¬Fin15AnchoredAtom2607 chi ∧
      ¬Fin15AnchoredAtom2717 chi ∧
      ¬Fin15AnchoredAtom2720 chi ∧
      ¬Fin15AnchoredAtom2721 chi ∧
      ¬Fin15AnchoredAtom2724 chi ∧
      ¬Fin15AnchoredAtom2725 chi ∧
      ¬Fin15AnchoredAtom2731 chi ∧
      ¬Fin15AnchoredAtom2734 chi ∧
      ¬Fin15AnchoredAtom2735 chi ∧
      ¬Fin15AnchoredAtom2741 chi ∧
      ¬Fin15AnchoredAtom2747 chi ∧
      ¬Fin15AnchoredAtom2789 chi ∧
      ¬Fin15AnchoredAtom2790 chi ∧
      ¬Fin15AnchoredAtom2796 chi ∧
      ¬Fin15AnchoredAtom2802 chi ∧
      ¬Fin15AnchoredAtom2812 chi ∧
      ¬Fin15AnchoredAtom4467 chi ∧
      ¬Fin15AnchoredAtom4470 chi ∧
      ¬Fin15AnchoredAtom4471 chi ∧
      ¬Fin15AnchoredAtom4474 chi ∧
      ¬Fin15AnchoredAtom4475 chi ∧
      ¬Fin15AnchoredAtom4481 chi ∧
      ¬Fin15AnchoredAtom4484 chi ∧
      ¬Fin15AnchoredAtom4485 chi ∧
      ¬Fin15AnchoredAtom4491 chi ∧
      ¬Fin15AnchoredAtom4497 chi ∧
      ¬Fin15AnchoredAtom4539 chi ∧
      ¬Fin15AnchoredAtom4540 chi ∧
      ¬Fin15AnchoredAtom4546 chi ∧
      ¬Fin15AnchoredAtom4552 chi ∧
      ¬Fin15AnchoredAtom4562 chi ∧
      ¬Fin15AnchoredAtom4735 chi ∧
      ¬Fin15AnchoredAtom4736 chi ∧
      ¬Fin15AnchoredAtom4742 chi ∧
      ¬Fin15AnchoredAtom4748 chi ∧
      ¬Fin15AnchoredAtom4758 chi ∧
      ¬Fin15AnchoredAtom4808 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 6, 8, 9, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26449
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2535 Fin15AnchoredAtom2536 Fin15AnchoredAtom2539
    Fin15AnchoredAtom2540 Fin15AnchoredAtom2541 Fin15AnchoredAtom2544 Fin15AnchoredAtom2545
    Fin15AnchoredAtom2548 Fin15AnchoredAtom2549 Fin15AnchoredAtom2555 Fin15AnchoredAtom2577
    Fin15AnchoredAtom2580 Fin15AnchoredAtom2581 Fin15AnchoredAtom2584 Fin15AnchoredAtom2585
    Fin15AnchoredAtom2591 Fin15AnchoredAtom2594 Fin15AnchoredAtom2595 Fin15AnchoredAtom2601
    Fin15AnchoredAtom2607 Fin15AnchoredAtom2717 Fin15AnchoredAtom2720 Fin15AnchoredAtom2721
    Fin15AnchoredAtom2724 Fin15AnchoredAtom2725 Fin15AnchoredAtom2731 Fin15AnchoredAtom2734
    Fin15AnchoredAtom2735 Fin15AnchoredAtom2741 Fin15AnchoredAtom2747 Fin15AnchoredAtom2789
    Fin15AnchoredAtom2790 Fin15AnchoredAtom2796 Fin15AnchoredAtom2802 Fin15AnchoredAtom2812
    Fin15AnchoredAtom4467 Fin15AnchoredAtom4470 Fin15AnchoredAtom4471 Fin15AnchoredAtom4474
    Fin15AnchoredAtom4475 Fin15AnchoredAtom4481 Fin15AnchoredAtom4484 Fin15AnchoredAtom4485
    Fin15AnchoredAtom4491 Fin15AnchoredAtom4497 Fin15AnchoredAtom4539 Fin15AnchoredAtom4540
    Fin15AnchoredAtom4546 Fin15AnchoredAtom4552 Fin15AnchoredAtom4562 Fin15AnchoredAtom4735
    Fin15AnchoredAtom4736 Fin15AnchoredAtom4742 Fin15AnchoredAtom4748 Fin15AnchoredAtom4758
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

theorem fin15Anchored_clause31586 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2535 chi ∧
      ¬Fin15AnchoredAtom2538 chi ∧
      ¬Fin15AnchoredAtom2539 chi ∧
      ¬Fin15AnchoredAtom2540 chi ∧
      ¬Fin15AnchoredAtom2543 chi ∧
      ¬Fin15AnchoredAtom2544 chi ∧
      ¬Fin15AnchoredAtom2545 chi ∧
      ¬Fin15AnchoredAtom2553 chi ∧
      ¬Fin15AnchoredAtom2554 chi ∧
      ¬Fin15AnchoredAtom2555 chi ∧
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
      ¬Fin15AnchoredAtom2719 chi ∧
      ¬Fin15AnchoredAtom2720 chi ∧
      ¬Fin15AnchoredAtom2721 chi ∧
      ¬Fin15AnchoredAtom2729 chi ∧
      ¬Fin15AnchoredAtom2730 chi ∧
      ¬Fin15AnchoredAtom2731 chi ∧
      ¬Fin15AnchoredAtom2739 chi ∧
      ¬Fin15AnchoredAtom2740 chi ∧
      ¬Fin15AnchoredAtom2741 chi ∧
      ¬Fin15AnchoredAtom2751 chi ∧
      ¬Fin15AnchoredAtom2794 chi ∧
      ¬Fin15AnchoredAtom2795 chi ∧
      ¬Fin15AnchoredAtom2796 chi ∧
      ¬Fin15AnchoredAtom2806 chi ∧
      ¬Fin15AnchoredAtom2816 chi ∧
      ¬Fin15AnchoredAtom4469 chi ∧
      ¬Fin15AnchoredAtom4470 chi ∧
      ¬Fin15AnchoredAtom4471 chi ∧
      ¬Fin15AnchoredAtom4479 chi ∧
      ¬Fin15AnchoredAtom4480 chi ∧
      ¬Fin15AnchoredAtom4481 chi ∧
      ¬Fin15AnchoredAtom4489 chi ∧
      ¬Fin15AnchoredAtom4490 chi ∧
      ¬Fin15AnchoredAtom4491 chi ∧
      ¬Fin15AnchoredAtom4501 chi ∧
      ¬Fin15AnchoredAtom4544 chi ∧
      ¬Fin15AnchoredAtom4545 chi ∧
      ¬Fin15AnchoredAtom4546 chi ∧
      ¬Fin15AnchoredAtom4556 chi ∧
      ¬Fin15AnchoredAtom4566 chi ∧
      ¬Fin15AnchoredAtom4740 chi ∧
      ¬Fin15AnchoredAtom4741 chi ∧
      ¬Fin15AnchoredAtom4742 chi ∧
      ¬Fin15AnchoredAtom4752 chi ∧
      ¬Fin15AnchoredAtom4762 chi ∧
      ¬Fin15AnchoredAtom4812 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 6, 8, 9, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29521
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2535 Fin15AnchoredAtom2538 Fin15AnchoredAtom2539
    Fin15AnchoredAtom2540 Fin15AnchoredAtom2543 Fin15AnchoredAtom2544 Fin15AnchoredAtom2545
    Fin15AnchoredAtom2553 Fin15AnchoredAtom2554 Fin15AnchoredAtom2555 Fin15AnchoredAtom2579
    Fin15AnchoredAtom2580 Fin15AnchoredAtom2581 Fin15AnchoredAtom2589 Fin15AnchoredAtom2590
    Fin15AnchoredAtom2591 Fin15AnchoredAtom2599 Fin15AnchoredAtom2600 Fin15AnchoredAtom2601
    Fin15AnchoredAtom2611 Fin15AnchoredAtom2719 Fin15AnchoredAtom2720 Fin15AnchoredAtom2721
    Fin15AnchoredAtom2729 Fin15AnchoredAtom2730 Fin15AnchoredAtom2731 Fin15AnchoredAtom2739
    Fin15AnchoredAtom2740 Fin15AnchoredAtom2741 Fin15AnchoredAtom2751 Fin15AnchoredAtom2794
    Fin15AnchoredAtom2795 Fin15AnchoredAtom2796 Fin15AnchoredAtom2806 Fin15AnchoredAtom2816
    Fin15AnchoredAtom4469 Fin15AnchoredAtom4470 Fin15AnchoredAtom4471 Fin15AnchoredAtom4479
    Fin15AnchoredAtom4480 Fin15AnchoredAtom4481 Fin15AnchoredAtom4489 Fin15AnchoredAtom4490
    Fin15AnchoredAtom4491 Fin15AnchoredAtom4501 Fin15AnchoredAtom4544 Fin15AnchoredAtom4545
    Fin15AnchoredAtom4546 Fin15AnchoredAtom4556 Fin15AnchoredAtom4566 Fin15AnchoredAtom4740
    Fin15AnchoredAtom4741 Fin15AnchoredAtom4742 Fin15AnchoredAtom4752 Fin15AnchoredAtom4762
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

theorem fin15Anchored_clause31587 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2536 chi ∧
      ¬Fin15AnchoredAtom2538 chi ∧
      ¬Fin15AnchoredAtom2539 chi ∧
      ¬Fin15AnchoredAtom2540 chi ∧
      ¬Fin15AnchoredAtom2547 chi ∧
      ¬Fin15AnchoredAtom2548 chi ∧
      ¬Fin15AnchoredAtom2549 chi ∧
      ¬Fin15AnchoredAtom2553 chi ∧
      ¬Fin15AnchoredAtom2554 chi ∧
      ¬Fin15AnchoredAtom2555 chi ∧
      ¬Fin15AnchoredAtom2583 chi ∧
      ¬Fin15AnchoredAtom2584 chi ∧
      ¬Fin15AnchoredAtom2585 chi ∧
      ¬Fin15AnchoredAtom2589 chi ∧
      ¬Fin15AnchoredAtom2590 chi ∧
      ¬Fin15AnchoredAtom2591 chi ∧
      ¬Fin15AnchoredAtom2605 chi ∧
      ¬Fin15AnchoredAtom2606 chi ∧
      ¬Fin15AnchoredAtom2607 chi ∧
      ¬Fin15AnchoredAtom2611 chi ∧
      ¬Fin15AnchoredAtom2723 chi ∧
      ¬Fin15AnchoredAtom2724 chi ∧
      ¬Fin15AnchoredAtom2725 chi ∧
      ¬Fin15AnchoredAtom2729 chi ∧
      ¬Fin15AnchoredAtom2730 chi ∧
      ¬Fin15AnchoredAtom2731 chi ∧
      ¬Fin15AnchoredAtom2745 chi ∧
      ¬Fin15AnchoredAtom2746 chi ∧
      ¬Fin15AnchoredAtom2747 chi ∧
      ¬Fin15AnchoredAtom2751 chi ∧
      ¬Fin15AnchoredAtom2800 chi ∧
      ¬Fin15AnchoredAtom2801 chi ∧
      ¬Fin15AnchoredAtom2802 chi ∧
      ¬Fin15AnchoredAtom2806 chi ∧
      ¬Fin15AnchoredAtom2820 chi ∧
      ¬Fin15AnchoredAtom4473 chi ∧
      ¬Fin15AnchoredAtom4474 chi ∧
      ¬Fin15AnchoredAtom4475 chi ∧
      ¬Fin15AnchoredAtom4479 chi ∧
      ¬Fin15AnchoredAtom4480 chi ∧
      ¬Fin15AnchoredAtom4481 chi ∧
      ¬Fin15AnchoredAtom4495 chi ∧
      ¬Fin15AnchoredAtom4496 chi ∧
      ¬Fin15AnchoredAtom4497 chi ∧
      ¬Fin15AnchoredAtom4501 chi ∧
      ¬Fin15AnchoredAtom4550 chi ∧
      ¬Fin15AnchoredAtom4551 chi ∧
      ¬Fin15AnchoredAtom4552 chi ∧
      ¬Fin15AnchoredAtom4556 chi ∧
      ¬Fin15AnchoredAtom4570 chi ∧
      ¬Fin15AnchoredAtom4746 chi ∧
      ¬Fin15AnchoredAtom4747 chi ∧
      ¬Fin15AnchoredAtom4748 chi ∧
      ¬Fin15AnchoredAtom4752 chi ∧
      ¬Fin15AnchoredAtom4766 chi ∧
      ¬Fin15AnchoredAtom4816 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 6, 8, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask30033
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2536 Fin15AnchoredAtom2538 Fin15AnchoredAtom2539
    Fin15AnchoredAtom2540 Fin15AnchoredAtom2547 Fin15AnchoredAtom2548 Fin15AnchoredAtom2549
    Fin15AnchoredAtom2553 Fin15AnchoredAtom2554 Fin15AnchoredAtom2555 Fin15AnchoredAtom2583
    Fin15AnchoredAtom2584 Fin15AnchoredAtom2585 Fin15AnchoredAtom2589 Fin15AnchoredAtom2590
    Fin15AnchoredAtom2591 Fin15AnchoredAtom2605 Fin15AnchoredAtom2606 Fin15AnchoredAtom2607
    Fin15AnchoredAtom2611 Fin15AnchoredAtom2723 Fin15AnchoredAtom2724 Fin15AnchoredAtom2725
    Fin15AnchoredAtom2729 Fin15AnchoredAtom2730 Fin15AnchoredAtom2731 Fin15AnchoredAtom2745
    Fin15AnchoredAtom2746 Fin15AnchoredAtom2747 Fin15AnchoredAtom2751 Fin15AnchoredAtom2800
    Fin15AnchoredAtom2801 Fin15AnchoredAtom2802 Fin15AnchoredAtom2806 Fin15AnchoredAtom2820
    Fin15AnchoredAtom4473 Fin15AnchoredAtom4474 Fin15AnchoredAtom4475 Fin15AnchoredAtom4479
    Fin15AnchoredAtom4480 Fin15AnchoredAtom4481 Fin15AnchoredAtom4495 Fin15AnchoredAtom4496
    Fin15AnchoredAtom4497 Fin15AnchoredAtom4501 Fin15AnchoredAtom4550 Fin15AnchoredAtom4551
    Fin15AnchoredAtom4552 Fin15AnchoredAtom4556 Fin15AnchoredAtom4570 Fin15AnchoredAtom4746
    Fin15AnchoredAtom4747 Fin15AnchoredAtom4748 Fin15AnchoredAtom4752 Fin15AnchoredAtom4766
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

theorem fin15Anchored_clause31588 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2541 chi ∧
      ¬Fin15AnchoredAtom2542 chi ∧
      ¬Fin15AnchoredAtom2543 chi ∧
      ¬Fin15AnchoredAtom2545 chi ∧
      ¬Fin15AnchoredAtom2546 chi ∧
      ¬Fin15AnchoredAtom2547 chi ∧
      ¬Fin15AnchoredAtom2549 chi ∧
      ¬Fin15AnchoredAtom2550 chi ∧
      ¬Fin15AnchoredAtom2552 chi ∧
      ¬Fin15AnchoredAtom2554 chi ∧
      ¬Fin15AnchoredAtom2592 chi ∧
      ¬Fin15AnchoredAtom2593 chi ∧
      ¬Fin15AnchoredAtom2595 chi ∧
      ¬Fin15AnchoredAtom2596 chi ∧
      ¬Fin15AnchoredAtom2598 chi ∧
      ¬Fin15AnchoredAtom2600 chi ∧
      ¬Fin15AnchoredAtom2602 chi ∧
      ¬Fin15AnchoredAtom2604 chi ∧
      ¬Fin15AnchoredAtom2606 chi ∧
      ¬Fin15AnchoredAtom2609 chi ∧
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
      ¬Fin15AnchoredAtom4482 chi ∧
      ¬Fin15AnchoredAtom4483 chi ∧
      ¬Fin15AnchoredAtom4485 chi ∧
      ¬Fin15AnchoredAtom4486 chi ∧
      ¬Fin15AnchoredAtom4488 chi ∧
      ¬Fin15AnchoredAtom4490 chi ∧
      ¬Fin15AnchoredAtom4492 chi ∧
      ¬Fin15AnchoredAtom4494 chi ∧
      ¬Fin15AnchoredAtom4496 chi ∧
      ¬Fin15AnchoredAtom4499 chi ∧
      ¬Fin15AnchoredAtom4557 chi ∧
      ¬Fin15AnchoredAtom4559 chi ∧
      ¬Fin15AnchoredAtom4561 chi ∧
      ¬Fin15AnchoredAtom4564 chi ∧
      ¬Fin15AnchoredAtom4568 chi ∧
      ¬Fin15AnchoredAtom4753 chi ∧
      ¬Fin15AnchoredAtom4755 chi ∧
      ¬Fin15AnchoredAtom4757 chi ∧
      ¬Fin15AnchoredAtom4760 chi ∧
      ¬Fin15AnchoredAtom4764 chi ∧
      ¬Fin15AnchoredAtom4819 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 6, 9, 10, 11, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask24145
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2541 Fin15AnchoredAtom2542 Fin15AnchoredAtom2543
    Fin15AnchoredAtom2545 Fin15AnchoredAtom2546 Fin15AnchoredAtom2547 Fin15AnchoredAtom2549
    Fin15AnchoredAtom2550 Fin15AnchoredAtom2552 Fin15AnchoredAtom2554 Fin15AnchoredAtom2592
    Fin15AnchoredAtom2593 Fin15AnchoredAtom2595 Fin15AnchoredAtom2596 Fin15AnchoredAtom2598
    Fin15AnchoredAtom2600 Fin15AnchoredAtom2602 Fin15AnchoredAtom2604 Fin15AnchoredAtom2606
    Fin15AnchoredAtom2609 Fin15AnchoredAtom2732 Fin15AnchoredAtom2733 Fin15AnchoredAtom2735
    Fin15AnchoredAtom2736 Fin15AnchoredAtom2738 Fin15AnchoredAtom2740 Fin15AnchoredAtom2742
    Fin15AnchoredAtom2744 Fin15AnchoredAtom2746 Fin15AnchoredAtom2749 Fin15AnchoredAtom2807
    Fin15AnchoredAtom2809 Fin15AnchoredAtom2811 Fin15AnchoredAtom2814 Fin15AnchoredAtom2818
    Fin15AnchoredAtom4482 Fin15AnchoredAtom4483 Fin15AnchoredAtom4485 Fin15AnchoredAtom4486
    Fin15AnchoredAtom4488 Fin15AnchoredAtom4490 Fin15AnchoredAtom4492 Fin15AnchoredAtom4494
    Fin15AnchoredAtom4496 Fin15AnchoredAtom4499 Fin15AnchoredAtom4557 Fin15AnchoredAtom4559
    Fin15AnchoredAtom4561 Fin15AnchoredAtom4564 Fin15AnchoredAtom4568 Fin15AnchoredAtom4753
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

theorem fin15Anchored_clause31589 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2541 chi ∧
      ¬Fin15AnchoredAtom2543 chi ∧
      ¬Fin15AnchoredAtom2544 chi ∧
      ¬Fin15AnchoredAtom2545 chi ∧
      ¬Fin15AnchoredAtom2547 chi ∧
      ¬Fin15AnchoredAtom2548 chi ∧
      ¬Fin15AnchoredAtom2549 chi ∧
      ¬Fin15AnchoredAtom2553 chi ∧
      ¬Fin15AnchoredAtom2554 chi ∧
      ¬Fin15AnchoredAtom2555 chi ∧
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
      ¬Fin15AnchoredAtom4483 chi ∧
      ¬Fin15AnchoredAtom4484 chi ∧
      ¬Fin15AnchoredAtom4485 chi ∧
      ¬Fin15AnchoredAtom4489 chi ∧
      ¬Fin15AnchoredAtom4490 chi ∧
      ¬Fin15AnchoredAtom4491 chi ∧
      ¬Fin15AnchoredAtom4495 chi ∧
      ¬Fin15AnchoredAtom4496 chi ∧
      ¬Fin15AnchoredAtom4497 chi ∧
      ¬Fin15AnchoredAtom4501 chi ∧
      ¬Fin15AnchoredAtom4560 chi ∧
      ¬Fin15AnchoredAtom4561 chi ∧
      ¬Fin15AnchoredAtom4562 chi ∧
      ¬Fin15AnchoredAtom4566 chi ∧
      ¬Fin15AnchoredAtom4570 chi ∧
      ¬Fin15AnchoredAtom4756 chi ∧
      ¬Fin15AnchoredAtom4757 chi ∧
      ¬Fin15AnchoredAtom4758 chi ∧
      ¬Fin15AnchoredAtom4762 chi ∧
      ¬Fin15AnchoredAtom4766 chi ∧
      ¬Fin15AnchoredAtom4821 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 6, 9, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask30289
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2541 Fin15AnchoredAtom2543 Fin15AnchoredAtom2544
    Fin15AnchoredAtom2545 Fin15AnchoredAtom2547 Fin15AnchoredAtom2548 Fin15AnchoredAtom2549
    Fin15AnchoredAtom2553 Fin15AnchoredAtom2554 Fin15AnchoredAtom2555 Fin15AnchoredAtom2593
    Fin15AnchoredAtom2594 Fin15AnchoredAtom2595 Fin15AnchoredAtom2599 Fin15AnchoredAtom2600
    Fin15AnchoredAtom2601 Fin15AnchoredAtom2605 Fin15AnchoredAtom2606 Fin15AnchoredAtom2607
    Fin15AnchoredAtom2611 Fin15AnchoredAtom2733 Fin15AnchoredAtom2734 Fin15AnchoredAtom2735
    Fin15AnchoredAtom2739 Fin15AnchoredAtom2740 Fin15AnchoredAtom2741 Fin15AnchoredAtom2745
    Fin15AnchoredAtom2746 Fin15AnchoredAtom2747 Fin15AnchoredAtom2751 Fin15AnchoredAtom2810
    Fin15AnchoredAtom2811 Fin15AnchoredAtom2812 Fin15AnchoredAtom2816 Fin15AnchoredAtom2820
    Fin15AnchoredAtom4483 Fin15AnchoredAtom4484 Fin15AnchoredAtom4485 Fin15AnchoredAtom4489
    Fin15AnchoredAtom4490 Fin15AnchoredAtom4491 Fin15AnchoredAtom4495 Fin15AnchoredAtom4496
    Fin15AnchoredAtom4497 Fin15AnchoredAtom4501 Fin15AnchoredAtom4560 Fin15AnchoredAtom4561
    Fin15AnchoredAtom4562 Fin15AnchoredAtom4566 Fin15AnchoredAtom4570 Fin15AnchoredAtom4756
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

theorem fin15Anchored_clause31590 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2556 chi ∧
      ¬Fin15AnchoredAtom2557 chi ∧
      ¬Fin15AnchoredAtom2559 chi ∧
      ¬Fin15AnchoredAtom2560 chi ∧
      ¬Fin15AnchoredAtom2562 chi ∧
      ¬Fin15AnchoredAtom2564 chi ∧
      ¬Fin15AnchoredAtom2565 chi ∧
      ¬Fin15AnchoredAtom2568 chi ∧
      ¬Fin15AnchoredAtom2569 chi ∧
      ¬Fin15AnchoredAtom2574 chi ∧
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
      ¬Fin15AnchoredAtom4502 chi ∧
      ¬Fin15AnchoredAtom4504 chi ∧
      ¬Fin15AnchoredAtom4505 chi ∧
      ¬Fin15AnchoredAtom4508 chi ∧
      ¬Fin15AnchoredAtom4509 chi ∧
      ¬Fin15AnchoredAtom4514 chi ∧
      ¬Fin15AnchoredAtom4518 chi ∧
      ¬Fin15AnchoredAtom4519 chi ∧
      ¬Fin15AnchoredAtom4524 chi ∧
      ¬Fin15AnchoredAtom4530 chi ∧
      ¬Fin15AnchoredAtom4538 chi ∧
      ¬Fin15AnchoredAtom4539 chi ∧
      ¬Fin15AnchoredAtom4544 chi ∧
      ¬Fin15AnchoredAtom4550 chi ∧
      ¬Fin15AnchoredAtom4560 chi ∧
      ¬Fin15AnchoredAtom4769 chi ∧
      ¬Fin15AnchoredAtom4770 chi ∧
      ¬Fin15AnchoredAtom4775 chi ∧
      ¬Fin15AnchoredAtom4781 chi ∧
      ¬Fin15AnchoredAtom4791 chi ∧
      ¬Fin15AnchoredAtom4806 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 7, 8, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask14225
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2556 Fin15AnchoredAtom2557 Fin15AnchoredAtom2559
    Fin15AnchoredAtom2560 Fin15AnchoredAtom2562 Fin15AnchoredAtom2564 Fin15AnchoredAtom2565
    Fin15AnchoredAtom2568 Fin15AnchoredAtom2569 Fin15AnchoredAtom2574 Fin15AnchoredAtom2577
    Fin15AnchoredAtom2579 Fin15AnchoredAtom2580 Fin15AnchoredAtom2583 Fin15AnchoredAtom2584
    Fin15AnchoredAtom2589 Fin15AnchoredAtom2593 Fin15AnchoredAtom2594 Fin15AnchoredAtom2599
    Fin15AnchoredAtom2605 Fin15AnchoredAtom2752 Fin15AnchoredAtom2754 Fin15AnchoredAtom2755
    Fin15AnchoredAtom2758 Fin15AnchoredAtom2759 Fin15AnchoredAtom2764 Fin15AnchoredAtom2768
    Fin15AnchoredAtom2769 Fin15AnchoredAtom2774 Fin15AnchoredAtom2780 Fin15AnchoredAtom2788
    Fin15AnchoredAtom2789 Fin15AnchoredAtom2794 Fin15AnchoredAtom2800 Fin15AnchoredAtom2810
    Fin15AnchoredAtom4502 Fin15AnchoredAtom4504 Fin15AnchoredAtom4505 Fin15AnchoredAtom4508
    Fin15AnchoredAtom4509 Fin15AnchoredAtom4514 Fin15AnchoredAtom4518 Fin15AnchoredAtom4519
    Fin15AnchoredAtom4524 Fin15AnchoredAtom4530 Fin15AnchoredAtom4538 Fin15AnchoredAtom4539
    Fin15AnchoredAtom4544 Fin15AnchoredAtom4550 Fin15AnchoredAtom4560 Fin15AnchoredAtom4769
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

theorem fin15Anchored_clause31591 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2556 chi ∧
      ¬Fin15AnchoredAtom2557 chi ∧
      ¬Fin15AnchoredAtom2559 chi ∧
      ¬Fin15AnchoredAtom2561 chi ∧
      ¬Fin15AnchoredAtom2562 chi ∧
      ¬Fin15AnchoredAtom2564 chi ∧
      ¬Fin15AnchoredAtom2566 chi ∧
      ¬Fin15AnchoredAtom2568 chi ∧
      ¬Fin15AnchoredAtom2570 chi ∧
      ¬Fin15AnchoredAtom2575 chi ∧
      ¬Fin15AnchoredAtom2577 chi ∧
      ¬Fin15AnchoredAtom2579 chi ∧
      ¬Fin15AnchoredAtom2581 chi ∧
      ¬Fin15AnchoredAtom2583 chi ∧
      ¬Fin15AnchoredAtom2585 chi ∧
      ¬Fin15AnchoredAtom2590 chi ∧
      ¬Fin15AnchoredAtom2593 chi ∧
      ¬Fin15AnchoredAtom2595 chi ∧
      ¬Fin15AnchoredAtom2600 chi ∧
      ¬Fin15AnchoredAtom2606 chi ∧
      ¬Fin15AnchoredAtom2752 chi ∧
      ¬Fin15AnchoredAtom2754 chi ∧
      ¬Fin15AnchoredAtom2756 chi ∧
      ¬Fin15AnchoredAtom2758 chi ∧
      ¬Fin15AnchoredAtom2760 chi ∧
      ¬Fin15AnchoredAtom2765 chi ∧
      ¬Fin15AnchoredAtom2768 chi ∧
      ¬Fin15AnchoredAtom2770 chi ∧
      ¬Fin15AnchoredAtom2775 chi ∧
      ¬Fin15AnchoredAtom2781 chi ∧
      ¬Fin15AnchoredAtom2788 chi ∧
      ¬Fin15AnchoredAtom2790 chi ∧
      ¬Fin15AnchoredAtom2795 chi ∧
      ¬Fin15AnchoredAtom2801 chi ∧
      ¬Fin15AnchoredAtom2811 chi ∧
      ¬Fin15AnchoredAtom4502 chi ∧
      ¬Fin15AnchoredAtom4504 chi ∧
      ¬Fin15AnchoredAtom4506 chi ∧
      ¬Fin15AnchoredAtom4508 chi ∧
      ¬Fin15AnchoredAtom4510 chi ∧
      ¬Fin15AnchoredAtom4515 chi ∧
      ¬Fin15AnchoredAtom4518 chi ∧
      ¬Fin15AnchoredAtom4520 chi ∧
      ¬Fin15AnchoredAtom4525 chi ∧
      ¬Fin15AnchoredAtom4531 chi ∧
      ¬Fin15AnchoredAtom4538 chi ∧
      ¬Fin15AnchoredAtom4540 chi ∧
      ¬Fin15AnchoredAtom4545 chi ∧
      ¬Fin15AnchoredAtom4551 chi ∧
      ¬Fin15AnchoredAtom4561 chi ∧
      ¬Fin15AnchoredAtom4769 chi ∧
      ¬Fin15AnchoredAtom4771 chi ∧
      ¬Fin15AnchoredAtom4776 chi ∧
      ¬Fin15AnchoredAtom4782 chi ∧
      ¬Fin15AnchoredAtom4792 chi ∧
      ¬Fin15AnchoredAtom4807 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 7, 8, 9, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22417
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2556 Fin15AnchoredAtom2557 Fin15AnchoredAtom2559
    Fin15AnchoredAtom2561 Fin15AnchoredAtom2562 Fin15AnchoredAtom2564 Fin15AnchoredAtom2566
    Fin15AnchoredAtom2568 Fin15AnchoredAtom2570 Fin15AnchoredAtom2575 Fin15AnchoredAtom2577
    Fin15AnchoredAtom2579 Fin15AnchoredAtom2581 Fin15AnchoredAtom2583 Fin15AnchoredAtom2585
    Fin15AnchoredAtom2590 Fin15AnchoredAtom2593 Fin15AnchoredAtom2595 Fin15AnchoredAtom2600
    Fin15AnchoredAtom2606 Fin15AnchoredAtom2752 Fin15AnchoredAtom2754 Fin15AnchoredAtom2756
    Fin15AnchoredAtom2758 Fin15AnchoredAtom2760 Fin15AnchoredAtom2765 Fin15AnchoredAtom2768
    Fin15AnchoredAtom2770 Fin15AnchoredAtom2775 Fin15AnchoredAtom2781 Fin15AnchoredAtom2788
    Fin15AnchoredAtom2790 Fin15AnchoredAtom2795 Fin15AnchoredAtom2801 Fin15AnchoredAtom2811
    Fin15AnchoredAtom4502 Fin15AnchoredAtom4504 Fin15AnchoredAtom4506 Fin15AnchoredAtom4508
    Fin15AnchoredAtom4510 Fin15AnchoredAtom4515 Fin15AnchoredAtom4518 Fin15AnchoredAtom4520
    Fin15AnchoredAtom4525 Fin15AnchoredAtom4531 Fin15AnchoredAtom4538 Fin15AnchoredAtom4540
    Fin15AnchoredAtom4545 Fin15AnchoredAtom4551 Fin15AnchoredAtom4561 Fin15AnchoredAtom4769
    Fin15AnchoredAtom4771 Fin15AnchoredAtom4776 Fin15AnchoredAtom4782 Fin15AnchoredAtom4792
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

theorem fin15Anchored_clause31592 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2556 chi ∧
      ¬Fin15AnchoredAtom2557 chi ∧
      ¬Fin15AnchoredAtom2560 chi ∧
      ¬Fin15AnchoredAtom2561 chi ∧
      ¬Fin15AnchoredAtom2562 chi ∧
      ¬Fin15AnchoredAtom2565 chi ∧
      ¬Fin15AnchoredAtom2566 chi ∧
      ¬Fin15AnchoredAtom2569 chi ∧
      ¬Fin15AnchoredAtom2570 chi ∧
      ¬Fin15AnchoredAtom2576 chi ∧
      ¬Fin15AnchoredAtom2577 chi ∧
      ¬Fin15AnchoredAtom2580 chi ∧
      ¬Fin15AnchoredAtom2581 chi ∧
      ¬Fin15AnchoredAtom2584 chi ∧
      ¬Fin15AnchoredAtom2585 chi ∧
      ¬Fin15AnchoredAtom2591 chi ∧
      ¬Fin15AnchoredAtom2594 chi ∧
      ¬Fin15AnchoredAtom2595 chi ∧
      ¬Fin15AnchoredAtom2601 chi ∧
      ¬Fin15AnchoredAtom2607 chi ∧
      ¬Fin15AnchoredAtom2752 chi ∧
      ¬Fin15AnchoredAtom2755 chi ∧
      ¬Fin15AnchoredAtom2756 chi ∧
      ¬Fin15AnchoredAtom2759 chi ∧
      ¬Fin15AnchoredAtom2760 chi ∧
      ¬Fin15AnchoredAtom2766 chi ∧
      ¬Fin15AnchoredAtom2769 chi ∧
      ¬Fin15AnchoredAtom2770 chi ∧
      ¬Fin15AnchoredAtom2776 chi ∧
      ¬Fin15AnchoredAtom2782 chi ∧
      ¬Fin15AnchoredAtom2789 chi ∧
      ¬Fin15AnchoredAtom2790 chi ∧
      ¬Fin15AnchoredAtom2796 chi ∧
      ¬Fin15AnchoredAtom2802 chi ∧
      ¬Fin15AnchoredAtom2812 chi ∧
      ¬Fin15AnchoredAtom4502 chi ∧
      ¬Fin15AnchoredAtom4505 chi ∧
      ¬Fin15AnchoredAtom4506 chi ∧
      ¬Fin15AnchoredAtom4509 chi ∧
      ¬Fin15AnchoredAtom4510 chi ∧
      ¬Fin15AnchoredAtom4516 chi ∧
      ¬Fin15AnchoredAtom4519 chi ∧
      ¬Fin15AnchoredAtom4520 chi ∧
      ¬Fin15AnchoredAtom4526 chi ∧
      ¬Fin15AnchoredAtom4532 chi ∧
      ¬Fin15AnchoredAtom4539 chi ∧
      ¬Fin15AnchoredAtom4540 chi ∧
      ¬Fin15AnchoredAtom4546 chi ∧
      ¬Fin15AnchoredAtom4552 chi ∧
      ¬Fin15AnchoredAtom4562 chi ∧
      ¬Fin15AnchoredAtom4770 chi ∧
      ¬Fin15AnchoredAtom4771 chi ∧
      ¬Fin15AnchoredAtom4777 chi ∧
      ¬Fin15AnchoredAtom4783 chi ∧
      ¬Fin15AnchoredAtom4793 chi ∧
      ¬Fin15AnchoredAtom4808 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 7, 8, 9, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26513
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2556 Fin15AnchoredAtom2557 Fin15AnchoredAtom2560
    Fin15AnchoredAtom2561 Fin15AnchoredAtom2562 Fin15AnchoredAtom2565 Fin15AnchoredAtom2566
    Fin15AnchoredAtom2569 Fin15AnchoredAtom2570 Fin15AnchoredAtom2576 Fin15AnchoredAtom2577
    Fin15AnchoredAtom2580 Fin15AnchoredAtom2581 Fin15AnchoredAtom2584 Fin15AnchoredAtom2585
    Fin15AnchoredAtom2591 Fin15AnchoredAtom2594 Fin15AnchoredAtom2595 Fin15AnchoredAtom2601
    Fin15AnchoredAtom2607 Fin15AnchoredAtom2752 Fin15AnchoredAtom2755 Fin15AnchoredAtom2756
    Fin15AnchoredAtom2759 Fin15AnchoredAtom2760 Fin15AnchoredAtom2766 Fin15AnchoredAtom2769
    Fin15AnchoredAtom2770 Fin15AnchoredAtom2776 Fin15AnchoredAtom2782 Fin15AnchoredAtom2789
    Fin15AnchoredAtom2790 Fin15AnchoredAtom2796 Fin15AnchoredAtom2802 Fin15AnchoredAtom2812
    Fin15AnchoredAtom4502 Fin15AnchoredAtom4505 Fin15AnchoredAtom4506 Fin15AnchoredAtom4509
    Fin15AnchoredAtom4510 Fin15AnchoredAtom4516 Fin15AnchoredAtom4519 Fin15AnchoredAtom4520
    Fin15AnchoredAtom4526 Fin15AnchoredAtom4532 Fin15AnchoredAtom4539 Fin15AnchoredAtom4540
    Fin15AnchoredAtom4546 Fin15AnchoredAtom4552 Fin15AnchoredAtom4562 Fin15AnchoredAtom4770
    Fin15AnchoredAtom4771 Fin15AnchoredAtom4777 Fin15AnchoredAtom4783 Fin15AnchoredAtom4793
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

theorem fin15Anchored_clause31593 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2556 chi ∧
      ¬Fin15AnchoredAtom2559 chi ∧
      ¬Fin15AnchoredAtom2560 chi ∧
      ¬Fin15AnchoredAtom2561 chi ∧
      ¬Fin15AnchoredAtom2564 chi ∧
      ¬Fin15AnchoredAtom2565 chi ∧
      ¬Fin15AnchoredAtom2566 chi ∧
      ¬Fin15AnchoredAtom2574 chi ∧
      ¬Fin15AnchoredAtom2575 chi ∧
      ¬Fin15AnchoredAtom2576 chi ∧
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
      ¬Fin15AnchoredAtom2754 chi ∧
      ¬Fin15AnchoredAtom2755 chi ∧
      ¬Fin15AnchoredAtom2756 chi ∧
      ¬Fin15AnchoredAtom2764 chi ∧
      ¬Fin15AnchoredAtom2765 chi ∧
      ¬Fin15AnchoredAtom2766 chi ∧
      ¬Fin15AnchoredAtom2774 chi ∧
      ¬Fin15AnchoredAtom2775 chi ∧
      ¬Fin15AnchoredAtom2776 chi ∧
      ¬Fin15AnchoredAtom2786 chi ∧
      ¬Fin15AnchoredAtom2794 chi ∧
      ¬Fin15AnchoredAtom2795 chi ∧
      ¬Fin15AnchoredAtom2796 chi ∧
      ¬Fin15AnchoredAtom2806 chi ∧
      ¬Fin15AnchoredAtom2816 chi ∧
      ¬Fin15AnchoredAtom4504 chi ∧
      ¬Fin15AnchoredAtom4505 chi ∧
      ¬Fin15AnchoredAtom4506 chi ∧
      ¬Fin15AnchoredAtom4514 chi ∧
      ¬Fin15AnchoredAtom4515 chi ∧
      ¬Fin15AnchoredAtom4516 chi ∧
      ¬Fin15AnchoredAtom4524 chi ∧
      ¬Fin15AnchoredAtom4525 chi ∧
      ¬Fin15AnchoredAtom4526 chi ∧
      ¬Fin15AnchoredAtom4536 chi ∧
      ¬Fin15AnchoredAtom4544 chi ∧
      ¬Fin15AnchoredAtom4545 chi ∧
      ¬Fin15AnchoredAtom4546 chi ∧
      ¬Fin15AnchoredAtom4556 chi ∧
      ¬Fin15AnchoredAtom4566 chi ∧
      ¬Fin15AnchoredAtom4775 chi ∧
      ¬Fin15AnchoredAtom4776 chi ∧
      ¬Fin15AnchoredAtom4777 chi ∧
      ¬Fin15AnchoredAtom4787 chi ∧
      ¬Fin15AnchoredAtom4797 chi ∧
      ¬Fin15AnchoredAtom4812 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 7, 8, 9, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29585
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2556 Fin15AnchoredAtom2559 Fin15AnchoredAtom2560
    Fin15AnchoredAtom2561 Fin15AnchoredAtom2564 Fin15AnchoredAtom2565 Fin15AnchoredAtom2566
    Fin15AnchoredAtom2574 Fin15AnchoredAtom2575 Fin15AnchoredAtom2576 Fin15AnchoredAtom2579
    Fin15AnchoredAtom2580 Fin15AnchoredAtom2581 Fin15AnchoredAtom2589 Fin15AnchoredAtom2590
    Fin15AnchoredAtom2591 Fin15AnchoredAtom2599 Fin15AnchoredAtom2600 Fin15AnchoredAtom2601
    Fin15AnchoredAtom2611 Fin15AnchoredAtom2754 Fin15AnchoredAtom2755 Fin15AnchoredAtom2756
    Fin15AnchoredAtom2764 Fin15AnchoredAtom2765 Fin15AnchoredAtom2766 Fin15AnchoredAtom2774
    Fin15AnchoredAtom2775 Fin15AnchoredAtom2776 Fin15AnchoredAtom2786 Fin15AnchoredAtom2794
    Fin15AnchoredAtom2795 Fin15AnchoredAtom2796 Fin15AnchoredAtom2806 Fin15AnchoredAtom2816
    Fin15AnchoredAtom4504 Fin15AnchoredAtom4505 Fin15AnchoredAtom4506 Fin15AnchoredAtom4514
    Fin15AnchoredAtom4515 Fin15AnchoredAtom4516 Fin15AnchoredAtom4524 Fin15AnchoredAtom4525
    Fin15AnchoredAtom4526 Fin15AnchoredAtom4536 Fin15AnchoredAtom4544 Fin15AnchoredAtom4545
    Fin15AnchoredAtom4546 Fin15AnchoredAtom4556 Fin15AnchoredAtom4566 Fin15AnchoredAtom4775
    Fin15AnchoredAtom4776 Fin15AnchoredAtom4777 Fin15AnchoredAtom4787 Fin15AnchoredAtom4797
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

theorem fin15Anchored_clause31594 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2557 chi ∧
      ¬Fin15AnchoredAtom2559 chi ∧
      ¬Fin15AnchoredAtom2560 chi ∧
      ¬Fin15AnchoredAtom2561 chi ∧
      ¬Fin15AnchoredAtom2568 chi ∧
      ¬Fin15AnchoredAtom2569 chi ∧
      ¬Fin15AnchoredAtom2570 chi ∧
      ¬Fin15AnchoredAtom2574 chi ∧
      ¬Fin15AnchoredAtom2575 chi ∧
      ¬Fin15AnchoredAtom2576 chi ∧
      ¬Fin15AnchoredAtom2583 chi ∧
      ¬Fin15AnchoredAtom2584 chi ∧
      ¬Fin15AnchoredAtom2585 chi ∧
      ¬Fin15AnchoredAtom2589 chi ∧
      ¬Fin15AnchoredAtom2590 chi ∧
      ¬Fin15AnchoredAtom2591 chi ∧
      ¬Fin15AnchoredAtom2605 chi ∧
      ¬Fin15AnchoredAtom2606 chi ∧
      ¬Fin15AnchoredAtom2607 chi ∧
      ¬Fin15AnchoredAtom2611 chi ∧
      ¬Fin15AnchoredAtom2758 chi ∧
      ¬Fin15AnchoredAtom2759 chi ∧
      ¬Fin15AnchoredAtom2760 chi ∧
      ¬Fin15AnchoredAtom2764 chi ∧
      ¬Fin15AnchoredAtom2765 chi ∧
      ¬Fin15AnchoredAtom2766 chi ∧
      ¬Fin15AnchoredAtom2780 chi ∧
      ¬Fin15AnchoredAtom2781 chi ∧
      ¬Fin15AnchoredAtom2782 chi ∧
      ¬Fin15AnchoredAtom2786 chi ∧
      ¬Fin15AnchoredAtom2800 chi ∧
      ¬Fin15AnchoredAtom2801 chi ∧
      ¬Fin15AnchoredAtom2802 chi ∧
      ¬Fin15AnchoredAtom2806 chi ∧
      ¬Fin15AnchoredAtom2820 chi ∧
      ¬Fin15AnchoredAtom4508 chi ∧
      ¬Fin15AnchoredAtom4509 chi ∧
      ¬Fin15AnchoredAtom4510 chi ∧
      ¬Fin15AnchoredAtom4514 chi ∧
      ¬Fin15AnchoredAtom4515 chi ∧
      ¬Fin15AnchoredAtom4516 chi ∧
      ¬Fin15AnchoredAtom4530 chi ∧
      ¬Fin15AnchoredAtom4531 chi ∧
      ¬Fin15AnchoredAtom4532 chi ∧
      ¬Fin15AnchoredAtom4536 chi ∧
      ¬Fin15AnchoredAtom4550 chi ∧
      ¬Fin15AnchoredAtom4551 chi ∧
      ¬Fin15AnchoredAtom4552 chi ∧
      ¬Fin15AnchoredAtom4556 chi ∧
      ¬Fin15AnchoredAtom4570 chi ∧
      ¬Fin15AnchoredAtom4781 chi ∧
      ¬Fin15AnchoredAtom4782 chi ∧
      ¬Fin15AnchoredAtom4783 chi ∧
      ¬Fin15AnchoredAtom4787 chi ∧
      ¬Fin15AnchoredAtom4801 chi ∧
      ¬Fin15AnchoredAtom4816 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 7, 8, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask30097
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2557 Fin15AnchoredAtom2559 Fin15AnchoredAtom2560
    Fin15AnchoredAtom2561 Fin15AnchoredAtom2568 Fin15AnchoredAtom2569 Fin15AnchoredAtom2570
    Fin15AnchoredAtom2574 Fin15AnchoredAtom2575 Fin15AnchoredAtom2576 Fin15AnchoredAtom2583
    Fin15AnchoredAtom2584 Fin15AnchoredAtom2585 Fin15AnchoredAtom2589 Fin15AnchoredAtom2590
    Fin15AnchoredAtom2591 Fin15AnchoredAtom2605 Fin15AnchoredAtom2606 Fin15AnchoredAtom2607
    Fin15AnchoredAtom2611 Fin15AnchoredAtom2758 Fin15AnchoredAtom2759 Fin15AnchoredAtom2760
    Fin15AnchoredAtom2764 Fin15AnchoredAtom2765 Fin15AnchoredAtom2766 Fin15AnchoredAtom2780
    Fin15AnchoredAtom2781 Fin15AnchoredAtom2782 Fin15AnchoredAtom2786 Fin15AnchoredAtom2800
    Fin15AnchoredAtom2801 Fin15AnchoredAtom2802 Fin15AnchoredAtom2806 Fin15AnchoredAtom2820
    Fin15AnchoredAtom4508 Fin15AnchoredAtom4509 Fin15AnchoredAtom4510 Fin15AnchoredAtom4514
    Fin15AnchoredAtom4515 Fin15AnchoredAtom4516 Fin15AnchoredAtom4530 Fin15AnchoredAtom4531
    Fin15AnchoredAtom4532 Fin15AnchoredAtom4536 Fin15AnchoredAtom4550 Fin15AnchoredAtom4551
    Fin15AnchoredAtom4552 Fin15AnchoredAtom4556 Fin15AnchoredAtom4570 Fin15AnchoredAtom4781
    Fin15AnchoredAtom4782 Fin15AnchoredAtom4783 Fin15AnchoredAtom4787 Fin15AnchoredAtom4801
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

theorem fin15Anchored_clause31595 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2562 chi ∧
      ¬Fin15AnchoredAtom2564 chi ∧
      ¬Fin15AnchoredAtom2565 chi ∧
      ¬Fin15AnchoredAtom2566 chi ∧
      ¬Fin15AnchoredAtom2568 chi ∧
      ¬Fin15AnchoredAtom2569 chi ∧
      ¬Fin15AnchoredAtom2570 chi ∧
      ¬Fin15AnchoredAtom2574 chi ∧
      ¬Fin15AnchoredAtom2575 chi ∧
      ¬Fin15AnchoredAtom2576 chi ∧
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
      ¬Fin15AnchoredAtom4518 chi ∧
      ¬Fin15AnchoredAtom4519 chi ∧
      ¬Fin15AnchoredAtom4520 chi ∧
      ¬Fin15AnchoredAtom4524 chi ∧
      ¬Fin15AnchoredAtom4525 chi ∧
      ¬Fin15AnchoredAtom4526 chi ∧
      ¬Fin15AnchoredAtom4530 chi ∧
      ¬Fin15AnchoredAtom4531 chi ∧
      ¬Fin15AnchoredAtom4532 chi ∧
      ¬Fin15AnchoredAtom4536 chi ∧
      ¬Fin15AnchoredAtom4560 chi ∧
      ¬Fin15AnchoredAtom4561 chi ∧
      ¬Fin15AnchoredAtom4562 chi ∧
      ¬Fin15AnchoredAtom4566 chi ∧
      ¬Fin15AnchoredAtom4570 chi ∧
      ¬Fin15AnchoredAtom4791 chi ∧
      ¬Fin15AnchoredAtom4792 chi ∧
      ¬Fin15AnchoredAtom4793 chi ∧
      ¬Fin15AnchoredAtom4797 chi ∧
      ¬Fin15AnchoredAtom4801 chi ∧
      ¬Fin15AnchoredAtom4821 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 7, 9, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask30353
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2562 Fin15AnchoredAtom2564 Fin15AnchoredAtom2565
    Fin15AnchoredAtom2566 Fin15AnchoredAtom2568 Fin15AnchoredAtom2569 Fin15AnchoredAtom2570
    Fin15AnchoredAtom2574 Fin15AnchoredAtom2575 Fin15AnchoredAtom2576 Fin15AnchoredAtom2593
    Fin15AnchoredAtom2594 Fin15AnchoredAtom2595 Fin15AnchoredAtom2599 Fin15AnchoredAtom2600
    Fin15AnchoredAtom2601 Fin15AnchoredAtom2605 Fin15AnchoredAtom2606 Fin15AnchoredAtom2607
    Fin15AnchoredAtom2611 Fin15AnchoredAtom2768 Fin15AnchoredAtom2769 Fin15AnchoredAtom2770
    Fin15AnchoredAtom2774 Fin15AnchoredAtom2775 Fin15AnchoredAtom2776 Fin15AnchoredAtom2780
    Fin15AnchoredAtom2781 Fin15AnchoredAtom2782 Fin15AnchoredAtom2786 Fin15AnchoredAtom2810
    Fin15AnchoredAtom2811 Fin15AnchoredAtom2812 Fin15AnchoredAtom2816 Fin15AnchoredAtom2820
    Fin15AnchoredAtom4518 Fin15AnchoredAtom4519 Fin15AnchoredAtom4520 Fin15AnchoredAtom4524
    Fin15AnchoredAtom4525 Fin15AnchoredAtom4526 Fin15AnchoredAtom4530 Fin15AnchoredAtom4531
    Fin15AnchoredAtom4532 Fin15AnchoredAtom4536 Fin15AnchoredAtom4560 Fin15AnchoredAtom4561
    Fin15AnchoredAtom4562 Fin15AnchoredAtom4566 Fin15AnchoredAtom4570 Fin15AnchoredAtom4791
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

theorem fin15Anchored_clause31596 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2577 chi ∧
      ¬Fin15AnchoredAtom2579 chi ∧
      ¬Fin15AnchoredAtom2580 chi ∧
      ¬Fin15AnchoredAtom2581 chi ∧
      ¬Fin15AnchoredAtom2583 chi ∧
      ¬Fin15AnchoredAtom2584 chi ∧
      ¬Fin15AnchoredAtom2585 chi ∧
      ¬Fin15AnchoredAtom2589 chi ∧
      ¬Fin15AnchoredAtom2590 chi ∧
      ¬Fin15AnchoredAtom2591 chi ∧
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
      ¬Fin15AnchoredAtom2788 chi ∧
      ¬Fin15AnchoredAtom2789 chi ∧
      ¬Fin15AnchoredAtom2790 chi ∧
      ¬Fin15AnchoredAtom2794 chi ∧
      ¬Fin15AnchoredAtom2795 chi ∧
      ¬Fin15AnchoredAtom2796 chi ∧
      ¬Fin15AnchoredAtom2800 chi ∧
      ¬Fin15AnchoredAtom2801 chi ∧
      ¬Fin15AnchoredAtom2802 chi ∧
      ¬Fin15AnchoredAtom2806 chi ∧
      ¬Fin15AnchoredAtom2810 chi ∧
      ¬Fin15AnchoredAtom2811 chi ∧
      ¬Fin15AnchoredAtom2812 chi ∧
      ¬Fin15AnchoredAtom2816 chi ∧
      ¬Fin15AnchoredAtom2820 chi ∧
      ¬Fin15AnchoredAtom4538 chi ∧
      ¬Fin15AnchoredAtom4539 chi ∧
      ¬Fin15AnchoredAtom4540 chi ∧
      ¬Fin15AnchoredAtom4544 chi ∧
      ¬Fin15AnchoredAtom4545 chi ∧
      ¬Fin15AnchoredAtom4546 chi ∧
      ¬Fin15AnchoredAtom4550 chi ∧
      ¬Fin15AnchoredAtom4551 chi ∧
      ¬Fin15AnchoredAtom4552 chi ∧
      ¬Fin15AnchoredAtom4556 chi ∧
      ¬Fin15AnchoredAtom4560 chi ∧
      ¬Fin15AnchoredAtom4561 chi ∧
      ¬Fin15AnchoredAtom4562 chi ∧
      ¬Fin15AnchoredAtom4566 chi ∧
      ¬Fin15AnchoredAtom4570 chi ∧
      ¬Fin15AnchoredAtom4806 chi ∧
      ¬Fin15AnchoredAtom4807 chi ∧
      ¬Fin15AnchoredAtom4808 chi ∧
      ¬Fin15AnchoredAtom4812 chi ∧
      ¬Fin15AnchoredAtom4816 chi ∧
      ¬Fin15AnchoredAtom4821 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 8, 9, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask30481
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2577 Fin15AnchoredAtom2579 Fin15AnchoredAtom2580
    Fin15AnchoredAtom2581 Fin15AnchoredAtom2583 Fin15AnchoredAtom2584 Fin15AnchoredAtom2585
    Fin15AnchoredAtom2589 Fin15AnchoredAtom2590 Fin15AnchoredAtom2591 Fin15AnchoredAtom2593
    Fin15AnchoredAtom2594 Fin15AnchoredAtom2595 Fin15AnchoredAtom2599 Fin15AnchoredAtom2600
    Fin15AnchoredAtom2601 Fin15AnchoredAtom2605 Fin15AnchoredAtom2606 Fin15AnchoredAtom2607
    Fin15AnchoredAtom2611 Fin15AnchoredAtom2788 Fin15AnchoredAtom2789 Fin15AnchoredAtom2790
    Fin15AnchoredAtom2794 Fin15AnchoredAtom2795 Fin15AnchoredAtom2796 Fin15AnchoredAtom2800
    Fin15AnchoredAtom2801 Fin15AnchoredAtom2802 Fin15AnchoredAtom2806 Fin15AnchoredAtom2810
    Fin15AnchoredAtom2811 Fin15AnchoredAtom2812 Fin15AnchoredAtom2816 Fin15AnchoredAtom2820
    Fin15AnchoredAtom4538 Fin15AnchoredAtom4539 Fin15AnchoredAtom4540 Fin15AnchoredAtom4544
    Fin15AnchoredAtom4545 Fin15AnchoredAtom4546 Fin15AnchoredAtom4550 Fin15AnchoredAtom4551
    Fin15AnchoredAtom4552 Fin15AnchoredAtom4556 Fin15AnchoredAtom4560 Fin15AnchoredAtom4561
    Fin15AnchoredAtom4562 Fin15AnchoredAtom4566 Fin15AnchoredAtom4570 Fin15AnchoredAtom4806
    Fin15AnchoredAtom4807 Fin15AnchoredAtom4808 Fin15AnchoredAtom4812 Fin15AnchoredAtom4816
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

theorem fin15Anchored_clause31597 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2612 chi ∧
      ¬Fin15AnchoredAtom2613 chi ∧
      ¬Fin15AnchoredAtom2614 chi ∧
      ¬Fin15AnchoredAtom2616 chi ∧
      ¬Fin15AnchoredAtom2619 chi ∧
      ¬Fin15AnchoredAtom2620 chi ∧
      ¬Fin15AnchoredAtom2622 chi ∧
      ¬Fin15AnchoredAtom2625 chi ∧
      ¬Fin15AnchoredAtom2627 chi ∧
      ¬Fin15AnchoredAtom2631 chi ∧
      ¬Fin15AnchoredAtom2640 chi ∧
      ¬Fin15AnchoredAtom2641 chi ∧
      ¬Fin15AnchoredAtom2643 chi ∧
      ¬Fin15AnchoredAtom2646 chi ∧
      ¬Fin15AnchoredAtom2648 chi ∧
      ¬Fin15AnchoredAtom2652 chi ∧
      ¬Fin15AnchoredAtom2661 chi ∧
      ¬Fin15AnchoredAtom2663 chi ∧
      ¬Fin15AnchoredAtom2667 chi ∧
      ¬Fin15AnchoredAtom2677 chi ∧
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
      ¬Fin15AnchoredAtom4572 chi ∧
      ¬Fin15AnchoredAtom4573 chi ∧
      ¬Fin15AnchoredAtom4575 chi ∧
      ¬Fin15AnchoredAtom4578 chi ∧
      ¬Fin15AnchoredAtom4580 chi ∧
      ¬Fin15AnchoredAtom4584 chi ∧
      ¬Fin15AnchoredAtom4593 chi ∧
      ¬Fin15AnchoredAtom4595 chi ∧
      ¬Fin15AnchoredAtom4599 chi ∧
      ¬Fin15AnchoredAtom4609 chi ∧
      ¬Fin15AnchoredAtom4628 chi ∧
      ¬Fin15AnchoredAtom4630 chi ∧
      ¬Fin15AnchoredAtom4634 chi ∧
      ¬Fin15AnchoredAtom4644 chi ∧
      ¬Fin15AnchoredAtom4664 chi ∧
      ¬Fin15AnchoredAtom4698 chi ∧
      ¬Fin15AnchoredAtom4700 chi ∧
      ¬Fin15AnchoredAtom4704 chi ∧
      ¬Fin15AnchoredAtom4714 chi ∧
      ¬Fin15AnchoredAtom4734 chi ∧
      ¬Fin15AnchoredAtom4769 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 5, 6, 7, 8, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask06113
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2612 Fin15AnchoredAtom2613 Fin15AnchoredAtom2614
    Fin15AnchoredAtom2616 Fin15AnchoredAtom2619 Fin15AnchoredAtom2620 Fin15AnchoredAtom2622
    Fin15AnchoredAtom2625 Fin15AnchoredAtom2627 Fin15AnchoredAtom2631 Fin15AnchoredAtom2640
    Fin15AnchoredAtom2641 Fin15AnchoredAtom2643 Fin15AnchoredAtom2646 Fin15AnchoredAtom2648
    Fin15AnchoredAtom2652 Fin15AnchoredAtom2661 Fin15AnchoredAtom2663 Fin15AnchoredAtom2667
    Fin15AnchoredAtom2677 Fin15AnchoredAtom2696 Fin15AnchoredAtom2697 Fin15AnchoredAtom2699
    Fin15AnchoredAtom2702 Fin15AnchoredAtom2704 Fin15AnchoredAtom2708 Fin15AnchoredAtom2717
    Fin15AnchoredAtom2719 Fin15AnchoredAtom2723 Fin15AnchoredAtom2733 Fin15AnchoredAtom2752
    Fin15AnchoredAtom2754 Fin15AnchoredAtom2758 Fin15AnchoredAtom2768 Fin15AnchoredAtom2788
    Fin15AnchoredAtom4572 Fin15AnchoredAtom4573 Fin15AnchoredAtom4575 Fin15AnchoredAtom4578
    Fin15AnchoredAtom4580 Fin15AnchoredAtom4584 Fin15AnchoredAtom4593 Fin15AnchoredAtom4595
    Fin15AnchoredAtom4599 Fin15AnchoredAtom4609 Fin15AnchoredAtom4628 Fin15AnchoredAtom4630
    Fin15AnchoredAtom4634 Fin15AnchoredAtom4644 Fin15AnchoredAtom4664 Fin15AnchoredAtom4698
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

theorem fin15Anchored_clause31598 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2612 chi ∧
      ¬Fin15AnchoredAtom2613 chi ∧
      ¬Fin15AnchoredAtom2614 chi ∧
      ¬Fin15AnchoredAtom2617 chi ∧
      ¬Fin15AnchoredAtom2619 chi ∧
      ¬Fin15AnchoredAtom2620 chi ∧
      ¬Fin15AnchoredAtom2623 chi ∧
      ¬Fin15AnchoredAtom2625 chi ∧
      ¬Fin15AnchoredAtom2628 chi ∧
      ¬Fin15AnchoredAtom2632 chi ∧
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
      ¬Fin15AnchoredAtom4572 chi ∧
      ¬Fin15AnchoredAtom4573 chi ∧
      ¬Fin15AnchoredAtom4576 chi ∧
      ¬Fin15AnchoredAtom4578 chi ∧
      ¬Fin15AnchoredAtom4581 chi ∧
      ¬Fin15AnchoredAtom4585 chi ∧
      ¬Fin15AnchoredAtom4593 chi ∧
      ¬Fin15AnchoredAtom4596 chi ∧
      ¬Fin15AnchoredAtom4600 chi ∧
      ¬Fin15AnchoredAtom4610 chi ∧
      ¬Fin15AnchoredAtom4628 chi ∧
      ¬Fin15AnchoredAtom4631 chi ∧
      ¬Fin15AnchoredAtom4635 chi ∧
      ¬Fin15AnchoredAtom4645 chi ∧
      ¬Fin15AnchoredAtom4665 chi ∧
      ¬Fin15AnchoredAtom4698 chi ∧
      ¬Fin15AnchoredAtom4701 chi ∧
      ¬Fin15AnchoredAtom4705 chi ∧
      ¬Fin15AnchoredAtom4715 chi ∧
      ¬Fin15AnchoredAtom4735 chi ∧
      ¬Fin15AnchoredAtom4770 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 5, 6, 7, 8, 9, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask10209
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2612 Fin15AnchoredAtom2613 Fin15AnchoredAtom2614
    Fin15AnchoredAtom2617 Fin15AnchoredAtom2619 Fin15AnchoredAtom2620 Fin15AnchoredAtom2623
    Fin15AnchoredAtom2625 Fin15AnchoredAtom2628 Fin15AnchoredAtom2632 Fin15AnchoredAtom2640
    Fin15AnchoredAtom2641 Fin15AnchoredAtom2644 Fin15AnchoredAtom2646 Fin15AnchoredAtom2649
    Fin15AnchoredAtom2653 Fin15AnchoredAtom2661 Fin15AnchoredAtom2664 Fin15AnchoredAtom2668
    Fin15AnchoredAtom2678 Fin15AnchoredAtom2696 Fin15AnchoredAtom2697 Fin15AnchoredAtom2700
    Fin15AnchoredAtom2702 Fin15AnchoredAtom2705 Fin15AnchoredAtom2709 Fin15AnchoredAtom2717
    Fin15AnchoredAtom2720 Fin15AnchoredAtom2724 Fin15AnchoredAtom2734 Fin15AnchoredAtom2752
    Fin15AnchoredAtom2755 Fin15AnchoredAtom2759 Fin15AnchoredAtom2769 Fin15AnchoredAtom2789
    Fin15AnchoredAtom4572 Fin15AnchoredAtom4573 Fin15AnchoredAtom4576 Fin15AnchoredAtom4578
    Fin15AnchoredAtom4581 Fin15AnchoredAtom4585 Fin15AnchoredAtom4593 Fin15AnchoredAtom4596
    Fin15AnchoredAtom4600 Fin15AnchoredAtom4610 Fin15AnchoredAtom4628 Fin15AnchoredAtom4631
    Fin15AnchoredAtom4635 Fin15AnchoredAtom4645 Fin15AnchoredAtom4665 Fin15AnchoredAtom4698
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

theorem fin15Anchored_clause31599 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2612 chi ∧
      ¬Fin15AnchoredAtom2613 chi ∧
      ¬Fin15AnchoredAtom2614 chi ∧
      ¬Fin15AnchoredAtom2618 chi ∧
      ¬Fin15AnchoredAtom2619 chi ∧
      ¬Fin15AnchoredAtom2620 chi ∧
      ¬Fin15AnchoredAtom2624 chi ∧
      ¬Fin15AnchoredAtom2625 chi ∧
      ¬Fin15AnchoredAtom2629 chi ∧
      ¬Fin15AnchoredAtom2633 chi ∧
      ¬Fin15AnchoredAtom2640 chi ∧
      ¬Fin15AnchoredAtom2641 chi ∧
      ¬Fin15AnchoredAtom2645 chi ∧
      ¬Fin15AnchoredAtom2646 chi ∧
      ¬Fin15AnchoredAtom2650 chi ∧
      ¬Fin15AnchoredAtom2654 chi ∧
      ¬Fin15AnchoredAtom2661 chi ∧
      ¬Fin15AnchoredAtom2665 chi ∧
      ¬Fin15AnchoredAtom2669 chi ∧
      ¬Fin15AnchoredAtom2679 chi ∧
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
      ¬Fin15AnchoredAtom4572 chi ∧
      ¬Fin15AnchoredAtom4573 chi ∧
      ¬Fin15AnchoredAtom4577 chi ∧
      ¬Fin15AnchoredAtom4578 chi ∧
      ¬Fin15AnchoredAtom4582 chi ∧
      ¬Fin15AnchoredAtom4586 chi ∧
      ¬Fin15AnchoredAtom4593 chi ∧
      ¬Fin15AnchoredAtom4597 chi ∧
      ¬Fin15AnchoredAtom4601 chi ∧
      ¬Fin15AnchoredAtom4611 chi ∧
      ¬Fin15AnchoredAtom4628 chi ∧
      ¬Fin15AnchoredAtom4632 chi ∧
      ¬Fin15AnchoredAtom4636 chi ∧
      ¬Fin15AnchoredAtom4646 chi ∧
      ¬Fin15AnchoredAtom4666 chi ∧
      ¬Fin15AnchoredAtom4698 chi ∧
      ¬Fin15AnchoredAtom4702 chi ∧
      ¬Fin15AnchoredAtom4706 chi ∧
      ¬Fin15AnchoredAtom4716 chi ∧
      ¬Fin15AnchoredAtom4736 chi ∧
      ¬Fin15AnchoredAtom4771 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 5, 6, 7, 8, 9, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask18401
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2612 Fin15AnchoredAtom2613 Fin15AnchoredAtom2614
    Fin15AnchoredAtom2618 Fin15AnchoredAtom2619 Fin15AnchoredAtom2620 Fin15AnchoredAtom2624
    Fin15AnchoredAtom2625 Fin15AnchoredAtom2629 Fin15AnchoredAtom2633 Fin15AnchoredAtom2640
    Fin15AnchoredAtom2641 Fin15AnchoredAtom2645 Fin15AnchoredAtom2646 Fin15AnchoredAtom2650
    Fin15AnchoredAtom2654 Fin15AnchoredAtom2661 Fin15AnchoredAtom2665 Fin15AnchoredAtom2669
    Fin15AnchoredAtom2679 Fin15AnchoredAtom2696 Fin15AnchoredAtom2697 Fin15AnchoredAtom2701
    Fin15AnchoredAtom2702 Fin15AnchoredAtom2706 Fin15AnchoredAtom2710 Fin15AnchoredAtom2717
    Fin15AnchoredAtom2721 Fin15AnchoredAtom2725 Fin15AnchoredAtom2735 Fin15AnchoredAtom2752
    Fin15AnchoredAtom2756 Fin15AnchoredAtom2760 Fin15AnchoredAtom2770 Fin15AnchoredAtom2790
    Fin15AnchoredAtom4572 Fin15AnchoredAtom4573 Fin15AnchoredAtom4577 Fin15AnchoredAtom4578
    Fin15AnchoredAtom4582 Fin15AnchoredAtom4586 Fin15AnchoredAtom4593 Fin15AnchoredAtom4597
    Fin15AnchoredAtom4601 Fin15AnchoredAtom4611 Fin15AnchoredAtom4628 Fin15AnchoredAtom4632
    Fin15AnchoredAtom4636 Fin15AnchoredAtom4646 Fin15AnchoredAtom4666 Fin15AnchoredAtom4698
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

theorem fin15Anchored_clause31600 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2612 chi ∧
      ¬Fin15AnchoredAtom2613 chi ∧
      ¬Fin15AnchoredAtom2616 chi ∧
      ¬Fin15AnchoredAtom2617 chi ∧
      ¬Fin15AnchoredAtom2619 chi ∧
      ¬Fin15AnchoredAtom2622 chi ∧
      ¬Fin15AnchoredAtom2623 chi ∧
      ¬Fin15AnchoredAtom2627 chi ∧
      ¬Fin15AnchoredAtom2628 chi ∧
      ¬Fin15AnchoredAtom2637 chi ∧
      ¬Fin15AnchoredAtom2640 chi ∧
      ¬Fin15AnchoredAtom2643 chi ∧
      ¬Fin15AnchoredAtom2644 chi ∧
      ¬Fin15AnchoredAtom2648 chi ∧
      ¬Fin15AnchoredAtom2649 chi ∧
      ¬Fin15AnchoredAtom2658 chi ∧
      ¬Fin15AnchoredAtom2663 chi ∧
      ¬Fin15AnchoredAtom2664 chi ∧
      ¬Fin15AnchoredAtom2673 chi ∧
      ¬Fin15AnchoredAtom2683 chi ∧
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
      ¬Fin15AnchoredAtom4572 chi ∧
      ¬Fin15AnchoredAtom4575 chi ∧
      ¬Fin15AnchoredAtom4576 chi ∧
      ¬Fin15AnchoredAtom4580 chi ∧
      ¬Fin15AnchoredAtom4581 chi ∧
      ¬Fin15AnchoredAtom4590 chi ∧
      ¬Fin15AnchoredAtom4595 chi ∧
      ¬Fin15AnchoredAtom4596 chi ∧
      ¬Fin15AnchoredAtom4605 chi ∧
      ¬Fin15AnchoredAtom4615 chi ∧
      ¬Fin15AnchoredAtom4630 chi ∧
      ¬Fin15AnchoredAtom4631 chi ∧
      ¬Fin15AnchoredAtom4640 chi ∧
      ¬Fin15AnchoredAtom4650 chi ∧
      ¬Fin15AnchoredAtom4670 chi ∧
      ¬Fin15AnchoredAtom4700 chi ∧
      ¬Fin15AnchoredAtom4701 chi ∧
      ¬Fin15AnchoredAtom4710 chi ∧
      ¬Fin15AnchoredAtom4720 chi ∧
      ¬Fin15AnchoredAtom4740 chi ∧
      ¬Fin15AnchoredAtom4775 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 5, 6, 7, 8, 9, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13281
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2612 Fin15AnchoredAtom2613 Fin15AnchoredAtom2616
    Fin15AnchoredAtom2617 Fin15AnchoredAtom2619 Fin15AnchoredAtom2622 Fin15AnchoredAtom2623
    Fin15AnchoredAtom2627 Fin15AnchoredAtom2628 Fin15AnchoredAtom2637 Fin15AnchoredAtom2640
    Fin15AnchoredAtom2643 Fin15AnchoredAtom2644 Fin15AnchoredAtom2648 Fin15AnchoredAtom2649
    Fin15AnchoredAtom2658 Fin15AnchoredAtom2663 Fin15AnchoredAtom2664 Fin15AnchoredAtom2673
    Fin15AnchoredAtom2683 Fin15AnchoredAtom2696 Fin15AnchoredAtom2699 Fin15AnchoredAtom2700
    Fin15AnchoredAtom2704 Fin15AnchoredAtom2705 Fin15AnchoredAtom2714 Fin15AnchoredAtom2719
    Fin15AnchoredAtom2720 Fin15AnchoredAtom2729 Fin15AnchoredAtom2739 Fin15AnchoredAtom2754
    Fin15AnchoredAtom2755 Fin15AnchoredAtom2764 Fin15AnchoredAtom2774 Fin15AnchoredAtom2794
    Fin15AnchoredAtom4572 Fin15AnchoredAtom4575 Fin15AnchoredAtom4576 Fin15AnchoredAtom4580
    Fin15AnchoredAtom4581 Fin15AnchoredAtom4590 Fin15AnchoredAtom4595 Fin15AnchoredAtom4596
    Fin15AnchoredAtom4605 Fin15AnchoredAtom4615 Fin15AnchoredAtom4630 Fin15AnchoredAtom4631
    Fin15AnchoredAtom4640 Fin15AnchoredAtom4650 Fin15AnchoredAtom4670 Fin15AnchoredAtom4700
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

theorem fin15Anchored_clause31601 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2612 chi ∧
      ¬Fin15AnchoredAtom2613 chi ∧
      ¬Fin15AnchoredAtom2616 chi ∧
      ¬Fin15AnchoredAtom2618 chi ∧
      ¬Fin15AnchoredAtom2619 chi ∧
      ¬Fin15AnchoredAtom2622 chi ∧
      ¬Fin15AnchoredAtom2624 chi ∧
      ¬Fin15AnchoredAtom2627 chi ∧
      ¬Fin15AnchoredAtom2629 chi ∧
      ¬Fin15AnchoredAtom2638 chi ∧
      ¬Fin15AnchoredAtom2640 chi ∧
      ¬Fin15AnchoredAtom2643 chi ∧
      ¬Fin15AnchoredAtom2645 chi ∧
      ¬Fin15AnchoredAtom2648 chi ∧
      ¬Fin15AnchoredAtom2650 chi ∧
      ¬Fin15AnchoredAtom2659 chi ∧
      ¬Fin15AnchoredAtom2663 chi ∧
      ¬Fin15AnchoredAtom2665 chi ∧
      ¬Fin15AnchoredAtom2674 chi ∧
      ¬Fin15AnchoredAtom2684 chi ∧
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
      ¬Fin15AnchoredAtom4572 chi ∧
      ¬Fin15AnchoredAtom4575 chi ∧
      ¬Fin15AnchoredAtom4577 chi ∧
      ¬Fin15AnchoredAtom4580 chi ∧
      ¬Fin15AnchoredAtom4582 chi ∧
      ¬Fin15AnchoredAtom4591 chi ∧
      ¬Fin15AnchoredAtom4595 chi ∧
      ¬Fin15AnchoredAtom4597 chi ∧
      ¬Fin15AnchoredAtom4606 chi ∧
      ¬Fin15AnchoredAtom4616 chi ∧
      ¬Fin15AnchoredAtom4630 chi ∧
      ¬Fin15AnchoredAtom4632 chi ∧
      ¬Fin15AnchoredAtom4641 chi ∧
      ¬Fin15AnchoredAtom4651 chi ∧
      ¬Fin15AnchoredAtom4671 chi ∧
      ¬Fin15AnchoredAtom4700 chi ∧
      ¬Fin15AnchoredAtom4702 chi ∧
      ¬Fin15AnchoredAtom4711 chi ∧
      ¬Fin15AnchoredAtom4721 chi ∧
      ¬Fin15AnchoredAtom4741 chi ∧
      ¬Fin15AnchoredAtom4776 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 5, 6, 7, 8, 9, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21473
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2612 Fin15AnchoredAtom2613 Fin15AnchoredAtom2616
    Fin15AnchoredAtom2618 Fin15AnchoredAtom2619 Fin15AnchoredAtom2622 Fin15AnchoredAtom2624
    Fin15AnchoredAtom2627 Fin15AnchoredAtom2629 Fin15AnchoredAtom2638 Fin15AnchoredAtom2640
    Fin15AnchoredAtom2643 Fin15AnchoredAtom2645 Fin15AnchoredAtom2648 Fin15AnchoredAtom2650
    Fin15AnchoredAtom2659 Fin15AnchoredAtom2663 Fin15AnchoredAtom2665 Fin15AnchoredAtom2674
    Fin15AnchoredAtom2684 Fin15AnchoredAtom2696 Fin15AnchoredAtom2699 Fin15AnchoredAtom2701
    Fin15AnchoredAtom2704 Fin15AnchoredAtom2706 Fin15AnchoredAtom2715 Fin15AnchoredAtom2719
    Fin15AnchoredAtom2721 Fin15AnchoredAtom2730 Fin15AnchoredAtom2740 Fin15AnchoredAtom2754
    Fin15AnchoredAtom2756 Fin15AnchoredAtom2765 Fin15AnchoredAtom2775 Fin15AnchoredAtom2795
    Fin15AnchoredAtom4572 Fin15AnchoredAtom4575 Fin15AnchoredAtom4577 Fin15AnchoredAtom4580
    Fin15AnchoredAtom4582 Fin15AnchoredAtom4591 Fin15AnchoredAtom4595 Fin15AnchoredAtom4597
    Fin15AnchoredAtom4606 Fin15AnchoredAtom4616 Fin15AnchoredAtom4630 Fin15AnchoredAtom4632
    Fin15AnchoredAtom4641 Fin15AnchoredAtom4651 Fin15AnchoredAtom4671 Fin15AnchoredAtom4700
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

theorem fin15Anchored_clause31602 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2612 chi ∧
      ¬Fin15AnchoredAtom2613 chi ∧
      ¬Fin15AnchoredAtom2617 chi ∧
      ¬Fin15AnchoredAtom2618 chi ∧
      ¬Fin15AnchoredAtom2619 chi ∧
      ¬Fin15AnchoredAtom2623 chi ∧
      ¬Fin15AnchoredAtom2624 chi ∧
      ¬Fin15AnchoredAtom2628 chi ∧
      ¬Fin15AnchoredAtom2629 chi ∧
      ¬Fin15AnchoredAtom2639 chi ∧
      ¬Fin15AnchoredAtom2640 chi ∧
      ¬Fin15AnchoredAtom2644 chi ∧
      ¬Fin15AnchoredAtom2645 chi ∧
      ¬Fin15AnchoredAtom2649 chi ∧
      ¬Fin15AnchoredAtom2650 chi ∧
      ¬Fin15AnchoredAtom2660 chi ∧
      ¬Fin15AnchoredAtom2664 chi ∧
      ¬Fin15AnchoredAtom2665 chi ∧
      ¬Fin15AnchoredAtom2675 chi ∧
      ¬Fin15AnchoredAtom2685 chi ∧
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
      ¬Fin15AnchoredAtom4572 chi ∧
      ¬Fin15AnchoredAtom4576 chi ∧
      ¬Fin15AnchoredAtom4577 chi ∧
      ¬Fin15AnchoredAtom4581 chi ∧
      ¬Fin15AnchoredAtom4582 chi ∧
      ¬Fin15AnchoredAtom4592 chi ∧
      ¬Fin15AnchoredAtom4596 chi ∧
      ¬Fin15AnchoredAtom4597 chi ∧
      ¬Fin15AnchoredAtom4607 chi ∧
      ¬Fin15AnchoredAtom4617 chi ∧
      ¬Fin15AnchoredAtom4631 chi ∧
      ¬Fin15AnchoredAtom4632 chi ∧
      ¬Fin15AnchoredAtom4642 chi ∧
      ¬Fin15AnchoredAtom4652 chi ∧
      ¬Fin15AnchoredAtom4672 chi ∧
      ¬Fin15AnchoredAtom4701 chi ∧
      ¬Fin15AnchoredAtom4702 chi ∧
      ¬Fin15AnchoredAtom4712 chi ∧
      ¬Fin15AnchoredAtom4722 chi ∧
      ¬Fin15AnchoredAtom4742 chi ∧
      ¬Fin15AnchoredAtom4777 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 5, 6, 7, 8, 9, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25569
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2612 Fin15AnchoredAtom2613 Fin15AnchoredAtom2617
    Fin15AnchoredAtom2618 Fin15AnchoredAtom2619 Fin15AnchoredAtom2623 Fin15AnchoredAtom2624
    Fin15AnchoredAtom2628 Fin15AnchoredAtom2629 Fin15AnchoredAtom2639 Fin15AnchoredAtom2640
    Fin15AnchoredAtom2644 Fin15AnchoredAtom2645 Fin15AnchoredAtom2649 Fin15AnchoredAtom2650
    Fin15AnchoredAtom2660 Fin15AnchoredAtom2664 Fin15AnchoredAtom2665 Fin15AnchoredAtom2675
    Fin15AnchoredAtom2685 Fin15AnchoredAtom2696 Fin15AnchoredAtom2700 Fin15AnchoredAtom2701
    Fin15AnchoredAtom2705 Fin15AnchoredAtom2706 Fin15AnchoredAtom2716 Fin15AnchoredAtom2720
    Fin15AnchoredAtom2721 Fin15AnchoredAtom2731 Fin15AnchoredAtom2741 Fin15AnchoredAtom2755
    Fin15AnchoredAtom2756 Fin15AnchoredAtom2766 Fin15AnchoredAtom2776 Fin15AnchoredAtom2796
    Fin15AnchoredAtom4572 Fin15AnchoredAtom4576 Fin15AnchoredAtom4577 Fin15AnchoredAtom4581
    Fin15AnchoredAtom4582 Fin15AnchoredAtom4592 Fin15AnchoredAtom4596 Fin15AnchoredAtom4597
    Fin15AnchoredAtom4607 Fin15AnchoredAtom4617 Fin15AnchoredAtom4631 Fin15AnchoredAtom4632
    Fin15AnchoredAtom4642 Fin15AnchoredAtom4652 Fin15AnchoredAtom4672 Fin15AnchoredAtom4701
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

theorem fin15Anchored_clause31603 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2612 chi ∧
      ¬Fin15AnchoredAtom2614 chi ∧
      ¬Fin15AnchoredAtom2616 chi ∧
      ¬Fin15AnchoredAtom2617 chi ∧
      ¬Fin15AnchoredAtom2620 chi ∧
      ¬Fin15AnchoredAtom2622 chi ∧
      ¬Fin15AnchoredAtom2623 chi ∧
      ¬Fin15AnchoredAtom2631 chi ∧
      ¬Fin15AnchoredAtom2632 chi ∧
      ¬Fin15AnchoredAtom2637 chi ∧
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
      ¬Fin15AnchoredAtom4573 chi ∧
      ¬Fin15AnchoredAtom4575 chi ∧
      ¬Fin15AnchoredAtom4576 chi ∧
      ¬Fin15AnchoredAtom4584 chi ∧
      ¬Fin15AnchoredAtom4585 chi ∧
      ¬Fin15AnchoredAtom4590 chi ∧
      ¬Fin15AnchoredAtom4599 chi ∧
      ¬Fin15AnchoredAtom4600 chi ∧
      ¬Fin15AnchoredAtom4605 chi ∧
      ¬Fin15AnchoredAtom4621 chi ∧
      ¬Fin15AnchoredAtom4634 chi ∧
      ¬Fin15AnchoredAtom4635 chi ∧
      ¬Fin15AnchoredAtom4640 chi ∧
      ¬Fin15AnchoredAtom4656 chi ∧
      ¬Fin15AnchoredAtom4676 chi ∧
      ¬Fin15AnchoredAtom4704 chi ∧
      ¬Fin15AnchoredAtom4705 chi ∧
      ¬Fin15AnchoredAtom4710 chi ∧
      ¬Fin15AnchoredAtom4726 chi ∧
      ¬Fin15AnchoredAtom4746 chi ∧
      ¬Fin15AnchoredAtom4781 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 5, 6, 7, 8, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13793
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2612 Fin15AnchoredAtom2614 Fin15AnchoredAtom2616
    Fin15AnchoredAtom2617 Fin15AnchoredAtom2620 Fin15AnchoredAtom2622 Fin15AnchoredAtom2623
    Fin15AnchoredAtom2631 Fin15AnchoredAtom2632 Fin15AnchoredAtom2637 Fin15AnchoredAtom2641
    Fin15AnchoredAtom2643 Fin15AnchoredAtom2644 Fin15AnchoredAtom2652 Fin15AnchoredAtom2653
    Fin15AnchoredAtom2658 Fin15AnchoredAtom2667 Fin15AnchoredAtom2668 Fin15AnchoredAtom2673
    Fin15AnchoredAtom2689 Fin15AnchoredAtom2697 Fin15AnchoredAtom2699 Fin15AnchoredAtom2700
    Fin15AnchoredAtom2708 Fin15AnchoredAtom2709 Fin15AnchoredAtom2714 Fin15AnchoredAtom2723
    Fin15AnchoredAtom2724 Fin15AnchoredAtom2729 Fin15AnchoredAtom2745 Fin15AnchoredAtom2758
    Fin15AnchoredAtom2759 Fin15AnchoredAtom2764 Fin15AnchoredAtom2780 Fin15AnchoredAtom2800
    Fin15AnchoredAtom4573 Fin15AnchoredAtom4575 Fin15AnchoredAtom4576 Fin15AnchoredAtom4584
    Fin15AnchoredAtom4585 Fin15AnchoredAtom4590 Fin15AnchoredAtom4599 Fin15AnchoredAtom4600
    Fin15AnchoredAtom4605 Fin15AnchoredAtom4621 Fin15AnchoredAtom4634 Fin15AnchoredAtom4635
    Fin15AnchoredAtom4640 Fin15AnchoredAtom4656 Fin15AnchoredAtom4676 Fin15AnchoredAtom4704
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

theorem fin15Anchored_clause31604 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2612 chi ∧
      ¬Fin15AnchoredAtom2614 chi ∧
      ¬Fin15AnchoredAtom2616 chi ∧
      ¬Fin15AnchoredAtom2618 chi ∧
      ¬Fin15AnchoredAtom2620 chi ∧
      ¬Fin15AnchoredAtom2622 chi ∧
      ¬Fin15AnchoredAtom2624 chi ∧
      ¬Fin15AnchoredAtom2631 chi ∧
      ¬Fin15AnchoredAtom2633 chi ∧
      ¬Fin15AnchoredAtom2638 chi ∧
      ¬Fin15AnchoredAtom2641 chi ∧
      ¬Fin15AnchoredAtom2643 chi ∧
      ¬Fin15AnchoredAtom2645 chi ∧
      ¬Fin15AnchoredAtom2652 chi ∧
      ¬Fin15AnchoredAtom2654 chi ∧
      ¬Fin15AnchoredAtom2659 chi ∧
      ¬Fin15AnchoredAtom2667 chi ∧
      ¬Fin15AnchoredAtom2669 chi ∧
      ¬Fin15AnchoredAtom2674 chi ∧
      ¬Fin15AnchoredAtom2690 chi ∧
      ¬Fin15AnchoredAtom2697 chi ∧
      ¬Fin15AnchoredAtom2699 chi ∧
      ¬Fin15AnchoredAtom2701 chi ∧
      ¬Fin15AnchoredAtom2708 chi ∧
      ¬Fin15AnchoredAtom2710 chi ∧
      ¬Fin15AnchoredAtom2715 chi ∧
      ¬Fin15AnchoredAtom2723 chi ∧
      ¬Fin15AnchoredAtom2725 chi ∧
      ¬Fin15AnchoredAtom2730 chi ∧
      ¬Fin15AnchoredAtom2746 chi ∧
      ¬Fin15AnchoredAtom2758 chi ∧
      ¬Fin15AnchoredAtom2760 chi ∧
      ¬Fin15AnchoredAtom2765 chi ∧
      ¬Fin15AnchoredAtom2781 chi ∧
      ¬Fin15AnchoredAtom2801 chi ∧
      ¬Fin15AnchoredAtom4573 chi ∧
      ¬Fin15AnchoredAtom4575 chi ∧
      ¬Fin15AnchoredAtom4577 chi ∧
      ¬Fin15AnchoredAtom4584 chi ∧
      ¬Fin15AnchoredAtom4586 chi ∧
      ¬Fin15AnchoredAtom4591 chi ∧
      ¬Fin15AnchoredAtom4599 chi ∧
      ¬Fin15AnchoredAtom4601 chi ∧
      ¬Fin15AnchoredAtom4606 chi ∧
      ¬Fin15AnchoredAtom4622 chi ∧
      ¬Fin15AnchoredAtom4634 chi ∧
      ¬Fin15AnchoredAtom4636 chi ∧
      ¬Fin15AnchoredAtom4641 chi ∧
      ¬Fin15AnchoredAtom4657 chi ∧
      ¬Fin15AnchoredAtom4677 chi ∧
      ¬Fin15AnchoredAtom4704 chi ∧
      ¬Fin15AnchoredAtom4706 chi ∧
      ¬Fin15AnchoredAtom4711 chi ∧
      ¬Fin15AnchoredAtom4727 chi ∧
      ¬Fin15AnchoredAtom4747 chi ∧
      ¬Fin15AnchoredAtom4782 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 5, 6, 7, 8, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21985
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2612 Fin15AnchoredAtom2614 Fin15AnchoredAtom2616
    Fin15AnchoredAtom2618 Fin15AnchoredAtom2620 Fin15AnchoredAtom2622 Fin15AnchoredAtom2624
    Fin15AnchoredAtom2631 Fin15AnchoredAtom2633 Fin15AnchoredAtom2638 Fin15AnchoredAtom2641
    Fin15AnchoredAtom2643 Fin15AnchoredAtom2645 Fin15AnchoredAtom2652 Fin15AnchoredAtom2654
    Fin15AnchoredAtom2659 Fin15AnchoredAtom2667 Fin15AnchoredAtom2669 Fin15AnchoredAtom2674
    Fin15AnchoredAtom2690 Fin15AnchoredAtom2697 Fin15AnchoredAtom2699 Fin15AnchoredAtom2701
    Fin15AnchoredAtom2708 Fin15AnchoredAtom2710 Fin15AnchoredAtom2715 Fin15AnchoredAtom2723
    Fin15AnchoredAtom2725 Fin15AnchoredAtom2730 Fin15AnchoredAtom2746 Fin15AnchoredAtom2758
    Fin15AnchoredAtom2760 Fin15AnchoredAtom2765 Fin15AnchoredAtom2781 Fin15AnchoredAtom2801
    Fin15AnchoredAtom4573 Fin15AnchoredAtom4575 Fin15AnchoredAtom4577 Fin15AnchoredAtom4584
    Fin15AnchoredAtom4586 Fin15AnchoredAtom4591 Fin15AnchoredAtom4599 Fin15AnchoredAtom4601
    Fin15AnchoredAtom4606 Fin15AnchoredAtom4622 Fin15AnchoredAtom4634 Fin15AnchoredAtom4636
    Fin15AnchoredAtom4641 Fin15AnchoredAtom4657 Fin15AnchoredAtom4677 Fin15AnchoredAtom4704
    Fin15AnchoredAtom4706 Fin15AnchoredAtom4711 Fin15AnchoredAtom4727 Fin15AnchoredAtom4747
    Fin15AnchoredAtom4782 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31605 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2612 chi ∧
      ¬Fin15AnchoredAtom2614 chi ∧
      ¬Fin15AnchoredAtom2617 chi ∧
      ¬Fin15AnchoredAtom2618 chi ∧
      ¬Fin15AnchoredAtom2620 chi ∧
      ¬Fin15AnchoredAtom2623 chi ∧
      ¬Fin15AnchoredAtom2624 chi ∧
      ¬Fin15AnchoredAtom2632 chi ∧
      ¬Fin15AnchoredAtom2633 chi ∧
      ¬Fin15AnchoredAtom2639 chi ∧
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
      ¬Fin15AnchoredAtom2697 chi ∧
      ¬Fin15AnchoredAtom2700 chi ∧
      ¬Fin15AnchoredAtom2701 chi ∧
      ¬Fin15AnchoredAtom2709 chi ∧
      ¬Fin15AnchoredAtom2710 chi ∧
      ¬Fin15AnchoredAtom2716 chi ∧
      ¬Fin15AnchoredAtom2724 chi ∧
      ¬Fin15AnchoredAtom2725 chi ∧
      ¬Fin15AnchoredAtom2731 chi ∧
      ¬Fin15AnchoredAtom2747 chi ∧
      ¬Fin15AnchoredAtom2759 chi ∧
      ¬Fin15AnchoredAtom2760 chi ∧
      ¬Fin15AnchoredAtom2766 chi ∧
      ¬Fin15AnchoredAtom2782 chi ∧
      ¬Fin15AnchoredAtom2802 chi ∧
      ¬Fin15AnchoredAtom4573 chi ∧
      ¬Fin15AnchoredAtom4576 chi ∧
      ¬Fin15AnchoredAtom4577 chi ∧
      ¬Fin15AnchoredAtom4585 chi ∧
      ¬Fin15AnchoredAtom4586 chi ∧
      ¬Fin15AnchoredAtom4592 chi ∧
      ¬Fin15AnchoredAtom4600 chi ∧
      ¬Fin15AnchoredAtom4601 chi ∧
      ¬Fin15AnchoredAtom4607 chi ∧
      ¬Fin15AnchoredAtom4623 chi ∧
      ¬Fin15AnchoredAtom4635 chi ∧
      ¬Fin15AnchoredAtom4636 chi ∧
      ¬Fin15AnchoredAtom4642 chi ∧
      ¬Fin15AnchoredAtom4658 chi ∧
      ¬Fin15AnchoredAtom4678 chi ∧
      ¬Fin15AnchoredAtom4705 chi ∧
      ¬Fin15AnchoredAtom4706 chi ∧
      ¬Fin15AnchoredAtom4712 chi ∧
      ¬Fin15AnchoredAtom4728 chi ∧
      ¬Fin15AnchoredAtom4748 chi ∧
      ¬Fin15AnchoredAtom4783 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 5, 6, 7, 8, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26081
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2612 Fin15AnchoredAtom2614 Fin15AnchoredAtom2617
    Fin15AnchoredAtom2618 Fin15AnchoredAtom2620 Fin15AnchoredAtom2623 Fin15AnchoredAtom2624
    Fin15AnchoredAtom2632 Fin15AnchoredAtom2633 Fin15AnchoredAtom2639 Fin15AnchoredAtom2641
    Fin15AnchoredAtom2644 Fin15AnchoredAtom2645 Fin15AnchoredAtom2653 Fin15AnchoredAtom2654
    Fin15AnchoredAtom2660 Fin15AnchoredAtom2668 Fin15AnchoredAtom2669 Fin15AnchoredAtom2675
    Fin15AnchoredAtom2691 Fin15AnchoredAtom2697 Fin15AnchoredAtom2700 Fin15AnchoredAtom2701
    Fin15AnchoredAtom2709 Fin15AnchoredAtom2710 Fin15AnchoredAtom2716 Fin15AnchoredAtom2724
    Fin15AnchoredAtom2725 Fin15AnchoredAtom2731 Fin15AnchoredAtom2747 Fin15AnchoredAtom2759
    Fin15AnchoredAtom2760 Fin15AnchoredAtom2766 Fin15AnchoredAtom2782 Fin15AnchoredAtom2802
    Fin15AnchoredAtom4573 Fin15AnchoredAtom4576 Fin15AnchoredAtom4577 Fin15AnchoredAtom4585
    Fin15AnchoredAtom4586 Fin15AnchoredAtom4592 Fin15AnchoredAtom4600 Fin15AnchoredAtom4601
    Fin15AnchoredAtom4607 Fin15AnchoredAtom4623 Fin15AnchoredAtom4635 Fin15AnchoredAtom4636
    Fin15AnchoredAtom4642 Fin15AnchoredAtom4658 Fin15AnchoredAtom4678 Fin15AnchoredAtom4705
    Fin15AnchoredAtom4706 Fin15AnchoredAtom4712 Fin15AnchoredAtom4728 Fin15AnchoredAtom4748
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

theorem fin15Anchored_clause31606 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2613 chi ∧
      ¬Fin15AnchoredAtom2614 chi ∧
      ¬Fin15AnchoredAtom2616 chi ∧
      ¬Fin15AnchoredAtom2617 chi ∧
      ¬Fin15AnchoredAtom2625 chi ∧
      ¬Fin15AnchoredAtom2627 chi ∧
      ¬Fin15AnchoredAtom2628 chi ∧
      ¬Fin15AnchoredAtom2631 chi ∧
      ¬Fin15AnchoredAtom2632 chi ∧
      ¬Fin15AnchoredAtom2637 chi ∧
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
      ¬Fin15AnchoredAtom4578 chi ∧
      ¬Fin15AnchoredAtom4580 chi ∧
      ¬Fin15AnchoredAtom4581 chi ∧
      ¬Fin15AnchoredAtom4584 chi ∧
      ¬Fin15AnchoredAtom4585 chi ∧
      ¬Fin15AnchoredAtom4590 chi ∧
      ¬Fin15AnchoredAtom4609 chi ∧
      ¬Fin15AnchoredAtom4610 chi ∧
      ¬Fin15AnchoredAtom4615 chi ∧
      ¬Fin15AnchoredAtom4621 chi ∧
      ¬Fin15AnchoredAtom4644 chi ∧
      ¬Fin15AnchoredAtom4645 chi ∧
      ¬Fin15AnchoredAtom4650 chi ∧
      ¬Fin15AnchoredAtom4656 chi ∧
      ¬Fin15AnchoredAtom4686 chi ∧
      ¬Fin15AnchoredAtom4714 chi ∧
      ¬Fin15AnchoredAtom4715 chi ∧
      ¬Fin15AnchoredAtom4720 chi ∧
      ¬Fin15AnchoredAtom4726 chi ∧
      ¬Fin15AnchoredAtom4756 chi ∧
      ¬Fin15AnchoredAtom4791 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 5, 6, 7, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask14049
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2613 Fin15AnchoredAtom2614 Fin15AnchoredAtom2616
    Fin15AnchoredAtom2617 Fin15AnchoredAtom2625 Fin15AnchoredAtom2627 Fin15AnchoredAtom2628
    Fin15AnchoredAtom2631 Fin15AnchoredAtom2632 Fin15AnchoredAtom2637 Fin15AnchoredAtom2646
    Fin15AnchoredAtom2648 Fin15AnchoredAtom2649 Fin15AnchoredAtom2652 Fin15AnchoredAtom2653
    Fin15AnchoredAtom2658 Fin15AnchoredAtom2677 Fin15AnchoredAtom2678 Fin15AnchoredAtom2683
    Fin15AnchoredAtom2689 Fin15AnchoredAtom2702 Fin15AnchoredAtom2704 Fin15AnchoredAtom2705
    Fin15AnchoredAtom2708 Fin15AnchoredAtom2709 Fin15AnchoredAtom2714 Fin15AnchoredAtom2733
    Fin15AnchoredAtom2734 Fin15AnchoredAtom2739 Fin15AnchoredAtom2745 Fin15AnchoredAtom2768
    Fin15AnchoredAtom2769 Fin15AnchoredAtom2774 Fin15AnchoredAtom2780 Fin15AnchoredAtom2810
    Fin15AnchoredAtom4578 Fin15AnchoredAtom4580 Fin15AnchoredAtom4581 Fin15AnchoredAtom4584
    Fin15AnchoredAtom4585 Fin15AnchoredAtom4590 Fin15AnchoredAtom4609 Fin15AnchoredAtom4610
    Fin15AnchoredAtom4615 Fin15AnchoredAtom4621 Fin15AnchoredAtom4644 Fin15AnchoredAtom4645
    Fin15AnchoredAtom4650 Fin15AnchoredAtom4656 Fin15AnchoredAtom4686 Fin15AnchoredAtom4714
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

theorem fin15Anchored_clause31607 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2613 chi ∧
      ¬Fin15AnchoredAtom2614 chi ∧
      ¬Fin15AnchoredAtom2616 chi ∧
      ¬Fin15AnchoredAtom2618 chi ∧
      ¬Fin15AnchoredAtom2625 chi ∧
      ¬Fin15AnchoredAtom2627 chi ∧
      ¬Fin15AnchoredAtom2629 chi ∧
      ¬Fin15AnchoredAtom2631 chi ∧
      ¬Fin15AnchoredAtom2633 chi ∧
      ¬Fin15AnchoredAtom2638 chi ∧
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
      ¬Fin15AnchoredAtom4578 chi ∧
      ¬Fin15AnchoredAtom4580 chi ∧
      ¬Fin15AnchoredAtom4582 chi ∧
      ¬Fin15AnchoredAtom4584 chi ∧
      ¬Fin15AnchoredAtom4586 chi ∧
      ¬Fin15AnchoredAtom4591 chi ∧
      ¬Fin15AnchoredAtom4609 chi ∧
      ¬Fin15AnchoredAtom4611 chi ∧
      ¬Fin15AnchoredAtom4616 chi ∧
      ¬Fin15AnchoredAtom4622 chi ∧
      ¬Fin15AnchoredAtom4644 chi ∧
      ¬Fin15AnchoredAtom4646 chi ∧
      ¬Fin15AnchoredAtom4651 chi ∧
      ¬Fin15AnchoredAtom4657 chi ∧
      ¬Fin15AnchoredAtom4687 chi ∧
      ¬Fin15AnchoredAtom4714 chi ∧
      ¬Fin15AnchoredAtom4716 chi ∧
      ¬Fin15AnchoredAtom4721 chi ∧
      ¬Fin15AnchoredAtom4727 chi ∧
      ¬Fin15AnchoredAtom4757 chi ∧
      ¬Fin15AnchoredAtom4792 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 5, 6, 7, 9, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22241
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2613 Fin15AnchoredAtom2614 Fin15AnchoredAtom2616
    Fin15AnchoredAtom2618 Fin15AnchoredAtom2625 Fin15AnchoredAtom2627 Fin15AnchoredAtom2629
    Fin15AnchoredAtom2631 Fin15AnchoredAtom2633 Fin15AnchoredAtom2638 Fin15AnchoredAtom2646
    Fin15AnchoredAtom2648 Fin15AnchoredAtom2650 Fin15AnchoredAtom2652 Fin15AnchoredAtom2654
    Fin15AnchoredAtom2659 Fin15AnchoredAtom2677 Fin15AnchoredAtom2679 Fin15AnchoredAtom2684
    Fin15AnchoredAtom2690 Fin15AnchoredAtom2702 Fin15AnchoredAtom2704 Fin15AnchoredAtom2706
    Fin15AnchoredAtom2708 Fin15AnchoredAtom2710 Fin15AnchoredAtom2715 Fin15AnchoredAtom2733
    Fin15AnchoredAtom2735 Fin15AnchoredAtom2740 Fin15AnchoredAtom2746 Fin15AnchoredAtom2768
    Fin15AnchoredAtom2770 Fin15AnchoredAtom2775 Fin15AnchoredAtom2781 Fin15AnchoredAtom2811
    Fin15AnchoredAtom4578 Fin15AnchoredAtom4580 Fin15AnchoredAtom4582 Fin15AnchoredAtom4584
    Fin15AnchoredAtom4586 Fin15AnchoredAtom4591 Fin15AnchoredAtom4609 Fin15AnchoredAtom4611
    Fin15AnchoredAtom4616 Fin15AnchoredAtom4622 Fin15AnchoredAtom4644 Fin15AnchoredAtom4646
    Fin15AnchoredAtom4651 Fin15AnchoredAtom4657 Fin15AnchoredAtom4687 Fin15AnchoredAtom4714
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

theorem fin15Anchored_clause31608 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2613 chi ∧
      ¬Fin15AnchoredAtom2614 chi ∧
      ¬Fin15AnchoredAtom2617 chi ∧
      ¬Fin15AnchoredAtom2618 chi ∧
      ¬Fin15AnchoredAtom2625 chi ∧
      ¬Fin15AnchoredAtom2628 chi ∧
      ¬Fin15AnchoredAtom2629 chi ∧
      ¬Fin15AnchoredAtom2632 chi ∧
      ¬Fin15AnchoredAtom2633 chi ∧
      ¬Fin15AnchoredAtom2639 chi ∧
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
      ¬Fin15AnchoredAtom4578 chi ∧
      ¬Fin15AnchoredAtom4581 chi ∧
      ¬Fin15AnchoredAtom4582 chi ∧
      ¬Fin15AnchoredAtom4585 chi ∧
      ¬Fin15AnchoredAtom4586 chi ∧
      ¬Fin15AnchoredAtom4592 chi ∧
      ¬Fin15AnchoredAtom4610 chi ∧
      ¬Fin15AnchoredAtom4611 chi ∧
      ¬Fin15AnchoredAtom4617 chi ∧
      ¬Fin15AnchoredAtom4623 chi ∧
      ¬Fin15AnchoredAtom4645 chi ∧
      ¬Fin15AnchoredAtom4646 chi ∧
      ¬Fin15AnchoredAtom4652 chi ∧
      ¬Fin15AnchoredAtom4658 chi ∧
      ¬Fin15AnchoredAtom4688 chi ∧
      ¬Fin15AnchoredAtom4715 chi ∧
      ¬Fin15AnchoredAtom4716 chi ∧
      ¬Fin15AnchoredAtom4722 chi ∧
      ¬Fin15AnchoredAtom4728 chi ∧
      ¬Fin15AnchoredAtom4758 chi ∧
      ¬Fin15AnchoredAtom4793 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 5, 6, 7, 9, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26337
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2613 Fin15AnchoredAtom2614 Fin15AnchoredAtom2617
    Fin15AnchoredAtom2618 Fin15AnchoredAtom2625 Fin15AnchoredAtom2628 Fin15AnchoredAtom2629
    Fin15AnchoredAtom2632 Fin15AnchoredAtom2633 Fin15AnchoredAtom2639 Fin15AnchoredAtom2646
    Fin15AnchoredAtom2649 Fin15AnchoredAtom2650 Fin15AnchoredAtom2653 Fin15AnchoredAtom2654
    Fin15AnchoredAtom2660 Fin15AnchoredAtom2678 Fin15AnchoredAtom2679 Fin15AnchoredAtom2685
    Fin15AnchoredAtom2691 Fin15AnchoredAtom2702 Fin15AnchoredAtom2705 Fin15AnchoredAtom2706
    Fin15AnchoredAtom2709 Fin15AnchoredAtom2710 Fin15AnchoredAtom2716 Fin15AnchoredAtom2734
    Fin15AnchoredAtom2735 Fin15AnchoredAtom2741 Fin15AnchoredAtom2747 Fin15AnchoredAtom2769
    Fin15AnchoredAtom2770 Fin15AnchoredAtom2776 Fin15AnchoredAtom2782 Fin15AnchoredAtom2812
    Fin15AnchoredAtom4578 Fin15AnchoredAtom4581 Fin15AnchoredAtom4582 Fin15AnchoredAtom4585
    Fin15AnchoredAtom4586 Fin15AnchoredAtom4592 Fin15AnchoredAtom4610 Fin15AnchoredAtom4611
    Fin15AnchoredAtom4617 Fin15AnchoredAtom4623 Fin15AnchoredAtom4645 Fin15AnchoredAtom4646
    Fin15AnchoredAtom4652 Fin15AnchoredAtom4658 Fin15AnchoredAtom4688 Fin15AnchoredAtom4715
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

theorem fin15Anchored_clause31609 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2613 chi ∧
      ¬Fin15AnchoredAtom2616 chi ∧
      ¬Fin15AnchoredAtom2617 chi ∧
      ¬Fin15AnchoredAtom2618 chi ∧
      ¬Fin15AnchoredAtom2627 chi ∧
      ¬Fin15AnchoredAtom2628 chi ∧
      ¬Fin15AnchoredAtom2629 chi ∧
      ¬Fin15AnchoredAtom2637 chi ∧
      ¬Fin15AnchoredAtom2638 chi ∧
      ¬Fin15AnchoredAtom2639 chi ∧
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
      ¬Fin15AnchoredAtom4580 chi ∧
      ¬Fin15AnchoredAtom4581 chi ∧
      ¬Fin15AnchoredAtom4582 chi ∧
      ¬Fin15AnchoredAtom4590 chi ∧
      ¬Fin15AnchoredAtom4591 chi ∧
      ¬Fin15AnchoredAtom4592 chi ∧
      ¬Fin15AnchoredAtom4615 chi ∧
      ¬Fin15AnchoredAtom4616 chi ∧
      ¬Fin15AnchoredAtom4617 chi ∧
      ¬Fin15AnchoredAtom4627 chi ∧
      ¬Fin15AnchoredAtom4650 chi ∧
      ¬Fin15AnchoredAtom4651 chi ∧
      ¬Fin15AnchoredAtom4652 chi ∧
      ¬Fin15AnchoredAtom4662 chi ∧
      ¬Fin15AnchoredAtom4692 chi ∧
      ¬Fin15AnchoredAtom4720 chi ∧
      ¬Fin15AnchoredAtom4721 chi ∧
      ¬Fin15AnchoredAtom4722 chi ∧
      ¬Fin15AnchoredAtom4732 chi ∧
      ¬Fin15AnchoredAtom4762 chi ∧
      ¬Fin15AnchoredAtom4797 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 5, 6, 7, 9, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29409
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2613 Fin15AnchoredAtom2616 Fin15AnchoredAtom2617
    Fin15AnchoredAtom2618 Fin15AnchoredAtom2627 Fin15AnchoredAtom2628 Fin15AnchoredAtom2629
    Fin15AnchoredAtom2637 Fin15AnchoredAtom2638 Fin15AnchoredAtom2639 Fin15AnchoredAtom2648
    Fin15AnchoredAtom2649 Fin15AnchoredAtom2650 Fin15AnchoredAtom2658 Fin15AnchoredAtom2659
    Fin15AnchoredAtom2660 Fin15AnchoredAtom2683 Fin15AnchoredAtom2684 Fin15AnchoredAtom2685
    Fin15AnchoredAtom2695 Fin15AnchoredAtom2704 Fin15AnchoredAtom2705 Fin15AnchoredAtom2706
    Fin15AnchoredAtom2714 Fin15AnchoredAtom2715 Fin15AnchoredAtom2716 Fin15AnchoredAtom2739
    Fin15AnchoredAtom2740 Fin15AnchoredAtom2741 Fin15AnchoredAtom2751 Fin15AnchoredAtom2774
    Fin15AnchoredAtom2775 Fin15AnchoredAtom2776 Fin15AnchoredAtom2786 Fin15AnchoredAtom2816
    Fin15AnchoredAtom4580 Fin15AnchoredAtom4581 Fin15AnchoredAtom4582 Fin15AnchoredAtom4590
    Fin15AnchoredAtom4591 Fin15AnchoredAtom4592 Fin15AnchoredAtom4615 Fin15AnchoredAtom4616
    Fin15AnchoredAtom4617 Fin15AnchoredAtom4627 Fin15AnchoredAtom4650 Fin15AnchoredAtom4651
    Fin15AnchoredAtom4652 Fin15AnchoredAtom4662 Fin15AnchoredAtom4692 Fin15AnchoredAtom4720
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

theorem fin15Anchored_clause31610 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2614 chi ∧
      ¬Fin15AnchoredAtom2615 chi ∧
      ¬Fin15AnchoredAtom2616 chi ∧
      ¬Fin15AnchoredAtom2618 chi ∧
      ¬Fin15AnchoredAtom2630 chi ∧
      ¬Fin15AnchoredAtom2631 chi ∧
      ¬Fin15AnchoredAtom2633 chi ∧
      ¬Fin15AnchoredAtom2634 chi ∧
      ¬Fin15AnchoredAtom2636 chi ∧
      ¬Fin15AnchoredAtom2638 chi ∧
      ¬Fin15AnchoredAtom2651 chi ∧
      ¬Fin15AnchoredAtom2652 chi ∧
      ¬Fin15AnchoredAtom2654 chi ∧
      ¬Fin15AnchoredAtom2655 chi ∧
      ¬Fin15AnchoredAtom2657 chi ∧
      ¬Fin15AnchoredAtom2659 chi ∧
      ¬Fin15AnchoredAtom2686 chi ∧
      ¬Fin15AnchoredAtom2688 chi ∧
      ¬Fin15AnchoredAtom2690 chi ∧
      ¬Fin15AnchoredAtom2693 chi ∧
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
      ¬Fin15AnchoredAtom4583 chi ∧
      ¬Fin15AnchoredAtom4584 chi ∧
      ¬Fin15AnchoredAtom4586 chi ∧
      ¬Fin15AnchoredAtom4587 chi ∧
      ¬Fin15AnchoredAtom4589 chi ∧
      ¬Fin15AnchoredAtom4591 chi ∧
      ¬Fin15AnchoredAtom4618 chi ∧
      ¬Fin15AnchoredAtom4620 chi ∧
      ¬Fin15AnchoredAtom4622 chi ∧
      ¬Fin15AnchoredAtom4625 chi ∧
      ¬Fin15AnchoredAtom4653 chi ∧
      ¬Fin15AnchoredAtom4655 chi ∧
      ¬Fin15AnchoredAtom4657 chi ∧
      ¬Fin15AnchoredAtom4660 chi ∧
      ¬Fin15AnchoredAtom4694 chi ∧
      ¬Fin15AnchoredAtom4723 chi ∧
      ¬Fin15AnchoredAtom4725 chi ∧
      ¬Fin15AnchoredAtom4727 chi ∧
      ¬Fin15AnchoredAtom4730 chi ∧
      ¬Fin15AnchoredAtom4764 chi ∧
      ¬Fin15AnchoredAtom4799 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 5, 6, 7, 10, 11, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask23777
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2614 Fin15AnchoredAtom2615 Fin15AnchoredAtom2616
    Fin15AnchoredAtom2618 Fin15AnchoredAtom2630 Fin15AnchoredAtom2631 Fin15AnchoredAtom2633
    Fin15AnchoredAtom2634 Fin15AnchoredAtom2636 Fin15AnchoredAtom2638 Fin15AnchoredAtom2651
    Fin15AnchoredAtom2652 Fin15AnchoredAtom2654 Fin15AnchoredAtom2655 Fin15AnchoredAtom2657
    Fin15AnchoredAtom2659 Fin15AnchoredAtom2686 Fin15AnchoredAtom2688 Fin15AnchoredAtom2690
    Fin15AnchoredAtom2693 Fin15AnchoredAtom2707 Fin15AnchoredAtom2708 Fin15AnchoredAtom2710
    Fin15AnchoredAtom2711 Fin15AnchoredAtom2713 Fin15AnchoredAtom2715 Fin15AnchoredAtom2742
    Fin15AnchoredAtom2744 Fin15AnchoredAtom2746 Fin15AnchoredAtom2749 Fin15AnchoredAtom2777
    Fin15AnchoredAtom2779 Fin15AnchoredAtom2781 Fin15AnchoredAtom2784 Fin15AnchoredAtom2818
    Fin15AnchoredAtom4583 Fin15AnchoredAtom4584 Fin15AnchoredAtom4586 Fin15AnchoredAtom4587
    Fin15AnchoredAtom4589 Fin15AnchoredAtom4591 Fin15AnchoredAtom4618 Fin15AnchoredAtom4620
    Fin15AnchoredAtom4622 Fin15AnchoredAtom4625 Fin15AnchoredAtom4653 Fin15AnchoredAtom4655
    Fin15AnchoredAtom4657 Fin15AnchoredAtom4660 Fin15AnchoredAtom4694 Fin15AnchoredAtom4723
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

theorem fin15Anchored_clause31611 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2614 chi ∧
      ¬Fin15AnchoredAtom2616 chi ∧
      ¬Fin15AnchoredAtom2617 chi ∧
      ¬Fin15AnchoredAtom2618 chi ∧
      ¬Fin15AnchoredAtom2631 chi ∧
      ¬Fin15AnchoredAtom2632 chi ∧
      ¬Fin15AnchoredAtom2633 chi ∧
      ¬Fin15AnchoredAtom2637 chi ∧
      ¬Fin15AnchoredAtom2638 chi ∧
      ¬Fin15AnchoredAtom2639 chi ∧
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
      ¬Fin15AnchoredAtom4584 chi ∧
      ¬Fin15AnchoredAtom4585 chi ∧
      ¬Fin15AnchoredAtom4586 chi ∧
      ¬Fin15AnchoredAtom4590 chi ∧
      ¬Fin15AnchoredAtom4591 chi ∧
      ¬Fin15AnchoredAtom4592 chi ∧
      ¬Fin15AnchoredAtom4621 chi ∧
      ¬Fin15AnchoredAtom4622 chi ∧
      ¬Fin15AnchoredAtom4623 chi ∧
      ¬Fin15AnchoredAtom4627 chi ∧
      ¬Fin15AnchoredAtom4656 chi ∧
      ¬Fin15AnchoredAtom4657 chi ∧
      ¬Fin15AnchoredAtom4658 chi ∧
      ¬Fin15AnchoredAtom4662 chi ∧
      ¬Fin15AnchoredAtom4696 chi ∧
      ¬Fin15AnchoredAtom4726 chi ∧
      ¬Fin15AnchoredAtom4727 chi ∧
      ¬Fin15AnchoredAtom4728 chi ∧
      ¬Fin15AnchoredAtom4732 chi ∧
      ¬Fin15AnchoredAtom4766 chi ∧
      ¬Fin15AnchoredAtom4801 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 5, 6, 7, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29921
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2614 Fin15AnchoredAtom2616 Fin15AnchoredAtom2617
    Fin15AnchoredAtom2618 Fin15AnchoredAtom2631 Fin15AnchoredAtom2632 Fin15AnchoredAtom2633
    Fin15AnchoredAtom2637 Fin15AnchoredAtom2638 Fin15AnchoredAtom2639 Fin15AnchoredAtom2652
    Fin15AnchoredAtom2653 Fin15AnchoredAtom2654 Fin15AnchoredAtom2658 Fin15AnchoredAtom2659
    Fin15AnchoredAtom2660 Fin15AnchoredAtom2689 Fin15AnchoredAtom2690 Fin15AnchoredAtom2691
    Fin15AnchoredAtom2695 Fin15AnchoredAtom2708 Fin15AnchoredAtom2709 Fin15AnchoredAtom2710
    Fin15AnchoredAtom2714 Fin15AnchoredAtom2715 Fin15AnchoredAtom2716 Fin15AnchoredAtom2745
    Fin15AnchoredAtom2746 Fin15AnchoredAtom2747 Fin15AnchoredAtom2751 Fin15AnchoredAtom2780
    Fin15AnchoredAtom2781 Fin15AnchoredAtom2782 Fin15AnchoredAtom2786 Fin15AnchoredAtom2820
    Fin15AnchoredAtom4584 Fin15AnchoredAtom4585 Fin15AnchoredAtom4586 Fin15AnchoredAtom4590
    Fin15AnchoredAtom4591 Fin15AnchoredAtom4592 Fin15AnchoredAtom4621 Fin15AnchoredAtom4622
    Fin15AnchoredAtom4623 Fin15AnchoredAtom4627 Fin15AnchoredAtom4656 Fin15AnchoredAtom4657
    Fin15AnchoredAtom4658 Fin15AnchoredAtom4662 Fin15AnchoredAtom4696 Fin15AnchoredAtom4726
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

theorem fin15Anchored_clause31612 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2619 chi ∧
      ¬Fin15AnchoredAtom2620 chi ∧
      ¬Fin15AnchoredAtom2622 chi ∧
      ¬Fin15AnchoredAtom2623 chi ∧
      ¬Fin15AnchoredAtom2625 chi ∧
      ¬Fin15AnchoredAtom2627 chi ∧
      ¬Fin15AnchoredAtom2628 chi ∧
      ¬Fin15AnchoredAtom2631 chi ∧
      ¬Fin15AnchoredAtom2632 chi ∧
      ¬Fin15AnchoredAtom2637 chi ∧
      ¬Fin15AnchoredAtom2661 chi ∧
      ¬Fin15AnchoredAtom2663 chi ∧
      ¬Fin15AnchoredAtom2664 chi ∧
      ¬Fin15AnchoredAtom2667 chi ∧
      ¬Fin15AnchoredAtom2668 chi ∧
      ¬Fin15AnchoredAtom2673 chi ∧
      ¬Fin15AnchoredAtom2677 chi ∧
      ¬Fin15AnchoredAtom2678 chi ∧
      ¬Fin15AnchoredAtom2683 chi ∧
      ¬Fin15AnchoredAtom2689 chi ∧
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
      ¬Fin15AnchoredAtom4593 chi ∧
      ¬Fin15AnchoredAtom4595 chi ∧
      ¬Fin15AnchoredAtom4596 chi ∧
      ¬Fin15AnchoredAtom4599 chi ∧
      ¬Fin15AnchoredAtom4600 chi ∧
      ¬Fin15AnchoredAtom4605 chi ∧
      ¬Fin15AnchoredAtom4609 chi ∧
      ¬Fin15AnchoredAtom4610 chi ∧
      ¬Fin15AnchoredAtom4615 chi ∧
      ¬Fin15AnchoredAtom4621 chi ∧
      ¬Fin15AnchoredAtom4664 chi ∧
      ¬Fin15AnchoredAtom4665 chi ∧
      ¬Fin15AnchoredAtom4670 chi ∧
      ¬Fin15AnchoredAtom4676 chi ∧
      ¬Fin15AnchoredAtom4686 chi ∧
      ¬Fin15AnchoredAtom4734 chi ∧
      ¬Fin15AnchoredAtom4735 chi ∧
      ¬Fin15AnchoredAtom4740 chi ∧
      ¬Fin15AnchoredAtom4746 chi ∧
      ¬Fin15AnchoredAtom4756 chi ∧
      ¬Fin15AnchoredAtom4806 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 5, 6, 8, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask14177
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2619 Fin15AnchoredAtom2620 Fin15AnchoredAtom2622
    Fin15AnchoredAtom2623 Fin15AnchoredAtom2625 Fin15AnchoredAtom2627 Fin15AnchoredAtom2628
    Fin15AnchoredAtom2631 Fin15AnchoredAtom2632 Fin15AnchoredAtom2637 Fin15AnchoredAtom2661
    Fin15AnchoredAtom2663 Fin15AnchoredAtom2664 Fin15AnchoredAtom2667 Fin15AnchoredAtom2668
    Fin15AnchoredAtom2673 Fin15AnchoredAtom2677 Fin15AnchoredAtom2678 Fin15AnchoredAtom2683
    Fin15AnchoredAtom2689 Fin15AnchoredAtom2717 Fin15AnchoredAtom2719 Fin15AnchoredAtom2720
    Fin15AnchoredAtom2723 Fin15AnchoredAtom2724 Fin15AnchoredAtom2729 Fin15AnchoredAtom2733
    Fin15AnchoredAtom2734 Fin15AnchoredAtom2739 Fin15AnchoredAtom2745 Fin15AnchoredAtom2788
    Fin15AnchoredAtom2789 Fin15AnchoredAtom2794 Fin15AnchoredAtom2800 Fin15AnchoredAtom2810
    Fin15AnchoredAtom4593 Fin15AnchoredAtom4595 Fin15AnchoredAtom4596 Fin15AnchoredAtom4599
    Fin15AnchoredAtom4600 Fin15AnchoredAtom4605 Fin15AnchoredAtom4609 Fin15AnchoredAtom4610
    Fin15AnchoredAtom4615 Fin15AnchoredAtom4621 Fin15AnchoredAtom4664 Fin15AnchoredAtom4665
    Fin15AnchoredAtom4670 Fin15AnchoredAtom4676 Fin15AnchoredAtom4686 Fin15AnchoredAtom4734
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

theorem fin15Anchored_clause31613 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2619 chi ∧
      ¬Fin15AnchoredAtom2620 chi ∧
      ¬Fin15AnchoredAtom2622 chi ∧
      ¬Fin15AnchoredAtom2624 chi ∧
      ¬Fin15AnchoredAtom2625 chi ∧
      ¬Fin15AnchoredAtom2627 chi ∧
      ¬Fin15AnchoredAtom2629 chi ∧
      ¬Fin15AnchoredAtom2631 chi ∧
      ¬Fin15AnchoredAtom2633 chi ∧
      ¬Fin15AnchoredAtom2638 chi ∧
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
      ¬Fin15AnchoredAtom4593 chi ∧
      ¬Fin15AnchoredAtom4595 chi ∧
      ¬Fin15AnchoredAtom4597 chi ∧
      ¬Fin15AnchoredAtom4599 chi ∧
      ¬Fin15AnchoredAtom4601 chi ∧
      ¬Fin15AnchoredAtom4606 chi ∧
      ¬Fin15AnchoredAtom4609 chi ∧
      ¬Fin15AnchoredAtom4611 chi ∧
      ¬Fin15AnchoredAtom4616 chi ∧
      ¬Fin15AnchoredAtom4622 chi ∧
      ¬Fin15AnchoredAtom4664 chi ∧
      ¬Fin15AnchoredAtom4666 chi ∧
      ¬Fin15AnchoredAtom4671 chi ∧
      ¬Fin15AnchoredAtom4677 chi ∧
      ¬Fin15AnchoredAtom4687 chi ∧
      ¬Fin15AnchoredAtom4734 chi ∧
      ¬Fin15AnchoredAtom4736 chi ∧
      ¬Fin15AnchoredAtom4741 chi ∧
      ¬Fin15AnchoredAtom4747 chi ∧
      ¬Fin15AnchoredAtom4757 chi ∧
      ¬Fin15AnchoredAtom4807 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 5, 6, 8, 9, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22369
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2619 Fin15AnchoredAtom2620 Fin15AnchoredAtom2622
    Fin15AnchoredAtom2624 Fin15AnchoredAtom2625 Fin15AnchoredAtom2627 Fin15AnchoredAtom2629
    Fin15AnchoredAtom2631 Fin15AnchoredAtom2633 Fin15AnchoredAtom2638 Fin15AnchoredAtom2661
    Fin15AnchoredAtom2663 Fin15AnchoredAtom2665 Fin15AnchoredAtom2667 Fin15AnchoredAtom2669
    Fin15AnchoredAtom2674 Fin15AnchoredAtom2677 Fin15AnchoredAtom2679 Fin15AnchoredAtom2684
    Fin15AnchoredAtom2690 Fin15AnchoredAtom2717 Fin15AnchoredAtom2719 Fin15AnchoredAtom2721
    Fin15AnchoredAtom2723 Fin15AnchoredAtom2725 Fin15AnchoredAtom2730 Fin15AnchoredAtom2733
    Fin15AnchoredAtom2735 Fin15AnchoredAtom2740 Fin15AnchoredAtom2746 Fin15AnchoredAtom2788
    Fin15AnchoredAtom2790 Fin15AnchoredAtom2795 Fin15AnchoredAtom2801 Fin15AnchoredAtom2811
    Fin15AnchoredAtom4593 Fin15AnchoredAtom4595 Fin15AnchoredAtom4597 Fin15AnchoredAtom4599
    Fin15AnchoredAtom4601 Fin15AnchoredAtom4606 Fin15AnchoredAtom4609 Fin15AnchoredAtom4611
    Fin15AnchoredAtom4616 Fin15AnchoredAtom4622 Fin15AnchoredAtom4664 Fin15AnchoredAtom4666
    Fin15AnchoredAtom4671 Fin15AnchoredAtom4677 Fin15AnchoredAtom4687 Fin15AnchoredAtom4734
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

theorem fin15Anchored_clause31614 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2619 chi ∧
      ¬Fin15AnchoredAtom2620 chi ∧
      ¬Fin15AnchoredAtom2623 chi ∧
      ¬Fin15AnchoredAtom2624 chi ∧
      ¬Fin15AnchoredAtom2625 chi ∧
      ¬Fin15AnchoredAtom2628 chi ∧
      ¬Fin15AnchoredAtom2629 chi ∧
      ¬Fin15AnchoredAtom2632 chi ∧
      ¬Fin15AnchoredAtom2633 chi ∧
      ¬Fin15AnchoredAtom2639 chi ∧
      ¬Fin15AnchoredAtom2661 chi ∧
      ¬Fin15AnchoredAtom2664 chi ∧
      ¬Fin15AnchoredAtom2665 chi ∧
      ¬Fin15AnchoredAtom2668 chi ∧
      ¬Fin15AnchoredAtom2669 chi ∧
      ¬Fin15AnchoredAtom2675 chi ∧
      ¬Fin15AnchoredAtom2678 chi ∧
      ¬Fin15AnchoredAtom2679 chi ∧
      ¬Fin15AnchoredAtom2685 chi ∧
      ¬Fin15AnchoredAtom2691 chi ∧
      ¬Fin15AnchoredAtom2717 chi ∧
      ¬Fin15AnchoredAtom2720 chi ∧
      ¬Fin15AnchoredAtom2721 chi ∧
      ¬Fin15AnchoredAtom2724 chi ∧
      ¬Fin15AnchoredAtom2725 chi ∧
      ¬Fin15AnchoredAtom2731 chi ∧
      ¬Fin15AnchoredAtom2734 chi ∧
      ¬Fin15AnchoredAtom2735 chi ∧
      ¬Fin15AnchoredAtom2741 chi ∧
      ¬Fin15AnchoredAtom2747 chi ∧
      ¬Fin15AnchoredAtom2789 chi ∧
      ¬Fin15AnchoredAtom2790 chi ∧
      ¬Fin15AnchoredAtom2796 chi ∧
      ¬Fin15AnchoredAtom2802 chi ∧
      ¬Fin15AnchoredAtom2812 chi ∧
      ¬Fin15AnchoredAtom4593 chi ∧
      ¬Fin15AnchoredAtom4596 chi ∧
      ¬Fin15AnchoredAtom4597 chi ∧
      ¬Fin15AnchoredAtom4600 chi ∧
      ¬Fin15AnchoredAtom4601 chi ∧
      ¬Fin15AnchoredAtom4607 chi ∧
      ¬Fin15AnchoredAtom4610 chi ∧
      ¬Fin15AnchoredAtom4611 chi ∧
      ¬Fin15AnchoredAtom4617 chi ∧
      ¬Fin15AnchoredAtom4623 chi ∧
      ¬Fin15AnchoredAtom4665 chi ∧
      ¬Fin15AnchoredAtom4666 chi ∧
      ¬Fin15AnchoredAtom4672 chi ∧
      ¬Fin15AnchoredAtom4678 chi ∧
      ¬Fin15AnchoredAtom4688 chi ∧
      ¬Fin15AnchoredAtom4735 chi ∧
      ¬Fin15AnchoredAtom4736 chi ∧
      ¬Fin15AnchoredAtom4742 chi ∧
      ¬Fin15AnchoredAtom4748 chi ∧
      ¬Fin15AnchoredAtom4758 chi ∧
      ¬Fin15AnchoredAtom4808 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 5, 6, 8, 9, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26465
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2619 Fin15AnchoredAtom2620 Fin15AnchoredAtom2623
    Fin15AnchoredAtom2624 Fin15AnchoredAtom2625 Fin15AnchoredAtom2628 Fin15AnchoredAtom2629
    Fin15AnchoredAtom2632 Fin15AnchoredAtom2633 Fin15AnchoredAtom2639 Fin15AnchoredAtom2661
    Fin15AnchoredAtom2664 Fin15AnchoredAtom2665 Fin15AnchoredAtom2668 Fin15AnchoredAtom2669
    Fin15AnchoredAtom2675 Fin15AnchoredAtom2678 Fin15AnchoredAtom2679 Fin15AnchoredAtom2685
    Fin15AnchoredAtom2691 Fin15AnchoredAtom2717 Fin15AnchoredAtom2720 Fin15AnchoredAtom2721
    Fin15AnchoredAtom2724 Fin15AnchoredAtom2725 Fin15AnchoredAtom2731 Fin15AnchoredAtom2734
    Fin15AnchoredAtom2735 Fin15AnchoredAtom2741 Fin15AnchoredAtom2747 Fin15AnchoredAtom2789
    Fin15AnchoredAtom2790 Fin15AnchoredAtom2796 Fin15AnchoredAtom2802 Fin15AnchoredAtom2812
    Fin15AnchoredAtom4593 Fin15AnchoredAtom4596 Fin15AnchoredAtom4597 Fin15AnchoredAtom4600
    Fin15AnchoredAtom4601 Fin15AnchoredAtom4607 Fin15AnchoredAtom4610 Fin15AnchoredAtom4611
    Fin15AnchoredAtom4617 Fin15AnchoredAtom4623 Fin15AnchoredAtom4665 Fin15AnchoredAtom4666
    Fin15AnchoredAtom4672 Fin15AnchoredAtom4678 Fin15AnchoredAtom4688 Fin15AnchoredAtom4735
    Fin15AnchoredAtom4736 Fin15AnchoredAtom4742 Fin15AnchoredAtom4748 Fin15AnchoredAtom4758
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

theorem fin15Anchored_clause31615 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2620 chi ∧
      ¬Fin15AnchoredAtom2622 chi ∧
      ¬Fin15AnchoredAtom2623 chi ∧
      ¬Fin15AnchoredAtom2624 chi ∧
      ¬Fin15AnchoredAtom2631 chi ∧
      ¬Fin15AnchoredAtom2632 chi ∧
      ¬Fin15AnchoredAtom2633 chi ∧
      ¬Fin15AnchoredAtom2637 chi ∧
      ¬Fin15AnchoredAtom2638 chi ∧
      ¬Fin15AnchoredAtom2639 chi ∧
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
      ¬Fin15AnchoredAtom2723 chi ∧
      ¬Fin15AnchoredAtom2724 chi ∧
      ¬Fin15AnchoredAtom2725 chi ∧
      ¬Fin15AnchoredAtom2729 chi ∧
      ¬Fin15AnchoredAtom2730 chi ∧
      ¬Fin15AnchoredAtom2731 chi ∧
      ¬Fin15AnchoredAtom2745 chi ∧
      ¬Fin15AnchoredAtom2746 chi ∧
      ¬Fin15AnchoredAtom2747 chi ∧
      ¬Fin15AnchoredAtom2751 chi ∧
      ¬Fin15AnchoredAtom2800 chi ∧
      ¬Fin15AnchoredAtom2801 chi ∧
      ¬Fin15AnchoredAtom2802 chi ∧
      ¬Fin15AnchoredAtom2806 chi ∧
      ¬Fin15AnchoredAtom2820 chi ∧
      ¬Fin15AnchoredAtom4599 chi ∧
      ¬Fin15AnchoredAtom4600 chi ∧
      ¬Fin15AnchoredAtom4601 chi ∧
      ¬Fin15AnchoredAtom4605 chi ∧
      ¬Fin15AnchoredAtom4606 chi ∧
      ¬Fin15AnchoredAtom4607 chi ∧
      ¬Fin15AnchoredAtom4621 chi ∧
      ¬Fin15AnchoredAtom4622 chi ∧
      ¬Fin15AnchoredAtom4623 chi ∧
      ¬Fin15AnchoredAtom4627 chi ∧
      ¬Fin15AnchoredAtom4676 chi ∧
      ¬Fin15AnchoredAtom4677 chi ∧
      ¬Fin15AnchoredAtom4678 chi ∧
      ¬Fin15AnchoredAtom4682 chi ∧
      ¬Fin15AnchoredAtom4696 chi ∧
      ¬Fin15AnchoredAtom4746 chi ∧
      ¬Fin15AnchoredAtom4747 chi ∧
      ¬Fin15AnchoredAtom4748 chi ∧
      ¬Fin15AnchoredAtom4752 chi ∧
      ¬Fin15AnchoredAtom4766 chi ∧
      ¬Fin15AnchoredAtom4816 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 5, 6, 8, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask30049
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2620 Fin15AnchoredAtom2622 Fin15AnchoredAtom2623
    Fin15AnchoredAtom2624 Fin15AnchoredAtom2631 Fin15AnchoredAtom2632 Fin15AnchoredAtom2633
    Fin15AnchoredAtom2637 Fin15AnchoredAtom2638 Fin15AnchoredAtom2639 Fin15AnchoredAtom2667
    Fin15AnchoredAtom2668 Fin15AnchoredAtom2669 Fin15AnchoredAtom2673 Fin15AnchoredAtom2674
    Fin15AnchoredAtom2675 Fin15AnchoredAtom2689 Fin15AnchoredAtom2690 Fin15AnchoredAtom2691
    Fin15AnchoredAtom2695 Fin15AnchoredAtom2723 Fin15AnchoredAtom2724 Fin15AnchoredAtom2725
    Fin15AnchoredAtom2729 Fin15AnchoredAtom2730 Fin15AnchoredAtom2731 Fin15AnchoredAtom2745
    Fin15AnchoredAtom2746 Fin15AnchoredAtom2747 Fin15AnchoredAtom2751 Fin15AnchoredAtom2800
    Fin15AnchoredAtom2801 Fin15AnchoredAtom2802 Fin15AnchoredAtom2806 Fin15AnchoredAtom2820
    Fin15AnchoredAtom4599 Fin15AnchoredAtom4600 Fin15AnchoredAtom4601 Fin15AnchoredAtom4605
    Fin15AnchoredAtom4606 Fin15AnchoredAtom4607 Fin15AnchoredAtom4621 Fin15AnchoredAtom4622
    Fin15AnchoredAtom4623 Fin15AnchoredAtom4627 Fin15AnchoredAtom4676 Fin15AnchoredAtom4677
    Fin15AnchoredAtom4678 Fin15AnchoredAtom4682 Fin15AnchoredAtom4696 Fin15AnchoredAtom4746
    Fin15AnchoredAtom4747 Fin15AnchoredAtom4748 Fin15AnchoredAtom4752 Fin15AnchoredAtom4766
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

end ErdosSzekeres

end
