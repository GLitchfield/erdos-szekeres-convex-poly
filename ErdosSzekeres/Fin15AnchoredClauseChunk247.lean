module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 247. -/

theorem fin15Anchored_clause31616 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2625 chi ∧
      ¬Fin15AnchoredAtom2627 chi ∧
      ¬Fin15AnchoredAtom2628 chi ∧
      ¬Fin15AnchoredAtom2629 chi ∧
      ¬Fin15AnchoredAtom2631 chi ∧
      ¬Fin15AnchoredAtom2632 chi ∧
      ¬Fin15AnchoredAtom2633 chi ∧
      ¬Fin15AnchoredAtom2637 chi ∧
      ¬Fin15AnchoredAtom2638 chi ∧
      ¬Fin15AnchoredAtom2639 chi ∧
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
      ¬Fin15AnchoredAtom4609 chi ∧
      ¬Fin15AnchoredAtom4610 chi ∧
      ¬Fin15AnchoredAtom4611 chi ∧
      ¬Fin15AnchoredAtom4615 chi ∧
      ¬Fin15AnchoredAtom4616 chi ∧
      ¬Fin15AnchoredAtom4617 chi ∧
      ¬Fin15AnchoredAtom4621 chi ∧
      ¬Fin15AnchoredAtom4622 chi ∧
      ¬Fin15AnchoredAtom4623 chi ∧
      ¬Fin15AnchoredAtom4627 chi ∧
      ¬Fin15AnchoredAtom4686 chi ∧
      ¬Fin15AnchoredAtom4687 chi ∧
      ¬Fin15AnchoredAtom4688 chi ∧
      ¬Fin15AnchoredAtom4692 chi ∧
      ¬Fin15AnchoredAtom4696 chi ∧
      ¬Fin15AnchoredAtom4756 chi ∧
      ¬Fin15AnchoredAtom4757 chi ∧
      ¬Fin15AnchoredAtom4758 chi ∧
      ¬Fin15AnchoredAtom4762 chi ∧
      ¬Fin15AnchoredAtom4766 chi ∧
      ¬Fin15AnchoredAtom4821 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 5, 6, 9, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask30305
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2625 Fin15AnchoredAtom2627 Fin15AnchoredAtom2628
    Fin15AnchoredAtom2629 Fin15AnchoredAtom2631 Fin15AnchoredAtom2632 Fin15AnchoredAtom2633
    Fin15AnchoredAtom2637 Fin15AnchoredAtom2638 Fin15AnchoredAtom2639 Fin15AnchoredAtom2677
    Fin15AnchoredAtom2678 Fin15AnchoredAtom2679 Fin15AnchoredAtom2683 Fin15AnchoredAtom2684
    Fin15AnchoredAtom2685 Fin15AnchoredAtom2689 Fin15AnchoredAtom2690 Fin15AnchoredAtom2691
    Fin15AnchoredAtom2695 Fin15AnchoredAtom2733 Fin15AnchoredAtom2734 Fin15AnchoredAtom2735
    Fin15AnchoredAtom2739 Fin15AnchoredAtom2740 Fin15AnchoredAtom2741 Fin15AnchoredAtom2745
    Fin15AnchoredAtom2746 Fin15AnchoredAtom2747 Fin15AnchoredAtom2751 Fin15AnchoredAtom2810
    Fin15AnchoredAtom2811 Fin15AnchoredAtom2812 Fin15AnchoredAtom2816 Fin15AnchoredAtom2820
    Fin15AnchoredAtom4609 Fin15AnchoredAtom4610 Fin15AnchoredAtom4611 Fin15AnchoredAtom4615
    Fin15AnchoredAtom4616 Fin15AnchoredAtom4617 Fin15AnchoredAtom4621 Fin15AnchoredAtom4622
    Fin15AnchoredAtom4623 Fin15AnchoredAtom4627 Fin15AnchoredAtom4686 Fin15AnchoredAtom4687
    Fin15AnchoredAtom4688 Fin15AnchoredAtom4692 Fin15AnchoredAtom4696 Fin15AnchoredAtom4756
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

theorem fin15Anchored_clause31617 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2640 chi ∧
      ¬Fin15AnchoredAtom2641 chi ∧
      ¬Fin15AnchoredAtom2643 chi ∧
      ¬Fin15AnchoredAtom2644 chi ∧
      ¬Fin15AnchoredAtom2646 chi ∧
      ¬Fin15AnchoredAtom2648 chi ∧
      ¬Fin15AnchoredAtom2649 chi ∧
      ¬Fin15AnchoredAtom2652 chi ∧
      ¬Fin15AnchoredAtom2653 chi ∧
      ¬Fin15AnchoredAtom2658 chi ∧
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
      ¬Fin15AnchoredAtom4628 chi ∧
      ¬Fin15AnchoredAtom4630 chi ∧
      ¬Fin15AnchoredAtom4631 chi ∧
      ¬Fin15AnchoredAtom4634 chi ∧
      ¬Fin15AnchoredAtom4635 chi ∧
      ¬Fin15AnchoredAtom4640 chi ∧
      ¬Fin15AnchoredAtom4644 chi ∧
      ¬Fin15AnchoredAtom4645 chi ∧
      ¬Fin15AnchoredAtom4650 chi ∧
      ¬Fin15AnchoredAtom4656 chi ∧
      ¬Fin15AnchoredAtom4664 chi ∧
      ¬Fin15AnchoredAtom4665 chi ∧
      ¬Fin15AnchoredAtom4670 chi ∧
      ¬Fin15AnchoredAtom4676 chi ∧
      ¬Fin15AnchoredAtom4686 chi ∧
      ¬Fin15AnchoredAtom4769 chi ∧
      ¬Fin15AnchoredAtom4770 chi ∧
      ¬Fin15AnchoredAtom4775 chi ∧
      ¬Fin15AnchoredAtom4781 chi ∧
      ¬Fin15AnchoredAtom4791 chi ∧
      ¬Fin15AnchoredAtom4806 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 5, 7, 8, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask14241
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2640 Fin15AnchoredAtom2641 Fin15AnchoredAtom2643
    Fin15AnchoredAtom2644 Fin15AnchoredAtom2646 Fin15AnchoredAtom2648 Fin15AnchoredAtom2649
    Fin15AnchoredAtom2652 Fin15AnchoredAtom2653 Fin15AnchoredAtom2658 Fin15AnchoredAtom2661
    Fin15AnchoredAtom2663 Fin15AnchoredAtom2664 Fin15AnchoredAtom2667 Fin15AnchoredAtom2668
    Fin15AnchoredAtom2673 Fin15AnchoredAtom2677 Fin15AnchoredAtom2678 Fin15AnchoredAtom2683
    Fin15AnchoredAtom2689 Fin15AnchoredAtom2752 Fin15AnchoredAtom2754 Fin15AnchoredAtom2755
    Fin15AnchoredAtom2758 Fin15AnchoredAtom2759 Fin15AnchoredAtom2764 Fin15AnchoredAtom2768
    Fin15AnchoredAtom2769 Fin15AnchoredAtom2774 Fin15AnchoredAtom2780 Fin15AnchoredAtom2788
    Fin15AnchoredAtom2789 Fin15AnchoredAtom2794 Fin15AnchoredAtom2800 Fin15AnchoredAtom2810
    Fin15AnchoredAtom4628 Fin15AnchoredAtom4630 Fin15AnchoredAtom4631 Fin15AnchoredAtom4634
    Fin15AnchoredAtom4635 Fin15AnchoredAtom4640 Fin15AnchoredAtom4644 Fin15AnchoredAtom4645
    Fin15AnchoredAtom4650 Fin15AnchoredAtom4656 Fin15AnchoredAtom4664 Fin15AnchoredAtom4665
    Fin15AnchoredAtom4670 Fin15AnchoredAtom4676 Fin15AnchoredAtom4686 Fin15AnchoredAtom4769
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

theorem fin15Anchored_clause31618 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2640 chi ∧
      ¬Fin15AnchoredAtom2641 chi ∧
      ¬Fin15AnchoredAtom2643 chi ∧
      ¬Fin15AnchoredAtom2645 chi ∧
      ¬Fin15AnchoredAtom2646 chi ∧
      ¬Fin15AnchoredAtom2648 chi ∧
      ¬Fin15AnchoredAtom2650 chi ∧
      ¬Fin15AnchoredAtom2652 chi ∧
      ¬Fin15AnchoredAtom2654 chi ∧
      ¬Fin15AnchoredAtom2659 chi ∧
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
      ¬Fin15AnchoredAtom4628 chi ∧
      ¬Fin15AnchoredAtom4630 chi ∧
      ¬Fin15AnchoredAtom4632 chi ∧
      ¬Fin15AnchoredAtom4634 chi ∧
      ¬Fin15AnchoredAtom4636 chi ∧
      ¬Fin15AnchoredAtom4641 chi ∧
      ¬Fin15AnchoredAtom4644 chi ∧
      ¬Fin15AnchoredAtom4646 chi ∧
      ¬Fin15AnchoredAtom4651 chi ∧
      ¬Fin15AnchoredAtom4657 chi ∧
      ¬Fin15AnchoredAtom4664 chi ∧
      ¬Fin15AnchoredAtom4666 chi ∧
      ¬Fin15AnchoredAtom4671 chi ∧
      ¬Fin15AnchoredAtom4677 chi ∧
      ¬Fin15AnchoredAtom4687 chi ∧
      ¬Fin15AnchoredAtom4769 chi ∧
      ¬Fin15AnchoredAtom4771 chi ∧
      ¬Fin15AnchoredAtom4776 chi ∧
      ¬Fin15AnchoredAtom4782 chi ∧
      ¬Fin15AnchoredAtom4792 chi ∧
      ¬Fin15AnchoredAtom4807 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 5, 7, 8, 9, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22433
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2640 Fin15AnchoredAtom2641 Fin15AnchoredAtom2643
    Fin15AnchoredAtom2645 Fin15AnchoredAtom2646 Fin15AnchoredAtom2648 Fin15AnchoredAtom2650
    Fin15AnchoredAtom2652 Fin15AnchoredAtom2654 Fin15AnchoredAtom2659 Fin15AnchoredAtom2661
    Fin15AnchoredAtom2663 Fin15AnchoredAtom2665 Fin15AnchoredAtom2667 Fin15AnchoredAtom2669
    Fin15AnchoredAtom2674 Fin15AnchoredAtom2677 Fin15AnchoredAtom2679 Fin15AnchoredAtom2684
    Fin15AnchoredAtom2690 Fin15AnchoredAtom2752 Fin15AnchoredAtom2754 Fin15AnchoredAtom2756
    Fin15AnchoredAtom2758 Fin15AnchoredAtom2760 Fin15AnchoredAtom2765 Fin15AnchoredAtom2768
    Fin15AnchoredAtom2770 Fin15AnchoredAtom2775 Fin15AnchoredAtom2781 Fin15AnchoredAtom2788
    Fin15AnchoredAtom2790 Fin15AnchoredAtom2795 Fin15AnchoredAtom2801 Fin15AnchoredAtom2811
    Fin15AnchoredAtom4628 Fin15AnchoredAtom4630 Fin15AnchoredAtom4632 Fin15AnchoredAtom4634
    Fin15AnchoredAtom4636 Fin15AnchoredAtom4641 Fin15AnchoredAtom4644 Fin15AnchoredAtom4646
    Fin15AnchoredAtom4651 Fin15AnchoredAtom4657 Fin15AnchoredAtom4664 Fin15AnchoredAtom4666
    Fin15AnchoredAtom4671 Fin15AnchoredAtom4677 Fin15AnchoredAtom4687 Fin15AnchoredAtom4769
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

theorem fin15Anchored_clause31619 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2640 chi ∧
      ¬Fin15AnchoredAtom2641 chi ∧
      ¬Fin15AnchoredAtom2644 chi ∧
      ¬Fin15AnchoredAtom2645 chi ∧
      ¬Fin15AnchoredAtom2646 chi ∧
      ¬Fin15AnchoredAtom2649 chi ∧
      ¬Fin15AnchoredAtom2650 chi ∧
      ¬Fin15AnchoredAtom2653 chi ∧
      ¬Fin15AnchoredAtom2654 chi ∧
      ¬Fin15AnchoredAtom2660 chi ∧
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
      ¬Fin15AnchoredAtom4628 chi ∧
      ¬Fin15AnchoredAtom4631 chi ∧
      ¬Fin15AnchoredAtom4632 chi ∧
      ¬Fin15AnchoredAtom4635 chi ∧
      ¬Fin15AnchoredAtom4636 chi ∧
      ¬Fin15AnchoredAtom4642 chi ∧
      ¬Fin15AnchoredAtom4645 chi ∧
      ¬Fin15AnchoredAtom4646 chi ∧
      ¬Fin15AnchoredAtom4652 chi ∧
      ¬Fin15AnchoredAtom4658 chi ∧
      ¬Fin15AnchoredAtom4665 chi ∧
      ¬Fin15AnchoredAtom4666 chi ∧
      ¬Fin15AnchoredAtom4672 chi ∧
      ¬Fin15AnchoredAtom4678 chi ∧
      ¬Fin15AnchoredAtom4688 chi ∧
      ¬Fin15AnchoredAtom4770 chi ∧
      ¬Fin15AnchoredAtom4771 chi ∧
      ¬Fin15AnchoredAtom4777 chi ∧
      ¬Fin15AnchoredAtom4783 chi ∧
      ¬Fin15AnchoredAtom4793 chi ∧
      ¬Fin15AnchoredAtom4808 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 5, 7, 8, 9, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26529
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2640 Fin15AnchoredAtom2641 Fin15AnchoredAtom2644
    Fin15AnchoredAtom2645 Fin15AnchoredAtom2646 Fin15AnchoredAtom2649 Fin15AnchoredAtom2650
    Fin15AnchoredAtom2653 Fin15AnchoredAtom2654 Fin15AnchoredAtom2660 Fin15AnchoredAtom2661
    Fin15AnchoredAtom2664 Fin15AnchoredAtom2665 Fin15AnchoredAtom2668 Fin15AnchoredAtom2669
    Fin15AnchoredAtom2675 Fin15AnchoredAtom2678 Fin15AnchoredAtom2679 Fin15AnchoredAtom2685
    Fin15AnchoredAtom2691 Fin15AnchoredAtom2752 Fin15AnchoredAtom2755 Fin15AnchoredAtom2756
    Fin15AnchoredAtom2759 Fin15AnchoredAtom2760 Fin15AnchoredAtom2766 Fin15AnchoredAtom2769
    Fin15AnchoredAtom2770 Fin15AnchoredAtom2776 Fin15AnchoredAtom2782 Fin15AnchoredAtom2789
    Fin15AnchoredAtom2790 Fin15AnchoredAtom2796 Fin15AnchoredAtom2802 Fin15AnchoredAtom2812
    Fin15AnchoredAtom4628 Fin15AnchoredAtom4631 Fin15AnchoredAtom4632 Fin15AnchoredAtom4635
    Fin15AnchoredAtom4636 Fin15AnchoredAtom4642 Fin15AnchoredAtom4645 Fin15AnchoredAtom4646
    Fin15AnchoredAtom4652 Fin15AnchoredAtom4658 Fin15AnchoredAtom4665 Fin15AnchoredAtom4666
    Fin15AnchoredAtom4672 Fin15AnchoredAtom4678 Fin15AnchoredAtom4688 Fin15AnchoredAtom4770
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

theorem fin15Anchored_clause31620 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2640 chi ∧
      ¬Fin15AnchoredAtom2643 chi ∧
      ¬Fin15AnchoredAtom2644 chi ∧
      ¬Fin15AnchoredAtom2645 chi ∧
      ¬Fin15AnchoredAtom2648 chi ∧
      ¬Fin15AnchoredAtom2649 chi ∧
      ¬Fin15AnchoredAtom2650 chi ∧
      ¬Fin15AnchoredAtom2658 chi ∧
      ¬Fin15AnchoredAtom2659 chi ∧
      ¬Fin15AnchoredAtom2660 chi ∧
      ¬Fin15AnchoredAtom2663 chi ∧
      ¬Fin15AnchoredAtom2664 chi ∧
      ¬Fin15AnchoredAtom2665 chi ∧
      ¬Fin15AnchoredAtom2673 chi ∧
      ¬Fin15AnchoredAtom2674 chi ∧
      ¬Fin15AnchoredAtom2675 chi ∧
      ¬Fin15AnchoredAtom2683 chi ∧
      ¬Fin15AnchoredAtom2684 chi ∧
      ¬Fin15AnchoredAtom2685 chi ∧
      ¬Fin15AnchoredAtom2695 chi ∧
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
      ¬Fin15AnchoredAtom4630 chi ∧
      ¬Fin15AnchoredAtom4631 chi ∧
      ¬Fin15AnchoredAtom4632 chi ∧
      ¬Fin15AnchoredAtom4640 chi ∧
      ¬Fin15AnchoredAtom4641 chi ∧
      ¬Fin15AnchoredAtom4642 chi ∧
      ¬Fin15AnchoredAtom4650 chi ∧
      ¬Fin15AnchoredAtom4651 chi ∧
      ¬Fin15AnchoredAtom4652 chi ∧
      ¬Fin15AnchoredAtom4662 chi ∧
      ¬Fin15AnchoredAtom4670 chi ∧
      ¬Fin15AnchoredAtom4671 chi ∧
      ¬Fin15AnchoredAtom4672 chi ∧
      ¬Fin15AnchoredAtom4682 chi ∧
      ¬Fin15AnchoredAtom4692 chi ∧
      ¬Fin15AnchoredAtom4775 chi ∧
      ¬Fin15AnchoredAtom4776 chi ∧
      ¬Fin15AnchoredAtom4777 chi ∧
      ¬Fin15AnchoredAtom4787 chi ∧
      ¬Fin15AnchoredAtom4797 chi ∧
      ¬Fin15AnchoredAtom4812 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 5, 7, 8, 9, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29601
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2640 Fin15AnchoredAtom2643 Fin15AnchoredAtom2644
    Fin15AnchoredAtom2645 Fin15AnchoredAtom2648 Fin15AnchoredAtom2649 Fin15AnchoredAtom2650
    Fin15AnchoredAtom2658 Fin15AnchoredAtom2659 Fin15AnchoredAtom2660 Fin15AnchoredAtom2663
    Fin15AnchoredAtom2664 Fin15AnchoredAtom2665 Fin15AnchoredAtom2673 Fin15AnchoredAtom2674
    Fin15AnchoredAtom2675 Fin15AnchoredAtom2683 Fin15AnchoredAtom2684 Fin15AnchoredAtom2685
    Fin15AnchoredAtom2695 Fin15AnchoredAtom2754 Fin15AnchoredAtom2755 Fin15AnchoredAtom2756
    Fin15AnchoredAtom2764 Fin15AnchoredAtom2765 Fin15AnchoredAtom2766 Fin15AnchoredAtom2774
    Fin15AnchoredAtom2775 Fin15AnchoredAtom2776 Fin15AnchoredAtom2786 Fin15AnchoredAtom2794
    Fin15AnchoredAtom2795 Fin15AnchoredAtom2796 Fin15AnchoredAtom2806 Fin15AnchoredAtom2816
    Fin15AnchoredAtom4630 Fin15AnchoredAtom4631 Fin15AnchoredAtom4632 Fin15AnchoredAtom4640
    Fin15AnchoredAtom4641 Fin15AnchoredAtom4642 Fin15AnchoredAtom4650 Fin15AnchoredAtom4651
    Fin15AnchoredAtom4652 Fin15AnchoredAtom4662 Fin15AnchoredAtom4670 Fin15AnchoredAtom4671
    Fin15AnchoredAtom4672 Fin15AnchoredAtom4682 Fin15AnchoredAtom4692 Fin15AnchoredAtom4775
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

theorem fin15Anchored_clause31621 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2641 chi ∧
      ¬Fin15AnchoredAtom2643 chi ∧
      ¬Fin15AnchoredAtom2644 chi ∧
      ¬Fin15AnchoredAtom2645 chi ∧
      ¬Fin15AnchoredAtom2652 chi ∧
      ¬Fin15AnchoredAtom2653 chi ∧
      ¬Fin15AnchoredAtom2654 chi ∧
      ¬Fin15AnchoredAtom2658 chi ∧
      ¬Fin15AnchoredAtom2659 chi ∧
      ¬Fin15AnchoredAtom2660 chi ∧
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
      ¬Fin15AnchoredAtom4634 chi ∧
      ¬Fin15AnchoredAtom4635 chi ∧
      ¬Fin15AnchoredAtom4636 chi ∧
      ¬Fin15AnchoredAtom4640 chi ∧
      ¬Fin15AnchoredAtom4641 chi ∧
      ¬Fin15AnchoredAtom4642 chi ∧
      ¬Fin15AnchoredAtom4656 chi ∧
      ¬Fin15AnchoredAtom4657 chi ∧
      ¬Fin15AnchoredAtom4658 chi ∧
      ¬Fin15AnchoredAtom4662 chi ∧
      ¬Fin15AnchoredAtom4676 chi ∧
      ¬Fin15AnchoredAtom4677 chi ∧
      ¬Fin15AnchoredAtom4678 chi ∧
      ¬Fin15AnchoredAtom4682 chi ∧
      ¬Fin15AnchoredAtom4696 chi ∧
      ¬Fin15AnchoredAtom4781 chi ∧
      ¬Fin15AnchoredAtom4782 chi ∧
      ¬Fin15AnchoredAtom4783 chi ∧
      ¬Fin15AnchoredAtom4787 chi ∧
      ¬Fin15AnchoredAtom4801 chi ∧
      ¬Fin15AnchoredAtom4816 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 5, 7, 8, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask30113
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2641 Fin15AnchoredAtom2643 Fin15AnchoredAtom2644
    Fin15AnchoredAtom2645 Fin15AnchoredAtom2652 Fin15AnchoredAtom2653 Fin15AnchoredAtom2654
    Fin15AnchoredAtom2658 Fin15AnchoredAtom2659 Fin15AnchoredAtom2660 Fin15AnchoredAtom2667
    Fin15AnchoredAtom2668 Fin15AnchoredAtom2669 Fin15AnchoredAtom2673 Fin15AnchoredAtom2674
    Fin15AnchoredAtom2675 Fin15AnchoredAtom2689 Fin15AnchoredAtom2690 Fin15AnchoredAtom2691
    Fin15AnchoredAtom2695 Fin15AnchoredAtom2758 Fin15AnchoredAtom2759 Fin15AnchoredAtom2760
    Fin15AnchoredAtom2764 Fin15AnchoredAtom2765 Fin15AnchoredAtom2766 Fin15AnchoredAtom2780
    Fin15AnchoredAtom2781 Fin15AnchoredAtom2782 Fin15AnchoredAtom2786 Fin15AnchoredAtom2800
    Fin15AnchoredAtom2801 Fin15AnchoredAtom2802 Fin15AnchoredAtom2806 Fin15AnchoredAtom2820
    Fin15AnchoredAtom4634 Fin15AnchoredAtom4635 Fin15AnchoredAtom4636 Fin15AnchoredAtom4640
    Fin15AnchoredAtom4641 Fin15AnchoredAtom4642 Fin15AnchoredAtom4656 Fin15AnchoredAtom4657
    Fin15AnchoredAtom4658 Fin15AnchoredAtom4662 Fin15AnchoredAtom4676 Fin15AnchoredAtom4677
    Fin15AnchoredAtom4678 Fin15AnchoredAtom4682 Fin15AnchoredAtom4696 Fin15AnchoredAtom4781
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

theorem fin15Anchored_clause31622 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2646 chi ∧
      ¬Fin15AnchoredAtom2648 chi ∧
      ¬Fin15AnchoredAtom2649 chi ∧
      ¬Fin15AnchoredAtom2650 chi ∧
      ¬Fin15AnchoredAtom2652 chi ∧
      ¬Fin15AnchoredAtom2653 chi ∧
      ¬Fin15AnchoredAtom2654 chi ∧
      ¬Fin15AnchoredAtom2658 chi ∧
      ¬Fin15AnchoredAtom2659 chi ∧
      ¬Fin15AnchoredAtom2660 chi ∧
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
      ¬Fin15AnchoredAtom4644 chi ∧
      ¬Fin15AnchoredAtom4645 chi ∧
      ¬Fin15AnchoredAtom4646 chi ∧
      ¬Fin15AnchoredAtom4650 chi ∧
      ¬Fin15AnchoredAtom4651 chi ∧
      ¬Fin15AnchoredAtom4652 chi ∧
      ¬Fin15AnchoredAtom4656 chi ∧
      ¬Fin15AnchoredAtom4657 chi ∧
      ¬Fin15AnchoredAtom4658 chi ∧
      ¬Fin15AnchoredAtom4662 chi ∧
      ¬Fin15AnchoredAtom4686 chi ∧
      ¬Fin15AnchoredAtom4687 chi ∧
      ¬Fin15AnchoredAtom4688 chi ∧
      ¬Fin15AnchoredAtom4692 chi ∧
      ¬Fin15AnchoredAtom4696 chi ∧
      ¬Fin15AnchoredAtom4791 chi ∧
      ¬Fin15AnchoredAtom4792 chi ∧
      ¬Fin15AnchoredAtom4793 chi ∧
      ¬Fin15AnchoredAtom4797 chi ∧
      ¬Fin15AnchoredAtom4801 chi ∧
      ¬Fin15AnchoredAtom4821 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 5, 7, 9, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask30369
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2646 Fin15AnchoredAtom2648 Fin15AnchoredAtom2649
    Fin15AnchoredAtom2650 Fin15AnchoredAtom2652 Fin15AnchoredAtom2653 Fin15AnchoredAtom2654
    Fin15AnchoredAtom2658 Fin15AnchoredAtom2659 Fin15AnchoredAtom2660 Fin15AnchoredAtom2677
    Fin15AnchoredAtom2678 Fin15AnchoredAtom2679 Fin15AnchoredAtom2683 Fin15AnchoredAtom2684
    Fin15AnchoredAtom2685 Fin15AnchoredAtom2689 Fin15AnchoredAtom2690 Fin15AnchoredAtom2691
    Fin15AnchoredAtom2695 Fin15AnchoredAtom2768 Fin15AnchoredAtom2769 Fin15AnchoredAtom2770
    Fin15AnchoredAtom2774 Fin15AnchoredAtom2775 Fin15AnchoredAtom2776 Fin15AnchoredAtom2780
    Fin15AnchoredAtom2781 Fin15AnchoredAtom2782 Fin15AnchoredAtom2786 Fin15AnchoredAtom2810
    Fin15AnchoredAtom2811 Fin15AnchoredAtom2812 Fin15AnchoredAtom2816 Fin15AnchoredAtom2820
    Fin15AnchoredAtom4644 Fin15AnchoredAtom4645 Fin15AnchoredAtom4646 Fin15AnchoredAtom4650
    Fin15AnchoredAtom4651 Fin15AnchoredAtom4652 Fin15AnchoredAtom4656 Fin15AnchoredAtom4657
    Fin15AnchoredAtom4658 Fin15AnchoredAtom4662 Fin15AnchoredAtom4686 Fin15AnchoredAtom4687
    Fin15AnchoredAtom4688 Fin15AnchoredAtom4692 Fin15AnchoredAtom4696 Fin15AnchoredAtom4791
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

theorem fin15Anchored_clause31623 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2661 chi ∧
      ¬Fin15AnchoredAtom2663 chi ∧
      ¬Fin15AnchoredAtom2664 chi ∧
      ¬Fin15AnchoredAtom2665 chi ∧
      ¬Fin15AnchoredAtom2667 chi ∧
      ¬Fin15AnchoredAtom2668 chi ∧
      ¬Fin15AnchoredAtom2669 chi ∧
      ¬Fin15AnchoredAtom2673 chi ∧
      ¬Fin15AnchoredAtom2674 chi ∧
      ¬Fin15AnchoredAtom2675 chi ∧
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
      ¬Fin15AnchoredAtom4664 chi ∧
      ¬Fin15AnchoredAtom4665 chi ∧
      ¬Fin15AnchoredAtom4666 chi ∧
      ¬Fin15AnchoredAtom4670 chi ∧
      ¬Fin15AnchoredAtom4671 chi ∧
      ¬Fin15AnchoredAtom4672 chi ∧
      ¬Fin15AnchoredAtom4676 chi ∧
      ¬Fin15AnchoredAtom4677 chi ∧
      ¬Fin15AnchoredAtom4678 chi ∧
      ¬Fin15AnchoredAtom4682 chi ∧
      ¬Fin15AnchoredAtom4686 chi ∧
      ¬Fin15AnchoredAtom4687 chi ∧
      ¬Fin15AnchoredAtom4688 chi ∧
      ¬Fin15AnchoredAtom4692 chi ∧
      ¬Fin15AnchoredAtom4696 chi ∧
      ¬Fin15AnchoredAtom4806 chi ∧
      ¬Fin15AnchoredAtom4807 chi ∧
      ¬Fin15AnchoredAtom4808 chi ∧
      ¬Fin15AnchoredAtom4812 chi ∧
      ¬Fin15AnchoredAtom4816 chi ∧
      ¬Fin15AnchoredAtom4821 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 5, 8, 9, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask30497
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2661 Fin15AnchoredAtom2663 Fin15AnchoredAtom2664
    Fin15AnchoredAtom2665 Fin15AnchoredAtom2667 Fin15AnchoredAtom2668 Fin15AnchoredAtom2669
    Fin15AnchoredAtom2673 Fin15AnchoredAtom2674 Fin15AnchoredAtom2675 Fin15AnchoredAtom2677
    Fin15AnchoredAtom2678 Fin15AnchoredAtom2679 Fin15AnchoredAtom2683 Fin15AnchoredAtom2684
    Fin15AnchoredAtom2685 Fin15AnchoredAtom2689 Fin15AnchoredAtom2690 Fin15AnchoredAtom2691
    Fin15AnchoredAtom2695 Fin15AnchoredAtom2788 Fin15AnchoredAtom2789 Fin15AnchoredAtom2790
    Fin15AnchoredAtom2794 Fin15AnchoredAtom2795 Fin15AnchoredAtom2796 Fin15AnchoredAtom2800
    Fin15AnchoredAtom2801 Fin15AnchoredAtom2802 Fin15AnchoredAtom2806 Fin15AnchoredAtom2810
    Fin15AnchoredAtom2811 Fin15AnchoredAtom2812 Fin15AnchoredAtom2816 Fin15AnchoredAtom2820
    Fin15AnchoredAtom4664 Fin15AnchoredAtom4665 Fin15AnchoredAtom4666 Fin15AnchoredAtom4670
    Fin15AnchoredAtom4671 Fin15AnchoredAtom4672 Fin15AnchoredAtom4676 Fin15AnchoredAtom4677
    Fin15AnchoredAtom4678 Fin15AnchoredAtom4682 Fin15AnchoredAtom4686 Fin15AnchoredAtom4687
    Fin15AnchoredAtom4688 Fin15AnchoredAtom4692 Fin15AnchoredAtom4696 Fin15AnchoredAtom4806
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

theorem fin15Anchored_clause31624 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2676 chi ∧
      ¬Fin15AnchoredAtom2677 chi ∧
      ¬Fin15AnchoredAtom2678 chi ∧
      ¬Fin15AnchoredAtom2679 chi ∧
      ¬Fin15AnchoredAtom2680 chi ∧
      ¬Fin15AnchoredAtom2681 chi ∧
      ¬Fin15AnchoredAtom2682 chi ∧
      ¬Fin15AnchoredAtom2683 chi ∧
      ¬Fin15AnchoredAtom2684 chi ∧
      ¬Fin15AnchoredAtom2685 chi ∧
      ¬Fin15AnchoredAtom2686 chi ∧
      ¬Fin15AnchoredAtom2687 chi ∧
      ¬Fin15AnchoredAtom2688 chi ∧
      ¬Fin15AnchoredAtom2689 chi ∧
      ¬Fin15AnchoredAtom2690 chi ∧
      ¬Fin15AnchoredAtom2691 chi ∧
      ¬Fin15AnchoredAtom2692 chi ∧
      ¬Fin15AnchoredAtom2693 chi ∧
      ¬Fin15AnchoredAtom2694 chi ∧
      ¬Fin15AnchoredAtom2695 chi ∧
      ¬Fin15AnchoredAtom2807 chi ∧
      ¬Fin15AnchoredAtom2808 chi ∧
      ¬Fin15AnchoredAtom2809 chi ∧
      ¬Fin15AnchoredAtom2810 chi ∧
      ¬Fin15AnchoredAtom2811 chi ∧
      ¬Fin15AnchoredAtom2812 chi ∧
      ¬Fin15AnchoredAtom2813 chi ∧
      ¬Fin15AnchoredAtom2814 chi ∧
      ¬Fin15AnchoredAtom2815 chi ∧
      ¬Fin15AnchoredAtom2816 chi ∧
      ¬Fin15AnchoredAtom2817 chi ∧
      ¬Fin15AnchoredAtom2818 chi ∧
      ¬Fin15AnchoredAtom2819 chi ∧
      ¬Fin15AnchoredAtom2820 chi ∧
      ¬Fin15AnchoredAtom2821 chi ∧
      ¬Fin15AnchoredAtom4683 chi ∧
      ¬Fin15AnchoredAtom4684 chi ∧
      ¬Fin15AnchoredAtom4685 chi ∧
      ¬Fin15AnchoredAtom4686 chi ∧
      ¬Fin15AnchoredAtom4687 chi ∧
      ¬Fin15AnchoredAtom4688 chi ∧
      ¬Fin15AnchoredAtom4689 chi ∧
      ¬Fin15AnchoredAtom4690 chi ∧
      ¬Fin15AnchoredAtom4691 chi ∧
      ¬Fin15AnchoredAtom4692 chi ∧
      ¬Fin15AnchoredAtom4693 chi ∧
      ¬Fin15AnchoredAtom4694 chi ∧
      ¬Fin15AnchoredAtom4695 chi ∧
      ¬Fin15AnchoredAtom4696 chi ∧
      ¬Fin15AnchoredAtom4697 chi ∧
      ¬Fin15AnchoredAtom4818 chi ∧
      ¬Fin15AnchoredAtom4819 chi ∧
      ¬Fin15AnchoredAtom4820 chi ∧
      ¬Fin15AnchoredAtom4821 chi ∧
      ¬Fin15AnchoredAtom4822 chi ∧
      ¬Fin15AnchoredAtom4823 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 5, 9, 10, 11, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask32289
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2676 Fin15AnchoredAtom2677 Fin15AnchoredAtom2678
    Fin15AnchoredAtom2679 Fin15AnchoredAtom2680 Fin15AnchoredAtom2681 Fin15AnchoredAtom2682
    Fin15AnchoredAtom2683 Fin15AnchoredAtom2684 Fin15AnchoredAtom2685 Fin15AnchoredAtom2686
    Fin15AnchoredAtom2687 Fin15AnchoredAtom2688 Fin15AnchoredAtom2689 Fin15AnchoredAtom2690
    Fin15AnchoredAtom2691 Fin15AnchoredAtom2692 Fin15AnchoredAtom2693 Fin15AnchoredAtom2694
    Fin15AnchoredAtom2695 Fin15AnchoredAtom2807 Fin15AnchoredAtom2808 Fin15AnchoredAtom2809
    Fin15AnchoredAtom2810 Fin15AnchoredAtom2811 Fin15AnchoredAtom2812 Fin15AnchoredAtom2813
    Fin15AnchoredAtom2814 Fin15AnchoredAtom2815 Fin15AnchoredAtom2816 Fin15AnchoredAtom2817
    Fin15AnchoredAtom2818 Fin15AnchoredAtom2819 Fin15AnchoredAtom2820 Fin15AnchoredAtom2821
    Fin15AnchoredAtom4683 Fin15AnchoredAtom4684 Fin15AnchoredAtom4685 Fin15AnchoredAtom4686
    Fin15AnchoredAtom4687 Fin15AnchoredAtom4688 Fin15AnchoredAtom4689 Fin15AnchoredAtom4690
    Fin15AnchoredAtom4691 Fin15AnchoredAtom4692 Fin15AnchoredAtom4693 Fin15AnchoredAtom4694
    Fin15AnchoredAtom4695 Fin15AnchoredAtom4696 Fin15AnchoredAtom4697 Fin15AnchoredAtom4818
    Fin15AnchoredAtom4819 Fin15AnchoredAtom4820 Fin15AnchoredAtom4821 Fin15AnchoredAtom4822
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

theorem fin15Anchored_clause31625 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2696 chi ∧
      ¬Fin15AnchoredAtom2697 chi ∧
      ¬Fin15AnchoredAtom2699 chi ∧
      ¬Fin15AnchoredAtom2700 chi ∧
      ¬Fin15AnchoredAtom2702 chi ∧
      ¬Fin15AnchoredAtom2704 chi ∧
      ¬Fin15AnchoredAtom2705 chi ∧
      ¬Fin15AnchoredAtom2708 chi ∧
      ¬Fin15AnchoredAtom2709 chi ∧
      ¬Fin15AnchoredAtom2714 chi ∧
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
      ¬Fin15AnchoredAtom4698 chi ∧
      ¬Fin15AnchoredAtom4700 chi ∧
      ¬Fin15AnchoredAtom4701 chi ∧
      ¬Fin15AnchoredAtom4704 chi ∧
      ¬Fin15AnchoredAtom4705 chi ∧
      ¬Fin15AnchoredAtom4710 chi ∧
      ¬Fin15AnchoredAtom4714 chi ∧
      ¬Fin15AnchoredAtom4715 chi ∧
      ¬Fin15AnchoredAtom4720 chi ∧
      ¬Fin15AnchoredAtom4726 chi ∧
      ¬Fin15AnchoredAtom4734 chi ∧
      ¬Fin15AnchoredAtom4735 chi ∧
      ¬Fin15AnchoredAtom4740 chi ∧
      ¬Fin15AnchoredAtom4746 chi ∧
      ¬Fin15AnchoredAtom4756 chi ∧
      ¬Fin15AnchoredAtom4769 chi ∧
      ¬Fin15AnchoredAtom4770 chi ∧
      ¬Fin15AnchoredAtom4775 chi ∧
      ¬Fin15AnchoredAtom4781 chi ∧
      ¬Fin15AnchoredAtom4791 chi ∧
      ¬Fin15AnchoredAtom4806 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 6, 7, 8, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask14273
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2696 Fin15AnchoredAtom2697 Fin15AnchoredAtom2699
    Fin15AnchoredAtom2700 Fin15AnchoredAtom2702 Fin15AnchoredAtom2704 Fin15AnchoredAtom2705
    Fin15AnchoredAtom2708 Fin15AnchoredAtom2709 Fin15AnchoredAtom2714 Fin15AnchoredAtom2717
    Fin15AnchoredAtom2719 Fin15AnchoredAtom2720 Fin15AnchoredAtom2723 Fin15AnchoredAtom2724
    Fin15AnchoredAtom2729 Fin15AnchoredAtom2733 Fin15AnchoredAtom2734 Fin15AnchoredAtom2739
    Fin15AnchoredAtom2745 Fin15AnchoredAtom2752 Fin15AnchoredAtom2754 Fin15AnchoredAtom2755
    Fin15AnchoredAtom2758 Fin15AnchoredAtom2759 Fin15AnchoredAtom2764 Fin15AnchoredAtom2768
    Fin15AnchoredAtom2769 Fin15AnchoredAtom2774 Fin15AnchoredAtom2780 Fin15AnchoredAtom2788
    Fin15AnchoredAtom2789 Fin15AnchoredAtom2794 Fin15AnchoredAtom2800 Fin15AnchoredAtom2810
    Fin15AnchoredAtom4698 Fin15AnchoredAtom4700 Fin15AnchoredAtom4701 Fin15AnchoredAtom4704
    Fin15AnchoredAtom4705 Fin15AnchoredAtom4710 Fin15AnchoredAtom4714 Fin15AnchoredAtom4715
    Fin15AnchoredAtom4720 Fin15AnchoredAtom4726 Fin15AnchoredAtom4734 Fin15AnchoredAtom4735
    Fin15AnchoredAtom4740 Fin15AnchoredAtom4746 Fin15AnchoredAtom4756 Fin15AnchoredAtom4769
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

theorem fin15Anchored_clause31626 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2696 chi ∧
      ¬Fin15AnchoredAtom2697 chi ∧
      ¬Fin15AnchoredAtom2699 chi ∧
      ¬Fin15AnchoredAtom2701 chi ∧
      ¬Fin15AnchoredAtom2702 chi ∧
      ¬Fin15AnchoredAtom2704 chi ∧
      ¬Fin15AnchoredAtom2706 chi ∧
      ¬Fin15AnchoredAtom2708 chi ∧
      ¬Fin15AnchoredAtom2710 chi ∧
      ¬Fin15AnchoredAtom2715 chi ∧
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
      ¬Fin15AnchoredAtom4698 chi ∧
      ¬Fin15AnchoredAtom4700 chi ∧
      ¬Fin15AnchoredAtom4702 chi ∧
      ¬Fin15AnchoredAtom4704 chi ∧
      ¬Fin15AnchoredAtom4706 chi ∧
      ¬Fin15AnchoredAtom4711 chi ∧
      ¬Fin15AnchoredAtom4714 chi ∧
      ¬Fin15AnchoredAtom4716 chi ∧
      ¬Fin15AnchoredAtom4721 chi ∧
      ¬Fin15AnchoredAtom4727 chi ∧
      ¬Fin15AnchoredAtom4734 chi ∧
      ¬Fin15AnchoredAtom4736 chi ∧
      ¬Fin15AnchoredAtom4741 chi ∧
      ¬Fin15AnchoredAtom4747 chi ∧
      ¬Fin15AnchoredAtom4757 chi ∧
      ¬Fin15AnchoredAtom4769 chi ∧
      ¬Fin15AnchoredAtom4771 chi ∧
      ¬Fin15AnchoredAtom4776 chi ∧
      ¬Fin15AnchoredAtom4782 chi ∧
      ¬Fin15AnchoredAtom4792 chi ∧
      ¬Fin15AnchoredAtom4807 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 6, 7, 8, 9, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22465
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2696 Fin15AnchoredAtom2697 Fin15AnchoredAtom2699
    Fin15AnchoredAtom2701 Fin15AnchoredAtom2702 Fin15AnchoredAtom2704 Fin15AnchoredAtom2706
    Fin15AnchoredAtom2708 Fin15AnchoredAtom2710 Fin15AnchoredAtom2715 Fin15AnchoredAtom2717
    Fin15AnchoredAtom2719 Fin15AnchoredAtom2721 Fin15AnchoredAtom2723 Fin15AnchoredAtom2725
    Fin15AnchoredAtom2730 Fin15AnchoredAtom2733 Fin15AnchoredAtom2735 Fin15AnchoredAtom2740
    Fin15AnchoredAtom2746 Fin15AnchoredAtom2752 Fin15AnchoredAtom2754 Fin15AnchoredAtom2756
    Fin15AnchoredAtom2758 Fin15AnchoredAtom2760 Fin15AnchoredAtom2765 Fin15AnchoredAtom2768
    Fin15AnchoredAtom2770 Fin15AnchoredAtom2775 Fin15AnchoredAtom2781 Fin15AnchoredAtom2788
    Fin15AnchoredAtom2790 Fin15AnchoredAtom2795 Fin15AnchoredAtom2801 Fin15AnchoredAtom2811
    Fin15AnchoredAtom4698 Fin15AnchoredAtom4700 Fin15AnchoredAtom4702 Fin15AnchoredAtom4704
    Fin15AnchoredAtom4706 Fin15AnchoredAtom4711 Fin15AnchoredAtom4714 Fin15AnchoredAtom4716
    Fin15AnchoredAtom4721 Fin15AnchoredAtom4727 Fin15AnchoredAtom4734 Fin15AnchoredAtom4736
    Fin15AnchoredAtom4741 Fin15AnchoredAtom4747 Fin15AnchoredAtom4757 Fin15AnchoredAtom4769
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

theorem fin15Anchored_clause31627 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2696 chi ∧
      ¬Fin15AnchoredAtom2697 chi ∧
      ¬Fin15AnchoredAtom2700 chi ∧
      ¬Fin15AnchoredAtom2701 chi ∧
      ¬Fin15AnchoredAtom2702 chi ∧
      ¬Fin15AnchoredAtom2705 chi ∧
      ¬Fin15AnchoredAtom2706 chi ∧
      ¬Fin15AnchoredAtom2709 chi ∧
      ¬Fin15AnchoredAtom2710 chi ∧
      ¬Fin15AnchoredAtom2716 chi ∧
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
      ¬Fin15AnchoredAtom4698 chi ∧
      ¬Fin15AnchoredAtom4701 chi ∧
      ¬Fin15AnchoredAtom4702 chi ∧
      ¬Fin15AnchoredAtom4705 chi ∧
      ¬Fin15AnchoredAtom4706 chi ∧
      ¬Fin15AnchoredAtom4712 chi ∧
      ¬Fin15AnchoredAtom4715 chi ∧
      ¬Fin15AnchoredAtom4716 chi ∧
      ¬Fin15AnchoredAtom4722 chi ∧
      ¬Fin15AnchoredAtom4728 chi ∧
      ¬Fin15AnchoredAtom4735 chi ∧
      ¬Fin15AnchoredAtom4736 chi ∧
      ¬Fin15AnchoredAtom4742 chi ∧
      ¬Fin15AnchoredAtom4748 chi ∧
      ¬Fin15AnchoredAtom4758 chi ∧
      ¬Fin15AnchoredAtom4770 chi ∧
      ¬Fin15AnchoredAtom4771 chi ∧
      ¬Fin15AnchoredAtom4777 chi ∧
      ¬Fin15AnchoredAtom4783 chi ∧
      ¬Fin15AnchoredAtom4793 chi ∧
      ¬Fin15AnchoredAtom4808 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 6, 7, 8, 9, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26561
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2696 Fin15AnchoredAtom2697 Fin15AnchoredAtom2700
    Fin15AnchoredAtom2701 Fin15AnchoredAtom2702 Fin15AnchoredAtom2705 Fin15AnchoredAtom2706
    Fin15AnchoredAtom2709 Fin15AnchoredAtom2710 Fin15AnchoredAtom2716 Fin15AnchoredAtom2717
    Fin15AnchoredAtom2720 Fin15AnchoredAtom2721 Fin15AnchoredAtom2724 Fin15AnchoredAtom2725
    Fin15AnchoredAtom2731 Fin15AnchoredAtom2734 Fin15AnchoredAtom2735 Fin15AnchoredAtom2741
    Fin15AnchoredAtom2747 Fin15AnchoredAtom2752 Fin15AnchoredAtom2755 Fin15AnchoredAtom2756
    Fin15AnchoredAtom2759 Fin15AnchoredAtom2760 Fin15AnchoredAtom2766 Fin15AnchoredAtom2769
    Fin15AnchoredAtom2770 Fin15AnchoredAtom2776 Fin15AnchoredAtom2782 Fin15AnchoredAtom2789
    Fin15AnchoredAtom2790 Fin15AnchoredAtom2796 Fin15AnchoredAtom2802 Fin15AnchoredAtom2812
    Fin15AnchoredAtom4698 Fin15AnchoredAtom4701 Fin15AnchoredAtom4702 Fin15AnchoredAtom4705
    Fin15AnchoredAtom4706 Fin15AnchoredAtom4712 Fin15AnchoredAtom4715 Fin15AnchoredAtom4716
    Fin15AnchoredAtom4722 Fin15AnchoredAtom4728 Fin15AnchoredAtom4735 Fin15AnchoredAtom4736
    Fin15AnchoredAtom4742 Fin15AnchoredAtom4748 Fin15AnchoredAtom4758 Fin15AnchoredAtom4770
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

theorem fin15Anchored_clause31628 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2697 chi ∧
      ¬Fin15AnchoredAtom2699 chi ∧
      ¬Fin15AnchoredAtom2700 chi ∧
      ¬Fin15AnchoredAtom2701 chi ∧
      ¬Fin15AnchoredAtom2708 chi ∧
      ¬Fin15AnchoredAtom2709 chi ∧
      ¬Fin15AnchoredAtom2710 chi ∧
      ¬Fin15AnchoredAtom2714 chi ∧
      ¬Fin15AnchoredAtom2715 chi ∧
      ¬Fin15AnchoredAtom2716 chi ∧
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
      ¬Fin15AnchoredAtom4704 chi ∧
      ¬Fin15AnchoredAtom4705 chi ∧
      ¬Fin15AnchoredAtom4706 chi ∧
      ¬Fin15AnchoredAtom4710 chi ∧
      ¬Fin15AnchoredAtom4711 chi ∧
      ¬Fin15AnchoredAtom4712 chi ∧
      ¬Fin15AnchoredAtom4726 chi ∧
      ¬Fin15AnchoredAtom4727 chi ∧
      ¬Fin15AnchoredAtom4728 chi ∧
      ¬Fin15AnchoredAtom4732 chi ∧
      ¬Fin15AnchoredAtom4746 chi ∧
      ¬Fin15AnchoredAtom4747 chi ∧
      ¬Fin15AnchoredAtom4748 chi ∧
      ¬Fin15AnchoredAtom4752 chi ∧
      ¬Fin15AnchoredAtom4766 chi ∧
      ¬Fin15AnchoredAtom4781 chi ∧
      ¬Fin15AnchoredAtom4782 chi ∧
      ¬Fin15AnchoredAtom4783 chi ∧
      ¬Fin15AnchoredAtom4787 chi ∧
      ¬Fin15AnchoredAtom4801 chi ∧
      ¬Fin15AnchoredAtom4816 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 6, 7, 8, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask30145
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2697 Fin15AnchoredAtom2699 Fin15AnchoredAtom2700
    Fin15AnchoredAtom2701 Fin15AnchoredAtom2708 Fin15AnchoredAtom2709 Fin15AnchoredAtom2710
    Fin15AnchoredAtom2714 Fin15AnchoredAtom2715 Fin15AnchoredAtom2716 Fin15AnchoredAtom2723
    Fin15AnchoredAtom2724 Fin15AnchoredAtom2725 Fin15AnchoredAtom2729 Fin15AnchoredAtom2730
    Fin15AnchoredAtom2731 Fin15AnchoredAtom2745 Fin15AnchoredAtom2746 Fin15AnchoredAtom2747
    Fin15AnchoredAtom2751 Fin15AnchoredAtom2758 Fin15AnchoredAtom2759 Fin15AnchoredAtom2760
    Fin15AnchoredAtom2764 Fin15AnchoredAtom2765 Fin15AnchoredAtom2766 Fin15AnchoredAtom2780
    Fin15AnchoredAtom2781 Fin15AnchoredAtom2782 Fin15AnchoredAtom2786 Fin15AnchoredAtom2800
    Fin15AnchoredAtom2801 Fin15AnchoredAtom2802 Fin15AnchoredAtom2806 Fin15AnchoredAtom2820
    Fin15AnchoredAtom4704 Fin15AnchoredAtom4705 Fin15AnchoredAtom4706 Fin15AnchoredAtom4710
    Fin15AnchoredAtom4711 Fin15AnchoredAtom4712 Fin15AnchoredAtom4726 Fin15AnchoredAtom4727
    Fin15AnchoredAtom4728 Fin15AnchoredAtom4732 Fin15AnchoredAtom4746 Fin15AnchoredAtom4747
    Fin15AnchoredAtom4748 Fin15AnchoredAtom4752 Fin15AnchoredAtom4766 Fin15AnchoredAtom4781
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

theorem fin15Anchored_clause31629 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2702 chi ∧
      ¬Fin15AnchoredAtom2703 chi ∧
      ¬Fin15AnchoredAtom2704 chi ∧
      ¬Fin15AnchoredAtom2705 chi ∧
      ¬Fin15AnchoredAtom2707 chi ∧
      ¬Fin15AnchoredAtom2708 chi ∧
      ¬Fin15AnchoredAtom2709 chi ∧
      ¬Fin15AnchoredAtom2711 chi ∧
      ¬Fin15AnchoredAtom2712 chi ∧
      ¬Fin15AnchoredAtom2714 chi ∧
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
      ¬Fin15AnchoredAtom4713 chi ∧
      ¬Fin15AnchoredAtom4714 chi ∧
      ¬Fin15AnchoredAtom4715 chi ∧
      ¬Fin15AnchoredAtom4717 chi ∧
      ¬Fin15AnchoredAtom4718 chi ∧
      ¬Fin15AnchoredAtom4720 chi ∧
      ¬Fin15AnchoredAtom4723 chi ∧
      ¬Fin15AnchoredAtom4724 chi ∧
      ¬Fin15AnchoredAtom4726 chi ∧
      ¬Fin15AnchoredAtom4729 chi ∧
      ¬Fin15AnchoredAtom4753 chi ∧
      ¬Fin15AnchoredAtom4754 chi ∧
      ¬Fin15AnchoredAtom4756 chi ∧
      ¬Fin15AnchoredAtom4759 chi ∧
      ¬Fin15AnchoredAtom4763 chi ∧
      ¬Fin15AnchoredAtom4788 chi ∧
      ¬Fin15AnchoredAtom4789 chi ∧
      ¬Fin15AnchoredAtom4791 chi ∧
      ¬Fin15AnchoredAtom4794 chi ∧
      ¬Fin15AnchoredAtom4798 chi ∧
      ¬Fin15AnchoredAtom4818 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 6, 7, 9, 10, 11, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask16065
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2702 Fin15AnchoredAtom2703 Fin15AnchoredAtom2704
    Fin15AnchoredAtom2705 Fin15AnchoredAtom2707 Fin15AnchoredAtom2708 Fin15AnchoredAtom2709
    Fin15AnchoredAtom2711 Fin15AnchoredAtom2712 Fin15AnchoredAtom2714 Fin15AnchoredAtom2732
    Fin15AnchoredAtom2733 Fin15AnchoredAtom2734 Fin15AnchoredAtom2736 Fin15AnchoredAtom2737
    Fin15AnchoredAtom2739 Fin15AnchoredAtom2742 Fin15AnchoredAtom2743 Fin15AnchoredAtom2745
    Fin15AnchoredAtom2748 Fin15AnchoredAtom2767 Fin15AnchoredAtom2768 Fin15AnchoredAtom2769
    Fin15AnchoredAtom2771 Fin15AnchoredAtom2772 Fin15AnchoredAtom2774 Fin15AnchoredAtom2777
    Fin15AnchoredAtom2778 Fin15AnchoredAtom2780 Fin15AnchoredAtom2783 Fin15AnchoredAtom2807
    Fin15AnchoredAtom2808 Fin15AnchoredAtom2810 Fin15AnchoredAtom2813 Fin15AnchoredAtom2817
    Fin15AnchoredAtom4713 Fin15AnchoredAtom4714 Fin15AnchoredAtom4715 Fin15AnchoredAtom4717
    Fin15AnchoredAtom4718 Fin15AnchoredAtom4720 Fin15AnchoredAtom4723 Fin15AnchoredAtom4724
    Fin15AnchoredAtom4726 Fin15AnchoredAtom4729 Fin15AnchoredAtom4753 Fin15AnchoredAtom4754
    Fin15AnchoredAtom4756 Fin15AnchoredAtom4759 Fin15AnchoredAtom4763 Fin15AnchoredAtom4788
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

theorem fin15Anchored_clause31630 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2702 chi ∧
      ¬Fin15AnchoredAtom2703 chi ∧
      ¬Fin15AnchoredAtom2704 chi ∧
      ¬Fin15AnchoredAtom2706 chi ∧
      ¬Fin15AnchoredAtom2707 chi ∧
      ¬Fin15AnchoredAtom2708 chi ∧
      ¬Fin15AnchoredAtom2710 chi ∧
      ¬Fin15AnchoredAtom2711 chi ∧
      ¬Fin15AnchoredAtom2713 chi ∧
      ¬Fin15AnchoredAtom2715 chi ∧
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
      ¬Fin15AnchoredAtom2767 chi ∧
      ¬Fin15AnchoredAtom2768 chi ∧
      ¬Fin15AnchoredAtom2770 chi ∧
      ¬Fin15AnchoredAtom2771 chi ∧
      ¬Fin15AnchoredAtom2773 chi ∧
      ¬Fin15AnchoredAtom2775 chi ∧
      ¬Fin15AnchoredAtom2777 chi ∧
      ¬Fin15AnchoredAtom2779 chi ∧
      ¬Fin15AnchoredAtom2781 chi ∧
      ¬Fin15AnchoredAtom2784 chi ∧
      ¬Fin15AnchoredAtom2807 chi ∧
      ¬Fin15AnchoredAtom2809 chi ∧
      ¬Fin15AnchoredAtom2811 chi ∧
      ¬Fin15AnchoredAtom2814 chi ∧
      ¬Fin15AnchoredAtom2818 chi ∧
      ¬Fin15AnchoredAtom4713 chi ∧
      ¬Fin15AnchoredAtom4714 chi ∧
      ¬Fin15AnchoredAtom4716 chi ∧
      ¬Fin15AnchoredAtom4717 chi ∧
      ¬Fin15AnchoredAtom4719 chi ∧
      ¬Fin15AnchoredAtom4721 chi ∧
      ¬Fin15AnchoredAtom4723 chi ∧
      ¬Fin15AnchoredAtom4725 chi ∧
      ¬Fin15AnchoredAtom4727 chi ∧
      ¬Fin15AnchoredAtom4730 chi ∧
      ¬Fin15AnchoredAtom4753 chi ∧
      ¬Fin15AnchoredAtom4755 chi ∧
      ¬Fin15AnchoredAtom4757 chi ∧
      ¬Fin15AnchoredAtom4760 chi ∧
      ¬Fin15AnchoredAtom4764 chi ∧
      ¬Fin15AnchoredAtom4788 chi ∧
      ¬Fin15AnchoredAtom4790 chi ∧
      ¬Fin15AnchoredAtom4792 chi ∧
      ¬Fin15AnchoredAtom4795 chi ∧
      ¬Fin15AnchoredAtom4799 chi ∧
      ¬Fin15AnchoredAtom4819 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 6, 7, 9, 10, 11, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask24257
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2702 Fin15AnchoredAtom2703 Fin15AnchoredAtom2704
    Fin15AnchoredAtom2706 Fin15AnchoredAtom2707 Fin15AnchoredAtom2708 Fin15AnchoredAtom2710
    Fin15AnchoredAtom2711 Fin15AnchoredAtom2713 Fin15AnchoredAtom2715 Fin15AnchoredAtom2732
    Fin15AnchoredAtom2733 Fin15AnchoredAtom2735 Fin15AnchoredAtom2736 Fin15AnchoredAtom2738
    Fin15AnchoredAtom2740 Fin15AnchoredAtom2742 Fin15AnchoredAtom2744 Fin15AnchoredAtom2746
    Fin15AnchoredAtom2749 Fin15AnchoredAtom2767 Fin15AnchoredAtom2768 Fin15AnchoredAtom2770
    Fin15AnchoredAtom2771 Fin15AnchoredAtom2773 Fin15AnchoredAtom2775 Fin15AnchoredAtom2777
    Fin15AnchoredAtom2779 Fin15AnchoredAtom2781 Fin15AnchoredAtom2784 Fin15AnchoredAtom2807
    Fin15AnchoredAtom2809 Fin15AnchoredAtom2811 Fin15AnchoredAtom2814 Fin15AnchoredAtom2818
    Fin15AnchoredAtom4713 Fin15AnchoredAtom4714 Fin15AnchoredAtom4716 Fin15AnchoredAtom4717
    Fin15AnchoredAtom4719 Fin15AnchoredAtom4721 Fin15AnchoredAtom4723 Fin15AnchoredAtom4725
    Fin15AnchoredAtom4727 Fin15AnchoredAtom4730 Fin15AnchoredAtom4753 Fin15AnchoredAtom4755
    Fin15AnchoredAtom4757 Fin15AnchoredAtom4760 Fin15AnchoredAtom4764 Fin15AnchoredAtom4788
    Fin15AnchoredAtom4790 Fin15AnchoredAtom4792 Fin15AnchoredAtom4795 Fin15AnchoredAtom4799
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

theorem fin15Anchored_clause31631 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2702 chi ∧
      ¬Fin15AnchoredAtom2704 chi ∧
      ¬Fin15AnchoredAtom2705 chi ∧
      ¬Fin15AnchoredAtom2706 chi ∧
      ¬Fin15AnchoredAtom2708 chi ∧
      ¬Fin15AnchoredAtom2709 chi ∧
      ¬Fin15AnchoredAtom2710 chi ∧
      ¬Fin15AnchoredAtom2714 chi ∧
      ¬Fin15AnchoredAtom2715 chi ∧
      ¬Fin15AnchoredAtom2716 chi ∧
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
      ¬Fin15AnchoredAtom4714 chi ∧
      ¬Fin15AnchoredAtom4715 chi ∧
      ¬Fin15AnchoredAtom4716 chi ∧
      ¬Fin15AnchoredAtom4720 chi ∧
      ¬Fin15AnchoredAtom4721 chi ∧
      ¬Fin15AnchoredAtom4722 chi ∧
      ¬Fin15AnchoredAtom4726 chi ∧
      ¬Fin15AnchoredAtom4727 chi ∧
      ¬Fin15AnchoredAtom4728 chi ∧
      ¬Fin15AnchoredAtom4732 chi ∧
      ¬Fin15AnchoredAtom4756 chi ∧
      ¬Fin15AnchoredAtom4757 chi ∧
      ¬Fin15AnchoredAtom4758 chi ∧
      ¬Fin15AnchoredAtom4762 chi ∧
      ¬Fin15AnchoredAtom4766 chi ∧
      ¬Fin15AnchoredAtom4791 chi ∧
      ¬Fin15AnchoredAtom4792 chi ∧
      ¬Fin15AnchoredAtom4793 chi ∧
      ¬Fin15AnchoredAtom4797 chi ∧
      ¬Fin15AnchoredAtom4801 chi ∧
      ¬Fin15AnchoredAtom4821 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 6, 7, 9, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask30401
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2702 Fin15AnchoredAtom2704 Fin15AnchoredAtom2705
    Fin15AnchoredAtom2706 Fin15AnchoredAtom2708 Fin15AnchoredAtom2709 Fin15AnchoredAtom2710
    Fin15AnchoredAtom2714 Fin15AnchoredAtom2715 Fin15AnchoredAtom2716 Fin15AnchoredAtom2733
    Fin15AnchoredAtom2734 Fin15AnchoredAtom2735 Fin15AnchoredAtom2739 Fin15AnchoredAtom2740
    Fin15AnchoredAtom2741 Fin15AnchoredAtom2745 Fin15AnchoredAtom2746 Fin15AnchoredAtom2747
    Fin15AnchoredAtom2751 Fin15AnchoredAtom2768 Fin15AnchoredAtom2769 Fin15AnchoredAtom2770
    Fin15AnchoredAtom2774 Fin15AnchoredAtom2775 Fin15AnchoredAtom2776 Fin15AnchoredAtom2780
    Fin15AnchoredAtom2781 Fin15AnchoredAtom2782 Fin15AnchoredAtom2786 Fin15AnchoredAtom2810
    Fin15AnchoredAtom2811 Fin15AnchoredAtom2812 Fin15AnchoredAtom2816 Fin15AnchoredAtom2820
    Fin15AnchoredAtom4714 Fin15AnchoredAtom4715 Fin15AnchoredAtom4716 Fin15AnchoredAtom4720
    Fin15AnchoredAtom4721 Fin15AnchoredAtom4722 Fin15AnchoredAtom4726 Fin15AnchoredAtom4727
    Fin15AnchoredAtom4728 Fin15AnchoredAtom4732 Fin15AnchoredAtom4756 Fin15AnchoredAtom4757
    Fin15AnchoredAtom4758 Fin15AnchoredAtom4762 Fin15AnchoredAtom4766 Fin15AnchoredAtom4791
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

theorem fin15Anchored_clause31632 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2717 chi ∧
      ¬Fin15AnchoredAtom2719 chi ∧
      ¬Fin15AnchoredAtom2720 chi ∧
      ¬Fin15AnchoredAtom2721 chi ∧
      ¬Fin15AnchoredAtom2723 chi ∧
      ¬Fin15AnchoredAtom2724 chi ∧
      ¬Fin15AnchoredAtom2725 chi ∧
      ¬Fin15AnchoredAtom2729 chi ∧
      ¬Fin15AnchoredAtom2730 chi ∧
      ¬Fin15AnchoredAtom2731 chi ∧
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
      ¬Fin15AnchoredAtom4734 chi ∧
      ¬Fin15AnchoredAtom4735 chi ∧
      ¬Fin15AnchoredAtom4736 chi ∧
      ¬Fin15AnchoredAtom4740 chi ∧
      ¬Fin15AnchoredAtom4741 chi ∧
      ¬Fin15AnchoredAtom4742 chi ∧
      ¬Fin15AnchoredAtom4746 chi ∧
      ¬Fin15AnchoredAtom4747 chi ∧
      ¬Fin15AnchoredAtom4748 chi ∧
      ¬Fin15AnchoredAtom4752 chi ∧
      ¬Fin15AnchoredAtom4756 chi ∧
      ¬Fin15AnchoredAtom4757 chi ∧
      ¬Fin15AnchoredAtom4758 chi ∧
      ¬Fin15AnchoredAtom4762 chi ∧
      ¬Fin15AnchoredAtom4766 chi ∧
      ¬Fin15AnchoredAtom4806 chi ∧
      ¬Fin15AnchoredAtom4807 chi ∧
      ¬Fin15AnchoredAtom4808 chi ∧
      ¬Fin15AnchoredAtom4812 chi ∧
      ¬Fin15AnchoredAtom4816 chi ∧
      ¬Fin15AnchoredAtom4821 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 6, 8, 9, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask30529
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2717 Fin15AnchoredAtom2719 Fin15AnchoredAtom2720
    Fin15AnchoredAtom2721 Fin15AnchoredAtom2723 Fin15AnchoredAtom2724 Fin15AnchoredAtom2725
    Fin15AnchoredAtom2729 Fin15AnchoredAtom2730 Fin15AnchoredAtom2731 Fin15AnchoredAtom2733
    Fin15AnchoredAtom2734 Fin15AnchoredAtom2735 Fin15AnchoredAtom2739 Fin15AnchoredAtom2740
    Fin15AnchoredAtom2741 Fin15AnchoredAtom2745 Fin15AnchoredAtom2746 Fin15AnchoredAtom2747
    Fin15AnchoredAtom2751 Fin15AnchoredAtom2788 Fin15AnchoredAtom2789 Fin15AnchoredAtom2790
    Fin15AnchoredAtom2794 Fin15AnchoredAtom2795 Fin15AnchoredAtom2796 Fin15AnchoredAtom2800
    Fin15AnchoredAtom2801 Fin15AnchoredAtom2802 Fin15AnchoredAtom2806 Fin15AnchoredAtom2810
    Fin15AnchoredAtom2811 Fin15AnchoredAtom2812 Fin15AnchoredAtom2816 Fin15AnchoredAtom2820
    Fin15AnchoredAtom4734 Fin15AnchoredAtom4735 Fin15AnchoredAtom4736 Fin15AnchoredAtom4740
    Fin15AnchoredAtom4741 Fin15AnchoredAtom4742 Fin15AnchoredAtom4746 Fin15AnchoredAtom4747
    Fin15AnchoredAtom4748 Fin15AnchoredAtom4752 Fin15AnchoredAtom4756 Fin15AnchoredAtom4757
    Fin15AnchoredAtom4758 Fin15AnchoredAtom4762 Fin15AnchoredAtom4766 Fin15AnchoredAtom4806
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

theorem fin15Anchored_clause31633 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2752 chi ∧
      ¬Fin15AnchoredAtom2754 chi ∧
      ¬Fin15AnchoredAtom2755 chi ∧
      ¬Fin15AnchoredAtom2756 chi ∧
      ¬Fin15AnchoredAtom2758 chi ∧
      ¬Fin15AnchoredAtom2759 chi ∧
      ¬Fin15AnchoredAtom2760 chi ∧
      ¬Fin15AnchoredAtom2764 chi ∧
      ¬Fin15AnchoredAtom2765 chi ∧
      ¬Fin15AnchoredAtom2766 chi ∧
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
      ¬Fin15AnchoredAtom4769 chi ∧
      ¬Fin15AnchoredAtom4770 chi ∧
      ¬Fin15AnchoredAtom4771 chi ∧
      ¬Fin15AnchoredAtom4775 chi ∧
      ¬Fin15AnchoredAtom4776 chi ∧
      ¬Fin15AnchoredAtom4777 chi ∧
      ¬Fin15AnchoredAtom4781 chi ∧
      ¬Fin15AnchoredAtom4782 chi ∧
      ¬Fin15AnchoredAtom4783 chi ∧
      ¬Fin15AnchoredAtom4787 chi ∧
      ¬Fin15AnchoredAtom4791 chi ∧
      ¬Fin15AnchoredAtom4792 chi ∧
      ¬Fin15AnchoredAtom4793 chi ∧
      ¬Fin15AnchoredAtom4797 chi ∧
      ¬Fin15AnchoredAtom4801 chi ∧
      ¬Fin15AnchoredAtom4806 chi ∧
      ¬Fin15AnchoredAtom4807 chi ∧
      ¬Fin15AnchoredAtom4808 chi ∧
      ¬Fin15AnchoredAtom4812 chi ∧
      ¬Fin15AnchoredAtom4816 chi ∧
      ¬Fin15AnchoredAtom4821 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 7, 8, 9, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask30593
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2752 Fin15AnchoredAtom2754 Fin15AnchoredAtom2755
    Fin15AnchoredAtom2756 Fin15AnchoredAtom2758 Fin15AnchoredAtom2759 Fin15AnchoredAtom2760
    Fin15AnchoredAtom2764 Fin15AnchoredAtom2765 Fin15AnchoredAtom2766 Fin15AnchoredAtom2768
    Fin15AnchoredAtom2769 Fin15AnchoredAtom2770 Fin15AnchoredAtom2774 Fin15AnchoredAtom2775
    Fin15AnchoredAtom2776 Fin15AnchoredAtom2780 Fin15AnchoredAtom2781 Fin15AnchoredAtom2782
    Fin15AnchoredAtom2786 Fin15AnchoredAtom2788 Fin15AnchoredAtom2789 Fin15AnchoredAtom2790
    Fin15AnchoredAtom2794 Fin15AnchoredAtom2795 Fin15AnchoredAtom2796 Fin15AnchoredAtom2800
    Fin15AnchoredAtom2801 Fin15AnchoredAtom2802 Fin15AnchoredAtom2806 Fin15AnchoredAtom2810
    Fin15AnchoredAtom2811 Fin15AnchoredAtom2812 Fin15AnchoredAtom2816 Fin15AnchoredAtom2820
    Fin15AnchoredAtom4769 Fin15AnchoredAtom4770 Fin15AnchoredAtom4771 Fin15AnchoredAtom4775
    Fin15AnchoredAtom4776 Fin15AnchoredAtom4777 Fin15AnchoredAtom4781 Fin15AnchoredAtom4782
    Fin15AnchoredAtom4783 Fin15AnchoredAtom4787 Fin15AnchoredAtom4791 Fin15AnchoredAtom4792
    Fin15AnchoredAtom4793 Fin15AnchoredAtom4797 Fin15AnchoredAtom4801 Fin15AnchoredAtom4806
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

theorem fin15Anchored_clause31634 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom2850 chi ∧
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
  refine ⟨{1, 2, 3, 4, 5, 6, 7, 9}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask00766
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2822 Fin15AnchoredAtom2823 Fin15AnchoredAtom2824
    Fin15AnchoredAtom2826 Fin15AnchoredAtom2832 Fin15AnchoredAtom2833 Fin15AnchoredAtom2835
    Fin15AnchoredAtom2841 Fin15AnchoredAtom2843 Fin15AnchoredAtom2850 Fin15AnchoredAtom2877
    Fin15AnchoredAtom2878 Fin15AnchoredAtom2880 Fin15AnchoredAtom2886 Fin15AnchoredAtom2888
    Fin15AnchoredAtom2895 Fin15AnchoredAtom2922 Fin15AnchoredAtom2924 Fin15AnchoredAtom2931
    Fin15AnchoredAtom2959 Fin15AnchoredAtom3042 Fin15AnchoredAtom3043 Fin15AnchoredAtom3045
    Fin15AnchoredAtom3051 Fin15AnchoredAtom3053 Fin15AnchoredAtom3060 Fin15AnchoredAtom3087
    Fin15AnchoredAtom3089 Fin15AnchoredAtom3096 Fin15AnchoredAtom3124 Fin15AnchoredAtom3207
    Fin15AnchoredAtom3209 Fin15AnchoredAtom3216 Fin15AnchoredAtom3244 Fin15AnchoredAtom3328
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

theorem fin15Anchored_clause31635 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom2851 chi ∧
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
  refine ⟨{1, 2, 3, 4, 5, 6, 7, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask01278
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2822 Fin15AnchoredAtom2823 Fin15AnchoredAtom2824
    Fin15AnchoredAtom2827 Fin15AnchoredAtom2832 Fin15AnchoredAtom2833 Fin15AnchoredAtom2836
    Fin15AnchoredAtom2841 Fin15AnchoredAtom2844 Fin15AnchoredAtom2851 Fin15AnchoredAtom2877
    Fin15AnchoredAtom2878 Fin15AnchoredAtom2881 Fin15AnchoredAtom2886 Fin15AnchoredAtom2889
    Fin15AnchoredAtom2896 Fin15AnchoredAtom2922 Fin15AnchoredAtom2925 Fin15AnchoredAtom2932
    Fin15AnchoredAtom2960 Fin15AnchoredAtom3042 Fin15AnchoredAtom3043 Fin15AnchoredAtom3046
    Fin15AnchoredAtom3051 Fin15AnchoredAtom3054 Fin15AnchoredAtom3061 Fin15AnchoredAtom3087
    Fin15AnchoredAtom3090 Fin15AnchoredAtom3097 Fin15AnchoredAtom3125 Fin15AnchoredAtom3207
    Fin15AnchoredAtom3210 Fin15AnchoredAtom3217 Fin15AnchoredAtom3245 Fin15AnchoredAtom3329
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

theorem fin15Anchored_clause31636 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom2853 chi ∧
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
  refine ⟨{1, 2, 3, 4, 5, 6, 7, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask04350
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2822 Fin15AnchoredAtom2823 Fin15AnchoredAtom2824
    Fin15AnchoredAtom2829 Fin15AnchoredAtom2832 Fin15AnchoredAtom2833 Fin15AnchoredAtom2838
    Fin15AnchoredAtom2841 Fin15AnchoredAtom2846 Fin15AnchoredAtom2853 Fin15AnchoredAtom2877
    Fin15AnchoredAtom2878 Fin15AnchoredAtom2883 Fin15AnchoredAtom2886 Fin15AnchoredAtom2891
    Fin15AnchoredAtom2898 Fin15AnchoredAtom2922 Fin15AnchoredAtom2927 Fin15AnchoredAtom2934
    Fin15AnchoredAtom2962 Fin15AnchoredAtom3042 Fin15AnchoredAtom3043 Fin15AnchoredAtom3048
    Fin15AnchoredAtom3051 Fin15AnchoredAtom3056 Fin15AnchoredAtom3063 Fin15AnchoredAtom3087
    Fin15AnchoredAtom3092 Fin15AnchoredAtom3099 Fin15AnchoredAtom3127 Fin15AnchoredAtom3207
    Fin15AnchoredAtom3212 Fin15AnchoredAtom3219 Fin15AnchoredAtom3247 Fin15AnchoredAtom3331
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

theorem fin15Anchored_clause31637 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom2854 chi ∧
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
  refine ⟨{1, 2, 3, 4, 5, 6, 7, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask08446
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2822 Fin15AnchoredAtom2823 Fin15AnchoredAtom2824
    Fin15AnchoredAtom2830 Fin15AnchoredAtom2832 Fin15AnchoredAtom2833 Fin15AnchoredAtom2839
    Fin15AnchoredAtom2841 Fin15AnchoredAtom2847 Fin15AnchoredAtom2854 Fin15AnchoredAtom2877
    Fin15AnchoredAtom2878 Fin15AnchoredAtom2884 Fin15AnchoredAtom2886 Fin15AnchoredAtom2892
    Fin15AnchoredAtom2899 Fin15AnchoredAtom2922 Fin15AnchoredAtom2928 Fin15AnchoredAtom2935
    Fin15AnchoredAtom2963 Fin15AnchoredAtom3042 Fin15AnchoredAtom3043 Fin15AnchoredAtom3049
    Fin15AnchoredAtom3051 Fin15AnchoredAtom3057 Fin15AnchoredAtom3064 Fin15AnchoredAtom3087
    Fin15AnchoredAtom3093 Fin15AnchoredAtom3100 Fin15AnchoredAtom3128 Fin15AnchoredAtom3207
    Fin15AnchoredAtom3213 Fin15AnchoredAtom3220 Fin15AnchoredAtom3248 Fin15AnchoredAtom3332
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

theorem fin15Anchored_clause31638 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom2855 chi ∧
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
  refine ⟨{1, 2, 3, 4, 5, 6, 7, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask16638
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2822 Fin15AnchoredAtom2823 Fin15AnchoredAtom2824
    Fin15AnchoredAtom2831 Fin15AnchoredAtom2832 Fin15AnchoredAtom2833 Fin15AnchoredAtom2840
    Fin15AnchoredAtom2841 Fin15AnchoredAtom2848 Fin15AnchoredAtom2855 Fin15AnchoredAtom2877
    Fin15AnchoredAtom2878 Fin15AnchoredAtom2885 Fin15AnchoredAtom2886 Fin15AnchoredAtom2893
    Fin15AnchoredAtom2900 Fin15AnchoredAtom2922 Fin15AnchoredAtom2929 Fin15AnchoredAtom2936
    Fin15AnchoredAtom2964 Fin15AnchoredAtom3042 Fin15AnchoredAtom3043 Fin15AnchoredAtom3050
    Fin15AnchoredAtom3051 Fin15AnchoredAtom3058 Fin15AnchoredAtom3065 Fin15AnchoredAtom3087
    Fin15AnchoredAtom3094 Fin15AnchoredAtom3101 Fin15AnchoredAtom3129 Fin15AnchoredAtom3207
    Fin15AnchoredAtom3214 Fin15AnchoredAtom3221 Fin15AnchoredAtom3249 Fin15AnchoredAtom3333
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

theorem fin15Anchored_clause31639 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom2862 chi ∧
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
  refine ⟨{1, 2, 3, 4, 5, 6, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask01662
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2822 Fin15AnchoredAtom2823 Fin15AnchoredAtom2826
    Fin15AnchoredAtom2827 Fin15AnchoredAtom2832 Fin15AnchoredAtom2835 Fin15AnchoredAtom2836
    Fin15AnchoredAtom2843 Fin15AnchoredAtom2844 Fin15AnchoredAtom2862 Fin15AnchoredAtom2877
    Fin15AnchoredAtom2880 Fin15AnchoredAtom2881 Fin15AnchoredAtom2888 Fin15AnchoredAtom2889
    Fin15AnchoredAtom2907 Fin15AnchoredAtom2924 Fin15AnchoredAtom2925 Fin15AnchoredAtom2943
    Fin15AnchoredAtom2971 Fin15AnchoredAtom3042 Fin15AnchoredAtom3045 Fin15AnchoredAtom3046
    Fin15AnchoredAtom3053 Fin15AnchoredAtom3054 Fin15AnchoredAtom3072 Fin15AnchoredAtom3089
    Fin15AnchoredAtom3090 Fin15AnchoredAtom3108 Fin15AnchoredAtom3136 Fin15AnchoredAtom3209
    Fin15AnchoredAtom3210 Fin15AnchoredAtom3228 Fin15AnchoredAtom3256 Fin15AnchoredAtom3340
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

theorem fin15Anchored_clause31640 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom2864 chi ∧
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
  refine ⟨{1, 2, 3, 4, 5, 6, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask04734
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2822 Fin15AnchoredAtom2823 Fin15AnchoredAtom2826
    Fin15AnchoredAtom2829 Fin15AnchoredAtom2832 Fin15AnchoredAtom2835 Fin15AnchoredAtom2838
    Fin15AnchoredAtom2843 Fin15AnchoredAtom2846 Fin15AnchoredAtom2864 Fin15AnchoredAtom2877
    Fin15AnchoredAtom2880 Fin15AnchoredAtom2883 Fin15AnchoredAtom2888 Fin15AnchoredAtom2891
    Fin15AnchoredAtom2909 Fin15AnchoredAtom2924 Fin15AnchoredAtom2927 Fin15AnchoredAtom2945
    Fin15AnchoredAtom2973 Fin15AnchoredAtom3042 Fin15AnchoredAtom3045 Fin15AnchoredAtom3048
    Fin15AnchoredAtom3053 Fin15AnchoredAtom3056 Fin15AnchoredAtom3074 Fin15AnchoredAtom3089
    Fin15AnchoredAtom3092 Fin15AnchoredAtom3110 Fin15AnchoredAtom3138 Fin15AnchoredAtom3209
    Fin15AnchoredAtom3212 Fin15AnchoredAtom3230 Fin15AnchoredAtom3258 Fin15AnchoredAtom3342
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

theorem fin15Anchored_clause31641 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom2865 chi ∧
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
  refine ⟨{1, 2, 3, 4, 5, 6, 9, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask08830
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2822 Fin15AnchoredAtom2823 Fin15AnchoredAtom2826
    Fin15AnchoredAtom2830 Fin15AnchoredAtom2832 Fin15AnchoredAtom2835 Fin15AnchoredAtom2839
    Fin15AnchoredAtom2843 Fin15AnchoredAtom2847 Fin15AnchoredAtom2865 Fin15AnchoredAtom2877
    Fin15AnchoredAtom2880 Fin15AnchoredAtom2884 Fin15AnchoredAtom2888 Fin15AnchoredAtom2892
    Fin15AnchoredAtom2910 Fin15AnchoredAtom2924 Fin15AnchoredAtom2928 Fin15AnchoredAtom2946
    Fin15AnchoredAtom2974 Fin15AnchoredAtom3042 Fin15AnchoredAtom3045 Fin15AnchoredAtom3049
    Fin15AnchoredAtom3053 Fin15AnchoredAtom3057 Fin15AnchoredAtom3075 Fin15AnchoredAtom3089
    Fin15AnchoredAtom3093 Fin15AnchoredAtom3111 Fin15AnchoredAtom3139 Fin15AnchoredAtom3209
    Fin15AnchoredAtom3213 Fin15AnchoredAtom3231 Fin15AnchoredAtom3259 Fin15AnchoredAtom3343
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

theorem fin15Anchored_clause31642 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom2866 chi ∧
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
  refine ⟨{1, 2, 3, 4, 5, 6, 9, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17022
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2822 Fin15AnchoredAtom2823 Fin15AnchoredAtom2826
    Fin15AnchoredAtom2831 Fin15AnchoredAtom2832 Fin15AnchoredAtom2835 Fin15AnchoredAtom2840
    Fin15AnchoredAtom2843 Fin15AnchoredAtom2848 Fin15AnchoredAtom2866 Fin15AnchoredAtom2877
    Fin15AnchoredAtom2880 Fin15AnchoredAtom2885 Fin15AnchoredAtom2888 Fin15AnchoredAtom2893
    Fin15AnchoredAtom2911 Fin15AnchoredAtom2924 Fin15AnchoredAtom2929 Fin15AnchoredAtom2947
    Fin15AnchoredAtom2975 Fin15AnchoredAtom3042 Fin15AnchoredAtom3045 Fin15AnchoredAtom3050
    Fin15AnchoredAtom3053 Fin15AnchoredAtom3058 Fin15AnchoredAtom3076 Fin15AnchoredAtom3089
    Fin15AnchoredAtom3094 Fin15AnchoredAtom3112 Fin15AnchoredAtom3140 Fin15AnchoredAtom3209
    Fin15AnchoredAtom3214 Fin15AnchoredAtom3232 Fin15AnchoredAtom3260 Fin15AnchoredAtom3344
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

theorem fin15Anchored_clause31643 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom2868 chi ∧
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
  refine ⟨{1, 2, 3, 4, 5, 6, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05246
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2822 Fin15AnchoredAtom2823 Fin15AnchoredAtom2827
    Fin15AnchoredAtom2829 Fin15AnchoredAtom2832 Fin15AnchoredAtom2836 Fin15AnchoredAtom2838
    Fin15AnchoredAtom2844 Fin15AnchoredAtom2846 Fin15AnchoredAtom2868 Fin15AnchoredAtom2877
    Fin15AnchoredAtom2881 Fin15AnchoredAtom2883 Fin15AnchoredAtom2889 Fin15AnchoredAtom2891
    Fin15AnchoredAtom2913 Fin15AnchoredAtom2925 Fin15AnchoredAtom2927 Fin15AnchoredAtom2949
    Fin15AnchoredAtom2977 Fin15AnchoredAtom3042 Fin15AnchoredAtom3046 Fin15AnchoredAtom3048
    Fin15AnchoredAtom3054 Fin15AnchoredAtom3056 Fin15AnchoredAtom3078 Fin15AnchoredAtom3090
    Fin15AnchoredAtom3092 Fin15AnchoredAtom3114 Fin15AnchoredAtom3142 Fin15AnchoredAtom3210
    Fin15AnchoredAtom3212 Fin15AnchoredAtom3234 Fin15AnchoredAtom3262 Fin15AnchoredAtom3346
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

theorem fin15Anchored_clause31644 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom2869 chi ∧
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
  refine ⟨{1, 2, 3, 4, 5, 6, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09342
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2822 Fin15AnchoredAtom2823 Fin15AnchoredAtom2827
    Fin15AnchoredAtom2830 Fin15AnchoredAtom2832 Fin15AnchoredAtom2836 Fin15AnchoredAtom2839
    Fin15AnchoredAtom2844 Fin15AnchoredAtom2847 Fin15AnchoredAtom2869 Fin15AnchoredAtom2877
    Fin15AnchoredAtom2881 Fin15AnchoredAtom2884 Fin15AnchoredAtom2889 Fin15AnchoredAtom2892
    Fin15AnchoredAtom2914 Fin15AnchoredAtom2925 Fin15AnchoredAtom2928 Fin15AnchoredAtom2950
    Fin15AnchoredAtom2978 Fin15AnchoredAtom3042 Fin15AnchoredAtom3046 Fin15AnchoredAtom3049
    Fin15AnchoredAtom3054 Fin15AnchoredAtom3057 Fin15AnchoredAtom3079 Fin15AnchoredAtom3090
    Fin15AnchoredAtom3093 Fin15AnchoredAtom3115 Fin15AnchoredAtom3143 Fin15AnchoredAtom3210
    Fin15AnchoredAtom3213 Fin15AnchoredAtom3235 Fin15AnchoredAtom3263 Fin15AnchoredAtom3347
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

theorem fin15Anchored_clause31645 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom2870 chi ∧
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
  refine ⟨{1, 2, 3, 4, 5, 6, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17534
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2822 Fin15AnchoredAtom2823 Fin15AnchoredAtom2827
    Fin15AnchoredAtom2831 Fin15AnchoredAtom2832 Fin15AnchoredAtom2836 Fin15AnchoredAtom2840
    Fin15AnchoredAtom2844 Fin15AnchoredAtom2848 Fin15AnchoredAtom2870 Fin15AnchoredAtom2877
    Fin15AnchoredAtom2881 Fin15AnchoredAtom2885 Fin15AnchoredAtom2889 Fin15AnchoredAtom2893
    Fin15AnchoredAtom2915 Fin15AnchoredAtom2925 Fin15AnchoredAtom2929 Fin15AnchoredAtom2951
    Fin15AnchoredAtom2979 Fin15AnchoredAtom3042 Fin15AnchoredAtom3046 Fin15AnchoredAtom3050
    Fin15AnchoredAtom3054 Fin15AnchoredAtom3058 Fin15AnchoredAtom3080 Fin15AnchoredAtom3090
    Fin15AnchoredAtom3094 Fin15AnchoredAtom3116 Fin15AnchoredAtom3144 Fin15AnchoredAtom3210
    Fin15AnchoredAtom3214 Fin15AnchoredAtom3236 Fin15AnchoredAtom3264 Fin15AnchoredAtom3348
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

theorem fin15Anchored_clause31646 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom2874 chi ∧
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
  refine ⟨{1, 2, 3, 4, 5, 6, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask12414
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2822 Fin15AnchoredAtom2823 Fin15AnchoredAtom2829
    Fin15AnchoredAtom2830 Fin15AnchoredAtom2832 Fin15AnchoredAtom2838 Fin15AnchoredAtom2839
    Fin15AnchoredAtom2846 Fin15AnchoredAtom2847 Fin15AnchoredAtom2874 Fin15AnchoredAtom2877
    Fin15AnchoredAtom2883 Fin15AnchoredAtom2884 Fin15AnchoredAtom2891 Fin15AnchoredAtom2892
    Fin15AnchoredAtom2919 Fin15AnchoredAtom2927 Fin15AnchoredAtom2928 Fin15AnchoredAtom2955
    Fin15AnchoredAtom2983 Fin15AnchoredAtom3042 Fin15AnchoredAtom3048 Fin15AnchoredAtom3049
    Fin15AnchoredAtom3056 Fin15AnchoredAtom3057 Fin15AnchoredAtom3084 Fin15AnchoredAtom3092
    Fin15AnchoredAtom3093 Fin15AnchoredAtom3120 Fin15AnchoredAtom3148 Fin15AnchoredAtom3212
    Fin15AnchoredAtom3213 Fin15AnchoredAtom3240 Fin15AnchoredAtom3268 Fin15AnchoredAtom3352
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

theorem fin15Anchored_clause31647 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom2875 chi ∧
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
  refine ⟨{1, 2, 3, 4, 5, 6, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask20606
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2822 Fin15AnchoredAtom2823 Fin15AnchoredAtom2829
    Fin15AnchoredAtom2831 Fin15AnchoredAtom2832 Fin15AnchoredAtom2838 Fin15AnchoredAtom2840
    Fin15AnchoredAtom2846 Fin15AnchoredAtom2848 Fin15AnchoredAtom2875 Fin15AnchoredAtom2877
    Fin15AnchoredAtom2883 Fin15AnchoredAtom2885 Fin15AnchoredAtom2891 Fin15AnchoredAtom2893
    Fin15AnchoredAtom2920 Fin15AnchoredAtom2927 Fin15AnchoredAtom2929 Fin15AnchoredAtom2956
    Fin15AnchoredAtom2984 Fin15AnchoredAtom3042 Fin15AnchoredAtom3048 Fin15AnchoredAtom3050
    Fin15AnchoredAtom3056 Fin15AnchoredAtom3058 Fin15AnchoredAtom3085 Fin15AnchoredAtom3092
    Fin15AnchoredAtom3094 Fin15AnchoredAtom3121 Fin15AnchoredAtom3149 Fin15AnchoredAtom3212
    Fin15AnchoredAtom3214 Fin15AnchoredAtom3241 Fin15AnchoredAtom3269 Fin15AnchoredAtom3353
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

theorem fin15Anchored_clause31648 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom2876 chi ∧
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
  refine ⟨{1, 2, 3, 4, 5, 6, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask24702
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2822 Fin15AnchoredAtom2823 Fin15AnchoredAtom2830
    Fin15AnchoredAtom2831 Fin15AnchoredAtom2832 Fin15AnchoredAtom2839 Fin15AnchoredAtom2840
    Fin15AnchoredAtom2847 Fin15AnchoredAtom2848 Fin15AnchoredAtom2876 Fin15AnchoredAtom2877
    Fin15AnchoredAtom2884 Fin15AnchoredAtom2885 Fin15AnchoredAtom2892 Fin15AnchoredAtom2893
    Fin15AnchoredAtom2921 Fin15AnchoredAtom2928 Fin15AnchoredAtom2929 Fin15AnchoredAtom2957
    Fin15AnchoredAtom2985 Fin15AnchoredAtom3042 Fin15AnchoredAtom3049 Fin15AnchoredAtom3050
    Fin15AnchoredAtom3057 Fin15AnchoredAtom3058 Fin15AnchoredAtom3086 Fin15AnchoredAtom3093
    Fin15AnchoredAtom3094 Fin15AnchoredAtom3122 Fin15AnchoredAtom3150 Fin15AnchoredAtom3213
    Fin15AnchoredAtom3214 Fin15AnchoredAtom3242 Fin15AnchoredAtom3270 Fin15AnchoredAtom3354
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

theorem fin15Anchored_clause31649 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom2862 chi ∧
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
  refine ⟨{1, 2, 3, 4, 5, 7, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask01726
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2822 Fin15AnchoredAtom2824 Fin15AnchoredAtom2826
    Fin15AnchoredAtom2827 Fin15AnchoredAtom2833 Fin15AnchoredAtom2835 Fin15AnchoredAtom2836
    Fin15AnchoredAtom2850 Fin15AnchoredAtom2851 Fin15AnchoredAtom2862 Fin15AnchoredAtom2878
    Fin15AnchoredAtom2880 Fin15AnchoredAtom2881 Fin15AnchoredAtom2895 Fin15AnchoredAtom2896
    Fin15AnchoredAtom2907 Fin15AnchoredAtom2931 Fin15AnchoredAtom2932 Fin15AnchoredAtom2943
    Fin15AnchoredAtom2992 Fin15AnchoredAtom3043 Fin15AnchoredAtom3045 Fin15AnchoredAtom3046
    Fin15AnchoredAtom3060 Fin15AnchoredAtom3061 Fin15AnchoredAtom3072 Fin15AnchoredAtom3096
    Fin15AnchoredAtom3097 Fin15AnchoredAtom3108 Fin15AnchoredAtom3157 Fin15AnchoredAtom3216
    Fin15AnchoredAtom3217 Fin15AnchoredAtom3228 Fin15AnchoredAtom3277 Fin15AnchoredAtom3361
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

theorem fin15Anchored_clause31650 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom2864 chi ∧
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
  refine ⟨{1, 2, 3, 4, 5, 7, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask04798
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2822 Fin15AnchoredAtom2824 Fin15AnchoredAtom2826
    Fin15AnchoredAtom2829 Fin15AnchoredAtom2833 Fin15AnchoredAtom2835 Fin15AnchoredAtom2838
    Fin15AnchoredAtom2850 Fin15AnchoredAtom2853 Fin15AnchoredAtom2864 Fin15AnchoredAtom2878
    Fin15AnchoredAtom2880 Fin15AnchoredAtom2883 Fin15AnchoredAtom2895 Fin15AnchoredAtom2898
    Fin15AnchoredAtom2909 Fin15AnchoredAtom2931 Fin15AnchoredAtom2934 Fin15AnchoredAtom2945
    Fin15AnchoredAtom2994 Fin15AnchoredAtom3043 Fin15AnchoredAtom3045 Fin15AnchoredAtom3048
    Fin15AnchoredAtom3060 Fin15AnchoredAtom3063 Fin15AnchoredAtom3074 Fin15AnchoredAtom3096
    Fin15AnchoredAtom3099 Fin15AnchoredAtom3110 Fin15AnchoredAtom3159 Fin15AnchoredAtom3216
    Fin15AnchoredAtom3219 Fin15AnchoredAtom3230 Fin15AnchoredAtom3279 Fin15AnchoredAtom3363
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

theorem fin15Anchored_clause31651 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom2865 chi ∧
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
  refine ⟨{1, 2, 3, 4, 5, 7, 9, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask08894
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2822 Fin15AnchoredAtom2824 Fin15AnchoredAtom2826
    Fin15AnchoredAtom2830 Fin15AnchoredAtom2833 Fin15AnchoredAtom2835 Fin15AnchoredAtom2839
    Fin15AnchoredAtom2850 Fin15AnchoredAtom2854 Fin15AnchoredAtom2865 Fin15AnchoredAtom2878
    Fin15AnchoredAtom2880 Fin15AnchoredAtom2884 Fin15AnchoredAtom2895 Fin15AnchoredAtom2899
    Fin15AnchoredAtom2910 Fin15AnchoredAtom2931 Fin15AnchoredAtom2935 Fin15AnchoredAtom2946
    Fin15AnchoredAtom2995 Fin15AnchoredAtom3043 Fin15AnchoredAtom3045 Fin15AnchoredAtom3049
    Fin15AnchoredAtom3060 Fin15AnchoredAtom3064 Fin15AnchoredAtom3075 Fin15AnchoredAtom3096
    Fin15AnchoredAtom3100 Fin15AnchoredAtom3111 Fin15AnchoredAtom3160 Fin15AnchoredAtom3216
    Fin15AnchoredAtom3220 Fin15AnchoredAtom3231 Fin15AnchoredAtom3280 Fin15AnchoredAtom3364
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

theorem fin15Anchored_clause31652 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom2866 chi ∧
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
  refine ⟨{1, 2, 3, 4, 5, 7, 9, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17086
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2822 Fin15AnchoredAtom2824 Fin15AnchoredAtom2826
    Fin15AnchoredAtom2831 Fin15AnchoredAtom2833 Fin15AnchoredAtom2835 Fin15AnchoredAtom2840
    Fin15AnchoredAtom2850 Fin15AnchoredAtom2855 Fin15AnchoredAtom2866 Fin15AnchoredAtom2878
    Fin15AnchoredAtom2880 Fin15AnchoredAtom2885 Fin15AnchoredAtom2895 Fin15AnchoredAtom2900
    Fin15AnchoredAtom2911 Fin15AnchoredAtom2931 Fin15AnchoredAtom2936 Fin15AnchoredAtom2947
    Fin15AnchoredAtom2996 Fin15AnchoredAtom3043 Fin15AnchoredAtom3045 Fin15AnchoredAtom3050
    Fin15AnchoredAtom3060 Fin15AnchoredAtom3065 Fin15AnchoredAtom3076 Fin15AnchoredAtom3096
    Fin15AnchoredAtom3101 Fin15AnchoredAtom3112 Fin15AnchoredAtom3161 Fin15AnchoredAtom3216
    Fin15AnchoredAtom3221 Fin15AnchoredAtom3232 Fin15AnchoredAtom3281 Fin15AnchoredAtom3365
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

theorem fin15Anchored_clause31653 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom2868 chi ∧
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
  refine ⟨{1, 2, 3, 4, 5, 7, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05310
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2822 Fin15AnchoredAtom2824 Fin15AnchoredAtom2827
    Fin15AnchoredAtom2829 Fin15AnchoredAtom2833 Fin15AnchoredAtom2836 Fin15AnchoredAtom2838
    Fin15AnchoredAtom2851 Fin15AnchoredAtom2853 Fin15AnchoredAtom2868 Fin15AnchoredAtom2878
    Fin15AnchoredAtom2881 Fin15AnchoredAtom2883 Fin15AnchoredAtom2896 Fin15AnchoredAtom2898
    Fin15AnchoredAtom2913 Fin15AnchoredAtom2932 Fin15AnchoredAtom2934 Fin15AnchoredAtom2949
    Fin15AnchoredAtom2998 Fin15AnchoredAtom3043 Fin15AnchoredAtom3046 Fin15AnchoredAtom3048
    Fin15AnchoredAtom3061 Fin15AnchoredAtom3063 Fin15AnchoredAtom3078 Fin15AnchoredAtom3097
    Fin15AnchoredAtom3099 Fin15AnchoredAtom3114 Fin15AnchoredAtom3163 Fin15AnchoredAtom3217
    Fin15AnchoredAtom3219 Fin15AnchoredAtom3234 Fin15AnchoredAtom3283 Fin15AnchoredAtom3367
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

theorem fin15Anchored_clause31654 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom2869 chi ∧
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
  refine ⟨{1, 2, 3, 4, 5, 7, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09406
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2822 Fin15AnchoredAtom2824 Fin15AnchoredAtom2827
    Fin15AnchoredAtom2830 Fin15AnchoredAtom2833 Fin15AnchoredAtom2836 Fin15AnchoredAtom2839
    Fin15AnchoredAtom2851 Fin15AnchoredAtom2854 Fin15AnchoredAtom2869 Fin15AnchoredAtom2878
    Fin15AnchoredAtom2881 Fin15AnchoredAtom2884 Fin15AnchoredAtom2896 Fin15AnchoredAtom2899
    Fin15AnchoredAtom2914 Fin15AnchoredAtom2932 Fin15AnchoredAtom2935 Fin15AnchoredAtom2950
    Fin15AnchoredAtom2999 Fin15AnchoredAtom3043 Fin15AnchoredAtom3046 Fin15AnchoredAtom3049
    Fin15AnchoredAtom3061 Fin15AnchoredAtom3064 Fin15AnchoredAtom3079 Fin15AnchoredAtom3097
    Fin15AnchoredAtom3100 Fin15AnchoredAtom3115 Fin15AnchoredAtom3164 Fin15AnchoredAtom3217
    Fin15AnchoredAtom3220 Fin15AnchoredAtom3235 Fin15AnchoredAtom3284 Fin15AnchoredAtom3368
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

theorem fin15Anchored_clause31655 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom2870 chi ∧
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
  refine ⟨{1, 2, 3, 4, 5, 7, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17598
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2822 Fin15AnchoredAtom2824 Fin15AnchoredAtom2827
    Fin15AnchoredAtom2831 Fin15AnchoredAtom2833 Fin15AnchoredAtom2836 Fin15AnchoredAtom2840
    Fin15AnchoredAtom2851 Fin15AnchoredAtom2855 Fin15AnchoredAtom2870 Fin15AnchoredAtom2878
    Fin15AnchoredAtom2881 Fin15AnchoredAtom2885 Fin15AnchoredAtom2896 Fin15AnchoredAtom2900
    Fin15AnchoredAtom2915 Fin15AnchoredAtom2932 Fin15AnchoredAtom2936 Fin15AnchoredAtom2951
    Fin15AnchoredAtom3000 Fin15AnchoredAtom3043 Fin15AnchoredAtom3046 Fin15AnchoredAtom3050
    Fin15AnchoredAtom3061 Fin15AnchoredAtom3065 Fin15AnchoredAtom3080 Fin15AnchoredAtom3097
    Fin15AnchoredAtom3101 Fin15AnchoredAtom3116 Fin15AnchoredAtom3165 Fin15AnchoredAtom3217
    Fin15AnchoredAtom3221 Fin15AnchoredAtom3236 Fin15AnchoredAtom3285 Fin15AnchoredAtom3369
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

theorem fin15Anchored_clause31656 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom2874 chi ∧
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
  refine ⟨{1, 2, 3, 4, 5, 7, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask12478
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2822 Fin15AnchoredAtom2824 Fin15AnchoredAtom2829
    Fin15AnchoredAtom2830 Fin15AnchoredAtom2833 Fin15AnchoredAtom2838 Fin15AnchoredAtom2839
    Fin15AnchoredAtom2853 Fin15AnchoredAtom2854 Fin15AnchoredAtom2874 Fin15AnchoredAtom2878
    Fin15AnchoredAtom2883 Fin15AnchoredAtom2884 Fin15AnchoredAtom2898 Fin15AnchoredAtom2899
    Fin15AnchoredAtom2919 Fin15AnchoredAtom2934 Fin15AnchoredAtom2935 Fin15AnchoredAtom2955
    Fin15AnchoredAtom3004 Fin15AnchoredAtom3043 Fin15AnchoredAtom3048 Fin15AnchoredAtom3049
    Fin15AnchoredAtom3063 Fin15AnchoredAtom3064 Fin15AnchoredAtom3084 Fin15AnchoredAtom3099
    Fin15AnchoredAtom3100 Fin15AnchoredAtom3120 Fin15AnchoredAtom3169 Fin15AnchoredAtom3219
    Fin15AnchoredAtom3220 Fin15AnchoredAtom3240 Fin15AnchoredAtom3289 Fin15AnchoredAtom3373
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

theorem fin15Anchored_clause31657 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom2875 chi ∧
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
  refine ⟨{1, 2, 3, 4, 5, 7, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask20670
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2822 Fin15AnchoredAtom2824 Fin15AnchoredAtom2829
    Fin15AnchoredAtom2831 Fin15AnchoredAtom2833 Fin15AnchoredAtom2838 Fin15AnchoredAtom2840
    Fin15AnchoredAtom2853 Fin15AnchoredAtom2855 Fin15AnchoredAtom2875 Fin15AnchoredAtom2878
    Fin15AnchoredAtom2883 Fin15AnchoredAtom2885 Fin15AnchoredAtom2898 Fin15AnchoredAtom2900
    Fin15AnchoredAtom2920 Fin15AnchoredAtom2934 Fin15AnchoredAtom2936 Fin15AnchoredAtom2956
    Fin15AnchoredAtom3005 Fin15AnchoredAtom3043 Fin15AnchoredAtom3048 Fin15AnchoredAtom3050
    Fin15AnchoredAtom3063 Fin15AnchoredAtom3065 Fin15AnchoredAtom3085 Fin15AnchoredAtom3099
    Fin15AnchoredAtom3101 Fin15AnchoredAtom3121 Fin15AnchoredAtom3170 Fin15AnchoredAtom3219
    Fin15AnchoredAtom3221 Fin15AnchoredAtom3241 Fin15AnchoredAtom3290 Fin15AnchoredAtom3374
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

theorem fin15Anchored_clause31658 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom2876 chi ∧
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
  refine ⟨{1, 2, 3, 4, 5, 7, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask24766
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2822 Fin15AnchoredAtom2824 Fin15AnchoredAtom2830
    Fin15AnchoredAtom2831 Fin15AnchoredAtom2833 Fin15AnchoredAtom2839 Fin15AnchoredAtom2840
    Fin15AnchoredAtom2854 Fin15AnchoredAtom2855 Fin15AnchoredAtom2876 Fin15AnchoredAtom2878
    Fin15AnchoredAtom2884 Fin15AnchoredAtom2885 Fin15AnchoredAtom2899 Fin15AnchoredAtom2900
    Fin15AnchoredAtom2921 Fin15AnchoredAtom2935 Fin15AnchoredAtom2936 Fin15AnchoredAtom2957
    Fin15AnchoredAtom3006 Fin15AnchoredAtom3043 Fin15AnchoredAtom3049 Fin15AnchoredAtom3050
    Fin15AnchoredAtom3064 Fin15AnchoredAtom3065 Fin15AnchoredAtom3086 Fin15AnchoredAtom3100
    Fin15AnchoredAtom3101 Fin15AnchoredAtom3122 Fin15AnchoredAtom3171 Fin15AnchoredAtom3220
    Fin15AnchoredAtom3221 Fin15AnchoredAtom3242 Fin15AnchoredAtom3291 Fin15AnchoredAtom3375
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

theorem fin15Anchored_clause31659 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom2864 chi ∧
      ¬Fin15AnchoredAtom2868 chi ∧
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
  refine ⟨{1, 2, 3, 4, 5, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05694
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2822 Fin15AnchoredAtom2826 Fin15AnchoredAtom2827
    Fin15AnchoredAtom2829 Fin15AnchoredAtom2835 Fin15AnchoredAtom2836 Fin15AnchoredAtom2838
    Fin15AnchoredAtom2862 Fin15AnchoredAtom2864 Fin15AnchoredAtom2868 Fin15AnchoredAtom2880
    Fin15AnchoredAtom2881 Fin15AnchoredAtom2883 Fin15AnchoredAtom2907 Fin15AnchoredAtom2909
    Fin15AnchoredAtom2913 Fin15AnchoredAtom2943 Fin15AnchoredAtom2945 Fin15AnchoredAtom2949
    Fin15AnchoredAtom3023 Fin15AnchoredAtom3045 Fin15AnchoredAtom3046 Fin15AnchoredAtom3048
    Fin15AnchoredAtom3072 Fin15AnchoredAtom3074 Fin15AnchoredAtom3078 Fin15AnchoredAtom3108
    Fin15AnchoredAtom3110 Fin15AnchoredAtom3114 Fin15AnchoredAtom3188 Fin15AnchoredAtom3228
    Fin15AnchoredAtom3230 Fin15AnchoredAtom3234 Fin15AnchoredAtom3308 Fin15AnchoredAtom3392
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

theorem fin15Anchored_clause31660 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom2865 chi ∧
      ¬Fin15AnchoredAtom2869 chi ∧
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
  refine ⟨{1, 2, 3, 4, 5, 9, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09790
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2822 Fin15AnchoredAtom2826 Fin15AnchoredAtom2827
    Fin15AnchoredAtom2830 Fin15AnchoredAtom2835 Fin15AnchoredAtom2836 Fin15AnchoredAtom2839
    Fin15AnchoredAtom2862 Fin15AnchoredAtom2865 Fin15AnchoredAtom2869 Fin15AnchoredAtom2880
    Fin15AnchoredAtom2881 Fin15AnchoredAtom2884 Fin15AnchoredAtom2907 Fin15AnchoredAtom2910
    Fin15AnchoredAtom2914 Fin15AnchoredAtom2943 Fin15AnchoredAtom2946 Fin15AnchoredAtom2950
    Fin15AnchoredAtom3024 Fin15AnchoredAtom3045 Fin15AnchoredAtom3046 Fin15AnchoredAtom3049
    Fin15AnchoredAtom3072 Fin15AnchoredAtom3075 Fin15AnchoredAtom3079 Fin15AnchoredAtom3108
    Fin15AnchoredAtom3111 Fin15AnchoredAtom3115 Fin15AnchoredAtom3189 Fin15AnchoredAtom3228
    Fin15AnchoredAtom3231 Fin15AnchoredAtom3235 Fin15AnchoredAtom3309 Fin15AnchoredAtom3393
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

theorem fin15Anchored_clause31661 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom2866 chi ∧
      ¬Fin15AnchoredAtom2870 chi ∧
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
  refine ⟨{1, 2, 3, 4, 5, 9, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17982
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2822 Fin15AnchoredAtom2826 Fin15AnchoredAtom2827
    Fin15AnchoredAtom2831 Fin15AnchoredAtom2835 Fin15AnchoredAtom2836 Fin15AnchoredAtom2840
    Fin15AnchoredAtom2862 Fin15AnchoredAtom2866 Fin15AnchoredAtom2870 Fin15AnchoredAtom2880
    Fin15AnchoredAtom2881 Fin15AnchoredAtom2885 Fin15AnchoredAtom2907 Fin15AnchoredAtom2911
    Fin15AnchoredAtom2915 Fin15AnchoredAtom2943 Fin15AnchoredAtom2947 Fin15AnchoredAtom2951
    Fin15AnchoredAtom3025 Fin15AnchoredAtom3045 Fin15AnchoredAtom3046 Fin15AnchoredAtom3050
    Fin15AnchoredAtom3072 Fin15AnchoredAtom3076 Fin15AnchoredAtom3080 Fin15AnchoredAtom3108
    Fin15AnchoredAtom3112 Fin15AnchoredAtom3116 Fin15AnchoredAtom3190 Fin15AnchoredAtom3228
    Fin15AnchoredAtom3232 Fin15AnchoredAtom3236 Fin15AnchoredAtom3310 Fin15AnchoredAtom3394
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

theorem fin15Anchored_clause31662 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom2864 chi ∧
      ¬Fin15AnchoredAtom2865 chi ∧
      ¬Fin15AnchoredAtom2874 chi ∧
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
  refine ⟨{1, 2, 3, 4, 5, 9, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask12862
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2822 Fin15AnchoredAtom2826 Fin15AnchoredAtom2829
    Fin15AnchoredAtom2830 Fin15AnchoredAtom2835 Fin15AnchoredAtom2838 Fin15AnchoredAtom2839
    Fin15AnchoredAtom2864 Fin15AnchoredAtom2865 Fin15AnchoredAtom2874 Fin15AnchoredAtom2880
    Fin15AnchoredAtom2883 Fin15AnchoredAtom2884 Fin15AnchoredAtom2909 Fin15AnchoredAtom2910
    Fin15AnchoredAtom2919 Fin15AnchoredAtom2945 Fin15AnchoredAtom2946 Fin15AnchoredAtom2955
    Fin15AnchoredAtom3029 Fin15AnchoredAtom3045 Fin15AnchoredAtom3048 Fin15AnchoredAtom3049
    Fin15AnchoredAtom3074 Fin15AnchoredAtom3075 Fin15AnchoredAtom3084 Fin15AnchoredAtom3110
    Fin15AnchoredAtom3111 Fin15AnchoredAtom3120 Fin15AnchoredAtom3194 Fin15AnchoredAtom3230
    Fin15AnchoredAtom3231 Fin15AnchoredAtom3240 Fin15AnchoredAtom3314 Fin15AnchoredAtom3398
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

theorem fin15Anchored_clause31663 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom2864 chi ∧
      ¬Fin15AnchoredAtom2866 chi ∧
      ¬Fin15AnchoredAtom2875 chi ∧
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
  refine ⟨{1, 2, 3, 4, 5, 9, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21054
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2822 Fin15AnchoredAtom2826 Fin15AnchoredAtom2829
    Fin15AnchoredAtom2831 Fin15AnchoredAtom2835 Fin15AnchoredAtom2838 Fin15AnchoredAtom2840
    Fin15AnchoredAtom2864 Fin15AnchoredAtom2866 Fin15AnchoredAtom2875 Fin15AnchoredAtom2880
    Fin15AnchoredAtom2883 Fin15AnchoredAtom2885 Fin15AnchoredAtom2909 Fin15AnchoredAtom2911
    Fin15AnchoredAtom2920 Fin15AnchoredAtom2945 Fin15AnchoredAtom2947 Fin15AnchoredAtom2956
    Fin15AnchoredAtom3030 Fin15AnchoredAtom3045 Fin15AnchoredAtom3048 Fin15AnchoredAtom3050
    Fin15AnchoredAtom3074 Fin15AnchoredAtom3076 Fin15AnchoredAtom3085 Fin15AnchoredAtom3110
    Fin15AnchoredAtom3112 Fin15AnchoredAtom3121 Fin15AnchoredAtom3195 Fin15AnchoredAtom3230
    Fin15AnchoredAtom3232 Fin15AnchoredAtom3241 Fin15AnchoredAtom3315 Fin15AnchoredAtom3399
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

theorem fin15Anchored_clause31664 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom2865 chi ∧
      ¬Fin15AnchoredAtom2866 chi ∧
      ¬Fin15AnchoredAtom2876 chi ∧
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
  refine ⟨{1, 2, 3, 4, 5, 9, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25150
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2822 Fin15AnchoredAtom2826 Fin15AnchoredAtom2830
    Fin15AnchoredAtom2831 Fin15AnchoredAtom2835 Fin15AnchoredAtom2839 Fin15AnchoredAtom2840
    Fin15AnchoredAtom2865 Fin15AnchoredAtom2866 Fin15AnchoredAtom2876 Fin15AnchoredAtom2880
    Fin15AnchoredAtom2884 Fin15AnchoredAtom2885 Fin15AnchoredAtom2910 Fin15AnchoredAtom2911
    Fin15AnchoredAtom2921 Fin15AnchoredAtom2946 Fin15AnchoredAtom2947 Fin15AnchoredAtom2957
    Fin15AnchoredAtom3031 Fin15AnchoredAtom3045 Fin15AnchoredAtom3049 Fin15AnchoredAtom3050
    Fin15AnchoredAtom3075 Fin15AnchoredAtom3076 Fin15AnchoredAtom3086 Fin15AnchoredAtom3111
    Fin15AnchoredAtom3112 Fin15AnchoredAtom3122 Fin15AnchoredAtom3196 Fin15AnchoredAtom3231
    Fin15AnchoredAtom3232 Fin15AnchoredAtom3242 Fin15AnchoredAtom3316 Fin15AnchoredAtom3400
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

theorem fin15Anchored_clause31665 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom2868 chi ∧
      ¬Fin15AnchoredAtom2869 chi ∧
      ¬Fin15AnchoredAtom2874 chi ∧
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
  refine ⟨{1, 2, 3, 4, 5, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13374
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2822 Fin15AnchoredAtom2827 Fin15AnchoredAtom2829
    Fin15AnchoredAtom2830 Fin15AnchoredAtom2836 Fin15AnchoredAtom2838 Fin15AnchoredAtom2839
    Fin15AnchoredAtom2868 Fin15AnchoredAtom2869 Fin15AnchoredAtom2874 Fin15AnchoredAtom2881
    Fin15AnchoredAtom2883 Fin15AnchoredAtom2884 Fin15AnchoredAtom2913 Fin15AnchoredAtom2914
    Fin15AnchoredAtom2919 Fin15AnchoredAtom2949 Fin15AnchoredAtom2950 Fin15AnchoredAtom2955
    Fin15AnchoredAtom3035 Fin15AnchoredAtom3046 Fin15AnchoredAtom3048 Fin15AnchoredAtom3049
    Fin15AnchoredAtom3078 Fin15AnchoredAtom3079 Fin15AnchoredAtom3084 Fin15AnchoredAtom3114
    Fin15AnchoredAtom3115 Fin15AnchoredAtom3120 Fin15AnchoredAtom3200 Fin15AnchoredAtom3234
    Fin15AnchoredAtom3235 Fin15AnchoredAtom3240 Fin15AnchoredAtom3320 Fin15AnchoredAtom3404
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

theorem fin15Anchored_clause31666 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom2868 chi ∧
      ¬Fin15AnchoredAtom2870 chi ∧
      ¬Fin15AnchoredAtom2875 chi ∧
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
  refine ⟨{1, 2, 3, 4, 5, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21566
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2822 Fin15AnchoredAtom2827 Fin15AnchoredAtom2829
    Fin15AnchoredAtom2831 Fin15AnchoredAtom2836 Fin15AnchoredAtom2838 Fin15AnchoredAtom2840
    Fin15AnchoredAtom2868 Fin15AnchoredAtom2870 Fin15AnchoredAtom2875 Fin15AnchoredAtom2881
    Fin15AnchoredAtom2883 Fin15AnchoredAtom2885 Fin15AnchoredAtom2913 Fin15AnchoredAtom2915
    Fin15AnchoredAtom2920 Fin15AnchoredAtom2949 Fin15AnchoredAtom2951 Fin15AnchoredAtom2956
    Fin15AnchoredAtom3036 Fin15AnchoredAtom3046 Fin15AnchoredAtom3048 Fin15AnchoredAtom3050
    Fin15AnchoredAtom3078 Fin15AnchoredAtom3080 Fin15AnchoredAtom3085 Fin15AnchoredAtom3114
    Fin15AnchoredAtom3116 Fin15AnchoredAtom3121 Fin15AnchoredAtom3201 Fin15AnchoredAtom3234
    Fin15AnchoredAtom3236 Fin15AnchoredAtom3241 Fin15AnchoredAtom3321 Fin15AnchoredAtom3405
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

theorem fin15Anchored_clause31667 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom2869 chi ∧
      ¬Fin15AnchoredAtom2870 chi ∧
      ¬Fin15AnchoredAtom2876 chi ∧
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
  refine ⟨{1, 2, 3, 4, 5, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25662
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2822 Fin15AnchoredAtom2827 Fin15AnchoredAtom2830
    Fin15AnchoredAtom2831 Fin15AnchoredAtom2836 Fin15AnchoredAtom2839 Fin15AnchoredAtom2840
    Fin15AnchoredAtom2869 Fin15AnchoredAtom2870 Fin15AnchoredAtom2876 Fin15AnchoredAtom2881
    Fin15AnchoredAtom2884 Fin15AnchoredAtom2885 Fin15AnchoredAtom2914 Fin15AnchoredAtom2915
    Fin15AnchoredAtom2921 Fin15AnchoredAtom2950 Fin15AnchoredAtom2951 Fin15AnchoredAtom2957
    Fin15AnchoredAtom3037 Fin15AnchoredAtom3046 Fin15AnchoredAtom3049 Fin15AnchoredAtom3050
    Fin15AnchoredAtom3079 Fin15AnchoredAtom3080 Fin15AnchoredAtom3086 Fin15AnchoredAtom3115
    Fin15AnchoredAtom3116 Fin15AnchoredAtom3122 Fin15AnchoredAtom3202 Fin15AnchoredAtom3235
    Fin15AnchoredAtom3236 Fin15AnchoredAtom3242 Fin15AnchoredAtom3322 Fin15AnchoredAtom3406
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

theorem fin15Anchored_clause31668 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom2874 chi ∧
      ¬Fin15AnchoredAtom2875 chi ∧
      ¬Fin15AnchoredAtom2876 chi ∧
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
  refine ⟨{1, 2, 3, 4, 5, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask28734
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2822 Fin15AnchoredAtom2829 Fin15AnchoredAtom2830
    Fin15AnchoredAtom2831 Fin15AnchoredAtom2838 Fin15AnchoredAtom2839 Fin15AnchoredAtom2840
    Fin15AnchoredAtom2874 Fin15AnchoredAtom2875 Fin15AnchoredAtom2876 Fin15AnchoredAtom2883
    Fin15AnchoredAtom2884 Fin15AnchoredAtom2885 Fin15AnchoredAtom2919 Fin15AnchoredAtom2920
    Fin15AnchoredAtom2921 Fin15AnchoredAtom2955 Fin15AnchoredAtom2956 Fin15AnchoredAtom2957
    Fin15AnchoredAtom3041 Fin15AnchoredAtom3048 Fin15AnchoredAtom3049 Fin15AnchoredAtom3050
    Fin15AnchoredAtom3084 Fin15AnchoredAtom3085 Fin15AnchoredAtom3086 Fin15AnchoredAtom3120
    Fin15AnchoredAtom3121 Fin15AnchoredAtom3122 Fin15AnchoredAtom3206 Fin15AnchoredAtom3240
    Fin15AnchoredAtom3241 Fin15AnchoredAtom3242 Fin15AnchoredAtom3326 Fin15AnchoredAtom3410
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

theorem fin15Anchored_clause31669 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2825 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom2842 chi ∧
      ¬Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom2849 chi ∧
      ¬Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom2861 chi ∧
      ¬Fin15AnchoredAtom2886 chi ∧
      ¬Fin15AnchoredAtom2887 chi ∧
      ¬Fin15AnchoredAtom2893 chi ∧
      ¬Fin15AnchoredAtom2894 chi ∧
      ¬Fin15AnchoredAtom2900 chi ∧
      ¬Fin15AnchoredAtom2906 chi ∧
      ¬Fin15AnchoredAtom2958 chi ∧
      ¬Fin15AnchoredAtom2964 chi ∧
      ¬Fin15AnchoredAtom2970 chi ∧
      ¬Fin15AnchoredAtom2991 chi ∧
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
      ¬Fin15AnchoredAtom3546 chi ∧
      ¬Fin15AnchoredAtom3547 chi ∧
      ¬Fin15AnchoredAtom3553 chi ∧
      ¬Fin15AnchoredAtom3554 chi ∧
      ¬Fin15AnchoredAtom3560 chi ∧
      ¬Fin15AnchoredAtom3566 chi ∧
      ¬Fin15AnchoredAtom3618 chi ∧
      ¬Fin15AnchoredAtom3624 chi ∧
      ¬Fin15AnchoredAtom3630 chi ∧
      ¬Fin15AnchoredAtom3651 chi ∧
      ¬Fin15AnchoredAtom3738 chi ∧
      ¬Fin15AnchoredAtom3744 chi ∧
      ¬Fin15AnchoredAtom3750 chi ∧
      ¬Fin15AnchoredAtom3771 chi ∧
      ¬Fin15AnchoredAtom3911 chi ∧
      ¬Fin15AnchoredAtom4068 chi ∧
      ¬Fin15AnchoredAtom4074 chi ∧
      ¬Fin15AnchoredAtom4080 chi ∧
      ¬Fin15AnchoredAtom4101 chi ∧
      ¬Fin15AnchoredAtom4241 chi ∧
      ¬Fin15AnchoredAtom4451 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 3, 4, 6, 7, 8, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask16862
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2823 Fin15AnchoredAtom2824 Fin15AnchoredAtom2825
    Fin15AnchoredAtom2831 Fin15AnchoredAtom2841 Fin15AnchoredAtom2842 Fin15AnchoredAtom2848
    Fin15AnchoredAtom2849 Fin15AnchoredAtom2855 Fin15AnchoredAtom2861 Fin15AnchoredAtom2886
    Fin15AnchoredAtom2887 Fin15AnchoredAtom2893 Fin15AnchoredAtom2894 Fin15AnchoredAtom2900
    Fin15AnchoredAtom2906 Fin15AnchoredAtom2958 Fin15AnchoredAtom2964 Fin15AnchoredAtom2970
    Fin15AnchoredAtom2991 Fin15AnchoredAtom3051 Fin15AnchoredAtom3052 Fin15AnchoredAtom3058
    Fin15AnchoredAtom3059 Fin15AnchoredAtom3065 Fin15AnchoredAtom3071 Fin15AnchoredAtom3123
    Fin15AnchoredAtom3129 Fin15AnchoredAtom3135 Fin15AnchoredAtom3156 Fin15AnchoredAtom3243
    Fin15AnchoredAtom3249 Fin15AnchoredAtom3255 Fin15AnchoredAtom3276 Fin15AnchoredAtom3416
    Fin15AnchoredAtom3546 Fin15AnchoredAtom3547 Fin15AnchoredAtom3553 Fin15AnchoredAtom3554
    Fin15AnchoredAtom3560 Fin15AnchoredAtom3566 Fin15AnchoredAtom3618 Fin15AnchoredAtom3624
    Fin15AnchoredAtom3630 Fin15AnchoredAtom3651 Fin15AnchoredAtom3738 Fin15AnchoredAtom3744
    Fin15AnchoredAtom3750 Fin15AnchoredAtom3771 Fin15AnchoredAtom3911 Fin15AnchoredAtom4068
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

theorem fin15Anchored_clause31670 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom2862 chi ∧
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
  refine ⟨{1, 2, 3, 4, 6, 7, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask01758
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2823 Fin15AnchoredAtom2824 Fin15AnchoredAtom2826
    Fin15AnchoredAtom2827 Fin15AnchoredAtom2841 Fin15AnchoredAtom2843 Fin15AnchoredAtom2844
    Fin15AnchoredAtom2850 Fin15AnchoredAtom2851 Fin15AnchoredAtom2862 Fin15AnchoredAtom2886
    Fin15AnchoredAtom2888 Fin15AnchoredAtom2889 Fin15AnchoredAtom2895 Fin15AnchoredAtom2896
    Fin15AnchoredAtom2907 Fin15AnchoredAtom2959 Fin15AnchoredAtom2960 Fin15AnchoredAtom2971
    Fin15AnchoredAtom2992 Fin15AnchoredAtom3051 Fin15AnchoredAtom3053 Fin15AnchoredAtom3054
    Fin15AnchoredAtom3060 Fin15AnchoredAtom3061 Fin15AnchoredAtom3072 Fin15AnchoredAtom3124
    Fin15AnchoredAtom3125 Fin15AnchoredAtom3136 Fin15AnchoredAtom3157 Fin15AnchoredAtom3244
    Fin15AnchoredAtom3245 Fin15AnchoredAtom3256 Fin15AnchoredAtom3277 Fin15AnchoredAtom3417
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

theorem fin15Anchored_clause31671 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom2864 chi ∧
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
  refine ⟨{1, 2, 3, 4, 6, 7, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask04830
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2823 Fin15AnchoredAtom2824 Fin15AnchoredAtom2826
    Fin15AnchoredAtom2829 Fin15AnchoredAtom2841 Fin15AnchoredAtom2843 Fin15AnchoredAtom2846
    Fin15AnchoredAtom2850 Fin15AnchoredAtom2853 Fin15AnchoredAtom2864 Fin15AnchoredAtom2886
    Fin15AnchoredAtom2888 Fin15AnchoredAtom2891 Fin15AnchoredAtom2895 Fin15AnchoredAtom2898
    Fin15AnchoredAtom2909 Fin15AnchoredAtom2959 Fin15AnchoredAtom2962 Fin15AnchoredAtom2973
    Fin15AnchoredAtom2994 Fin15AnchoredAtom3051 Fin15AnchoredAtom3053 Fin15AnchoredAtom3056
    Fin15AnchoredAtom3060 Fin15AnchoredAtom3063 Fin15AnchoredAtom3074 Fin15AnchoredAtom3124
    Fin15AnchoredAtom3127 Fin15AnchoredAtom3138 Fin15AnchoredAtom3159 Fin15AnchoredAtom3244
    Fin15AnchoredAtom3247 Fin15AnchoredAtom3258 Fin15AnchoredAtom3279 Fin15AnchoredAtom3419
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

theorem fin15Anchored_clause31672 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom2865 chi ∧
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
  refine ⟨{1, 2, 3, 4, 6, 7, 9, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask08926
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2823 Fin15AnchoredAtom2824 Fin15AnchoredAtom2826
    Fin15AnchoredAtom2830 Fin15AnchoredAtom2841 Fin15AnchoredAtom2843 Fin15AnchoredAtom2847
    Fin15AnchoredAtom2850 Fin15AnchoredAtom2854 Fin15AnchoredAtom2865 Fin15AnchoredAtom2886
    Fin15AnchoredAtom2888 Fin15AnchoredAtom2892 Fin15AnchoredAtom2895 Fin15AnchoredAtom2899
    Fin15AnchoredAtom2910 Fin15AnchoredAtom2959 Fin15AnchoredAtom2963 Fin15AnchoredAtom2974
    Fin15AnchoredAtom2995 Fin15AnchoredAtom3051 Fin15AnchoredAtom3053 Fin15AnchoredAtom3057
    Fin15AnchoredAtom3060 Fin15AnchoredAtom3064 Fin15AnchoredAtom3075 Fin15AnchoredAtom3124
    Fin15AnchoredAtom3128 Fin15AnchoredAtom3139 Fin15AnchoredAtom3160 Fin15AnchoredAtom3244
    Fin15AnchoredAtom3248 Fin15AnchoredAtom3259 Fin15AnchoredAtom3280 Fin15AnchoredAtom3420
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

theorem fin15Anchored_clause31673 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom2866 chi ∧
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
  refine ⟨{1, 2, 3, 4, 6, 7, 9, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17118
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2823 Fin15AnchoredAtom2824 Fin15AnchoredAtom2826
    Fin15AnchoredAtom2831 Fin15AnchoredAtom2841 Fin15AnchoredAtom2843 Fin15AnchoredAtom2848
    Fin15AnchoredAtom2850 Fin15AnchoredAtom2855 Fin15AnchoredAtom2866 Fin15AnchoredAtom2886
    Fin15AnchoredAtom2888 Fin15AnchoredAtom2893 Fin15AnchoredAtom2895 Fin15AnchoredAtom2900
    Fin15AnchoredAtom2911 Fin15AnchoredAtom2959 Fin15AnchoredAtom2964 Fin15AnchoredAtom2975
    Fin15AnchoredAtom2996 Fin15AnchoredAtom3051 Fin15AnchoredAtom3053 Fin15AnchoredAtom3058
    Fin15AnchoredAtom3060 Fin15AnchoredAtom3065 Fin15AnchoredAtom3076 Fin15AnchoredAtom3124
    Fin15AnchoredAtom3129 Fin15AnchoredAtom3140 Fin15AnchoredAtom3161 Fin15AnchoredAtom3244
    Fin15AnchoredAtom3249 Fin15AnchoredAtom3260 Fin15AnchoredAtom3281 Fin15AnchoredAtom3421
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

theorem fin15Anchored_clause31674 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom2868 chi ∧
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
  refine ⟨{1, 2, 3, 4, 6, 7, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05342
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2823 Fin15AnchoredAtom2824 Fin15AnchoredAtom2827
    Fin15AnchoredAtom2829 Fin15AnchoredAtom2841 Fin15AnchoredAtom2844 Fin15AnchoredAtom2846
    Fin15AnchoredAtom2851 Fin15AnchoredAtom2853 Fin15AnchoredAtom2868 Fin15AnchoredAtom2886
    Fin15AnchoredAtom2889 Fin15AnchoredAtom2891 Fin15AnchoredAtom2896 Fin15AnchoredAtom2898
    Fin15AnchoredAtom2913 Fin15AnchoredAtom2960 Fin15AnchoredAtom2962 Fin15AnchoredAtom2977
    Fin15AnchoredAtom2998 Fin15AnchoredAtom3051 Fin15AnchoredAtom3054 Fin15AnchoredAtom3056
    Fin15AnchoredAtom3061 Fin15AnchoredAtom3063 Fin15AnchoredAtom3078 Fin15AnchoredAtom3125
    Fin15AnchoredAtom3127 Fin15AnchoredAtom3142 Fin15AnchoredAtom3163 Fin15AnchoredAtom3245
    Fin15AnchoredAtom3247 Fin15AnchoredAtom3262 Fin15AnchoredAtom3283 Fin15AnchoredAtom3423
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

theorem fin15Anchored_clause31675 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom2869 chi ∧
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
  refine ⟨{1, 2, 3, 4, 6, 7, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09438
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2823 Fin15AnchoredAtom2824 Fin15AnchoredAtom2827
    Fin15AnchoredAtom2830 Fin15AnchoredAtom2841 Fin15AnchoredAtom2844 Fin15AnchoredAtom2847
    Fin15AnchoredAtom2851 Fin15AnchoredAtom2854 Fin15AnchoredAtom2869 Fin15AnchoredAtom2886
    Fin15AnchoredAtom2889 Fin15AnchoredAtom2892 Fin15AnchoredAtom2896 Fin15AnchoredAtom2899
    Fin15AnchoredAtom2914 Fin15AnchoredAtom2960 Fin15AnchoredAtom2963 Fin15AnchoredAtom2978
    Fin15AnchoredAtom2999 Fin15AnchoredAtom3051 Fin15AnchoredAtom3054 Fin15AnchoredAtom3057
    Fin15AnchoredAtom3061 Fin15AnchoredAtom3064 Fin15AnchoredAtom3079 Fin15AnchoredAtom3125
    Fin15AnchoredAtom3128 Fin15AnchoredAtom3143 Fin15AnchoredAtom3164 Fin15AnchoredAtom3245
    Fin15AnchoredAtom3248 Fin15AnchoredAtom3263 Fin15AnchoredAtom3284 Fin15AnchoredAtom3424
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

theorem fin15Anchored_clause31676 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom2870 chi ∧
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
  refine ⟨{1, 2, 3, 4, 6, 7, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17630
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2823 Fin15AnchoredAtom2824 Fin15AnchoredAtom2827
    Fin15AnchoredAtom2831 Fin15AnchoredAtom2841 Fin15AnchoredAtom2844 Fin15AnchoredAtom2848
    Fin15AnchoredAtom2851 Fin15AnchoredAtom2855 Fin15AnchoredAtom2870 Fin15AnchoredAtom2886
    Fin15AnchoredAtom2889 Fin15AnchoredAtom2893 Fin15AnchoredAtom2896 Fin15AnchoredAtom2900
    Fin15AnchoredAtom2915 Fin15AnchoredAtom2960 Fin15AnchoredAtom2964 Fin15AnchoredAtom2979
    Fin15AnchoredAtom3000 Fin15AnchoredAtom3051 Fin15AnchoredAtom3054 Fin15AnchoredAtom3058
    Fin15AnchoredAtom3061 Fin15AnchoredAtom3065 Fin15AnchoredAtom3080 Fin15AnchoredAtom3125
    Fin15AnchoredAtom3129 Fin15AnchoredAtom3144 Fin15AnchoredAtom3165 Fin15AnchoredAtom3245
    Fin15AnchoredAtom3249 Fin15AnchoredAtom3264 Fin15AnchoredAtom3285 Fin15AnchoredAtom3425
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

theorem fin15Anchored_clause31677 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom2874 chi ∧
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
  refine ⟨{1, 2, 3, 4, 6, 7, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask12510
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2823 Fin15AnchoredAtom2824 Fin15AnchoredAtom2829
    Fin15AnchoredAtom2830 Fin15AnchoredAtom2841 Fin15AnchoredAtom2846 Fin15AnchoredAtom2847
    Fin15AnchoredAtom2853 Fin15AnchoredAtom2854 Fin15AnchoredAtom2874 Fin15AnchoredAtom2886
    Fin15AnchoredAtom2891 Fin15AnchoredAtom2892 Fin15AnchoredAtom2898 Fin15AnchoredAtom2899
    Fin15AnchoredAtom2919 Fin15AnchoredAtom2962 Fin15AnchoredAtom2963 Fin15AnchoredAtom2983
    Fin15AnchoredAtom3004 Fin15AnchoredAtom3051 Fin15AnchoredAtom3056 Fin15AnchoredAtom3057
    Fin15AnchoredAtom3063 Fin15AnchoredAtom3064 Fin15AnchoredAtom3084 Fin15AnchoredAtom3127
    Fin15AnchoredAtom3128 Fin15AnchoredAtom3148 Fin15AnchoredAtom3169 Fin15AnchoredAtom3247
    Fin15AnchoredAtom3248 Fin15AnchoredAtom3268 Fin15AnchoredAtom3289 Fin15AnchoredAtom3429
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

theorem fin15Anchored_clause31678 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom2875 chi ∧
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
  refine ⟨{1, 2, 3, 4, 6, 7, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask20702
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2823 Fin15AnchoredAtom2824 Fin15AnchoredAtom2829
    Fin15AnchoredAtom2831 Fin15AnchoredAtom2841 Fin15AnchoredAtom2846 Fin15AnchoredAtom2848
    Fin15AnchoredAtom2853 Fin15AnchoredAtom2855 Fin15AnchoredAtom2875 Fin15AnchoredAtom2886
    Fin15AnchoredAtom2891 Fin15AnchoredAtom2893 Fin15AnchoredAtom2898 Fin15AnchoredAtom2900
    Fin15AnchoredAtom2920 Fin15AnchoredAtom2962 Fin15AnchoredAtom2964 Fin15AnchoredAtom2984
    Fin15AnchoredAtom3005 Fin15AnchoredAtom3051 Fin15AnchoredAtom3056 Fin15AnchoredAtom3058
    Fin15AnchoredAtom3063 Fin15AnchoredAtom3065 Fin15AnchoredAtom3085 Fin15AnchoredAtom3127
    Fin15AnchoredAtom3129 Fin15AnchoredAtom3149 Fin15AnchoredAtom3170 Fin15AnchoredAtom3247
    Fin15AnchoredAtom3249 Fin15AnchoredAtom3269 Fin15AnchoredAtom3290 Fin15AnchoredAtom3430
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

theorem fin15Anchored_clause31679 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom2876 chi ∧
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
  refine ⟨{1, 2, 3, 4, 6, 7, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask24798
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2823 Fin15AnchoredAtom2824 Fin15AnchoredAtom2830
    Fin15AnchoredAtom2831 Fin15AnchoredAtom2841 Fin15AnchoredAtom2847 Fin15AnchoredAtom2848
    Fin15AnchoredAtom2854 Fin15AnchoredAtom2855 Fin15AnchoredAtom2876 Fin15AnchoredAtom2886
    Fin15AnchoredAtom2892 Fin15AnchoredAtom2893 Fin15AnchoredAtom2899 Fin15AnchoredAtom2900
    Fin15AnchoredAtom2921 Fin15AnchoredAtom2963 Fin15AnchoredAtom2964 Fin15AnchoredAtom2985
    Fin15AnchoredAtom3006 Fin15AnchoredAtom3051 Fin15AnchoredAtom3057 Fin15AnchoredAtom3058
    Fin15AnchoredAtom3064 Fin15AnchoredAtom3065 Fin15AnchoredAtom3086 Fin15AnchoredAtom3128
    Fin15AnchoredAtom3129 Fin15AnchoredAtom3150 Fin15AnchoredAtom3171 Fin15AnchoredAtom3248
    Fin15AnchoredAtom3249 Fin15AnchoredAtom3270 Fin15AnchoredAtom3291 Fin15AnchoredAtom3431
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

theorem fin15Anchored_clause31680 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom2864 chi ∧
      ¬Fin15AnchoredAtom2868 chi ∧
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
  refine ⟨{1, 2, 3, 4, 6, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05726
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2823 Fin15AnchoredAtom2826 Fin15AnchoredAtom2827
    Fin15AnchoredAtom2829 Fin15AnchoredAtom2843 Fin15AnchoredAtom2844 Fin15AnchoredAtom2846
    Fin15AnchoredAtom2862 Fin15AnchoredAtom2864 Fin15AnchoredAtom2868 Fin15AnchoredAtom2888
    Fin15AnchoredAtom2889 Fin15AnchoredAtom2891 Fin15AnchoredAtom2907 Fin15AnchoredAtom2909
    Fin15AnchoredAtom2913 Fin15AnchoredAtom2971 Fin15AnchoredAtom2973 Fin15AnchoredAtom2977
    Fin15AnchoredAtom3023 Fin15AnchoredAtom3053 Fin15AnchoredAtom3054 Fin15AnchoredAtom3056
    Fin15AnchoredAtom3072 Fin15AnchoredAtom3074 Fin15AnchoredAtom3078 Fin15AnchoredAtom3136
    Fin15AnchoredAtom3138 Fin15AnchoredAtom3142 Fin15AnchoredAtom3188 Fin15AnchoredAtom3256
    Fin15AnchoredAtom3258 Fin15AnchoredAtom3262 Fin15AnchoredAtom3308 Fin15AnchoredAtom3448
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

theorem fin15Anchored_clause31681 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom2865 chi ∧
      ¬Fin15AnchoredAtom2869 chi ∧
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
  refine ⟨{1, 2, 3, 4, 6, 9, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09822
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2823 Fin15AnchoredAtom2826 Fin15AnchoredAtom2827
    Fin15AnchoredAtom2830 Fin15AnchoredAtom2843 Fin15AnchoredAtom2844 Fin15AnchoredAtom2847
    Fin15AnchoredAtom2862 Fin15AnchoredAtom2865 Fin15AnchoredAtom2869 Fin15AnchoredAtom2888
    Fin15AnchoredAtom2889 Fin15AnchoredAtom2892 Fin15AnchoredAtom2907 Fin15AnchoredAtom2910
    Fin15AnchoredAtom2914 Fin15AnchoredAtom2971 Fin15AnchoredAtom2974 Fin15AnchoredAtom2978
    Fin15AnchoredAtom3024 Fin15AnchoredAtom3053 Fin15AnchoredAtom3054 Fin15AnchoredAtom3057
    Fin15AnchoredAtom3072 Fin15AnchoredAtom3075 Fin15AnchoredAtom3079 Fin15AnchoredAtom3136
    Fin15AnchoredAtom3139 Fin15AnchoredAtom3143 Fin15AnchoredAtom3189 Fin15AnchoredAtom3256
    Fin15AnchoredAtom3259 Fin15AnchoredAtom3263 Fin15AnchoredAtom3309 Fin15AnchoredAtom3449
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

theorem fin15Anchored_clause31682 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom2866 chi ∧
      ¬Fin15AnchoredAtom2870 chi ∧
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
  refine ⟨{1, 2, 3, 4, 6, 9, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask18014
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2823 Fin15AnchoredAtom2826 Fin15AnchoredAtom2827
    Fin15AnchoredAtom2831 Fin15AnchoredAtom2843 Fin15AnchoredAtom2844 Fin15AnchoredAtom2848
    Fin15AnchoredAtom2862 Fin15AnchoredAtom2866 Fin15AnchoredAtom2870 Fin15AnchoredAtom2888
    Fin15AnchoredAtom2889 Fin15AnchoredAtom2893 Fin15AnchoredAtom2907 Fin15AnchoredAtom2911
    Fin15AnchoredAtom2915 Fin15AnchoredAtom2971 Fin15AnchoredAtom2975 Fin15AnchoredAtom2979
    Fin15AnchoredAtom3025 Fin15AnchoredAtom3053 Fin15AnchoredAtom3054 Fin15AnchoredAtom3058
    Fin15AnchoredAtom3072 Fin15AnchoredAtom3076 Fin15AnchoredAtom3080 Fin15AnchoredAtom3136
    Fin15AnchoredAtom3140 Fin15AnchoredAtom3144 Fin15AnchoredAtom3190 Fin15AnchoredAtom3256
    Fin15AnchoredAtom3260 Fin15AnchoredAtom3264 Fin15AnchoredAtom3310 Fin15AnchoredAtom3450
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

theorem fin15Anchored_clause31683 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom2864 chi ∧
      ¬Fin15AnchoredAtom2865 chi ∧
      ¬Fin15AnchoredAtom2874 chi ∧
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
  refine ⟨{1, 2, 3, 4, 6, 9, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask12894
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2823 Fin15AnchoredAtom2826 Fin15AnchoredAtom2829
    Fin15AnchoredAtom2830 Fin15AnchoredAtom2843 Fin15AnchoredAtom2846 Fin15AnchoredAtom2847
    Fin15AnchoredAtom2864 Fin15AnchoredAtom2865 Fin15AnchoredAtom2874 Fin15AnchoredAtom2888
    Fin15AnchoredAtom2891 Fin15AnchoredAtom2892 Fin15AnchoredAtom2909 Fin15AnchoredAtom2910
    Fin15AnchoredAtom2919 Fin15AnchoredAtom2973 Fin15AnchoredAtom2974 Fin15AnchoredAtom2983
    Fin15AnchoredAtom3029 Fin15AnchoredAtom3053 Fin15AnchoredAtom3056 Fin15AnchoredAtom3057
    Fin15AnchoredAtom3074 Fin15AnchoredAtom3075 Fin15AnchoredAtom3084 Fin15AnchoredAtom3138
    Fin15AnchoredAtom3139 Fin15AnchoredAtom3148 Fin15AnchoredAtom3194 Fin15AnchoredAtom3258
    Fin15AnchoredAtom3259 Fin15AnchoredAtom3268 Fin15AnchoredAtom3314 Fin15AnchoredAtom3454
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

theorem fin15Anchored_clause31684 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom2864 chi ∧
      ¬Fin15AnchoredAtom2866 chi ∧
      ¬Fin15AnchoredAtom2875 chi ∧
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
  refine ⟨{1, 2, 3, 4, 6, 9, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21086
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2823 Fin15AnchoredAtom2826 Fin15AnchoredAtom2829
    Fin15AnchoredAtom2831 Fin15AnchoredAtom2843 Fin15AnchoredAtom2846 Fin15AnchoredAtom2848
    Fin15AnchoredAtom2864 Fin15AnchoredAtom2866 Fin15AnchoredAtom2875 Fin15AnchoredAtom2888
    Fin15AnchoredAtom2891 Fin15AnchoredAtom2893 Fin15AnchoredAtom2909 Fin15AnchoredAtom2911
    Fin15AnchoredAtom2920 Fin15AnchoredAtom2973 Fin15AnchoredAtom2975 Fin15AnchoredAtom2984
    Fin15AnchoredAtom3030 Fin15AnchoredAtom3053 Fin15AnchoredAtom3056 Fin15AnchoredAtom3058
    Fin15AnchoredAtom3074 Fin15AnchoredAtom3076 Fin15AnchoredAtom3085 Fin15AnchoredAtom3138
    Fin15AnchoredAtom3140 Fin15AnchoredAtom3149 Fin15AnchoredAtom3195 Fin15AnchoredAtom3258
    Fin15AnchoredAtom3260 Fin15AnchoredAtom3269 Fin15AnchoredAtom3315 Fin15AnchoredAtom3455
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

theorem fin15Anchored_clause31685 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom2865 chi ∧
      ¬Fin15AnchoredAtom2866 chi ∧
      ¬Fin15AnchoredAtom2876 chi ∧
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
  refine ⟨{1, 2, 3, 4, 6, 9, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25182
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2823 Fin15AnchoredAtom2826 Fin15AnchoredAtom2830
    Fin15AnchoredAtom2831 Fin15AnchoredAtom2843 Fin15AnchoredAtom2847 Fin15AnchoredAtom2848
    Fin15AnchoredAtom2865 Fin15AnchoredAtom2866 Fin15AnchoredAtom2876 Fin15AnchoredAtom2888
    Fin15AnchoredAtom2892 Fin15AnchoredAtom2893 Fin15AnchoredAtom2910 Fin15AnchoredAtom2911
    Fin15AnchoredAtom2921 Fin15AnchoredAtom2974 Fin15AnchoredAtom2975 Fin15AnchoredAtom2985
    Fin15AnchoredAtom3031 Fin15AnchoredAtom3053 Fin15AnchoredAtom3057 Fin15AnchoredAtom3058
    Fin15AnchoredAtom3075 Fin15AnchoredAtom3076 Fin15AnchoredAtom3086 Fin15AnchoredAtom3139
    Fin15AnchoredAtom3140 Fin15AnchoredAtom3150 Fin15AnchoredAtom3196 Fin15AnchoredAtom3259
    Fin15AnchoredAtom3260 Fin15AnchoredAtom3270 Fin15AnchoredAtom3316 Fin15AnchoredAtom3456
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

theorem fin15Anchored_clause31686 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom2868 chi ∧
      ¬Fin15AnchoredAtom2869 chi ∧
      ¬Fin15AnchoredAtom2874 chi ∧
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
  refine ⟨{1, 2, 3, 4, 6, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13406
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2823 Fin15AnchoredAtom2827 Fin15AnchoredAtom2829
    Fin15AnchoredAtom2830 Fin15AnchoredAtom2844 Fin15AnchoredAtom2846 Fin15AnchoredAtom2847
    Fin15AnchoredAtom2868 Fin15AnchoredAtom2869 Fin15AnchoredAtom2874 Fin15AnchoredAtom2889
    Fin15AnchoredAtom2891 Fin15AnchoredAtom2892 Fin15AnchoredAtom2913 Fin15AnchoredAtom2914
    Fin15AnchoredAtom2919 Fin15AnchoredAtom2977 Fin15AnchoredAtom2978 Fin15AnchoredAtom2983
    Fin15AnchoredAtom3035 Fin15AnchoredAtom3054 Fin15AnchoredAtom3056 Fin15AnchoredAtom3057
    Fin15AnchoredAtom3078 Fin15AnchoredAtom3079 Fin15AnchoredAtom3084 Fin15AnchoredAtom3142
    Fin15AnchoredAtom3143 Fin15AnchoredAtom3148 Fin15AnchoredAtom3200 Fin15AnchoredAtom3262
    Fin15AnchoredAtom3263 Fin15AnchoredAtom3268 Fin15AnchoredAtom3320 Fin15AnchoredAtom3460
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

theorem fin15Anchored_clause31687 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom2868 chi ∧
      ¬Fin15AnchoredAtom2870 chi ∧
      ¬Fin15AnchoredAtom2875 chi ∧
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
  refine ⟨{1, 2, 3, 4, 6, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21598
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2823 Fin15AnchoredAtom2827 Fin15AnchoredAtom2829
    Fin15AnchoredAtom2831 Fin15AnchoredAtom2844 Fin15AnchoredAtom2846 Fin15AnchoredAtom2848
    Fin15AnchoredAtom2868 Fin15AnchoredAtom2870 Fin15AnchoredAtom2875 Fin15AnchoredAtom2889
    Fin15AnchoredAtom2891 Fin15AnchoredAtom2893 Fin15AnchoredAtom2913 Fin15AnchoredAtom2915
    Fin15AnchoredAtom2920 Fin15AnchoredAtom2977 Fin15AnchoredAtom2979 Fin15AnchoredAtom2984
    Fin15AnchoredAtom3036 Fin15AnchoredAtom3054 Fin15AnchoredAtom3056 Fin15AnchoredAtom3058
    Fin15AnchoredAtom3078 Fin15AnchoredAtom3080 Fin15AnchoredAtom3085 Fin15AnchoredAtom3142
    Fin15AnchoredAtom3144 Fin15AnchoredAtom3149 Fin15AnchoredAtom3201 Fin15AnchoredAtom3262
    Fin15AnchoredAtom3264 Fin15AnchoredAtom3269 Fin15AnchoredAtom3321 Fin15AnchoredAtom3461
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

theorem fin15Anchored_clause31688 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom2869 chi ∧
      ¬Fin15AnchoredAtom2870 chi ∧
      ¬Fin15AnchoredAtom2876 chi ∧
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
  refine ⟨{1, 2, 3, 4, 6, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25694
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2823 Fin15AnchoredAtom2827 Fin15AnchoredAtom2830
    Fin15AnchoredAtom2831 Fin15AnchoredAtom2844 Fin15AnchoredAtom2847 Fin15AnchoredAtom2848
    Fin15AnchoredAtom2869 Fin15AnchoredAtom2870 Fin15AnchoredAtom2876 Fin15AnchoredAtom2889
    Fin15AnchoredAtom2892 Fin15AnchoredAtom2893 Fin15AnchoredAtom2914 Fin15AnchoredAtom2915
    Fin15AnchoredAtom2921 Fin15AnchoredAtom2978 Fin15AnchoredAtom2979 Fin15AnchoredAtom2985
    Fin15AnchoredAtom3037 Fin15AnchoredAtom3054 Fin15AnchoredAtom3057 Fin15AnchoredAtom3058
    Fin15AnchoredAtom3079 Fin15AnchoredAtom3080 Fin15AnchoredAtom3086 Fin15AnchoredAtom3143
    Fin15AnchoredAtom3144 Fin15AnchoredAtom3150 Fin15AnchoredAtom3202 Fin15AnchoredAtom3263
    Fin15AnchoredAtom3264 Fin15AnchoredAtom3270 Fin15AnchoredAtom3322 Fin15AnchoredAtom3462
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

theorem fin15Anchored_clause31689 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom2874 chi ∧
      ¬Fin15AnchoredAtom2875 chi ∧
      ¬Fin15AnchoredAtom2876 chi ∧
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
  refine ⟨{1, 2, 3, 4, 6, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask28766
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2823 Fin15AnchoredAtom2829 Fin15AnchoredAtom2830
    Fin15AnchoredAtom2831 Fin15AnchoredAtom2846 Fin15AnchoredAtom2847 Fin15AnchoredAtom2848
    Fin15AnchoredAtom2874 Fin15AnchoredAtom2875 Fin15AnchoredAtom2876 Fin15AnchoredAtom2891
    Fin15AnchoredAtom2892 Fin15AnchoredAtom2893 Fin15AnchoredAtom2919 Fin15AnchoredAtom2920
    Fin15AnchoredAtom2921 Fin15AnchoredAtom2983 Fin15AnchoredAtom2984 Fin15AnchoredAtom2985
    Fin15AnchoredAtom3041 Fin15AnchoredAtom3056 Fin15AnchoredAtom3057 Fin15AnchoredAtom3058
    Fin15AnchoredAtom3084 Fin15AnchoredAtom3085 Fin15AnchoredAtom3086 Fin15AnchoredAtom3148
    Fin15AnchoredAtom3149 Fin15AnchoredAtom3150 Fin15AnchoredAtom3206 Fin15AnchoredAtom3268
    Fin15AnchoredAtom3269 Fin15AnchoredAtom3270 Fin15AnchoredAtom3326 Fin15AnchoredAtom3466
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

theorem fin15Anchored_clause31690 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom2864 chi ∧
      ¬Fin15AnchoredAtom2868 chi ∧
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
  refine ⟨{1, 2, 3, 4, 7, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05790
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2824 Fin15AnchoredAtom2826 Fin15AnchoredAtom2827
    Fin15AnchoredAtom2829 Fin15AnchoredAtom2850 Fin15AnchoredAtom2851 Fin15AnchoredAtom2853
    Fin15AnchoredAtom2862 Fin15AnchoredAtom2864 Fin15AnchoredAtom2868 Fin15AnchoredAtom2895
    Fin15AnchoredAtom2896 Fin15AnchoredAtom2898 Fin15AnchoredAtom2907 Fin15AnchoredAtom2909
    Fin15AnchoredAtom2913 Fin15AnchoredAtom2992 Fin15AnchoredAtom2994 Fin15AnchoredAtom2998
    Fin15AnchoredAtom3023 Fin15AnchoredAtom3060 Fin15AnchoredAtom3061 Fin15AnchoredAtom3063
    Fin15AnchoredAtom3072 Fin15AnchoredAtom3074 Fin15AnchoredAtom3078 Fin15AnchoredAtom3157
    Fin15AnchoredAtom3159 Fin15AnchoredAtom3163 Fin15AnchoredAtom3188 Fin15AnchoredAtom3277
    Fin15AnchoredAtom3279 Fin15AnchoredAtom3283 Fin15AnchoredAtom3308 Fin15AnchoredAtom3483
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

theorem fin15Anchored_clause31691 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom2865 chi ∧
      ¬Fin15AnchoredAtom2869 chi ∧
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
  refine ⟨{1, 2, 3, 4, 7, 9, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09886
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2824 Fin15AnchoredAtom2826 Fin15AnchoredAtom2827
    Fin15AnchoredAtom2830 Fin15AnchoredAtom2850 Fin15AnchoredAtom2851 Fin15AnchoredAtom2854
    Fin15AnchoredAtom2862 Fin15AnchoredAtom2865 Fin15AnchoredAtom2869 Fin15AnchoredAtom2895
    Fin15AnchoredAtom2896 Fin15AnchoredAtom2899 Fin15AnchoredAtom2907 Fin15AnchoredAtom2910
    Fin15AnchoredAtom2914 Fin15AnchoredAtom2992 Fin15AnchoredAtom2995 Fin15AnchoredAtom2999
    Fin15AnchoredAtom3024 Fin15AnchoredAtom3060 Fin15AnchoredAtom3061 Fin15AnchoredAtom3064
    Fin15AnchoredAtom3072 Fin15AnchoredAtom3075 Fin15AnchoredAtom3079 Fin15AnchoredAtom3157
    Fin15AnchoredAtom3160 Fin15AnchoredAtom3164 Fin15AnchoredAtom3189 Fin15AnchoredAtom3277
    Fin15AnchoredAtom3280 Fin15AnchoredAtom3284 Fin15AnchoredAtom3309 Fin15AnchoredAtom3484
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

theorem fin15Anchored_clause31692 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom2866 chi ∧
      ¬Fin15AnchoredAtom2870 chi ∧
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
  refine ⟨{1, 2, 3, 4, 7, 9, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask18078
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2824 Fin15AnchoredAtom2826 Fin15AnchoredAtom2827
    Fin15AnchoredAtom2831 Fin15AnchoredAtom2850 Fin15AnchoredAtom2851 Fin15AnchoredAtom2855
    Fin15AnchoredAtom2862 Fin15AnchoredAtom2866 Fin15AnchoredAtom2870 Fin15AnchoredAtom2895
    Fin15AnchoredAtom2896 Fin15AnchoredAtom2900 Fin15AnchoredAtom2907 Fin15AnchoredAtom2911
    Fin15AnchoredAtom2915 Fin15AnchoredAtom2992 Fin15AnchoredAtom2996 Fin15AnchoredAtom3000
    Fin15AnchoredAtom3025 Fin15AnchoredAtom3060 Fin15AnchoredAtom3061 Fin15AnchoredAtom3065
    Fin15AnchoredAtom3072 Fin15AnchoredAtom3076 Fin15AnchoredAtom3080 Fin15AnchoredAtom3157
    Fin15AnchoredAtom3161 Fin15AnchoredAtom3165 Fin15AnchoredAtom3190 Fin15AnchoredAtom3277
    Fin15AnchoredAtom3281 Fin15AnchoredAtom3285 Fin15AnchoredAtom3310 Fin15AnchoredAtom3485
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

theorem fin15Anchored_clause31693 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom2864 chi ∧
      ¬Fin15AnchoredAtom2865 chi ∧
      ¬Fin15AnchoredAtom2874 chi ∧
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
  refine ⟨{1, 2, 3, 4, 7, 9, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask12958
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2824 Fin15AnchoredAtom2826 Fin15AnchoredAtom2829
    Fin15AnchoredAtom2830 Fin15AnchoredAtom2850 Fin15AnchoredAtom2853 Fin15AnchoredAtom2854
    Fin15AnchoredAtom2864 Fin15AnchoredAtom2865 Fin15AnchoredAtom2874 Fin15AnchoredAtom2895
    Fin15AnchoredAtom2898 Fin15AnchoredAtom2899 Fin15AnchoredAtom2909 Fin15AnchoredAtom2910
    Fin15AnchoredAtom2919 Fin15AnchoredAtom2994 Fin15AnchoredAtom2995 Fin15AnchoredAtom3004
    Fin15AnchoredAtom3029 Fin15AnchoredAtom3060 Fin15AnchoredAtom3063 Fin15AnchoredAtom3064
    Fin15AnchoredAtom3074 Fin15AnchoredAtom3075 Fin15AnchoredAtom3084 Fin15AnchoredAtom3159
    Fin15AnchoredAtom3160 Fin15AnchoredAtom3169 Fin15AnchoredAtom3194 Fin15AnchoredAtom3279
    Fin15AnchoredAtom3280 Fin15AnchoredAtom3289 Fin15AnchoredAtom3314 Fin15AnchoredAtom3489
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

theorem fin15Anchored_clause31694 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom2864 chi ∧
      ¬Fin15AnchoredAtom2866 chi ∧
      ¬Fin15AnchoredAtom2875 chi ∧
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
  refine ⟨{1, 2, 3, 4, 7, 9, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21150
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2824 Fin15AnchoredAtom2826 Fin15AnchoredAtom2829
    Fin15AnchoredAtom2831 Fin15AnchoredAtom2850 Fin15AnchoredAtom2853 Fin15AnchoredAtom2855
    Fin15AnchoredAtom2864 Fin15AnchoredAtom2866 Fin15AnchoredAtom2875 Fin15AnchoredAtom2895
    Fin15AnchoredAtom2898 Fin15AnchoredAtom2900 Fin15AnchoredAtom2909 Fin15AnchoredAtom2911
    Fin15AnchoredAtom2920 Fin15AnchoredAtom2994 Fin15AnchoredAtom2996 Fin15AnchoredAtom3005
    Fin15AnchoredAtom3030 Fin15AnchoredAtom3060 Fin15AnchoredAtom3063 Fin15AnchoredAtom3065
    Fin15AnchoredAtom3074 Fin15AnchoredAtom3076 Fin15AnchoredAtom3085 Fin15AnchoredAtom3159
    Fin15AnchoredAtom3161 Fin15AnchoredAtom3170 Fin15AnchoredAtom3195 Fin15AnchoredAtom3279
    Fin15AnchoredAtom3281 Fin15AnchoredAtom3290 Fin15AnchoredAtom3315 Fin15AnchoredAtom3490
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

theorem fin15Anchored_clause31695 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom2865 chi ∧
      ¬Fin15AnchoredAtom2866 chi ∧
      ¬Fin15AnchoredAtom2876 chi ∧
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
  refine ⟨{1, 2, 3, 4, 7, 9, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25246
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2824 Fin15AnchoredAtom2826 Fin15AnchoredAtom2830
    Fin15AnchoredAtom2831 Fin15AnchoredAtom2850 Fin15AnchoredAtom2854 Fin15AnchoredAtom2855
    Fin15AnchoredAtom2865 Fin15AnchoredAtom2866 Fin15AnchoredAtom2876 Fin15AnchoredAtom2895
    Fin15AnchoredAtom2899 Fin15AnchoredAtom2900 Fin15AnchoredAtom2910 Fin15AnchoredAtom2911
    Fin15AnchoredAtom2921 Fin15AnchoredAtom2995 Fin15AnchoredAtom2996 Fin15AnchoredAtom3006
    Fin15AnchoredAtom3031 Fin15AnchoredAtom3060 Fin15AnchoredAtom3064 Fin15AnchoredAtom3065
    Fin15AnchoredAtom3075 Fin15AnchoredAtom3076 Fin15AnchoredAtom3086 Fin15AnchoredAtom3160
    Fin15AnchoredAtom3161 Fin15AnchoredAtom3171 Fin15AnchoredAtom3196 Fin15AnchoredAtom3280
    Fin15AnchoredAtom3281 Fin15AnchoredAtom3291 Fin15AnchoredAtom3316 Fin15AnchoredAtom3491
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

theorem fin15Anchored_clause31696 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom2868 chi ∧
      ¬Fin15AnchoredAtom2869 chi ∧
      ¬Fin15AnchoredAtom2874 chi ∧
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
  refine ⟨{1, 2, 3, 4, 7, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13470
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2824 Fin15AnchoredAtom2827 Fin15AnchoredAtom2829
    Fin15AnchoredAtom2830 Fin15AnchoredAtom2851 Fin15AnchoredAtom2853 Fin15AnchoredAtom2854
    Fin15AnchoredAtom2868 Fin15AnchoredAtom2869 Fin15AnchoredAtom2874 Fin15AnchoredAtom2896
    Fin15AnchoredAtom2898 Fin15AnchoredAtom2899 Fin15AnchoredAtom2913 Fin15AnchoredAtom2914
    Fin15AnchoredAtom2919 Fin15AnchoredAtom2998 Fin15AnchoredAtom2999 Fin15AnchoredAtom3004
    Fin15AnchoredAtom3035 Fin15AnchoredAtom3061 Fin15AnchoredAtom3063 Fin15AnchoredAtom3064
    Fin15AnchoredAtom3078 Fin15AnchoredAtom3079 Fin15AnchoredAtom3084 Fin15AnchoredAtom3163
    Fin15AnchoredAtom3164 Fin15AnchoredAtom3169 Fin15AnchoredAtom3200 Fin15AnchoredAtom3283
    Fin15AnchoredAtom3284 Fin15AnchoredAtom3289 Fin15AnchoredAtom3320 Fin15AnchoredAtom3495
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

theorem fin15Anchored_clause31697 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom2868 chi ∧
      ¬Fin15AnchoredAtom2870 chi ∧
      ¬Fin15AnchoredAtom2875 chi ∧
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
  refine ⟨{1, 2, 3, 4, 7, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21662
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2824 Fin15AnchoredAtom2827 Fin15AnchoredAtom2829
    Fin15AnchoredAtom2831 Fin15AnchoredAtom2851 Fin15AnchoredAtom2853 Fin15AnchoredAtom2855
    Fin15AnchoredAtom2868 Fin15AnchoredAtom2870 Fin15AnchoredAtom2875 Fin15AnchoredAtom2896
    Fin15AnchoredAtom2898 Fin15AnchoredAtom2900 Fin15AnchoredAtom2913 Fin15AnchoredAtom2915
    Fin15AnchoredAtom2920 Fin15AnchoredAtom2998 Fin15AnchoredAtom3000 Fin15AnchoredAtom3005
    Fin15AnchoredAtom3036 Fin15AnchoredAtom3061 Fin15AnchoredAtom3063 Fin15AnchoredAtom3065
    Fin15AnchoredAtom3078 Fin15AnchoredAtom3080 Fin15AnchoredAtom3085 Fin15AnchoredAtom3163
    Fin15AnchoredAtom3165 Fin15AnchoredAtom3170 Fin15AnchoredAtom3201 Fin15AnchoredAtom3283
    Fin15AnchoredAtom3285 Fin15AnchoredAtom3290 Fin15AnchoredAtom3321 Fin15AnchoredAtom3496
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

theorem fin15Anchored_clause31698 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom2869 chi ∧
      ¬Fin15AnchoredAtom2870 chi ∧
      ¬Fin15AnchoredAtom2876 chi ∧
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
  refine ⟨{1, 2, 3, 4, 7, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25758
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2824 Fin15AnchoredAtom2827 Fin15AnchoredAtom2830
    Fin15AnchoredAtom2831 Fin15AnchoredAtom2851 Fin15AnchoredAtom2854 Fin15AnchoredAtom2855
    Fin15AnchoredAtom2869 Fin15AnchoredAtom2870 Fin15AnchoredAtom2876 Fin15AnchoredAtom2896
    Fin15AnchoredAtom2899 Fin15AnchoredAtom2900 Fin15AnchoredAtom2914 Fin15AnchoredAtom2915
    Fin15AnchoredAtom2921 Fin15AnchoredAtom2999 Fin15AnchoredAtom3000 Fin15AnchoredAtom3006
    Fin15AnchoredAtom3037 Fin15AnchoredAtom3061 Fin15AnchoredAtom3064 Fin15AnchoredAtom3065
    Fin15AnchoredAtom3079 Fin15AnchoredAtom3080 Fin15AnchoredAtom3086 Fin15AnchoredAtom3164
    Fin15AnchoredAtom3165 Fin15AnchoredAtom3171 Fin15AnchoredAtom3202 Fin15AnchoredAtom3284
    Fin15AnchoredAtom3285 Fin15AnchoredAtom3291 Fin15AnchoredAtom3322 Fin15AnchoredAtom3497
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

theorem fin15Anchored_clause31699 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom2874 chi ∧
      ¬Fin15AnchoredAtom2875 chi ∧
      ¬Fin15AnchoredAtom2876 chi ∧
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
  refine ⟨{1, 2, 3, 4, 7, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask28830
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2824 Fin15AnchoredAtom2829 Fin15AnchoredAtom2830
    Fin15AnchoredAtom2831 Fin15AnchoredAtom2853 Fin15AnchoredAtom2854 Fin15AnchoredAtom2855
    Fin15AnchoredAtom2874 Fin15AnchoredAtom2875 Fin15AnchoredAtom2876 Fin15AnchoredAtom2898
    Fin15AnchoredAtom2899 Fin15AnchoredAtom2900 Fin15AnchoredAtom2919 Fin15AnchoredAtom2920
    Fin15AnchoredAtom2921 Fin15AnchoredAtom3004 Fin15AnchoredAtom3005 Fin15AnchoredAtom3006
    Fin15AnchoredAtom3041 Fin15AnchoredAtom3063 Fin15AnchoredAtom3064 Fin15AnchoredAtom3065
    Fin15AnchoredAtom3084 Fin15AnchoredAtom3085 Fin15AnchoredAtom3086 Fin15AnchoredAtom3169
    Fin15AnchoredAtom3170 Fin15AnchoredAtom3171 Fin15AnchoredAtom3206 Fin15AnchoredAtom3289
    Fin15AnchoredAtom3290 Fin15AnchoredAtom3291 Fin15AnchoredAtom3326 Fin15AnchoredAtom3501
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

theorem fin15Anchored_clause31700 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom2864 chi ∧
      ¬Fin15AnchoredAtom2865 chi ∧
      ¬Fin15AnchoredAtom2868 chi ∧
      ¬Fin15AnchoredAtom2869 chi ∧
      ¬Fin15AnchoredAtom2874 chi ∧
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
  refine ⟨{1, 2, 3, 4, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13854
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2826 Fin15AnchoredAtom2827 Fin15AnchoredAtom2829
    Fin15AnchoredAtom2830 Fin15AnchoredAtom2862 Fin15AnchoredAtom2864 Fin15AnchoredAtom2865
    Fin15AnchoredAtom2868 Fin15AnchoredAtom2869 Fin15AnchoredAtom2874 Fin15AnchoredAtom2907
    Fin15AnchoredAtom2909 Fin15AnchoredAtom2910 Fin15AnchoredAtom2913 Fin15AnchoredAtom2914
    Fin15AnchoredAtom2919 Fin15AnchoredAtom3023 Fin15AnchoredAtom3024 Fin15AnchoredAtom3029
    Fin15AnchoredAtom3035 Fin15AnchoredAtom3072 Fin15AnchoredAtom3074 Fin15AnchoredAtom3075
    Fin15AnchoredAtom3078 Fin15AnchoredAtom3079 Fin15AnchoredAtom3084 Fin15AnchoredAtom3188
    Fin15AnchoredAtom3189 Fin15AnchoredAtom3194 Fin15AnchoredAtom3200 Fin15AnchoredAtom3308
    Fin15AnchoredAtom3309 Fin15AnchoredAtom3314 Fin15AnchoredAtom3320 Fin15AnchoredAtom3525
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

theorem fin15Anchored_clause31701 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom2864 chi ∧
      ¬Fin15AnchoredAtom2866 chi ∧
      ¬Fin15AnchoredAtom2868 chi ∧
      ¬Fin15AnchoredAtom2870 chi ∧
      ¬Fin15AnchoredAtom2875 chi ∧
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
  refine ⟨{1, 2, 3, 4, 9, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22046
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2826 Fin15AnchoredAtom2827 Fin15AnchoredAtom2829
    Fin15AnchoredAtom2831 Fin15AnchoredAtom2862 Fin15AnchoredAtom2864 Fin15AnchoredAtom2866
    Fin15AnchoredAtom2868 Fin15AnchoredAtom2870 Fin15AnchoredAtom2875 Fin15AnchoredAtom2907
    Fin15AnchoredAtom2909 Fin15AnchoredAtom2911 Fin15AnchoredAtom2913 Fin15AnchoredAtom2915
    Fin15AnchoredAtom2920 Fin15AnchoredAtom3023 Fin15AnchoredAtom3025 Fin15AnchoredAtom3030
    Fin15AnchoredAtom3036 Fin15AnchoredAtom3072 Fin15AnchoredAtom3074 Fin15AnchoredAtom3076
    Fin15AnchoredAtom3078 Fin15AnchoredAtom3080 Fin15AnchoredAtom3085 Fin15AnchoredAtom3188
    Fin15AnchoredAtom3190 Fin15AnchoredAtom3195 Fin15AnchoredAtom3201 Fin15AnchoredAtom3308
    Fin15AnchoredAtom3310 Fin15AnchoredAtom3315 Fin15AnchoredAtom3321 Fin15AnchoredAtom3526
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

theorem fin15Anchored_clause31702 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom2865 chi ∧
      ¬Fin15AnchoredAtom2866 chi ∧
      ¬Fin15AnchoredAtom2869 chi ∧
      ¬Fin15AnchoredAtom2870 chi ∧
      ¬Fin15AnchoredAtom2876 chi ∧
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
  refine ⟨{1, 2, 3, 4, 9, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26142
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2826 Fin15AnchoredAtom2827 Fin15AnchoredAtom2830
    Fin15AnchoredAtom2831 Fin15AnchoredAtom2862 Fin15AnchoredAtom2865 Fin15AnchoredAtom2866
    Fin15AnchoredAtom2869 Fin15AnchoredAtom2870 Fin15AnchoredAtom2876 Fin15AnchoredAtom2907
    Fin15AnchoredAtom2910 Fin15AnchoredAtom2911 Fin15AnchoredAtom2914 Fin15AnchoredAtom2915
    Fin15AnchoredAtom2921 Fin15AnchoredAtom3024 Fin15AnchoredAtom3025 Fin15AnchoredAtom3031
    Fin15AnchoredAtom3037 Fin15AnchoredAtom3072 Fin15AnchoredAtom3075 Fin15AnchoredAtom3076
    Fin15AnchoredAtom3079 Fin15AnchoredAtom3080 Fin15AnchoredAtom3086 Fin15AnchoredAtom3189
    Fin15AnchoredAtom3190 Fin15AnchoredAtom3196 Fin15AnchoredAtom3202 Fin15AnchoredAtom3309
    Fin15AnchoredAtom3310 Fin15AnchoredAtom3316 Fin15AnchoredAtom3322 Fin15AnchoredAtom3527
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

theorem fin15Anchored_clause31703 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2864 chi ∧
      ¬Fin15AnchoredAtom2865 chi ∧
      ¬Fin15AnchoredAtom2866 chi ∧
      ¬Fin15AnchoredAtom2874 chi ∧
      ¬Fin15AnchoredAtom2875 chi ∧
      ¬Fin15AnchoredAtom2876 chi ∧
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
  refine ⟨{1, 2, 3, 4, 9, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29214
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2826 Fin15AnchoredAtom2829 Fin15AnchoredAtom2830
    Fin15AnchoredAtom2831 Fin15AnchoredAtom2864 Fin15AnchoredAtom2865 Fin15AnchoredAtom2866
    Fin15AnchoredAtom2874 Fin15AnchoredAtom2875 Fin15AnchoredAtom2876 Fin15AnchoredAtom2909
    Fin15AnchoredAtom2910 Fin15AnchoredAtom2911 Fin15AnchoredAtom2919 Fin15AnchoredAtom2920
    Fin15AnchoredAtom2921 Fin15AnchoredAtom3029 Fin15AnchoredAtom3030 Fin15AnchoredAtom3031
    Fin15AnchoredAtom3041 Fin15AnchoredAtom3074 Fin15AnchoredAtom3075 Fin15AnchoredAtom3076
    Fin15AnchoredAtom3084 Fin15AnchoredAtom3085 Fin15AnchoredAtom3086 Fin15AnchoredAtom3194
    Fin15AnchoredAtom3195 Fin15AnchoredAtom3196 Fin15AnchoredAtom3206 Fin15AnchoredAtom3314
    Fin15AnchoredAtom3315 Fin15AnchoredAtom3316 Fin15AnchoredAtom3326 Fin15AnchoredAtom3531
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

theorem fin15Anchored_clause31704 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2868 chi ∧
      ¬Fin15AnchoredAtom2869 chi ∧
      ¬Fin15AnchoredAtom2870 chi ∧
      ¬Fin15AnchoredAtom2874 chi ∧
      ¬Fin15AnchoredAtom2875 chi ∧
      ¬Fin15AnchoredAtom2876 chi ∧
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
  refine ⟨{1, 2, 3, 4, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29726
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2827 Fin15AnchoredAtom2829 Fin15AnchoredAtom2830
    Fin15AnchoredAtom2831 Fin15AnchoredAtom2868 Fin15AnchoredAtom2869 Fin15AnchoredAtom2870
    Fin15AnchoredAtom2874 Fin15AnchoredAtom2875 Fin15AnchoredAtom2876 Fin15AnchoredAtom2913
    Fin15AnchoredAtom2914 Fin15AnchoredAtom2915 Fin15AnchoredAtom2919 Fin15AnchoredAtom2920
    Fin15AnchoredAtom2921 Fin15AnchoredAtom3035 Fin15AnchoredAtom3036 Fin15AnchoredAtom3037
    Fin15AnchoredAtom3041 Fin15AnchoredAtom3078 Fin15AnchoredAtom3079 Fin15AnchoredAtom3080
    Fin15AnchoredAtom3084 Fin15AnchoredAtom3085 Fin15AnchoredAtom3086 Fin15AnchoredAtom3200
    Fin15AnchoredAtom3201 Fin15AnchoredAtom3202 Fin15AnchoredAtom3206 Fin15AnchoredAtom3320
    Fin15AnchoredAtom3321 Fin15AnchoredAtom3322 Fin15AnchoredAtom3326 Fin15AnchoredAtom3535
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

theorem fin15Anchored_clause31705 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom2862 chi ∧
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
  refine ⟨{1, 2, 3, 5, 6, 7, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask01774
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2832 Fin15AnchoredAtom2833 Fin15AnchoredAtom2835
    Fin15AnchoredAtom2836 Fin15AnchoredAtom2841 Fin15AnchoredAtom2843 Fin15AnchoredAtom2844
    Fin15AnchoredAtom2850 Fin15AnchoredAtom2851 Fin15AnchoredAtom2862 Fin15AnchoredAtom2922
    Fin15AnchoredAtom2924 Fin15AnchoredAtom2925 Fin15AnchoredAtom2931 Fin15AnchoredAtom2932
    Fin15AnchoredAtom2943 Fin15AnchoredAtom2959 Fin15AnchoredAtom2960 Fin15AnchoredAtom2971
    Fin15AnchoredAtom2992 Fin15AnchoredAtom3087 Fin15AnchoredAtom3089 Fin15AnchoredAtom3090
    Fin15AnchoredAtom3096 Fin15AnchoredAtom3097 Fin15AnchoredAtom3108 Fin15AnchoredAtom3124
    Fin15AnchoredAtom3125 Fin15AnchoredAtom3136 Fin15AnchoredAtom3157 Fin15AnchoredAtom3328
    Fin15AnchoredAtom3329 Fin15AnchoredAtom3340 Fin15AnchoredAtom3361 Fin15AnchoredAtom3417
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

theorem fin15Anchored_clause31706 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom2864 chi ∧
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
  refine ⟨{1, 2, 3, 5, 6, 7, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask04846
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2832 Fin15AnchoredAtom2833 Fin15AnchoredAtom2835
    Fin15AnchoredAtom2838 Fin15AnchoredAtom2841 Fin15AnchoredAtom2843 Fin15AnchoredAtom2846
    Fin15AnchoredAtom2850 Fin15AnchoredAtom2853 Fin15AnchoredAtom2864 Fin15AnchoredAtom2922
    Fin15AnchoredAtom2924 Fin15AnchoredAtom2927 Fin15AnchoredAtom2931 Fin15AnchoredAtom2934
    Fin15AnchoredAtom2945 Fin15AnchoredAtom2959 Fin15AnchoredAtom2962 Fin15AnchoredAtom2973
    Fin15AnchoredAtom2994 Fin15AnchoredAtom3087 Fin15AnchoredAtom3089 Fin15AnchoredAtom3092
    Fin15AnchoredAtom3096 Fin15AnchoredAtom3099 Fin15AnchoredAtom3110 Fin15AnchoredAtom3124
    Fin15AnchoredAtom3127 Fin15AnchoredAtom3138 Fin15AnchoredAtom3159 Fin15AnchoredAtom3328
    Fin15AnchoredAtom3331 Fin15AnchoredAtom3342 Fin15AnchoredAtom3363 Fin15AnchoredAtom3419
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

theorem fin15Anchored_clause31707 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom2865 chi ∧
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
  refine ⟨{1, 2, 3, 5, 6, 7, 9, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask08942
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2832 Fin15AnchoredAtom2833 Fin15AnchoredAtom2835
    Fin15AnchoredAtom2839 Fin15AnchoredAtom2841 Fin15AnchoredAtom2843 Fin15AnchoredAtom2847
    Fin15AnchoredAtom2850 Fin15AnchoredAtom2854 Fin15AnchoredAtom2865 Fin15AnchoredAtom2922
    Fin15AnchoredAtom2924 Fin15AnchoredAtom2928 Fin15AnchoredAtom2931 Fin15AnchoredAtom2935
    Fin15AnchoredAtom2946 Fin15AnchoredAtom2959 Fin15AnchoredAtom2963 Fin15AnchoredAtom2974
    Fin15AnchoredAtom2995 Fin15AnchoredAtom3087 Fin15AnchoredAtom3089 Fin15AnchoredAtom3093
    Fin15AnchoredAtom3096 Fin15AnchoredAtom3100 Fin15AnchoredAtom3111 Fin15AnchoredAtom3124
    Fin15AnchoredAtom3128 Fin15AnchoredAtom3139 Fin15AnchoredAtom3160 Fin15AnchoredAtom3328
    Fin15AnchoredAtom3332 Fin15AnchoredAtom3343 Fin15AnchoredAtom3364 Fin15AnchoredAtom3420
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

theorem fin15Anchored_clause31708 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom2866 chi ∧
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
  refine ⟨{1, 2, 3, 5, 6, 7, 9, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17134
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2832 Fin15AnchoredAtom2833 Fin15AnchoredAtom2835
    Fin15AnchoredAtom2840 Fin15AnchoredAtom2841 Fin15AnchoredAtom2843 Fin15AnchoredAtom2848
    Fin15AnchoredAtom2850 Fin15AnchoredAtom2855 Fin15AnchoredAtom2866 Fin15AnchoredAtom2922
    Fin15AnchoredAtom2924 Fin15AnchoredAtom2929 Fin15AnchoredAtom2931 Fin15AnchoredAtom2936
    Fin15AnchoredAtom2947 Fin15AnchoredAtom2959 Fin15AnchoredAtom2964 Fin15AnchoredAtom2975
    Fin15AnchoredAtom2996 Fin15AnchoredAtom3087 Fin15AnchoredAtom3089 Fin15AnchoredAtom3094
    Fin15AnchoredAtom3096 Fin15AnchoredAtom3101 Fin15AnchoredAtom3112 Fin15AnchoredAtom3124
    Fin15AnchoredAtom3129 Fin15AnchoredAtom3140 Fin15AnchoredAtom3161 Fin15AnchoredAtom3328
    Fin15AnchoredAtom3333 Fin15AnchoredAtom3344 Fin15AnchoredAtom3365 Fin15AnchoredAtom3421
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

theorem fin15Anchored_clause31709 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom2868 chi ∧
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
  refine ⟨{1, 2, 3, 5, 6, 7, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05358
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2832 Fin15AnchoredAtom2833 Fin15AnchoredAtom2836
    Fin15AnchoredAtom2838 Fin15AnchoredAtom2841 Fin15AnchoredAtom2844 Fin15AnchoredAtom2846
    Fin15AnchoredAtom2851 Fin15AnchoredAtom2853 Fin15AnchoredAtom2868 Fin15AnchoredAtom2922
    Fin15AnchoredAtom2925 Fin15AnchoredAtom2927 Fin15AnchoredAtom2932 Fin15AnchoredAtom2934
    Fin15AnchoredAtom2949 Fin15AnchoredAtom2960 Fin15AnchoredAtom2962 Fin15AnchoredAtom2977
    Fin15AnchoredAtom2998 Fin15AnchoredAtom3087 Fin15AnchoredAtom3090 Fin15AnchoredAtom3092
    Fin15AnchoredAtom3097 Fin15AnchoredAtom3099 Fin15AnchoredAtom3114 Fin15AnchoredAtom3125
    Fin15AnchoredAtom3127 Fin15AnchoredAtom3142 Fin15AnchoredAtom3163 Fin15AnchoredAtom3329
    Fin15AnchoredAtom3331 Fin15AnchoredAtom3346 Fin15AnchoredAtom3367 Fin15AnchoredAtom3423
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

theorem fin15Anchored_clause31710 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom2869 chi ∧
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
  refine ⟨{1, 2, 3, 5, 6, 7, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09454
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2832 Fin15AnchoredAtom2833 Fin15AnchoredAtom2836
    Fin15AnchoredAtom2839 Fin15AnchoredAtom2841 Fin15AnchoredAtom2844 Fin15AnchoredAtom2847
    Fin15AnchoredAtom2851 Fin15AnchoredAtom2854 Fin15AnchoredAtom2869 Fin15AnchoredAtom2922
    Fin15AnchoredAtom2925 Fin15AnchoredAtom2928 Fin15AnchoredAtom2932 Fin15AnchoredAtom2935
    Fin15AnchoredAtom2950 Fin15AnchoredAtom2960 Fin15AnchoredAtom2963 Fin15AnchoredAtom2978
    Fin15AnchoredAtom2999 Fin15AnchoredAtom3087 Fin15AnchoredAtom3090 Fin15AnchoredAtom3093
    Fin15AnchoredAtom3097 Fin15AnchoredAtom3100 Fin15AnchoredAtom3115 Fin15AnchoredAtom3125
    Fin15AnchoredAtom3128 Fin15AnchoredAtom3143 Fin15AnchoredAtom3164 Fin15AnchoredAtom3329
    Fin15AnchoredAtom3332 Fin15AnchoredAtom3347 Fin15AnchoredAtom3368 Fin15AnchoredAtom3424
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

theorem fin15Anchored_clause31711 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom2870 chi ∧
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
  refine ⟨{1, 2, 3, 5, 6, 7, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17646
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2832 Fin15AnchoredAtom2833 Fin15AnchoredAtom2836
    Fin15AnchoredAtom2840 Fin15AnchoredAtom2841 Fin15AnchoredAtom2844 Fin15AnchoredAtom2848
    Fin15AnchoredAtom2851 Fin15AnchoredAtom2855 Fin15AnchoredAtom2870 Fin15AnchoredAtom2922
    Fin15AnchoredAtom2925 Fin15AnchoredAtom2929 Fin15AnchoredAtom2932 Fin15AnchoredAtom2936
    Fin15AnchoredAtom2951 Fin15AnchoredAtom2960 Fin15AnchoredAtom2964 Fin15AnchoredAtom2979
    Fin15AnchoredAtom3000 Fin15AnchoredAtom3087 Fin15AnchoredAtom3090 Fin15AnchoredAtom3094
    Fin15AnchoredAtom3097 Fin15AnchoredAtom3101 Fin15AnchoredAtom3116 Fin15AnchoredAtom3125
    Fin15AnchoredAtom3129 Fin15AnchoredAtom3144 Fin15AnchoredAtom3165 Fin15AnchoredAtom3329
    Fin15AnchoredAtom3333 Fin15AnchoredAtom3348 Fin15AnchoredAtom3369 Fin15AnchoredAtom3425
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

theorem fin15Anchored_clause31712 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom2874 chi ∧
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
  refine ⟨{1, 2, 3, 5, 6, 7, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask12526
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2832 Fin15AnchoredAtom2833 Fin15AnchoredAtom2838
    Fin15AnchoredAtom2839 Fin15AnchoredAtom2841 Fin15AnchoredAtom2846 Fin15AnchoredAtom2847
    Fin15AnchoredAtom2853 Fin15AnchoredAtom2854 Fin15AnchoredAtom2874 Fin15AnchoredAtom2922
    Fin15AnchoredAtom2927 Fin15AnchoredAtom2928 Fin15AnchoredAtom2934 Fin15AnchoredAtom2935
    Fin15AnchoredAtom2955 Fin15AnchoredAtom2962 Fin15AnchoredAtom2963 Fin15AnchoredAtom2983
    Fin15AnchoredAtom3004 Fin15AnchoredAtom3087 Fin15AnchoredAtom3092 Fin15AnchoredAtom3093
    Fin15AnchoredAtom3099 Fin15AnchoredAtom3100 Fin15AnchoredAtom3120 Fin15AnchoredAtom3127
    Fin15AnchoredAtom3128 Fin15AnchoredAtom3148 Fin15AnchoredAtom3169 Fin15AnchoredAtom3331
    Fin15AnchoredAtom3332 Fin15AnchoredAtom3352 Fin15AnchoredAtom3373 Fin15AnchoredAtom3429
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

theorem fin15Anchored_clause31713 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom2875 chi ∧
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
  refine ⟨{1, 2, 3, 5, 6, 7, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask20718
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2832 Fin15AnchoredAtom2833 Fin15AnchoredAtom2838
    Fin15AnchoredAtom2840 Fin15AnchoredAtom2841 Fin15AnchoredAtom2846 Fin15AnchoredAtom2848
    Fin15AnchoredAtom2853 Fin15AnchoredAtom2855 Fin15AnchoredAtom2875 Fin15AnchoredAtom2922
    Fin15AnchoredAtom2927 Fin15AnchoredAtom2929 Fin15AnchoredAtom2934 Fin15AnchoredAtom2936
    Fin15AnchoredAtom2956 Fin15AnchoredAtom2962 Fin15AnchoredAtom2964 Fin15AnchoredAtom2984
    Fin15AnchoredAtom3005 Fin15AnchoredAtom3087 Fin15AnchoredAtom3092 Fin15AnchoredAtom3094
    Fin15AnchoredAtom3099 Fin15AnchoredAtom3101 Fin15AnchoredAtom3121 Fin15AnchoredAtom3127
    Fin15AnchoredAtom3129 Fin15AnchoredAtom3149 Fin15AnchoredAtom3170 Fin15AnchoredAtom3331
    Fin15AnchoredAtom3333 Fin15AnchoredAtom3353 Fin15AnchoredAtom3374 Fin15AnchoredAtom3430
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

theorem fin15Anchored_clause31714 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom2876 chi ∧
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
  refine ⟨{1, 2, 3, 5, 6, 7, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask24814
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2832 Fin15AnchoredAtom2833 Fin15AnchoredAtom2839
    Fin15AnchoredAtom2840 Fin15AnchoredAtom2841 Fin15AnchoredAtom2847 Fin15AnchoredAtom2848
    Fin15AnchoredAtom2854 Fin15AnchoredAtom2855 Fin15AnchoredAtom2876 Fin15AnchoredAtom2922
    Fin15AnchoredAtom2928 Fin15AnchoredAtom2929 Fin15AnchoredAtom2935 Fin15AnchoredAtom2936
    Fin15AnchoredAtom2957 Fin15AnchoredAtom2963 Fin15AnchoredAtom2964 Fin15AnchoredAtom2985
    Fin15AnchoredAtom3006 Fin15AnchoredAtom3087 Fin15AnchoredAtom3093 Fin15AnchoredAtom3094
    Fin15AnchoredAtom3100 Fin15AnchoredAtom3101 Fin15AnchoredAtom3122 Fin15AnchoredAtom3128
    Fin15AnchoredAtom3129 Fin15AnchoredAtom3150 Fin15AnchoredAtom3171 Fin15AnchoredAtom3332
    Fin15AnchoredAtom3333 Fin15AnchoredAtom3354 Fin15AnchoredAtom3375 Fin15AnchoredAtom3431
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

theorem fin15Anchored_clause31715 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2837 chi ∧
      ¬Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom2845 chi ∧
      ¬Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom2863 chi ∧
      ¬Fin15AnchoredAtom2867 chi ∧
      ¬Fin15AnchoredAtom2924 chi ∧
      ¬Fin15AnchoredAtom2925 chi ∧
      ¬Fin15AnchoredAtom2926 chi ∧
      ¬Fin15AnchoredAtom2943 chi ∧
      ¬Fin15AnchoredAtom2944 chi ∧
      ¬Fin15AnchoredAtom2948 chi ∧
      ¬Fin15AnchoredAtom2971 chi ∧
      ¬Fin15AnchoredAtom2972 chi ∧
      ¬Fin15AnchoredAtom2976 chi ∧
      ¬Fin15AnchoredAtom3022 chi ∧
      ¬Fin15AnchoredAtom3089 chi ∧
      ¬Fin15AnchoredAtom3090 chi ∧
      ¬Fin15AnchoredAtom3091 chi ∧
      ¬Fin15AnchoredAtom3108 chi ∧
      ¬Fin15AnchoredAtom3109 chi ∧
      ¬Fin15AnchoredAtom3113 chi ∧
      ¬Fin15AnchoredAtom3136 chi ∧
      ¬Fin15AnchoredAtom3137 chi ∧
      ¬Fin15AnchoredAtom3141 chi ∧
      ¬Fin15AnchoredAtom3187 chi ∧
      ¬Fin15AnchoredAtom3340 chi ∧
      ¬Fin15AnchoredAtom3341 chi ∧
      ¬Fin15AnchoredAtom3345 chi ∧
      ¬Fin15AnchoredAtom3391 chi ∧
      ¬Fin15AnchoredAtom3447 chi ∧
      ¬Fin15AnchoredAtom3584 chi ∧
      ¬Fin15AnchoredAtom3585 chi ∧
      ¬Fin15AnchoredAtom3586 chi ∧
      ¬Fin15AnchoredAtom3603 chi ∧
      ¬Fin15AnchoredAtom3604 chi ∧
      ¬Fin15AnchoredAtom3608 chi ∧
      ¬Fin15AnchoredAtom3631 chi ∧
      ¬Fin15AnchoredAtom3632 chi ∧
      ¬Fin15AnchoredAtom3636 chi ∧
      ¬Fin15AnchoredAtom3682 chi ∧
      ¬Fin15AnchoredAtom3835 chi ∧
      ¬Fin15AnchoredAtom3836 chi ∧
      ¬Fin15AnchoredAtom3840 chi ∧
      ¬Fin15AnchoredAtom3886 chi ∧
      ¬Fin15AnchoredAtom3942 chi ∧
      ¬Fin15AnchoredAtom4165 chi ∧
      ¬Fin15AnchoredAtom4166 chi ∧
      ¬Fin15AnchoredAtom4170 chi ∧
      ¬Fin15AnchoredAtom4216 chi ∧
      ¬Fin15AnchoredAtom4272 chi ∧
      ¬Fin15AnchoredAtom4608 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 3, 5, 6, 9, 10, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask03694
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2832 Fin15AnchoredAtom2835 Fin15AnchoredAtom2836
    Fin15AnchoredAtom2837 Fin15AnchoredAtom2843 Fin15AnchoredAtom2844 Fin15AnchoredAtom2845
    Fin15AnchoredAtom2862 Fin15AnchoredAtom2863 Fin15AnchoredAtom2867 Fin15AnchoredAtom2924
    Fin15AnchoredAtom2925 Fin15AnchoredAtom2926 Fin15AnchoredAtom2943 Fin15AnchoredAtom2944
    Fin15AnchoredAtom2948 Fin15AnchoredAtom2971 Fin15AnchoredAtom2972 Fin15AnchoredAtom2976
    Fin15AnchoredAtom3022 Fin15AnchoredAtom3089 Fin15AnchoredAtom3090 Fin15AnchoredAtom3091
    Fin15AnchoredAtom3108 Fin15AnchoredAtom3109 Fin15AnchoredAtom3113 Fin15AnchoredAtom3136
    Fin15AnchoredAtom3137 Fin15AnchoredAtom3141 Fin15AnchoredAtom3187 Fin15AnchoredAtom3340
    Fin15AnchoredAtom3341 Fin15AnchoredAtom3345 Fin15AnchoredAtom3391 Fin15AnchoredAtom3447
    Fin15AnchoredAtom3584 Fin15AnchoredAtom3585 Fin15AnchoredAtom3586 Fin15AnchoredAtom3603
    Fin15AnchoredAtom3604 Fin15AnchoredAtom3608 Fin15AnchoredAtom3631 Fin15AnchoredAtom3632
    Fin15AnchoredAtom3636 Fin15AnchoredAtom3682 Fin15AnchoredAtom3835 Fin15AnchoredAtom3836
    Fin15AnchoredAtom3840 Fin15AnchoredAtom3886 Fin15AnchoredAtom3942 Fin15AnchoredAtom4165
    Fin15AnchoredAtom4166 Fin15AnchoredAtom4170 Fin15AnchoredAtom4216 Fin15AnchoredAtom4272
    Fin15AnchoredAtom4608 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31716 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom2864 chi ∧
      ¬Fin15AnchoredAtom2868 chi ∧
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
  refine ⟨{1, 2, 3, 5, 6, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05742
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2832 Fin15AnchoredAtom2835 Fin15AnchoredAtom2836
    Fin15AnchoredAtom2838 Fin15AnchoredAtom2843 Fin15AnchoredAtom2844 Fin15AnchoredAtom2846
    Fin15AnchoredAtom2862 Fin15AnchoredAtom2864 Fin15AnchoredAtom2868 Fin15AnchoredAtom2924
    Fin15AnchoredAtom2925 Fin15AnchoredAtom2927 Fin15AnchoredAtom2943 Fin15AnchoredAtom2945
    Fin15AnchoredAtom2949 Fin15AnchoredAtom2971 Fin15AnchoredAtom2973 Fin15AnchoredAtom2977
    Fin15AnchoredAtom3023 Fin15AnchoredAtom3089 Fin15AnchoredAtom3090 Fin15AnchoredAtom3092
    Fin15AnchoredAtom3108 Fin15AnchoredAtom3110 Fin15AnchoredAtom3114 Fin15AnchoredAtom3136
    Fin15AnchoredAtom3138 Fin15AnchoredAtom3142 Fin15AnchoredAtom3188 Fin15AnchoredAtom3340
    Fin15AnchoredAtom3342 Fin15AnchoredAtom3346 Fin15AnchoredAtom3392 Fin15AnchoredAtom3448
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

theorem fin15Anchored_clause31717 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom2865 chi ∧
      ¬Fin15AnchoredAtom2869 chi ∧
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
  refine ⟨{1, 2, 3, 5, 6, 9, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09838
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2832 Fin15AnchoredAtom2835 Fin15AnchoredAtom2836
    Fin15AnchoredAtom2839 Fin15AnchoredAtom2843 Fin15AnchoredAtom2844 Fin15AnchoredAtom2847
    Fin15AnchoredAtom2862 Fin15AnchoredAtom2865 Fin15AnchoredAtom2869 Fin15AnchoredAtom2924
    Fin15AnchoredAtom2925 Fin15AnchoredAtom2928 Fin15AnchoredAtom2943 Fin15AnchoredAtom2946
    Fin15AnchoredAtom2950 Fin15AnchoredAtom2971 Fin15AnchoredAtom2974 Fin15AnchoredAtom2978
    Fin15AnchoredAtom3024 Fin15AnchoredAtom3089 Fin15AnchoredAtom3090 Fin15AnchoredAtom3093
    Fin15AnchoredAtom3108 Fin15AnchoredAtom3111 Fin15AnchoredAtom3115 Fin15AnchoredAtom3136
    Fin15AnchoredAtom3139 Fin15AnchoredAtom3143 Fin15AnchoredAtom3189 Fin15AnchoredAtom3340
    Fin15AnchoredAtom3343 Fin15AnchoredAtom3347 Fin15AnchoredAtom3393 Fin15AnchoredAtom3449
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

theorem fin15Anchored_clause31718 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom2866 chi ∧
      ¬Fin15AnchoredAtom2870 chi ∧
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
  refine ⟨{1, 2, 3, 5, 6, 9, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask18030
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2832 Fin15AnchoredAtom2835 Fin15AnchoredAtom2836
    Fin15AnchoredAtom2840 Fin15AnchoredAtom2843 Fin15AnchoredAtom2844 Fin15AnchoredAtom2848
    Fin15AnchoredAtom2862 Fin15AnchoredAtom2866 Fin15AnchoredAtom2870 Fin15AnchoredAtom2924
    Fin15AnchoredAtom2925 Fin15AnchoredAtom2929 Fin15AnchoredAtom2943 Fin15AnchoredAtom2947
    Fin15AnchoredAtom2951 Fin15AnchoredAtom2971 Fin15AnchoredAtom2975 Fin15AnchoredAtom2979
    Fin15AnchoredAtom3025 Fin15AnchoredAtom3089 Fin15AnchoredAtom3090 Fin15AnchoredAtom3094
    Fin15AnchoredAtom3108 Fin15AnchoredAtom3112 Fin15AnchoredAtom3116 Fin15AnchoredAtom3136
    Fin15AnchoredAtom3140 Fin15AnchoredAtom3144 Fin15AnchoredAtom3190 Fin15AnchoredAtom3340
    Fin15AnchoredAtom3344 Fin15AnchoredAtom3348 Fin15AnchoredAtom3394 Fin15AnchoredAtom3450
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

theorem fin15Anchored_clause31719 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom2864 chi ∧
      ¬Fin15AnchoredAtom2865 chi ∧
      ¬Fin15AnchoredAtom2874 chi ∧
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
  refine ⟨{1, 2, 3, 5, 6, 9, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask12910
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2832 Fin15AnchoredAtom2835 Fin15AnchoredAtom2838
    Fin15AnchoredAtom2839 Fin15AnchoredAtom2843 Fin15AnchoredAtom2846 Fin15AnchoredAtom2847
    Fin15AnchoredAtom2864 Fin15AnchoredAtom2865 Fin15AnchoredAtom2874 Fin15AnchoredAtom2924
    Fin15AnchoredAtom2927 Fin15AnchoredAtom2928 Fin15AnchoredAtom2945 Fin15AnchoredAtom2946
    Fin15AnchoredAtom2955 Fin15AnchoredAtom2973 Fin15AnchoredAtom2974 Fin15AnchoredAtom2983
    Fin15AnchoredAtom3029 Fin15AnchoredAtom3089 Fin15AnchoredAtom3092 Fin15AnchoredAtom3093
    Fin15AnchoredAtom3110 Fin15AnchoredAtom3111 Fin15AnchoredAtom3120 Fin15AnchoredAtom3138
    Fin15AnchoredAtom3139 Fin15AnchoredAtom3148 Fin15AnchoredAtom3194 Fin15AnchoredAtom3342
    Fin15AnchoredAtom3343 Fin15AnchoredAtom3352 Fin15AnchoredAtom3398 Fin15AnchoredAtom3454
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

theorem fin15Anchored_clause31720 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom2864 chi ∧
      ¬Fin15AnchoredAtom2866 chi ∧
      ¬Fin15AnchoredAtom2875 chi ∧
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
  refine ⟨{1, 2, 3, 5, 6, 9, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21102
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2832 Fin15AnchoredAtom2835 Fin15AnchoredAtom2838
    Fin15AnchoredAtom2840 Fin15AnchoredAtom2843 Fin15AnchoredAtom2846 Fin15AnchoredAtom2848
    Fin15AnchoredAtom2864 Fin15AnchoredAtom2866 Fin15AnchoredAtom2875 Fin15AnchoredAtom2924
    Fin15AnchoredAtom2927 Fin15AnchoredAtom2929 Fin15AnchoredAtom2945 Fin15AnchoredAtom2947
    Fin15AnchoredAtom2956 Fin15AnchoredAtom2973 Fin15AnchoredAtom2975 Fin15AnchoredAtom2984
    Fin15AnchoredAtom3030 Fin15AnchoredAtom3089 Fin15AnchoredAtom3092 Fin15AnchoredAtom3094
    Fin15AnchoredAtom3110 Fin15AnchoredAtom3112 Fin15AnchoredAtom3121 Fin15AnchoredAtom3138
    Fin15AnchoredAtom3140 Fin15AnchoredAtom3149 Fin15AnchoredAtom3195 Fin15AnchoredAtom3342
    Fin15AnchoredAtom3344 Fin15AnchoredAtom3353 Fin15AnchoredAtom3399 Fin15AnchoredAtom3455
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

theorem fin15Anchored_clause31721 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom2865 chi ∧
      ¬Fin15AnchoredAtom2866 chi ∧
      ¬Fin15AnchoredAtom2876 chi ∧
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
  refine ⟨{1, 2, 3, 5, 6, 9, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25198
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2832 Fin15AnchoredAtom2835 Fin15AnchoredAtom2839
    Fin15AnchoredAtom2840 Fin15AnchoredAtom2843 Fin15AnchoredAtom2847 Fin15AnchoredAtom2848
    Fin15AnchoredAtom2865 Fin15AnchoredAtom2866 Fin15AnchoredAtom2876 Fin15AnchoredAtom2924
    Fin15AnchoredAtom2928 Fin15AnchoredAtom2929 Fin15AnchoredAtom2946 Fin15AnchoredAtom2947
    Fin15AnchoredAtom2957 Fin15AnchoredAtom2974 Fin15AnchoredAtom2975 Fin15AnchoredAtom2985
    Fin15AnchoredAtom3031 Fin15AnchoredAtom3089 Fin15AnchoredAtom3093 Fin15AnchoredAtom3094
    Fin15AnchoredAtom3111 Fin15AnchoredAtom3112 Fin15AnchoredAtom3122 Fin15AnchoredAtom3139
    Fin15AnchoredAtom3140 Fin15AnchoredAtom3150 Fin15AnchoredAtom3196 Fin15AnchoredAtom3343
    Fin15AnchoredAtom3344 Fin15AnchoredAtom3354 Fin15AnchoredAtom3400 Fin15AnchoredAtom3456
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

theorem fin15Anchored_clause31722 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom2868 chi ∧
      ¬Fin15AnchoredAtom2869 chi ∧
      ¬Fin15AnchoredAtom2874 chi ∧
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
  refine ⟨{1, 2, 3, 5, 6, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13422
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2832 Fin15AnchoredAtom2836 Fin15AnchoredAtom2838
    Fin15AnchoredAtom2839 Fin15AnchoredAtom2844 Fin15AnchoredAtom2846 Fin15AnchoredAtom2847
    Fin15AnchoredAtom2868 Fin15AnchoredAtom2869 Fin15AnchoredAtom2874 Fin15AnchoredAtom2925
    Fin15AnchoredAtom2927 Fin15AnchoredAtom2928 Fin15AnchoredAtom2949 Fin15AnchoredAtom2950
    Fin15AnchoredAtom2955 Fin15AnchoredAtom2977 Fin15AnchoredAtom2978 Fin15AnchoredAtom2983
    Fin15AnchoredAtom3035 Fin15AnchoredAtom3090 Fin15AnchoredAtom3092 Fin15AnchoredAtom3093
    Fin15AnchoredAtom3114 Fin15AnchoredAtom3115 Fin15AnchoredAtom3120 Fin15AnchoredAtom3142
    Fin15AnchoredAtom3143 Fin15AnchoredAtom3148 Fin15AnchoredAtom3200 Fin15AnchoredAtom3346
    Fin15AnchoredAtom3347 Fin15AnchoredAtom3352 Fin15AnchoredAtom3404 Fin15AnchoredAtom3460
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

theorem fin15Anchored_clause31723 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom2868 chi ∧
      ¬Fin15AnchoredAtom2870 chi ∧
      ¬Fin15AnchoredAtom2875 chi ∧
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
  refine ⟨{1, 2, 3, 5, 6, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21614
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2832 Fin15AnchoredAtom2836 Fin15AnchoredAtom2838
    Fin15AnchoredAtom2840 Fin15AnchoredAtom2844 Fin15AnchoredAtom2846 Fin15AnchoredAtom2848
    Fin15AnchoredAtom2868 Fin15AnchoredAtom2870 Fin15AnchoredAtom2875 Fin15AnchoredAtom2925
    Fin15AnchoredAtom2927 Fin15AnchoredAtom2929 Fin15AnchoredAtom2949 Fin15AnchoredAtom2951
    Fin15AnchoredAtom2956 Fin15AnchoredAtom2977 Fin15AnchoredAtom2979 Fin15AnchoredAtom2984
    Fin15AnchoredAtom3036 Fin15AnchoredAtom3090 Fin15AnchoredAtom3092 Fin15AnchoredAtom3094
    Fin15AnchoredAtom3114 Fin15AnchoredAtom3116 Fin15AnchoredAtom3121 Fin15AnchoredAtom3142
    Fin15AnchoredAtom3144 Fin15AnchoredAtom3149 Fin15AnchoredAtom3201 Fin15AnchoredAtom3346
    Fin15AnchoredAtom3348 Fin15AnchoredAtom3353 Fin15AnchoredAtom3405 Fin15AnchoredAtom3461
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

theorem fin15Anchored_clause31724 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom2869 chi ∧
      ¬Fin15AnchoredAtom2870 chi ∧
      ¬Fin15AnchoredAtom2876 chi ∧
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
  refine ⟨{1, 2, 3, 5, 6, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25710
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2832 Fin15AnchoredAtom2836 Fin15AnchoredAtom2839
    Fin15AnchoredAtom2840 Fin15AnchoredAtom2844 Fin15AnchoredAtom2847 Fin15AnchoredAtom2848
    Fin15AnchoredAtom2869 Fin15AnchoredAtom2870 Fin15AnchoredAtom2876 Fin15AnchoredAtom2925
    Fin15AnchoredAtom2928 Fin15AnchoredAtom2929 Fin15AnchoredAtom2950 Fin15AnchoredAtom2951
    Fin15AnchoredAtom2957 Fin15AnchoredAtom2978 Fin15AnchoredAtom2979 Fin15AnchoredAtom2985
    Fin15AnchoredAtom3037 Fin15AnchoredAtom3090 Fin15AnchoredAtom3093 Fin15AnchoredAtom3094
    Fin15AnchoredAtom3115 Fin15AnchoredAtom3116 Fin15AnchoredAtom3122 Fin15AnchoredAtom3143
    Fin15AnchoredAtom3144 Fin15AnchoredAtom3150 Fin15AnchoredAtom3202 Fin15AnchoredAtom3347
    Fin15AnchoredAtom3348 Fin15AnchoredAtom3354 Fin15AnchoredAtom3406 Fin15AnchoredAtom3462
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

theorem fin15Anchored_clause31725 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom2874 chi ∧
      ¬Fin15AnchoredAtom2875 chi ∧
      ¬Fin15AnchoredAtom2876 chi ∧
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
  refine ⟨{1, 2, 3, 5, 6, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask28782
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2832 Fin15AnchoredAtom2838 Fin15AnchoredAtom2839
    Fin15AnchoredAtom2840 Fin15AnchoredAtom2846 Fin15AnchoredAtom2847 Fin15AnchoredAtom2848
    Fin15AnchoredAtom2874 Fin15AnchoredAtom2875 Fin15AnchoredAtom2876 Fin15AnchoredAtom2927
    Fin15AnchoredAtom2928 Fin15AnchoredAtom2929 Fin15AnchoredAtom2955 Fin15AnchoredAtom2956
    Fin15AnchoredAtom2957 Fin15AnchoredAtom2983 Fin15AnchoredAtom2984 Fin15AnchoredAtom2985
    Fin15AnchoredAtom3041 Fin15AnchoredAtom3092 Fin15AnchoredAtom3093 Fin15AnchoredAtom3094
    Fin15AnchoredAtom3120 Fin15AnchoredAtom3121 Fin15AnchoredAtom3122 Fin15AnchoredAtom3148
    Fin15AnchoredAtom3149 Fin15AnchoredAtom3150 Fin15AnchoredAtom3206 Fin15AnchoredAtom3352
    Fin15AnchoredAtom3353 Fin15AnchoredAtom3354 Fin15AnchoredAtom3410 Fin15AnchoredAtom3466
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

theorem fin15Anchored_clause31726 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2837 chi ∧
      ¬Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom2852 chi ∧
      ¬Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom2863 chi ∧
      ¬Fin15AnchoredAtom2867 chi ∧
      ¬Fin15AnchoredAtom2931 chi ∧
      ¬Fin15AnchoredAtom2932 chi ∧
      ¬Fin15AnchoredAtom2933 chi ∧
      ¬Fin15AnchoredAtom2943 chi ∧
      ¬Fin15AnchoredAtom2944 chi ∧
      ¬Fin15AnchoredAtom2948 chi ∧
      ¬Fin15AnchoredAtom2992 chi ∧
      ¬Fin15AnchoredAtom2993 chi ∧
      ¬Fin15AnchoredAtom2997 chi ∧
      ¬Fin15AnchoredAtom3022 chi ∧
      ¬Fin15AnchoredAtom3096 chi ∧
      ¬Fin15AnchoredAtom3097 chi ∧
      ¬Fin15AnchoredAtom3098 chi ∧
      ¬Fin15AnchoredAtom3108 chi ∧
      ¬Fin15AnchoredAtom3109 chi ∧
      ¬Fin15AnchoredAtom3113 chi ∧
      ¬Fin15AnchoredAtom3157 chi ∧
      ¬Fin15AnchoredAtom3158 chi ∧
      ¬Fin15AnchoredAtom3162 chi ∧
      ¬Fin15AnchoredAtom3187 chi ∧
      ¬Fin15AnchoredAtom3361 chi ∧
      ¬Fin15AnchoredAtom3362 chi ∧
      ¬Fin15AnchoredAtom3366 chi ∧
      ¬Fin15AnchoredAtom3391 chi ∧
      ¬Fin15AnchoredAtom3482 chi ∧
      ¬Fin15AnchoredAtom3591 chi ∧
      ¬Fin15AnchoredAtom3592 chi ∧
      ¬Fin15AnchoredAtom3593 chi ∧
      ¬Fin15AnchoredAtom3603 chi ∧
      ¬Fin15AnchoredAtom3604 chi ∧
      ¬Fin15AnchoredAtom3608 chi ∧
      ¬Fin15AnchoredAtom3652 chi ∧
      ¬Fin15AnchoredAtom3653 chi ∧
      ¬Fin15AnchoredAtom3657 chi ∧
      ¬Fin15AnchoredAtom3682 chi ∧
      ¬Fin15AnchoredAtom3856 chi ∧
      ¬Fin15AnchoredAtom3857 chi ∧
      ¬Fin15AnchoredAtom3861 chi ∧
      ¬Fin15AnchoredAtom3886 chi ∧
      ¬Fin15AnchoredAtom3977 chi ∧
      ¬Fin15AnchoredAtom4186 chi ∧
      ¬Fin15AnchoredAtom4187 chi ∧
      ¬Fin15AnchoredAtom4191 chi ∧
      ¬Fin15AnchoredAtom4216 chi ∧
      ¬Fin15AnchoredAtom4307 chi ∧
      ¬Fin15AnchoredAtom4643 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 3, 5, 7, 9, 10, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask03758
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2833 Fin15AnchoredAtom2835 Fin15AnchoredAtom2836
    Fin15AnchoredAtom2837 Fin15AnchoredAtom2850 Fin15AnchoredAtom2851 Fin15AnchoredAtom2852
    Fin15AnchoredAtom2862 Fin15AnchoredAtom2863 Fin15AnchoredAtom2867 Fin15AnchoredAtom2931
    Fin15AnchoredAtom2932 Fin15AnchoredAtom2933 Fin15AnchoredAtom2943 Fin15AnchoredAtom2944
    Fin15AnchoredAtom2948 Fin15AnchoredAtom2992 Fin15AnchoredAtom2993 Fin15AnchoredAtom2997
    Fin15AnchoredAtom3022 Fin15AnchoredAtom3096 Fin15AnchoredAtom3097 Fin15AnchoredAtom3098
    Fin15AnchoredAtom3108 Fin15AnchoredAtom3109 Fin15AnchoredAtom3113 Fin15AnchoredAtom3157
    Fin15AnchoredAtom3158 Fin15AnchoredAtom3162 Fin15AnchoredAtom3187 Fin15AnchoredAtom3361
    Fin15AnchoredAtom3362 Fin15AnchoredAtom3366 Fin15AnchoredAtom3391 Fin15AnchoredAtom3482
    Fin15AnchoredAtom3591 Fin15AnchoredAtom3592 Fin15AnchoredAtom3593 Fin15AnchoredAtom3603
    Fin15AnchoredAtom3604 Fin15AnchoredAtom3608 Fin15AnchoredAtom3652 Fin15AnchoredAtom3653
    Fin15AnchoredAtom3657 Fin15AnchoredAtom3682 Fin15AnchoredAtom3856 Fin15AnchoredAtom3857
    Fin15AnchoredAtom3861 Fin15AnchoredAtom3886 Fin15AnchoredAtom3977 Fin15AnchoredAtom4186
    Fin15AnchoredAtom4187 Fin15AnchoredAtom4191 Fin15AnchoredAtom4216 Fin15AnchoredAtom4307
    Fin15AnchoredAtom4643 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31727 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom2864 chi ∧
      ¬Fin15AnchoredAtom2868 chi ∧
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
  refine ⟨{1, 2, 3, 5, 7, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05806
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2833 Fin15AnchoredAtom2835 Fin15AnchoredAtom2836
    Fin15AnchoredAtom2838 Fin15AnchoredAtom2850 Fin15AnchoredAtom2851 Fin15AnchoredAtom2853
    Fin15AnchoredAtom2862 Fin15AnchoredAtom2864 Fin15AnchoredAtom2868 Fin15AnchoredAtom2931
    Fin15AnchoredAtom2932 Fin15AnchoredAtom2934 Fin15AnchoredAtom2943 Fin15AnchoredAtom2945
    Fin15AnchoredAtom2949 Fin15AnchoredAtom2992 Fin15AnchoredAtom2994 Fin15AnchoredAtom2998
    Fin15AnchoredAtom3023 Fin15AnchoredAtom3096 Fin15AnchoredAtom3097 Fin15AnchoredAtom3099
    Fin15AnchoredAtom3108 Fin15AnchoredAtom3110 Fin15AnchoredAtom3114 Fin15AnchoredAtom3157
    Fin15AnchoredAtom3159 Fin15AnchoredAtom3163 Fin15AnchoredAtom3188 Fin15AnchoredAtom3361
    Fin15AnchoredAtom3363 Fin15AnchoredAtom3367 Fin15AnchoredAtom3392 Fin15AnchoredAtom3483
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

theorem fin15Anchored_clause31728 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom2865 chi ∧
      ¬Fin15AnchoredAtom2869 chi ∧
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
  refine ⟨{1, 2, 3, 5, 7, 9, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09902
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2833 Fin15AnchoredAtom2835 Fin15AnchoredAtom2836
    Fin15AnchoredAtom2839 Fin15AnchoredAtom2850 Fin15AnchoredAtom2851 Fin15AnchoredAtom2854
    Fin15AnchoredAtom2862 Fin15AnchoredAtom2865 Fin15AnchoredAtom2869 Fin15AnchoredAtom2931
    Fin15AnchoredAtom2932 Fin15AnchoredAtom2935 Fin15AnchoredAtom2943 Fin15AnchoredAtom2946
    Fin15AnchoredAtom2950 Fin15AnchoredAtom2992 Fin15AnchoredAtom2995 Fin15AnchoredAtom2999
    Fin15AnchoredAtom3024 Fin15AnchoredAtom3096 Fin15AnchoredAtom3097 Fin15AnchoredAtom3100
    Fin15AnchoredAtom3108 Fin15AnchoredAtom3111 Fin15AnchoredAtom3115 Fin15AnchoredAtom3157
    Fin15AnchoredAtom3160 Fin15AnchoredAtom3164 Fin15AnchoredAtom3189 Fin15AnchoredAtom3361
    Fin15AnchoredAtom3364 Fin15AnchoredAtom3368 Fin15AnchoredAtom3393 Fin15AnchoredAtom3484
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

theorem fin15Anchored_clause31729 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom2866 chi ∧
      ¬Fin15AnchoredAtom2870 chi ∧
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
  refine ⟨{1, 2, 3, 5, 7, 9, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask18094
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2833 Fin15AnchoredAtom2835 Fin15AnchoredAtom2836
    Fin15AnchoredAtom2840 Fin15AnchoredAtom2850 Fin15AnchoredAtom2851 Fin15AnchoredAtom2855
    Fin15AnchoredAtom2862 Fin15AnchoredAtom2866 Fin15AnchoredAtom2870 Fin15AnchoredAtom2931
    Fin15AnchoredAtom2932 Fin15AnchoredAtom2936 Fin15AnchoredAtom2943 Fin15AnchoredAtom2947
    Fin15AnchoredAtom2951 Fin15AnchoredAtom2992 Fin15AnchoredAtom2996 Fin15AnchoredAtom3000
    Fin15AnchoredAtom3025 Fin15AnchoredAtom3096 Fin15AnchoredAtom3097 Fin15AnchoredAtom3101
    Fin15AnchoredAtom3108 Fin15AnchoredAtom3112 Fin15AnchoredAtom3116 Fin15AnchoredAtom3157
    Fin15AnchoredAtom3161 Fin15AnchoredAtom3165 Fin15AnchoredAtom3190 Fin15AnchoredAtom3361
    Fin15AnchoredAtom3365 Fin15AnchoredAtom3369 Fin15AnchoredAtom3394 Fin15AnchoredAtom3485
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

theorem fin15Anchored_clause31730 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom2864 chi ∧
      ¬Fin15AnchoredAtom2865 chi ∧
      ¬Fin15AnchoredAtom2874 chi ∧
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
  refine ⟨{1, 2, 3, 5, 7, 9, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask12974
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2833 Fin15AnchoredAtom2835 Fin15AnchoredAtom2838
    Fin15AnchoredAtom2839 Fin15AnchoredAtom2850 Fin15AnchoredAtom2853 Fin15AnchoredAtom2854
    Fin15AnchoredAtom2864 Fin15AnchoredAtom2865 Fin15AnchoredAtom2874 Fin15AnchoredAtom2931
    Fin15AnchoredAtom2934 Fin15AnchoredAtom2935 Fin15AnchoredAtom2945 Fin15AnchoredAtom2946
    Fin15AnchoredAtom2955 Fin15AnchoredAtom2994 Fin15AnchoredAtom2995 Fin15AnchoredAtom3004
    Fin15AnchoredAtom3029 Fin15AnchoredAtom3096 Fin15AnchoredAtom3099 Fin15AnchoredAtom3100
    Fin15AnchoredAtom3110 Fin15AnchoredAtom3111 Fin15AnchoredAtom3120 Fin15AnchoredAtom3159
    Fin15AnchoredAtom3160 Fin15AnchoredAtom3169 Fin15AnchoredAtom3194 Fin15AnchoredAtom3363
    Fin15AnchoredAtom3364 Fin15AnchoredAtom3373 Fin15AnchoredAtom3398 Fin15AnchoredAtom3489
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

theorem fin15Anchored_clause31731 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom2864 chi ∧
      ¬Fin15AnchoredAtom2866 chi ∧
      ¬Fin15AnchoredAtom2875 chi ∧
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
  refine ⟨{1, 2, 3, 5, 7, 9, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21166
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2833 Fin15AnchoredAtom2835 Fin15AnchoredAtom2838
    Fin15AnchoredAtom2840 Fin15AnchoredAtom2850 Fin15AnchoredAtom2853 Fin15AnchoredAtom2855
    Fin15AnchoredAtom2864 Fin15AnchoredAtom2866 Fin15AnchoredAtom2875 Fin15AnchoredAtom2931
    Fin15AnchoredAtom2934 Fin15AnchoredAtom2936 Fin15AnchoredAtom2945 Fin15AnchoredAtom2947
    Fin15AnchoredAtom2956 Fin15AnchoredAtom2994 Fin15AnchoredAtom2996 Fin15AnchoredAtom3005
    Fin15AnchoredAtom3030 Fin15AnchoredAtom3096 Fin15AnchoredAtom3099 Fin15AnchoredAtom3101
    Fin15AnchoredAtom3110 Fin15AnchoredAtom3112 Fin15AnchoredAtom3121 Fin15AnchoredAtom3159
    Fin15AnchoredAtom3161 Fin15AnchoredAtom3170 Fin15AnchoredAtom3195 Fin15AnchoredAtom3363
    Fin15AnchoredAtom3365 Fin15AnchoredAtom3374 Fin15AnchoredAtom3399 Fin15AnchoredAtom3490
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

theorem fin15Anchored_clause31732 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom2865 chi ∧
      ¬Fin15AnchoredAtom2866 chi ∧
      ¬Fin15AnchoredAtom2876 chi ∧
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
  refine ⟨{1, 2, 3, 5, 7, 9, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25262
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2833 Fin15AnchoredAtom2835 Fin15AnchoredAtom2839
    Fin15AnchoredAtom2840 Fin15AnchoredAtom2850 Fin15AnchoredAtom2854 Fin15AnchoredAtom2855
    Fin15AnchoredAtom2865 Fin15AnchoredAtom2866 Fin15AnchoredAtom2876 Fin15AnchoredAtom2931
    Fin15AnchoredAtom2935 Fin15AnchoredAtom2936 Fin15AnchoredAtom2946 Fin15AnchoredAtom2947
    Fin15AnchoredAtom2957 Fin15AnchoredAtom2995 Fin15AnchoredAtom2996 Fin15AnchoredAtom3006
    Fin15AnchoredAtom3031 Fin15AnchoredAtom3096 Fin15AnchoredAtom3100 Fin15AnchoredAtom3101
    Fin15AnchoredAtom3111 Fin15AnchoredAtom3112 Fin15AnchoredAtom3122 Fin15AnchoredAtom3160
    Fin15AnchoredAtom3161 Fin15AnchoredAtom3171 Fin15AnchoredAtom3196 Fin15AnchoredAtom3364
    Fin15AnchoredAtom3365 Fin15AnchoredAtom3375 Fin15AnchoredAtom3400 Fin15AnchoredAtom3491
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

theorem fin15Anchored_clause31733 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom2868 chi ∧
      ¬Fin15AnchoredAtom2869 chi ∧
      ¬Fin15AnchoredAtom2874 chi ∧
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
  refine ⟨{1, 2, 3, 5, 7, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13486
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2833 Fin15AnchoredAtom2836 Fin15AnchoredAtom2838
    Fin15AnchoredAtom2839 Fin15AnchoredAtom2851 Fin15AnchoredAtom2853 Fin15AnchoredAtom2854
    Fin15AnchoredAtom2868 Fin15AnchoredAtom2869 Fin15AnchoredAtom2874 Fin15AnchoredAtom2932
    Fin15AnchoredAtom2934 Fin15AnchoredAtom2935 Fin15AnchoredAtom2949 Fin15AnchoredAtom2950
    Fin15AnchoredAtom2955 Fin15AnchoredAtom2998 Fin15AnchoredAtom2999 Fin15AnchoredAtom3004
    Fin15AnchoredAtom3035 Fin15AnchoredAtom3097 Fin15AnchoredAtom3099 Fin15AnchoredAtom3100
    Fin15AnchoredAtom3114 Fin15AnchoredAtom3115 Fin15AnchoredAtom3120 Fin15AnchoredAtom3163
    Fin15AnchoredAtom3164 Fin15AnchoredAtom3169 Fin15AnchoredAtom3200 Fin15AnchoredAtom3367
    Fin15AnchoredAtom3368 Fin15AnchoredAtom3373 Fin15AnchoredAtom3404 Fin15AnchoredAtom3495
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

theorem fin15Anchored_clause31734 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom2868 chi ∧
      ¬Fin15AnchoredAtom2870 chi ∧
      ¬Fin15AnchoredAtom2875 chi ∧
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
  refine ⟨{1, 2, 3, 5, 7, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21678
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2833 Fin15AnchoredAtom2836 Fin15AnchoredAtom2838
    Fin15AnchoredAtom2840 Fin15AnchoredAtom2851 Fin15AnchoredAtom2853 Fin15AnchoredAtom2855
    Fin15AnchoredAtom2868 Fin15AnchoredAtom2870 Fin15AnchoredAtom2875 Fin15AnchoredAtom2932
    Fin15AnchoredAtom2934 Fin15AnchoredAtom2936 Fin15AnchoredAtom2949 Fin15AnchoredAtom2951
    Fin15AnchoredAtom2956 Fin15AnchoredAtom2998 Fin15AnchoredAtom3000 Fin15AnchoredAtom3005
    Fin15AnchoredAtom3036 Fin15AnchoredAtom3097 Fin15AnchoredAtom3099 Fin15AnchoredAtom3101
    Fin15AnchoredAtom3114 Fin15AnchoredAtom3116 Fin15AnchoredAtom3121 Fin15AnchoredAtom3163
    Fin15AnchoredAtom3165 Fin15AnchoredAtom3170 Fin15AnchoredAtom3201 Fin15AnchoredAtom3367
    Fin15AnchoredAtom3369 Fin15AnchoredAtom3374 Fin15AnchoredAtom3405 Fin15AnchoredAtom3496
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

theorem fin15Anchored_clause31735 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom2869 chi ∧
      ¬Fin15AnchoredAtom2870 chi ∧
      ¬Fin15AnchoredAtom2876 chi ∧
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
  refine ⟨{1, 2, 3, 5, 7, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25774
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2833 Fin15AnchoredAtom2836 Fin15AnchoredAtom2839
    Fin15AnchoredAtom2840 Fin15AnchoredAtom2851 Fin15AnchoredAtom2854 Fin15AnchoredAtom2855
    Fin15AnchoredAtom2869 Fin15AnchoredAtom2870 Fin15AnchoredAtom2876 Fin15AnchoredAtom2932
    Fin15AnchoredAtom2935 Fin15AnchoredAtom2936 Fin15AnchoredAtom2950 Fin15AnchoredAtom2951
    Fin15AnchoredAtom2957 Fin15AnchoredAtom2999 Fin15AnchoredAtom3000 Fin15AnchoredAtom3006
    Fin15AnchoredAtom3037 Fin15AnchoredAtom3097 Fin15AnchoredAtom3100 Fin15AnchoredAtom3101
    Fin15AnchoredAtom3115 Fin15AnchoredAtom3116 Fin15AnchoredAtom3122 Fin15AnchoredAtom3164
    Fin15AnchoredAtom3165 Fin15AnchoredAtom3171 Fin15AnchoredAtom3202 Fin15AnchoredAtom3368
    Fin15AnchoredAtom3369 Fin15AnchoredAtom3375 Fin15AnchoredAtom3406 Fin15AnchoredAtom3497
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

theorem fin15Anchored_clause31736 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom2874 chi ∧
      ¬Fin15AnchoredAtom2875 chi ∧
      ¬Fin15AnchoredAtom2876 chi ∧
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
  refine ⟨{1, 2, 3, 5, 7, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask28846
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2833 Fin15AnchoredAtom2838 Fin15AnchoredAtom2839
    Fin15AnchoredAtom2840 Fin15AnchoredAtom2853 Fin15AnchoredAtom2854 Fin15AnchoredAtom2855
    Fin15AnchoredAtom2874 Fin15AnchoredAtom2875 Fin15AnchoredAtom2876 Fin15AnchoredAtom2934
    Fin15AnchoredAtom2935 Fin15AnchoredAtom2936 Fin15AnchoredAtom2955 Fin15AnchoredAtom2956
    Fin15AnchoredAtom2957 Fin15AnchoredAtom3004 Fin15AnchoredAtom3005 Fin15AnchoredAtom3006
    Fin15AnchoredAtom3041 Fin15AnchoredAtom3099 Fin15AnchoredAtom3100 Fin15AnchoredAtom3101
    Fin15AnchoredAtom3120 Fin15AnchoredAtom3121 Fin15AnchoredAtom3122 Fin15AnchoredAtom3169
    Fin15AnchoredAtom3170 Fin15AnchoredAtom3171 Fin15AnchoredAtom3206 Fin15AnchoredAtom3373
    Fin15AnchoredAtom3374 Fin15AnchoredAtom3375 Fin15AnchoredAtom3410 Fin15AnchoredAtom3501
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

theorem fin15Anchored_clause31737 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2834 chi ∧
      ¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom2857 chi ∧
      ¬Fin15AnchoredAtom2859 chi ∧
      ¬Fin15AnchoredAtom2860 chi ∧
      ¬Fin15AnchoredAtom2868 chi ∧
      ¬Fin15AnchoredAtom2869 chi ∧
      ¬Fin15AnchoredAtom2874 chi ∧
      ¬Fin15AnchoredAtom2938 chi ∧
      ¬Fin15AnchoredAtom2940 chi ∧
      ¬Fin15AnchoredAtom2941 chi ∧
      ¬Fin15AnchoredAtom2949 chi ∧
      ¬Fin15AnchoredAtom2950 chi ∧
      ¬Fin15AnchoredAtom2955 chi ∧
      ¬Fin15AnchoredAtom3013 chi ∧
      ¬Fin15AnchoredAtom3014 chi ∧
      ¬Fin15AnchoredAtom3019 chi ∧
      ¬Fin15AnchoredAtom3035 chi ∧
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
  refine ⟨{1, 2, 3, 5, 8, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13614
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2834 Fin15AnchoredAtom2836 Fin15AnchoredAtom2838
    Fin15AnchoredAtom2839 Fin15AnchoredAtom2857 Fin15AnchoredAtom2859 Fin15AnchoredAtom2860
    Fin15AnchoredAtom2868 Fin15AnchoredAtom2869 Fin15AnchoredAtom2874 Fin15AnchoredAtom2938
    Fin15AnchoredAtom2940 Fin15AnchoredAtom2941 Fin15AnchoredAtom2949 Fin15AnchoredAtom2950
    Fin15AnchoredAtom2955 Fin15AnchoredAtom3013 Fin15AnchoredAtom3014 Fin15AnchoredAtom3019
    Fin15AnchoredAtom3035 Fin15AnchoredAtom3103 Fin15AnchoredAtom3105 Fin15AnchoredAtom3106
    Fin15AnchoredAtom3114 Fin15AnchoredAtom3115 Fin15AnchoredAtom3120 Fin15AnchoredAtom3178
    Fin15AnchoredAtom3179 Fin15AnchoredAtom3184 Fin15AnchoredAtom3200 Fin15AnchoredAtom3382
    Fin15AnchoredAtom3383 Fin15AnchoredAtom3388 Fin15AnchoredAtom3404 Fin15AnchoredAtom3515
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

theorem fin15Anchored_clause31738 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom2864 chi ∧
      ¬Fin15AnchoredAtom2865 chi ∧
      ¬Fin15AnchoredAtom2868 chi ∧
      ¬Fin15AnchoredAtom2869 chi ∧
      ¬Fin15AnchoredAtom2874 chi ∧
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
  refine ⟨{1, 2, 3, 5, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13870
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2835 Fin15AnchoredAtom2836 Fin15AnchoredAtom2838
    Fin15AnchoredAtom2839 Fin15AnchoredAtom2862 Fin15AnchoredAtom2864 Fin15AnchoredAtom2865
    Fin15AnchoredAtom2868 Fin15AnchoredAtom2869 Fin15AnchoredAtom2874 Fin15AnchoredAtom2943
    Fin15AnchoredAtom2945 Fin15AnchoredAtom2946 Fin15AnchoredAtom2949 Fin15AnchoredAtom2950
    Fin15AnchoredAtom2955 Fin15AnchoredAtom3023 Fin15AnchoredAtom3024 Fin15AnchoredAtom3029
    Fin15AnchoredAtom3035 Fin15AnchoredAtom3108 Fin15AnchoredAtom3110 Fin15AnchoredAtom3111
    Fin15AnchoredAtom3114 Fin15AnchoredAtom3115 Fin15AnchoredAtom3120 Fin15AnchoredAtom3188
    Fin15AnchoredAtom3189 Fin15AnchoredAtom3194 Fin15AnchoredAtom3200 Fin15AnchoredAtom3392
    Fin15AnchoredAtom3393 Fin15AnchoredAtom3398 Fin15AnchoredAtom3404 Fin15AnchoredAtom3525
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

theorem fin15Anchored_clause31739 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom2864 chi ∧
      ¬Fin15AnchoredAtom2866 chi ∧
      ¬Fin15AnchoredAtom2868 chi ∧
      ¬Fin15AnchoredAtom2870 chi ∧
      ¬Fin15AnchoredAtom2875 chi ∧
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
  refine ⟨{1, 2, 3, 5, 9, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22062
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2835 Fin15AnchoredAtom2836 Fin15AnchoredAtom2838
    Fin15AnchoredAtom2840 Fin15AnchoredAtom2862 Fin15AnchoredAtom2864 Fin15AnchoredAtom2866
    Fin15AnchoredAtom2868 Fin15AnchoredAtom2870 Fin15AnchoredAtom2875 Fin15AnchoredAtom2943
    Fin15AnchoredAtom2945 Fin15AnchoredAtom2947 Fin15AnchoredAtom2949 Fin15AnchoredAtom2951
    Fin15AnchoredAtom2956 Fin15AnchoredAtom3023 Fin15AnchoredAtom3025 Fin15AnchoredAtom3030
    Fin15AnchoredAtom3036 Fin15AnchoredAtom3108 Fin15AnchoredAtom3110 Fin15AnchoredAtom3112
    Fin15AnchoredAtom3114 Fin15AnchoredAtom3116 Fin15AnchoredAtom3121 Fin15AnchoredAtom3188
    Fin15AnchoredAtom3190 Fin15AnchoredAtom3195 Fin15AnchoredAtom3201 Fin15AnchoredAtom3392
    Fin15AnchoredAtom3394 Fin15AnchoredAtom3399 Fin15AnchoredAtom3405 Fin15AnchoredAtom3526
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

theorem fin15Anchored_clause31740 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom2865 chi ∧
      ¬Fin15AnchoredAtom2866 chi ∧
      ¬Fin15AnchoredAtom2869 chi ∧
      ¬Fin15AnchoredAtom2870 chi ∧
      ¬Fin15AnchoredAtom2876 chi ∧
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
  refine ⟨{1, 2, 3, 5, 9, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26158
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2835 Fin15AnchoredAtom2836 Fin15AnchoredAtom2839
    Fin15AnchoredAtom2840 Fin15AnchoredAtom2862 Fin15AnchoredAtom2865 Fin15AnchoredAtom2866
    Fin15AnchoredAtom2869 Fin15AnchoredAtom2870 Fin15AnchoredAtom2876 Fin15AnchoredAtom2943
    Fin15AnchoredAtom2946 Fin15AnchoredAtom2947 Fin15AnchoredAtom2950 Fin15AnchoredAtom2951
    Fin15AnchoredAtom2957 Fin15AnchoredAtom3024 Fin15AnchoredAtom3025 Fin15AnchoredAtom3031
    Fin15AnchoredAtom3037 Fin15AnchoredAtom3108 Fin15AnchoredAtom3111 Fin15AnchoredAtom3112
    Fin15AnchoredAtom3115 Fin15AnchoredAtom3116 Fin15AnchoredAtom3122 Fin15AnchoredAtom3189
    Fin15AnchoredAtom3190 Fin15AnchoredAtom3196 Fin15AnchoredAtom3202 Fin15AnchoredAtom3393
    Fin15AnchoredAtom3394 Fin15AnchoredAtom3400 Fin15AnchoredAtom3406 Fin15AnchoredAtom3527
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

theorem fin15Anchored_clause31741 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom2864 chi ∧
      ¬Fin15AnchoredAtom2865 chi ∧
      ¬Fin15AnchoredAtom2866 chi ∧
      ¬Fin15AnchoredAtom2874 chi ∧
      ¬Fin15AnchoredAtom2875 chi ∧
      ¬Fin15AnchoredAtom2876 chi ∧
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
      ¬Fin15AnchoredAtom3605 chi ∧
      ¬Fin15AnchoredAtom3606 chi ∧
      ¬Fin15AnchoredAtom3607 chi ∧
      ¬Fin15AnchoredAtom3615 chi ∧
      ¬Fin15AnchoredAtom3616 chi ∧
      ¬Fin15AnchoredAtom3617 chi ∧
      ¬Fin15AnchoredAtom3689 chi ∧
      ¬Fin15AnchoredAtom3690 chi ∧
      ¬Fin15AnchoredAtom3691 chi ∧
      ¬Fin15AnchoredAtom3701 chi ∧
      ¬Fin15AnchoredAtom3893 chi ∧
      ¬Fin15AnchoredAtom3894 chi ∧
      ¬Fin15AnchoredAtom3895 chi ∧
      ¬Fin15AnchoredAtom3905 chi ∧
      ¬Fin15AnchoredAtom4026 chi ∧
      ¬Fin15AnchoredAtom4223 chi ∧
      ¬Fin15AnchoredAtom4224 chi ∧
      ¬Fin15AnchoredAtom4225 chi ∧
      ¬Fin15AnchoredAtom4235 chi ∧
      ¬Fin15AnchoredAtom4356 chi ∧
      ¬Fin15AnchoredAtom4692 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 3, 5, 9, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29230
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2835 Fin15AnchoredAtom2838 Fin15AnchoredAtom2839
    Fin15AnchoredAtom2840 Fin15AnchoredAtom2864 Fin15AnchoredAtom2865 Fin15AnchoredAtom2866
    Fin15AnchoredAtom2874 Fin15AnchoredAtom2875 Fin15AnchoredAtom2876 Fin15AnchoredAtom2945
    Fin15AnchoredAtom2946 Fin15AnchoredAtom2947 Fin15AnchoredAtom2955 Fin15AnchoredAtom2956
    Fin15AnchoredAtom2957 Fin15AnchoredAtom3029 Fin15AnchoredAtom3030 Fin15AnchoredAtom3031
    Fin15AnchoredAtom3041 Fin15AnchoredAtom3110 Fin15AnchoredAtom3111 Fin15AnchoredAtom3112
    Fin15AnchoredAtom3120 Fin15AnchoredAtom3121 Fin15AnchoredAtom3122 Fin15AnchoredAtom3194
    Fin15AnchoredAtom3195 Fin15AnchoredAtom3196 Fin15AnchoredAtom3206 Fin15AnchoredAtom3398
    Fin15AnchoredAtom3399 Fin15AnchoredAtom3400 Fin15AnchoredAtom3410 Fin15AnchoredAtom3531
    Fin15AnchoredAtom3605 Fin15AnchoredAtom3606 Fin15AnchoredAtom3607 Fin15AnchoredAtom3615
    Fin15AnchoredAtom3616 Fin15AnchoredAtom3617 Fin15AnchoredAtom3689 Fin15AnchoredAtom3690
    Fin15AnchoredAtom3691 Fin15AnchoredAtom3701 Fin15AnchoredAtom3893 Fin15AnchoredAtom3894
    Fin15AnchoredAtom3895 Fin15AnchoredAtom3905 Fin15AnchoredAtom4026 Fin15AnchoredAtom4223
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

theorem fin15Anchored_clause31742 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom2868 chi ∧
      ¬Fin15AnchoredAtom2869 chi ∧
      ¬Fin15AnchoredAtom2870 chi ∧
      ¬Fin15AnchoredAtom2874 chi ∧
      ¬Fin15AnchoredAtom2875 chi ∧
      ¬Fin15AnchoredAtom2876 chi ∧
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
      ¬Fin15AnchoredAtom3609 chi ∧
      ¬Fin15AnchoredAtom3610 chi ∧
      ¬Fin15AnchoredAtom3611 chi ∧
      ¬Fin15AnchoredAtom3615 chi ∧
      ¬Fin15AnchoredAtom3616 chi ∧
      ¬Fin15AnchoredAtom3617 chi ∧
      ¬Fin15AnchoredAtom3695 chi ∧
      ¬Fin15AnchoredAtom3696 chi ∧
      ¬Fin15AnchoredAtom3697 chi ∧
      ¬Fin15AnchoredAtom3701 chi ∧
      ¬Fin15AnchoredAtom3899 chi ∧
      ¬Fin15AnchoredAtom3900 chi ∧
      ¬Fin15AnchoredAtom3901 chi ∧
      ¬Fin15AnchoredAtom3905 chi ∧
      ¬Fin15AnchoredAtom4030 chi ∧
      ¬Fin15AnchoredAtom4229 chi ∧
      ¬Fin15AnchoredAtom4230 chi ∧
      ¬Fin15AnchoredAtom4231 chi ∧
      ¬Fin15AnchoredAtom4235 chi ∧
      ¬Fin15AnchoredAtom4360 chi ∧
      ¬Fin15AnchoredAtom4696 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 3, 5, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29742
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2836 Fin15AnchoredAtom2838 Fin15AnchoredAtom2839
    Fin15AnchoredAtom2840 Fin15AnchoredAtom2868 Fin15AnchoredAtom2869 Fin15AnchoredAtom2870
    Fin15AnchoredAtom2874 Fin15AnchoredAtom2875 Fin15AnchoredAtom2876 Fin15AnchoredAtom2949
    Fin15AnchoredAtom2950 Fin15AnchoredAtom2951 Fin15AnchoredAtom2955 Fin15AnchoredAtom2956
    Fin15AnchoredAtom2957 Fin15AnchoredAtom3035 Fin15AnchoredAtom3036 Fin15AnchoredAtom3037
    Fin15AnchoredAtom3041 Fin15AnchoredAtom3114 Fin15AnchoredAtom3115 Fin15AnchoredAtom3116
    Fin15AnchoredAtom3120 Fin15AnchoredAtom3121 Fin15AnchoredAtom3122 Fin15AnchoredAtom3200
    Fin15AnchoredAtom3201 Fin15AnchoredAtom3202 Fin15AnchoredAtom3206 Fin15AnchoredAtom3404
    Fin15AnchoredAtom3405 Fin15AnchoredAtom3406 Fin15AnchoredAtom3410 Fin15AnchoredAtom3535
    Fin15AnchoredAtom3609 Fin15AnchoredAtom3610 Fin15AnchoredAtom3611 Fin15AnchoredAtom3615
    Fin15AnchoredAtom3616 Fin15AnchoredAtom3617 Fin15AnchoredAtom3695 Fin15AnchoredAtom3696
    Fin15AnchoredAtom3697 Fin15AnchoredAtom3701 Fin15AnchoredAtom3899 Fin15AnchoredAtom3900
    Fin15AnchoredAtom3901 Fin15AnchoredAtom3905 Fin15AnchoredAtom4030 Fin15AnchoredAtom4229
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

theorem fin15Anchored_clause31743 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom2864 chi ∧
      ¬Fin15AnchoredAtom2868 chi ∧
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
      ¬Fin15AnchoredAtom3619 chi ∧
      ¬Fin15AnchoredAtom3620 chi ∧
      ¬Fin15AnchoredAtom3622 chi ∧
      ¬Fin15AnchoredAtom3631 chi ∧
      ¬Fin15AnchoredAtom3633 chi ∧
      ¬Fin15AnchoredAtom3637 chi ∧
      ¬Fin15AnchoredAtom3652 chi ∧
      ¬Fin15AnchoredAtom3654 chi ∧
      ¬Fin15AnchoredAtom3658 chi ∧
      ¬Fin15AnchoredAtom3683 chi ∧
      ¬Fin15AnchoredAtom3912 chi ∧
      ¬Fin15AnchoredAtom3914 chi ∧
      ¬Fin15AnchoredAtom3918 chi ∧
      ¬Fin15AnchoredAtom3943 chi ∧
      ¬Fin15AnchoredAtom3978 chi ∧
      ¬Fin15AnchoredAtom4242 chi ∧
      ¬Fin15AnchoredAtom4244 chi ∧
      ¬Fin15AnchoredAtom4248 chi ∧
      ¬Fin15AnchoredAtom4273 chi ∧
      ¬Fin15AnchoredAtom4308 chi ∧
      ¬Fin15AnchoredAtom4714 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 3, 6, 7, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05838
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2841 Fin15AnchoredAtom2843 Fin15AnchoredAtom2844
    Fin15AnchoredAtom2846 Fin15AnchoredAtom2850 Fin15AnchoredAtom2851 Fin15AnchoredAtom2853
    Fin15AnchoredAtom2862 Fin15AnchoredAtom2864 Fin15AnchoredAtom2868 Fin15AnchoredAtom2959
    Fin15AnchoredAtom2960 Fin15AnchoredAtom2962 Fin15AnchoredAtom2971 Fin15AnchoredAtom2973
    Fin15AnchoredAtom2977 Fin15AnchoredAtom2992 Fin15AnchoredAtom2994 Fin15AnchoredAtom2998
    Fin15AnchoredAtom3023 Fin15AnchoredAtom3124 Fin15AnchoredAtom3125 Fin15AnchoredAtom3127
    Fin15AnchoredAtom3136 Fin15AnchoredAtom3138 Fin15AnchoredAtom3142 Fin15AnchoredAtom3157
    Fin15AnchoredAtom3159 Fin15AnchoredAtom3163 Fin15AnchoredAtom3188 Fin15AnchoredAtom3417
    Fin15AnchoredAtom3419 Fin15AnchoredAtom3423 Fin15AnchoredAtom3448 Fin15AnchoredAtom3483
    Fin15AnchoredAtom3619 Fin15AnchoredAtom3620 Fin15AnchoredAtom3622 Fin15AnchoredAtom3631
    Fin15AnchoredAtom3633 Fin15AnchoredAtom3637 Fin15AnchoredAtom3652 Fin15AnchoredAtom3654
    Fin15AnchoredAtom3658 Fin15AnchoredAtom3683 Fin15AnchoredAtom3912 Fin15AnchoredAtom3914
    Fin15AnchoredAtom3918 Fin15AnchoredAtom3943 Fin15AnchoredAtom3978 Fin15AnchoredAtom4242
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

end ErdosSzekeres

end
