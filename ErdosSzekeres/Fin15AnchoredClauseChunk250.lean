module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 250. -/

theorem fin15Anchored_clause32000 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3537 chi ∧
      ¬Fin15AnchoredAtom3538 chi ∧
      ¬Fin15AnchoredAtom3541 chi ∧
      ¬Fin15AnchoredAtom3544 chi ∧
      ¬Fin15AnchoredAtom3546 chi ∧
      ¬Fin15AnchoredAtom3549 chi ∧
      ¬Fin15AnchoredAtom3552 chi ∧
      ¬Fin15AnchoredAtom3556 chi ∧
      ¬Fin15AnchoredAtom3559 chi ∧
      ¬Fin15AnchoredAtom3574 chi ∧
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
      ¬Fin15AnchoredAtom3702 chi ∧
      ¬Fin15AnchoredAtom3705 chi ∧
      ¬Fin15AnchoredAtom3708 chi ∧
      ¬Fin15AnchoredAtom3712 chi ∧
      ¬Fin15AnchoredAtom3715 chi ∧
      ¬Fin15AnchoredAtom3730 chi ∧
      ¬Fin15AnchoredAtom3740 chi ∧
      ¬Fin15AnchoredAtom3743 chi ∧
      ¬Fin15AnchoredAtom3758 chi ∧
      ¬Fin15AnchoredAtom3779 chi ∧
      ¬Fin15AnchoredAtom3824 chi ∧
      ¬Fin15AnchoredAtom3827 chi ∧
      ¬Fin15AnchoredAtom3842 chi ∧
      ¬Fin15AnchoredAtom3863 chi ∧
      ¬Fin15AnchoredAtom3919 chi ∧
      ¬Fin15AnchoredAtom4032 chi ∧
      ¬Fin15AnchoredAtom4035 chi ∧
      ¬Fin15AnchoredAtom4038 chi ∧
      ¬Fin15AnchoredAtom4042 chi ∧
      ¬Fin15AnchoredAtom4045 chi ∧
      ¬Fin15AnchoredAtom4060 chi ∧
      ¬Fin15AnchoredAtom4070 chi ∧
      ¬Fin15AnchoredAtom4073 chi ∧
      ¬Fin15AnchoredAtom4088 chi ∧
      ¬Fin15AnchoredAtom4109 chi ∧
      ¬Fin15AnchoredAtom4154 chi ∧
      ¬Fin15AnchoredAtom4157 chi ∧
      ¬Fin15AnchoredAtom4172 chi ∧
      ¬Fin15AnchoredAtom4193 chi ∧
      ¬Fin15AnchoredAtom4249 chi ∧
      ¬Fin15AnchoredAtom4364 chi ∧
      ¬Fin15AnchoredAtom4367 chi ∧
      ¬Fin15AnchoredAtom4382 chi ∧
      ¬Fin15AnchoredAtom4403 chi ∧
      ¬Fin15AnchoredAtom4459 chi ∧
      ¬Fin15AnchoredAtom4585 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 6, 7, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09468
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3537 Fin15AnchoredAtom3538 Fin15AnchoredAtom3541
    Fin15AnchoredAtom3544 Fin15AnchoredAtom3546 Fin15AnchoredAtom3549 Fin15AnchoredAtom3552
    Fin15AnchoredAtom3556 Fin15AnchoredAtom3559 Fin15AnchoredAtom3574 Fin15AnchoredAtom3582
    Fin15AnchoredAtom3585 Fin15AnchoredAtom3588 Fin15AnchoredAtom3592 Fin15AnchoredAtom3595
    Fin15AnchoredAtom3610 Fin15AnchoredAtom3620 Fin15AnchoredAtom3623 Fin15AnchoredAtom3638
    Fin15AnchoredAtom3659 Fin15AnchoredAtom3702 Fin15AnchoredAtom3705 Fin15AnchoredAtom3708
    Fin15AnchoredAtom3712 Fin15AnchoredAtom3715 Fin15AnchoredAtom3730 Fin15AnchoredAtom3740
    Fin15AnchoredAtom3743 Fin15AnchoredAtom3758 Fin15AnchoredAtom3779 Fin15AnchoredAtom3824
    Fin15AnchoredAtom3827 Fin15AnchoredAtom3842 Fin15AnchoredAtom3863 Fin15AnchoredAtom3919
    Fin15AnchoredAtom4032 Fin15AnchoredAtom4035 Fin15AnchoredAtom4038 Fin15AnchoredAtom4042
    Fin15AnchoredAtom4045 Fin15AnchoredAtom4060 Fin15AnchoredAtom4070 Fin15AnchoredAtom4073
    Fin15AnchoredAtom4088 Fin15AnchoredAtom4109 Fin15AnchoredAtom4154 Fin15AnchoredAtom4157
    Fin15AnchoredAtom4172 Fin15AnchoredAtom4193 Fin15AnchoredAtom4249 Fin15AnchoredAtom4364
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

theorem fin15Anchored_clause32001 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3537 chi ∧
      ¬Fin15AnchoredAtom3538 chi ∧
      ¬Fin15AnchoredAtom3541 chi ∧
      ¬Fin15AnchoredAtom3545 chi ∧
      ¬Fin15AnchoredAtom3546 chi ∧
      ¬Fin15AnchoredAtom3549 chi ∧
      ¬Fin15AnchoredAtom3553 chi ∧
      ¬Fin15AnchoredAtom3556 chi ∧
      ¬Fin15AnchoredAtom3560 chi ∧
      ¬Fin15AnchoredAtom3575 chi ∧
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
      ¬Fin15AnchoredAtom3702 chi ∧
      ¬Fin15AnchoredAtom3705 chi ∧
      ¬Fin15AnchoredAtom3709 chi ∧
      ¬Fin15AnchoredAtom3712 chi ∧
      ¬Fin15AnchoredAtom3716 chi ∧
      ¬Fin15AnchoredAtom3731 chi ∧
      ¬Fin15AnchoredAtom3740 chi ∧
      ¬Fin15AnchoredAtom3744 chi ∧
      ¬Fin15AnchoredAtom3759 chi ∧
      ¬Fin15AnchoredAtom3780 chi ∧
      ¬Fin15AnchoredAtom3824 chi ∧
      ¬Fin15AnchoredAtom3828 chi ∧
      ¬Fin15AnchoredAtom3843 chi ∧
      ¬Fin15AnchoredAtom3864 chi ∧
      ¬Fin15AnchoredAtom3920 chi ∧
      ¬Fin15AnchoredAtom4032 chi ∧
      ¬Fin15AnchoredAtom4035 chi ∧
      ¬Fin15AnchoredAtom4039 chi ∧
      ¬Fin15AnchoredAtom4042 chi ∧
      ¬Fin15AnchoredAtom4046 chi ∧
      ¬Fin15AnchoredAtom4061 chi ∧
      ¬Fin15AnchoredAtom4070 chi ∧
      ¬Fin15AnchoredAtom4074 chi ∧
      ¬Fin15AnchoredAtom4089 chi ∧
      ¬Fin15AnchoredAtom4110 chi ∧
      ¬Fin15AnchoredAtom4154 chi ∧
      ¬Fin15AnchoredAtom4158 chi ∧
      ¬Fin15AnchoredAtom4173 chi ∧
      ¬Fin15AnchoredAtom4194 chi ∧
      ¬Fin15AnchoredAtom4250 chi ∧
      ¬Fin15AnchoredAtom4364 chi ∧
      ¬Fin15AnchoredAtom4368 chi ∧
      ¬Fin15AnchoredAtom4383 chi ∧
      ¬Fin15AnchoredAtom4404 chi ∧
      ¬Fin15AnchoredAtom4460 chi ∧
      ¬Fin15AnchoredAtom4586 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 6, 7, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17660
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3537 Fin15AnchoredAtom3538 Fin15AnchoredAtom3541
    Fin15AnchoredAtom3545 Fin15AnchoredAtom3546 Fin15AnchoredAtom3549 Fin15AnchoredAtom3553
    Fin15AnchoredAtom3556 Fin15AnchoredAtom3560 Fin15AnchoredAtom3575 Fin15AnchoredAtom3582
    Fin15AnchoredAtom3585 Fin15AnchoredAtom3589 Fin15AnchoredAtom3592 Fin15AnchoredAtom3596
    Fin15AnchoredAtom3611 Fin15AnchoredAtom3620 Fin15AnchoredAtom3624 Fin15AnchoredAtom3639
    Fin15AnchoredAtom3660 Fin15AnchoredAtom3702 Fin15AnchoredAtom3705 Fin15AnchoredAtom3709
    Fin15AnchoredAtom3712 Fin15AnchoredAtom3716 Fin15AnchoredAtom3731 Fin15AnchoredAtom3740
    Fin15AnchoredAtom3744 Fin15AnchoredAtom3759 Fin15AnchoredAtom3780 Fin15AnchoredAtom3824
    Fin15AnchoredAtom3828 Fin15AnchoredAtom3843 Fin15AnchoredAtom3864 Fin15AnchoredAtom3920
    Fin15AnchoredAtom4032 Fin15AnchoredAtom4035 Fin15AnchoredAtom4039 Fin15AnchoredAtom4042
    Fin15AnchoredAtom4046 Fin15AnchoredAtom4061 Fin15AnchoredAtom4070 Fin15AnchoredAtom4074
    Fin15AnchoredAtom4089 Fin15AnchoredAtom4110 Fin15AnchoredAtom4154 Fin15AnchoredAtom4158
    Fin15AnchoredAtom4173 Fin15AnchoredAtom4194 Fin15AnchoredAtom4250 Fin15AnchoredAtom4364
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

theorem fin15Anchored_clause32002 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3537 chi ∧
      ¬Fin15AnchoredAtom3538 chi ∧
      ¬Fin15AnchoredAtom3543 chi ∧
      ¬Fin15AnchoredAtom3544 chi ∧
      ¬Fin15AnchoredAtom3546 chi ∧
      ¬Fin15AnchoredAtom3551 chi ∧
      ¬Fin15AnchoredAtom3552 chi ∧
      ¬Fin15AnchoredAtom3558 chi ∧
      ¬Fin15AnchoredAtom3559 chi ∧
      ¬Fin15AnchoredAtom3579 chi ∧
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
      ¬Fin15AnchoredAtom3702 chi ∧
      ¬Fin15AnchoredAtom3707 chi ∧
      ¬Fin15AnchoredAtom3708 chi ∧
      ¬Fin15AnchoredAtom3714 chi ∧
      ¬Fin15AnchoredAtom3715 chi ∧
      ¬Fin15AnchoredAtom3735 chi ∧
      ¬Fin15AnchoredAtom3742 chi ∧
      ¬Fin15AnchoredAtom3743 chi ∧
      ¬Fin15AnchoredAtom3763 chi ∧
      ¬Fin15AnchoredAtom3784 chi ∧
      ¬Fin15AnchoredAtom3826 chi ∧
      ¬Fin15AnchoredAtom3827 chi ∧
      ¬Fin15AnchoredAtom3847 chi ∧
      ¬Fin15AnchoredAtom3868 chi ∧
      ¬Fin15AnchoredAtom3924 chi ∧
      ¬Fin15AnchoredAtom4032 chi ∧
      ¬Fin15AnchoredAtom4037 chi ∧
      ¬Fin15AnchoredAtom4038 chi ∧
      ¬Fin15AnchoredAtom4044 chi ∧
      ¬Fin15AnchoredAtom4045 chi ∧
      ¬Fin15AnchoredAtom4065 chi ∧
      ¬Fin15AnchoredAtom4072 chi ∧
      ¬Fin15AnchoredAtom4073 chi ∧
      ¬Fin15AnchoredAtom4093 chi ∧
      ¬Fin15AnchoredAtom4114 chi ∧
      ¬Fin15AnchoredAtom4156 chi ∧
      ¬Fin15AnchoredAtom4157 chi ∧
      ¬Fin15AnchoredAtom4177 chi ∧
      ¬Fin15AnchoredAtom4198 chi ∧
      ¬Fin15AnchoredAtom4254 chi ∧
      ¬Fin15AnchoredAtom4366 chi ∧
      ¬Fin15AnchoredAtom4367 chi ∧
      ¬Fin15AnchoredAtom4387 chi ∧
      ¬Fin15AnchoredAtom4408 chi ∧
      ¬Fin15AnchoredAtom4464 chi ∧
      ¬Fin15AnchoredAtom4590 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 6, 7, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask12540
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3537 Fin15AnchoredAtom3538 Fin15AnchoredAtom3543
    Fin15AnchoredAtom3544 Fin15AnchoredAtom3546 Fin15AnchoredAtom3551 Fin15AnchoredAtom3552
    Fin15AnchoredAtom3558 Fin15AnchoredAtom3559 Fin15AnchoredAtom3579 Fin15AnchoredAtom3582
    Fin15AnchoredAtom3587 Fin15AnchoredAtom3588 Fin15AnchoredAtom3594 Fin15AnchoredAtom3595
    Fin15AnchoredAtom3615 Fin15AnchoredAtom3622 Fin15AnchoredAtom3623 Fin15AnchoredAtom3643
    Fin15AnchoredAtom3664 Fin15AnchoredAtom3702 Fin15AnchoredAtom3707 Fin15AnchoredAtom3708
    Fin15AnchoredAtom3714 Fin15AnchoredAtom3715 Fin15AnchoredAtom3735 Fin15AnchoredAtom3742
    Fin15AnchoredAtom3743 Fin15AnchoredAtom3763 Fin15AnchoredAtom3784 Fin15AnchoredAtom3826
    Fin15AnchoredAtom3827 Fin15AnchoredAtom3847 Fin15AnchoredAtom3868 Fin15AnchoredAtom3924
    Fin15AnchoredAtom4032 Fin15AnchoredAtom4037 Fin15AnchoredAtom4038 Fin15AnchoredAtom4044
    Fin15AnchoredAtom4045 Fin15AnchoredAtom4065 Fin15AnchoredAtom4072 Fin15AnchoredAtom4073
    Fin15AnchoredAtom4093 Fin15AnchoredAtom4114 Fin15AnchoredAtom4156 Fin15AnchoredAtom4157
    Fin15AnchoredAtom4177 Fin15AnchoredAtom4198 Fin15AnchoredAtom4254 Fin15AnchoredAtom4366
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

theorem fin15Anchored_clause32003 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3537 chi ∧
      ¬Fin15AnchoredAtom3538 chi ∧
      ¬Fin15AnchoredAtom3543 chi ∧
      ¬Fin15AnchoredAtom3545 chi ∧
      ¬Fin15AnchoredAtom3546 chi ∧
      ¬Fin15AnchoredAtom3551 chi ∧
      ¬Fin15AnchoredAtom3553 chi ∧
      ¬Fin15AnchoredAtom3558 chi ∧
      ¬Fin15AnchoredAtom3560 chi ∧
      ¬Fin15AnchoredAtom3580 chi ∧
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
      ¬Fin15AnchoredAtom3702 chi ∧
      ¬Fin15AnchoredAtom3707 chi ∧
      ¬Fin15AnchoredAtom3709 chi ∧
      ¬Fin15AnchoredAtom3714 chi ∧
      ¬Fin15AnchoredAtom3716 chi ∧
      ¬Fin15AnchoredAtom3736 chi ∧
      ¬Fin15AnchoredAtom3742 chi ∧
      ¬Fin15AnchoredAtom3744 chi ∧
      ¬Fin15AnchoredAtom3764 chi ∧
      ¬Fin15AnchoredAtom3785 chi ∧
      ¬Fin15AnchoredAtom3826 chi ∧
      ¬Fin15AnchoredAtom3828 chi ∧
      ¬Fin15AnchoredAtom3848 chi ∧
      ¬Fin15AnchoredAtom3869 chi ∧
      ¬Fin15AnchoredAtom3925 chi ∧
      ¬Fin15AnchoredAtom4032 chi ∧
      ¬Fin15AnchoredAtom4037 chi ∧
      ¬Fin15AnchoredAtom4039 chi ∧
      ¬Fin15AnchoredAtom4044 chi ∧
      ¬Fin15AnchoredAtom4046 chi ∧
      ¬Fin15AnchoredAtom4066 chi ∧
      ¬Fin15AnchoredAtom4072 chi ∧
      ¬Fin15AnchoredAtom4074 chi ∧
      ¬Fin15AnchoredAtom4094 chi ∧
      ¬Fin15AnchoredAtom4115 chi ∧
      ¬Fin15AnchoredAtom4156 chi ∧
      ¬Fin15AnchoredAtom4158 chi ∧
      ¬Fin15AnchoredAtom4178 chi ∧
      ¬Fin15AnchoredAtom4199 chi ∧
      ¬Fin15AnchoredAtom4255 chi ∧
      ¬Fin15AnchoredAtom4366 chi ∧
      ¬Fin15AnchoredAtom4368 chi ∧
      ¬Fin15AnchoredAtom4388 chi ∧
      ¬Fin15AnchoredAtom4409 chi ∧
      ¬Fin15AnchoredAtom4465 chi ∧
      ¬Fin15AnchoredAtom4591 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 6, 7, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask20732
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3537 Fin15AnchoredAtom3538 Fin15AnchoredAtom3543
    Fin15AnchoredAtom3545 Fin15AnchoredAtom3546 Fin15AnchoredAtom3551 Fin15AnchoredAtom3553
    Fin15AnchoredAtom3558 Fin15AnchoredAtom3560 Fin15AnchoredAtom3580 Fin15AnchoredAtom3582
    Fin15AnchoredAtom3587 Fin15AnchoredAtom3589 Fin15AnchoredAtom3594 Fin15AnchoredAtom3596
    Fin15AnchoredAtom3616 Fin15AnchoredAtom3622 Fin15AnchoredAtom3624 Fin15AnchoredAtom3644
    Fin15AnchoredAtom3665 Fin15AnchoredAtom3702 Fin15AnchoredAtom3707 Fin15AnchoredAtom3709
    Fin15AnchoredAtom3714 Fin15AnchoredAtom3716 Fin15AnchoredAtom3736 Fin15AnchoredAtom3742
    Fin15AnchoredAtom3744 Fin15AnchoredAtom3764 Fin15AnchoredAtom3785 Fin15AnchoredAtom3826
    Fin15AnchoredAtom3828 Fin15AnchoredAtom3848 Fin15AnchoredAtom3869 Fin15AnchoredAtom3925
    Fin15AnchoredAtom4032 Fin15AnchoredAtom4037 Fin15AnchoredAtom4039 Fin15AnchoredAtom4044
    Fin15AnchoredAtom4046 Fin15AnchoredAtom4066 Fin15AnchoredAtom4072 Fin15AnchoredAtom4074
    Fin15AnchoredAtom4094 Fin15AnchoredAtom4115 Fin15AnchoredAtom4156 Fin15AnchoredAtom4158
    Fin15AnchoredAtom4178 Fin15AnchoredAtom4199 Fin15AnchoredAtom4255 Fin15AnchoredAtom4366
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

theorem fin15Anchored_clause32004 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3537 chi ∧
      ¬Fin15AnchoredAtom3538 chi ∧
      ¬Fin15AnchoredAtom3544 chi ∧
      ¬Fin15AnchoredAtom3545 chi ∧
      ¬Fin15AnchoredAtom3546 chi ∧
      ¬Fin15AnchoredAtom3552 chi ∧
      ¬Fin15AnchoredAtom3553 chi ∧
      ¬Fin15AnchoredAtom3559 chi ∧
      ¬Fin15AnchoredAtom3560 chi ∧
      ¬Fin15AnchoredAtom3581 chi ∧
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
      ¬Fin15AnchoredAtom3702 chi ∧
      ¬Fin15AnchoredAtom3708 chi ∧
      ¬Fin15AnchoredAtom3709 chi ∧
      ¬Fin15AnchoredAtom3715 chi ∧
      ¬Fin15AnchoredAtom3716 chi ∧
      ¬Fin15AnchoredAtom3737 chi ∧
      ¬Fin15AnchoredAtom3743 chi ∧
      ¬Fin15AnchoredAtom3744 chi ∧
      ¬Fin15AnchoredAtom3765 chi ∧
      ¬Fin15AnchoredAtom3786 chi ∧
      ¬Fin15AnchoredAtom3827 chi ∧
      ¬Fin15AnchoredAtom3828 chi ∧
      ¬Fin15AnchoredAtom3849 chi ∧
      ¬Fin15AnchoredAtom3870 chi ∧
      ¬Fin15AnchoredAtom3926 chi ∧
      ¬Fin15AnchoredAtom4032 chi ∧
      ¬Fin15AnchoredAtom4038 chi ∧
      ¬Fin15AnchoredAtom4039 chi ∧
      ¬Fin15AnchoredAtom4045 chi ∧
      ¬Fin15AnchoredAtom4046 chi ∧
      ¬Fin15AnchoredAtom4067 chi ∧
      ¬Fin15AnchoredAtom4073 chi ∧
      ¬Fin15AnchoredAtom4074 chi ∧
      ¬Fin15AnchoredAtom4095 chi ∧
      ¬Fin15AnchoredAtom4116 chi ∧
      ¬Fin15AnchoredAtom4157 chi ∧
      ¬Fin15AnchoredAtom4158 chi ∧
      ¬Fin15AnchoredAtom4179 chi ∧
      ¬Fin15AnchoredAtom4200 chi ∧
      ¬Fin15AnchoredAtom4256 chi ∧
      ¬Fin15AnchoredAtom4367 chi ∧
      ¬Fin15AnchoredAtom4368 chi ∧
      ¬Fin15AnchoredAtom4389 chi ∧
      ¬Fin15AnchoredAtom4410 chi ∧
      ¬Fin15AnchoredAtom4466 chi ∧
      ¬Fin15AnchoredAtom4592 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 6, 7, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask24828
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3537 Fin15AnchoredAtom3538 Fin15AnchoredAtom3544
    Fin15AnchoredAtom3545 Fin15AnchoredAtom3546 Fin15AnchoredAtom3552 Fin15AnchoredAtom3553
    Fin15AnchoredAtom3559 Fin15AnchoredAtom3560 Fin15AnchoredAtom3581 Fin15AnchoredAtom3582
    Fin15AnchoredAtom3588 Fin15AnchoredAtom3589 Fin15AnchoredAtom3595 Fin15AnchoredAtom3596
    Fin15AnchoredAtom3617 Fin15AnchoredAtom3623 Fin15AnchoredAtom3624 Fin15AnchoredAtom3645
    Fin15AnchoredAtom3666 Fin15AnchoredAtom3702 Fin15AnchoredAtom3708 Fin15AnchoredAtom3709
    Fin15AnchoredAtom3715 Fin15AnchoredAtom3716 Fin15AnchoredAtom3737 Fin15AnchoredAtom3743
    Fin15AnchoredAtom3744 Fin15AnchoredAtom3765 Fin15AnchoredAtom3786 Fin15AnchoredAtom3827
    Fin15AnchoredAtom3828 Fin15AnchoredAtom3849 Fin15AnchoredAtom3870 Fin15AnchoredAtom3926
    Fin15AnchoredAtom4032 Fin15AnchoredAtom4038 Fin15AnchoredAtom4039 Fin15AnchoredAtom4045
    Fin15AnchoredAtom4046 Fin15AnchoredAtom4067 Fin15AnchoredAtom4073 Fin15AnchoredAtom4074
    Fin15AnchoredAtom4095 Fin15AnchoredAtom4116 Fin15AnchoredAtom4157 Fin15AnchoredAtom4158
    Fin15AnchoredAtom4179 Fin15AnchoredAtom4200 Fin15AnchoredAtom4256 Fin15AnchoredAtom4367
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

theorem fin15Anchored_clause32005 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3537 chi ∧
      ¬Fin15AnchoredAtom3540 chi ∧
      ¬Fin15AnchoredAtom3541 chi ∧
      ¬Fin15AnchoredAtom3543 chi ∧
      ¬Fin15AnchoredAtom3548 chi ∧
      ¬Fin15AnchoredAtom3549 chi ∧
      ¬Fin15AnchoredAtom3551 chi ∧
      ¬Fin15AnchoredAtom3567 chi ∧
      ¬Fin15AnchoredAtom3569 chi ∧
      ¬Fin15AnchoredAtom3573 chi ∧
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
      ¬Fin15AnchoredAtom3704 chi ∧
      ¬Fin15AnchoredAtom3705 chi ∧
      ¬Fin15AnchoredAtom3707 chi ∧
      ¬Fin15AnchoredAtom3723 chi ∧
      ¬Fin15AnchoredAtom3725 chi ∧
      ¬Fin15AnchoredAtom3729 chi ∧
      ¬Fin15AnchoredAtom3751 chi ∧
      ¬Fin15AnchoredAtom3753 chi ∧
      ¬Fin15AnchoredAtom3757 chi ∧
      ¬Fin15AnchoredAtom3803 chi ∧
      ¬Fin15AnchoredAtom3835 chi ∧
      ¬Fin15AnchoredAtom3837 chi ∧
      ¬Fin15AnchoredAtom3841 chi ∧
      ¬Fin15AnchoredAtom3887 chi ∧
      ¬Fin15AnchoredAtom3943 chi ∧
      ¬Fin15AnchoredAtom4034 chi ∧
      ¬Fin15AnchoredAtom4035 chi ∧
      ¬Fin15AnchoredAtom4037 chi ∧
      ¬Fin15AnchoredAtom4053 chi ∧
      ¬Fin15AnchoredAtom4055 chi ∧
      ¬Fin15AnchoredAtom4059 chi ∧
      ¬Fin15AnchoredAtom4081 chi ∧
      ¬Fin15AnchoredAtom4083 chi ∧
      ¬Fin15AnchoredAtom4087 chi ∧
      ¬Fin15AnchoredAtom4133 chi ∧
      ¬Fin15AnchoredAtom4165 chi ∧
      ¬Fin15AnchoredAtom4167 chi ∧
      ¬Fin15AnchoredAtom4171 chi ∧
      ¬Fin15AnchoredAtom4217 chi ∧
      ¬Fin15AnchoredAtom4273 chi ∧
      ¬Fin15AnchoredAtom4375 chi ∧
      ¬Fin15AnchoredAtom4377 chi ∧
      ¬Fin15AnchoredAtom4381 chi ∧
      ¬Fin15AnchoredAtom4427 chi ∧
      ¬Fin15AnchoredAtom4483 chi ∧
      ¬Fin15AnchoredAtom4609 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 6, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05756
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3537 Fin15AnchoredAtom3540 Fin15AnchoredAtom3541
    Fin15AnchoredAtom3543 Fin15AnchoredAtom3548 Fin15AnchoredAtom3549 Fin15AnchoredAtom3551
    Fin15AnchoredAtom3567 Fin15AnchoredAtom3569 Fin15AnchoredAtom3573 Fin15AnchoredAtom3584
    Fin15AnchoredAtom3585 Fin15AnchoredAtom3587 Fin15AnchoredAtom3603 Fin15AnchoredAtom3605
    Fin15AnchoredAtom3609 Fin15AnchoredAtom3631 Fin15AnchoredAtom3633 Fin15AnchoredAtom3637
    Fin15AnchoredAtom3683 Fin15AnchoredAtom3704 Fin15AnchoredAtom3705 Fin15AnchoredAtom3707
    Fin15AnchoredAtom3723 Fin15AnchoredAtom3725 Fin15AnchoredAtom3729 Fin15AnchoredAtom3751
    Fin15AnchoredAtom3753 Fin15AnchoredAtom3757 Fin15AnchoredAtom3803 Fin15AnchoredAtom3835
    Fin15AnchoredAtom3837 Fin15AnchoredAtom3841 Fin15AnchoredAtom3887 Fin15AnchoredAtom3943
    Fin15AnchoredAtom4034 Fin15AnchoredAtom4035 Fin15AnchoredAtom4037 Fin15AnchoredAtom4053
    Fin15AnchoredAtom4055 Fin15AnchoredAtom4059 Fin15AnchoredAtom4081 Fin15AnchoredAtom4083
    Fin15AnchoredAtom4087 Fin15AnchoredAtom4133 Fin15AnchoredAtom4165 Fin15AnchoredAtom4167
    Fin15AnchoredAtom4171 Fin15AnchoredAtom4217 Fin15AnchoredAtom4273 Fin15AnchoredAtom4375
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

theorem fin15Anchored_clause32006 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3537 chi ∧
      ¬Fin15AnchoredAtom3540 chi ∧
      ¬Fin15AnchoredAtom3541 chi ∧
      ¬Fin15AnchoredAtom3544 chi ∧
      ¬Fin15AnchoredAtom3548 chi ∧
      ¬Fin15AnchoredAtom3549 chi ∧
      ¬Fin15AnchoredAtom3552 chi ∧
      ¬Fin15AnchoredAtom3567 chi ∧
      ¬Fin15AnchoredAtom3570 chi ∧
      ¬Fin15AnchoredAtom3574 chi ∧
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
      ¬Fin15AnchoredAtom3704 chi ∧
      ¬Fin15AnchoredAtom3705 chi ∧
      ¬Fin15AnchoredAtom3708 chi ∧
      ¬Fin15AnchoredAtom3723 chi ∧
      ¬Fin15AnchoredAtom3726 chi ∧
      ¬Fin15AnchoredAtom3730 chi ∧
      ¬Fin15AnchoredAtom3751 chi ∧
      ¬Fin15AnchoredAtom3754 chi ∧
      ¬Fin15AnchoredAtom3758 chi ∧
      ¬Fin15AnchoredAtom3804 chi ∧
      ¬Fin15AnchoredAtom3835 chi ∧
      ¬Fin15AnchoredAtom3838 chi ∧
      ¬Fin15AnchoredAtom3842 chi ∧
      ¬Fin15AnchoredAtom3888 chi ∧
      ¬Fin15AnchoredAtom3944 chi ∧
      ¬Fin15AnchoredAtom4034 chi ∧
      ¬Fin15AnchoredAtom4035 chi ∧
      ¬Fin15AnchoredAtom4038 chi ∧
      ¬Fin15AnchoredAtom4053 chi ∧
      ¬Fin15AnchoredAtom4056 chi ∧
      ¬Fin15AnchoredAtom4060 chi ∧
      ¬Fin15AnchoredAtom4081 chi ∧
      ¬Fin15AnchoredAtom4084 chi ∧
      ¬Fin15AnchoredAtom4088 chi ∧
      ¬Fin15AnchoredAtom4134 chi ∧
      ¬Fin15AnchoredAtom4165 chi ∧
      ¬Fin15AnchoredAtom4168 chi ∧
      ¬Fin15AnchoredAtom4172 chi ∧
      ¬Fin15AnchoredAtom4218 chi ∧
      ¬Fin15AnchoredAtom4274 chi ∧
      ¬Fin15AnchoredAtom4375 chi ∧
      ¬Fin15AnchoredAtom4378 chi ∧
      ¬Fin15AnchoredAtom4382 chi ∧
      ¬Fin15AnchoredAtom4428 chi ∧
      ¬Fin15AnchoredAtom4484 chi ∧
      ¬Fin15AnchoredAtom4610 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 6, 9, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09852
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3537 Fin15AnchoredAtom3540 Fin15AnchoredAtom3541
    Fin15AnchoredAtom3544 Fin15AnchoredAtom3548 Fin15AnchoredAtom3549 Fin15AnchoredAtom3552
    Fin15AnchoredAtom3567 Fin15AnchoredAtom3570 Fin15AnchoredAtom3574 Fin15AnchoredAtom3584
    Fin15AnchoredAtom3585 Fin15AnchoredAtom3588 Fin15AnchoredAtom3603 Fin15AnchoredAtom3606
    Fin15AnchoredAtom3610 Fin15AnchoredAtom3631 Fin15AnchoredAtom3634 Fin15AnchoredAtom3638
    Fin15AnchoredAtom3684 Fin15AnchoredAtom3704 Fin15AnchoredAtom3705 Fin15AnchoredAtom3708
    Fin15AnchoredAtom3723 Fin15AnchoredAtom3726 Fin15AnchoredAtom3730 Fin15AnchoredAtom3751
    Fin15AnchoredAtom3754 Fin15AnchoredAtom3758 Fin15AnchoredAtom3804 Fin15AnchoredAtom3835
    Fin15AnchoredAtom3838 Fin15AnchoredAtom3842 Fin15AnchoredAtom3888 Fin15AnchoredAtom3944
    Fin15AnchoredAtom4034 Fin15AnchoredAtom4035 Fin15AnchoredAtom4038 Fin15AnchoredAtom4053
    Fin15AnchoredAtom4056 Fin15AnchoredAtom4060 Fin15AnchoredAtom4081 Fin15AnchoredAtom4084
    Fin15AnchoredAtom4088 Fin15AnchoredAtom4134 Fin15AnchoredAtom4165 Fin15AnchoredAtom4168
    Fin15AnchoredAtom4172 Fin15AnchoredAtom4218 Fin15AnchoredAtom4274 Fin15AnchoredAtom4375
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

theorem fin15Anchored_clause32007 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3537 chi ∧
      ¬Fin15AnchoredAtom3540 chi ∧
      ¬Fin15AnchoredAtom3541 chi ∧
      ¬Fin15AnchoredAtom3545 chi ∧
      ¬Fin15AnchoredAtom3548 chi ∧
      ¬Fin15AnchoredAtom3549 chi ∧
      ¬Fin15AnchoredAtom3553 chi ∧
      ¬Fin15AnchoredAtom3567 chi ∧
      ¬Fin15AnchoredAtom3571 chi ∧
      ¬Fin15AnchoredAtom3575 chi ∧
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
      ¬Fin15AnchoredAtom3704 chi ∧
      ¬Fin15AnchoredAtom3705 chi ∧
      ¬Fin15AnchoredAtom3709 chi ∧
      ¬Fin15AnchoredAtom3723 chi ∧
      ¬Fin15AnchoredAtom3727 chi ∧
      ¬Fin15AnchoredAtom3731 chi ∧
      ¬Fin15AnchoredAtom3751 chi ∧
      ¬Fin15AnchoredAtom3755 chi ∧
      ¬Fin15AnchoredAtom3759 chi ∧
      ¬Fin15AnchoredAtom3805 chi ∧
      ¬Fin15AnchoredAtom3835 chi ∧
      ¬Fin15AnchoredAtom3839 chi ∧
      ¬Fin15AnchoredAtom3843 chi ∧
      ¬Fin15AnchoredAtom3889 chi ∧
      ¬Fin15AnchoredAtom3945 chi ∧
      ¬Fin15AnchoredAtom4034 chi ∧
      ¬Fin15AnchoredAtom4035 chi ∧
      ¬Fin15AnchoredAtom4039 chi ∧
      ¬Fin15AnchoredAtom4053 chi ∧
      ¬Fin15AnchoredAtom4057 chi ∧
      ¬Fin15AnchoredAtom4061 chi ∧
      ¬Fin15AnchoredAtom4081 chi ∧
      ¬Fin15AnchoredAtom4085 chi ∧
      ¬Fin15AnchoredAtom4089 chi ∧
      ¬Fin15AnchoredAtom4135 chi ∧
      ¬Fin15AnchoredAtom4165 chi ∧
      ¬Fin15AnchoredAtom4169 chi ∧
      ¬Fin15AnchoredAtom4173 chi ∧
      ¬Fin15AnchoredAtom4219 chi ∧
      ¬Fin15AnchoredAtom4275 chi ∧
      ¬Fin15AnchoredAtom4375 chi ∧
      ¬Fin15AnchoredAtom4379 chi ∧
      ¬Fin15AnchoredAtom4383 chi ∧
      ¬Fin15AnchoredAtom4429 chi ∧
      ¬Fin15AnchoredAtom4485 chi ∧
      ¬Fin15AnchoredAtom4611 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 6, 9, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask18044
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3537 Fin15AnchoredAtom3540 Fin15AnchoredAtom3541
    Fin15AnchoredAtom3545 Fin15AnchoredAtom3548 Fin15AnchoredAtom3549 Fin15AnchoredAtom3553
    Fin15AnchoredAtom3567 Fin15AnchoredAtom3571 Fin15AnchoredAtom3575 Fin15AnchoredAtom3584
    Fin15AnchoredAtom3585 Fin15AnchoredAtom3589 Fin15AnchoredAtom3603 Fin15AnchoredAtom3607
    Fin15AnchoredAtom3611 Fin15AnchoredAtom3631 Fin15AnchoredAtom3635 Fin15AnchoredAtom3639
    Fin15AnchoredAtom3685 Fin15AnchoredAtom3704 Fin15AnchoredAtom3705 Fin15AnchoredAtom3709
    Fin15AnchoredAtom3723 Fin15AnchoredAtom3727 Fin15AnchoredAtom3731 Fin15AnchoredAtom3751
    Fin15AnchoredAtom3755 Fin15AnchoredAtom3759 Fin15AnchoredAtom3805 Fin15AnchoredAtom3835
    Fin15AnchoredAtom3839 Fin15AnchoredAtom3843 Fin15AnchoredAtom3889 Fin15AnchoredAtom3945
    Fin15AnchoredAtom4034 Fin15AnchoredAtom4035 Fin15AnchoredAtom4039 Fin15AnchoredAtom4053
    Fin15AnchoredAtom4057 Fin15AnchoredAtom4061 Fin15AnchoredAtom4081 Fin15AnchoredAtom4085
    Fin15AnchoredAtom4089 Fin15AnchoredAtom4135 Fin15AnchoredAtom4165 Fin15AnchoredAtom4169
    Fin15AnchoredAtom4173 Fin15AnchoredAtom4219 Fin15AnchoredAtom4275 Fin15AnchoredAtom4375
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

theorem fin15Anchored_clause32008 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3537 chi ∧
      ¬Fin15AnchoredAtom3540 chi ∧
      ¬Fin15AnchoredAtom3542 chi ∧
      ¬Fin15AnchoredAtom3545 chi ∧
      ¬Fin15AnchoredAtom3548 chi ∧
      ¬Fin15AnchoredAtom3550 chi ∧
      ¬Fin15AnchoredAtom3553 chi ∧
      ¬Fin15AnchoredAtom3568 chi ∧
      ¬Fin15AnchoredAtom3571 chi ∧
      ¬Fin15AnchoredAtom3578 chi ∧
      ¬Fin15AnchoredAtom3584 chi ∧
      ¬Fin15AnchoredAtom3586 chi ∧
      ¬Fin15AnchoredAtom3589 chi ∧
      ¬Fin15AnchoredAtom3604 chi ∧
      ¬Fin15AnchoredAtom3607 chi ∧
      ¬Fin15AnchoredAtom3614 chi ∧
      ¬Fin15AnchoredAtom3632 chi ∧
      ¬Fin15AnchoredAtom3635 chi ∧
      ¬Fin15AnchoredAtom3642 chi ∧
      ¬Fin15AnchoredAtom3688 chi ∧
      ¬Fin15AnchoredAtom3704 chi ∧
      ¬Fin15AnchoredAtom3706 chi ∧
      ¬Fin15AnchoredAtom3709 chi ∧
      ¬Fin15AnchoredAtom3724 chi ∧
      ¬Fin15AnchoredAtom3727 chi ∧
      ¬Fin15AnchoredAtom3734 chi ∧
      ¬Fin15AnchoredAtom3752 chi ∧
      ¬Fin15AnchoredAtom3755 chi ∧
      ¬Fin15AnchoredAtom3762 chi ∧
      ¬Fin15AnchoredAtom3808 chi ∧
      ¬Fin15AnchoredAtom3836 chi ∧
      ¬Fin15AnchoredAtom3839 chi ∧
      ¬Fin15AnchoredAtom3846 chi ∧
      ¬Fin15AnchoredAtom3892 chi ∧
      ¬Fin15AnchoredAtom3948 chi ∧
      ¬Fin15AnchoredAtom4034 chi ∧
      ¬Fin15AnchoredAtom4036 chi ∧
      ¬Fin15AnchoredAtom4039 chi ∧
      ¬Fin15AnchoredAtom4054 chi ∧
      ¬Fin15AnchoredAtom4057 chi ∧
      ¬Fin15AnchoredAtom4064 chi ∧
      ¬Fin15AnchoredAtom4082 chi ∧
      ¬Fin15AnchoredAtom4085 chi ∧
      ¬Fin15AnchoredAtom4092 chi ∧
      ¬Fin15AnchoredAtom4138 chi ∧
      ¬Fin15AnchoredAtom4166 chi ∧
      ¬Fin15AnchoredAtom4169 chi ∧
      ¬Fin15AnchoredAtom4176 chi ∧
      ¬Fin15AnchoredAtom4222 chi ∧
      ¬Fin15AnchoredAtom4278 chi ∧
      ¬Fin15AnchoredAtom4376 chi ∧
      ¬Fin15AnchoredAtom4379 chi ∧
      ¬Fin15AnchoredAtom4386 chi ∧
      ¬Fin15AnchoredAtom4432 chi ∧
      ¬Fin15AnchoredAtom4488 chi ∧
      ¬Fin15AnchoredAtom4614 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 6, 9, 11, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask19068
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3537 Fin15AnchoredAtom3540 Fin15AnchoredAtom3542
    Fin15AnchoredAtom3545 Fin15AnchoredAtom3548 Fin15AnchoredAtom3550 Fin15AnchoredAtom3553
    Fin15AnchoredAtom3568 Fin15AnchoredAtom3571 Fin15AnchoredAtom3578 Fin15AnchoredAtom3584
    Fin15AnchoredAtom3586 Fin15AnchoredAtom3589 Fin15AnchoredAtom3604 Fin15AnchoredAtom3607
    Fin15AnchoredAtom3614 Fin15AnchoredAtom3632 Fin15AnchoredAtom3635 Fin15AnchoredAtom3642
    Fin15AnchoredAtom3688 Fin15AnchoredAtom3704 Fin15AnchoredAtom3706 Fin15AnchoredAtom3709
    Fin15AnchoredAtom3724 Fin15AnchoredAtom3727 Fin15AnchoredAtom3734 Fin15AnchoredAtom3752
    Fin15AnchoredAtom3755 Fin15AnchoredAtom3762 Fin15AnchoredAtom3808 Fin15AnchoredAtom3836
    Fin15AnchoredAtom3839 Fin15AnchoredAtom3846 Fin15AnchoredAtom3892 Fin15AnchoredAtom3948
    Fin15AnchoredAtom4034 Fin15AnchoredAtom4036 Fin15AnchoredAtom4039 Fin15AnchoredAtom4054
    Fin15AnchoredAtom4057 Fin15AnchoredAtom4064 Fin15AnchoredAtom4082 Fin15AnchoredAtom4085
    Fin15AnchoredAtom4092 Fin15AnchoredAtom4138 Fin15AnchoredAtom4166 Fin15AnchoredAtom4169
    Fin15AnchoredAtom4176 Fin15AnchoredAtom4222 Fin15AnchoredAtom4278 Fin15AnchoredAtom4376
    Fin15AnchoredAtom4379 Fin15AnchoredAtom4386 Fin15AnchoredAtom4432 Fin15AnchoredAtom4488
    Fin15AnchoredAtom4614 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause32009 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3537 chi ∧
      ¬Fin15AnchoredAtom3540 chi ∧
      ¬Fin15AnchoredAtom3543 chi ∧
      ¬Fin15AnchoredAtom3544 chi ∧
      ¬Fin15AnchoredAtom3548 chi ∧
      ¬Fin15AnchoredAtom3551 chi ∧
      ¬Fin15AnchoredAtom3552 chi ∧
      ¬Fin15AnchoredAtom3569 chi ∧
      ¬Fin15AnchoredAtom3570 chi ∧
      ¬Fin15AnchoredAtom3579 chi ∧
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
      ¬Fin15AnchoredAtom3704 chi ∧
      ¬Fin15AnchoredAtom3707 chi ∧
      ¬Fin15AnchoredAtom3708 chi ∧
      ¬Fin15AnchoredAtom3725 chi ∧
      ¬Fin15AnchoredAtom3726 chi ∧
      ¬Fin15AnchoredAtom3735 chi ∧
      ¬Fin15AnchoredAtom3753 chi ∧
      ¬Fin15AnchoredAtom3754 chi ∧
      ¬Fin15AnchoredAtom3763 chi ∧
      ¬Fin15AnchoredAtom3809 chi ∧
      ¬Fin15AnchoredAtom3837 chi ∧
      ¬Fin15AnchoredAtom3838 chi ∧
      ¬Fin15AnchoredAtom3847 chi ∧
      ¬Fin15AnchoredAtom3893 chi ∧
      ¬Fin15AnchoredAtom3949 chi ∧
      ¬Fin15AnchoredAtom4034 chi ∧
      ¬Fin15AnchoredAtom4037 chi ∧
      ¬Fin15AnchoredAtom4038 chi ∧
      ¬Fin15AnchoredAtom4055 chi ∧
      ¬Fin15AnchoredAtom4056 chi ∧
      ¬Fin15AnchoredAtom4065 chi ∧
      ¬Fin15AnchoredAtom4083 chi ∧
      ¬Fin15AnchoredAtom4084 chi ∧
      ¬Fin15AnchoredAtom4093 chi ∧
      ¬Fin15AnchoredAtom4139 chi ∧
      ¬Fin15AnchoredAtom4167 chi ∧
      ¬Fin15AnchoredAtom4168 chi ∧
      ¬Fin15AnchoredAtom4177 chi ∧
      ¬Fin15AnchoredAtom4223 chi ∧
      ¬Fin15AnchoredAtom4279 chi ∧
      ¬Fin15AnchoredAtom4377 chi ∧
      ¬Fin15AnchoredAtom4378 chi ∧
      ¬Fin15AnchoredAtom4387 chi ∧
      ¬Fin15AnchoredAtom4433 chi ∧
      ¬Fin15AnchoredAtom4489 chi ∧
      ¬Fin15AnchoredAtom4615 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 6, 9, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask12924
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3537 Fin15AnchoredAtom3540 Fin15AnchoredAtom3543
    Fin15AnchoredAtom3544 Fin15AnchoredAtom3548 Fin15AnchoredAtom3551 Fin15AnchoredAtom3552
    Fin15AnchoredAtom3569 Fin15AnchoredAtom3570 Fin15AnchoredAtom3579 Fin15AnchoredAtom3584
    Fin15AnchoredAtom3587 Fin15AnchoredAtom3588 Fin15AnchoredAtom3605 Fin15AnchoredAtom3606
    Fin15AnchoredAtom3615 Fin15AnchoredAtom3633 Fin15AnchoredAtom3634 Fin15AnchoredAtom3643
    Fin15AnchoredAtom3689 Fin15AnchoredAtom3704 Fin15AnchoredAtom3707 Fin15AnchoredAtom3708
    Fin15AnchoredAtom3725 Fin15AnchoredAtom3726 Fin15AnchoredAtom3735 Fin15AnchoredAtom3753
    Fin15AnchoredAtom3754 Fin15AnchoredAtom3763 Fin15AnchoredAtom3809 Fin15AnchoredAtom3837
    Fin15AnchoredAtom3838 Fin15AnchoredAtom3847 Fin15AnchoredAtom3893 Fin15AnchoredAtom3949
    Fin15AnchoredAtom4034 Fin15AnchoredAtom4037 Fin15AnchoredAtom4038 Fin15AnchoredAtom4055
    Fin15AnchoredAtom4056 Fin15AnchoredAtom4065 Fin15AnchoredAtom4083 Fin15AnchoredAtom4084
    Fin15AnchoredAtom4093 Fin15AnchoredAtom4139 Fin15AnchoredAtom4167 Fin15AnchoredAtom4168
    Fin15AnchoredAtom4177 Fin15AnchoredAtom4223 Fin15AnchoredAtom4279 Fin15AnchoredAtom4377
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

theorem fin15Anchored_clause32010 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3537 chi ∧
      ¬Fin15AnchoredAtom3540 chi ∧
      ¬Fin15AnchoredAtom3543 chi ∧
      ¬Fin15AnchoredAtom3545 chi ∧
      ¬Fin15AnchoredAtom3548 chi ∧
      ¬Fin15AnchoredAtom3551 chi ∧
      ¬Fin15AnchoredAtom3553 chi ∧
      ¬Fin15AnchoredAtom3569 chi ∧
      ¬Fin15AnchoredAtom3571 chi ∧
      ¬Fin15AnchoredAtom3580 chi ∧
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
      ¬Fin15AnchoredAtom3704 chi ∧
      ¬Fin15AnchoredAtom3707 chi ∧
      ¬Fin15AnchoredAtom3709 chi ∧
      ¬Fin15AnchoredAtom3725 chi ∧
      ¬Fin15AnchoredAtom3727 chi ∧
      ¬Fin15AnchoredAtom3736 chi ∧
      ¬Fin15AnchoredAtom3753 chi ∧
      ¬Fin15AnchoredAtom3755 chi ∧
      ¬Fin15AnchoredAtom3764 chi ∧
      ¬Fin15AnchoredAtom3810 chi ∧
      ¬Fin15AnchoredAtom3837 chi ∧
      ¬Fin15AnchoredAtom3839 chi ∧
      ¬Fin15AnchoredAtom3848 chi ∧
      ¬Fin15AnchoredAtom3894 chi ∧
      ¬Fin15AnchoredAtom3950 chi ∧
      ¬Fin15AnchoredAtom4034 chi ∧
      ¬Fin15AnchoredAtom4037 chi ∧
      ¬Fin15AnchoredAtom4039 chi ∧
      ¬Fin15AnchoredAtom4055 chi ∧
      ¬Fin15AnchoredAtom4057 chi ∧
      ¬Fin15AnchoredAtom4066 chi ∧
      ¬Fin15AnchoredAtom4083 chi ∧
      ¬Fin15AnchoredAtom4085 chi ∧
      ¬Fin15AnchoredAtom4094 chi ∧
      ¬Fin15AnchoredAtom4140 chi ∧
      ¬Fin15AnchoredAtom4167 chi ∧
      ¬Fin15AnchoredAtom4169 chi ∧
      ¬Fin15AnchoredAtom4178 chi ∧
      ¬Fin15AnchoredAtom4224 chi ∧
      ¬Fin15AnchoredAtom4280 chi ∧
      ¬Fin15AnchoredAtom4377 chi ∧
      ¬Fin15AnchoredAtom4379 chi ∧
      ¬Fin15AnchoredAtom4388 chi ∧
      ¬Fin15AnchoredAtom4434 chi ∧
      ¬Fin15AnchoredAtom4490 chi ∧
      ¬Fin15AnchoredAtom4616 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 6, 9, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21116
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3537 Fin15AnchoredAtom3540 Fin15AnchoredAtom3543
    Fin15AnchoredAtom3545 Fin15AnchoredAtom3548 Fin15AnchoredAtom3551 Fin15AnchoredAtom3553
    Fin15AnchoredAtom3569 Fin15AnchoredAtom3571 Fin15AnchoredAtom3580 Fin15AnchoredAtom3584
    Fin15AnchoredAtom3587 Fin15AnchoredAtom3589 Fin15AnchoredAtom3605 Fin15AnchoredAtom3607
    Fin15AnchoredAtom3616 Fin15AnchoredAtom3633 Fin15AnchoredAtom3635 Fin15AnchoredAtom3644
    Fin15AnchoredAtom3690 Fin15AnchoredAtom3704 Fin15AnchoredAtom3707 Fin15AnchoredAtom3709
    Fin15AnchoredAtom3725 Fin15AnchoredAtom3727 Fin15AnchoredAtom3736 Fin15AnchoredAtom3753
    Fin15AnchoredAtom3755 Fin15AnchoredAtom3764 Fin15AnchoredAtom3810 Fin15AnchoredAtom3837
    Fin15AnchoredAtom3839 Fin15AnchoredAtom3848 Fin15AnchoredAtom3894 Fin15AnchoredAtom3950
    Fin15AnchoredAtom4034 Fin15AnchoredAtom4037 Fin15AnchoredAtom4039 Fin15AnchoredAtom4055
    Fin15AnchoredAtom4057 Fin15AnchoredAtom4066 Fin15AnchoredAtom4083 Fin15AnchoredAtom4085
    Fin15AnchoredAtom4094 Fin15AnchoredAtom4140 Fin15AnchoredAtom4167 Fin15AnchoredAtom4169
    Fin15AnchoredAtom4178 Fin15AnchoredAtom4224 Fin15AnchoredAtom4280 Fin15AnchoredAtom4377
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

theorem fin15Anchored_clause32011 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3537 chi ∧
      ¬Fin15AnchoredAtom3540 chi ∧
      ¬Fin15AnchoredAtom3544 chi ∧
      ¬Fin15AnchoredAtom3545 chi ∧
      ¬Fin15AnchoredAtom3548 chi ∧
      ¬Fin15AnchoredAtom3552 chi ∧
      ¬Fin15AnchoredAtom3553 chi ∧
      ¬Fin15AnchoredAtom3570 chi ∧
      ¬Fin15AnchoredAtom3571 chi ∧
      ¬Fin15AnchoredAtom3581 chi ∧
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
      ¬Fin15AnchoredAtom3704 chi ∧
      ¬Fin15AnchoredAtom3708 chi ∧
      ¬Fin15AnchoredAtom3709 chi ∧
      ¬Fin15AnchoredAtom3726 chi ∧
      ¬Fin15AnchoredAtom3727 chi ∧
      ¬Fin15AnchoredAtom3737 chi ∧
      ¬Fin15AnchoredAtom3754 chi ∧
      ¬Fin15AnchoredAtom3755 chi ∧
      ¬Fin15AnchoredAtom3765 chi ∧
      ¬Fin15AnchoredAtom3811 chi ∧
      ¬Fin15AnchoredAtom3838 chi ∧
      ¬Fin15AnchoredAtom3839 chi ∧
      ¬Fin15AnchoredAtom3849 chi ∧
      ¬Fin15AnchoredAtom3895 chi ∧
      ¬Fin15AnchoredAtom3951 chi ∧
      ¬Fin15AnchoredAtom4034 chi ∧
      ¬Fin15AnchoredAtom4038 chi ∧
      ¬Fin15AnchoredAtom4039 chi ∧
      ¬Fin15AnchoredAtom4056 chi ∧
      ¬Fin15AnchoredAtom4057 chi ∧
      ¬Fin15AnchoredAtom4067 chi ∧
      ¬Fin15AnchoredAtom4084 chi ∧
      ¬Fin15AnchoredAtom4085 chi ∧
      ¬Fin15AnchoredAtom4095 chi ∧
      ¬Fin15AnchoredAtom4141 chi ∧
      ¬Fin15AnchoredAtom4168 chi ∧
      ¬Fin15AnchoredAtom4169 chi ∧
      ¬Fin15AnchoredAtom4179 chi ∧
      ¬Fin15AnchoredAtom4225 chi ∧
      ¬Fin15AnchoredAtom4281 chi ∧
      ¬Fin15AnchoredAtom4378 chi ∧
      ¬Fin15AnchoredAtom4379 chi ∧
      ¬Fin15AnchoredAtom4389 chi ∧
      ¬Fin15AnchoredAtom4435 chi ∧
      ¬Fin15AnchoredAtom4491 chi ∧
      ¬Fin15AnchoredAtom4617 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 6, 9, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25212
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3537 Fin15AnchoredAtom3540 Fin15AnchoredAtom3544
    Fin15AnchoredAtom3545 Fin15AnchoredAtom3548 Fin15AnchoredAtom3552 Fin15AnchoredAtom3553
    Fin15AnchoredAtom3570 Fin15AnchoredAtom3571 Fin15AnchoredAtom3581 Fin15AnchoredAtom3584
    Fin15AnchoredAtom3588 Fin15AnchoredAtom3589 Fin15AnchoredAtom3606 Fin15AnchoredAtom3607
    Fin15AnchoredAtom3617 Fin15AnchoredAtom3634 Fin15AnchoredAtom3635 Fin15AnchoredAtom3645
    Fin15AnchoredAtom3691 Fin15AnchoredAtom3704 Fin15AnchoredAtom3708 Fin15AnchoredAtom3709
    Fin15AnchoredAtom3726 Fin15AnchoredAtom3727 Fin15AnchoredAtom3737 Fin15AnchoredAtom3754
    Fin15AnchoredAtom3755 Fin15AnchoredAtom3765 Fin15AnchoredAtom3811 Fin15AnchoredAtom3838
    Fin15AnchoredAtom3839 Fin15AnchoredAtom3849 Fin15AnchoredAtom3895 Fin15AnchoredAtom3951
    Fin15AnchoredAtom4034 Fin15AnchoredAtom4038 Fin15AnchoredAtom4039 Fin15AnchoredAtom4056
    Fin15AnchoredAtom4057 Fin15AnchoredAtom4067 Fin15AnchoredAtom4084 Fin15AnchoredAtom4085
    Fin15AnchoredAtom4095 Fin15AnchoredAtom4141 Fin15AnchoredAtom4168 Fin15AnchoredAtom4169
    Fin15AnchoredAtom4179 Fin15AnchoredAtom4225 Fin15AnchoredAtom4281 Fin15AnchoredAtom4378
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

theorem fin15Anchored_clause32012 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3537 chi ∧
      ¬Fin15AnchoredAtom3541 chi ∧
      ¬Fin15AnchoredAtom3543 chi ∧
      ¬Fin15AnchoredAtom3544 chi ∧
      ¬Fin15AnchoredAtom3549 chi ∧
      ¬Fin15AnchoredAtom3551 chi ∧
      ¬Fin15AnchoredAtom3552 chi ∧
      ¬Fin15AnchoredAtom3573 chi ∧
      ¬Fin15AnchoredAtom3574 chi ∧
      ¬Fin15AnchoredAtom3579 chi ∧
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
      ¬Fin15AnchoredAtom3705 chi ∧
      ¬Fin15AnchoredAtom3707 chi ∧
      ¬Fin15AnchoredAtom3708 chi ∧
      ¬Fin15AnchoredAtom3729 chi ∧
      ¬Fin15AnchoredAtom3730 chi ∧
      ¬Fin15AnchoredAtom3735 chi ∧
      ¬Fin15AnchoredAtom3757 chi ∧
      ¬Fin15AnchoredAtom3758 chi ∧
      ¬Fin15AnchoredAtom3763 chi ∧
      ¬Fin15AnchoredAtom3815 chi ∧
      ¬Fin15AnchoredAtom3841 chi ∧
      ¬Fin15AnchoredAtom3842 chi ∧
      ¬Fin15AnchoredAtom3847 chi ∧
      ¬Fin15AnchoredAtom3899 chi ∧
      ¬Fin15AnchoredAtom3955 chi ∧
      ¬Fin15AnchoredAtom4035 chi ∧
      ¬Fin15AnchoredAtom4037 chi ∧
      ¬Fin15AnchoredAtom4038 chi ∧
      ¬Fin15AnchoredAtom4059 chi ∧
      ¬Fin15AnchoredAtom4060 chi ∧
      ¬Fin15AnchoredAtom4065 chi ∧
      ¬Fin15AnchoredAtom4087 chi ∧
      ¬Fin15AnchoredAtom4088 chi ∧
      ¬Fin15AnchoredAtom4093 chi ∧
      ¬Fin15AnchoredAtom4145 chi ∧
      ¬Fin15AnchoredAtom4171 chi ∧
      ¬Fin15AnchoredAtom4172 chi ∧
      ¬Fin15AnchoredAtom4177 chi ∧
      ¬Fin15AnchoredAtom4229 chi ∧
      ¬Fin15AnchoredAtom4285 chi ∧
      ¬Fin15AnchoredAtom4381 chi ∧
      ¬Fin15AnchoredAtom4382 chi ∧
      ¬Fin15AnchoredAtom4387 chi ∧
      ¬Fin15AnchoredAtom4439 chi ∧
      ¬Fin15AnchoredAtom4495 chi ∧
      ¬Fin15AnchoredAtom4621 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 6, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13436
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3537 Fin15AnchoredAtom3541 Fin15AnchoredAtom3543
    Fin15AnchoredAtom3544 Fin15AnchoredAtom3549 Fin15AnchoredAtom3551 Fin15AnchoredAtom3552
    Fin15AnchoredAtom3573 Fin15AnchoredAtom3574 Fin15AnchoredAtom3579 Fin15AnchoredAtom3585
    Fin15AnchoredAtom3587 Fin15AnchoredAtom3588 Fin15AnchoredAtom3609 Fin15AnchoredAtom3610
    Fin15AnchoredAtom3615 Fin15AnchoredAtom3637 Fin15AnchoredAtom3638 Fin15AnchoredAtom3643
    Fin15AnchoredAtom3695 Fin15AnchoredAtom3705 Fin15AnchoredAtom3707 Fin15AnchoredAtom3708
    Fin15AnchoredAtom3729 Fin15AnchoredAtom3730 Fin15AnchoredAtom3735 Fin15AnchoredAtom3757
    Fin15AnchoredAtom3758 Fin15AnchoredAtom3763 Fin15AnchoredAtom3815 Fin15AnchoredAtom3841
    Fin15AnchoredAtom3842 Fin15AnchoredAtom3847 Fin15AnchoredAtom3899 Fin15AnchoredAtom3955
    Fin15AnchoredAtom4035 Fin15AnchoredAtom4037 Fin15AnchoredAtom4038 Fin15AnchoredAtom4059
    Fin15AnchoredAtom4060 Fin15AnchoredAtom4065 Fin15AnchoredAtom4087 Fin15AnchoredAtom4088
    Fin15AnchoredAtom4093 Fin15AnchoredAtom4145 Fin15AnchoredAtom4171 Fin15AnchoredAtom4172
    Fin15AnchoredAtom4177 Fin15AnchoredAtom4229 Fin15AnchoredAtom4285 Fin15AnchoredAtom4381
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

theorem fin15Anchored_clause32013 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3537 chi ∧
      ¬Fin15AnchoredAtom3541 chi ∧
      ¬Fin15AnchoredAtom3543 chi ∧
      ¬Fin15AnchoredAtom3545 chi ∧
      ¬Fin15AnchoredAtom3549 chi ∧
      ¬Fin15AnchoredAtom3551 chi ∧
      ¬Fin15AnchoredAtom3553 chi ∧
      ¬Fin15AnchoredAtom3573 chi ∧
      ¬Fin15AnchoredAtom3575 chi ∧
      ¬Fin15AnchoredAtom3580 chi ∧
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
      ¬Fin15AnchoredAtom3705 chi ∧
      ¬Fin15AnchoredAtom3707 chi ∧
      ¬Fin15AnchoredAtom3709 chi ∧
      ¬Fin15AnchoredAtom3729 chi ∧
      ¬Fin15AnchoredAtom3731 chi ∧
      ¬Fin15AnchoredAtom3736 chi ∧
      ¬Fin15AnchoredAtom3757 chi ∧
      ¬Fin15AnchoredAtom3759 chi ∧
      ¬Fin15AnchoredAtom3764 chi ∧
      ¬Fin15AnchoredAtom3816 chi ∧
      ¬Fin15AnchoredAtom3841 chi ∧
      ¬Fin15AnchoredAtom3843 chi ∧
      ¬Fin15AnchoredAtom3848 chi ∧
      ¬Fin15AnchoredAtom3900 chi ∧
      ¬Fin15AnchoredAtom3956 chi ∧
      ¬Fin15AnchoredAtom4035 chi ∧
      ¬Fin15AnchoredAtom4037 chi ∧
      ¬Fin15AnchoredAtom4039 chi ∧
      ¬Fin15AnchoredAtom4059 chi ∧
      ¬Fin15AnchoredAtom4061 chi ∧
      ¬Fin15AnchoredAtom4066 chi ∧
      ¬Fin15AnchoredAtom4087 chi ∧
      ¬Fin15AnchoredAtom4089 chi ∧
      ¬Fin15AnchoredAtom4094 chi ∧
      ¬Fin15AnchoredAtom4146 chi ∧
      ¬Fin15AnchoredAtom4171 chi ∧
      ¬Fin15AnchoredAtom4173 chi ∧
      ¬Fin15AnchoredAtom4178 chi ∧
      ¬Fin15AnchoredAtom4230 chi ∧
      ¬Fin15AnchoredAtom4286 chi ∧
      ¬Fin15AnchoredAtom4381 chi ∧
      ¬Fin15AnchoredAtom4383 chi ∧
      ¬Fin15AnchoredAtom4388 chi ∧
      ¬Fin15AnchoredAtom4440 chi ∧
      ¬Fin15AnchoredAtom4496 chi ∧
      ¬Fin15AnchoredAtom4622 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 6, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21628
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3537 Fin15AnchoredAtom3541 Fin15AnchoredAtom3543
    Fin15AnchoredAtom3545 Fin15AnchoredAtom3549 Fin15AnchoredAtom3551 Fin15AnchoredAtom3553
    Fin15AnchoredAtom3573 Fin15AnchoredAtom3575 Fin15AnchoredAtom3580 Fin15AnchoredAtom3585
    Fin15AnchoredAtom3587 Fin15AnchoredAtom3589 Fin15AnchoredAtom3609 Fin15AnchoredAtom3611
    Fin15AnchoredAtom3616 Fin15AnchoredAtom3637 Fin15AnchoredAtom3639 Fin15AnchoredAtom3644
    Fin15AnchoredAtom3696 Fin15AnchoredAtom3705 Fin15AnchoredAtom3707 Fin15AnchoredAtom3709
    Fin15AnchoredAtom3729 Fin15AnchoredAtom3731 Fin15AnchoredAtom3736 Fin15AnchoredAtom3757
    Fin15AnchoredAtom3759 Fin15AnchoredAtom3764 Fin15AnchoredAtom3816 Fin15AnchoredAtom3841
    Fin15AnchoredAtom3843 Fin15AnchoredAtom3848 Fin15AnchoredAtom3900 Fin15AnchoredAtom3956
    Fin15AnchoredAtom4035 Fin15AnchoredAtom4037 Fin15AnchoredAtom4039 Fin15AnchoredAtom4059
    Fin15AnchoredAtom4061 Fin15AnchoredAtom4066 Fin15AnchoredAtom4087 Fin15AnchoredAtom4089
    Fin15AnchoredAtom4094 Fin15AnchoredAtom4146 Fin15AnchoredAtom4171 Fin15AnchoredAtom4173
    Fin15AnchoredAtom4178 Fin15AnchoredAtom4230 Fin15AnchoredAtom4286 Fin15AnchoredAtom4381
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

theorem fin15Anchored_clause32014 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3537 chi ∧
      ¬Fin15AnchoredAtom3541 chi ∧
      ¬Fin15AnchoredAtom3544 chi ∧
      ¬Fin15AnchoredAtom3545 chi ∧
      ¬Fin15AnchoredAtom3549 chi ∧
      ¬Fin15AnchoredAtom3552 chi ∧
      ¬Fin15AnchoredAtom3553 chi ∧
      ¬Fin15AnchoredAtom3574 chi ∧
      ¬Fin15AnchoredAtom3575 chi ∧
      ¬Fin15AnchoredAtom3581 chi ∧
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
      ¬Fin15AnchoredAtom3705 chi ∧
      ¬Fin15AnchoredAtom3708 chi ∧
      ¬Fin15AnchoredAtom3709 chi ∧
      ¬Fin15AnchoredAtom3730 chi ∧
      ¬Fin15AnchoredAtom3731 chi ∧
      ¬Fin15AnchoredAtom3737 chi ∧
      ¬Fin15AnchoredAtom3758 chi ∧
      ¬Fin15AnchoredAtom3759 chi ∧
      ¬Fin15AnchoredAtom3765 chi ∧
      ¬Fin15AnchoredAtom3817 chi ∧
      ¬Fin15AnchoredAtom3842 chi ∧
      ¬Fin15AnchoredAtom3843 chi ∧
      ¬Fin15AnchoredAtom3849 chi ∧
      ¬Fin15AnchoredAtom3901 chi ∧
      ¬Fin15AnchoredAtom3957 chi ∧
      ¬Fin15AnchoredAtom4035 chi ∧
      ¬Fin15AnchoredAtom4038 chi ∧
      ¬Fin15AnchoredAtom4039 chi ∧
      ¬Fin15AnchoredAtom4060 chi ∧
      ¬Fin15AnchoredAtom4061 chi ∧
      ¬Fin15AnchoredAtom4067 chi ∧
      ¬Fin15AnchoredAtom4088 chi ∧
      ¬Fin15AnchoredAtom4089 chi ∧
      ¬Fin15AnchoredAtom4095 chi ∧
      ¬Fin15AnchoredAtom4147 chi ∧
      ¬Fin15AnchoredAtom4172 chi ∧
      ¬Fin15AnchoredAtom4173 chi ∧
      ¬Fin15AnchoredAtom4179 chi ∧
      ¬Fin15AnchoredAtom4231 chi ∧
      ¬Fin15AnchoredAtom4287 chi ∧
      ¬Fin15AnchoredAtom4382 chi ∧
      ¬Fin15AnchoredAtom4383 chi ∧
      ¬Fin15AnchoredAtom4389 chi ∧
      ¬Fin15AnchoredAtom4441 chi ∧
      ¬Fin15AnchoredAtom4497 chi ∧
      ¬Fin15AnchoredAtom4623 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 6, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25724
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3537 Fin15AnchoredAtom3541 Fin15AnchoredAtom3544
    Fin15AnchoredAtom3545 Fin15AnchoredAtom3549 Fin15AnchoredAtom3552 Fin15AnchoredAtom3553
    Fin15AnchoredAtom3574 Fin15AnchoredAtom3575 Fin15AnchoredAtom3581 Fin15AnchoredAtom3585
    Fin15AnchoredAtom3588 Fin15AnchoredAtom3589 Fin15AnchoredAtom3610 Fin15AnchoredAtom3611
    Fin15AnchoredAtom3617 Fin15AnchoredAtom3638 Fin15AnchoredAtom3639 Fin15AnchoredAtom3645
    Fin15AnchoredAtom3697 Fin15AnchoredAtom3705 Fin15AnchoredAtom3708 Fin15AnchoredAtom3709
    Fin15AnchoredAtom3730 Fin15AnchoredAtom3731 Fin15AnchoredAtom3737 Fin15AnchoredAtom3758
    Fin15AnchoredAtom3759 Fin15AnchoredAtom3765 Fin15AnchoredAtom3817 Fin15AnchoredAtom3842
    Fin15AnchoredAtom3843 Fin15AnchoredAtom3849 Fin15AnchoredAtom3901 Fin15AnchoredAtom3957
    Fin15AnchoredAtom4035 Fin15AnchoredAtom4038 Fin15AnchoredAtom4039 Fin15AnchoredAtom4060
    Fin15AnchoredAtom4061 Fin15AnchoredAtom4067 Fin15AnchoredAtom4088 Fin15AnchoredAtom4089
    Fin15AnchoredAtom4095 Fin15AnchoredAtom4147 Fin15AnchoredAtom4172 Fin15AnchoredAtom4173
    Fin15AnchoredAtom4179 Fin15AnchoredAtom4231 Fin15AnchoredAtom4287 Fin15AnchoredAtom4382
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

theorem fin15Anchored_clause32015 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3537 chi ∧
      ¬Fin15AnchoredAtom3543 chi ∧
      ¬Fin15AnchoredAtom3544 chi ∧
      ¬Fin15AnchoredAtom3545 chi ∧
      ¬Fin15AnchoredAtom3551 chi ∧
      ¬Fin15AnchoredAtom3552 chi ∧
      ¬Fin15AnchoredAtom3553 chi ∧
      ¬Fin15AnchoredAtom3579 chi ∧
      ¬Fin15AnchoredAtom3580 chi ∧
      ¬Fin15AnchoredAtom3581 chi ∧
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
      ¬Fin15AnchoredAtom3707 chi ∧
      ¬Fin15AnchoredAtom3708 chi ∧
      ¬Fin15AnchoredAtom3709 chi ∧
      ¬Fin15AnchoredAtom3735 chi ∧
      ¬Fin15AnchoredAtom3736 chi ∧
      ¬Fin15AnchoredAtom3737 chi ∧
      ¬Fin15AnchoredAtom3763 chi ∧
      ¬Fin15AnchoredAtom3764 chi ∧
      ¬Fin15AnchoredAtom3765 chi ∧
      ¬Fin15AnchoredAtom3821 chi ∧
      ¬Fin15AnchoredAtom3847 chi ∧
      ¬Fin15AnchoredAtom3848 chi ∧
      ¬Fin15AnchoredAtom3849 chi ∧
      ¬Fin15AnchoredAtom3905 chi ∧
      ¬Fin15AnchoredAtom3961 chi ∧
      ¬Fin15AnchoredAtom4037 chi ∧
      ¬Fin15AnchoredAtom4038 chi ∧
      ¬Fin15AnchoredAtom4039 chi ∧
      ¬Fin15AnchoredAtom4065 chi ∧
      ¬Fin15AnchoredAtom4066 chi ∧
      ¬Fin15AnchoredAtom4067 chi ∧
      ¬Fin15AnchoredAtom4093 chi ∧
      ¬Fin15AnchoredAtom4094 chi ∧
      ¬Fin15AnchoredAtom4095 chi ∧
      ¬Fin15AnchoredAtom4151 chi ∧
      ¬Fin15AnchoredAtom4177 chi ∧
      ¬Fin15AnchoredAtom4178 chi ∧
      ¬Fin15AnchoredAtom4179 chi ∧
      ¬Fin15AnchoredAtom4235 chi ∧
      ¬Fin15AnchoredAtom4291 chi ∧
      ¬Fin15AnchoredAtom4387 chi ∧
      ¬Fin15AnchoredAtom4388 chi ∧
      ¬Fin15AnchoredAtom4389 chi ∧
      ¬Fin15AnchoredAtom4445 chi ∧
      ¬Fin15AnchoredAtom4501 chi ∧
      ¬Fin15AnchoredAtom4627 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 6, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask28796
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3537 Fin15AnchoredAtom3543 Fin15AnchoredAtom3544
    Fin15AnchoredAtom3545 Fin15AnchoredAtom3551 Fin15AnchoredAtom3552 Fin15AnchoredAtom3553
    Fin15AnchoredAtom3579 Fin15AnchoredAtom3580 Fin15AnchoredAtom3581 Fin15AnchoredAtom3587
    Fin15AnchoredAtom3588 Fin15AnchoredAtom3589 Fin15AnchoredAtom3615 Fin15AnchoredAtom3616
    Fin15AnchoredAtom3617 Fin15AnchoredAtom3643 Fin15AnchoredAtom3644 Fin15AnchoredAtom3645
    Fin15AnchoredAtom3701 Fin15AnchoredAtom3707 Fin15AnchoredAtom3708 Fin15AnchoredAtom3709
    Fin15AnchoredAtom3735 Fin15AnchoredAtom3736 Fin15AnchoredAtom3737 Fin15AnchoredAtom3763
    Fin15AnchoredAtom3764 Fin15AnchoredAtom3765 Fin15AnchoredAtom3821 Fin15AnchoredAtom3847
    Fin15AnchoredAtom3848 Fin15AnchoredAtom3849 Fin15AnchoredAtom3905 Fin15AnchoredAtom3961
    Fin15AnchoredAtom4037 Fin15AnchoredAtom4038 Fin15AnchoredAtom4039 Fin15AnchoredAtom4065
    Fin15AnchoredAtom4066 Fin15AnchoredAtom4067 Fin15AnchoredAtom4093 Fin15AnchoredAtom4094
    Fin15AnchoredAtom4095 Fin15AnchoredAtom4151 Fin15AnchoredAtom4177 Fin15AnchoredAtom4178
    Fin15AnchoredAtom4179 Fin15AnchoredAtom4235 Fin15AnchoredAtom4291 Fin15AnchoredAtom4387
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

theorem fin15Anchored_clause32016 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3538 chi ∧
      ¬Fin15AnchoredAtom3540 chi ∧
      ¬Fin15AnchoredAtom3541 chi ∧
      ¬Fin15AnchoredAtom3542 chi ∧
      ¬Fin15AnchoredAtom3555 chi ∧
      ¬Fin15AnchoredAtom3556 chi ∧
      ¬Fin15AnchoredAtom3557 chi ∧
      ¬Fin15AnchoredAtom3567 chi ∧
      ¬Fin15AnchoredAtom3568 chi ∧
      ¬Fin15AnchoredAtom3572 chi ∧
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
      ¬Fin15AnchoredAtom3711 chi ∧
      ¬Fin15AnchoredAtom3712 chi ∧
      ¬Fin15AnchoredAtom3713 chi ∧
      ¬Fin15AnchoredAtom3723 chi ∧
      ¬Fin15AnchoredAtom3724 chi ∧
      ¬Fin15AnchoredAtom3728 chi ∧
      ¬Fin15AnchoredAtom3772 chi ∧
      ¬Fin15AnchoredAtom3773 chi ∧
      ¬Fin15AnchoredAtom3777 chi ∧
      ¬Fin15AnchoredAtom3802 chi ∧
      ¬Fin15AnchoredAtom3856 chi ∧
      ¬Fin15AnchoredAtom3857 chi ∧
      ¬Fin15AnchoredAtom3861 chi ∧
      ¬Fin15AnchoredAtom3886 chi ∧
      ¬Fin15AnchoredAtom3977 chi ∧
      ¬Fin15AnchoredAtom4041 chi ∧
      ¬Fin15AnchoredAtom4042 chi ∧
      ¬Fin15AnchoredAtom4043 chi ∧
      ¬Fin15AnchoredAtom4053 chi ∧
      ¬Fin15AnchoredAtom4054 chi ∧
      ¬Fin15AnchoredAtom4058 chi ∧
      ¬Fin15AnchoredAtom4102 chi ∧
      ¬Fin15AnchoredAtom4103 chi ∧
      ¬Fin15AnchoredAtom4107 chi ∧
      ¬Fin15AnchoredAtom4132 chi ∧
      ¬Fin15AnchoredAtom4186 chi ∧
      ¬Fin15AnchoredAtom4187 chi ∧
      ¬Fin15AnchoredAtom4191 chi ∧
      ¬Fin15AnchoredAtom4216 chi ∧
      ¬Fin15AnchoredAtom4307 chi ∧
      ¬Fin15AnchoredAtom4396 chi ∧
      ¬Fin15AnchoredAtom4397 chi ∧
      ¬Fin15AnchoredAtom4401 chi ∧
      ¬Fin15AnchoredAtom4426 chi ∧
      ¬Fin15AnchoredAtom4517 chi ∧
      ¬Fin15AnchoredAtom4643 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 7, 9, 10, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask03772
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3538 Fin15AnchoredAtom3540 Fin15AnchoredAtom3541
    Fin15AnchoredAtom3542 Fin15AnchoredAtom3555 Fin15AnchoredAtom3556 Fin15AnchoredAtom3557
    Fin15AnchoredAtom3567 Fin15AnchoredAtom3568 Fin15AnchoredAtom3572 Fin15AnchoredAtom3591
    Fin15AnchoredAtom3592 Fin15AnchoredAtom3593 Fin15AnchoredAtom3603 Fin15AnchoredAtom3604
    Fin15AnchoredAtom3608 Fin15AnchoredAtom3652 Fin15AnchoredAtom3653 Fin15AnchoredAtom3657
    Fin15AnchoredAtom3682 Fin15AnchoredAtom3711 Fin15AnchoredAtom3712 Fin15AnchoredAtom3713
    Fin15AnchoredAtom3723 Fin15AnchoredAtom3724 Fin15AnchoredAtom3728 Fin15AnchoredAtom3772
    Fin15AnchoredAtom3773 Fin15AnchoredAtom3777 Fin15AnchoredAtom3802 Fin15AnchoredAtom3856
    Fin15AnchoredAtom3857 Fin15AnchoredAtom3861 Fin15AnchoredAtom3886 Fin15AnchoredAtom3977
    Fin15AnchoredAtom4041 Fin15AnchoredAtom4042 Fin15AnchoredAtom4043 Fin15AnchoredAtom4053
    Fin15AnchoredAtom4054 Fin15AnchoredAtom4058 Fin15AnchoredAtom4102 Fin15AnchoredAtom4103
    Fin15AnchoredAtom4107 Fin15AnchoredAtom4132 Fin15AnchoredAtom4186 Fin15AnchoredAtom4187
    Fin15AnchoredAtom4191 Fin15AnchoredAtom4216 Fin15AnchoredAtom4307 Fin15AnchoredAtom4396
    Fin15AnchoredAtom4397 Fin15AnchoredAtom4401 Fin15AnchoredAtom4426 Fin15AnchoredAtom4517
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

theorem fin15Anchored_clause32017 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3538 chi ∧
      ¬Fin15AnchoredAtom3540 chi ∧
      ¬Fin15AnchoredAtom3541 chi ∧
      ¬Fin15AnchoredAtom3543 chi ∧
      ¬Fin15AnchoredAtom3555 chi ∧
      ¬Fin15AnchoredAtom3556 chi ∧
      ¬Fin15AnchoredAtom3558 chi ∧
      ¬Fin15AnchoredAtom3567 chi ∧
      ¬Fin15AnchoredAtom3569 chi ∧
      ¬Fin15AnchoredAtom3573 chi ∧
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
      ¬Fin15AnchoredAtom3711 chi ∧
      ¬Fin15AnchoredAtom3712 chi ∧
      ¬Fin15AnchoredAtom3714 chi ∧
      ¬Fin15AnchoredAtom3723 chi ∧
      ¬Fin15AnchoredAtom3725 chi ∧
      ¬Fin15AnchoredAtom3729 chi ∧
      ¬Fin15AnchoredAtom3772 chi ∧
      ¬Fin15AnchoredAtom3774 chi ∧
      ¬Fin15AnchoredAtom3778 chi ∧
      ¬Fin15AnchoredAtom3803 chi ∧
      ¬Fin15AnchoredAtom3856 chi ∧
      ¬Fin15AnchoredAtom3858 chi ∧
      ¬Fin15AnchoredAtom3862 chi ∧
      ¬Fin15AnchoredAtom3887 chi ∧
      ¬Fin15AnchoredAtom3978 chi ∧
      ¬Fin15AnchoredAtom4041 chi ∧
      ¬Fin15AnchoredAtom4042 chi ∧
      ¬Fin15AnchoredAtom4044 chi ∧
      ¬Fin15AnchoredAtom4053 chi ∧
      ¬Fin15AnchoredAtom4055 chi ∧
      ¬Fin15AnchoredAtom4059 chi ∧
      ¬Fin15AnchoredAtom4102 chi ∧
      ¬Fin15AnchoredAtom4104 chi ∧
      ¬Fin15AnchoredAtom4108 chi ∧
      ¬Fin15AnchoredAtom4133 chi ∧
      ¬Fin15AnchoredAtom4186 chi ∧
      ¬Fin15AnchoredAtom4188 chi ∧
      ¬Fin15AnchoredAtom4192 chi ∧
      ¬Fin15AnchoredAtom4217 chi ∧
      ¬Fin15AnchoredAtom4308 chi ∧
      ¬Fin15AnchoredAtom4396 chi ∧
      ¬Fin15AnchoredAtom4398 chi ∧
      ¬Fin15AnchoredAtom4402 chi ∧
      ¬Fin15AnchoredAtom4427 chi ∧
      ¬Fin15AnchoredAtom4518 chi ∧
      ¬Fin15AnchoredAtom4644 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 7, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05820
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3538 Fin15AnchoredAtom3540 Fin15AnchoredAtom3541
    Fin15AnchoredAtom3543 Fin15AnchoredAtom3555 Fin15AnchoredAtom3556 Fin15AnchoredAtom3558
    Fin15AnchoredAtom3567 Fin15AnchoredAtom3569 Fin15AnchoredAtom3573 Fin15AnchoredAtom3591
    Fin15AnchoredAtom3592 Fin15AnchoredAtom3594 Fin15AnchoredAtom3603 Fin15AnchoredAtom3605
    Fin15AnchoredAtom3609 Fin15AnchoredAtom3652 Fin15AnchoredAtom3654 Fin15AnchoredAtom3658
    Fin15AnchoredAtom3683 Fin15AnchoredAtom3711 Fin15AnchoredAtom3712 Fin15AnchoredAtom3714
    Fin15AnchoredAtom3723 Fin15AnchoredAtom3725 Fin15AnchoredAtom3729 Fin15AnchoredAtom3772
    Fin15AnchoredAtom3774 Fin15AnchoredAtom3778 Fin15AnchoredAtom3803 Fin15AnchoredAtom3856
    Fin15AnchoredAtom3858 Fin15AnchoredAtom3862 Fin15AnchoredAtom3887 Fin15AnchoredAtom3978
    Fin15AnchoredAtom4041 Fin15AnchoredAtom4042 Fin15AnchoredAtom4044 Fin15AnchoredAtom4053
    Fin15AnchoredAtom4055 Fin15AnchoredAtom4059 Fin15AnchoredAtom4102 Fin15AnchoredAtom4104
    Fin15AnchoredAtom4108 Fin15AnchoredAtom4133 Fin15AnchoredAtom4186 Fin15AnchoredAtom4188
    Fin15AnchoredAtom4192 Fin15AnchoredAtom4217 Fin15AnchoredAtom4308 Fin15AnchoredAtom4396
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

theorem fin15Anchored_clause32018 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3538 chi ∧
      ¬Fin15AnchoredAtom3540 chi ∧
      ¬Fin15AnchoredAtom3541 chi ∧
      ¬Fin15AnchoredAtom3544 chi ∧
      ¬Fin15AnchoredAtom3555 chi ∧
      ¬Fin15AnchoredAtom3556 chi ∧
      ¬Fin15AnchoredAtom3559 chi ∧
      ¬Fin15AnchoredAtom3567 chi ∧
      ¬Fin15AnchoredAtom3570 chi ∧
      ¬Fin15AnchoredAtom3574 chi ∧
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
      ¬Fin15AnchoredAtom3711 chi ∧
      ¬Fin15AnchoredAtom3712 chi ∧
      ¬Fin15AnchoredAtom3715 chi ∧
      ¬Fin15AnchoredAtom3723 chi ∧
      ¬Fin15AnchoredAtom3726 chi ∧
      ¬Fin15AnchoredAtom3730 chi ∧
      ¬Fin15AnchoredAtom3772 chi ∧
      ¬Fin15AnchoredAtom3775 chi ∧
      ¬Fin15AnchoredAtom3779 chi ∧
      ¬Fin15AnchoredAtom3804 chi ∧
      ¬Fin15AnchoredAtom3856 chi ∧
      ¬Fin15AnchoredAtom3859 chi ∧
      ¬Fin15AnchoredAtom3863 chi ∧
      ¬Fin15AnchoredAtom3888 chi ∧
      ¬Fin15AnchoredAtom3979 chi ∧
      ¬Fin15AnchoredAtom4041 chi ∧
      ¬Fin15AnchoredAtom4042 chi ∧
      ¬Fin15AnchoredAtom4045 chi ∧
      ¬Fin15AnchoredAtom4053 chi ∧
      ¬Fin15AnchoredAtom4056 chi ∧
      ¬Fin15AnchoredAtom4060 chi ∧
      ¬Fin15AnchoredAtom4102 chi ∧
      ¬Fin15AnchoredAtom4105 chi ∧
      ¬Fin15AnchoredAtom4109 chi ∧
      ¬Fin15AnchoredAtom4134 chi ∧
      ¬Fin15AnchoredAtom4186 chi ∧
      ¬Fin15AnchoredAtom4189 chi ∧
      ¬Fin15AnchoredAtom4193 chi ∧
      ¬Fin15AnchoredAtom4218 chi ∧
      ¬Fin15AnchoredAtom4309 chi ∧
      ¬Fin15AnchoredAtom4396 chi ∧
      ¬Fin15AnchoredAtom4399 chi ∧
      ¬Fin15AnchoredAtom4403 chi ∧
      ¬Fin15AnchoredAtom4428 chi ∧
      ¬Fin15AnchoredAtom4519 chi ∧
      ¬Fin15AnchoredAtom4645 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 7, 9, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09916
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3538 Fin15AnchoredAtom3540 Fin15AnchoredAtom3541
    Fin15AnchoredAtom3544 Fin15AnchoredAtom3555 Fin15AnchoredAtom3556 Fin15AnchoredAtom3559
    Fin15AnchoredAtom3567 Fin15AnchoredAtom3570 Fin15AnchoredAtom3574 Fin15AnchoredAtom3591
    Fin15AnchoredAtom3592 Fin15AnchoredAtom3595 Fin15AnchoredAtom3603 Fin15AnchoredAtom3606
    Fin15AnchoredAtom3610 Fin15AnchoredAtom3652 Fin15AnchoredAtom3655 Fin15AnchoredAtom3659
    Fin15AnchoredAtom3684 Fin15AnchoredAtom3711 Fin15AnchoredAtom3712 Fin15AnchoredAtom3715
    Fin15AnchoredAtom3723 Fin15AnchoredAtom3726 Fin15AnchoredAtom3730 Fin15AnchoredAtom3772
    Fin15AnchoredAtom3775 Fin15AnchoredAtom3779 Fin15AnchoredAtom3804 Fin15AnchoredAtom3856
    Fin15AnchoredAtom3859 Fin15AnchoredAtom3863 Fin15AnchoredAtom3888 Fin15AnchoredAtom3979
    Fin15AnchoredAtom4041 Fin15AnchoredAtom4042 Fin15AnchoredAtom4045 Fin15AnchoredAtom4053
    Fin15AnchoredAtom4056 Fin15AnchoredAtom4060 Fin15AnchoredAtom4102 Fin15AnchoredAtom4105
    Fin15AnchoredAtom4109 Fin15AnchoredAtom4134 Fin15AnchoredAtom4186 Fin15AnchoredAtom4189
    Fin15AnchoredAtom4193 Fin15AnchoredAtom4218 Fin15AnchoredAtom4309 Fin15AnchoredAtom4396
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

theorem fin15Anchored_clause32019 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3538 chi ∧
      ¬Fin15AnchoredAtom3540 chi ∧
      ¬Fin15AnchoredAtom3541 chi ∧
      ¬Fin15AnchoredAtom3545 chi ∧
      ¬Fin15AnchoredAtom3555 chi ∧
      ¬Fin15AnchoredAtom3556 chi ∧
      ¬Fin15AnchoredAtom3560 chi ∧
      ¬Fin15AnchoredAtom3567 chi ∧
      ¬Fin15AnchoredAtom3571 chi ∧
      ¬Fin15AnchoredAtom3575 chi ∧
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
      ¬Fin15AnchoredAtom3711 chi ∧
      ¬Fin15AnchoredAtom3712 chi ∧
      ¬Fin15AnchoredAtom3716 chi ∧
      ¬Fin15AnchoredAtom3723 chi ∧
      ¬Fin15AnchoredAtom3727 chi ∧
      ¬Fin15AnchoredAtom3731 chi ∧
      ¬Fin15AnchoredAtom3772 chi ∧
      ¬Fin15AnchoredAtom3776 chi ∧
      ¬Fin15AnchoredAtom3780 chi ∧
      ¬Fin15AnchoredAtom3805 chi ∧
      ¬Fin15AnchoredAtom3856 chi ∧
      ¬Fin15AnchoredAtom3860 chi ∧
      ¬Fin15AnchoredAtom3864 chi ∧
      ¬Fin15AnchoredAtom3889 chi ∧
      ¬Fin15AnchoredAtom3980 chi ∧
      ¬Fin15AnchoredAtom4041 chi ∧
      ¬Fin15AnchoredAtom4042 chi ∧
      ¬Fin15AnchoredAtom4046 chi ∧
      ¬Fin15AnchoredAtom4053 chi ∧
      ¬Fin15AnchoredAtom4057 chi ∧
      ¬Fin15AnchoredAtom4061 chi ∧
      ¬Fin15AnchoredAtom4102 chi ∧
      ¬Fin15AnchoredAtom4106 chi ∧
      ¬Fin15AnchoredAtom4110 chi ∧
      ¬Fin15AnchoredAtom4135 chi ∧
      ¬Fin15AnchoredAtom4186 chi ∧
      ¬Fin15AnchoredAtom4190 chi ∧
      ¬Fin15AnchoredAtom4194 chi ∧
      ¬Fin15AnchoredAtom4219 chi ∧
      ¬Fin15AnchoredAtom4310 chi ∧
      ¬Fin15AnchoredAtom4396 chi ∧
      ¬Fin15AnchoredAtom4400 chi ∧
      ¬Fin15AnchoredAtom4404 chi ∧
      ¬Fin15AnchoredAtom4429 chi ∧
      ¬Fin15AnchoredAtom4520 chi ∧
      ¬Fin15AnchoredAtom4646 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 7, 9, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask18108
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3538 Fin15AnchoredAtom3540 Fin15AnchoredAtom3541
    Fin15AnchoredAtom3545 Fin15AnchoredAtom3555 Fin15AnchoredAtom3556 Fin15AnchoredAtom3560
    Fin15AnchoredAtom3567 Fin15AnchoredAtom3571 Fin15AnchoredAtom3575 Fin15AnchoredAtom3591
    Fin15AnchoredAtom3592 Fin15AnchoredAtom3596 Fin15AnchoredAtom3603 Fin15AnchoredAtom3607
    Fin15AnchoredAtom3611 Fin15AnchoredAtom3652 Fin15AnchoredAtom3656 Fin15AnchoredAtom3660
    Fin15AnchoredAtom3685 Fin15AnchoredAtom3711 Fin15AnchoredAtom3712 Fin15AnchoredAtom3716
    Fin15AnchoredAtom3723 Fin15AnchoredAtom3727 Fin15AnchoredAtom3731 Fin15AnchoredAtom3772
    Fin15AnchoredAtom3776 Fin15AnchoredAtom3780 Fin15AnchoredAtom3805 Fin15AnchoredAtom3856
    Fin15AnchoredAtom3860 Fin15AnchoredAtom3864 Fin15AnchoredAtom3889 Fin15AnchoredAtom3980
    Fin15AnchoredAtom4041 Fin15AnchoredAtom4042 Fin15AnchoredAtom4046 Fin15AnchoredAtom4053
    Fin15AnchoredAtom4057 Fin15AnchoredAtom4061 Fin15AnchoredAtom4102 Fin15AnchoredAtom4106
    Fin15AnchoredAtom4110 Fin15AnchoredAtom4135 Fin15AnchoredAtom4186 Fin15AnchoredAtom4190
    Fin15AnchoredAtom4194 Fin15AnchoredAtom4219 Fin15AnchoredAtom4310 Fin15AnchoredAtom4396
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

theorem fin15Anchored_clause32020 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3538 chi ∧
      ¬Fin15AnchoredAtom3540 chi ∧
      ¬Fin15AnchoredAtom3543 chi ∧
      ¬Fin15AnchoredAtom3544 chi ∧
      ¬Fin15AnchoredAtom3555 chi ∧
      ¬Fin15AnchoredAtom3558 chi ∧
      ¬Fin15AnchoredAtom3559 chi ∧
      ¬Fin15AnchoredAtom3569 chi ∧
      ¬Fin15AnchoredAtom3570 chi ∧
      ¬Fin15AnchoredAtom3579 chi ∧
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
      ¬Fin15AnchoredAtom3711 chi ∧
      ¬Fin15AnchoredAtom3714 chi ∧
      ¬Fin15AnchoredAtom3715 chi ∧
      ¬Fin15AnchoredAtom3725 chi ∧
      ¬Fin15AnchoredAtom3726 chi ∧
      ¬Fin15AnchoredAtom3735 chi ∧
      ¬Fin15AnchoredAtom3774 chi ∧
      ¬Fin15AnchoredAtom3775 chi ∧
      ¬Fin15AnchoredAtom3784 chi ∧
      ¬Fin15AnchoredAtom3809 chi ∧
      ¬Fin15AnchoredAtom3858 chi ∧
      ¬Fin15AnchoredAtom3859 chi ∧
      ¬Fin15AnchoredAtom3868 chi ∧
      ¬Fin15AnchoredAtom3893 chi ∧
      ¬Fin15AnchoredAtom3984 chi ∧
      ¬Fin15AnchoredAtom4041 chi ∧
      ¬Fin15AnchoredAtom4044 chi ∧
      ¬Fin15AnchoredAtom4045 chi ∧
      ¬Fin15AnchoredAtom4055 chi ∧
      ¬Fin15AnchoredAtom4056 chi ∧
      ¬Fin15AnchoredAtom4065 chi ∧
      ¬Fin15AnchoredAtom4104 chi ∧
      ¬Fin15AnchoredAtom4105 chi ∧
      ¬Fin15AnchoredAtom4114 chi ∧
      ¬Fin15AnchoredAtom4139 chi ∧
      ¬Fin15AnchoredAtom4188 chi ∧
      ¬Fin15AnchoredAtom4189 chi ∧
      ¬Fin15AnchoredAtom4198 chi ∧
      ¬Fin15AnchoredAtom4223 chi ∧
      ¬Fin15AnchoredAtom4314 chi ∧
      ¬Fin15AnchoredAtom4398 chi ∧
      ¬Fin15AnchoredAtom4399 chi ∧
      ¬Fin15AnchoredAtom4408 chi ∧
      ¬Fin15AnchoredAtom4433 chi ∧
      ¬Fin15AnchoredAtom4524 chi ∧
      ¬Fin15AnchoredAtom4650 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 7, 9, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask12988
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3538 Fin15AnchoredAtom3540 Fin15AnchoredAtom3543
    Fin15AnchoredAtom3544 Fin15AnchoredAtom3555 Fin15AnchoredAtom3558 Fin15AnchoredAtom3559
    Fin15AnchoredAtom3569 Fin15AnchoredAtom3570 Fin15AnchoredAtom3579 Fin15AnchoredAtom3591
    Fin15AnchoredAtom3594 Fin15AnchoredAtom3595 Fin15AnchoredAtom3605 Fin15AnchoredAtom3606
    Fin15AnchoredAtom3615 Fin15AnchoredAtom3654 Fin15AnchoredAtom3655 Fin15AnchoredAtom3664
    Fin15AnchoredAtom3689 Fin15AnchoredAtom3711 Fin15AnchoredAtom3714 Fin15AnchoredAtom3715
    Fin15AnchoredAtom3725 Fin15AnchoredAtom3726 Fin15AnchoredAtom3735 Fin15AnchoredAtom3774
    Fin15AnchoredAtom3775 Fin15AnchoredAtom3784 Fin15AnchoredAtom3809 Fin15AnchoredAtom3858
    Fin15AnchoredAtom3859 Fin15AnchoredAtom3868 Fin15AnchoredAtom3893 Fin15AnchoredAtom3984
    Fin15AnchoredAtom4041 Fin15AnchoredAtom4044 Fin15AnchoredAtom4045 Fin15AnchoredAtom4055
    Fin15AnchoredAtom4056 Fin15AnchoredAtom4065 Fin15AnchoredAtom4104 Fin15AnchoredAtom4105
    Fin15AnchoredAtom4114 Fin15AnchoredAtom4139 Fin15AnchoredAtom4188 Fin15AnchoredAtom4189
    Fin15AnchoredAtom4198 Fin15AnchoredAtom4223 Fin15AnchoredAtom4314 Fin15AnchoredAtom4398
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

theorem fin15Anchored_clause32021 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3538 chi ∧
      ¬Fin15AnchoredAtom3540 chi ∧
      ¬Fin15AnchoredAtom3543 chi ∧
      ¬Fin15AnchoredAtom3545 chi ∧
      ¬Fin15AnchoredAtom3555 chi ∧
      ¬Fin15AnchoredAtom3558 chi ∧
      ¬Fin15AnchoredAtom3560 chi ∧
      ¬Fin15AnchoredAtom3569 chi ∧
      ¬Fin15AnchoredAtom3571 chi ∧
      ¬Fin15AnchoredAtom3580 chi ∧
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
      ¬Fin15AnchoredAtom3711 chi ∧
      ¬Fin15AnchoredAtom3714 chi ∧
      ¬Fin15AnchoredAtom3716 chi ∧
      ¬Fin15AnchoredAtom3725 chi ∧
      ¬Fin15AnchoredAtom3727 chi ∧
      ¬Fin15AnchoredAtom3736 chi ∧
      ¬Fin15AnchoredAtom3774 chi ∧
      ¬Fin15AnchoredAtom3776 chi ∧
      ¬Fin15AnchoredAtom3785 chi ∧
      ¬Fin15AnchoredAtom3810 chi ∧
      ¬Fin15AnchoredAtom3858 chi ∧
      ¬Fin15AnchoredAtom3860 chi ∧
      ¬Fin15AnchoredAtom3869 chi ∧
      ¬Fin15AnchoredAtom3894 chi ∧
      ¬Fin15AnchoredAtom3985 chi ∧
      ¬Fin15AnchoredAtom4041 chi ∧
      ¬Fin15AnchoredAtom4044 chi ∧
      ¬Fin15AnchoredAtom4046 chi ∧
      ¬Fin15AnchoredAtom4055 chi ∧
      ¬Fin15AnchoredAtom4057 chi ∧
      ¬Fin15AnchoredAtom4066 chi ∧
      ¬Fin15AnchoredAtom4104 chi ∧
      ¬Fin15AnchoredAtom4106 chi ∧
      ¬Fin15AnchoredAtom4115 chi ∧
      ¬Fin15AnchoredAtom4140 chi ∧
      ¬Fin15AnchoredAtom4188 chi ∧
      ¬Fin15AnchoredAtom4190 chi ∧
      ¬Fin15AnchoredAtom4199 chi ∧
      ¬Fin15AnchoredAtom4224 chi ∧
      ¬Fin15AnchoredAtom4315 chi ∧
      ¬Fin15AnchoredAtom4398 chi ∧
      ¬Fin15AnchoredAtom4400 chi ∧
      ¬Fin15AnchoredAtom4409 chi ∧
      ¬Fin15AnchoredAtom4434 chi ∧
      ¬Fin15AnchoredAtom4525 chi ∧
      ¬Fin15AnchoredAtom4651 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 7, 9, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21180
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3538 Fin15AnchoredAtom3540 Fin15AnchoredAtom3543
    Fin15AnchoredAtom3545 Fin15AnchoredAtom3555 Fin15AnchoredAtom3558 Fin15AnchoredAtom3560
    Fin15AnchoredAtom3569 Fin15AnchoredAtom3571 Fin15AnchoredAtom3580 Fin15AnchoredAtom3591
    Fin15AnchoredAtom3594 Fin15AnchoredAtom3596 Fin15AnchoredAtom3605 Fin15AnchoredAtom3607
    Fin15AnchoredAtom3616 Fin15AnchoredAtom3654 Fin15AnchoredAtom3656 Fin15AnchoredAtom3665
    Fin15AnchoredAtom3690 Fin15AnchoredAtom3711 Fin15AnchoredAtom3714 Fin15AnchoredAtom3716
    Fin15AnchoredAtom3725 Fin15AnchoredAtom3727 Fin15AnchoredAtom3736 Fin15AnchoredAtom3774
    Fin15AnchoredAtom3776 Fin15AnchoredAtom3785 Fin15AnchoredAtom3810 Fin15AnchoredAtom3858
    Fin15AnchoredAtom3860 Fin15AnchoredAtom3869 Fin15AnchoredAtom3894 Fin15AnchoredAtom3985
    Fin15AnchoredAtom4041 Fin15AnchoredAtom4044 Fin15AnchoredAtom4046 Fin15AnchoredAtom4055
    Fin15AnchoredAtom4057 Fin15AnchoredAtom4066 Fin15AnchoredAtom4104 Fin15AnchoredAtom4106
    Fin15AnchoredAtom4115 Fin15AnchoredAtom4140 Fin15AnchoredAtom4188 Fin15AnchoredAtom4190
    Fin15AnchoredAtom4199 Fin15AnchoredAtom4224 Fin15AnchoredAtom4315 Fin15AnchoredAtom4398
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

theorem fin15Anchored_clause32022 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3538 chi ∧
      ¬Fin15AnchoredAtom3540 chi ∧
      ¬Fin15AnchoredAtom3544 chi ∧
      ¬Fin15AnchoredAtom3545 chi ∧
      ¬Fin15AnchoredAtom3555 chi ∧
      ¬Fin15AnchoredAtom3559 chi ∧
      ¬Fin15AnchoredAtom3560 chi ∧
      ¬Fin15AnchoredAtom3570 chi ∧
      ¬Fin15AnchoredAtom3571 chi ∧
      ¬Fin15AnchoredAtom3581 chi ∧
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
      ¬Fin15AnchoredAtom3711 chi ∧
      ¬Fin15AnchoredAtom3715 chi ∧
      ¬Fin15AnchoredAtom3716 chi ∧
      ¬Fin15AnchoredAtom3726 chi ∧
      ¬Fin15AnchoredAtom3727 chi ∧
      ¬Fin15AnchoredAtom3737 chi ∧
      ¬Fin15AnchoredAtom3775 chi ∧
      ¬Fin15AnchoredAtom3776 chi ∧
      ¬Fin15AnchoredAtom3786 chi ∧
      ¬Fin15AnchoredAtom3811 chi ∧
      ¬Fin15AnchoredAtom3859 chi ∧
      ¬Fin15AnchoredAtom3860 chi ∧
      ¬Fin15AnchoredAtom3870 chi ∧
      ¬Fin15AnchoredAtom3895 chi ∧
      ¬Fin15AnchoredAtom3986 chi ∧
      ¬Fin15AnchoredAtom4041 chi ∧
      ¬Fin15AnchoredAtom4045 chi ∧
      ¬Fin15AnchoredAtom4046 chi ∧
      ¬Fin15AnchoredAtom4056 chi ∧
      ¬Fin15AnchoredAtom4057 chi ∧
      ¬Fin15AnchoredAtom4067 chi ∧
      ¬Fin15AnchoredAtom4105 chi ∧
      ¬Fin15AnchoredAtom4106 chi ∧
      ¬Fin15AnchoredAtom4116 chi ∧
      ¬Fin15AnchoredAtom4141 chi ∧
      ¬Fin15AnchoredAtom4189 chi ∧
      ¬Fin15AnchoredAtom4190 chi ∧
      ¬Fin15AnchoredAtom4200 chi ∧
      ¬Fin15AnchoredAtom4225 chi ∧
      ¬Fin15AnchoredAtom4316 chi ∧
      ¬Fin15AnchoredAtom4399 chi ∧
      ¬Fin15AnchoredAtom4400 chi ∧
      ¬Fin15AnchoredAtom4410 chi ∧
      ¬Fin15AnchoredAtom4435 chi ∧
      ¬Fin15AnchoredAtom4526 chi ∧
      ¬Fin15AnchoredAtom4652 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 7, 9, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25276
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3538 Fin15AnchoredAtom3540 Fin15AnchoredAtom3544
    Fin15AnchoredAtom3545 Fin15AnchoredAtom3555 Fin15AnchoredAtom3559 Fin15AnchoredAtom3560
    Fin15AnchoredAtom3570 Fin15AnchoredAtom3571 Fin15AnchoredAtom3581 Fin15AnchoredAtom3591
    Fin15AnchoredAtom3595 Fin15AnchoredAtom3596 Fin15AnchoredAtom3606 Fin15AnchoredAtom3607
    Fin15AnchoredAtom3617 Fin15AnchoredAtom3655 Fin15AnchoredAtom3656 Fin15AnchoredAtom3666
    Fin15AnchoredAtom3691 Fin15AnchoredAtom3711 Fin15AnchoredAtom3715 Fin15AnchoredAtom3716
    Fin15AnchoredAtom3726 Fin15AnchoredAtom3727 Fin15AnchoredAtom3737 Fin15AnchoredAtom3775
    Fin15AnchoredAtom3776 Fin15AnchoredAtom3786 Fin15AnchoredAtom3811 Fin15AnchoredAtom3859
    Fin15AnchoredAtom3860 Fin15AnchoredAtom3870 Fin15AnchoredAtom3895 Fin15AnchoredAtom3986
    Fin15AnchoredAtom4041 Fin15AnchoredAtom4045 Fin15AnchoredAtom4046 Fin15AnchoredAtom4056
    Fin15AnchoredAtom4057 Fin15AnchoredAtom4067 Fin15AnchoredAtom4105 Fin15AnchoredAtom4106
    Fin15AnchoredAtom4116 Fin15AnchoredAtom4141 Fin15AnchoredAtom4189 Fin15AnchoredAtom4190
    Fin15AnchoredAtom4200 Fin15AnchoredAtom4225 Fin15AnchoredAtom4316 Fin15AnchoredAtom4399
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

theorem fin15Anchored_clause32023 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3538 chi ∧
      ¬Fin15AnchoredAtom3541 chi ∧
      ¬Fin15AnchoredAtom3543 chi ∧
      ¬Fin15AnchoredAtom3544 chi ∧
      ¬Fin15AnchoredAtom3556 chi ∧
      ¬Fin15AnchoredAtom3558 chi ∧
      ¬Fin15AnchoredAtom3559 chi ∧
      ¬Fin15AnchoredAtom3573 chi ∧
      ¬Fin15AnchoredAtom3574 chi ∧
      ¬Fin15AnchoredAtom3579 chi ∧
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
      ¬Fin15AnchoredAtom3712 chi ∧
      ¬Fin15AnchoredAtom3714 chi ∧
      ¬Fin15AnchoredAtom3715 chi ∧
      ¬Fin15AnchoredAtom3729 chi ∧
      ¬Fin15AnchoredAtom3730 chi ∧
      ¬Fin15AnchoredAtom3735 chi ∧
      ¬Fin15AnchoredAtom3778 chi ∧
      ¬Fin15AnchoredAtom3779 chi ∧
      ¬Fin15AnchoredAtom3784 chi ∧
      ¬Fin15AnchoredAtom3815 chi ∧
      ¬Fin15AnchoredAtom3862 chi ∧
      ¬Fin15AnchoredAtom3863 chi ∧
      ¬Fin15AnchoredAtom3868 chi ∧
      ¬Fin15AnchoredAtom3899 chi ∧
      ¬Fin15AnchoredAtom3990 chi ∧
      ¬Fin15AnchoredAtom4042 chi ∧
      ¬Fin15AnchoredAtom4044 chi ∧
      ¬Fin15AnchoredAtom4045 chi ∧
      ¬Fin15AnchoredAtom4059 chi ∧
      ¬Fin15AnchoredAtom4060 chi ∧
      ¬Fin15AnchoredAtom4065 chi ∧
      ¬Fin15AnchoredAtom4108 chi ∧
      ¬Fin15AnchoredAtom4109 chi ∧
      ¬Fin15AnchoredAtom4114 chi ∧
      ¬Fin15AnchoredAtom4145 chi ∧
      ¬Fin15AnchoredAtom4192 chi ∧
      ¬Fin15AnchoredAtom4193 chi ∧
      ¬Fin15AnchoredAtom4198 chi ∧
      ¬Fin15AnchoredAtom4229 chi ∧
      ¬Fin15AnchoredAtom4320 chi ∧
      ¬Fin15AnchoredAtom4402 chi ∧
      ¬Fin15AnchoredAtom4403 chi ∧
      ¬Fin15AnchoredAtom4408 chi ∧
      ¬Fin15AnchoredAtom4439 chi ∧
      ¬Fin15AnchoredAtom4530 chi ∧
      ¬Fin15AnchoredAtom4656 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 7, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13500
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3538 Fin15AnchoredAtom3541 Fin15AnchoredAtom3543
    Fin15AnchoredAtom3544 Fin15AnchoredAtom3556 Fin15AnchoredAtom3558 Fin15AnchoredAtom3559
    Fin15AnchoredAtom3573 Fin15AnchoredAtom3574 Fin15AnchoredAtom3579 Fin15AnchoredAtom3592
    Fin15AnchoredAtom3594 Fin15AnchoredAtom3595 Fin15AnchoredAtom3609 Fin15AnchoredAtom3610
    Fin15AnchoredAtom3615 Fin15AnchoredAtom3658 Fin15AnchoredAtom3659 Fin15AnchoredAtom3664
    Fin15AnchoredAtom3695 Fin15AnchoredAtom3712 Fin15AnchoredAtom3714 Fin15AnchoredAtom3715
    Fin15AnchoredAtom3729 Fin15AnchoredAtom3730 Fin15AnchoredAtom3735 Fin15AnchoredAtom3778
    Fin15AnchoredAtom3779 Fin15AnchoredAtom3784 Fin15AnchoredAtom3815 Fin15AnchoredAtom3862
    Fin15AnchoredAtom3863 Fin15AnchoredAtom3868 Fin15AnchoredAtom3899 Fin15AnchoredAtom3990
    Fin15AnchoredAtom4042 Fin15AnchoredAtom4044 Fin15AnchoredAtom4045 Fin15AnchoredAtom4059
    Fin15AnchoredAtom4060 Fin15AnchoredAtom4065 Fin15AnchoredAtom4108 Fin15AnchoredAtom4109
    Fin15AnchoredAtom4114 Fin15AnchoredAtom4145 Fin15AnchoredAtom4192 Fin15AnchoredAtom4193
    Fin15AnchoredAtom4198 Fin15AnchoredAtom4229 Fin15AnchoredAtom4320 Fin15AnchoredAtom4402
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

theorem fin15Anchored_clause32024 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3538 chi ∧
      ¬Fin15AnchoredAtom3541 chi ∧
      ¬Fin15AnchoredAtom3543 chi ∧
      ¬Fin15AnchoredAtom3545 chi ∧
      ¬Fin15AnchoredAtom3556 chi ∧
      ¬Fin15AnchoredAtom3558 chi ∧
      ¬Fin15AnchoredAtom3560 chi ∧
      ¬Fin15AnchoredAtom3573 chi ∧
      ¬Fin15AnchoredAtom3575 chi ∧
      ¬Fin15AnchoredAtom3580 chi ∧
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
      ¬Fin15AnchoredAtom3712 chi ∧
      ¬Fin15AnchoredAtom3714 chi ∧
      ¬Fin15AnchoredAtom3716 chi ∧
      ¬Fin15AnchoredAtom3729 chi ∧
      ¬Fin15AnchoredAtom3731 chi ∧
      ¬Fin15AnchoredAtom3736 chi ∧
      ¬Fin15AnchoredAtom3778 chi ∧
      ¬Fin15AnchoredAtom3780 chi ∧
      ¬Fin15AnchoredAtom3785 chi ∧
      ¬Fin15AnchoredAtom3816 chi ∧
      ¬Fin15AnchoredAtom3862 chi ∧
      ¬Fin15AnchoredAtom3864 chi ∧
      ¬Fin15AnchoredAtom3869 chi ∧
      ¬Fin15AnchoredAtom3900 chi ∧
      ¬Fin15AnchoredAtom3991 chi ∧
      ¬Fin15AnchoredAtom4042 chi ∧
      ¬Fin15AnchoredAtom4044 chi ∧
      ¬Fin15AnchoredAtom4046 chi ∧
      ¬Fin15AnchoredAtom4059 chi ∧
      ¬Fin15AnchoredAtom4061 chi ∧
      ¬Fin15AnchoredAtom4066 chi ∧
      ¬Fin15AnchoredAtom4108 chi ∧
      ¬Fin15AnchoredAtom4110 chi ∧
      ¬Fin15AnchoredAtom4115 chi ∧
      ¬Fin15AnchoredAtom4146 chi ∧
      ¬Fin15AnchoredAtom4192 chi ∧
      ¬Fin15AnchoredAtom4194 chi ∧
      ¬Fin15AnchoredAtom4199 chi ∧
      ¬Fin15AnchoredAtom4230 chi ∧
      ¬Fin15AnchoredAtom4321 chi ∧
      ¬Fin15AnchoredAtom4402 chi ∧
      ¬Fin15AnchoredAtom4404 chi ∧
      ¬Fin15AnchoredAtom4409 chi ∧
      ¬Fin15AnchoredAtom4440 chi ∧
      ¬Fin15AnchoredAtom4531 chi ∧
      ¬Fin15AnchoredAtom4657 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 7, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21692
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3538 Fin15AnchoredAtom3541 Fin15AnchoredAtom3543
    Fin15AnchoredAtom3545 Fin15AnchoredAtom3556 Fin15AnchoredAtom3558 Fin15AnchoredAtom3560
    Fin15AnchoredAtom3573 Fin15AnchoredAtom3575 Fin15AnchoredAtom3580 Fin15AnchoredAtom3592
    Fin15AnchoredAtom3594 Fin15AnchoredAtom3596 Fin15AnchoredAtom3609 Fin15AnchoredAtom3611
    Fin15AnchoredAtom3616 Fin15AnchoredAtom3658 Fin15AnchoredAtom3660 Fin15AnchoredAtom3665
    Fin15AnchoredAtom3696 Fin15AnchoredAtom3712 Fin15AnchoredAtom3714 Fin15AnchoredAtom3716
    Fin15AnchoredAtom3729 Fin15AnchoredAtom3731 Fin15AnchoredAtom3736 Fin15AnchoredAtom3778
    Fin15AnchoredAtom3780 Fin15AnchoredAtom3785 Fin15AnchoredAtom3816 Fin15AnchoredAtom3862
    Fin15AnchoredAtom3864 Fin15AnchoredAtom3869 Fin15AnchoredAtom3900 Fin15AnchoredAtom3991
    Fin15AnchoredAtom4042 Fin15AnchoredAtom4044 Fin15AnchoredAtom4046 Fin15AnchoredAtom4059
    Fin15AnchoredAtom4061 Fin15AnchoredAtom4066 Fin15AnchoredAtom4108 Fin15AnchoredAtom4110
    Fin15AnchoredAtom4115 Fin15AnchoredAtom4146 Fin15AnchoredAtom4192 Fin15AnchoredAtom4194
    Fin15AnchoredAtom4199 Fin15AnchoredAtom4230 Fin15AnchoredAtom4321 Fin15AnchoredAtom4402
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

theorem fin15Anchored_clause32025 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3538 chi ∧
      ¬Fin15AnchoredAtom3541 chi ∧
      ¬Fin15AnchoredAtom3544 chi ∧
      ¬Fin15AnchoredAtom3545 chi ∧
      ¬Fin15AnchoredAtom3556 chi ∧
      ¬Fin15AnchoredAtom3559 chi ∧
      ¬Fin15AnchoredAtom3560 chi ∧
      ¬Fin15AnchoredAtom3574 chi ∧
      ¬Fin15AnchoredAtom3575 chi ∧
      ¬Fin15AnchoredAtom3581 chi ∧
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
      ¬Fin15AnchoredAtom3712 chi ∧
      ¬Fin15AnchoredAtom3715 chi ∧
      ¬Fin15AnchoredAtom3716 chi ∧
      ¬Fin15AnchoredAtom3730 chi ∧
      ¬Fin15AnchoredAtom3731 chi ∧
      ¬Fin15AnchoredAtom3737 chi ∧
      ¬Fin15AnchoredAtom3779 chi ∧
      ¬Fin15AnchoredAtom3780 chi ∧
      ¬Fin15AnchoredAtom3786 chi ∧
      ¬Fin15AnchoredAtom3817 chi ∧
      ¬Fin15AnchoredAtom3863 chi ∧
      ¬Fin15AnchoredAtom3864 chi ∧
      ¬Fin15AnchoredAtom3870 chi ∧
      ¬Fin15AnchoredAtom3901 chi ∧
      ¬Fin15AnchoredAtom3992 chi ∧
      ¬Fin15AnchoredAtom4042 chi ∧
      ¬Fin15AnchoredAtom4045 chi ∧
      ¬Fin15AnchoredAtom4046 chi ∧
      ¬Fin15AnchoredAtom4060 chi ∧
      ¬Fin15AnchoredAtom4061 chi ∧
      ¬Fin15AnchoredAtom4067 chi ∧
      ¬Fin15AnchoredAtom4109 chi ∧
      ¬Fin15AnchoredAtom4110 chi ∧
      ¬Fin15AnchoredAtom4116 chi ∧
      ¬Fin15AnchoredAtom4147 chi ∧
      ¬Fin15AnchoredAtom4193 chi ∧
      ¬Fin15AnchoredAtom4194 chi ∧
      ¬Fin15AnchoredAtom4200 chi ∧
      ¬Fin15AnchoredAtom4231 chi ∧
      ¬Fin15AnchoredAtom4322 chi ∧
      ¬Fin15AnchoredAtom4403 chi ∧
      ¬Fin15AnchoredAtom4404 chi ∧
      ¬Fin15AnchoredAtom4410 chi ∧
      ¬Fin15AnchoredAtom4441 chi ∧
      ¬Fin15AnchoredAtom4532 chi ∧
      ¬Fin15AnchoredAtom4658 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 7, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25788
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3538 Fin15AnchoredAtom3541 Fin15AnchoredAtom3544
    Fin15AnchoredAtom3545 Fin15AnchoredAtom3556 Fin15AnchoredAtom3559 Fin15AnchoredAtom3560
    Fin15AnchoredAtom3574 Fin15AnchoredAtom3575 Fin15AnchoredAtom3581 Fin15AnchoredAtom3592
    Fin15AnchoredAtom3595 Fin15AnchoredAtom3596 Fin15AnchoredAtom3610 Fin15AnchoredAtom3611
    Fin15AnchoredAtom3617 Fin15AnchoredAtom3659 Fin15AnchoredAtom3660 Fin15AnchoredAtom3666
    Fin15AnchoredAtom3697 Fin15AnchoredAtom3712 Fin15AnchoredAtom3715 Fin15AnchoredAtom3716
    Fin15AnchoredAtom3730 Fin15AnchoredAtom3731 Fin15AnchoredAtom3737 Fin15AnchoredAtom3779
    Fin15AnchoredAtom3780 Fin15AnchoredAtom3786 Fin15AnchoredAtom3817 Fin15AnchoredAtom3863
    Fin15AnchoredAtom3864 Fin15AnchoredAtom3870 Fin15AnchoredAtom3901 Fin15AnchoredAtom3992
    Fin15AnchoredAtom4042 Fin15AnchoredAtom4045 Fin15AnchoredAtom4046 Fin15AnchoredAtom4060
    Fin15AnchoredAtom4061 Fin15AnchoredAtom4067 Fin15AnchoredAtom4109 Fin15AnchoredAtom4110
    Fin15AnchoredAtom4116 Fin15AnchoredAtom4147 Fin15AnchoredAtom4193 Fin15AnchoredAtom4194
    Fin15AnchoredAtom4200 Fin15AnchoredAtom4231 Fin15AnchoredAtom4322 Fin15AnchoredAtom4403
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

theorem fin15Anchored_clause32026 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3538 chi ∧
      ¬Fin15AnchoredAtom3543 chi ∧
      ¬Fin15AnchoredAtom3544 chi ∧
      ¬Fin15AnchoredAtom3545 chi ∧
      ¬Fin15AnchoredAtom3558 chi ∧
      ¬Fin15AnchoredAtom3559 chi ∧
      ¬Fin15AnchoredAtom3560 chi ∧
      ¬Fin15AnchoredAtom3579 chi ∧
      ¬Fin15AnchoredAtom3580 chi ∧
      ¬Fin15AnchoredAtom3581 chi ∧
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
      ¬Fin15AnchoredAtom3714 chi ∧
      ¬Fin15AnchoredAtom3715 chi ∧
      ¬Fin15AnchoredAtom3716 chi ∧
      ¬Fin15AnchoredAtom3735 chi ∧
      ¬Fin15AnchoredAtom3736 chi ∧
      ¬Fin15AnchoredAtom3737 chi ∧
      ¬Fin15AnchoredAtom3784 chi ∧
      ¬Fin15AnchoredAtom3785 chi ∧
      ¬Fin15AnchoredAtom3786 chi ∧
      ¬Fin15AnchoredAtom3821 chi ∧
      ¬Fin15AnchoredAtom3868 chi ∧
      ¬Fin15AnchoredAtom3869 chi ∧
      ¬Fin15AnchoredAtom3870 chi ∧
      ¬Fin15AnchoredAtom3905 chi ∧
      ¬Fin15AnchoredAtom3996 chi ∧
      ¬Fin15AnchoredAtom4044 chi ∧
      ¬Fin15AnchoredAtom4045 chi ∧
      ¬Fin15AnchoredAtom4046 chi ∧
      ¬Fin15AnchoredAtom4065 chi ∧
      ¬Fin15AnchoredAtom4066 chi ∧
      ¬Fin15AnchoredAtom4067 chi ∧
      ¬Fin15AnchoredAtom4114 chi ∧
      ¬Fin15AnchoredAtom4115 chi ∧
      ¬Fin15AnchoredAtom4116 chi ∧
      ¬Fin15AnchoredAtom4151 chi ∧
      ¬Fin15AnchoredAtom4198 chi ∧
      ¬Fin15AnchoredAtom4199 chi ∧
      ¬Fin15AnchoredAtom4200 chi ∧
      ¬Fin15AnchoredAtom4235 chi ∧
      ¬Fin15AnchoredAtom4326 chi ∧
      ¬Fin15AnchoredAtom4408 chi ∧
      ¬Fin15AnchoredAtom4409 chi ∧
      ¬Fin15AnchoredAtom4410 chi ∧
      ¬Fin15AnchoredAtom4445 chi ∧
      ¬Fin15AnchoredAtom4536 chi ∧
      ¬Fin15AnchoredAtom4662 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 7, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask28860
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3538 Fin15AnchoredAtom3543 Fin15AnchoredAtom3544
    Fin15AnchoredAtom3545 Fin15AnchoredAtom3558 Fin15AnchoredAtom3559 Fin15AnchoredAtom3560
    Fin15AnchoredAtom3579 Fin15AnchoredAtom3580 Fin15AnchoredAtom3581 Fin15AnchoredAtom3594
    Fin15AnchoredAtom3595 Fin15AnchoredAtom3596 Fin15AnchoredAtom3615 Fin15AnchoredAtom3616
    Fin15AnchoredAtom3617 Fin15AnchoredAtom3664 Fin15AnchoredAtom3665 Fin15AnchoredAtom3666
    Fin15AnchoredAtom3701 Fin15AnchoredAtom3714 Fin15AnchoredAtom3715 Fin15AnchoredAtom3716
    Fin15AnchoredAtom3735 Fin15AnchoredAtom3736 Fin15AnchoredAtom3737 Fin15AnchoredAtom3784
    Fin15AnchoredAtom3785 Fin15AnchoredAtom3786 Fin15AnchoredAtom3821 Fin15AnchoredAtom3868
    Fin15AnchoredAtom3869 Fin15AnchoredAtom3870 Fin15AnchoredAtom3905 Fin15AnchoredAtom3996
    Fin15AnchoredAtom4044 Fin15AnchoredAtom4045 Fin15AnchoredAtom4046 Fin15AnchoredAtom4065
    Fin15AnchoredAtom4066 Fin15AnchoredAtom4067 Fin15AnchoredAtom4114 Fin15AnchoredAtom4115
    Fin15AnchoredAtom4116 Fin15AnchoredAtom4151 Fin15AnchoredAtom4198 Fin15AnchoredAtom4199
    Fin15AnchoredAtom4200 Fin15AnchoredAtom4235 Fin15AnchoredAtom4326 Fin15AnchoredAtom4408
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

theorem fin15Anchored_clause32027 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3540 chi ∧
      ¬Fin15AnchoredAtom3541 chi ∧
      ¬Fin15AnchoredAtom3543 chi ∧
      ¬Fin15AnchoredAtom3544 chi ∧
      ¬Fin15AnchoredAtom3567 chi ∧
      ¬Fin15AnchoredAtom3569 chi ∧
      ¬Fin15AnchoredAtom3570 chi ∧
      ¬Fin15AnchoredAtom3573 chi ∧
      ¬Fin15AnchoredAtom3574 chi ∧
      ¬Fin15AnchoredAtom3579 chi ∧
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
      ¬Fin15AnchoredAtom3723 chi ∧
      ¬Fin15AnchoredAtom3725 chi ∧
      ¬Fin15AnchoredAtom3726 chi ∧
      ¬Fin15AnchoredAtom3729 chi ∧
      ¬Fin15AnchoredAtom3730 chi ∧
      ¬Fin15AnchoredAtom3735 chi ∧
      ¬Fin15AnchoredAtom3803 chi ∧
      ¬Fin15AnchoredAtom3804 chi ∧
      ¬Fin15AnchoredAtom3809 chi ∧
      ¬Fin15AnchoredAtom3815 chi ∧
      ¬Fin15AnchoredAtom3887 chi ∧
      ¬Fin15AnchoredAtom3888 chi ∧
      ¬Fin15AnchoredAtom3893 chi ∧
      ¬Fin15AnchoredAtom3899 chi ∧
      ¬Fin15AnchoredAtom4020 chi ∧
      ¬Fin15AnchoredAtom4053 chi ∧
      ¬Fin15AnchoredAtom4055 chi ∧
      ¬Fin15AnchoredAtom4056 chi ∧
      ¬Fin15AnchoredAtom4059 chi ∧
      ¬Fin15AnchoredAtom4060 chi ∧
      ¬Fin15AnchoredAtom4065 chi ∧
      ¬Fin15AnchoredAtom4133 chi ∧
      ¬Fin15AnchoredAtom4134 chi ∧
      ¬Fin15AnchoredAtom4139 chi ∧
      ¬Fin15AnchoredAtom4145 chi ∧
      ¬Fin15AnchoredAtom4217 chi ∧
      ¬Fin15AnchoredAtom4218 chi ∧
      ¬Fin15AnchoredAtom4223 chi ∧
      ¬Fin15AnchoredAtom4229 chi ∧
      ¬Fin15AnchoredAtom4350 chi ∧
      ¬Fin15AnchoredAtom4427 chi ∧
      ¬Fin15AnchoredAtom4428 chi ∧
      ¬Fin15AnchoredAtom4433 chi ∧
      ¬Fin15AnchoredAtom4439 chi ∧
      ¬Fin15AnchoredAtom4560 chi ∧
      ¬Fin15AnchoredAtom4686 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13884
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3540 Fin15AnchoredAtom3541 Fin15AnchoredAtom3543
    Fin15AnchoredAtom3544 Fin15AnchoredAtom3567 Fin15AnchoredAtom3569 Fin15AnchoredAtom3570
    Fin15AnchoredAtom3573 Fin15AnchoredAtom3574 Fin15AnchoredAtom3579 Fin15AnchoredAtom3603
    Fin15AnchoredAtom3605 Fin15AnchoredAtom3606 Fin15AnchoredAtom3609 Fin15AnchoredAtom3610
    Fin15AnchoredAtom3615 Fin15AnchoredAtom3683 Fin15AnchoredAtom3684 Fin15AnchoredAtom3689
    Fin15AnchoredAtom3695 Fin15AnchoredAtom3723 Fin15AnchoredAtom3725 Fin15AnchoredAtom3726
    Fin15AnchoredAtom3729 Fin15AnchoredAtom3730 Fin15AnchoredAtom3735 Fin15AnchoredAtom3803
    Fin15AnchoredAtom3804 Fin15AnchoredAtom3809 Fin15AnchoredAtom3815 Fin15AnchoredAtom3887
    Fin15AnchoredAtom3888 Fin15AnchoredAtom3893 Fin15AnchoredAtom3899 Fin15AnchoredAtom4020
    Fin15AnchoredAtom4053 Fin15AnchoredAtom4055 Fin15AnchoredAtom4056 Fin15AnchoredAtom4059
    Fin15AnchoredAtom4060 Fin15AnchoredAtom4065 Fin15AnchoredAtom4133 Fin15AnchoredAtom4134
    Fin15AnchoredAtom4139 Fin15AnchoredAtom4145 Fin15AnchoredAtom4217 Fin15AnchoredAtom4218
    Fin15AnchoredAtom4223 Fin15AnchoredAtom4229 Fin15AnchoredAtom4350 Fin15AnchoredAtom4427
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

theorem fin15Anchored_clause32028 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3540 chi ∧
      ¬Fin15AnchoredAtom3541 chi ∧
      ¬Fin15AnchoredAtom3543 chi ∧
      ¬Fin15AnchoredAtom3545 chi ∧
      ¬Fin15AnchoredAtom3567 chi ∧
      ¬Fin15AnchoredAtom3569 chi ∧
      ¬Fin15AnchoredAtom3571 chi ∧
      ¬Fin15AnchoredAtom3573 chi ∧
      ¬Fin15AnchoredAtom3575 chi ∧
      ¬Fin15AnchoredAtom3580 chi ∧
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
      ¬Fin15AnchoredAtom3723 chi ∧
      ¬Fin15AnchoredAtom3725 chi ∧
      ¬Fin15AnchoredAtom3727 chi ∧
      ¬Fin15AnchoredAtom3729 chi ∧
      ¬Fin15AnchoredAtom3731 chi ∧
      ¬Fin15AnchoredAtom3736 chi ∧
      ¬Fin15AnchoredAtom3803 chi ∧
      ¬Fin15AnchoredAtom3805 chi ∧
      ¬Fin15AnchoredAtom3810 chi ∧
      ¬Fin15AnchoredAtom3816 chi ∧
      ¬Fin15AnchoredAtom3887 chi ∧
      ¬Fin15AnchoredAtom3889 chi ∧
      ¬Fin15AnchoredAtom3894 chi ∧
      ¬Fin15AnchoredAtom3900 chi ∧
      ¬Fin15AnchoredAtom4021 chi ∧
      ¬Fin15AnchoredAtom4053 chi ∧
      ¬Fin15AnchoredAtom4055 chi ∧
      ¬Fin15AnchoredAtom4057 chi ∧
      ¬Fin15AnchoredAtom4059 chi ∧
      ¬Fin15AnchoredAtom4061 chi ∧
      ¬Fin15AnchoredAtom4066 chi ∧
      ¬Fin15AnchoredAtom4133 chi ∧
      ¬Fin15AnchoredAtom4135 chi ∧
      ¬Fin15AnchoredAtom4140 chi ∧
      ¬Fin15AnchoredAtom4146 chi ∧
      ¬Fin15AnchoredAtom4217 chi ∧
      ¬Fin15AnchoredAtom4219 chi ∧
      ¬Fin15AnchoredAtom4224 chi ∧
      ¬Fin15AnchoredAtom4230 chi ∧
      ¬Fin15AnchoredAtom4351 chi ∧
      ¬Fin15AnchoredAtom4427 chi ∧
      ¬Fin15AnchoredAtom4429 chi ∧
      ¬Fin15AnchoredAtom4434 chi ∧
      ¬Fin15AnchoredAtom4440 chi ∧
      ¬Fin15AnchoredAtom4561 chi ∧
      ¬Fin15AnchoredAtom4687 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 9, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22076
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3540 Fin15AnchoredAtom3541 Fin15AnchoredAtom3543
    Fin15AnchoredAtom3545 Fin15AnchoredAtom3567 Fin15AnchoredAtom3569 Fin15AnchoredAtom3571
    Fin15AnchoredAtom3573 Fin15AnchoredAtom3575 Fin15AnchoredAtom3580 Fin15AnchoredAtom3603
    Fin15AnchoredAtom3605 Fin15AnchoredAtom3607 Fin15AnchoredAtom3609 Fin15AnchoredAtom3611
    Fin15AnchoredAtom3616 Fin15AnchoredAtom3683 Fin15AnchoredAtom3685 Fin15AnchoredAtom3690
    Fin15AnchoredAtom3696 Fin15AnchoredAtom3723 Fin15AnchoredAtom3725 Fin15AnchoredAtom3727
    Fin15AnchoredAtom3729 Fin15AnchoredAtom3731 Fin15AnchoredAtom3736 Fin15AnchoredAtom3803
    Fin15AnchoredAtom3805 Fin15AnchoredAtom3810 Fin15AnchoredAtom3816 Fin15AnchoredAtom3887
    Fin15AnchoredAtom3889 Fin15AnchoredAtom3894 Fin15AnchoredAtom3900 Fin15AnchoredAtom4021
    Fin15AnchoredAtom4053 Fin15AnchoredAtom4055 Fin15AnchoredAtom4057 Fin15AnchoredAtom4059
    Fin15AnchoredAtom4061 Fin15AnchoredAtom4066 Fin15AnchoredAtom4133 Fin15AnchoredAtom4135
    Fin15AnchoredAtom4140 Fin15AnchoredAtom4146 Fin15AnchoredAtom4217 Fin15AnchoredAtom4219
    Fin15AnchoredAtom4224 Fin15AnchoredAtom4230 Fin15AnchoredAtom4351 Fin15AnchoredAtom4427
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

theorem fin15Anchored_clause32029 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3540 chi ∧
      ¬Fin15AnchoredAtom3541 chi ∧
      ¬Fin15AnchoredAtom3544 chi ∧
      ¬Fin15AnchoredAtom3545 chi ∧
      ¬Fin15AnchoredAtom3567 chi ∧
      ¬Fin15AnchoredAtom3570 chi ∧
      ¬Fin15AnchoredAtom3571 chi ∧
      ¬Fin15AnchoredAtom3574 chi ∧
      ¬Fin15AnchoredAtom3575 chi ∧
      ¬Fin15AnchoredAtom3581 chi ∧
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
      ¬Fin15AnchoredAtom3723 chi ∧
      ¬Fin15AnchoredAtom3726 chi ∧
      ¬Fin15AnchoredAtom3727 chi ∧
      ¬Fin15AnchoredAtom3730 chi ∧
      ¬Fin15AnchoredAtom3731 chi ∧
      ¬Fin15AnchoredAtom3737 chi ∧
      ¬Fin15AnchoredAtom3804 chi ∧
      ¬Fin15AnchoredAtom3805 chi ∧
      ¬Fin15AnchoredAtom3811 chi ∧
      ¬Fin15AnchoredAtom3817 chi ∧
      ¬Fin15AnchoredAtom3888 chi ∧
      ¬Fin15AnchoredAtom3889 chi ∧
      ¬Fin15AnchoredAtom3895 chi ∧
      ¬Fin15AnchoredAtom3901 chi ∧
      ¬Fin15AnchoredAtom4022 chi ∧
      ¬Fin15AnchoredAtom4053 chi ∧
      ¬Fin15AnchoredAtom4056 chi ∧
      ¬Fin15AnchoredAtom4057 chi ∧
      ¬Fin15AnchoredAtom4060 chi ∧
      ¬Fin15AnchoredAtom4061 chi ∧
      ¬Fin15AnchoredAtom4067 chi ∧
      ¬Fin15AnchoredAtom4134 chi ∧
      ¬Fin15AnchoredAtom4135 chi ∧
      ¬Fin15AnchoredAtom4141 chi ∧
      ¬Fin15AnchoredAtom4147 chi ∧
      ¬Fin15AnchoredAtom4218 chi ∧
      ¬Fin15AnchoredAtom4219 chi ∧
      ¬Fin15AnchoredAtom4225 chi ∧
      ¬Fin15AnchoredAtom4231 chi ∧
      ¬Fin15AnchoredAtom4352 chi ∧
      ¬Fin15AnchoredAtom4428 chi ∧
      ¬Fin15AnchoredAtom4429 chi ∧
      ¬Fin15AnchoredAtom4435 chi ∧
      ¬Fin15AnchoredAtom4441 chi ∧
      ¬Fin15AnchoredAtom4562 chi ∧
      ¬Fin15AnchoredAtom4688 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 9, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26172
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3540 Fin15AnchoredAtom3541 Fin15AnchoredAtom3544
    Fin15AnchoredAtom3545 Fin15AnchoredAtom3567 Fin15AnchoredAtom3570 Fin15AnchoredAtom3571
    Fin15AnchoredAtom3574 Fin15AnchoredAtom3575 Fin15AnchoredAtom3581 Fin15AnchoredAtom3603
    Fin15AnchoredAtom3606 Fin15AnchoredAtom3607 Fin15AnchoredAtom3610 Fin15AnchoredAtom3611
    Fin15AnchoredAtom3617 Fin15AnchoredAtom3684 Fin15AnchoredAtom3685 Fin15AnchoredAtom3691
    Fin15AnchoredAtom3697 Fin15AnchoredAtom3723 Fin15AnchoredAtom3726 Fin15AnchoredAtom3727
    Fin15AnchoredAtom3730 Fin15AnchoredAtom3731 Fin15AnchoredAtom3737 Fin15AnchoredAtom3804
    Fin15AnchoredAtom3805 Fin15AnchoredAtom3811 Fin15AnchoredAtom3817 Fin15AnchoredAtom3888
    Fin15AnchoredAtom3889 Fin15AnchoredAtom3895 Fin15AnchoredAtom3901 Fin15AnchoredAtom4022
    Fin15AnchoredAtom4053 Fin15AnchoredAtom4056 Fin15AnchoredAtom4057 Fin15AnchoredAtom4060
    Fin15AnchoredAtom4061 Fin15AnchoredAtom4067 Fin15AnchoredAtom4134 Fin15AnchoredAtom4135
    Fin15AnchoredAtom4141 Fin15AnchoredAtom4147 Fin15AnchoredAtom4218 Fin15AnchoredAtom4219
    Fin15AnchoredAtom4225 Fin15AnchoredAtom4231 Fin15AnchoredAtom4352 Fin15AnchoredAtom4428
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

theorem fin15Anchored_clause32030 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3540 chi ∧
      ¬Fin15AnchoredAtom3542 chi ∧
      ¬Fin15AnchoredAtom3543 chi ∧
      ¬Fin15AnchoredAtom3544 chi ∧
      ¬Fin15AnchoredAtom3568 chi ∧
      ¬Fin15AnchoredAtom3569 chi ∧
      ¬Fin15AnchoredAtom3570 chi ∧
      ¬Fin15AnchoredAtom3576 chi ∧
      ¬Fin15AnchoredAtom3577 chi ∧
      ¬Fin15AnchoredAtom3579 chi ∧
      ¬Fin15AnchoredAtom3604 chi ∧
      ¬Fin15AnchoredAtom3605 chi ∧
      ¬Fin15AnchoredAtom3606 chi ∧
      ¬Fin15AnchoredAtom3612 chi ∧
      ¬Fin15AnchoredAtom3613 chi ∧
      ¬Fin15AnchoredAtom3615 chi ∧
      ¬Fin15AnchoredAtom3686 chi ∧
      ¬Fin15AnchoredAtom3687 chi ∧
      ¬Fin15AnchoredAtom3689 chi ∧
      ¬Fin15AnchoredAtom3698 chi ∧
      ¬Fin15AnchoredAtom3724 chi ∧
      ¬Fin15AnchoredAtom3725 chi ∧
      ¬Fin15AnchoredAtom3726 chi ∧
      ¬Fin15AnchoredAtom3732 chi ∧
      ¬Fin15AnchoredAtom3733 chi ∧
      ¬Fin15AnchoredAtom3735 chi ∧
      ¬Fin15AnchoredAtom3806 chi ∧
      ¬Fin15AnchoredAtom3807 chi ∧
      ¬Fin15AnchoredAtom3809 chi ∧
      ¬Fin15AnchoredAtom3818 chi ∧
      ¬Fin15AnchoredAtom3890 chi ∧
      ¬Fin15AnchoredAtom3891 chi ∧
      ¬Fin15AnchoredAtom3893 chi ∧
      ¬Fin15AnchoredAtom3902 chi ∧
      ¬Fin15AnchoredAtom4023 chi ∧
      ¬Fin15AnchoredAtom4054 chi ∧
      ¬Fin15AnchoredAtom4055 chi ∧
      ¬Fin15AnchoredAtom4056 chi ∧
      ¬Fin15AnchoredAtom4062 chi ∧
      ¬Fin15AnchoredAtom4063 chi ∧
      ¬Fin15AnchoredAtom4065 chi ∧
      ¬Fin15AnchoredAtom4136 chi ∧
      ¬Fin15AnchoredAtom4137 chi ∧
      ¬Fin15AnchoredAtom4139 chi ∧
      ¬Fin15AnchoredAtom4148 chi ∧
      ¬Fin15AnchoredAtom4220 chi ∧
      ¬Fin15AnchoredAtom4221 chi ∧
      ¬Fin15AnchoredAtom4223 chi ∧
      ¬Fin15AnchoredAtom4232 chi ∧
      ¬Fin15AnchoredAtom4353 chi ∧
      ¬Fin15AnchoredAtom4430 chi ∧
      ¬Fin15AnchoredAtom4431 chi ∧
      ¬Fin15AnchoredAtom4433 chi ∧
      ¬Fin15AnchoredAtom4442 chi ∧
      ¬Fin15AnchoredAtom4563 chi ∧
      ¬Fin15AnchoredAtom4689 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 9, 11, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask14908
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3540 Fin15AnchoredAtom3542 Fin15AnchoredAtom3543
    Fin15AnchoredAtom3544 Fin15AnchoredAtom3568 Fin15AnchoredAtom3569 Fin15AnchoredAtom3570
    Fin15AnchoredAtom3576 Fin15AnchoredAtom3577 Fin15AnchoredAtom3579 Fin15AnchoredAtom3604
    Fin15AnchoredAtom3605 Fin15AnchoredAtom3606 Fin15AnchoredAtom3612 Fin15AnchoredAtom3613
    Fin15AnchoredAtom3615 Fin15AnchoredAtom3686 Fin15AnchoredAtom3687 Fin15AnchoredAtom3689
    Fin15AnchoredAtom3698 Fin15AnchoredAtom3724 Fin15AnchoredAtom3725 Fin15AnchoredAtom3726
    Fin15AnchoredAtom3732 Fin15AnchoredAtom3733 Fin15AnchoredAtom3735 Fin15AnchoredAtom3806
    Fin15AnchoredAtom3807 Fin15AnchoredAtom3809 Fin15AnchoredAtom3818 Fin15AnchoredAtom3890
    Fin15AnchoredAtom3891 Fin15AnchoredAtom3893 Fin15AnchoredAtom3902 Fin15AnchoredAtom4023
    Fin15AnchoredAtom4054 Fin15AnchoredAtom4055 Fin15AnchoredAtom4056 Fin15AnchoredAtom4062
    Fin15AnchoredAtom4063 Fin15AnchoredAtom4065 Fin15AnchoredAtom4136 Fin15AnchoredAtom4137
    Fin15AnchoredAtom4139 Fin15AnchoredAtom4148 Fin15AnchoredAtom4220 Fin15AnchoredAtom4221
    Fin15AnchoredAtom4223 Fin15AnchoredAtom4232 Fin15AnchoredAtom4353 Fin15AnchoredAtom4430
    Fin15AnchoredAtom4431 Fin15AnchoredAtom4433 Fin15AnchoredAtom4442 Fin15AnchoredAtom4563
    Fin15AnchoredAtom4689 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause32031 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3540 chi ∧
      ¬Fin15AnchoredAtom3543 chi ∧
      ¬Fin15AnchoredAtom3544 chi ∧
      ¬Fin15AnchoredAtom3545 chi ∧
      ¬Fin15AnchoredAtom3569 chi ∧
      ¬Fin15AnchoredAtom3570 chi ∧
      ¬Fin15AnchoredAtom3571 chi ∧
      ¬Fin15AnchoredAtom3579 chi ∧
      ¬Fin15AnchoredAtom3580 chi ∧
      ¬Fin15AnchoredAtom3581 chi ∧
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
      ¬Fin15AnchoredAtom3725 chi ∧
      ¬Fin15AnchoredAtom3726 chi ∧
      ¬Fin15AnchoredAtom3727 chi ∧
      ¬Fin15AnchoredAtom3735 chi ∧
      ¬Fin15AnchoredAtom3736 chi ∧
      ¬Fin15AnchoredAtom3737 chi ∧
      ¬Fin15AnchoredAtom3809 chi ∧
      ¬Fin15AnchoredAtom3810 chi ∧
      ¬Fin15AnchoredAtom3811 chi ∧
      ¬Fin15AnchoredAtom3821 chi ∧
      ¬Fin15AnchoredAtom3893 chi ∧
      ¬Fin15AnchoredAtom3894 chi ∧
      ¬Fin15AnchoredAtom3895 chi ∧
      ¬Fin15AnchoredAtom3905 chi ∧
      ¬Fin15AnchoredAtom4026 chi ∧
      ¬Fin15AnchoredAtom4055 chi ∧
      ¬Fin15AnchoredAtom4056 chi ∧
      ¬Fin15AnchoredAtom4057 chi ∧
      ¬Fin15AnchoredAtom4065 chi ∧
      ¬Fin15AnchoredAtom4066 chi ∧
      ¬Fin15AnchoredAtom4067 chi ∧
      ¬Fin15AnchoredAtom4139 chi ∧
      ¬Fin15AnchoredAtom4140 chi ∧
      ¬Fin15AnchoredAtom4141 chi ∧
      ¬Fin15AnchoredAtom4151 chi ∧
      ¬Fin15AnchoredAtom4223 chi ∧
      ¬Fin15AnchoredAtom4224 chi ∧
      ¬Fin15AnchoredAtom4225 chi ∧
      ¬Fin15AnchoredAtom4235 chi ∧
      ¬Fin15AnchoredAtom4356 chi ∧
      ¬Fin15AnchoredAtom4433 chi ∧
      ¬Fin15AnchoredAtom4434 chi ∧
      ¬Fin15AnchoredAtom4435 chi ∧
      ¬Fin15AnchoredAtom4445 chi ∧
      ¬Fin15AnchoredAtom4566 chi ∧
      ¬Fin15AnchoredAtom4692 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 9, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29244
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3540 Fin15AnchoredAtom3543 Fin15AnchoredAtom3544
    Fin15AnchoredAtom3545 Fin15AnchoredAtom3569 Fin15AnchoredAtom3570 Fin15AnchoredAtom3571
    Fin15AnchoredAtom3579 Fin15AnchoredAtom3580 Fin15AnchoredAtom3581 Fin15AnchoredAtom3605
    Fin15AnchoredAtom3606 Fin15AnchoredAtom3607 Fin15AnchoredAtom3615 Fin15AnchoredAtom3616
    Fin15AnchoredAtom3617 Fin15AnchoredAtom3689 Fin15AnchoredAtom3690 Fin15AnchoredAtom3691
    Fin15AnchoredAtom3701 Fin15AnchoredAtom3725 Fin15AnchoredAtom3726 Fin15AnchoredAtom3727
    Fin15AnchoredAtom3735 Fin15AnchoredAtom3736 Fin15AnchoredAtom3737 Fin15AnchoredAtom3809
    Fin15AnchoredAtom3810 Fin15AnchoredAtom3811 Fin15AnchoredAtom3821 Fin15AnchoredAtom3893
    Fin15AnchoredAtom3894 Fin15AnchoredAtom3895 Fin15AnchoredAtom3905 Fin15AnchoredAtom4026
    Fin15AnchoredAtom4055 Fin15AnchoredAtom4056 Fin15AnchoredAtom4057 Fin15AnchoredAtom4065
    Fin15AnchoredAtom4066 Fin15AnchoredAtom4067 Fin15AnchoredAtom4139 Fin15AnchoredAtom4140
    Fin15AnchoredAtom4141 Fin15AnchoredAtom4151 Fin15AnchoredAtom4223 Fin15AnchoredAtom4224
    Fin15AnchoredAtom4225 Fin15AnchoredAtom4235 Fin15AnchoredAtom4356 Fin15AnchoredAtom4433
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

theorem fin15Anchored_clause32032 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3541 chi ∧
      ¬Fin15AnchoredAtom3543 chi ∧
      ¬Fin15AnchoredAtom3544 chi ∧
      ¬Fin15AnchoredAtom3545 chi ∧
      ¬Fin15AnchoredAtom3573 chi ∧
      ¬Fin15AnchoredAtom3574 chi ∧
      ¬Fin15AnchoredAtom3575 chi ∧
      ¬Fin15AnchoredAtom3579 chi ∧
      ¬Fin15AnchoredAtom3580 chi ∧
      ¬Fin15AnchoredAtom3581 chi ∧
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
      ¬Fin15AnchoredAtom3729 chi ∧
      ¬Fin15AnchoredAtom3730 chi ∧
      ¬Fin15AnchoredAtom3731 chi ∧
      ¬Fin15AnchoredAtom3735 chi ∧
      ¬Fin15AnchoredAtom3736 chi ∧
      ¬Fin15AnchoredAtom3737 chi ∧
      ¬Fin15AnchoredAtom3815 chi ∧
      ¬Fin15AnchoredAtom3816 chi ∧
      ¬Fin15AnchoredAtom3817 chi ∧
      ¬Fin15AnchoredAtom3821 chi ∧
      ¬Fin15AnchoredAtom3899 chi ∧
      ¬Fin15AnchoredAtom3900 chi ∧
      ¬Fin15AnchoredAtom3901 chi ∧
      ¬Fin15AnchoredAtom3905 chi ∧
      ¬Fin15AnchoredAtom4030 chi ∧
      ¬Fin15AnchoredAtom4059 chi ∧
      ¬Fin15AnchoredAtom4060 chi ∧
      ¬Fin15AnchoredAtom4061 chi ∧
      ¬Fin15AnchoredAtom4065 chi ∧
      ¬Fin15AnchoredAtom4066 chi ∧
      ¬Fin15AnchoredAtom4067 chi ∧
      ¬Fin15AnchoredAtom4145 chi ∧
      ¬Fin15AnchoredAtom4146 chi ∧
      ¬Fin15AnchoredAtom4147 chi ∧
      ¬Fin15AnchoredAtom4151 chi ∧
      ¬Fin15AnchoredAtom4229 chi ∧
      ¬Fin15AnchoredAtom4230 chi ∧
      ¬Fin15AnchoredAtom4231 chi ∧
      ¬Fin15AnchoredAtom4235 chi ∧
      ¬Fin15AnchoredAtom4360 chi ∧
      ¬Fin15AnchoredAtom4439 chi ∧
      ¬Fin15AnchoredAtom4440 chi ∧
      ¬Fin15AnchoredAtom4441 chi ∧
      ¬Fin15AnchoredAtom4445 chi ∧
      ¬Fin15AnchoredAtom4570 chi ∧
      ¬Fin15AnchoredAtom4696 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29756
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3541 Fin15AnchoredAtom3543 Fin15AnchoredAtom3544
    Fin15AnchoredAtom3545 Fin15AnchoredAtom3573 Fin15AnchoredAtom3574 Fin15AnchoredAtom3575
    Fin15AnchoredAtom3579 Fin15AnchoredAtom3580 Fin15AnchoredAtom3581 Fin15AnchoredAtom3609
    Fin15AnchoredAtom3610 Fin15AnchoredAtom3611 Fin15AnchoredAtom3615 Fin15AnchoredAtom3616
    Fin15AnchoredAtom3617 Fin15AnchoredAtom3695 Fin15AnchoredAtom3696 Fin15AnchoredAtom3697
    Fin15AnchoredAtom3701 Fin15AnchoredAtom3729 Fin15AnchoredAtom3730 Fin15AnchoredAtom3731
    Fin15AnchoredAtom3735 Fin15AnchoredAtom3736 Fin15AnchoredAtom3737 Fin15AnchoredAtom3815
    Fin15AnchoredAtom3816 Fin15AnchoredAtom3817 Fin15AnchoredAtom3821 Fin15AnchoredAtom3899
    Fin15AnchoredAtom3900 Fin15AnchoredAtom3901 Fin15AnchoredAtom3905 Fin15AnchoredAtom4030
    Fin15AnchoredAtom4059 Fin15AnchoredAtom4060 Fin15AnchoredAtom4061 Fin15AnchoredAtom4065
    Fin15AnchoredAtom4066 Fin15AnchoredAtom4067 Fin15AnchoredAtom4145 Fin15AnchoredAtom4146
    Fin15AnchoredAtom4147 Fin15AnchoredAtom4151 Fin15AnchoredAtom4229 Fin15AnchoredAtom4230
    Fin15AnchoredAtom4231 Fin15AnchoredAtom4235 Fin15AnchoredAtom4360 Fin15AnchoredAtom4439
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

theorem fin15Anchored_clause32033 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3546 chi ∧
      ¬Fin15AnchoredAtom3548 chi ∧
      ¬Fin15AnchoredAtom3549 chi ∧
      ¬Fin15AnchoredAtom3551 chi ∧
      ¬Fin15AnchoredAtom3555 chi ∧
      ¬Fin15AnchoredAtom3556 chi ∧
      ¬Fin15AnchoredAtom3558 chi ∧
      ¬Fin15AnchoredAtom3567 chi ∧
      ¬Fin15AnchoredAtom3569 chi ∧
      ¬Fin15AnchoredAtom3573 chi ∧
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
      ¬Fin15AnchoredAtom3739 chi ∧
      ¬Fin15AnchoredAtom3740 chi ∧
      ¬Fin15AnchoredAtom3742 chi ∧
      ¬Fin15AnchoredAtom3751 chi ∧
      ¬Fin15AnchoredAtom3753 chi ∧
      ¬Fin15AnchoredAtom3757 chi ∧
      ¬Fin15AnchoredAtom3772 chi ∧
      ¬Fin15AnchoredAtom3774 chi ∧
      ¬Fin15AnchoredAtom3778 chi ∧
      ¬Fin15AnchoredAtom3803 chi ∧
      ¬Fin15AnchoredAtom3912 chi ∧
      ¬Fin15AnchoredAtom3914 chi ∧
      ¬Fin15AnchoredAtom3918 chi ∧
      ¬Fin15AnchoredAtom3943 chi ∧
      ¬Fin15AnchoredAtom3978 chi ∧
      ¬Fin15AnchoredAtom4069 chi ∧
      ¬Fin15AnchoredAtom4070 chi ∧
      ¬Fin15AnchoredAtom4072 chi ∧
      ¬Fin15AnchoredAtom4081 chi ∧
      ¬Fin15AnchoredAtom4083 chi ∧
      ¬Fin15AnchoredAtom4087 chi ∧
      ¬Fin15AnchoredAtom4102 chi ∧
      ¬Fin15AnchoredAtom4104 chi ∧
      ¬Fin15AnchoredAtom4108 chi ∧
      ¬Fin15AnchoredAtom4133 chi ∧
      ¬Fin15AnchoredAtom4242 chi ∧
      ¬Fin15AnchoredAtom4244 chi ∧
      ¬Fin15AnchoredAtom4248 chi ∧
      ¬Fin15AnchoredAtom4273 chi ∧
      ¬Fin15AnchoredAtom4308 chi ∧
      ¬Fin15AnchoredAtom4452 chi ∧
      ¬Fin15AnchoredAtom4454 chi ∧
      ¬Fin15AnchoredAtom4458 chi ∧
      ¬Fin15AnchoredAtom4483 chi ∧
      ¬Fin15AnchoredAtom4518 chi ∧
      ¬Fin15AnchoredAtom4714 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 6, 7, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05852
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3546 Fin15AnchoredAtom3548 Fin15AnchoredAtom3549
    Fin15AnchoredAtom3551 Fin15AnchoredAtom3555 Fin15AnchoredAtom3556 Fin15AnchoredAtom3558
    Fin15AnchoredAtom3567 Fin15AnchoredAtom3569 Fin15AnchoredAtom3573 Fin15AnchoredAtom3619
    Fin15AnchoredAtom3620 Fin15AnchoredAtom3622 Fin15AnchoredAtom3631 Fin15AnchoredAtom3633
    Fin15AnchoredAtom3637 Fin15AnchoredAtom3652 Fin15AnchoredAtom3654 Fin15AnchoredAtom3658
    Fin15AnchoredAtom3683 Fin15AnchoredAtom3739 Fin15AnchoredAtom3740 Fin15AnchoredAtom3742
    Fin15AnchoredAtom3751 Fin15AnchoredAtom3753 Fin15AnchoredAtom3757 Fin15AnchoredAtom3772
    Fin15AnchoredAtom3774 Fin15AnchoredAtom3778 Fin15AnchoredAtom3803 Fin15AnchoredAtom3912
    Fin15AnchoredAtom3914 Fin15AnchoredAtom3918 Fin15AnchoredAtom3943 Fin15AnchoredAtom3978
    Fin15AnchoredAtom4069 Fin15AnchoredAtom4070 Fin15AnchoredAtom4072 Fin15AnchoredAtom4081
    Fin15AnchoredAtom4083 Fin15AnchoredAtom4087 Fin15AnchoredAtom4102 Fin15AnchoredAtom4104
    Fin15AnchoredAtom4108 Fin15AnchoredAtom4133 Fin15AnchoredAtom4242 Fin15AnchoredAtom4244
    Fin15AnchoredAtom4248 Fin15AnchoredAtom4273 Fin15AnchoredAtom4308 Fin15AnchoredAtom4452
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

theorem fin15Anchored_clause32034 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3546 chi ∧
      ¬Fin15AnchoredAtom3548 chi ∧
      ¬Fin15AnchoredAtom3549 chi ∧
      ¬Fin15AnchoredAtom3552 chi ∧
      ¬Fin15AnchoredAtom3555 chi ∧
      ¬Fin15AnchoredAtom3556 chi ∧
      ¬Fin15AnchoredAtom3559 chi ∧
      ¬Fin15AnchoredAtom3567 chi ∧
      ¬Fin15AnchoredAtom3570 chi ∧
      ¬Fin15AnchoredAtom3574 chi ∧
      ¬Fin15AnchoredAtom3619 chi ∧
      ¬Fin15AnchoredAtom3620 chi ∧
      ¬Fin15AnchoredAtom3623 chi ∧
      ¬Fin15AnchoredAtom3631 chi ∧
      ¬Fin15AnchoredAtom3634 chi ∧
      ¬Fin15AnchoredAtom3638 chi ∧
      ¬Fin15AnchoredAtom3652 chi ∧
      ¬Fin15AnchoredAtom3655 chi ∧
      ¬Fin15AnchoredAtom3659 chi ∧
      ¬Fin15AnchoredAtom3684 chi ∧
      ¬Fin15AnchoredAtom3739 chi ∧
      ¬Fin15AnchoredAtom3740 chi ∧
      ¬Fin15AnchoredAtom3743 chi ∧
      ¬Fin15AnchoredAtom3751 chi ∧
      ¬Fin15AnchoredAtom3754 chi ∧
      ¬Fin15AnchoredAtom3758 chi ∧
      ¬Fin15AnchoredAtom3772 chi ∧
      ¬Fin15AnchoredAtom3775 chi ∧
      ¬Fin15AnchoredAtom3779 chi ∧
      ¬Fin15AnchoredAtom3804 chi ∧
      ¬Fin15AnchoredAtom3912 chi ∧
      ¬Fin15AnchoredAtom3915 chi ∧
      ¬Fin15AnchoredAtom3919 chi ∧
      ¬Fin15AnchoredAtom3944 chi ∧
      ¬Fin15AnchoredAtom3979 chi ∧
      ¬Fin15AnchoredAtom4069 chi ∧
      ¬Fin15AnchoredAtom4070 chi ∧
      ¬Fin15AnchoredAtom4073 chi ∧
      ¬Fin15AnchoredAtom4081 chi ∧
      ¬Fin15AnchoredAtom4084 chi ∧
      ¬Fin15AnchoredAtom4088 chi ∧
      ¬Fin15AnchoredAtom4102 chi ∧
      ¬Fin15AnchoredAtom4105 chi ∧
      ¬Fin15AnchoredAtom4109 chi ∧
      ¬Fin15AnchoredAtom4134 chi ∧
      ¬Fin15AnchoredAtom4242 chi ∧
      ¬Fin15AnchoredAtom4245 chi ∧
      ¬Fin15AnchoredAtom4249 chi ∧
      ¬Fin15AnchoredAtom4274 chi ∧
      ¬Fin15AnchoredAtom4309 chi ∧
      ¬Fin15AnchoredAtom4452 chi ∧
      ¬Fin15AnchoredAtom4455 chi ∧
      ¬Fin15AnchoredAtom4459 chi ∧
      ¬Fin15AnchoredAtom4484 chi ∧
      ¬Fin15AnchoredAtom4519 chi ∧
      ¬Fin15AnchoredAtom4715 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 6, 7, 9, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09948
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3546 Fin15AnchoredAtom3548 Fin15AnchoredAtom3549
    Fin15AnchoredAtom3552 Fin15AnchoredAtom3555 Fin15AnchoredAtom3556 Fin15AnchoredAtom3559
    Fin15AnchoredAtom3567 Fin15AnchoredAtom3570 Fin15AnchoredAtom3574 Fin15AnchoredAtom3619
    Fin15AnchoredAtom3620 Fin15AnchoredAtom3623 Fin15AnchoredAtom3631 Fin15AnchoredAtom3634
    Fin15AnchoredAtom3638 Fin15AnchoredAtom3652 Fin15AnchoredAtom3655 Fin15AnchoredAtom3659
    Fin15AnchoredAtom3684 Fin15AnchoredAtom3739 Fin15AnchoredAtom3740 Fin15AnchoredAtom3743
    Fin15AnchoredAtom3751 Fin15AnchoredAtom3754 Fin15AnchoredAtom3758 Fin15AnchoredAtom3772
    Fin15AnchoredAtom3775 Fin15AnchoredAtom3779 Fin15AnchoredAtom3804 Fin15AnchoredAtom3912
    Fin15AnchoredAtom3915 Fin15AnchoredAtom3919 Fin15AnchoredAtom3944 Fin15AnchoredAtom3979
    Fin15AnchoredAtom4069 Fin15AnchoredAtom4070 Fin15AnchoredAtom4073 Fin15AnchoredAtom4081
    Fin15AnchoredAtom4084 Fin15AnchoredAtom4088 Fin15AnchoredAtom4102 Fin15AnchoredAtom4105
    Fin15AnchoredAtom4109 Fin15AnchoredAtom4134 Fin15AnchoredAtom4242 Fin15AnchoredAtom4245
    Fin15AnchoredAtom4249 Fin15AnchoredAtom4274 Fin15AnchoredAtom4309 Fin15AnchoredAtom4452
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

theorem fin15Anchored_clause32035 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3546 chi ∧
      ¬Fin15AnchoredAtom3548 chi ∧
      ¬Fin15AnchoredAtom3549 chi ∧
      ¬Fin15AnchoredAtom3553 chi ∧
      ¬Fin15AnchoredAtom3555 chi ∧
      ¬Fin15AnchoredAtom3556 chi ∧
      ¬Fin15AnchoredAtom3560 chi ∧
      ¬Fin15AnchoredAtom3567 chi ∧
      ¬Fin15AnchoredAtom3571 chi ∧
      ¬Fin15AnchoredAtom3575 chi ∧
      ¬Fin15AnchoredAtom3619 chi ∧
      ¬Fin15AnchoredAtom3620 chi ∧
      ¬Fin15AnchoredAtom3624 chi ∧
      ¬Fin15AnchoredAtom3631 chi ∧
      ¬Fin15AnchoredAtom3635 chi ∧
      ¬Fin15AnchoredAtom3639 chi ∧
      ¬Fin15AnchoredAtom3652 chi ∧
      ¬Fin15AnchoredAtom3656 chi ∧
      ¬Fin15AnchoredAtom3660 chi ∧
      ¬Fin15AnchoredAtom3685 chi ∧
      ¬Fin15AnchoredAtom3739 chi ∧
      ¬Fin15AnchoredAtom3740 chi ∧
      ¬Fin15AnchoredAtom3744 chi ∧
      ¬Fin15AnchoredAtom3751 chi ∧
      ¬Fin15AnchoredAtom3755 chi ∧
      ¬Fin15AnchoredAtom3759 chi ∧
      ¬Fin15AnchoredAtom3772 chi ∧
      ¬Fin15AnchoredAtom3776 chi ∧
      ¬Fin15AnchoredAtom3780 chi ∧
      ¬Fin15AnchoredAtom3805 chi ∧
      ¬Fin15AnchoredAtom3912 chi ∧
      ¬Fin15AnchoredAtom3916 chi ∧
      ¬Fin15AnchoredAtom3920 chi ∧
      ¬Fin15AnchoredAtom3945 chi ∧
      ¬Fin15AnchoredAtom3980 chi ∧
      ¬Fin15AnchoredAtom4069 chi ∧
      ¬Fin15AnchoredAtom4070 chi ∧
      ¬Fin15AnchoredAtom4074 chi ∧
      ¬Fin15AnchoredAtom4081 chi ∧
      ¬Fin15AnchoredAtom4085 chi ∧
      ¬Fin15AnchoredAtom4089 chi ∧
      ¬Fin15AnchoredAtom4102 chi ∧
      ¬Fin15AnchoredAtom4106 chi ∧
      ¬Fin15AnchoredAtom4110 chi ∧
      ¬Fin15AnchoredAtom4135 chi ∧
      ¬Fin15AnchoredAtom4242 chi ∧
      ¬Fin15AnchoredAtom4246 chi ∧
      ¬Fin15AnchoredAtom4250 chi ∧
      ¬Fin15AnchoredAtom4275 chi ∧
      ¬Fin15AnchoredAtom4310 chi ∧
      ¬Fin15AnchoredAtom4452 chi ∧
      ¬Fin15AnchoredAtom4456 chi ∧
      ¬Fin15AnchoredAtom4460 chi ∧
      ¬Fin15AnchoredAtom4485 chi ∧
      ¬Fin15AnchoredAtom4520 chi ∧
      ¬Fin15AnchoredAtom4716 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 6, 7, 9, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask18140
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3546 Fin15AnchoredAtom3548 Fin15AnchoredAtom3549
    Fin15AnchoredAtom3553 Fin15AnchoredAtom3555 Fin15AnchoredAtom3556 Fin15AnchoredAtom3560
    Fin15AnchoredAtom3567 Fin15AnchoredAtom3571 Fin15AnchoredAtom3575 Fin15AnchoredAtom3619
    Fin15AnchoredAtom3620 Fin15AnchoredAtom3624 Fin15AnchoredAtom3631 Fin15AnchoredAtom3635
    Fin15AnchoredAtom3639 Fin15AnchoredAtom3652 Fin15AnchoredAtom3656 Fin15AnchoredAtom3660
    Fin15AnchoredAtom3685 Fin15AnchoredAtom3739 Fin15AnchoredAtom3740 Fin15AnchoredAtom3744
    Fin15AnchoredAtom3751 Fin15AnchoredAtom3755 Fin15AnchoredAtom3759 Fin15AnchoredAtom3772
    Fin15AnchoredAtom3776 Fin15AnchoredAtom3780 Fin15AnchoredAtom3805 Fin15AnchoredAtom3912
    Fin15AnchoredAtom3916 Fin15AnchoredAtom3920 Fin15AnchoredAtom3945 Fin15AnchoredAtom3980
    Fin15AnchoredAtom4069 Fin15AnchoredAtom4070 Fin15AnchoredAtom4074 Fin15AnchoredAtom4081
    Fin15AnchoredAtom4085 Fin15AnchoredAtom4089 Fin15AnchoredAtom4102 Fin15AnchoredAtom4106
    Fin15AnchoredAtom4110 Fin15AnchoredAtom4135 Fin15AnchoredAtom4242 Fin15AnchoredAtom4246
    Fin15AnchoredAtom4250 Fin15AnchoredAtom4275 Fin15AnchoredAtom4310 Fin15AnchoredAtom4452
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

theorem fin15Anchored_clause32036 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3546 chi ∧
      ¬Fin15AnchoredAtom3548 chi ∧
      ¬Fin15AnchoredAtom3551 chi ∧
      ¬Fin15AnchoredAtom3552 chi ∧
      ¬Fin15AnchoredAtom3555 chi ∧
      ¬Fin15AnchoredAtom3558 chi ∧
      ¬Fin15AnchoredAtom3559 chi ∧
      ¬Fin15AnchoredAtom3569 chi ∧
      ¬Fin15AnchoredAtom3570 chi ∧
      ¬Fin15AnchoredAtom3579 chi ∧
      ¬Fin15AnchoredAtom3619 chi ∧
      ¬Fin15AnchoredAtom3622 chi ∧
      ¬Fin15AnchoredAtom3623 chi ∧
      ¬Fin15AnchoredAtom3633 chi ∧
      ¬Fin15AnchoredAtom3634 chi ∧
      ¬Fin15AnchoredAtom3643 chi ∧
      ¬Fin15AnchoredAtom3654 chi ∧
      ¬Fin15AnchoredAtom3655 chi ∧
      ¬Fin15AnchoredAtom3664 chi ∧
      ¬Fin15AnchoredAtom3689 chi ∧
      ¬Fin15AnchoredAtom3739 chi ∧
      ¬Fin15AnchoredAtom3742 chi ∧
      ¬Fin15AnchoredAtom3743 chi ∧
      ¬Fin15AnchoredAtom3753 chi ∧
      ¬Fin15AnchoredAtom3754 chi ∧
      ¬Fin15AnchoredAtom3763 chi ∧
      ¬Fin15AnchoredAtom3774 chi ∧
      ¬Fin15AnchoredAtom3775 chi ∧
      ¬Fin15AnchoredAtom3784 chi ∧
      ¬Fin15AnchoredAtom3809 chi ∧
      ¬Fin15AnchoredAtom3914 chi ∧
      ¬Fin15AnchoredAtom3915 chi ∧
      ¬Fin15AnchoredAtom3924 chi ∧
      ¬Fin15AnchoredAtom3949 chi ∧
      ¬Fin15AnchoredAtom3984 chi ∧
      ¬Fin15AnchoredAtom4069 chi ∧
      ¬Fin15AnchoredAtom4072 chi ∧
      ¬Fin15AnchoredAtom4073 chi ∧
      ¬Fin15AnchoredAtom4083 chi ∧
      ¬Fin15AnchoredAtom4084 chi ∧
      ¬Fin15AnchoredAtom4093 chi ∧
      ¬Fin15AnchoredAtom4104 chi ∧
      ¬Fin15AnchoredAtom4105 chi ∧
      ¬Fin15AnchoredAtom4114 chi ∧
      ¬Fin15AnchoredAtom4139 chi ∧
      ¬Fin15AnchoredAtom4244 chi ∧
      ¬Fin15AnchoredAtom4245 chi ∧
      ¬Fin15AnchoredAtom4254 chi ∧
      ¬Fin15AnchoredAtom4279 chi ∧
      ¬Fin15AnchoredAtom4314 chi ∧
      ¬Fin15AnchoredAtom4454 chi ∧
      ¬Fin15AnchoredAtom4455 chi ∧
      ¬Fin15AnchoredAtom4464 chi ∧
      ¬Fin15AnchoredAtom4489 chi ∧
      ¬Fin15AnchoredAtom4524 chi ∧
      ¬Fin15AnchoredAtom4720 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 6, 7, 9, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13020
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3546 Fin15AnchoredAtom3548 Fin15AnchoredAtom3551
    Fin15AnchoredAtom3552 Fin15AnchoredAtom3555 Fin15AnchoredAtom3558 Fin15AnchoredAtom3559
    Fin15AnchoredAtom3569 Fin15AnchoredAtom3570 Fin15AnchoredAtom3579 Fin15AnchoredAtom3619
    Fin15AnchoredAtom3622 Fin15AnchoredAtom3623 Fin15AnchoredAtom3633 Fin15AnchoredAtom3634
    Fin15AnchoredAtom3643 Fin15AnchoredAtom3654 Fin15AnchoredAtom3655 Fin15AnchoredAtom3664
    Fin15AnchoredAtom3689 Fin15AnchoredAtom3739 Fin15AnchoredAtom3742 Fin15AnchoredAtom3743
    Fin15AnchoredAtom3753 Fin15AnchoredAtom3754 Fin15AnchoredAtom3763 Fin15AnchoredAtom3774
    Fin15AnchoredAtom3775 Fin15AnchoredAtom3784 Fin15AnchoredAtom3809 Fin15AnchoredAtom3914
    Fin15AnchoredAtom3915 Fin15AnchoredAtom3924 Fin15AnchoredAtom3949 Fin15AnchoredAtom3984
    Fin15AnchoredAtom4069 Fin15AnchoredAtom4072 Fin15AnchoredAtom4073 Fin15AnchoredAtom4083
    Fin15AnchoredAtom4084 Fin15AnchoredAtom4093 Fin15AnchoredAtom4104 Fin15AnchoredAtom4105
    Fin15AnchoredAtom4114 Fin15AnchoredAtom4139 Fin15AnchoredAtom4244 Fin15AnchoredAtom4245
    Fin15AnchoredAtom4254 Fin15AnchoredAtom4279 Fin15AnchoredAtom4314 Fin15AnchoredAtom4454
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

theorem fin15Anchored_clause32037 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3546 chi ∧
      ¬Fin15AnchoredAtom3548 chi ∧
      ¬Fin15AnchoredAtom3551 chi ∧
      ¬Fin15AnchoredAtom3553 chi ∧
      ¬Fin15AnchoredAtom3555 chi ∧
      ¬Fin15AnchoredAtom3558 chi ∧
      ¬Fin15AnchoredAtom3560 chi ∧
      ¬Fin15AnchoredAtom3569 chi ∧
      ¬Fin15AnchoredAtom3571 chi ∧
      ¬Fin15AnchoredAtom3580 chi ∧
      ¬Fin15AnchoredAtom3619 chi ∧
      ¬Fin15AnchoredAtom3622 chi ∧
      ¬Fin15AnchoredAtom3624 chi ∧
      ¬Fin15AnchoredAtom3633 chi ∧
      ¬Fin15AnchoredAtom3635 chi ∧
      ¬Fin15AnchoredAtom3644 chi ∧
      ¬Fin15AnchoredAtom3654 chi ∧
      ¬Fin15AnchoredAtom3656 chi ∧
      ¬Fin15AnchoredAtom3665 chi ∧
      ¬Fin15AnchoredAtom3690 chi ∧
      ¬Fin15AnchoredAtom3739 chi ∧
      ¬Fin15AnchoredAtom3742 chi ∧
      ¬Fin15AnchoredAtom3744 chi ∧
      ¬Fin15AnchoredAtom3753 chi ∧
      ¬Fin15AnchoredAtom3755 chi ∧
      ¬Fin15AnchoredAtom3764 chi ∧
      ¬Fin15AnchoredAtom3774 chi ∧
      ¬Fin15AnchoredAtom3776 chi ∧
      ¬Fin15AnchoredAtom3785 chi ∧
      ¬Fin15AnchoredAtom3810 chi ∧
      ¬Fin15AnchoredAtom3914 chi ∧
      ¬Fin15AnchoredAtom3916 chi ∧
      ¬Fin15AnchoredAtom3925 chi ∧
      ¬Fin15AnchoredAtom3950 chi ∧
      ¬Fin15AnchoredAtom3985 chi ∧
      ¬Fin15AnchoredAtom4069 chi ∧
      ¬Fin15AnchoredAtom4072 chi ∧
      ¬Fin15AnchoredAtom4074 chi ∧
      ¬Fin15AnchoredAtom4083 chi ∧
      ¬Fin15AnchoredAtom4085 chi ∧
      ¬Fin15AnchoredAtom4094 chi ∧
      ¬Fin15AnchoredAtom4104 chi ∧
      ¬Fin15AnchoredAtom4106 chi ∧
      ¬Fin15AnchoredAtom4115 chi ∧
      ¬Fin15AnchoredAtom4140 chi ∧
      ¬Fin15AnchoredAtom4244 chi ∧
      ¬Fin15AnchoredAtom4246 chi ∧
      ¬Fin15AnchoredAtom4255 chi ∧
      ¬Fin15AnchoredAtom4280 chi ∧
      ¬Fin15AnchoredAtom4315 chi ∧
      ¬Fin15AnchoredAtom4454 chi ∧
      ¬Fin15AnchoredAtom4456 chi ∧
      ¬Fin15AnchoredAtom4465 chi ∧
      ¬Fin15AnchoredAtom4490 chi ∧
      ¬Fin15AnchoredAtom4525 chi ∧
      ¬Fin15AnchoredAtom4721 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 6, 7, 9, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21212
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3546 Fin15AnchoredAtom3548 Fin15AnchoredAtom3551
    Fin15AnchoredAtom3553 Fin15AnchoredAtom3555 Fin15AnchoredAtom3558 Fin15AnchoredAtom3560
    Fin15AnchoredAtom3569 Fin15AnchoredAtom3571 Fin15AnchoredAtom3580 Fin15AnchoredAtom3619
    Fin15AnchoredAtom3622 Fin15AnchoredAtom3624 Fin15AnchoredAtom3633 Fin15AnchoredAtom3635
    Fin15AnchoredAtom3644 Fin15AnchoredAtom3654 Fin15AnchoredAtom3656 Fin15AnchoredAtom3665
    Fin15AnchoredAtom3690 Fin15AnchoredAtom3739 Fin15AnchoredAtom3742 Fin15AnchoredAtom3744
    Fin15AnchoredAtom3753 Fin15AnchoredAtom3755 Fin15AnchoredAtom3764 Fin15AnchoredAtom3774
    Fin15AnchoredAtom3776 Fin15AnchoredAtom3785 Fin15AnchoredAtom3810 Fin15AnchoredAtom3914
    Fin15AnchoredAtom3916 Fin15AnchoredAtom3925 Fin15AnchoredAtom3950 Fin15AnchoredAtom3985
    Fin15AnchoredAtom4069 Fin15AnchoredAtom4072 Fin15AnchoredAtom4074 Fin15AnchoredAtom4083
    Fin15AnchoredAtom4085 Fin15AnchoredAtom4094 Fin15AnchoredAtom4104 Fin15AnchoredAtom4106
    Fin15AnchoredAtom4115 Fin15AnchoredAtom4140 Fin15AnchoredAtom4244 Fin15AnchoredAtom4246
    Fin15AnchoredAtom4255 Fin15AnchoredAtom4280 Fin15AnchoredAtom4315 Fin15AnchoredAtom4454
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

theorem fin15Anchored_clause32038 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3546 chi ∧
      ¬Fin15AnchoredAtom3548 chi ∧
      ¬Fin15AnchoredAtom3552 chi ∧
      ¬Fin15AnchoredAtom3553 chi ∧
      ¬Fin15AnchoredAtom3555 chi ∧
      ¬Fin15AnchoredAtom3559 chi ∧
      ¬Fin15AnchoredAtom3560 chi ∧
      ¬Fin15AnchoredAtom3570 chi ∧
      ¬Fin15AnchoredAtom3571 chi ∧
      ¬Fin15AnchoredAtom3581 chi ∧
      ¬Fin15AnchoredAtom3619 chi ∧
      ¬Fin15AnchoredAtom3623 chi ∧
      ¬Fin15AnchoredAtom3624 chi ∧
      ¬Fin15AnchoredAtom3634 chi ∧
      ¬Fin15AnchoredAtom3635 chi ∧
      ¬Fin15AnchoredAtom3645 chi ∧
      ¬Fin15AnchoredAtom3655 chi ∧
      ¬Fin15AnchoredAtom3656 chi ∧
      ¬Fin15AnchoredAtom3666 chi ∧
      ¬Fin15AnchoredAtom3691 chi ∧
      ¬Fin15AnchoredAtom3739 chi ∧
      ¬Fin15AnchoredAtom3743 chi ∧
      ¬Fin15AnchoredAtom3744 chi ∧
      ¬Fin15AnchoredAtom3754 chi ∧
      ¬Fin15AnchoredAtom3755 chi ∧
      ¬Fin15AnchoredAtom3765 chi ∧
      ¬Fin15AnchoredAtom3775 chi ∧
      ¬Fin15AnchoredAtom3776 chi ∧
      ¬Fin15AnchoredAtom3786 chi ∧
      ¬Fin15AnchoredAtom3811 chi ∧
      ¬Fin15AnchoredAtom3915 chi ∧
      ¬Fin15AnchoredAtom3916 chi ∧
      ¬Fin15AnchoredAtom3926 chi ∧
      ¬Fin15AnchoredAtom3951 chi ∧
      ¬Fin15AnchoredAtom3986 chi ∧
      ¬Fin15AnchoredAtom4069 chi ∧
      ¬Fin15AnchoredAtom4073 chi ∧
      ¬Fin15AnchoredAtom4074 chi ∧
      ¬Fin15AnchoredAtom4084 chi ∧
      ¬Fin15AnchoredAtom4085 chi ∧
      ¬Fin15AnchoredAtom4095 chi ∧
      ¬Fin15AnchoredAtom4105 chi ∧
      ¬Fin15AnchoredAtom4106 chi ∧
      ¬Fin15AnchoredAtom4116 chi ∧
      ¬Fin15AnchoredAtom4141 chi ∧
      ¬Fin15AnchoredAtom4245 chi ∧
      ¬Fin15AnchoredAtom4246 chi ∧
      ¬Fin15AnchoredAtom4256 chi ∧
      ¬Fin15AnchoredAtom4281 chi ∧
      ¬Fin15AnchoredAtom4316 chi ∧
      ¬Fin15AnchoredAtom4455 chi ∧
      ¬Fin15AnchoredAtom4456 chi ∧
      ¬Fin15AnchoredAtom4466 chi ∧
      ¬Fin15AnchoredAtom4491 chi ∧
      ¬Fin15AnchoredAtom4526 chi ∧
      ¬Fin15AnchoredAtom4722 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 6, 7, 9, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25308
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3546 Fin15AnchoredAtom3548 Fin15AnchoredAtom3552
    Fin15AnchoredAtom3553 Fin15AnchoredAtom3555 Fin15AnchoredAtom3559 Fin15AnchoredAtom3560
    Fin15AnchoredAtom3570 Fin15AnchoredAtom3571 Fin15AnchoredAtom3581 Fin15AnchoredAtom3619
    Fin15AnchoredAtom3623 Fin15AnchoredAtom3624 Fin15AnchoredAtom3634 Fin15AnchoredAtom3635
    Fin15AnchoredAtom3645 Fin15AnchoredAtom3655 Fin15AnchoredAtom3656 Fin15AnchoredAtom3666
    Fin15AnchoredAtom3691 Fin15AnchoredAtom3739 Fin15AnchoredAtom3743 Fin15AnchoredAtom3744
    Fin15AnchoredAtom3754 Fin15AnchoredAtom3755 Fin15AnchoredAtom3765 Fin15AnchoredAtom3775
    Fin15AnchoredAtom3776 Fin15AnchoredAtom3786 Fin15AnchoredAtom3811 Fin15AnchoredAtom3915
    Fin15AnchoredAtom3916 Fin15AnchoredAtom3926 Fin15AnchoredAtom3951 Fin15AnchoredAtom3986
    Fin15AnchoredAtom4069 Fin15AnchoredAtom4073 Fin15AnchoredAtom4074 Fin15AnchoredAtom4084
    Fin15AnchoredAtom4085 Fin15AnchoredAtom4095 Fin15AnchoredAtom4105 Fin15AnchoredAtom4106
    Fin15AnchoredAtom4116 Fin15AnchoredAtom4141 Fin15AnchoredAtom4245 Fin15AnchoredAtom4246
    Fin15AnchoredAtom4256 Fin15AnchoredAtom4281 Fin15AnchoredAtom4316 Fin15AnchoredAtom4455
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

theorem fin15Anchored_clause32039 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3546 chi ∧
      ¬Fin15AnchoredAtom3549 chi ∧
      ¬Fin15AnchoredAtom3551 chi ∧
      ¬Fin15AnchoredAtom3552 chi ∧
      ¬Fin15AnchoredAtom3556 chi ∧
      ¬Fin15AnchoredAtom3558 chi ∧
      ¬Fin15AnchoredAtom3559 chi ∧
      ¬Fin15AnchoredAtom3573 chi ∧
      ¬Fin15AnchoredAtom3574 chi ∧
      ¬Fin15AnchoredAtom3579 chi ∧
      ¬Fin15AnchoredAtom3620 chi ∧
      ¬Fin15AnchoredAtom3622 chi ∧
      ¬Fin15AnchoredAtom3623 chi ∧
      ¬Fin15AnchoredAtom3637 chi ∧
      ¬Fin15AnchoredAtom3638 chi ∧
      ¬Fin15AnchoredAtom3643 chi ∧
      ¬Fin15AnchoredAtom3658 chi ∧
      ¬Fin15AnchoredAtom3659 chi ∧
      ¬Fin15AnchoredAtom3664 chi ∧
      ¬Fin15AnchoredAtom3695 chi ∧
      ¬Fin15AnchoredAtom3740 chi ∧
      ¬Fin15AnchoredAtom3742 chi ∧
      ¬Fin15AnchoredAtom3743 chi ∧
      ¬Fin15AnchoredAtom3757 chi ∧
      ¬Fin15AnchoredAtom3758 chi ∧
      ¬Fin15AnchoredAtom3763 chi ∧
      ¬Fin15AnchoredAtom3778 chi ∧
      ¬Fin15AnchoredAtom3779 chi ∧
      ¬Fin15AnchoredAtom3784 chi ∧
      ¬Fin15AnchoredAtom3815 chi ∧
      ¬Fin15AnchoredAtom3918 chi ∧
      ¬Fin15AnchoredAtom3919 chi ∧
      ¬Fin15AnchoredAtom3924 chi ∧
      ¬Fin15AnchoredAtom3955 chi ∧
      ¬Fin15AnchoredAtom3990 chi ∧
      ¬Fin15AnchoredAtom4070 chi ∧
      ¬Fin15AnchoredAtom4072 chi ∧
      ¬Fin15AnchoredAtom4073 chi ∧
      ¬Fin15AnchoredAtom4087 chi ∧
      ¬Fin15AnchoredAtom4088 chi ∧
      ¬Fin15AnchoredAtom4093 chi ∧
      ¬Fin15AnchoredAtom4108 chi ∧
      ¬Fin15AnchoredAtom4109 chi ∧
      ¬Fin15AnchoredAtom4114 chi ∧
      ¬Fin15AnchoredAtom4145 chi ∧
      ¬Fin15AnchoredAtom4248 chi ∧
      ¬Fin15AnchoredAtom4249 chi ∧
      ¬Fin15AnchoredAtom4254 chi ∧
      ¬Fin15AnchoredAtom4285 chi ∧
      ¬Fin15AnchoredAtom4320 chi ∧
      ¬Fin15AnchoredAtom4458 chi ∧
      ¬Fin15AnchoredAtom4459 chi ∧
      ¬Fin15AnchoredAtom4464 chi ∧
      ¬Fin15AnchoredAtom4495 chi ∧
      ¬Fin15AnchoredAtom4530 chi ∧
      ¬Fin15AnchoredAtom4726 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 6, 7, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13532
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3546 Fin15AnchoredAtom3549 Fin15AnchoredAtom3551
    Fin15AnchoredAtom3552 Fin15AnchoredAtom3556 Fin15AnchoredAtom3558 Fin15AnchoredAtom3559
    Fin15AnchoredAtom3573 Fin15AnchoredAtom3574 Fin15AnchoredAtom3579 Fin15AnchoredAtom3620
    Fin15AnchoredAtom3622 Fin15AnchoredAtom3623 Fin15AnchoredAtom3637 Fin15AnchoredAtom3638
    Fin15AnchoredAtom3643 Fin15AnchoredAtom3658 Fin15AnchoredAtom3659 Fin15AnchoredAtom3664
    Fin15AnchoredAtom3695 Fin15AnchoredAtom3740 Fin15AnchoredAtom3742 Fin15AnchoredAtom3743
    Fin15AnchoredAtom3757 Fin15AnchoredAtom3758 Fin15AnchoredAtom3763 Fin15AnchoredAtom3778
    Fin15AnchoredAtom3779 Fin15AnchoredAtom3784 Fin15AnchoredAtom3815 Fin15AnchoredAtom3918
    Fin15AnchoredAtom3919 Fin15AnchoredAtom3924 Fin15AnchoredAtom3955 Fin15AnchoredAtom3990
    Fin15AnchoredAtom4070 Fin15AnchoredAtom4072 Fin15AnchoredAtom4073 Fin15AnchoredAtom4087
    Fin15AnchoredAtom4088 Fin15AnchoredAtom4093 Fin15AnchoredAtom4108 Fin15AnchoredAtom4109
    Fin15AnchoredAtom4114 Fin15AnchoredAtom4145 Fin15AnchoredAtom4248 Fin15AnchoredAtom4249
    Fin15AnchoredAtom4254 Fin15AnchoredAtom4285 Fin15AnchoredAtom4320 Fin15AnchoredAtom4458
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

theorem fin15Anchored_clause32040 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3546 chi ∧
      ¬Fin15AnchoredAtom3549 chi ∧
      ¬Fin15AnchoredAtom3551 chi ∧
      ¬Fin15AnchoredAtom3553 chi ∧
      ¬Fin15AnchoredAtom3556 chi ∧
      ¬Fin15AnchoredAtom3558 chi ∧
      ¬Fin15AnchoredAtom3560 chi ∧
      ¬Fin15AnchoredAtom3573 chi ∧
      ¬Fin15AnchoredAtom3575 chi ∧
      ¬Fin15AnchoredAtom3580 chi ∧
      ¬Fin15AnchoredAtom3620 chi ∧
      ¬Fin15AnchoredAtom3622 chi ∧
      ¬Fin15AnchoredAtom3624 chi ∧
      ¬Fin15AnchoredAtom3637 chi ∧
      ¬Fin15AnchoredAtom3639 chi ∧
      ¬Fin15AnchoredAtom3644 chi ∧
      ¬Fin15AnchoredAtom3658 chi ∧
      ¬Fin15AnchoredAtom3660 chi ∧
      ¬Fin15AnchoredAtom3665 chi ∧
      ¬Fin15AnchoredAtom3696 chi ∧
      ¬Fin15AnchoredAtom3740 chi ∧
      ¬Fin15AnchoredAtom3742 chi ∧
      ¬Fin15AnchoredAtom3744 chi ∧
      ¬Fin15AnchoredAtom3757 chi ∧
      ¬Fin15AnchoredAtom3759 chi ∧
      ¬Fin15AnchoredAtom3764 chi ∧
      ¬Fin15AnchoredAtom3778 chi ∧
      ¬Fin15AnchoredAtom3780 chi ∧
      ¬Fin15AnchoredAtom3785 chi ∧
      ¬Fin15AnchoredAtom3816 chi ∧
      ¬Fin15AnchoredAtom3918 chi ∧
      ¬Fin15AnchoredAtom3920 chi ∧
      ¬Fin15AnchoredAtom3925 chi ∧
      ¬Fin15AnchoredAtom3956 chi ∧
      ¬Fin15AnchoredAtom3991 chi ∧
      ¬Fin15AnchoredAtom4070 chi ∧
      ¬Fin15AnchoredAtom4072 chi ∧
      ¬Fin15AnchoredAtom4074 chi ∧
      ¬Fin15AnchoredAtom4087 chi ∧
      ¬Fin15AnchoredAtom4089 chi ∧
      ¬Fin15AnchoredAtom4094 chi ∧
      ¬Fin15AnchoredAtom4108 chi ∧
      ¬Fin15AnchoredAtom4110 chi ∧
      ¬Fin15AnchoredAtom4115 chi ∧
      ¬Fin15AnchoredAtom4146 chi ∧
      ¬Fin15AnchoredAtom4248 chi ∧
      ¬Fin15AnchoredAtom4250 chi ∧
      ¬Fin15AnchoredAtom4255 chi ∧
      ¬Fin15AnchoredAtom4286 chi ∧
      ¬Fin15AnchoredAtom4321 chi ∧
      ¬Fin15AnchoredAtom4458 chi ∧
      ¬Fin15AnchoredAtom4460 chi ∧
      ¬Fin15AnchoredAtom4465 chi ∧
      ¬Fin15AnchoredAtom4496 chi ∧
      ¬Fin15AnchoredAtom4531 chi ∧
      ¬Fin15AnchoredAtom4727 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 6, 7, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21724
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3546 Fin15AnchoredAtom3549 Fin15AnchoredAtom3551
    Fin15AnchoredAtom3553 Fin15AnchoredAtom3556 Fin15AnchoredAtom3558 Fin15AnchoredAtom3560
    Fin15AnchoredAtom3573 Fin15AnchoredAtom3575 Fin15AnchoredAtom3580 Fin15AnchoredAtom3620
    Fin15AnchoredAtom3622 Fin15AnchoredAtom3624 Fin15AnchoredAtom3637 Fin15AnchoredAtom3639
    Fin15AnchoredAtom3644 Fin15AnchoredAtom3658 Fin15AnchoredAtom3660 Fin15AnchoredAtom3665
    Fin15AnchoredAtom3696 Fin15AnchoredAtom3740 Fin15AnchoredAtom3742 Fin15AnchoredAtom3744
    Fin15AnchoredAtom3757 Fin15AnchoredAtom3759 Fin15AnchoredAtom3764 Fin15AnchoredAtom3778
    Fin15AnchoredAtom3780 Fin15AnchoredAtom3785 Fin15AnchoredAtom3816 Fin15AnchoredAtom3918
    Fin15AnchoredAtom3920 Fin15AnchoredAtom3925 Fin15AnchoredAtom3956 Fin15AnchoredAtom3991
    Fin15AnchoredAtom4070 Fin15AnchoredAtom4072 Fin15AnchoredAtom4074 Fin15AnchoredAtom4087
    Fin15AnchoredAtom4089 Fin15AnchoredAtom4094 Fin15AnchoredAtom4108 Fin15AnchoredAtom4110
    Fin15AnchoredAtom4115 Fin15AnchoredAtom4146 Fin15AnchoredAtom4248 Fin15AnchoredAtom4250
    Fin15AnchoredAtom4255 Fin15AnchoredAtom4286 Fin15AnchoredAtom4321 Fin15AnchoredAtom4458
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

theorem fin15Anchored_clause32041 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3546 chi ∧
      ¬Fin15AnchoredAtom3549 chi ∧
      ¬Fin15AnchoredAtom3552 chi ∧
      ¬Fin15AnchoredAtom3553 chi ∧
      ¬Fin15AnchoredAtom3556 chi ∧
      ¬Fin15AnchoredAtom3559 chi ∧
      ¬Fin15AnchoredAtom3560 chi ∧
      ¬Fin15AnchoredAtom3574 chi ∧
      ¬Fin15AnchoredAtom3575 chi ∧
      ¬Fin15AnchoredAtom3581 chi ∧
      ¬Fin15AnchoredAtom3620 chi ∧
      ¬Fin15AnchoredAtom3623 chi ∧
      ¬Fin15AnchoredAtom3624 chi ∧
      ¬Fin15AnchoredAtom3638 chi ∧
      ¬Fin15AnchoredAtom3639 chi ∧
      ¬Fin15AnchoredAtom3645 chi ∧
      ¬Fin15AnchoredAtom3659 chi ∧
      ¬Fin15AnchoredAtom3660 chi ∧
      ¬Fin15AnchoredAtom3666 chi ∧
      ¬Fin15AnchoredAtom3697 chi ∧
      ¬Fin15AnchoredAtom3740 chi ∧
      ¬Fin15AnchoredAtom3743 chi ∧
      ¬Fin15AnchoredAtom3744 chi ∧
      ¬Fin15AnchoredAtom3758 chi ∧
      ¬Fin15AnchoredAtom3759 chi ∧
      ¬Fin15AnchoredAtom3765 chi ∧
      ¬Fin15AnchoredAtom3779 chi ∧
      ¬Fin15AnchoredAtom3780 chi ∧
      ¬Fin15AnchoredAtom3786 chi ∧
      ¬Fin15AnchoredAtom3817 chi ∧
      ¬Fin15AnchoredAtom3919 chi ∧
      ¬Fin15AnchoredAtom3920 chi ∧
      ¬Fin15AnchoredAtom3926 chi ∧
      ¬Fin15AnchoredAtom3957 chi ∧
      ¬Fin15AnchoredAtom3992 chi ∧
      ¬Fin15AnchoredAtom4070 chi ∧
      ¬Fin15AnchoredAtom4073 chi ∧
      ¬Fin15AnchoredAtom4074 chi ∧
      ¬Fin15AnchoredAtom4088 chi ∧
      ¬Fin15AnchoredAtom4089 chi ∧
      ¬Fin15AnchoredAtom4095 chi ∧
      ¬Fin15AnchoredAtom4109 chi ∧
      ¬Fin15AnchoredAtom4110 chi ∧
      ¬Fin15AnchoredAtom4116 chi ∧
      ¬Fin15AnchoredAtom4147 chi ∧
      ¬Fin15AnchoredAtom4249 chi ∧
      ¬Fin15AnchoredAtom4250 chi ∧
      ¬Fin15AnchoredAtom4256 chi ∧
      ¬Fin15AnchoredAtom4287 chi ∧
      ¬Fin15AnchoredAtom4322 chi ∧
      ¬Fin15AnchoredAtom4459 chi ∧
      ¬Fin15AnchoredAtom4460 chi ∧
      ¬Fin15AnchoredAtom4466 chi ∧
      ¬Fin15AnchoredAtom4497 chi ∧
      ¬Fin15AnchoredAtom4532 chi ∧
      ¬Fin15AnchoredAtom4728 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 6, 7, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25820
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3546 Fin15AnchoredAtom3549 Fin15AnchoredAtom3552
    Fin15AnchoredAtom3553 Fin15AnchoredAtom3556 Fin15AnchoredAtom3559 Fin15AnchoredAtom3560
    Fin15AnchoredAtom3574 Fin15AnchoredAtom3575 Fin15AnchoredAtom3581 Fin15AnchoredAtom3620
    Fin15AnchoredAtom3623 Fin15AnchoredAtom3624 Fin15AnchoredAtom3638 Fin15AnchoredAtom3639
    Fin15AnchoredAtom3645 Fin15AnchoredAtom3659 Fin15AnchoredAtom3660 Fin15AnchoredAtom3666
    Fin15AnchoredAtom3697 Fin15AnchoredAtom3740 Fin15AnchoredAtom3743 Fin15AnchoredAtom3744
    Fin15AnchoredAtom3758 Fin15AnchoredAtom3759 Fin15AnchoredAtom3765 Fin15AnchoredAtom3779
    Fin15AnchoredAtom3780 Fin15AnchoredAtom3786 Fin15AnchoredAtom3817 Fin15AnchoredAtom3919
    Fin15AnchoredAtom3920 Fin15AnchoredAtom3926 Fin15AnchoredAtom3957 Fin15AnchoredAtom3992
    Fin15AnchoredAtom4070 Fin15AnchoredAtom4073 Fin15AnchoredAtom4074 Fin15AnchoredAtom4088
    Fin15AnchoredAtom4089 Fin15AnchoredAtom4095 Fin15AnchoredAtom4109 Fin15AnchoredAtom4110
    Fin15AnchoredAtom4116 Fin15AnchoredAtom4147 Fin15AnchoredAtom4249 Fin15AnchoredAtom4250
    Fin15AnchoredAtom4256 Fin15AnchoredAtom4287 Fin15AnchoredAtom4322 Fin15AnchoredAtom4459
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

theorem fin15Anchored_clause32042 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3546 chi ∧
      ¬Fin15AnchoredAtom3551 chi ∧
      ¬Fin15AnchoredAtom3552 chi ∧
      ¬Fin15AnchoredAtom3553 chi ∧
      ¬Fin15AnchoredAtom3558 chi ∧
      ¬Fin15AnchoredAtom3559 chi ∧
      ¬Fin15AnchoredAtom3560 chi ∧
      ¬Fin15AnchoredAtom3579 chi ∧
      ¬Fin15AnchoredAtom3580 chi ∧
      ¬Fin15AnchoredAtom3581 chi ∧
      ¬Fin15AnchoredAtom3622 chi ∧
      ¬Fin15AnchoredAtom3623 chi ∧
      ¬Fin15AnchoredAtom3624 chi ∧
      ¬Fin15AnchoredAtom3643 chi ∧
      ¬Fin15AnchoredAtom3644 chi ∧
      ¬Fin15AnchoredAtom3645 chi ∧
      ¬Fin15AnchoredAtom3664 chi ∧
      ¬Fin15AnchoredAtom3665 chi ∧
      ¬Fin15AnchoredAtom3666 chi ∧
      ¬Fin15AnchoredAtom3701 chi ∧
      ¬Fin15AnchoredAtom3742 chi ∧
      ¬Fin15AnchoredAtom3743 chi ∧
      ¬Fin15AnchoredAtom3744 chi ∧
      ¬Fin15AnchoredAtom3763 chi ∧
      ¬Fin15AnchoredAtom3764 chi ∧
      ¬Fin15AnchoredAtom3765 chi ∧
      ¬Fin15AnchoredAtom3784 chi ∧
      ¬Fin15AnchoredAtom3785 chi ∧
      ¬Fin15AnchoredAtom3786 chi ∧
      ¬Fin15AnchoredAtom3821 chi ∧
      ¬Fin15AnchoredAtom3924 chi ∧
      ¬Fin15AnchoredAtom3925 chi ∧
      ¬Fin15AnchoredAtom3926 chi ∧
      ¬Fin15AnchoredAtom3961 chi ∧
      ¬Fin15AnchoredAtom3996 chi ∧
      ¬Fin15AnchoredAtom4072 chi ∧
      ¬Fin15AnchoredAtom4073 chi ∧
      ¬Fin15AnchoredAtom4074 chi ∧
      ¬Fin15AnchoredAtom4093 chi ∧
      ¬Fin15AnchoredAtom4094 chi ∧
      ¬Fin15AnchoredAtom4095 chi ∧
      ¬Fin15AnchoredAtom4114 chi ∧
      ¬Fin15AnchoredAtom4115 chi ∧
      ¬Fin15AnchoredAtom4116 chi ∧
      ¬Fin15AnchoredAtom4151 chi ∧
      ¬Fin15AnchoredAtom4254 chi ∧
      ¬Fin15AnchoredAtom4255 chi ∧
      ¬Fin15AnchoredAtom4256 chi ∧
      ¬Fin15AnchoredAtom4291 chi ∧
      ¬Fin15AnchoredAtom4326 chi ∧
      ¬Fin15AnchoredAtom4464 chi ∧
      ¬Fin15AnchoredAtom4465 chi ∧
      ¬Fin15AnchoredAtom4466 chi ∧
      ¬Fin15AnchoredAtom4501 chi ∧
      ¬Fin15AnchoredAtom4536 chi ∧
      ¬Fin15AnchoredAtom4732 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 6, 7, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask28892
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3546 Fin15AnchoredAtom3551 Fin15AnchoredAtom3552
    Fin15AnchoredAtom3553 Fin15AnchoredAtom3558 Fin15AnchoredAtom3559 Fin15AnchoredAtom3560
    Fin15AnchoredAtom3579 Fin15AnchoredAtom3580 Fin15AnchoredAtom3581 Fin15AnchoredAtom3622
    Fin15AnchoredAtom3623 Fin15AnchoredAtom3624 Fin15AnchoredAtom3643 Fin15AnchoredAtom3644
    Fin15AnchoredAtom3645 Fin15AnchoredAtom3664 Fin15AnchoredAtom3665 Fin15AnchoredAtom3666
    Fin15AnchoredAtom3701 Fin15AnchoredAtom3742 Fin15AnchoredAtom3743 Fin15AnchoredAtom3744
    Fin15AnchoredAtom3763 Fin15AnchoredAtom3764 Fin15AnchoredAtom3765 Fin15AnchoredAtom3784
    Fin15AnchoredAtom3785 Fin15AnchoredAtom3786 Fin15AnchoredAtom3821 Fin15AnchoredAtom3924
    Fin15AnchoredAtom3925 Fin15AnchoredAtom3926 Fin15AnchoredAtom3961 Fin15AnchoredAtom3996
    Fin15AnchoredAtom4072 Fin15AnchoredAtom4073 Fin15AnchoredAtom4074 Fin15AnchoredAtom4093
    Fin15AnchoredAtom4094 Fin15AnchoredAtom4095 Fin15AnchoredAtom4114 Fin15AnchoredAtom4115
    Fin15AnchoredAtom4116 Fin15AnchoredAtom4151 Fin15AnchoredAtom4254 Fin15AnchoredAtom4255
    Fin15AnchoredAtom4256 Fin15AnchoredAtom4291 Fin15AnchoredAtom4326 Fin15AnchoredAtom4464
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

theorem fin15Anchored_clause32043 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3548 chi ∧
      ¬Fin15AnchoredAtom3549 chi ∧
      ¬Fin15AnchoredAtom3551 chi ∧
      ¬Fin15AnchoredAtom3552 chi ∧
      ¬Fin15AnchoredAtom3567 chi ∧
      ¬Fin15AnchoredAtom3569 chi ∧
      ¬Fin15AnchoredAtom3570 chi ∧
      ¬Fin15AnchoredAtom3573 chi ∧
      ¬Fin15AnchoredAtom3574 chi ∧
      ¬Fin15AnchoredAtom3579 chi ∧
      ¬Fin15AnchoredAtom3631 chi ∧
      ¬Fin15AnchoredAtom3633 chi ∧
      ¬Fin15AnchoredAtom3634 chi ∧
      ¬Fin15AnchoredAtom3637 chi ∧
      ¬Fin15AnchoredAtom3638 chi ∧
      ¬Fin15AnchoredAtom3643 chi ∧
      ¬Fin15AnchoredAtom3683 chi ∧
      ¬Fin15AnchoredAtom3684 chi ∧
      ¬Fin15AnchoredAtom3689 chi ∧
      ¬Fin15AnchoredAtom3695 chi ∧
      ¬Fin15AnchoredAtom3751 chi ∧
      ¬Fin15AnchoredAtom3753 chi ∧
      ¬Fin15AnchoredAtom3754 chi ∧
      ¬Fin15AnchoredAtom3757 chi ∧
      ¬Fin15AnchoredAtom3758 chi ∧
      ¬Fin15AnchoredAtom3763 chi ∧
      ¬Fin15AnchoredAtom3803 chi ∧
      ¬Fin15AnchoredAtom3804 chi ∧
      ¬Fin15AnchoredAtom3809 chi ∧
      ¬Fin15AnchoredAtom3815 chi ∧
      ¬Fin15AnchoredAtom3943 chi ∧
      ¬Fin15AnchoredAtom3944 chi ∧
      ¬Fin15AnchoredAtom3949 chi ∧
      ¬Fin15AnchoredAtom3955 chi ∧
      ¬Fin15AnchoredAtom4020 chi ∧
      ¬Fin15AnchoredAtom4081 chi ∧
      ¬Fin15AnchoredAtom4083 chi ∧
      ¬Fin15AnchoredAtom4084 chi ∧
      ¬Fin15AnchoredAtom4087 chi ∧
      ¬Fin15AnchoredAtom4088 chi ∧
      ¬Fin15AnchoredAtom4093 chi ∧
      ¬Fin15AnchoredAtom4133 chi ∧
      ¬Fin15AnchoredAtom4134 chi ∧
      ¬Fin15AnchoredAtom4139 chi ∧
      ¬Fin15AnchoredAtom4145 chi ∧
      ¬Fin15AnchoredAtom4273 chi ∧
      ¬Fin15AnchoredAtom4274 chi ∧
      ¬Fin15AnchoredAtom4279 chi ∧
      ¬Fin15AnchoredAtom4285 chi ∧
      ¬Fin15AnchoredAtom4350 chi ∧
      ¬Fin15AnchoredAtom4483 chi ∧
      ¬Fin15AnchoredAtom4484 chi ∧
      ¬Fin15AnchoredAtom4489 chi ∧
      ¬Fin15AnchoredAtom4495 chi ∧
      ¬Fin15AnchoredAtom4560 chi ∧
      ¬Fin15AnchoredAtom4756 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 6, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13916
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3548 Fin15AnchoredAtom3549 Fin15AnchoredAtom3551
    Fin15AnchoredAtom3552 Fin15AnchoredAtom3567 Fin15AnchoredAtom3569 Fin15AnchoredAtom3570
    Fin15AnchoredAtom3573 Fin15AnchoredAtom3574 Fin15AnchoredAtom3579 Fin15AnchoredAtom3631
    Fin15AnchoredAtom3633 Fin15AnchoredAtom3634 Fin15AnchoredAtom3637 Fin15AnchoredAtom3638
    Fin15AnchoredAtom3643 Fin15AnchoredAtom3683 Fin15AnchoredAtom3684 Fin15AnchoredAtom3689
    Fin15AnchoredAtom3695 Fin15AnchoredAtom3751 Fin15AnchoredAtom3753 Fin15AnchoredAtom3754
    Fin15AnchoredAtom3757 Fin15AnchoredAtom3758 Fin15AnchoredAtom3763 Fin15AnchoredAtom3803
    Fin15AnchoredAtom3804 Fin15AnchoredAtom3809 Fin15AnchoredAtom3815 Fin15AnchoredAtom3943
    Fin15AnchoredAtom3944 Fin15AnchoredAtom3949 Fin15AnchoredAtom3955 Fin15AnchoredAtom4020
    Fin15AnchoredAtom4081 Fin15AnchoredAtom4083 Fin15AnchoredAtom4084 Fin15AnchoredAtom4087
    Fin15AnchoredAtom4088 Fin15AnchoredAtom4093 Fin15AnchoredAtom4133 Fin15AnchoredAtom4134
    Fin15AnchoredAtom4139 Fin15AnchoredAtom4145 Fin15AnchoredAtom4273 Fin15AnchoredAtom4274
    Fin15AnchoredAtom4279 Fin15AnchoredAtom4285 Fin15AnchoredAtom4350 Fin15AnchoredAtom4483
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

theorem fin15Anchored_clause32044 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3548 chi ∧
      ¬Fin15AnchoredAtom3549 chi ∧
      ¬Fin15AnchoredAtom3551 chi ∧
      ¬Fin15AnchoredAtom3553 chi ∧
      ¬Fin15AnchoredAtom3567 chi ∧
      ¬Fin15AnchoredAtom3569 chi ∧
      ¬Fin15AnchoredAtom3571 chi ∧
      ¬Fin15AnchoredAtom3573 chi ∧
      ¬Fin15AnchoredAtom3575 chi ∧
      ¬Fin15AnchoredAtom3580 chi ∧
      ¬Fin15AnchoredAtom3631 chi ∧
      ¬Fin15AnchoredAtom3633 chi ∧
      ¬Fin15AnchoredAtom3635 chi ∧
      ¬Fin15AnchoredAtom3637 chi ∧
      ¬Fin15AnchoredAtom3639 chi ∧
      ¬Fin15AnchoredAtom3644 chi ∧
      ¬Fin15AnchoredAtom3683 chi ∧
      ¬Fin15AnchoredAtom3685 chi ∧
      ¬Fin15AnchoredAtom3690 chi ∧
      ¬Fin15AnchoredAtom3696 chi ∧
      ¬Fin15AnchoredAtom3751 chi ∧
      ¬Fin15AnchoredAtom3753 chi ∧
      ¬Fin15AnchoredAtom3755 chi ∧
      ¬Fin15AnchoredAtom3757 chi ∧
      ¬Fin15AnchoredAtom3759 chi ∧
      ¬Fin15AnchoredAtom3764 chi ∧
      ¬Fin15AnchoredAtom3803 chi ∧
      ¬Fin15AnchoredAtom3805 chi ∧
      ¬Fin15AnchoredAtom3810 chi ∧
      ¬Fin15AnchoredAtom3816 chi ∧
      ¬Fin15AnchoredAtom3943 chi ∧
      ¬Fin15AnchoredAtom3945 chi ∧
      ¬Fin15AnchoredAtom3950 chi ∧
      ¬Fin15AnchoredAtom3956 chi ∧
      ¬Fin15AnchoredAtom4021 chi ∧
      ¬Fin15AnchoredAtom4081 chi ∧
      ¬Fin15AnchoredAtom4083 chi ∧
      ¬Fin15AnchoredAtom4085 chi ∧
      ¬Fin15AnchoredAtom4087 chi ∧
      ¬Fin15AnchoredAtom4089 chi ∧
      ¬Fin15AnchoredAtom4094 chi ∧
      ¬Fin15AnchoredAtom4133 chi ∧
      ¬Fin15AnchoredAtom4135 chi ∧
      ¬Fin15AnchoredAtom4140 chi ∧
      ¬Fin15AnchoredAtom4146 chi ∧
      ¬Fin15AnchoredAtom4273 chi ∧
      ¬Fin15AnchoredAtom4275 chi ∧
      ¬Fin15AnchoredAtom4280 chi ∧
      ¬Fin15AnchoredAtom4286 chi ∧
      ¬Fin15AnchoredAtom4351 chi ∧
      ¬Fin15AnchoredAtom4483 chi ∧
      ¬Fin15AnchoredAtom4485 chi ∧
      ¬Fin15AnchoredAtom4490 chi ∧
      ¬Fin15AnchoredAtom4496 chi ∧
      ¬Fin15AnchoredAtom4561 chi ∧
      ¬Fin15AnchoredAtom4757 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 6, 9, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22108
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3548 Fin15AnchoredAtom3549 Fin15AnchoredAtom3551
    Fin15AnchoredAtom3553 Fin15AnchoredAtom3567 Fin15AnchoredAtom3569 Fin15AnchoredAtom3571
    Fin15AnchoredAtom3573 Fin15AnchoredAtom3575 Fin15AnchoredAtom3580 Fin15AnchoredAtom3631
    Fin15AnchoredAtom3633 Fin15AnchoredAtom3635 Fin15AnchoredAtom3637 Fin15AnchoredAtom3639
    Fin15AnchoredAtom3644 Fin15AnchoredAtom3683 Fin15AnchoredAtom3685 Fin15AnchoredAtom3690
    Fin15AnchoredAtom3696 Fin15AnchoredAtom3751 Fin15AnchoredAtom3753 Fin15AnchoredAtom3755
    Fin15AnchoredAtom3757 Fin15AnchoredAtom3759 Fin15AnchoredAtom3764 Fin15AnchoredAtom3803
    Fin15AnchoredAtom3805 Fin15AnchoredAtom3810 Fin15AnchoredAtom3816 Fin15AnchoredAtom3943
    Fin15AnchoredAtom3945 Fin15AnchoredAtom3950 Fin15AnchoredAtom3956 Fin15AnchoredAtom4021
    Fin15AnchoredAtom4081 Fin15AnchoredAtom4083 Fin15AnchoredAtom4085 Fin15AnchoredAtom4087
    Fin15AnchoredAtom4089 Fin15AnchoredAtom4094 Fin15AnchoredAtom4133 Fin15AnchoredAtom4135
    Fin15AnchoredAtom4140 Fin15AnchoredAtom4146 Fin15AnchoredAtom4273 Fin15AnchoredAtom4275
    Fin15AnchoredAtom4280 Fin15AnchoredAtom4286 Fin15AnchoredAtom4351 Fin15AnchoredAtom4483
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

theorem fin15Anchored_clause32045 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3548 chi ∧
      ¬Fin15AnchoredAtom3549 chi ∧
      ¬Fin15AnchoredAtom3552 chi ∧
      ¬Fin15AnchoredAtom3553 chi ∧
      ¬Fin15AnchoredAtom3567 chi ∧
      ¬Fin15AnchoredAtom3570 chi ∧
      ¬Fin15AnchoredAtom3571 chi ∧
      ¬Fin15AnchoredAtom3574 chi ∧
      ¬Fin15AnchoredAtom3575 chi ∧
      ¬Fin15AnchoredAtom3581 chi ∧
      ¬Fin15AnchoredAtom3631 chi ∧
      ¬Fin15AnchoredAtom3634 chi ∧
      ¬Fin15AnchoredAtom3635 chi ∧
      ¬Fin15AnchoredAtom3638 chi ∧
      ¬Fin15AnchoredAtom3639 chi ∧
      ¬Fin15AnchoredAtom3645 chi ∧
      ¬Fin15AnchoredAtom3684 chi ∧
      ¬Fin15AnchoredAtom3685 chi ∧
      ¬Fin15AnchoredAtom3691 chi ∧
      ¬Fin15AnchoredAtom3697 chi ∧
      ¬Fin15AnchoredAtom3751 chi ∧
      ¬Fin15AnchoredAtom3754 chi ∧
      ¬Fin15AnchoredAtom3755 chi ∧
      ¬Fin15AnchoredAtom3758 chi ∧
      ¬Fin15AnchoredAtom3759 chi ∧
      ¬Fin15AnchoredAtom3765 chi ∧
      ¬Fin15AnchoredAtom3804 chi ∧
      ¬Fin15AnchoredAtom3805 chi ∧
      ¬Fin15AnchoredAtom3811 chi ∧
      ¬Fin15AnchoredAtom3817 chi ∧
      ¬Fin15AnchoredAtom3944 chi ∧
      ¬Fin15AnchoredAtom3945 chi ∧
      ¬Fin15AnchoredAtom3951 chi ∧
      ¬Fin15AnchoredAtom3957 chi ∧
      ¬Fin15AnchoredAtom4022 chi ∧
      ¬Fin15AnchoredAtom4081 chi ∧
      ¬Fin15AnchoredAtom4084 chi ∧
      ¬Fin15AnchoredAtom4085 chi ∧
      ¬Fin15AnchoredAtom4088 chi ∧
      ¬Fin15AnchoredAtom4089 chi ∧
      ¬Fin15AnchoredAtom4095 chi ∧
      ¬Fin15AnchoredAtom4134 chi ∧
      ¬Fin15AnchoredAtom4135 chi ∧
      ¬Fin15AnchoredAtom4141 chi ∧
      ¬Fin15AnchoredAtom4147 chi ∧
      ¬Fin15AnchoredAtom4274 chi ∧
      ¬Fin15AnchoredAtom4275 chi ∧
      ¬Fin15AnchoredAtom4281 chi ∧
      ¬Fin15AnchoredAtom4287 chi ∧
      ¬Fin15AnchoredAtom4352 chi ∧
      ¬Fin15AnchoredAtom4484 chi ∧
      ¬Fin15AnchoredAtom4485 chi ∧
      ¬Fin15AnchoredAtom4491 chi ∧
      ¬Fin15AnchoredAtom4497 chi ∧
      ¬Fin15AnchoredAtom4562 chi ∧
      ¬Fin15AnchoredAtom4758 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 6, 9, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26204
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3548 Fin15AnchoredAtom3549 Fin15AnchoredAtom3552
    Fin15AnchoredAtom3553 Fin15AnchoredAtom3567 Fin15AnchoredAtom3570 Fin15AnchoredAtom3571
    Fin15AnchoredAtom3574 Fin15AnchoredAtom3575 Fin15AnchoredAtom3581 Fin15AnchoredAtom3631
    Fin15AnchoredAtom3634 Fin15AnchoredAtom3635 Fin15AnchoredAtom3638 Fin15AnchoredAtom3639
    Fin15AnchoredAtom3645 Fin15AnchoredAtom3684 Fin15AnchoredAtom3685 Fin15AnchoredAtom3691
    Fin15AnchoredAtom3697 Fin15AnchoredAtom3751 Fin15AnchoredAtom3754 Fin15AnchoredAtom3755
    Fin15AnchoredAtom3758 Fin15AnchoredAtom3759 Fin15AnchoredAtom3765 Fin15AnchoredAtom3804
    Fin15AnchoredAtom3805 Fin15AnchoredAtom3811 Fin15AnchoredAtom3817 Fin15AnchoredAtom3944
    Fin15AnchoredAtom3945 Fin15AnchoredAtom3951 Fin15AnchoredAtom3957 Fin15AnchoredAtom4022
    Fin15AnchoredAtom4081 Fin15AnchoredAtom4084 Fin15AnchoredAtom4085 Fin15AnchoredAtom4088
    Fin15AnchoredAtom4089 Fin15AnchoredAtom4095 Fin15AnchoredAtom4134 Fin15AnchoredAtom4135
    Fin15AnchoredAtom4141 Fin15AnchoredAtom4147 Fin15AnchoredAtom4274 Fin15AnchoredAtom4275
    Fin15AnchoredAtom4281 Fin15AnchoredAtom4287 Fin15AnchoredAtom4352 Fin15AnchoredAtom4484
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

theorem fin15Anchored_clause32046 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3548 chi ∧
      ¬Fin15AnchoredAtom3551 chi ∧
      ¬Fin15AnchoredAtom3552 chi ∧
      ¬Fin15AnchoredAtom3553 chi ∧
      ¬Fin15AnchoredAtom3569 chi ∧
      ¬Fin15AnchoredAtom3570 chi ∧
      ¬Fin15AnchoredAtom3571 chi ∧
      ¬Fin15AnchoredAtom3579 chi ∧
      ¬Fin15AnchoredAtom3580 chi ∧
      ¬Fin15AnchoredAtom3581 chi ∧
      ¬Fin15AnchoredAtom3633 chi ∧
      ¬Fin15AnchoredAtom3634 chi ∧
      ¬Fin15AnchoredAtom3635 chi ∧
      ¬Fin15AnchoredAtom3643 chi ∧
      ¬Fin15AnchoredAtom3644 chi ∧
      ¬Fin15AnchoredAtom3645 chi ∧
      ¬Fin15AnchoredAtom3689 chi ∧
      ¬Fin15AnchoredAtom3690 chi ∧
      ¬Fin15AnchoredAtom3691 chi ∧
      ¬Fin15AnchoredAtom3701 chi ∧
      ¬Fin15AnchoredAtom3753 chi ∧
      ¬Fin15AnchoredAtom3754 chi ∧
      ¬Fin15AnchoredAtom3755 chi ∧
      ¬Fin15AnchoredAtom3763 chi ∧
      ¬Fin15AnchoredAtom3764 chi ∧
      ¬Fin15AnchoredAtom3765 chi ∧
      ¬Fin15AnchoredAtom3809 chi ∧
      ¬Fin15AnchoredAtom3810 chi ∧
      ¬Fin15AnchoredAtom3811 chi ∧
      ¬Fin15AnchoredAtom3821 chi ∧
      ¬Fin15AnchoredAtom3949 chi ∧
      ¬Fin15AnchoredAtom3950 chi ∧
      ¬Fin15AnchoredAtom3951 chi ∧
      ¬Fin15AnchoredAtom3961 chi ∧
      ¬Fin15AnchoredAtom4026 chi ∧
      ¬Fin15AnchoredAtom4083 chi ∧
      ¬Fin15AnchoredAtom4084 chi ∧
      ¬Fin15AnchoredAtom4085 chi ∧
      ¬Fin15AnchoredAtom4093 chi ∧
      ¬Fin15AnchoredAtom4094 chi ∧
      ¬Fin15AnchoredAtom4095 chi ∧
      ¬Fin15AnchoredAtom4139 chi ∧
      ¬Fin15AnchoredAtom4140 chi ∧
      ¬Fin15AnchoredAtom4141 chi ∧
      ¬Fin15AnchoredAtom4151 chi ∧
      ¬Fin15AnchoredAtom4279 chi ∧
      ¬Fin15AnchoredAtom4280 chi ∧
      ¬Fin15AnchoredAtom4281 chi ∧
      ¬Fin15AnchoredAtom4291 chi ∧
      ¬Fin15AnchoredAtom4356 chi ∧
      ¬Fin15AnchoredAtom4489 chi ∧
      ¬Fin15AnchoredAtom4490 chi ∧
      ¬Fin15AnchoredAtom4491 chi ∧
      ¬Fin15AnchoredAtom4501 chi ∧
      ¬Fin15AnchoredAtom4566 chi ∧
      ¬Fin15AnchoredAtom4762 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 6, 9, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29276
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3548 Fin15AnchoredAtom3551 Fin15AnchoredAtom3552
    Fin15AnchoredAtom3553 Fin15AnchoredAtom3569 Fin15AnchoredAtom3570 Fin15AnchoredAtom3571
    Fin15AnchoredAtom3579 Fin15AnchoredAtom3580 Fin15AnchoredAtom3581 Fin15AnchoredAtom3633
    Fin15AnchoredAtom3634 Fin15AnchoredAtom3635 Fin15AnchoredAtom3643 Fin15AnchoredAtom3644
    Fin15AnchoredAtom3645 Fin15AnchoredAtom3689 Fin15AnchoredAtom3690 Fin15AnchoredAtom3691
    Fin15AnchoredAtom3701 Fin15AnchoredAtom3753 Fin15AnchoredAtom3754 Fin15AnchoredAtom3755
    Fin15AnchoredAtom3763 Fin15AnchoredAtom3764 Fin15AnchoredAtom3765 Fin15AnchoredAtom3809
    Fin15AnchoredAtom3810 Fin15AnchoredAtom3811 Fin15AnchoredAtom3821 Fin15AnchoredAtom3949
    Fin15AnchoredAtom3950 Fin15AnchoredAtom3951 Fin15AnchoredAtom3961 Fin15AnchoredAtom4026
    Fin15AnchoredAtom4083 Fin15AnchoredAtom4084 Fin15AnchoredAtom4085 Fin15AnchoredAtom4093
    Fin15AnchoredAtom4094 Fin15AnchoredAtom4095 Fin15AnchoredAtom4139 Fin15AnchoredAtom4140
    Fin15AnchoredAtom4141 Fin15AnchoredAtom4151 Fin15AnchoredAtom4279 Fin15AnchoredAtom4280
    Fin15AnchoredAtom4281 Fin15AnchoredAtom4291 Fin15AnchoredAtom4356 Fin15AnchoredAtom4489
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

theorem fin15Anchored_clause32047 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3549 chi ∧
      ¬Fin15AnchoredAtom3551 chi ∧
      ¬Fin15AnchoredAtom3552 chi ∧
      ¬Fin15AnchoredAtom3553 chi ∧
      ¬Fin15AnchoredAtom3573 chi ∧
      ¬Fin15AnchoredAtom3574 chi ∧
      ¬Fin15AnchoredAtom3575 chi ∧
      ¬Fin15AnchoredAtom3579 chi ∧
      ¬Fin15AnchoredAtom3580 chi ∧
      ¬Fin15AnchoredAtom3581 chi ∧
      ¬Fin15AnchoredAtom3637 chi ∧
      ¬Fin15AnchoredAtom3638 chi ∧
      ¬Fin15AnchoredAtom3639 chi ∧
      ¬Fin15AnchoredAtom3643 chi ∧
      ¬Fin15AnchoredAtom3644 chi ∧
      ¬Fin15AnchoredAtom3645 chi ∧
      ¬Fin15AnchoredAtom3695 chi ∧
      ¬Fin15AnchoredAtom3696 chi ∧
      ¬Fin15AnchoredAtom3697 chi ∧
      ¬Fin15AnchoredAtom3701 chi ∧
      ¬Fin15AnchoredAtom3757 chi ∧
      ¬Fin15AnchoredAtom3758 chi ∧
      ¬Fin15AnchoredAtom3759 chi ∧
      ¬Fin15AnchoredAtom3763 chi ∧
      ¬Fin15AnchoredAtom3764 chi ∧
      ¬Fin15AnchoredAtom3765 chi ∧
      ¬Fin15AnchoredAtom3815 chi ∧
      ¬Fin15AnchoredAtom3816 chi ∧
      ¬Fin15AnchoredAtom3817 chi ∧
      ¬Fin15AnchoredAtom3821 chi ∧
      ¬Fin15AnchoredAtom3955 chi ∧
      ¬Fin15AnchoredAtom3956 chi ∧
      ¬Fin15AnchoredAtom3957 chi ∧
      ¬Fin15AnchoredAtom3961 chi ∧
      ¬Fin15AnchoredAtom4030 chi ∧
      ¬Fin15AnchoredAtom4087 chi ∧
      ¬Fin15AnchoredAtom4088 chi ∧
      ¬Fin15AnchoredAtom4089 chi ∧
      ¬Fin15AnchoredAtom4093 chi ∧
      ¬Fin15AnchoredAtom4094 chi ∧
      ¬Fin15AnchoredAtom4095 chi ∧
      ¬Fin15AnchoredAtom4145 chi ∧
      ¬Fin15AnchoredAtom4146 chi ∧
      ¬Fin15AnchoredAtom4147 chi ∧
      ¬Fin15AnchoredAtom4151 chi ∧
      ¬Fin15AnchoredAtom4285 chi ∧
      ¬Fin15AnchoredAtom4286 chi ∧
      ¬Fin15AnchoredAtom4287 chi ∧
      ¬Fin15AnchoredAtom4291 chi ∧
      ¬Fin15AnchoredAtom4360 chi ∧
      ¬Fin15AnchoredAtom4495 chi ∧
      ¬Fin15AnchoredAtom4496 chi ∧
      ¬Fin15AnchoredAtom4497 chi ∧
      ¬Fin15AnchoredAtom4501 chi ∧
      ¬Fin15AnchoredAtom4570 chi ∧
      ¬Fin15AnchoredAtom4766 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 6, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29788
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3549 Fin15AnchoredAtom3551 Fin15AnchoredAtom3552
    Fin15AnchoredAtom3553 Fin15AnchoredAtom3573 Fin15AnchoredAtom3574 Fin15AnchoredAtom3575
    Fin15AnchoredAtom3579 Fin15AnchoredAtom3580 Fin15AnchoredAtom3581 Fin15AnchoredAtom3637
    Fin15AnchoredAtom3638 Fin15AnchoredAtom3639 Fin15AnchoredAtom3643 Fin15AnchoredAtom3644
    Fin15AnchoredAtom3645 Fin15AnchoredAtom3695 Fin15AnchoredAtom3696 Fin15AnchoredAtom3697
    Fin15AnchoredAtom3701 Fin15AnchoredAtom3757 Fin15AnchoredAtom3758 Fin15AnchoredAtom3759
    Fin15AnchoredAtom3763 Fin15AnchoredAtom3764 Fin15AnchoredAtom3765 Fin15AnchoredAtom3815
    Fin15AnchoredAtom3816 Fin15AnchoredAtom3817 Fin15AnchoredAtom3821 Fin15AnchoredAtom3955
    Fin15AnchoredAtom3956 Fin15AnchoredAtom3957 Fin15AnchoredAtom3961 Fin15AnchoredAtom4030
    Fin15AnchoredAtom4087 Fin15AnchoredAtom4088 Fin15AnchoredAtom4089 Fin15AnchoredAtom4093
    Fin15AnchoredAtom4094 Fin15AnchoredAtom4095 Fin15AnchoredAtom4145 Fin15AnchoredAtom4146
    Fin15AnchoredAtom4147 Fin15AnchoredAtom4151 Fin15AnchoredAtom4285 Fin15AnchoredAtom4286
    Fin15AnchoredAtom4287 Fin15AnchoredAtom4291 Fin15AnchoredAtom4360 Fin15AnchoredAtom4495
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

theorem fin15Anchored_clause32048 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3555 chi ∧
      ¬Fin15AnchoredAtom3556 chi ∧
      ¬Fin15AnchoredAtom3558 chi ∧
      ¬Fin15AnchoredAtom3559 chi ∧
      ¬Fin15AnchoredAtom3567 chi ∧
      ¬Fin15AnchoredAtom3569 chi ∧
      ¬Fin15AnchoredAtom3570 chi ∧
      ¬Fin15AnchoredAtom3573 chi ∧
      ¬Fin15AnchoredAtom3574 chi ∧
      ¬Fin15AnchoredAtom3579 chi ∧
      ¬Fin15AnchoredAtom3652 chi ∧
      ¬Fin15AnchoredAtom3654 chi ∧
      ¬Fin15AnchoredAtom3655 chi ∧
      ¬Fin15AnchoredAtom3658 chi ∧
      ¬Fin15AnchoredAtom3659 chi ∧
      ¬Fin15AnchoredAtom3664 chi ∧
      ¬Fin15AnchoredAtom3683 chi ∧
      ¬Fin15AnchoredAtom3684 chi ∧
      ¬Fin15AnchoredAtom3689 chi ∧
      ¬Fin15AnchoredAtom3695 chi ∧
      ¬Fin15AnchoredAtom3772 chi ∧
      ¬Fin15AnchoredAtom3774 chi ∧
      ¬Fin15AnchoredAtom3775 chi ∧
      ¬Fin15AnchoredAtom3778 chi ∧
      ¬Fin15AnchoredAtom3779 chi ∧
      ¬Fin15AnchoredAtom3784 chi ∧
      ¬Fin15AnchoredAtom3803 chi ∧
      ¬Fin15AnchoredAtom3804 chi ∧
      ¬Fin15AnchoredAtom3809 chi ∧
      ¬Fin15AnchoredAtom3815 chi ∧
      ¬Fin15AnchoredAtom3978 chi ∧
      ¬Fin15AnchoredAtom3979 chi ∧
      ¬Fin15AnchoredAtom3984 chi ∧
      ¬Fin15AnchoredAtom3990 chi ∧
      ¬Fin15AnchoredAtom4020 chi ∧
      ¬Fin15AnchoredAtom4102 chi ∧
      ¬Fin15AnchoredAtom4104 chi ∧
      ¬Fin15AnchoredAtom4105 chi ∧
      ¬Fin15AnchoredAtom4108 chi ∧
      ¬Fin15AnchoredAtom4109 chi ∧
      ¬Fin15AnchoredAtom4114 chi ∧
      ¬Fin15AnchoredAtom4133 chi ∧
      ¬Fin15AnchoredAtom4134 chi ∧
      ¬Fin15AnchoredAtom4139 chi ∧
      ¬Fin15AnchoredAtom4145 chi ∧
      ¬Fin15AnchoredAtom4308 chi ∧
      ¬Fin15AnchoredAtom4309 chi ∧
      ¬Fin15AnchoredAtom4314 chi ∧
      ¬Fin15AnchoredAtom4320 chi ∧
      ¬Fin15AnchoredAtom4350 chi ∧
      ¬Fin15AnchoredAtom4518 chi ∧
      ¬Fin15AnchoredAtom4519 chi ∧
      ¬Fin15AnchoredAtom4524 chi ∧
      ¬Fin15AnchoredAtom4530 chi ∧
      ¬Fin15AnchoredAtom4560 chi ∧
      ¬Fin15AnchoredAtom4791 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 7, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13980
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3555 Fin15AnchoredAtom3556 Fin15AnchoredAtom3558
    Fin15AnchoredAtom3559 Fin15AnchoredAtom3567 Fin15AnchoredAtom3569 Fin15AnchoredAtom3570
    Fin15AnchoredAtom3573 Fin15AnchoredAtom3574 Fin15AnchoredAtom3579 Fin15AnchoredAtom3652
    Fin15AnchoredAtom3654 Fin15AnchoredAtom3655 Fin15AnchoredAtom3658 Fin15AnchoredAtom3659
    Fin15AnchoredAtom3664 Fin15AnchoredAtom3683 Fin15AnchoredAtom3684 Fin15AnchoredAtom3689
    Fin15AnchoredAtom3695 Fin15AnchoredAtom3772 Fin15AnchoredAtom3774 Fin15AnchoredAtom3775
    Fin15AnchoredAtom3778 Fin15AnchoredAtom3779 Fin15AnchoredAtom3784 Fin15AnchoredAtom3803
    Fin15AnchoredAtom3804 Fin15AnchoredAtom3809 Fin15AnchoredAtom3815 Fin15AnchoredAtom3978
    Fin15AnchoredAtom3979 Fin15AnchoredAtom3984 Fin15AnchoredAtom3990 Fin15AnchoredAtom4020
    Fin15AnchoredAtom4102 Fin15AnchoredAtom4104 Fin15AnchoredAtom4105 Fin15AnchoredAtom4108
    Fin15AnchoredAtom4109 Fin15AnchoredAtom4114 Fin15AnchoredAtom4133 Fin15AnchoredAtom4134
    Fin15AnchoredAtom4139 Fin15AnchoredAtom4145 Fin15AnchoredAtom4308 Fin15AnchoredAtom4309
    Fin15AnchoredAtom4314 Fin15AnchoredAtom4320 Fin15AnchoredAtom4350 Fin15AnchoredAtom4518
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

theorem fin15Anchored_clause32049 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3555 chi ∧
      ¬Fin15AnchoredAtom3556 chi ∧
      ¬Fin15AnchoredAtom3558 chi ∧
      ¬Fin15AnchoredAtom3560 chi ∧
      ¬Fin15AnchoredAtom3567 chi ∧
      ¬Fin15AnchoredAtom3569 chi ∧
      ¬Fin15AnchoredAtom3571 chi ∧
      ¬Fin15AnchoredAtom3573 chi ∧
      ¬Fin15AnchoredAtom3575 chi ∧
      ¬Fin15AnchoredAtom3580 chi ∧
      ¬Fin15AnchoredAtom3652 chi ∧
      ¬Fin15AnchoredAtom3654 chi ∧
      ¬Fin15AnchoredAtom3656 chi ∧
      ¬Fin15AnchoredAtom3658 chi ∧
      ¬Fin15AnchoredAtom3660 chi ∧
      ¬Fin15AnchoredAtom3665 chi ∧
      ¬Fin15AnchoredAtom3683 chi ∧
      ¬Fin15AnchoredAtom3685 chi ∧
      ¬Fin15AnchoredAtom3690 chi ∧
      ¬Fin15AnchoredAtom3696 chi ∧
      ¬Fin15AnchoredAtom3772 chi ∧
      ¬Fin15AnchoredAtom3774 chi ∧
      ¬Fin15AnchoredAtom3776 chi ∧
      ¬Fin15AnchoredAtom3778 chi ∧
      ¬Fin15AnchoredAtom3780 chi ∧
      ¬Fin15AnchoredAtom3785 chi ∧
      ¬Fin15AnchoredAtom3803 chi ∧
      ¬Fin15AnchoredAtom3805 chi ∧
      ¬Fin15AnchoredAtom3810 chi ∧
      ¬Fin15AnchoredAtom3816 chi ∧
      ¬Fin15AnchoredAtom3978 chi ∧
      ¬Fin15AnchoredAtom3980 chi ∧
      ¬Fin15AnchoredAtom3985 chi ∧
      ¬Fin15AnchoredAtom3991 chi ∧
      ¬Fin15AnchoredAtom4021 chi ∧
      ¬Fin15AnchoredAtom4102 chi ∧
      ¬Fin15AnchoredAtom4104 chi ∧
      ¬Fin15AnchoredAtom4106 chi ∧
      ¬Fin15AnchoredAtom4108 chi ∧
      ¬Fin15AnchoredAtom4110 chi ∧
      ¬Fin15AnchoredAtom4115 chi ∧
      ¬Fin15AnchoredAtom4133 chi ∧
      ¬Fin15AnchoredAtom4135 chi ∧
      ¬Fin15AnchoredAtom4140 chi ∧
      ¬Fin15AnchoredAtom4146 chi ∧
      ¬Fin15AnchoredAtom4308 chi ∧
      ¬Fin15AnchoredAtom4310 chi ∧
      ¬Fin15AnchoredAtom4315 chi ∧
      ¬Fin15AnchoredAtom4321 chi ∧
      ¬Fin15AnchoredAtom4351 chi ∧
      ¬Fin15AnchoredAtom4518 chi ∧
      ¬Fin15AnchoredAtom4520 chi ∧
      ¬Fin15AnchoredAtom4525 chi ∧
      ¬Fin15AnchoredAtom4531 chi ∧
      ¬Fin15AnchoredAtom4561 chi ∧
      ¬Fin15AnchoredAtom4792 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 7, 9, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22172
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3555 Fin15AnchoredAtom3556 Fin15AnchoredAtom3558
    Fin15AnchoredAtom3560 Fin15AnchoredAtom3567 Fin15AnchoredAtom3569 Fin15AnchoredAtom3571
    Fin15AnchoredAtom3573 Fin15AnchoredAtom3575 Fin15AnchoredAtom3580 Fin15AnchoredAtom3652
    Fin15AnchoredAtom3654 Fin15AnchoredAtom3656 Fin15AnchoredAtom3658 Fin15AnchoredAtom3660
    Fin15AnchoredAtom3665 Fin15AnchoredAtom3683 Fin15AnchoredAtom3685 Fin15AnchoredAtom3690
    Fin15AnchoredAtom3696 Fin15AnchoredAtom3772 Fin15AnchoredAtom3774 Fin15AnchoredAtom3776
    Fin15AnchoredAtom3778 Fin15AnchoredAtom3780 Fin15AnchoredAtom3785 Fin15AnchoredAtom3803
    Fin15AnchoredAtom3805 Fin15AnchoredAtom3810 Fin15AnchoredAtom3816 Fin15AnchoredAtom3978
    Fin15AnchoredAtom3980 Fin15AnchoredAtom3985 Fin15AnchoredAtom3991 Fin15AnchoredAtom4021
    Fin15AnchoredAtom4102 Fin15AnchoredAtom4104 Fin15AnchoredAtom4106 Fin15AnchoredAtom4108
    Fin15AnchoredAtom4110 Fin15AnchoredAtom4115 Fin15AnchoredAtom4133 Fin15AnchoredAtom4135
    Fin15AnchoredAtom4140 Fin15AnchoredAtom4146 Fin15AnchoredAtom4308 Fin15AnchoredAtom4310
    Fin15AnchoredAtom4315 Fin15AnchoredAtom4321 Fin15AnchoredAtom4351 Fin15AnchoredAtom4518
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

theorem fin15Anchored_clause32050 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3555 chi ∧
      ¬Fin15AnchoredAtom3556 chi ∧
      ¬Fin15AnchoredAtom3559 chi ∧
      ¬Fin15AnchoredAtom3560 chi ∧
      ¬Fin15AnchoredAtom3567 chi ∧
      ¬Fin15AnchoredAtom3570 chi ∧
      ¬Fin15AnchoredAtom3571 chi ∧
      ¬Fin15AnchoredAtom3574 chi ∧
      ¬Fin15AnchoredAtom3575 chi ∧
      ¬Fin15AnchoredAtom3581 chi ∧
      ¬Fin15AnchoredAtom3652 chi ∧
      ¬Fin15AnchoredAtom3655 chi ∧
      ¬Fin15AnchoredAtom3656 chi ∧
      ¬Fin15AnchoredAtom3659 chi ∧
      ¬Fin15AnchoredAtom3660 chi ∧
      ¬Fin15AnchoredAtom3666 chi ∧
      ¬Fin15AnchoredAtom3684 chi ∧
      ¬Fin15AnchoredAtom3685 chi ∧
      ¬Fin15AnchoredAtom3691 chi ∧
      ¬Fin15AnchoredAtom3697 chi ∧
      ¬Fin15AnchoredAtom3772 chi ∧
      ¬Fin15AnchoredAtom3775 chi ∧
      ¬Fin15AnchoredAtom3776 chi ∧
      ¬Fin15AnchoredAtom3779 chi ∧
      ¬Fin15AnchoredAtom3780 chi ∧
      ¬Fin15AnchoredAtom3786 chi ∧
      ¬Fin15AnchoredAtom3804 chi ∧
      ¬Fin15AnchoredAtom3805 chi ∧
      ¬Fin15AnchoredAtom3811 chi ∧
      ¬Fin15AnchoredAtom3817 chi ∧
      ¬Fin15AnchoredAtom3979 chi ∧
      ¬Fin15AnchoredAtom3980 chi ∧
      ¬Fin15AnchoredAtom3986 chi ∧
      ¬Fin15AnchoredAtom3992 chi ∧
      ¬Fin15AnchoredAtom4022 chi ∧
      ¬Fin15AnchoredAtom4102 chi ∧
      ¬Fin15AnchoredAtom4105 chi ∧
      ¬Fin15AnchoredAtom4106 chi ∧
      ¬Fin15AnchoredAtom4109 chi ∧
      ¬Fin15AnchoredAtom4110 chi ∧
      ¬Fin15AnchoredAtom4116 chi ∧
      ¬Fin15AnchoredAtom4134 chi ∧
      ¬Fin15AnchoredAtom4135 chi ∧
      ¬Fin15AnchoredAtom4141 chi ∧
      ¬Fin15AnchoredAtom4147 chi ∧
      ¬Fin15AnchoredAtom4309 chi ∧
      ¬Fin15AnchoredAtom4310 chi ∧
      ¬Fin15AnchoredAtom4316 chi ∧
      ¬Fin15AnchoredAtom4322 chi ∧
      ¬Fin15AnchoredAtom4352 chi ∧
      ¬Fin15AnchoredAtom4519 chi ∧
      ¬Fin15AnchoredAtom4520 chi ∧
      ¬Fin15AnchoredAtom4526 chi ∧
      ¬Fin15AnchoredAtom4532 chi ∧
      ¬Fin15AnchoredAtom4562 chi ∧
      ¬Fin15AnchoredAtom4793 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 7, 9, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26268
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3555 Fin15AnchoredAtom3556 Fin15AnchoredAtom3559
    Fin15AnchoredAtom3560 Fin15AnchoredAtom3567 Fin15AnchoredAtom3570 Fin15AnchoredAtom3571
    Fin15AnchoredAtom3574 Fin15AnchoredAtom3575 Fin15AnchoredAtom3581 Fin15AnchoredAtom3652
    Fin15AnchoredAtom3655 Fin15AnchoredAtom3656 Fin15AnchoredAtom3659 Fin15AnchoredAtom3660
    Fin15AnchoredAtom3666 Fin15AnchoredAtom3684 Fin15AnchoredAtom3685 Fin15AnchoredAtom3691
    Fin15AnchoredAtom3697 Fin15AnchoredAtom3772 Fin15AnchoredAtom3775 Fin15AnchoredAtom3776
    Fin15AnchoredAtom3779 Fin15AnchoredAtom3780 Fin15AnchoredAtom3786 Fin15AnchoredAtom3804
    Fin15AnchoredAtom3805 Fin15AnchoredAtom3811 Fin15AnchoredAtom3817 Fin15AnchoredAtom3979
    Fin15AnchoredAtom3980 Fin15AnchoredAtom3986 Fin15AnchoredAtom3992 Fin15AnchoredAtom4022
    Fin15AnchoredAtom4102 Fin15AnchoredAtom4105 Fin15AnchoredAtom4106 Fin15AnchoredAtom4109
    Fin15AnchoredAtom4110 Fin15AnchoredAtom4116 Fin15AnchoredAtom4134 Fin15AnchoredAtom4135
    Fin15AnchoredAtom4141 Fin15AnchoredAtom4147 Fin15AnchoredAtom4309 Fin15AnchoredAtom4310
    Fin15AnchoredAtom4316 Fin15AnchoredAtom4322 Fin15AnchoredAtom4352 Fin15AnchoredAtom4519
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

theorem fin15Anchored_clause32051 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3555 chi ∧
      ¬Fin15AnchoredAtom3558 chi ∧
      ¬Fin15AnchoredAtom3559 chi ∧
      ¬Fin15AnchoredAtom3560 chi ∧
      ¬Fin15AnchoredAtom3569 chi ∧
      ¬Fin15AnchoredAtom3570 chi ∧
      ¬Fin15AnchoredAtom3571 chi ∧
      ¬Fin15AnchoredAtom3579 chi ∧
      ¬Fin15AnchoredAtom3580 chi ∧
      ¬Fin15AnchoredAtom3581 chi ∧
      ¬Fin15AnchoredAtom3654 chi ∧
      ¬Fin15AnchoredAtom3655 chi ∧
      ¬Fin15AnchoredAtom3656 chi ∧
      ¬Fin15AnchoredAtom3664 chi ∧
      ¬Fin15AnchoredAtom3665 chi ∧
      ¬Fin15AnchoredAtom3666 chi ∧
      ¬Fin15AnchoredAtom3689 chi ∧
      ¬Fin15AnchoredAtom3690 chi ∧
      ¬Fin15AnchoredAtom3691 chi ∧
      ¬Fin15AnchoredAtom3701 chi ∧
      ¬Fin15AnchoredAtom3774 chi ∧
      ¬Fin15AnchoredAtom3775 chi ∧
      ¬Fin15AnchoredAtom3776 chi ∧
      ¬Fin15AnchoredAtom3784 chi ∧
      ¬Fin15AnchoredAtom3785 chi ∧
      ¬Fin15AnchoredAtom3786 chi ∧
      ¬Fin15AnchoredAtom3809 chi ∧
      ¬Fin15AnchoredAtom3810 chi ∧
      ¬Fin15AnchoredAtom3811 chi ∧
      ¬Fin15AnchoredAtom3821 chi ∧
      ¬Fin15AnchoredAtom3984 chi ∧
      ¬Fin15AnchoredAtom3985 chi ∧
      ¬Fin15AnchoredAtom3986 chi ∧
      ¬Fin15AnchoredAtom3996 chi ∧
      ¬Fin15AnchoredAtom4026 chi ∧
      ¬Fin15AnchoredAtom4104 chi ∧
      ¬Fin15AnchoredAtom4105 chi ∧
      ¬Fin15AnchoredAtom4106 chi ∧
      ¬Fin15AnchoredAtom4114 chi ∧
      ¬Fin15AnchoredAtom4115 chi ∧
      ¬Fin15AnchoredAtom4116 chi ∧
      ¬Fin15AnchoredAtom4139 chi ∧
      ¬Fin15AnchoredAtom4140 chi ∧
      ¬Fin15AnchoredAtom4141 chi ∧
      ¬Fin15AnchoredAtom4151 chi ∧
      ¬Fin15AnchoredAtom4314 chi ∧
      ¬Fin15AnchoredAtom4315 chi ∧
      ¬Fin15AnchoredAtom4316 chi ∧
      ¬Fin15AnchoredAtom4326 chi ∧
      ¬Fin15AnchoredAtom4356 chi ∧
      ¬Fin15AnchoredAtom4524 chi ∧
      ¬Fin15AnchoredAtom4525 chi ∧
      ¬Fin15AnchoredAtom4526 chi ∧
      ¬Fin15AnchoredAtom4536 chi ∧
      ¬Fin15AnchoredAtom4566 chi ∧
      ¬Fin15AnchoredAtom4797 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 7, 9, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29340
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3555 Fin15AnchoredAtom3558 Fin15AnchoredAtom3559
    Fin15AnchoredAtom3560 Fin15AnchoredAtom3569 Fin15AnchoredAtom3570 Fin15AnchoredAtom3571
    Fin15AnchoredAtom3579 Fin15AnchoredAtom3580 Fin15AnchoredAtom3581 Fin15AnchoredAtom3654
    Fin15AnchoredAtom3655 Fin15AnchoredAtom3656 Fin15AnchoredAtom3664 Fin15AnchoredAtom3665
    Fin15AnchoredAtom3666 Fin15AnchoredAtom3689 Fin15AnchoredAtom3690 Fin15AnchoredAtom3691
    Fin15AnchoredAtom3701 Fin15AnchoredAtom3774 Fin15AnchoredAtom3775 Fin15AnchoredAtom3776
    Fin15AnchoredAtom3784 Fin15AnchoredAtom3785 Fin15AnchoredAtom3786 Fin15AnchoredAtom3809
    Fin15AnchoredAtom3810 Fin15AnchoredAtom3811 Fin15AnchoredAtom3821 Fin15AnchoredAtom3984
    Fin15AnchoredAtom3985 Fin15AnchoredAtom3986 Fin15AnchoredAtom3996 Fin15AnchoredAtom4026
    Fin15AnchoredAtom4104 Fin15AnchoredAtom4105 Fin15AnchoredAtom4106 Fin15AnchoredAtom4114
    Fin15AnchoredAtom4115 Fin15AnchoredAtom4116 Fin15AnchoredAtom4139 Fin15AnchoredAtom4140
    Fin15AnchoredAtom4141 Fin15AnchoredAtom4151 Fin15AnchoredAtom4314 Fin15AnchoredAtom4315
    Fin15AnchoredAtom4316 Fin15AnchoredAtom4326 Fin15AnchoredAtom4356 Fin15AnchoredAtom4524
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

theorem fin15Anchored_clause32052 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3556 chi ∧
      ¬Fin15AnchoredAtom3558 chi ∧
      ¬Fin15AnchoredAtom3559 chi ∧
      ¬Fin15AnchoredAtom3560 chi ∧
      ¬Fin15AnchoredAtom3573 chi ∧
      ¬Fin15AnchoredAtom3574 chi ∧
      ¬Fin15AnchoredAtom3575 chi ∧
      ¬Fin15AnchoredAtom3579 chi ∧
      ¬Fin15AnchoredAtom3580 chi ∧
      ¬Fin15AnchoredAtom3581 chi ∧
      ¬Fin15AnchoredAtom3658 chi ∧
      ¬Fin15AnchoredAtom3659 chi ∧
      ¬Fin15AnchoredAtom3660 chi ∧
      ¬Fin15AnchoredAtom3664 chi ∧
      ¬Fin15AnchoredAtom3665 chi ∧
      ¬Fin15AnchoredAtom3666 chi ∧
      ¬Fin15AnchoredAtom3695 chi ∧
      ¬Fin15AnchoredAtom3696 chi ∧
      ¬Fin15AnchoredAtom3697 chi ∧
      ¬Fin15AnchoredAtom3701 chi ∧
      ¬Fin15AnchoredAtom3778 chi ∧
      ¬Fin15AnchoredAtom3779 chi ∧
      ¬Fin15AnchoredAtom3780 chi ∧
      ¬Fin15AnchoredAtom3784 chi ∧
      ¬Fin15AnchoredAtom3785 chi ∧
      ¬Fin15AnchoredAtom3786 chi ∧
      ¬Fin15AnchoredAtom3815 chi ∧
      ¬Fin15AnchoredAtom3816 chi ∧
      ¬Fin15AnchoredAtom3817 chi ∧
      ¬Fin15AnchoredAtom3821 chi ∧
      ¬Fin15AnchoredAtom3990 chi ∧
      ¬Fin15AnchoredAtom3991 chi ∧
      ¬Fin15AnchoredAtom3992 chi ∧
      ¬Fin15AnchoredAtom3996 chi ∧
      ¬Fin15AnchoredAtom4030 chi ∧
      ¬Fin15AnchoredAtom4108 chi ∧
      ¬Fin15AnchoredAtom4109 chi ∧
      ¬Fin15AnchoredAtom4110 chi ∧
      ¬Fin15AnchoredAtom4114 chi ∧
      ¬Fin15AnchoredAtom4115 chi ∧
      ¬Fin15AnchoredAtom4116 chi ∧
      ¬Fin15AnchoredAtom4145 chi ∧
      ¬Fin15AnchoredAtom4146 chi ∧
      ¬Fin15AnchoredAtom4147 chi ∧
      ¬Fin15AnchoredAtom4151 chi ∧
      ¬Fin15AnchoredAtom4320 chi ∧
      ¬Fin15AnchoredAtom4321 chi ∧
      ¬Fin15AnchoredAtom4322 chi ∧
      ¬Fin15AnchoredAtom4326 chi ∧
      ¬Fin15AnchoredAtom4360 chi ∧
      ¬Fin15AnchoredAtom4530 chi ∧
      ¬Fin15AnchoredAtom4531 chi ∧
      ¬Fin15AnchoredAtom4532 chi ∧
      ¬Fin15AnchoredAtom4536 chi ∧
      ¬Fin15AnchoredAtom4570 chi ∧
      ¬Fin15AnchoredAtom4801 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 7, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29852
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3556 Fin15AnchoredAtom3558 Fin15AnchoredAtom3559
    Fin15AnchoredAtom3560 Fin15AnchoredAtom3573 Fin15AnchoredAtom3574 Fin15AnchoredAtom3575
    Fin15AnchoredAtom3579 Fin15AnchoredAtom3580 Fin15AnchoredAtom3581 Fin15AnchoredAtom3658
    Fin15AnchoredAtom3659 Fin15AnchoredAtom3660 Fin15AnchoredAtom3664 Fin15AnchoredAtom3665
    Fin15AnchoredAtom3666 Fin15AnchoredAtom3695 Fin15AnchoredAtom3696 Fin15AnchoredAtom3697
    Fin15AnchoredAtom3701 Fin15AnchoredAtom3778 Fin15AnchoredAtom3779 Fin15AnchoredAtom3780
    Fin15AnchoredAtom3784 Fin15AnchoredAtom3785 Fin15AnchoredAtom3786 Fin15AnchoredAtom3815
    Fin15AnchoredAtom3816 Fin15AnchoredAtom3817 Fin15AnchoredAtom3821 Fin15AnchoredAtom3990
    Fin15AnchoredAtom3991 Fin15AnchoredAtom3992 Fin15AnchoredAtom3996 Fin15AnchoredAtom4030
    Fin15AnchoredAtom4108 Fin15AnchoredAtom4109 Fin15AnchoredAtom4110 Fin15AnchoredAtom4114
    Fin15AnchoredAtom4115 Fin15AnchoredAtom4116 Fin15AnchoredAtom4145 Fin15AnchoredAtom4146
    Fin15AnchoredAtom4147 Fin15AnchoredAtom4151 Fin15AnchoredAtom4320 Fin15AnchoredAtom4321
    Fin15AnchoredAtom4322 Fin15AnchoredAtom4326 Fin15AnchoredAtom4360 Fin15AnchoredAtom4530
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

theorem fin15Anchored_clause32053 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3567 chi ∧
      ¬Fin15AnchoredAtom3569 chi ∧
      ¬Fin15AnchoredAtom3570 chi ∧
      ¬Fin15AnchoredAtom3571 chi ∧
      ¬Fin15AnchoredAtom3573 chi ∧
      ¬Fin15AnchoredAtom3574 chi ∧
      ¬Fin15AnchoredAtom3575 chi ∧
      ¬Fin15AnchoredAtom3579 chi ∧
      ¬Fin15AnchoredAtom3580 chi ∧
      ¬Fin15AnchoredAtom3581 chi ∧
      ¬Fin15AnchoredAtom3683 chi ∧
      ¬Fin15AnchoredAtom3684 chi ∧
      ¬Fin15AnchoredAtom3685 chi ∧
      ¬Fin15AnchoredAtom3689 chi ∧
      ¬Fin15AnchoredAtom3690 chi ∧
      ¬Fin15AnchoredAtom3691 chi ∧
      ¬Fin15AnchoredAtom3695 chi ∧
      ¬Fin15AnchoredAtom3696 chi ∧
      ¬Fin15AnchoredAtom3697 chi ∧
      ¬Fin15AnchoredAtom3701 chi ∧
      ¬Fin15AnchoredAtom3803 chi ∧
      ¬Fin15AnchoredAtom3804 chi ∧
      ¬Fin15AnchoredAtom3805 chi ∧
      ¬Fin15AnchoredAtom3809 chi ∧
      ¬Fin15AnchoredAtom3810 chi ∧
      ¬Fin15AnchoredAtom3811 chi ∧
      ¬Fin15AnchoredAtom3815 chi ∧
      ¬Fin15AnchoredAtom3816 chi ∧
      ¬Fin15AnchoredAtom3817 chi ∧
      ¬Fin15AnchoredAtom3821 chi ∧
      ¬Fin15AnchoredAtom4020 chi ∧
      ¬Fin15AnchoredAtom4021 chi ∧
      ¬Fin15AnchoredAtom4022 chi ∧
      ¬Fin15AnchoredAtom4026 chi ∧
      ¬Fin15AnchoredAtom4030 chi ∧
      ¬Fin15AnchoredAtom4133 chi ∧
      ¬Fin15AnchoredAtom4134 chi ∧
      ¬Fin15AnchoredAtom4135 chi ∧
      ¬Fin15AnchoredAtom4139 chi ∧
      ¬Fin15AnchoredAtom4140 chi ∧
      ¬Fin15AnchoredAtom4141 chi ∧
      ¬Fin15AnchoredAtom4145 chi ∧
      ¬Fin15AnchoredAtom4146 chi ∧
      ¬Fin15AnchoredAtom4147 chi ∧
      ¬Fin15AnchoredAtom4151 chi ∧
      ¬Fin15AnchoredAtom4350 chi ∧
      ¬Fin15AnchoredAtom4351 chi ∧
      ¬Fin15AnchoredAtom4352 chi ∧
      ¬Fin15AnchoredAtom4356 chi ∧
      ¬Fin15AnchoredAtom4360 chi ∧
      ¬Fin15AnchoredAtom4560 chi ∧
      ¬Fin15AnchoredAtom4561 chi ∧
      ¬Fin15AnchoredAtom4562 chi ∧
      ¬Fin15AnchoredAtom4566 chi ∧
      ¬Fin15AnchoredAtom4570 chi ∧
      ¬Fin15AnchoredAtom4821 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 9, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask30236
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3567 Fin15AnchoredAtom3569 Fin15AnchoredAtom3570
    Fin15AnchoredAtom3571 Fin15AnchoredAtom3573 Fin15AnchoredAtom3574 Fin15AnchoredAtom3575
    Fin15AnchoredAtom3579 Fin15AnchoredAtom3580 Fin15AnchoredAtom3581 Fin15AnchoredAtom3683
    Fin15AnchoredAtom3684 Fin15AnchoredAtom3685 Fin15AnchoredAtom3689 Fin15AnchoredAtom3690
    Fin15AnchoredAtom3691 Fin15AnchoredAtom3695 Fin15AnchoredAtom3696 Fin15AnchoredAtom3697
    Fin15AnchoredAtom3701 Fin15AnchoredAtom3803 Fin15AnchoredAtom3804 Fin15AnchoredAtom3805
    Fin15AnchoredAtom3809 Fin15AnchoredAtom3810 Fin15AnchoredAtom3811 Fin15AnchoredAtom3815
    Fin15AnchoredAtom3816 Fin15AnchoredAtom3817 Fin15AnchoredAtom3821 Fin15AnchoredAtom4020
    Fin15AnchoredAtom4021 Fin15AnchoredAtom4022 Fin15AnchoredAtom4026 Fin15AnchoredAtom4030
    Fin15AnchoredAtom4133 Fin15AnchoredAtom4134 Fin15AnchoredAtom4135 Fin15AnchoredAtom4139
    Fin15AnchoredAtom4140 Fin15AnchoredAtom4141 Fin15AnchoredAtom4145 Fin15AnchoredAtom4146
    Fin15AnchoredAtom4147 Fin15AnchoredAtom4151 Fin15AnchoredAtom4350 Fin15AnchoredAtom4351
    Fin15AnchoredAtom4352 Fin15AnchoredAtom4356 Fin15AnchoredAtom4360 Fin15AnchoredAtom4560
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

theorem fin15Anchored_clause32054 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3582 chi ∧
      ¬Fin15AnchoredAtom3584 chi ∧
      ¬Fin15AnchoredAtom3585 chi ∧
      ¬Fin15AnchoredAtom3587 chi ∧
      ¬Fin15AnchoredAtom3591 chi ∧
      ¬Fin15AnchoredAtom3592 chi ∧
      ¬Fin15AnchoredAtom3594 chi ∧
      ¬Fin15AnchoredAtom3603 chi ∧
      ¬Fin15AnchoredAtom3605 chi ∧
      ¬Fin15AnchoredAtom3609 chi ∧
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
      ¬Fin15AnchoredAtom3823 chi ∧
      ¬Fin15AnchoredAtom3824 chi ∧
      ¬Fin15AnchoredAtom3826 chi ∧
      ¬Fin15AnchoredAtom3835 chi ∧
      ¬Fin15AnchoredAtom3837 chi ∧
      ¬Fin15AnchoredAtom3841 chi ∧
      ¬Fin15AnchoredAtom3856 chi ∧
      ¬Fin15AnchoredAtom3858 chi ∧
      ¬Fin15AnchoredAtom3862 chi ∧
      ¬Fin15AnchoredAtom3887 chi ∧
      ¬Fin15AnchoredAtom3912 chi ∧
      ¬Fin15AnchoredAtom3914 chi ∧
      ¬Fin15AnchoredAtom3918 chi ∧
      ¬Fin15AnchoredAtom3943 chi ∧
      ¬Fin15AnchoredAtom3978 chi ∧
      ¬Fin15AnchoredAtom4153 chi ∧
      ¬Fin15AnchoredAtom4154 chi ∧
      ¬Fin15AnchoredAtom4156 chi ∧
      ¬Fin15AnchoredAtom4165 chi ∧
      ¬Fin15AnchoredAtom4167 chi ∧
      ¬Fin15AnchoredAtom4171 chi ∧
      ¬Fin15AnchoredAtom4186 chi ∧
      ¬Fin15AnchoredAtom4188 chi ∧
      ¬Fin15AnchoredAtom4192 chi ∧
      ¬Fin15AnchoredAtom4217 chi ∧
      ¬Fin15AnchoredAtom4242 chi ∧
      ¬Fin15AnchoredAtom4244 chi ∧
      ¬Fin15AnchoredAtom4248 chi ∧
      ¬Fin15AnchoredAtom4273 chi ∧
      ¬Fin15AnchoredAtom4308 chi ∧
      ¬Fin15AnchoredAtom4578 chi ∧
      ¬Fin15AnchoredAtom4580 chi ∧
      ¬Fin15AnchoredAtom4584 chi ∧
      ¬Fin15AnchoredAtom4609 chi ∧
      ¬Fin15AnchoredAtom4644 chi ∧
      ¬Fin15AnchoredAtom4714 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 5, 6, 7, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05868
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3582 Fin15AnchoredAtom3584 Fin15AnchoredAtom3585
    Fin15AnchoredAtom3587 Fin15AnchoredAtom3591 Fin15AnchoredAtom3592 Fin15AnchoredAtom3594
    Fin15AnchoredAtom3603 Fin15AnchoredAtom3605 Fin15AnchoredAtom3609 Fin15AnchoredAtom3619
    Fin15AnchoredAtom3620 Fin15AnchoredAtom3622 Fin15AnchoredAtom3631 Fin15AnchoredAtom3633
    Fin15AnchoredAtom3637 Fin15AnchoredAtom3652 Fin15AnchoredAtom3654 Fin15AnchoredAtom3658
    Fin15AnchoredAtom3683 Fin15AnchoredAtom3823 Fin15AnchoredAtom3824 Fin15AnchoredAtom3826
    Fin15AnchoredAtom3835 Fin15AnchoredAtom3837 Fin15AnchoredAtom3841 Fin15AnchoredAtom3856
    Fin15AnchoredAtom3858 Fin15AnchoredAtom3862 Fin15AnchoredAtom3887 Fin15AnchoredAtom3912
    Fin15AnchoredAtom3914 Fin15AnchoredAtom3918 Fin15AnchoredAtom3943 Fin15AnchoredAtom3978
    Fin15AnchoredAtom4153 Fin15AnchoredAtom4154 Fin15AnchoredAtom4156 Fin15AnchoredAtom4165
    Fin15AnchoredAtom4167 Fin15AnchoredAtom4171 Fin15AnchoredAtom4186 Fin15AnchoredAtom4188
    Fin15AnchoredAtom4192 Fin15AnchoredAtom4217 Fin15AnchoredAtom4242 Fin15AnchoredAtom4244
    Fin15AnchoredAtom4248 Fin15AnchoredAtom4273 Fin15AnchoredAtom4308 Fin15AnchoredAtom4578
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

theorem fin15Anchored_clause32055 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3582 chi ∧
      ¬Fin15AnchoredAtom3584 chi ∧
      ¬Fin15AnchoredAtom3585 chi ∧
      ¬Fin15AnchoredAtom3588 chi ∧
      ¬Fin15AnchoredAtom3591 chi ∧
      ¬Fin15AnchoredAtom3592 chi ∧
      ¬Fin15AnchoredAtom3595 chi ∧
      ¬Fin15AnchoredAtom3603 chi ∧
      ¬Fin15AnchoredAtom3606 chi ∧
      ¬Fin15AnchoredAtom3610 chi ∧
      ¬Fin15AnchoredAtom3619 chi ∧
      ¬Fin15AnchoredAtom3620 chi ∧
      ¬Fin15AnchoredAtom3623 chi ∧
      ¬Fin15AnchoredAtom3631 chi ∧
      ¬Fin15AnchoredAtom3634 chi ∧
      ¬Fin15AnchoredAtom3638 chi ∧
      ¬Fin15AnchoredAtom3652 chi ∧
      ¬Fin15AnchoredAtom3655 chi ∧
      ¬Fin15AnchoredAtom3659 chi ∧
      ¬Fin15AnchoredAtom3684 chi ∧
      ¬Fin15AnchoredAtom3823 chi ∧
      ¬Fin15AnchoredAtom3824 chi ∧
      ¬Fin15AnchoredAtom3827 chi ∧
      ¬Fin15AnchoredAtom3835 chi ∧
      ¬Fin15AnchoredAtom3838 chi ∧
      ¬Fin15AnchoredAtom3842 chi ∧
      ¬Fin15AnchoredAtom3856 chi ∧
      ¬Fin15AnchoredAtom3859 chi ∧
      ¬Fin15AnchoredAtom3863 chi ∧
      ¬Fin15AnchoredAtom3888 chi ∧
      ¬Fin15AnchoredAtom3912 chi ∧
      ¬Fin15AnchoredAtom3915 chi ∧
      ¬Fin15AnchoredAtom3919 chi ∧
      ¬Fin15AnchoredAtom3944 chi ∧
      ¬Fin15AnchoredAtom3979 chi ∧
      ¬Fin15AnchoredAtom4153 chi ∧
      ¬Fin15AnchoredAtom4154 chi ∧
      ¬Fin15AnchoredAtom4157 chi ∧
      ¬Fin15AnchoredAtom4165 chi ∧
      ¬Fin15AnchoredAtom4168 chi ∧
      ¬Fin15AnchoredAtom4172 chi ∧
      ¬Fin15AnchoredAtom4186 chi ∧
      ¬Fin15AnchoredAtom4189 chi ∧
      ¬Fin15AnchoredAtom4193 chi ∧
      ¬Fin15AnchoredAtom4218 chi ∧
      ¬Fin15AnchoredAtom4242 chi ∧
      ¬Fin15AnchoredAtom4245 chi ∧
      ¬Fin15AnchoredAtom4249 chi ∧
      ¬Fin15AnchoredAtom4274 chi ∧
      ¬Fin15AnchoredAtom4309 chi ∧
      ¬Fin15AnchoredAtom4578 chi ∧
      ¬Fin15AnchoredAtom4581 chi ∧
      ¬Fin15AnchoredAtom4585 chi ∧
      ¬Fin15AnchoredAtom4610 chi ∧
      ¬Fin15AnchoredAtom4645 chi ∧
      ¬Fin15AnchoredAtom4715 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 5, 6, 7, 9, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09964
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3582 Fin15AnchoredAtom3584 Fin15AnchoredAtom3585
    Fin15AnchoredAtom3588 Fin15AnchoredAtom3591 Fin15AnchoredAtom3592 Fin15AnchoredAtom3595
    Fin15AnchoredAtom3603 Fin15AnchoredAtom3606 Fin15AnchoredAtom3610 Fin15AnchoredAtom3619
    Fin15AnchoredAtom3620 Fin15AnchoredAtom3623 Fin15AnchoredAtom3631 Fin15AnchoredAtom3634
    Fin15AnchoredAtom3638 Fin15AnchoredAtom3652 Fin15AnchoredAtom3655 Fin15AnchoredAtom3659
    Fin15AnchoredAtom3684 Fin15AnchoredAtom3823 Fin15AnchoredAtom3824 Fin15AnchoredAtom3827
    Fin15AnchoredAtom3835 Fin15AnchoredAtom3838 Fin15AnchoredAtom3842 Fin15AnchoredAtom3856
    Fin15AnchoredAtom3859 Fin15AnchoredAtom3863 Fin15AnchoredAtom3888 Fin15AnchoredAtom3912
    Fin15AnchoredAtom3915 Fin15AnchoredAtom3919 Fin15AnchoredAtom3944 Fin15AnchoredAtom3979
    Fin15AnchoredAtom4153 Fin15AnchoredAtom4154 Fin15AnchoredAtom4157 Fin15AnchoredAtom4165
    Fin15AnchoredAtom4168 Fin15AnchoredAtom4172 Fin15AnchoredAtom4186 Fin15AnchoredAtom4189
    Fin15AnchoredAtom4193 Fin15AnchoredAtom4218 Fin15AnchoredAtom4242 Fin15AnchoredAtom4245
    Fin15AnchoredAtom4249 Fin15AnchoredAtom4274 Fin15AnchoredAtom4309 Fin15AnchoredAtom4578
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

theorem fin15Anchored_clause32056 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3582 chi ∧
      ¬Fin15AnchoredAtom3584 chi ∧
      ¬Fin15AnchoredAtom3585 chi ∧
      ¬Fin15AnchoredAtom3589 chi ∧
      ¬Fin15AnchoredAtom3591 chi ∧
      ¬Fin15AnchoredAtom3592 chi ∧
      ¬Fin15AnchoredAtom3596 chi ∧
      ¬Fin15AnchoredAtom3603 chi ∧
      ¬Fin15AnchoredAtom3607 chi ∧
      ¬Fin15AnchoredAtom3611 chi ∧
      ¬Fin15AnchoredAtom3619 chi ∧
      ¬Fin15AnchoredAtom3620 chi ∧
      ¬Fin15AnchoredAtom3624 chi ∧
      ¬Fin15AnchoredAtom3631 chi ∧
      ¬Fin15AnchoredAtom3635 chi ∧
      ¬Fin15AnchoredAtom3639 chi ∧
      ¬Fin15AnchoredAtom3652 chi ∧
      ¬Fin15AnchoredAtom3656 chi ∧
      ¬Fin15AnchoredAtom3660 chi ∧
      ¬Fin15AnchoredAtom3685 chi ∧
      ¬Fin15AnchoredAtom3823 chi ∧
      ¬Fin15AnchoredAtom3824 chi ∧
      ¬Fin15AnchoredAtom3828 chi ∧
      ¬Fin15AnchoredAtom3835 chi ∧
      ¬Fin15AnchoredAtom3839 chi ∧
      ¬Fin15AnchoredAtom3843 chi ∧
      ¬Fin15AnchoredAtom3856 chi ∧
      ¬Fin15AnchoredAtom3860 chi ∧
      ¬Fin15AnchoredAtom3864 chi ∧
      ¬Fin15AnchoredAtom3889 chi ∧
      ¬Fin15AnchoredAtom3912 chi ∧
      ¬Fin15AnchoredAtom3916 chi ∧
      ¬Fin15AnchoredAtom3920 chi ∧
      ¬Fin15AnchoredAtom3945 chi ∧
      ¬Fin15AnchoredAtom3980 chi ∧
      ¬Fin15AnchoredAtom4153 chi ∧
      ¬Fin15AnchoredAtom4154 chi ∧
      ¬Fin15AnchoredAtom4158 chi ∧
      ¬Fin15AnchoredAtom4165 chi ∧
      ¬Fin15AnchoredAtom4169 chi ∧
      ¬Fin15AnchoredAtom4173 chi ∧
      ¬Fin15AnchoredAtom4186 chi ∧
      ¬Fin15AnchoredAtom4190 chi ∧
      ¬Fin15AnchoredAtom4194 chi ∧
      ¬Fin15AnchoredAtom4219 chi ∧
      ¬Fin15AnchoredAtom4242 chi ∧
      ¬Fin15AnchoredAtom4246 chi ∧
      ¬Fin15AnchoredAtom4250 chi ∧
      ¬Fin15AnchoredAtom4275 chi ∧
      ¬Fin15AnchoredAtom4310 chi ∧
      ¬Fin15AnchoredAtom4578 chi ∧
      ¬Fin15AnchoredAtom4582 chi ∧
      ¬Fin15AnchoredAtom4586 chi ∧
      ¬Fin15AnchoredAtom4611 chi ∧
      ¬Fin15AnchoredAtom4646 chi ∧
      ¬Fin15AnchoredAtom4716 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 5, 6, 7, 9, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask18156
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3582 Fin15AnchoredAtom3584 Fin15AnchoredAtom3585
    Fin15AnchoredAtom3589 Fin15AnchoredAtom3591 Fin15AnchoredAtom3592 Fin15AnchoredAtom3596
    Fin15AnchoredAtom3603 Fin15AnchoredAtom3607 Fin15AnchoredAtom3611 Fin15AnchoredAtom3619
    Fin15AnchoredAtom3620 Fin15AnchoredAtom3624 Fin15AnchoredAtom3631 Fin15AnchoredAtom3635
    Fin15AnchoredAtom3639 Fin15AnchoredAtom3652 Fin15AnchoredAtom3656 Fin15AnchoredAtom3660
    Fin15AnchoredAtom3685 Fin15AnchoredAtom3823 Fin15AnchoredAtom3824 Fin15AnchoredAtom3828
    Fin15AnchoredAtom3835 Fin15AnchoredAtom3839 Fin15AnchoredAtom3843 Fin15AnchoredAtom3856
    Fin15AnchoredAtom3860 Fin15AnchoredAtom3864 Fin15AnchoredAtom3889 Fin15AnchoredAtom3912
    Fin15AnchoredAtom3916 Fin15AnchoredAtom3920 Fin15AnchoredAtom3945 Fin15AnchoredAtom3980
    Fin15AnchoredAtom4153 Fin15AnchoredAtom4154 Fin15AnchoredAtom4158 Fin15AnchoredAtom4165
    Fin15AnchoredAtom4169 Fin15AnchoredAtom4173 Fin15AnchoredAtom4186 Fin15AnchoredAtom4190
    Fin15AnchoredAtom4194 Fin15AnchoredAtom4219 Fin15AnchoredAtom4242 Fin15AnchoredAtom4246
    Fin15AnchoredAtom4250 Fin15AnchoredAtom4275 Fin15AnchoredAtom4310 Fin15AnchoredAtom4578
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

theorem fin15Anchored_clause32057 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3582 chi ∧
      ¬Fin15AnchoredAtom3584 chi ∧
      ¬Fin15AnchoredAtom3587 chi ∧
      ¬Fin15AnchoredAtom3588 chi ∧
      ¬Fin15AnchoredAtom3591 chi ∧
      ¬Fin15AnchoredAtom3594 chi ∧
      ¬Fin15AnchoredAtom3595 chi ∧
      ¬Fin15AnchoredAtom3605 chi ∧
      ¬Fin15AnchoredAtom3606 chi ∧
      ¬Fin15AnchoredAtom3615 chi ∧
      ¬Fin15AnchoredAtom3619 chi ∧
      ¬Fin15AnchoredAtom3622 chi ∧
      ¬Fin15AnchoredAtom3623 chi ∧
      ¬Fin15AnchoredAtom3633 chi ∧
      ¬Fin15AnchoredAtom3634 chi ∧
      ¬Fin15AnchoredAtom3643 chi ∧
      ¬Fin15AnchoredAtom3654 chi ∧
      ¬Fin15AnchoredAtom3655 chi ∧
      ¬Fin15AnchoredAtom3664 chi ∧
      ¬Fin15AnchoredAtom3689 chi ∧
      ¬Fin15AnchoredAtom3823 chi ∧
      ¬Fin15AnchoredAtom3826 chi ∧
      ¬Fin15AnchoredAtom3827 chi ∧
      ¬Fin15AnchoredAtom3837 chi ∧
      ¬Fin15AnchoredAtom3838 chi ∧
      ¬Fin15AnchoredAtom3847 chi ∧
      ¬Fin15AnchoredAtom3858 chi ∧
      ¬Fin15AnchoredAtom3859 chi ∧
      ¬Fin15AnchoredAtom3868 chi ∧
      ¬Fin15AnchoredAtom3893 chi ∧
      ¬Fin15AnchoredAtom3914 chi ∧
      ¬Fin15AnchoredAtom3915 chi ∧
      ¬Fin15AnchoredAtom3924 chi ∧
      ¬Fin15AnchoredAtom3949 chi ∧
      ¬Fin15AnchoredAtom3984 chi ∧
      ¬Fin15AnchoredAtom4153 chi ∧
      ¬Fin15AnchoredAtom4156 chi ∧
      ¬Fin15AnchoredAtom4157 chi ∧
      ¬Fin15AnchoredAtom4167 chi ∧
      ¬Fin15AnchoredAtom4168 chi ∧
      ¬Fin15AnchoredAtom4177 chi ∧
      ¬Fin15AnchoredAtom4188 chi ∧
      ¬Fin15AnchoredAtom4189 chi ∧
      ¬Fin15AnchoredAtom4198 chi ∧
      ¬Fin15AnchoredAtom4223 chi ∧
      ¬Fin15AnchoredAtom4244 chi ∧
      ¬Fin15AnchoredAtom4245 chi ∧
      ¬Fin15AnchoredAtom4254 chi ∧
      ¬Fin15AnchoredAtom4279 chi ∧
      ¬Fin15AnchoredAtom4314 chi ∧
      ¬Fin15AnchoredAtom4580 chi ∧
      ¬Fin15AnchoredAtom4581 chi ∧
      ¬Fin15AnchoredAtom4590 chi ∧
      ¬Fin15AnchoredAtom4615 chi ∧
      ¬Fin15AnchoredAtom4650 chi ∧
      ¬Fin15AnchoredAtom4720 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 5, 6, 7, 9, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13036
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3582 Fin15AnchoredAtom3584 Fin15AnchoredAtom3587
    Fin15AnchoredAtom3588 Fin15AnchoredAtom3591 Fin15AnchoredAtom3594 Fin15AnchoredAtom3595
    Fin15AnchoredAtom3605 Fin15AnchoredAtom3606 Fin15AnchoredAtom3615 Fin15AnchoredAtom3619
    Fin15AnchoredAtom3622 Fin15AnchoredAtom3623 Fin15AnchoredAtom3633 Fin15AnchoredAtom3634
    Fin15AnchoredAtom3643 Fin15AnchoredAtom3654 Fin15AnchoredAtom3655 Fin15AnchoredAtom3664
    Fin15AnchoredAtom3689 Fin15AnchoredAtom3823 Fin15AnchoredAtom3826 Fin15AnchoredAtom3827
    Fin15AnchoredAtom3837 Fin15AnchoredAtom3838 Fin15AnchoredAtom3847 Fin15AnchoredAtom3858
    Fin15AnchoredAtom3859 Fin15AnchoredAtom3868 Fin15AnchoredAtom3893 Fin15AnchoredAtom3914
    Fin15AnchoredAtom3915 Fin15AnchoredAtom3924 Fin15AnchoredAtom3949 Fin15AnchoredAtom3984
    Fin15AnchoredAtom4153 Fin15AnchoredAtom4156 Fin15AnchoredAtom4157 Fin15AnchoredAtom4167
    Fin15AnchoredAtom4168 Fin15AnchoredAtom4177 Fin15AnchoredAtom4188 Fin15AnchoredAtom4189
    Fin15AnchoredAtom4198 Fin15AnchoredAtom4223 Fin15AnchoredAtom4244 Fin15AnchoredAtom4245
    Fin15AnchoredAtom4254 Fin15AnchoredAtom4279 Fin15AnchoredAtom4314 Fin15AnchoredAtom4580
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

theorem fin15Anchored_clause32058 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3582 chi ∧
      ¬Fin15AnchoredAtom3584 chi ∧
      ¬Fin15AnchoredAtom3587 chi ∧
      ¬Fin15AnchoredAtom3589 chi ∧
      ¬Fin15AnchoredAtom3591 chi ∧
      ¬Fin15AnchoredAtom3594 chi ∧
      ¬Fin15AnchoredAtom3596 chi ∧
      ¬Fin15AnchoredAtom3605 chi ∧
      ¬Fin15AnchoredAtom3607 chi ∧
      ¬Fin15AnchoredAtom3616 chi ∧
      ¬Fin15AnchoredAtom3619 chi ∧
      ¬Fin15AnchoredAtom3622 chi ∧
      ¬Fin15AnchoredAtom3624 chi ∧
      ¬Fin15AnchoredAtom3633 chi ∧
      ¬Fin15AnchoredAtom3635 chi ∧
      ¬Fin15AnchoredAtom3644 chi ∧
      ¬Fin15AnchoredAtom3654 chi ∧
      ¬Fin15AnchoredAtom3656 chi ∧
      ¬Fin15AnchoredAtom3665 chi ∧
      ¬Fin15AnchoredAtom3690 chi ∧
      ¬Fin15AnchoredAtom3823 chi ∧
      ¬Fin15AnchoredAtom3826 chi ∧
      ¬Fin15AnchoredAtom3828 chi ∧
      ¬Fin15AnchoredAtom3837 chi ∧
      ¬Fin15AnchoredAtom3839 chi ∧
      ¬Fin15AnchoredAtom3848 chi ∧
      ¬Fin15AnchoredAtom3858 chi ∧
      ¬Fin15AnchoredAtom3860 chi ∧
      ¬Fin15AnchoredAtom3869 chi ∧
      ¬Fin15AnchoredAtom3894 chi ∧
      ¬Fin15AnchoredAtom3914 chi ∧
      ¬Fin15AnchoredAtom3916 chi ∧
      ¬Fin15AnchoredAtom3925 chi ∧
      ¬Fin15AnchoredAtom3950 chi ∧
      ¬Fin15AnchoredAtom3985 chi ∧
      ¬Fin15AnchoredAtom4153 chi ∧
      ¬Fin15AnchoredAtom4156 chi ∧
      ¬Fin15AnchoredAtom4158 chi ∧
      ¬Fin15AnchoredAtom4167 chi ∧
      ¬Fin15AnchoredAtom4169 chi ∧
      ¬Fin15AnchoredAtom4178 chi ∧
      ¬Fin15AnchoredAtom4188 chi ∧
      ¬Fin15AnchoredAtom4190 chi ∧
      ¬Fin15AnchoredAtom4199 chi ∧
      ¬Fin15AnchoredAtom4224 chi ∧
      ¬Fin15AnchoredAtom4244 chi ∧
      ¬Fin15AnchoredAtom4246 chi ∧
      ¬Fin15AnchoredAtom4255 chi ∧
      ¬Fin15AnchoredAtom4280 chi ∧
      ¬Fin15AnchoredAtom4315 chi ∧
      ¬Fin15AnchoredAtom4580 chi ∧
      ¬Fin15AnchoredAtom4582 chi ∧
      ¬Fin15AnchoredAtom4591 chi ∧
      ¬Fin15AnchoredAtom4616 chi ∧
      ¬Fin15AnchoredAtom4651 chi ∧
      ¬Fin15AnchoredAtom4721 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 5, 6, 7, 9, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21228
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3582 Fin15AnchoredAtom3584 Fin15AnchoredAtom3587
    Fin15AnchoredAtom3589 Fin15AnchoredAtom3591 Fin15AnchoredAtom3594 Fin15AnchoredAtom3596
    Fin15AnchoredAtom3605 Fin15AnchoredAtom3607 Fin15AnchoredAtom3616 Fin15AnchoredAtom3619
    Fin15AnchoredAtom3622 Fin15AnchoredAtom3624 Fin15AnchoredAtom3633 Fin15AnchoredAtom3635
    Fin15AnchoredAtom3644 Fin15AnchoredAtom3654 Fin15AnchoredAtom3656 Fin15AnchoredAtom3665
    Fin15AnchoredAtom3690 Fin15AnchoredAtom3823 Fin15AnchoredAtom3826 Fin15AnchoredAtom3828
    Fin15AnchoredAtom3837 Fin15AnchoredAtom3839 Fin15AnchoredAtom3848 Fin15AnchoredAtom3858
    Fin15AnchoredAtom3860 Fin15AnchoredAtom3869 Fin15AnchoredAtom3894 Fin15AnchoredAtom3914
    Fin15AnchoredAtom3916 Fin15AnchoredAtom3925 Fin15AnchoredAtom3950 Fin15AnchoredAtom3985
    Fin15AnchoredAtom4153 Fin15AnchoredAtom4156 Fin15AnchoredAtom4158 Fin15AnchoredAtom4167
    Fin15AnchoredAtom4169 Fin15AnchoredAtom4178 Fin15AnchoredAtom4188 Fin15AnchoredAtom4190
    Fin15AnchoredAtom4199 Fin15AnchoredAtom4224 Fin15AnchoredAtom4244 Fin15AnchoredAtom4246
    Fin15AnchoredAtom4255 Fin15AnchoredAtom4280 Fin15AnchoredAtom4315 Fin15AnchoredAtom4580
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

theorem fin15Anchored_clause32059 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3582 chi ∧
      ¬Fin15AnchoredAtom3584 chi ∧
      ¬Fin15AnchoredAtom3588 chi ∧
      ¬Fin15AnchoredAtom3589 chi ∧
      ¬Fin15AnchoredAtom3591 chi ∧
      ¬Fin15AnchoredAtom3595 chi ∧
      ¬Fin15AnchoredAtom3596 chi ∧
      ¬Fin15AnchoredAtom3606 chi ∧
      ¬Fin15AnchoredAtom3607 chi ∧
      ¬Fin15AnchoredAtom3617 chi ∧
      ¬Fin15AnchoredAtom3619 chi ∧
      ¬Fin15AnchoredAtom3623 chi ∧
      ¬Fin15AnchoredAtom3624 chi ∧
      ¬Fin15AnchoredAtom3634 chi ∧
      ¬Fin15AnchoredAtom3635 chi ∧
      ¬Fin15AnchoredAtom3645 chi ∧
      ¬Fin15AnchoredAtom3655 chi ∧
      ¬Fin15AnchoredAtom3656 chi ∧
      ¬Fin15AnchoredAtom3666 chi ∧
      ¬Fin15AnchoredAtom3691 chi ∧
      ¬Fin15AnchoredAtom3823 chi ∧
      ¬Fin15AnchoredAtom3827 chi ∧
      ¬Fin15AnchoredAtom3828 chi ∧
      ¬Fin15AnchoredAtom3838 chi ∧
      ¬Fin15AnchoredAtom3839 chi ∧
      ¬Fin15AnchoredAtom3849 chi ∧
      ¬Fin15AnchoredAtom3859 chi ∧
      ¬Fin15AnchoredAtom3860 chi ∧
      ¬Fin15AnchoredAtom3870 chi ∧
      ¬Fin15AnchoredAtom3895 chi ∧
      ¬Fin15AnchoredAtom3915 chi ∧
      ¬Fin15AnchoredAtom3916 chi ∧
      ¬Fin15AnchoredAtom3926 chi ∧
      ¬Fin15AnchoredAtom3951 chi ∧
      ¬Fin15AnchoredAtom3986 chi ∧
      ¬Fin15AnchoredAtom4153 chi ∧
      ¬Fin15AnchoredAtom4157 chi ∧
      ¬Fin15AnchoredAtom4158 chi ∧
      ¬Fin15AnchoredAtom4168 chi ∧
      ¬Fin15AnchoredAtom4169 chi ∧
      ¬Fin15AnchoredAtom4179 chi ∧
      ¬Fin15AnchoredAtom4189 chi ∧
      ¬Fin15AnchoredAtom4190 chi ∧
      ¬Fin15AnchoredAtom4200 chi ∧
      ¬Fin15AnchoredAtom4225 chi ∧
      ¬Fin15AnchoredAtom4245 chi ∧
      ¬Fin15AnchoredAtom4246 chi ∧
      ¬Fin15AnchoredAtom4256 chi ∧
      ¬Fin15AnchoredAtom4281 chi ∧
      ¬Fin15AnchoredAtom4316 chi ∧
      ¬Fin15AnchoredAtom4581 chi ∧
      ¬Fin15AnchoredAtom4582 chi ∧
      ¬Fin15AnchoredAtom4592 chi ∧
      ¬Fin15AnchoredAtom4617 chi ∧
      ¬Fin15AnchoredAtom4652 chi ∧
      ¬Fin15AnchoredAtom4722 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 5, 6, 7, 9, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25324
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3582 Fin15AnchoredAtom3584 Fin15AnchoredAtom3588
    Fin15AnchoredAtom3589 Fin15AnchoredAtom3591 Fin15AnchoredAtom3595 Fin15AnchoredAtom3596
    Fin15AnchoredAtom3606 Fin15AnchoredAtom3607 Fin15AnchoredAtom3617 Fin15AnchoredAtom3619
    Fin15AnchoredAtom3623 Fin15AnchoredAtom3624 Fin15AnchoredAtom3634 Fin15AnchoredAtom3635
    Fin15AnchoredAtom3645 Fin15AnchoredAtom3655 Fin15AnchoredAtom3656 Fin15AnchoredAtom3666
    Fin15AnchoredAtom3691 Fin15AnchoredAtom3823 Fin15AnchoredAtom3827 Fin15AnchoredAtom3828
    Fin15AnchoredAtom3838 Fin15AnchoredAtom3839 Fin15AnchoredAtom3849 Fin15AnchoredAtom3859
    Fin15AnchoredAtom3860 Fin15AnchoredAtom3870 Fin15AnchoredAtom3895 Fin15AnchoredAtom3915
    Fin15AnchoredAtom3916 Fin15AnchoredAtom3926 Fin15AnchoredAtom3951 Fin15AnchoredAtom3986
    Fin15AnchoredAtom4153 Fin15AnchoredAtom4157 Fin15AnchoredAtom4158 Fin15AnchoredAtom4168
    Fin15AnchoredAtom4169 Fin15AnchoredAtom4179 Fin15AnchoredAtom4189 Fin15AnchoredAtom4190
    Fin15AnchoredAtom4200 Fin15AnchoredAtom4225 Fin15AnchoredAtom4245 Fin15AnchoredAtom4246
    Fin15AnchoredAtom4256 Fin15AnchoredAtom4281 Fin15AnchoredAtom4316 Fin15AnchoredAtom4581
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

theorem fin15Anchored_clause32060 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3582 chi ∧
      ¬Fin15AnchoredAtom3585 chi ∧
      ¬Fin15AnchoredAtom3587 chi ∧
      ¬Fin15AnchoredAtom3588 chi ∧
      ¬Fin15AnchoredAtom3592 chi ∧
      ¬Fin15AnchoredAtom3594 chi ∧
      ¬Fin15AnchoredAtom3595 chi ∧
      ¬Fin15AnchoredAtom3609 chi ∧
      ¬Fin15AnchoredAtom3610 chi ∧
      ¬Fin15AnchoredAtom3615 chi ∧
      ¬Fin15AnchoredAtom3620 chi ∧
      ¬Fin15AnchoredAtom3622 chi ∧
      ¬Fin15AnchoredAtom3623 chi ∧
      ¬Fin15AnchoredAtom3637 chi ∧
      ¬Fin15AnchoredAtom3638 chi ∧
      ¬Fin15AnchoredAtom3643 chi ∧
      ¬Fin15AnchoredAtom3658 chi ∧
      ¬Fin15AnchoredAtom3659 chi ∧
      ¬Fin15AnchoredAtom3664 chi ∧
      ¬Fin15AnchoredAtom3695 chi ∧
      ¬Fin15AnchoredAtom3824 chi ∧
      ¬Fin15AnchoredAtom3826 chi ∧
      ¬Fin15AnchoredAtom3827 chi ∧
      ¬Fin15AnchoredAtom3841 chi ∧
      ¬Fin15AnchoredAtom3842 chi ∧
      ¬Fin15AnchoredAtom3847 chi ∧
      ¬Fin15AnchoredAtom3862 chi ∧
      ¬Fin15AnchoredAtom3863 chi ∧
      ¬Fin15AnchoredAtom3868 chi ∧
      ¬Fin15AnchoredAtom3899 chi ∧
      ¬Fin15AnchoredAtom3918 chi ∧
      ¬Fin15AnchoredAtom3919 chi ∧
      ¬Fin15AnchoredAtom3924 chi ∧
      ¬Fin15AnchoredAtom3955 chi ∧
      ¬Fin15AnchoredAtom3990 chi ∧
      ¬Fin15AnchoredAtom4154 chi ∧
      ¬Fin15AnchoredAtom4156 chi ∧
      ¬Fin15AnchoredAtom4157 chi ∧
      ¬Fin15AnchoredAtom4171 chi ∧
      ¬Fin15AnchoredAtom4172 chi ∧
      ¬Fin15AnchoredAtom4177 chi ∧
      ¬Fin15AnchoredAtom4192 chi ∧
      ¬Fin15AnchoredAtom4193 chi ∧
      ¬Fin15AnchoredAtom4198 chi ∧
      ¬Fin15AnchoredAtom4229 chi ∧
      ¬Fin15AnchoredAtom4248 chi ∧
      ¬Fin15AnchoredAtom4249 chi ∧
      ¬Fin15AnchoredAtom4254 chi ∧
      ¬Fin15AnchoredAtom4285 chi ∧
      ¬Fin15AnchoredAtom4320 chi ∧
      ¬Fin15AnchoredAtom4584 chi ∧
      ¬Fin15AnchoredAtom4585 chi ∧
      ¬Fin15AnchoredAtom4590 chi ∧
      ¬Fin15AnchoredAtom4621 chi ∧
      ¬Fin15AnchoredAtom4656 chi ∧
      ¬Fin15AnchoredAtom4726 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 5, 6, 7, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13548
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3582 Fin15AnchoredAtom3585 Fin15AnchoredAtom3587
    Fin15AnchoredAtom3588 Fin15AnchoredAtom3592 Fin15AnchoredAtom3594 Fin15AnchoredAtom3595
    Fin15AnchoredAtom3609 Fin15AnchoredAtom3610 Fin15AnchoredAtom3615 Fin15AnchoredAtom3620
    Fin15AnchoredAtom3622 Fin15AnchoredAtom3623 Fin15AnchoredAtom3637 Fin15AnchoredAtom3638
    Fin15AnchoredAtom3643 Fin15AnchoredAtom3658 Fin15AnchoredAtom3659 Fin15AnchoredAtom3664
    Fin15AnchoredAtom3695 Fin15AnchoredAtom3824 Fin15AnchoredAtom3826 Fin15AnchoredAtom3827
    Fin15AnchoredAtom3841 Fin15AnchoredAtom3842 Fin15AnchoredAtom3847 Fin15AnchoredAtom3862
    Fin15AnchoredAtom3863 Fin15AnchoredAtom3868 Fin15AnchoredAtom3899 Fin15AnchoredAtom3918
    Fin15AnchoredAtom3919 Fin15AnchoredAtom3924 Fin15AnchoredAtom3955 Fin15AnchoredAtom3990
    Fin15AnchoredAtom4154 Fin15AnchoredAtom4156 Fin15AnchoredAtom4157 Fin15AnchoredAtom4171
    Fin15AnchoredAtom4172 Fin15AnchoredAtom4177 Fin15AnchoredAtom4192 Fin15AnchoredAtom4193
    Fin15AnchoredAtom4198 Fin15AnchoredAtom4229 Fin15AnchoredAtom4248 Fin15AnchoredAtom4249
    Fin15AnchoredAtom4254 Fin15AnchoredAtom4285 Fin15AnchoredAtom4320 Fin15AnchoredAtom4584
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

theorem fin15Anchored_clause32061 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3582 chi ∧
      ¬Fin15AnchoredAtom3585 chi ∧
      ¬Fin15AnchoredAtom3587 chi ∧
      ¬Fin15AnchoredAtom3589 chi ∧
      ¬Fin15AnchoredAtom3592 chi ∧
      ¬Fin15AnchoredAtom3594 chi ∧
      ¬Fin15AnchoredAtom3596 chi ∧
      ¬Fin15AnchoredAtom3609 chi ∧
      ¬Fin15AnchoredAtom3611 chi ∧
      ¬Fin15AnchoredAtom3616 chi ∧
      ¬Fin15AnchoredAtom3620 chi ∧
      ¬Fin15AnchoredAtom3622 chi ∧
      ¬Fin15AnchoredAtom3624 chi ∧
      ¬Fin15AnchoredAtom3637 chi ∧
      ¬Fin15AnchoredAtom3639 chi ∧
      ¬Fin15AnchoredAtom3644 chi ∧
      ¬Fin15AnchoredAtom3658 chi ∧
      ¬Fin15AnchoredAtom3660 chi ∧
      ¬Fin15AnchoredAtom3665 chi ∧
      ¬Fin15AnchoredAtom3696 chi ∧
      ¬Fin15AnchoredAtom3824 chi ∧
      ¬Fin15AnchoredAtom3826 chi ∧
      ¬Fin15AnchoredAtom3828 chi ∧
      ¬Fin15AnchoredAtom3841 chi ∧
      ¬Fin15AnchoredAtom3843 chi ∧
      ¬Fin15AnchoredAtom3848 chi ∧
      ¬Fin15AnchoredAtom3862 chi ∧
      ¬Fin15AnchoredAtom3864 chi ∧
      ¬Fin15AnchoredAtom3869 chi ∧
      ¬Fin15AnchoredAtom3900 chi ∧
      ¬Fin15AnchoredAtom3918 chi ∧
      ¬Fin15AnchoredAtom3920 chi ∧
      ¬Fin15AnchoredAtom3925 chi ∧
      ¬Fin15AnchoredAtom3956 chi ∧
      ¬Fin15AnchoredAtom3991 chi ∧
      ¬Fin15AnchoredAtom4154 chi ∧
      ¬Fin15AnchoredAtom4156 chi ∧
      ¬Fin15AnchoredAtom4158 chi ∧
      ¬Fin15AnchoredAtom4171 chi ∧
      ¬Fin15AnchoredAtom4173 chi ∧
      ¬Fin15AnchoredAtom4178 chi ∧
      ¬Fin15AnchoredAtom4192 chi ∧
      ¬Fin15AnchoredAtom4194 chi ∧
      ¬Fin15AnchoredAtom4199 chi ∧
      ¬Fin15AnchoredAtom4230 chi ∧
      ¬Fin15AnchoredAtom4248 chi ∧
      ¬Fin15AnchoredAtom4250 chi ∧
      ¬Fin15AnchoredAtom4255 chi ∧
      ¬Fin15AnchoredAtom4286 chi ∧
      ¬Fin15AnchoredAtom4321 chi ∧
      ¬Fin15AnchoredAtom4584 chi ∧
      ¬Fin15AnchoredAtom4586 chi ∧
      ¬Fin15AnchoredAtom4591 chi ∧
      ¬Fin15AnchoredAtom4622 chi ∧
      ¬Fin15AnchoredAtom4657 chi ∧
      ¬Fin15AnchoredAtom4727 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 5, 6, 7, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21740
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3582 Fin15AnchoredAtom3585 Fin15AnchoredAtom3587
    Fin15AnchoredAtom3589 Fin15AnchoredAtom3592 Fin15AnchoredAtom3594 Fin15AnchoredAtom3596
    Fin15AnchoredAtom3609 Fin15AnchoredAtom3611 Fin15AnchoredAtom3616 Fin15AnchoredAtom3620
    Fin15AnchoredAtom3622 Fin15AnchoredAtom3624 Fin15AnchoredAtom3637 Fin15AnchoredAtom3639
    Fin15AnchoredAtom3644 Fin15AnchoredAtom3658 Fin15AnchoredAtom3660 Fin15AnchoredAtom3665
    Fin15AnchoredAtom3696 Fin15AnchoredAtom3824 Fin15AnchoredAtom3826 Fin15AnchoredAtom3828
    Fin15AnchoredAtom3841 Fin15AnchoredAtom3843 Fin15AnchoredAtom3848 Fin15AnchoredAtom3862
    Fin15AnchoredAtom3864 Fin15AnchoredAtom3869 Fin15AnchoredAtom3900 Fin15AnchoredAtom3918
    Fin15AnchoredAtom3920 Fin15AnchoredAtom3925 Fin15AnchoredAtom3956 Fin15AnchoredAtom3991
    Fin15AnchoredAtom4154 Fin15AnchoredAtom4156 Fin15AnchoredAtom4158 Fin15AnchoredAtom4171
    Fin15AnchoredAtom4173 Fin15AnchoredAtom4178 Fin15AnchoredAtom4192 Fin15AnchoredAtom4194
    Fin15AnchoredAtom4199 Fin15AnchoredAtom4230 Fin15AnchoredAtom4248 Fin15AnchoredAtom4250
    Fin15AnchoredAtom4255 Fin15AnchoredAtom4286 Fin15AnchoredAtom4321 Fin15AnchoredAtom4584
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

theorem fin15Anchored_clause32062 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3582 chi ∧
      ¬Fin15AnchoredAtom3585 chi ∧
      ¬Fin15AnchoredAtom3588 chi ∧
      ¬Fin15AnchoredAtom3589 chi ∧
      ¬Fin15AnchoredAtom3592 chi ∧
      ¬Fin15AnchoredAtom3595 chi ∧
      ¬Fin15AnchoredAtom3596 chi ∧
      ¬Fin15AnchoredAtom3610 chi ∧
      ¬Fin15AnchoredAtom3611 chi ∧
      ¬Fin15AnchoredAtom3617 chi ∧
      ¬Fin15AnchoredAtom3620 chi ∧
      ¬Fin15AnchoredAtom3623 chi ∧
      ¬Fin15AnchoredAtom3624 chi ∧
      ¬Fin15AnchoredAtom3638 chi ∧
      ¬Fin15AnchoredAtom3639 chi ∧
      ¬Fin15AnchoredAtom3645 chi ∧
      ¬Fin15AnchoredAtom3659 chi ∧
      ¬Fin15AnchoredAtom3660 chi ∧
      ¬Fin15AnchoredAtom3666 chi ∧
      ¬Fin15AnchoredAtom3697 chi ∧
      ¬Fin15AnchoredAtom3824 chi ∧
      ¬Fin15AnchoredAtom3827 chi ∧
      ¬Fin15AnchoredAtom3828 chi ∧
      ¬Fin15AnchoredAtom3842 chi ∧
      ¬Fin15AnchoredAtom3843 chi ∧
      ¬Fin15AnchoredAtom3849 chi ∧
      ¬Fin15AnchoredAtom3863 chi ∧
      ¬Fin15AnchoredAtom3864 chi ∧
      ¬Fin15AnchoredAtom3870 chi ∧
      ¬Fin15AnchoredAtom3901 chi ∧
      ¬Fin15AnchoredAtom3919 chi ∧
      ¬Fin15AnchoredAtom3920 chi ∧
      ¬Fin15AnchoredAtom3926 chi ∧
      ¬Fin15AnchoredAtom3957 chi ∧
      ¬Fin15AnchoredAtom3992 chi ∧
      ¬Fin15AnchoredAtom4154 chi ∧
      ¬Fin15AnchoredAtom4157 chi ∧
      ¬Fin15AnchoredAtom4158 chi ∧
      ¬Fin15AnchoredAtom4172 chi ∧
      ¬Fin15AnchoredAtom4173 chi ∧
      ¬Fin15AnchoredAtom4179 chi ∧
      ¬Fin15AnchoredAtom4193 chi ∧
      ¬Fin15AnchoredAtom4194 chi ∧
      ¬Fin15AnchoredAtom4200 chi ∧
      ¬Fin15AnchoredAtom4231 chi ∧
      ¬Fin15AnchoredAtom4249 chi ∧
      ¬Fin15AnchoredAtom4250 chi ∧
      ¬Fin15AnchoredAtom4256 chi ∧
      ¬Fin15AnchoredAtom4287 chi ∧
      ¬Fin15AnchoredAtom4322 chi ∧
      ¬Fin15AnchoredAtom4585 chi ∧
      ¬Fin15AnchoredAtom4586 chi ∧
      ¬Fin15AnchoredAtom4592 chi ∧
      ¬Fin15AnchoredAtom4623 chi ∧
      ¬Fin15AnchoredAtom4658 chi ∧
      ¬Fin15AnchoredAtom4728 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 5, 6, 7, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25836
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3582 Fin15AnchoredAtom3585 Fin15AnchoredAtom3588
    Fin15AnchoredAtom3589 Fin15AnchoredAtom3592 Fin15AnchoredAtom3595 Fin15AnchoredAtom3596
    Fin15AnchoredAtom3610 Fin15AnchoredAtom3611 Fin15AnchoredAtom3617 Fin15AnchoredAtom3620
    Fin15AnchoredAtom3623 Fin15AnchoredAtom3624 Fin15AnchoredAtom3638 Fin15AnchoredAtom3639
    Fin15AnchoredAtom3645 Fin15AnchoredAtom3659 Fin15AnchoredAtom3660 Fin15AnchoredAtom3666
    Fin15AnchoredAtom3697 Fin15AnchoredAtom3824 Fin15AnchoredAtom3827 Fin15AnchoredAtom3828
    Fin15AnchoredAtom3842 Fin15AnchoredAtom3843 Fin15AnchoredAtom3849 Fin15AnchoredAtom3863
    Fin15AnchoredAtom3864 Fin15AnchoredAtom3870 Fin15AnchoredAtom3901 Fin15AnchoredAtom3919
    Fin15AnchoredAtom3920 Fin15AnchoredAtom3926 Fin15AnchoredAtom3957 Fin15AnchoredAtom3992
    Fin15AnchoredAtom4154 Fin15AnchoredAtom4157 Fin15AnchoredAtom4158 Fin15AnchoredAtom4172
    Fin15AnchoredAtom4173 Fin15AnchoredAtom4179 Fin15AnchoredAtom4193 Fin15AnchoredAtom4194
    Fin15AnchoredAtom4200 Fin15AnchoredAtom4231 Fin15AnchoredAtom4249 Fin15AnchoredAtom4250
    Fin15AnchoredAtom4256 Fin15AnchoredAtom4287 Fin15AnchoredAtom4322 Fin15AnchoredAtom4585
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

theorem fin15Anchored_clause32063 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3582 chi ∧
      ¬Fin15AnchoredAtom3587 chi ∧
      ¬Fin15AnchoredAtom3588 chi ∧
      ¬Fin15AnchoredAtom3589 chi ∧
      ¬Fin15AnchoredAtom3594 chi ∧
      ¬Fin15AnchoredAtom3595 chi ∧
      ¬Fin15AnchoredAtom3596 chi ∧
      ¬Fin15AnchoredAtom3615 chi ∧
      ¬Fin15AnchoredAtom3616 chi ∧
      ¬Fin15AnchoredAtom3617 chi ∧
      ¬Fin15AnchoredAtom3622 chi ∧
      ¬Fin15AnchoredAtom3623 chi ∧
      ¬Fin15AnchoredAtom3624 chi ∧
      ¬Fin15AnchoredAtom3643 chi ∧
      ¬Fin15AnchoredAtom3644 chi ∧
      ¬Fin15AnchoredAtom3645 chi ∧
      ¬Fin15AnchoredAtom3664 chi ∧
      ¬Fin15AnchoredAtom3665 chi ∧
      ¬Fin15AnchoredAtom3666 chi ∧
      ¬Fin15AnchoredAtom3701 chi ∧
      ¬Fin15AnchoredAtom3826 chi ∧
      ¬Fin15AnchoredAtom3827 chi ∧
      ¬Fin15AnchoredAtom3828 chi ∧
      ¬Fin15AnchoredAtom3847 chi ∧
      ¬Fin15AnchoredAtom3848 chi ∧
      ¬Fin15AnchoredAtom3849 chi ∧
      ¬Fin15AnchoredAtom3868 chi ∧
      ¬Fin15AnchoredAtom3869 chi ∧
      ¬Fin15AnchoredAtom3870 chi ∧
      ¬Fin15AnchoredAtom3905 chi ∧
      ¬Fin15AnchoredAtom3924 chi ∧
      ¬Fin15AnchoredAtom3925 chi ∧
      ¬Fin15AnchoredAtom3926 chi ∧
      ¬Fin15AnchoredAtom3961 chi ∧
      ¬Fin15AnchoredAtom3996 chi ∧
      ¬Fin15AnchoredAtom4156 chi ∧
      ¬Fin15AnchoredAtom4157 chi ∧
      ¬Fin15AnchoredAtom4158 chi ∧
      ¬Fin15AnchoredAtom4177 chi ∧
      ¬Fin15AnchoredAtom4178 chi ∧
      ¬Fin15AnchoredAtom4179 chi ∧
      ¬Fin15AnchoredAtom4198 chi ∧
      ¬Fin15AnchoredAtom4199 chi ∧
      ¬Fin15AnchoredAtom4200 chi ∧
      ¬Fin15AnchoredAtom4235 chi ∧
      ¬Fin15AnchoredAtom4254 chi ∧
      ¬Fin15AnchoredAtom4255 chi ∧
      ¬Fin15AnchoredAtom4256 chi ∧
      ¬Fin15AnchoredAtom4291 chi ∧
      ¬Fin15AnchoredAtom4326 chi ∧
      ¬Fin15AnchoredAtom4590 chi ∧
      ¬Fin15AnchoredAtom4591 chi ∧
      ¬Fin15AnchoredAtom4592 chi ∧
      ¬Fin15AnchoredAtom4627 chi ∧
      ¬Fin15AnchoredAtom4662 chi ∧
      ¬Fin15AnchoredAtom4732 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 5, 6, 7, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask28908
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3582 Fin15AnchoredAtom3587 Fin15AnchoredAtom3588
    Fin15AnchoredAtom3589 Fin15AnchoredAtom3594 Fin15AnchoredAtom3595 Fin15AnchoredAtom3596
    Fin15AnchoredAtom3615 Fin15AnchoredAtom3616 Fin15AnchoredAtom3617 Fin15AnchoredAtom3622
    Fin15AnchoredAtom3623 Fin15AnchoredAtom3624 Fin15AnchoredAtom3643 Fin15AnchoredAtom3644
    Fin15AnchoredAtom3645 Fin15AnchoredAtom3664 Fin15AnchoredAtom3665 Fin15AnchoredAtom3666
    Fin15AnchoredAtom3701 Fin15AnchoredAtom3826 Fin15AnchoredAtom3827 Fin15AnchoredAtom3828
    Fin15AnchoredAtom3847 Fin15AnchoredAtom3848 Fin15AnchoredAtom3849 Fin15AnchoredAtom3868
    Fin15AnchoredAtom3869 Fin15AnchoredAtom3870 Fin15AnchoredAtom3905 Fin15AnchoredAtom3924
    Fin15AnchoredAtom3925 Fin15AnchoredAtom3926 Fin15AnchoredAtom3961 Fin15AnchoredAtom3996
    Fin15AnchoredAtom4156 Fin15AnchoredAtom4157 Fin15AnchoredAtom4158 Fin15AnchoredAtom4177
    Fin15AnchoredAtom4178 Fin15AnchoredAtom4179 Fin15AnchoredAtom4198 Fin15AnchoredAtom4199
    Fin15AnchoredAtom4200 Fin15AnchoredAtom4235 Fin15AnchoredAtom4254 Fin15AnchoredAtom4255
    Fin15AnchoredAtom4256 Fin15AnchoredAtom4291 Fin15AnchoredAtom4326 Fin15AnchoredAtom4590
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

theorem fin15Anchored_clause32064 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3584 chi ∧
      ¬Fin15AnchoredAtom3585 chi ∧
      ¬Fin15AnchoredAtom3587 chi ∧
      ¬Fin15AnchoredAtom3588 chi ∧
      ¬Fin15AnchoredAtom3603 chi ∧
      ¬Fin15AnchoredAtom3605 chi ∧
      ¬Fin15AnchoredAtom3606 chi ∧
      ¬Fin15AnchoredAtom3609 chi ∧
      ¬Fin15AnchoredAtom3610 chi ∧
      ¬Fin15AnchoredAtom3615 chi ∧
      ¬Fin15AnchoredAtom3631 chi ∧
      ¬Fin15AnchoredAtom3633 chi ∧
      ¬Fin15AnchoredAtom3634 chi ∧
      ¬Fin15AnchoredAtom3637 chi ∧
      ¬Fin15AnchoredAtom3638 chi ∧
      ¬Fin15AnchoredAtom3643 chi ∧
      ¬Fin15AnchoredAtom3683 chi ∧
      ¬Fin15AnchoredAtom3684 chi ∧
      ¬Fin15AnchoredAtom3689 chi ∧
      ¬Fin15AnchoredAtom3695 chi ∧
      ¬Fin15AnchoredAtom3835 chi ∧
      ¬Fin15AnchoredAtom3837 chi ∧
      ¬Fin15AnchoredAtom3838 chi ∧
      ¬Fin15AnchoredAtom3841 chi ∧
      ¬Fin15AnchoredAtom3842 chi ∧
      ¬Fin15AnchoredAtom3847 chi ∧
      ¬Fin15AnchoredAtom3887 chi ∧
      ¬Fin15AnchoredAtom3888 chi ∧
      ¬Fin15AnchoredAtom3893 chi ∧
      ¬Fin15AnchoredAtom3899 chi ∧
      ¬Fin15AnchoredAtom3943 chi ∧
      ¬Fin15AnchoredAtom3944 chi ∧
      ¬Fin15AnchoredAtom3949 chi ∧
      ¬Fin15AnchoredAtom3955 chi ∧
      ¬Fin15AnchoredAtom4020 chi ∧
      ¬Fin15AnchoredAtom4165 chi ∧
      ¬Fin15AnchoredAtom4167 chi ∧
      ¬Fin15AnchoredAtom4168 chi ∧
      ¬Fin15AnchoredAtom4171 chi ∧
      ¬Fin15AnchoredAtom4172 chi ∧
      ¬Fin15AnchoredAtom4177 chi ∧
      ¬Fin15AnchoredAtom4217 chi ∧
      ¬Fin15AnchoredAtom4218 chi ∧
      ¬Fin15AnchoredAtom4223 chi ∧
      ¬Fin15AnchoredAtom4229 chi ∧
      ¬Fin15AnchoredAtom4273 chi ∧
      ¬Fin15AnchoredAtom4274 chi ∧
      ¬Fin15AnchoredAtom4279 chi ∧
      ¬Fin15AnchoredAtom4285 chi ∧
      ¬Fin15AnchoredAtom4350 chi ∧
      ¬Fin15AnchoredAtom4609 chi ∧
      ¬Fin15AnchoredAtom4610 chi ∧
      ¬Fin15AnchoredAtom4615 chi ∧
      ¬Fin15AnchoredAtom4621 chi ∧
      ¬Fin15AnchoredAtom4686 chi ∧
      ¬Fin15AnchoredAtom4756 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 5, 6, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13932
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3584 Fin15AnchoredAtom3585 Fin15AnchoredAtom3587
    Fin15AnchoredAtom3588 Fin15AnchoredAtom3603 Fin15AnchoredAtom3605 Fin15AnchoredAtom3606
    Fin15AnchoredAtom3609 Fin15AnchoredAtom3610 Fin15AnchoredAtom3615 Fin15AnchoredAtom3631
    Fin15AnchoredAtom3633 Fin15AnchoredAtom3634 Fin15AnchoredAtom3637 Fin15AnchoredAtom3638
    Fin15AnchoredAtom3643 Fin15AnchoredAtom3683 Fin15AnchoredAtom3684 Fin15AnchoredAtom3689
    Fin15AnchoredAtom3695 Fin15AnchoredAtom3835 Fin15AnchoredAtom3837 Fin15AnchoredAtom3838
    Fin15AnchoredAtom3841 Fin15AnchoredAtom3842 Fin15AnchoredAtom3847 Fin15AnchoredAtom3887
    Fin15AnchoredAtom3888 Fin15AnchoredAtom3893 Fin15AnchoredAtom3899 Fin15AnchoredAtom3943
    Fin15AnchoredAtom3944 Fin15AnchoredAtom3949 Fin15AnchoredAtom3955 Fin15AnchoredAtom4020
    Fin15AnchoredAtom4165 Fin15AnchoredAtom4167 Fin15AnchoredAtom4168 Fin15AnchoredAtom4171
    Fin15AnchoredAtom4172 Fin15AnchoredAtom4177 Fin15AnchoredAtom4217 Fin15AnchoredAtom4218
    Fin15AnchoredAtom4223 Fin15AnchoredAtom4229 Fin15AnchoredAtom4273 Fin15AnchoredAtom4274
    Fin15AnchoredAtom4279 Fin15AnchoredAtom4285 Fin15AnchoredAtom4350 Fin15AnchoredAtom4609
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

theorem fin15Anchored_clause32065 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3584 chi ∧
      ¬Fin15AnchoredAtom3585 chi ∧
      ¬Fin15AnchoredAtom3587 chi ∧
      ¬Fin15AnchoredAtom3589 chi ∧
      ¬Fin15AnchoredAtom3603 chi ∧
      ¬Fin15AnchoredAtom3605 chi ∧
      ¬Fin15AnchoredAtom3607 chi ∧
      ¬Fin15AnchoredAtom3609 chi ∧
      ¬Fin15AnchoredAtom3611 chi ∧
      ¬Fin15AnchoredAtom3616 chi ∧
      ¬Fin15AnchoredAtom3631 chi ∧
      ¬Fin15AnchoredAtom3633 chi ∧
      ¬Fin15AnchoredAtom3635 chi ∧
      ¬Fin15AnchoredAtom3637 chi ∧
      ¬Fin15AnchoredAtom3639 chi ∧
      ¬Fin15AnchoredAtom3644 chi ∧
      ¬Fin15AnchoredAtom3683 chi ∧
      ¬Fin15AnchoredAtom3685 chi ∧
      ¬Fin15AnchoredAtom3690 chi ∧
      ¬Fin15AnchoredAtom3696 chi ∧
      ¬Fin15AnchoredAtom3835 chi ∧
      ¬Fin15AnchoredAtom3837 chi ∧
      ¬Fin15AnchoredAtom3839 chi ∧
      ¬Fin15AnchoredAtom3841 chi ∧
      ¬Fin15AnchoredAtom3843 chi ∧
      ¬Fin15AnchoredAtom3848 chi ∧
      ¬Fin15AnchoredAtom3887 chi ∧
      ¬Fin15AnchoredAtom3889 chi ∧
      ¬Fin15AnchoredAtom3894 chi ∧
      ¬Fin15AnchoredAtom3900 chi ∧
      ¬Fin15AnchoredAtom3943 chi ∧
      ¬Fin15AnchoredAtom3945 chi ∧
      ¬Fin15AnchoredAtom3950 chi ∧
      ¬Fin15AnchoredAtom3956 chi ∧
      ¬Fin15AnchoredAtom4021 chi ∧
      ¬Fin15AnchoredAtom4165 chi ∧
      ¬Fin15AnchoredAtom4167 chi ∧
      ¬Fin15AnchoredAtom4169 chi ∧
      ¬Fin15AnchoredAtom4171 chi ∧
      ¬Fin15AnchoredAtom4173 chi ∧
      ¬Fin15AnchoredAtom4178 chi ∧
      ¬Fin15AnchoredAtom4217 chi ∧
      ¬Fin15AnchoredAtom4219 chi ∧
      ¬Fin15AnchoredAtom4224 chi ∧
      ¬Fin15AnchoredAtom4230 chi ∧
      ¬Fin15AnchoredAtom4273 chi ∧
      ¬Fin15AnchoredAtom4275 chi ∧
      ¬Fin15AnchoredAtom4280 chi ∧
      ¬Fin15AnchoredAtom4286 chi ∧
      ¬Fin15AnchoredAtom4351 chi ∧
      ¬Fin15AnchoredAtom4609 chi ∧
      ¬Fin15AnchoredAtom4611 chi ∧
      ¬Fin15AnchoredAtom4616 chi ∧
      ¬Fin15AnchoredAtom4622 chi ∧
      ¬Fin15AnchoredAtom4687 chi ∧
      ¬Fin15AnchoredAtom4757 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 5, 6, 9, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22124
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3584 Fin15AnchoredAtom3585 Fin15AnchoredAtom3587
    Fin15AnchoredAtom3589 Fin15AnchoredAtom3603 Fin15AnchoredAtom3605 Fin15AnchoredAtom3607
    Fin15AnchoredAtom3609 Fin15AnchoredAtom3611 Fin15AnchoredAtom3616 Fin15AnchoredAtom3631
    Fin15AnchoredAtom3633 Fin15AnchoredAtom3635 Fin15AnchoredAtom3637 Fin15AnchoredAtom3639
    Fin15AnchoredAtom3644 Fin15AnchoredAtom3683 Fin15AnchoredAtom3685 Fin15AnchoredAtom3690
    Fin15AnchoredAtom3696 Fin15AnchoredAtom3835 Fin15AnchoredAtom3837 Fin15AnchoredAtom3839
    Fin15AnchoredAtom3841 Fin15AnchoredAtom3843 Fin15AnchoredAtom3848 Fin15AnchoredAtom3887
    Fin15AnchoredAtom3889 Fin15AnchoredAtom3894 Fin15AnchoredAtom3900 Fin15AnchoredAtom3943
    Fin15AnchoredAtom3945 Fin15AnchoredAtom3950 Fin15AnchoredAtom3956 Fin15AnchoredAtom4021
    Fin15AnchoredAtom4165 Fin15AnchoredAtom4167 Fin15AnchoredAtom4169 Fin15AnchoredAtom4171
    Fin15AnchoredAtom4173 Fin15AnchoredAtom4178 Fin15AnchoredAtom4217 Fin15AnchoredAtom4219
    Fin15AnchoredAtom4224 Fin15AnchoredAtom4230 Fin15AnchoredAtom4273 Fin15AnchoredAtom4275
    Fin15AnchoredAtom4280 Fin15AnchoredAtom4286 Fin15AnchoredAtom4351 Fin15AnchoredAtom4609
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

theorem fin15Anchored_clause32066 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3584 chi ∧
      ¬Fin15AnchoredAtom3585 chi ∧
      ¬Fin15AnchoredAtom3588 chi ∧
      ¬Fin15AnchoredAtom3589 chi ∧
      ¬Fin15AnchoredAtom3603 chi ∧
      ¬Fin15AnchoredAtom3606 chi ∧
      ¬Fin15AnchoredAtom3607 chi ∧
      ¬Fin15AnchoredAtom3610 chi ∧
      ¬Fin15AnchoredAtom3611 chi ∧
      ¬Fin15AnchoredAtom3617 chi ∧
      ¬Fin15AnchoredAtom3631 chi ∧
      ¬Fin15AnchoredAtom3634 chi ∧
      ¬Fin15AnchoredAtom3635 chi ∧
      ¬Fin15AnchoredAtom3638 chi ∧
      ¬Fin15AnchoredAtom3639 chi ∧
      ¬Fin15AnchoredAtom3645 chi ∧
      ¬Fin15AnchoredAtom3684 chi ∧
      ¬Fin15AnchoredAtom3685 chi ∧
      ¬Fin15AnchoredAtom3691 chi ∧
      ¬Fin15AnchoredAtom3697 chi ∧
      ¬Fin15AnchoredAtom3835 chi ∧
      ¬Fin15AnchoredAtom3838 chi ∧
      ¬Fin15AnchoredAtom3839 chi ∧
      ¬Fin15AnchoredAtom3842 chi ∧
      ¬Fin15AnchoredAtom3843 chi ∧
      ¬Fin15AnchoredAtom3849 chi ∧
      ¬Fin15AnchoredAtom3888 chi ∧
      ¬Fin15AnchoredAtom3889 chi ∧
      ¬Fin15AnchoredAtom3895 chi ∧
      ¬Fin15AnchoredAtom3901 chi ∧
      ¬Fin15AnchoredAtom3944 chi ∧
      ¬Fin15AnchoredAtom3945 chi ∧
      ¬Fin15AnchoredAtom3951 chi ∧
      ¬Fin15AnchoredAtom3957 chi ∧
      ¬Fin15AnchoredAtom4022 chi ∧
      ¬Fin15AnchoredAtom4165 chi ∧
      ¬Fin15AnchoredAtom4168 chi ∧
      ¬Fin15AnchoredAtom4169 chi ∧
      ¬Fin15AnchoredAtom4172 chi ∧
      ¬Fin15AnchoredAtom4173 chi ∧
      ¬Fin15AnchoredAtom4179 chi ∧
      ¬Fin15AnchoredAtom4218 chi ∧
      ¬Fin15AnchoredAtom4219 chi ∧
      ¬Fin15AnchoredAtom4225 chi ∧
      ¬Fin15AnchoredAtom4231 chi ∧
      ¬Fin15AnchoredAtom4274 chi ∧
      ¬Fin15AnchoredAtom4275 chi ∧
      ¬Fin15AnchoredAtom4281 chi ∧
      ¬Fin15AnchoredAtom4287 chi ∧
      ¬Fin15AnchoredAtom4352 chi ∧
      ¬Fin15AnchoredAtom4610 chi ∧
      ¬Fin15AnchoredAtom4611 chi ∧
      ¬Fin15AnchoredAtom4617 chi ∧
      ¬Fin15AnchoredAtom4623 chi ∧
      ¬Fin15AnchoredAtom4688 chi ∧
      ¬Fin15AnchoredAtom4758 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 5, 6, 9, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26220
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3584 Fin15AnchoredAtom3585 Fin15AnchoredAtom3588
    Fin15AnchoredAtom3589 Fin15AnchoredAtom3603 Fin15AnchoredAtom3606 Fin15AnchoredAtom3607
    Fin15AnchoredAtom3610 Fin15AnchoredAtom3611 Fin15AnchoredAtom3617 Fin15AnchoredAtom3631
    Fin15AnchoredAtom3634 Fin15AnchoredAtom3635 Fin15AnchoredAtom3638 Fin15AnchoredAtom3639
    Fin15AnchoredAtom3645 Fin15AnchoredAtom3684 Fin15AnchoredAtom3685 Fin15AnchoredAtom3691
    Fin15AnchoredAtom3697 Fin15AnchoredAtom3835 Fin15AnchoredAtom3838 Fin15AnchoredAtom3839
    Fin15AnchoredAtom3842 Fin15AnchoredAtom3843 Fin15AnchoredAtom3849 Fin15AnchoredAtom3888
    Fin15AnchoredAtom3889 Fin15AnchoredAtom3895 Fin15AnchoredAtom3901 Fin15AnchoredAtom3944
    Fin15AnchoredAtom3945 Fin15AnchoredAtom3951 Fin15AnchoredAtom3957 Fin15AnchoredAtom4022
    Fin15AnchoredAtom4165 Fin15AnchoredAtom4168 Fin15AnchoredAtom4169 Fin15AnchoredAtom4172
    Fin15AnchoredAtom4173 Fin15AnchoredAtom4179 Fin15AnchoredAtom4218 Fin15AnchoredAtom4219
    Fin15AnchoredAtom4225 Fin15AnchoredAtom4231 Fin15AnchoredAtom4274 Fin15AnchoredAtom4275
    Fin15AnchoredAtom4281 Fin15AnchoredAtom4287 Fin15AnchoredAtom4352 Fin15AnchoredAtom4610
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

theorem fin15Anchored_clause32067 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3584 chi ∧
      ¬Fin15AnchoredAtom3587 chi ∧
      ¬Fin15AnchoredAtom3588 chi ∧
      ¬Fin15AnchoredAtom3589 chi ∧
      ¬Fin15AnchoredAtom3605 chi ∧
      ¬Fin15AnchoredAtom3606 chi ∧
      ¬Fin15AnchoredAtom3607 chi ∧
      ¬Fin15AnchoredAtom3615 chi ∧
      ¬Fin15AnchoredAtom3616 chi ∧
      ¬Fin15AnchoredAtom3617 chi ∧
      ¬Fin15AnchoredAtom3633 chi ∧
      ¬Fin15AnchoredAtom3634 chi ∧
      ¬Fin15AnchoredAtom3635 chi ∧
      ¬Fin15AnchoredAtom3643 chi ∧
      ¬Fin15AnchoredAtom3644 chi ∧
      ¬Fin15AnchoredAtom3645 chi ∧
      ¬Fin15AnchoredAtom3689 chi ∧
      ¬Fin15AnchoredAtom3690 chi ∧
      ¬Fin15AnchoredAtom3691 chi ∧
      ¬Fin15AnchoredAtom3701 chi ∧
      ¬Fin15AnchoredAtom3837 chi ∧
      ¬Fin15AnchoredAtom3838 chi ∧
      ¬Fin15AnchoredAtom3839 chi ∧
      ¬Fin15AnchoredAtom3847 chi ∧
      ¬Fin15AnchoredAtom3848 chi ∧
      ¬Fin15AnchoredAtom3849 chi ∧
      ¬Fin15AnchoredAtom3893 chi ∧
      ¬Fin15AnchoredAtom3894 chi ∧
      ¬Fin15AnchoredAtom3895 chi ∧
      ¬Fin15AnchoredAtom3905 chi ∧
      ¬Fin15AnchoredAtom3949 chi ∧
      ¬Fin15AnchoredAtom3950 chi ∧
      ¬Fin15AnchoredAtom3951 chi ∧
      ¬Fin15AnchoredAtom3961 chi ∧
      ¬Fin15AnchoredAtom4026 chi ∧
      ¬Fin15AnchoredAtom4167 chi ∧
      ¬Fin15AnchoredAtom4168 chi ∧
      ¬Fin15AnchoredAtom4169 chi ∧
      ¬Fin15AnchoredAtom4177 chi ∧
      ¬Fin15AnchoredAtom4178 chi ∧
      ¬Fin15AnchoredAtom4179 chi ∧
      ¬Fin15AnchoredAtom4223 chi ∧
      ¬Fin15AnchoredAtom4224 chi ∧
      ¬Fin15AnchoredAtom4225 chi ∧
      ¬Fin15AnchoredAtom4235 chi ∧
      ¬Fin15AnchoredAtom4279 chi ∧
      ¬Fin15AnchoredAtom4280 chi ∧
      ¬Fin15AnchoredAtom4281 chi ∧
      ¬Fin15AnchoredAtom4291 chi ∧
      ¬Fin15AnchoredAtom4356 chi ∧
      ¬Fin15AnchoredAtom4615 chi ∧
      ¬Fin15AnchoredAtom4616 chi ∧
      ¬Fin15AnchoredAtom4617 chi ∧
      ¬Fin15AnchoredAtom4627 chi ∧
      ¬Fin15AnchoredAtom4692 chi ∧
      ¬Fin15AnchoredAtom4762 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 5, 6, 9, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29292
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3584 Fin15AnchoredAtom3587 Fin15AnchoredAtom3588
    Fin15AnchoredAtom3589 Fin15AnchoredAtom3605 Fin15AnchoredAtom3606 Fin15AnchoredAtom3607
    Fin15AnchoredAtom3615 Fin15AnchoredAtom3616 Fin15AnchoredAtom3617 Fin15AnchoredAtom3633
    Fin15AnchoredAtom3634 Fin15AnchoredAtom3635 Fin15AnchoredAtom3643 Fin15AnchoredAtom3644
    Fin15AnchoredAtom3645 Fin15AnchoredAtom3689 Fin15AnchoredAtom3690 Fin15AnchoredAtom3691
    Fin15AnchoredAtom3701 Fin15AnchoredAtom3837 Fin15AnchoredAtom3838 Fin15AnchoredAtom3839
    Fin15AnchoredAtom3847 Fin15AnchoredAtom3848 Fin15AnchoredAtom3849 Fin15AnchoredAtom3893
    Fin15AnchoredAtom3894 Fin15AnchoredAtom3895 Fin15AnchoredAtom3905 Fin15AnchoredAtom3949
    Fin15AnchoredAtom3950 Fin15AnchoredAtom3951 Fin15AnchoredAtom3961 Fin15AnchoredAtom4026
    Fin15AnchoredAtom4167 Fin15AnchoredAtom4168 Fin15AnchoredAtom4169 Fin15AnchoredAtom4177
    Fin15AnchoredAtom4178 Fin15AnchoredAtom4179 Fin15AnchoredAtom4223 Fin15AnchoredAtom4224
    Fin15AnchoredAtom4225 Fin15AnchoredAtom4235 Fin15AnchoredAtom4279 Fin15AnchoredAtom4280
    Fin15AnchoredAtom4281 Fin15AnchoredAtom4291 Fin15AnchoredAtom4356 Fin15AnchoredAtom4615
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

theorem fin15Anchored_clause32068 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3585 chi ∧
      ¬Fin15AnchoredAtom3587 chi ∧
      ¬Fin15AnchoredAtom3588 chi ∧
      ¬Fin15AnchoredAtom3589 chi ∧
      ¬Fin15AnchoredAtom3609 chi ∧
      ¬Fin15AnchoredAtom3610 chi ∧
      ¬Fin15AnchoredAtom3611 chi ∧
      ¬Fin15AnchoredAtom3615 chi ∧
      ¬Fin15AnchoredAtom3616 chi ∧
      ¬Fin15AnchoredAtom3617 chi ∧
      ¬Fin15AnchoredAtom3637 chi ∧
      ¬Fin15AnchoredAtom3638 chi ∧
      ¬Fin15AnchoredAtom3639 chi ∧
      ¬Fin15AnchoredAtom3643 chi ∧
      ¬Fin15AnchoredAtom3644 chi ∧
      ¬Fin15AnchoredAtom3645 chi ∧
      ¬Fin15AnchoredAtom3695 chi ∧
      ¬Fin15AnchoredAtom3696 chi ∧
      ¬Fin15AnchoredAtom3697 chi ∧
      ¬Fin15AnchoredAtom3701 chi ∧
      ¬Fin15AnchoredAtom3841 chi ∧
      ¬Fin15AnchoredAtom3842 chi ∧
      ¬Fin15AnchoredAtom3843 chi ∧
      ¬Fin15AnchoredAtom3847 chi ∧
      ¬Fin15AnchoredAtom3848 chi ∧
      ¬Fin15AnchoredAtom3849 chi ∧
      ¬Fin15AnchoredAtom3899 chi ∧
      ¬Fin15AnchoredAtom3900 chi ∧
      ¬Fin15AnchoredAtom3901 chi ∧
      ¬Fin15AnchoredAtom3905 chi ∧
      ¬Fin15AnchoredAtom3955 chi ∧
      ¬Fin15AnchoredAtom3956 chi ∧
      ¬Fin15AnchoredAtom3957 chi ∧
      ¬Fin15AnchoredAtom3961 chi ∧
      ¬Fin15AnchoredAtom4030 chi ∧
      ¬Fin15AnchoredAtom4171 chi ∧
      ¬Fin15AnchoredAtom4172 chi ∧
      ¬Fin15AnchoredAtom4173 chi ∧
      ¬Fin15AnchoredAtom4177 chi ∧
      ¬Fin15AnchoredAtom4178 chi ∧
      ¬Fin15AnchoredAtom4179 chi ∧
      ¬Fin15AnchoredAtom4229 chi ∧
      ¬Fin15AnchoredAtom4230 chi ∧
      ¬Fin15AnchoredAtom4231 chi ∧
      ¬Fin15AnchoredAtom4235 chi ∧
      ¬Fin15AnchoredAtom4285 chi ∧
      ¬Fin15AnchoredAtom4286 chi ∧
      ¬Fin15AnchoredAtom4287 chi ∧
      ¬Fin15AnchoredAtom4291 chi ∧
      ¬Fin15AnchoredAtom4360 chi ∧
      ¬Fin15AnchoredAtom4621 chi ∧
      ¬Fin15AnchoredAtom4622 chi ∧
      ¬Fin15AnchoredAtom4623 chi ∧
      ¬Fin15AnchoredAtom4627 chi ∧
      ¬Fin15AnchoredAtom4696 chi ∧
      ¬Fin15AnchoredAtom4766 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 5, 6, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29804
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3585 Fin15AnchoredAtom3587 Fin15AnchoredAtom3588
    Fin15AnchoredAtom3589 Fin15AnchoredAtom3609 Fin15AnchoredAtom3610 Fin15AnchoredAtom3611
    Fin15AnchoredAtom3615 Fin15AnchoredAtom3616 Fin15AnchoredAtom3617 Fin15AnchoredAtom3637
    Fin15AnchoredAtom3638 Fin15AnchoredAtom3639 Fin15AnchoredAtom3643 Fin15AnchoredAtom3644
    Fin15AnchoredAtom3645 Fin15AnchoredAtom3695 Fin15AnchoredAtom3696 Fin15AnchoredAtom3697
    Fin15AnchoredAtom3701 Fin15AnchoredAtom3841 Fin15AnchoredAtom3842 Fin15AnchoredAtom3843
    Fin15AnchoredAtom3847 Fin15AnchoredAtom3848 Fin15AnchoredAtom3849 Fin15AnchoredAtom3899
    Fin15AnchoredAtom3900 Fin15AnchoredAtom3901 Fin15AnchoredAtom3905 Fin15AnchoredAtom3955
    Fin15AnchoredAtom3956 Fin15AnchoredAtom3957 Fin15AnchoredAtom3961 Fin15AnchoredAtom4030
    Fin15AnchoredAtom4171 Fin15AnchoredAtom4172 Fin15AnchoredAtom4173 Fin15AnchoredAtom4177
    Fin15AnchoredAtom4178 Fin15AnchoredAtom4179 Fin15AnchoredAtom4229 Fin15AnchoredAtom4230
    Fin15AnchoredAtom4231 Fin15AnchoredAtom4235 Fin15AnchoredAtom4285 Fin15AnchoredAtom4286
    Fin15AnchoredAtom4287 Fin15AnchoredAtom4291 Fin15AnchoredAtom4360 Fin15AnchoredAtom4621
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

theorem fin15Anchored_clause32069 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3591 chi ∧
      ¬Fin15AnchoredAtom3592 chi ∧
      ¬Fin15AnchoredAtom3594 chi ∧
      ¬Fin15AnchoredAtom3595 chi ∧
      ¬Fin15AnchoredAtom3603 chi ∧
      ¬Fin15AnchoredAtom3605 chi ∧
      ¬Fin15AnchoredAtom3606 chi ∧
      ¬Fin15AnchoredAtom3609 chi ∧
      ¬Fin15AnchoredAtom3610 chi ∧
      ¬Fin15AnchoredAtom3615 chi ∧
      ¬Fin15AnchoredAtom3652 chi ∧
      ¬Fin15AnchoredAtom3654 chi ∧
      ¬Fin15AnchoredAtom3655 chi ∧
      ¬Fin15AnchoredAtom3658 chi ∧
      ¬Fin15AnchoredAtom3659 chi ∧
      ¬Fin15AnchoredAtom3664 chi ∧
      ¬Fin15AnchoredAtom3683 chi ∧
      ¬Fin15AnchoredAtom3684 chi ∧
      ¬Fin15AnchoredAtom3689 chi ∧
      ¬Fin15AnchoredAtom3695 chi ∧
      ¬Fin15AnchoredAtom3856 chi ∧
      ¬Fin15AnchoredAtom3858 chi ∧
      ¬Fin15AnchoredAtom3859 chi ∧
      ¬Fin15AnchoredAtom3862 chi ∧
      ¬Fin15AnchoredAtom3863 chi ∧
      ¬Fin15AnchoredAtom3868 chi ∧
      ¬Fin15AnchoredAtom3887 chi ∧
      ¬Fin15AnchoredAtom3888 chi ∧
      ¬Fin15AnchoredAtom3893 chi ∧
      ¬Fin15AnchoredAtom3899 chi ∧
      ¬Fin15AnchoredAtom3978 chi ∧
      ¬Fin15AnchoredAtom3979 chi ∧
      ¬Fin15AnchoredAtom3984 chi ∧
      ¬Fin15AnchoredAtom3990 chi ∧
      ¬Fin15AnchoredAtom4020 chi ∧
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
  refine ⟨{2, 3, 5, 7, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13996
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3591 Fin15AnchoredAtom3592 Fin15AnchoredAtom3594
    Fin15AnchoredAtom3595 Fin15AnchoredAtom3603 Fin15AnchoredAtom3605 Fin15AnchoredAtom3606
    Fin15AnchoredAtom3609 Fin15AnchoredAtom3610 Fin15AnchoredAtom3615 Fin15AnchoredAtom3652
    Fin15AnchoredAtom3654 Fin15AnchoredAtom3655 Fin15AnchoredAtom3658 Fin15AnchoredAtom3659
    Fin15AnchoredAtom3664 Fin15AnchoredAtom3683 Fin15AnchoredAtom3684 Fin15AnchoredAtom3689
    Fin15AnchoredAtom3695 Fin15AnchoredAtom3856 Fin15AnchoredAtom3858 Fin15AnchoredAtom3859
    Fin15AnchoredAtom3862 Fin15AnchoredAtom3863 Fin15AnchoredAtom3868 Fin15AnchoredAtom3887
    Fin15AnchoredAtom3888 Fin15AnchoredAtom3893 Fin15AnchoredAtom3899 Fin15AnchoredAtom3978
    Fin15AnchoredAtom3979 Fin15AnchoredAtom3984 Fin15AnchoredAtom3990 Fin15AnchoredAtom4020
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

theorem fin15Anchored_clause32070 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3591 chi ∧
      ¬Fin15AnchoredAtom3592 chi ∧
      ¬Fin15AnchoredAtom3594 chi ∧
      ¬Fin15AnchoredAtom3596 chi ∧
      ¬Fin15AnchoredAtom3603 chi ∧
      ¬Fin15AnchoredAtom3605 chi ∧
      ¬Fin15AnchoredAtom3607 chi ∧
      ¬Fin15AnchoredAtom3609 chi ∧
      ¬Fin15AnchoredAtom3611 chi ∧
      ¬Fin15AnchoredAtom3616 chi ∧
      ¬Fin15AnchoredAtom3652 chi ∧
      ¬Fin15AnchoredAtom3654 chi ∧
      ¬Fin15AnchoredAtom3656 chi ∧
      ¬Fin15AnchoredAtom3658 chi ∧
      ¬Fin15AnchoredAtom3660 chi ∧
      ¬Fin15AnchoredAtom3665 chi ∧
      ¬Fin15AnchoredAtom3683 chi ∧
      ¬Fin15AnchoredAtom3685 chi ∧
      ¬Fin15AnchoredAtom3690 chi ∧
      ¬Fin15AnchoredAtom3696 chi ∧
      ¬Fin15AnchoredAtom3856 chi ∧
      ¬Fin15AnchoredAtom3858 chi ∧
      ¬Fin15AnchoredAtom3860 chi ∧
      ¬Fin15AnchoredAtom3862 chi ∧
      ¬Fin15AnchoredAtom3864 chi ∧
      ¬Fin15AnchoredAtom3869 chi ∧
      ¬Fin15AnchoredAtom3887 chi ∧
      ¬Fin15AnchoredAtom3889 chi ∧
      ¬Fin15AnchoredAtom3894 chi ∧
      ¬Fin15AnchoredAtom3900 chi ∧
      ¬Fin15AnchoredAtom3978 chi ∧
      ¬Fin15AnchoredAtom3980 chi ∧
      ¬Fin15AnchoredAtom3985 chi ∧
      ¬Fin15AnchoredAtom3991 chi ∧
      ¬Fin15AnchoredAtom4021 chi ∧
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
  refine ⟨{2, 3, 5, 7, 9, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22188
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3591 Fin15AnchoredAtom3592 Fin15AnchoredAtom3594
    Fin15AnchoredAtom3596 Fin15AnchoredAtom3603 Fin15AnchoredAtom3605 Fin15AnchoredAtom3607
    Fin15AnchoredAtom3609 Fin15AnchoredAtom3611 Fin15AnchoredAtom3616 Fin15AnchoredAtom3652
    Fin15AnchoredAtom3654 Fin15AnchoredAtom3656 Fin15AnchoredAtom3658 Fin15AnchoredAtom3660
    Fin15AnchoredAtom3665 Fin15AnchoredAtom3683 Fin15AnchoredAtom3685 Fin15AnchoredAtom3690
    Fin15AnchoredAtom3696 Fin15AnchoredAtom3856 Fin15AnchoredAtom3858 Fin15AnchoredAtom3860
    Fin15AnchoredAtom3862 Fin15AnchoredAtom3864 Fin15AnchoredAtom3869 Fin15AnchoredAtom3887
    Fin15AnchoredAtom3889 Fin15AnchoredAtom3894 Fin15AnchoredAtom3900 Fin15AnchoredAtom3978
    Fin15AnchoredAtom3980 Fin15AnchoredAtom3985 Fin15AnchoredAtom3991 Fin15AnchoredAtom4021
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

theorem fin15Anchored_clause32071 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3591 chi ∧
      ¬Fin15AnchoredAtom3592 chi ∧
      ¬Fin15AnchoredAtom3595 chi ∧
      ¬Fin15AnchoredAtom3596 chi ∧
      ¬Fin15AnchoredAtom3603 chi ∧
      ¬Fin15AnchoredAtom3606 chi ∧
      ¬Fin15AnchoredAtom3607 chi ∧
      ¬Fin15AnchoredAtom3610 chi ∧
      ¬Fin15AnchoredAtom3611 chi ∧
      ¬Fin15AnchoredAtom3617 chi ∧
      ¬Fin15AnchoredAtom3652 chi ∧
      ¬Fin15AnchoredAtom3655 chi ∧
      ¬Fin15AnchoredAtom3656 chi ∧
      ¬Fin15AnchoredAtom3659 chi ∧
      ¬Fin15AnchoredAtom3660 chi ∧
      ¬Fin15AnchoredAtom3666 chi ∧
      ¬Fin15AnchoredAtom3684 chi ∧
      ¬Fin15AnchoredAtom3685 chi ∧
      ¬Fin15AnchoredAtom3691 chi ∧
      ¬Fin15AnchoredAtom3697 chi ∧
      ¬Fin15AnchoredAtom3856 chi ∧
      ¬Fin15AnchoredAtom3859 chi ∧
      ¬Fin15AnchoredAtom3860 chi ∧
      ¬Fin15AnchoredAtom3863 chi ∧
      ¬Fin15AnchoredAtom3864 chi ∧
      ¬Fin15AnchoredAtom3870 chi ∧
      ¬Fin15AnchoredAtom3888 chi ∧
      ¬Fin15AnchoredAtom3889 chi ∧
      ¬Fin15AnchoredAtom3895 chi ∧
      ¬Fin15AnchoredAtom3901 chi ∧
      ¬Fin15AnchoredAtom3979 chi ∧
      ¬Fin15AnchoredAtom3980 chi ∧
      ¬Fin15AnchoredAtom3986 chi ∧
      ¬Fin15AnchoredAtom3992 chi ∧
      ¬Fin15AnchoredAtom4022 chi ∧
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
  refine ⟨{2, 3, 5, 7, 9, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26284
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3591 Fin15AnchoredAtom3592 Fin15AnchoredAtom3595
    Fin15AnchoredAtom3596 Fin15AnchoredAtom3603 Fin15AnchoredAtom3606 Fin15AnchoredAtom3607
    Fin15AnchoredAtom3610 Fin15AnchoredAtom3611 Fin15AnchoredAtom3617 Fin15AnchoredAtom3652
    Fin15AnchoredAtom3655 Fin15AnchoredAtom3656 Fin15AnchoredAtom3659 Fin15AnchoredAtom3660
    Fin15AnchoredAtom3666 Fin15AnchoredAtom3684 Fin15AnchoredAtom3685 Fin15AnchoredAtom3691
    Fin15AnchoredAtom3697 Fin15AnchoredAtom3856 Fin15AnchoredAtom3859 Fin15AnchoredAtom3860
    Fin15AnchoredAtom3863 Fin15AnchoredAtom3864 Fin15AnchoredAtom3870 Fin15AnchoredAtom3888
    Fin15AnchoredAtom3889 Fin15AnchoredAtom3895 Fin15AnchoredAtom3901 Fin15AnchoredAtom3979
    Fin15AnchoredAtom3980 Fin15AnchoredAtom3986 Fin15AnchoredAtom3992 Fin15AnchoredAtom4022
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

theorem fin15Anchored_clause32072 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3591 chi ∧
      ¬Fin15AnchoredAtom3594 chi ∧
      ¬Fin15AnchoredAtom3595 chi ∧
      ¬Fin15AnchoredAtom3596 chi ∧
      ¬Fin15AnchoredAtom3605 chi ∧
      ¬Fin15AnchoredAtom3606 chi ∧
      ¬Fin15AnchoredAtom3607 chi ∧
      ¬Fin15AnchoredAtom3615 chi ∧
      ¬Fin15AnchoredAtom3616 chi ∧
      ¬Fin15AnchoredAtom3617 chi ∧
      ¬Fin15AnchoredAtom3654 chi ∧
      ¬Fin15AnchoredAtom3655 chi ∧
      ¬Fin15AnchoredAtom3656 chi ∧
      ¬Fin15AnchoredAtom3664 chi ∧
      ¬Fin15AnchoredAtom3665 chi ∧
      ¬Fin15AnchoredAtom3666 chi ∧
      ¬Fin15AnchoredAtom3689 chi ∧
      ¬Fin15AnchoredAtom3690 chi ∧
      ¬Fin15AnchoredAtom3691 chi ∧
      ¬Fin15AnchoredAtom3701 chi ∧
      ¬Fin15AnchoredAtom3858 chi ∧
      ¬Fin15AnchoredAtom3859 chi ∧
      ¬Fin15AnchoredAtom3860 chi ∧
      ¬Fin15AnchoredAtom3868 chi ∧
      ¬Fin15AnchoredAtom3869 chi ∧
      ¬Fin15AnchoredAtom3870 chi ∧
      ¬Fin15AnchoredAtom3893 chi ∧
      ¬Fin15AnchoredAtom3894 chi ∧
      ¬Fin15AnchoredAtom3895 chi ∧
      ¬Fin15AnchoredAtom3905 chi ∧
      ¬Fin15AnchoredAtom3984 chi ∧
      ¬Fin15AnchoredAtom3985 chi ∧
      ¬Fin15AnchoredAtom3986 chi ∧
      ¬Fin15AnchoredAtom3996 chi ∧
      ¬Fin15AnchoredAtom4026 chi ∧
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
  refine ⟨{2, 3, 5, 7, 9, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29356
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3591 Fin15AnchoredAtom3594 Fin15AnchoredAtom3595
    Fin15AnchoredAtom3596 Fin15AnchoredAtom3605 Fin15AnchoredAtom3606 Fin15AnchoredAtom3607
    Fin15AnchoredAtom3615 Fin15AnchoredAtom3616 Fin15AnchoredAtom3617 Fin15AnchoredAtom3654
    Fin15AnchoredAtom3655 Fin15AnchoredAtom3656 Fin15AnchoredAtom3664 Fin15AnchoredAtom3665
    Fin15AnchoredAtom3666 Fin15AnchoredAtom3689 Fin15AnchoredAtom3690 Fin15AnchoredAtom3691
    Fin15AnchoredAtom3701 Fin15AnchoredAtom3858 Fin15AnchoredAtom3859 Fin15AnchoredAtom3860
    Fin15AnchoredAtom3868 Fin15AnchoredAtom3869 Fin15AnchoredAtom3870 Fin15AnchoredAtom3893
    Fin15AnchoredAtom3894 Fin15AnchoredAtom3895 Fin15AnchoredAtom3905 Fin15AnchoredAtom3984
    Fin15AnchoredAtom3985 Fin15AnchoredAtom3986 Fin15AnchoredAtom3996 Fin15AnchoredAtom4026
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

theorem fin15Anchored_clause32073 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3592 chi ∧
      ¬Fin15AnchoredAtom3594 chi ∧
      ¬Fin15AnchoredAtom3595 chi ∧
      ¬Fin15AnchoredAtom3596 chi ∧
      ¬Fin15AnchoredAtom3609 chi ∧
      ¬Fin15AnchoredAtom3610 chi ∧
      ¬Fin15AnchoredAtom3611 chi ∧
      ¬Fin15AnchoredAtom3615 chi ∧
      ¬Fin15AnchoredAtom3616 chi ∧
      ¬Fin15AnchoredAtom3617 chi ∧
      ¬Fin15AnchoredAtom3658 chi ∧
      ¬Fin15AnchoredAtom3659 chi ∧
      ¬Fin15AnchoredAtom3660 chi ∧
      ¬Fin15AnchoredAtom3664 chi ∧
      ¬Fin15AnchoredAtom3665 chi ∧
      ¬Fin15AnchoredAtom3666 chi ∧
      ¬Fin15AnchoredAtom3695 chi ∧
      ¬Fin15AnchoredAtom3696 chi ∧
      ¬Fin15AnchoredAtom3697 chi ∧
      ¬Fin15AnchoredAtom3701 chi ∧
      ¬Fin15AnchoredAtom3862 chi ∧
      ¬Fin15AnchoredAtom3863 chi ∧
      ¬Fin15AnchoredAtom3864 chi ∧
      ¬Fin15AnchoredAtom3868 chi ∧
      ¬Fin15AnchoredAtom3869 chi ∧
      ¬Fin15AnchoredAtom3870 chi ∧
      ¬Fin15AnchoredAtom3899 chi ∧
      ¬Fin15AnchoredAtom3900 chi ∧
      ¬Fin15AnchoredAtom3901 chi ∧
      ¬Fin15AnchoredAtom3905 chi ∧
      ¬Fin15AnchoredAtom3990 chi ∧
      ¬Fin15AnchoredAtom3991 chi ∧
      ¬Fin15AnchoredAtom3992 chi ∧
      ¬Fin15AnchoredAtom3996 chi ∧
      ¬Fin15AnchoredAtom4030 chi ∧
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
  refine ⟨{2, 3, 5, 7, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29868
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3592 Fin15AnchoredAtom3594 Fin15AnchoredAtom3595
    Fin15AnchoredAtom3596 Fin15AnchoredAtom3609 Fin15AnchoredAtom3610 Fin15AnchoredAtom3611
    Fin15AnchoredAtom3615 Fin15AnchoredAtom3616 Fin15AnchoredAtom3617 Fin15AnchoredAtom3658
    Fin15AnchoredAtom3659 Fin15AnchoredAtom3660 Fin15AnchoredAtom3664 Fin15AnchoredAtom3665
    Fin15AnchoredAtom3666 Fin15AnchoredAtom3695 Fin15AnchoredAtom3696 Fin15AnchoredAtom3697
    Fin15AnchoredAtom3701 Fin15AnchoredAtom3862 Fin15AnchoredAtom3863 Fin15AnchoredAtom3864
    Fin15AnchoredAtom3868 Fin15AnchoredAtom3869 Fin15AnchoredAtom3870 Fin15AnchoredAtom3899
    Fin15AnchoredAtom3900 Fin15AnchoredAtom3901 Fin15AnchoredAtom3905 Fin15AnchoredAtom3990
    Fin15AnchoredAtom3991 Fin15AnchoredAtom3992 Fin15AnchoredAtom3996 Fin15AnchoredAtom4030
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

theorem fin15Anchored_clause32074 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3603 chi ∧
      ¬Fin15AnchoredAtom3605 chi ∧
      ¬Fin15AnchoredAtom3606 chi ∧
      ¬Fin15AnchoredAtom3607 chi ∧
      ¬Fin15AnchoredAtom3609 chi ∧
      ¬Fin15AnchoredAtom3610 chi ∧
      ¬Fin15AnchoredAtom3611 chi ∧
      ¬Fin15AnchoredAtom3615 chi ∧
      ¬Fin15AnchoredAtom3616 chi ∧
      ¬Fin15AnchoredAtom3617 chi ∧
      ¬Fin15AnchoredAtom3683 chi ∧
      ¬Fin15AnchoredAtom3684 chi ∧
      ¬Fin15AnchoredAtom3685 chi ∧
      ¬Fin15AnchoredAtom3689 chi ∧
      ¬Fin15AnchoredAtom3690 chi ∧
      ¬Fin15AnchoredAtom3691 chi ∧
      ¬Fin15AnchoredAtom3695 chi ∧
      ¬Fin15AnchoredAtom3696 chi ∧
      ¬Fin15AnchoredAtom3697 chi ∧
      ¬Fin15AnchoredAtom3701 chi ∧
      ¬Fin15AnchoredAtom3887 chi ∧
      ¬Fin15AnchoredAtom3888 chi ∧
      ¬Fin15AnchoredAtom3889 chi ∧
      ¬Fin15AnchoredAtom3893 chi ∧
      ¬Fin15AnchoredAtom3894 chi ∧
      ¬Fin15AnchoredAtom3895 chi ∧
      ¬Fin15AnchoredAtom3899 chi ∧
      ¬Fin15AnchoredAtom3900 chi ∧
      ¬Fin15AnchoredAtom3901 chi ∧
      ¬Fin15AnchoredAtom3905 chi ∧
      ¬Fin15AnchoredAtom4020 chi ∧
      ¬Fin15AnchoredAtom4021 chi ∧
      ¬Fin15AnchoredAtom4022 chi ∧
      ¬Fin15AnchoredAtom4026 chi ∧
      ¬Fin15AnchoredAtom4030 chi ∧
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
  refine ⟨{2, 3, 5, 9, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask30252
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3603 Fin15AnchoredAtom3605 Fin15AnchoredAtom3606
    Fin15AnchoredAtom3607 Fin15AnchoredAtom3609 Fin15AnchoredAtom3610 Fin15AnchoredAtom3611
    Fin15AnchoredAtom3615 Fin15AnchoredAtom3616 Fin15AnchoredAtom3617 Fin15AnchoredAtom3683
    Fin15AnchoredAtom3684 Fin15AnchoredAtom3685 Fin15AnchoredAtom3689 Fin15AnchoredAtom3690
    Fin15AnchoredAtom3691 Fin15AnchoredAtom3695 Fin15AnchoredAtom3696 Fin15AnchoredAtom3697
    Fin15AnchoredAtom3701 Fin15AnchoredAtom3887 Fin15AnchoredAtom3888 Fin15AnchoredAtom3889
    Fin15AnchoredAtom3893 Fin15AnchoredAtom3894 Fin15AnchoredAtom3895 Fin15AnchoredAtom3899
    Fin15AnchoredAtom3900 Fin15AnchoredAtom3901 Fin15AnchoredAtom3905 Fin15AnchoredAtom4020
    Fin15AnchoredAtom4021 Fin15AnchoredAtom4022 Fin15AnchoredAtom4026 Fin15AnchoredAtom4030
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

theorem fin15Anchored_clause32075 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3619 chi ∧
      ¬Fin15AnchoredAtom3620 chi ∧
      ¬Fin15AnchoredAtom3622 chi ∧
      ¬Fin15AnchoredAtom3623 chi ∧
      ¬Fin15AnchoredAtom3631 chi ∧
      ¬Fin15AnchoredAtom3633 chi ∧
      ¬Fin15AnchoredAtom3634 chi ∧
      ¬Fin15AnchoredAtom3637 chi ∧
      ¬Fin15AnchoredAtom3638 chi ∧
      ¬Fin15AnchoredAtom3643 chi ∧
      ¬Fin15AnchoredAtom3652 chi ∧
      ¬Fin15AnchoredAtom3654 chi ∧
      ¬Fin15AnchoredAtom3655 chi ∧
      ¬Fin15AnchoredAtom3658 chi ∧
      ¬Fin15AnchoredAtom3659 chi ∧
      ¬Fin15AnchoredAtom3664 chi ∧
      ¬Fin15AnchoredAtom3683 chi ∧
      ¬Fin15AnchoredAtom3684 chi ∧
      ¬Fin15AnchoredAtom3689 chi ∧
      ¬Fin15AnchoredAtom3695 chi ∧
      ¬Fin15AnchoredAtom3912 chi ∧
      ¬Fin15AnchoredAtom3914 chi ∧
      ¬Fin15AnchoredAtom3915 chi ∧
      ¬Fin15AnchoredAtom3918 chi ∧
      ¬Fin15AnchoredAtom3919 chi ∧
      ¬Fin15AnchoredAtom3924 chi ∧
      ¬Fin15AnchoredAtom3943 chi ∧
      ¬Fin15AnchoredAtom3944 chi ∧
      ¬Fin15AnchoredAtom3949 chi ∧
      ¬Fin15AnchoredAtom3955 chi ∧
      ¬Fin15AnchoredAtom3978 chi ∧
      ¬Fin15AnchoredAtom3979 chi ∧
      ¬Fin15AnchoredAtom3984 chi ∧
      ¬Fin15AnchoredAtom3990 chi ∧
      ¬Fin15AnchoredAtom4020 chi ∧
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
  refine ⟨{2, 3, 6, 7, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask14028
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3619 Fin15AnchoredAtom3620 Fin15AnchoredAtom3622
    Fin15AnchoredAtom3623 Fin15AnchoredAtom3631 Fin15AnchoredAtom3633 Fin15AnchoredAtom3634
    Fin15AnchoredAtom3637 Fin15AnchoredAtom3638 Fin15AnchoredAtom3643 Fin15AnchoredAtom3652
    Fin15AnchoredAtom3654 Fin15AnchoredAtom3655 Fin15AnchoredAtom3658 Fin15AnchoredAtom3659
    Fin15AnchoredAtom3664 Fin15AnchoredAtom3683 Fin15AnchoredAtom3684 Fin15AnchoredAtom3689
    Fin15AnchoredAtom3695 Fin15AnchoredAtom3912 Fin15AnchoredAtom3914 Fin15AnchoredAtom3915
    Fin15AnchoredAtom3918 Fin15AnchoredAtom3919 Fin15AnchoredAtom3924 Fin15AnchoredAtom3943
    Fin15AnchoredAtom3944 Fin15AnchoredAtom3949 Fin15AnchoredAtom3955 Fin15AnchoredAtom3978
    Fin15AnchoredAtom3979 Fin15AnchoredAtom3984 Fin15AnchoredAtom3990 Fin15AnchoredAtom4020
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

theorem fin15Anchored_clause32076 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3619 chi ∧
      ¬Fin15AnchoredAtom3620 chi ∧
      ¬Fin15AnchoredAtom3622 chi ∧
      ¬Fin15AnchoredAtom3624 chi ∧
      ¬Fin15AnchoredAtom3631 chi ∧
      ¬Fin15AnchoredAtom3633 chi ∧
      ¬Fin15AnchoredAtom3635 chi ∧
      ¬Fin15AnchoredAtom3637 chi ∧
      ¬Fin15AnchoredAtom3639 chi ∧
      ¬Fin15AnchoredAtom3644 chi ∧
      ¬Fin15AnchoredAtom3652 chi ∧
      ¬Fin15AnchoredAtom3654 chi ∧
      ¬Fin15AnchoredAtom3656 chi ∧
      ¬Fin15AnchoredAtom3658 chi ∧
      ¬Fin15AnchoredAtom3660 chi ∧
      ¬Fin15AnchoredAtom3665 chi ∧
      ¬Fin15AnchoredAtom3683 chi ∧
      ¬Fin15AnchoredAtom3685 chi ∧
      ¬Fin15AnchoredAtom3690 chi ∧
      ¬Fin15AnchoredAtom3696 chi ∧
      ¬Fin15AnchoredAtom3912 chi ∧
      ¬Fin15AnchoredAtom3914 chi ∧
      ¬Fin15AnchoredAtom3916 chi ∧
      ¬Fin15AnchoredAtom3918 chi ∧
      ¬Fin15AnchoredAtom3920 chi ∧
      ¬Fin15AnchoredAtom3925 chi ∧
      ¬Fin15AnchoredAtom3943 chi ∧
      ¬Fin15AnchoredAtom3945 chi ∧
      ¬Fin15AnchoredAtom3950 chi ∧
      ¬Fin15AnchoredAtom3956 chi ∧
      ¬Fin15AnchoredAtom3978 chi ∧
      ¬Fin15AnchoredAtom3980 chi ∧
      ¬Fin15AnchoredAtom3985 chi ∧
      ¬Fin15AnchoredAtom3991 chi ∧
      ¬Fin15AnchoredAtom4021 chi ∧
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
  refine ⟨{2, 3, 6, 7, 9, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22220
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3619 Fin15AnchoredAtom3620 Fin15AnchoredAtom3622
    Fin15AnchoredAtom3624 Fin15AnchoredAtom3631 Fin15AnchoredAtom3633 Fin15AnchoredAtom3635
    Fin15AnchoredAtom3637 Fin15AnchoredAtom3639 Fin15AnchoredAtom3644 Fin15AnchoredAtom3652
    Fin15AnchoredAtom3654 Fin15AnchoredAtom3656 Fin15AnchoredAtom3658 Fin15AnchoredAtom3660
    Fin15AnchoredAtom3665 Fin15AnchoredAtom3683 Fin15AnchoredAtom3685 Fin15AnchoredAtom3690
    Fin15AnchoredAtom3696 Fin15AnchoredAtom3912 Fin15AnchoredAtom3914 Fin15AnchoredAtom3916
    Fin15AnchoredAtom3918 Fin15AnchoredAtom3920 Fin15AnchoredAtom3925 Fin15AnchoredAtom3943
    Fin15AnchoredAtom3945 Fin15AnchoredAtom3950 Fin15AnchoredAtom3956 Fin15AnchoredAtom3978
    Fin15AnchoredAtom3980 Fin15AnchoredAtom3985 Fin15AnchoredAtom3991 Fin15AnchoredAtom4021
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

theorem fin15Anchored_clause32077 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3619 chi ∧
      ¬Fin15AnchoredAtom3620 chi ∧
      ¬Fin15AnchoredAtom3623 chi ∧
      ¬Fin15AnchoredAtom3624 chi ∧
      ¬Fin15AnchoredAtom3631 chi ∧
      ¬Fin15AnchoredAtom3634 chi ∧
      ¬Fin15AnchoredAtom3635 chi ∧
      ¬Fin15AnchoredAtom3638 chi ∧
      ¬Fin15AnchoredAtom3639 chi ∧
      ¬Fin15AnchoredAtom3645 chi ∧
      ¬Fin15AnchoredAtom3652 chi ∧
      ¬Fin15AnchoredAtom3655 chi ∧
      ¬Fin15AnchoredAtom3656 chi ∧
      ¬Fin15AnchoredAtom3659 chi ∧
      ¬Fin15AnchoredAtom3660 chi ∧
      ¬Fin15AnchoredAtom3666 chi ∧
      ¬Fin15AnchoredAtom3684 chi ∧
      ¬Fin15AnchoredAtom3685 chi ∧
      ¬Fin15AnchoredAtom3691 chi ∧
      ¬Fin15AnchoredAtom3697 chi ∧
      ¬Fin15AnchoredAtom3912 chi ∧
      ¬Fin15AnchoredAtom3915 chi ∧
      ¬Fin15AnchoredAtom3916 chi ∧
      ¬Fin15AnchoredAtom3919 chi ∧
      ¬Fin15AnchoredAtom3920 chi ∧
      ¬Fin15AnchoredAtom3926 chi ∧
      ¬Fin15AnchoredAtom3944 chi ∧
      ¬Fin15AnchoredAtom3945 chi ∧
      ¬Fin15AnchoredAtom3951 chi ∧
      ¬Fin15AnchoredAtom3957 chi ∧
      ¬Fin15AnchoredAtom3979 chi ∧
      ¬Fin15AnchoredAtom3980 chi ∧
      ¬Fin15AnchoredAtom3986 chi ∧
      ¬Fin15AnchoredAtom3992 chi ∧
      ¬Fin15AnchoredAtom4022 chi ∧
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
  refine ⟨{2, 3, 6, 7, 9, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26316
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3619 Fin15AnchoredAtom3620 Fin15AnchoredAtom3623
    Fin15AnchoredAtom3624 Fin15AnchoredAtom3631 Fin15AnchoredAtom3634 Fin15AnchoredAtom3635
    Fin15AnchoredAtom3638 Fin15AnchoredAtom3639 Fin15AnchoredAtom3645 Fin15AnchoredAtom3652
    Fin15AnchoredAtom3655 Fin15AnchoredAtom3656 Fin15AnchoredAtom3659 Fin15AnchoredAtom3660
    Fin15AnchoredAtom3666 Fin15AnchoredAtom3684 Fin15AnchoredAtom3685 Fin15AnchoredAtom3691
    Fin15AnchoredAtom3697 Fin15AnchoredAtom3912 Fin15AnchoredAtom3915 Fin15AnchoredAtom3916
    Fin15AnchoredAtom3919 Fin15AnchoredAtom3920 Fin15AnchoredAtom3926 Fin15AnchoredAtom3944
    Fin15AnchoredAtom3945 Fin15AnchoredAtom3951 Fin15AnchoredAtom3957 Fin15AnchoredAtom3979
    Fin15AnchoredAtom3980 Fin15AnchoredAtom3986 Fin15AnchoredAtom3992 Fin15AnchoredAtom4022
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

theorem fin15Anchored_clause32078 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3619 chi ∧
      ¬Fin15AnchoredAtom3622 chi ∧
      ¬Fin15AnchoredAtom3623 chi ∧
      ¬Fin15AnchoredAtom3624 chi ∧
      ¬Fin15AnchoredAtom3633 chi ∧
      ¬Fin15AnchoredAtom3634 chi ∧
      ¬Fin15AnchoredAtom3635 chi ∧
      ¬Fin15AnchoredAtom3643 chi ∧
      ¬Fin15AnchoredAtom3644 chi ∧
      ¬Fin15AnchoredAtom3645 chi ∧
      ¬Fin15AnchoredAtom3654 chi ∧
      ¬Fin15AnchoredAtom3655 chi ∧
      ¬Fin15AnchoredAtom3656 chi ∧
      ¬Fin15AnchoredAtom3664 chi ∧
      ¬Fin15AnchoredAtom3665 chi ∧
      ¬Fin15AnchoredAtom3666 chi ∧
      ¬Fin15AnchoredAtom3689 chi ∧
      ¬Fin15AnchoredAtom3690 chi ∧
      ¬Fin15AnchoredAtom3691 chi ∧
      ¬Fin15AnchoredAtom3701 chi ∧
      ¬Fin15AnchoredAtom3914 chi ∧
      ¬Fin15AnchoredAtom3915 chi ∧
      ¬Fin15AnchoredAtom3916 chi ∧
      ¬Fin15AnchoredAtom3924 chi ∧
      ¬Fin15AnchoredAtom3925 chi ∧
      ¬Fin15AnchoredAtom3926 chi ∧
      ¬Fin15AnchoredAtom3949 chi ∧
      ¬Fin15AnchoredAtom3950 chi ∧
      ¬Fin15AnchoredAtom3951 chi ∧
      ¬Fin15AnchoredAtom3961 chi ∧
      ¬Fin15AnchoredAtom3984 chi ∧
      ¬Fin15AnchoredAtom3985 chi ∧
      ¬Fin15AnchoredAtom3986 chi ∧
      ¬Fin15AnchoredAtom3996 chi ∧
      ¬Fin15AnchoredAtom4026 chi ∧
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
  refine ⟨{2, 3, 6, 7, 9, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29388
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3619 Fin15AnchoredAtom3622 Fin15AnchoredAtom3623
    Fin15AnchoredAtom3624 Fin15AnchoredAtom3633 Fin15AnchoredAtom3634 Fin15AnchoredAtom3635
    Fin15AnchoredAtom3643 Fin15AnchoredAtom3644 Fin15AnchoredAtom3645 Fin15AnchoredAtom3654
    Fin15AnchoredAtom3655 Fin15AnchoredAtom3656 Fin15AnchoredAtom3664 Fin15AnchoredAtom3665
    Fin15AnchoredAtom3666 Fin15AnchoredAtom3689 Fin15AnchoredAtom3690 Fin15AnchoredAtom3691
    Fin15AnchoredAtom3701 Fin15AnchoredAtom3914 Fin15AnchoredAtom3915 Fin15AnchoredAtom3916
    Fin15AnchoredAtom3924 Fin15AnchoredAtom3925 Fin15AnchoredAtom3926 Fin15AnchoredAtom3949
    Fin15AnchoredAtom3950 Fin15AnchoredAtom3951 Fin15AnchoredAtom3961 Fin15AnchoredAtom3984
    Fin15AnchoredAtom3985 Fin15AnchoredAtom3986 Fin15AnchoredAtom3996 Fin15AnchoredAtom4026
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

theorem fin15Anchored_clause32079 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3620 chi ∧
      ¬Fin15AnchoredAtom3622 chi ∧
      ¬Fin15AnchoredAtom3623 chi ∧
      ¬Fin15AnchoredAtom3624 chi ∧
      ¬Fin15AnchoredAtom3637 chi ∧
      ¬Fin15AnchoredAtom3638 chi ∧
      ¬Fin15AnchoredAtom3639 chi ∧
      ¬Fin15AnchoredAtom3643 chi ∧
      ¬Fin15AnchoredAtom3644 chi ∧
      ¬Fin15AnchoredAtom3645 chi ∧
      ¬Fin15AnchoredAtom3658 chi ∧
      ¬Fin15AnchoredAtom3659 chi ∧
      ¬Fin15AnchoredAtom3660 chi ∧
      ¬Fin15AnchoredAtom3664 chi ∧
      ¬Fin15AnchoredAtom3665 chi ∧
      ¬Fin15AnchoredAtom3666 chi ∧
      ¬Fin15AnchoredAtom3695 chi ∧
      ¬Fin15AnchoredAtom3696 chi ∧
      ¬Fin15AnchoredAtom3697 chi ∧
      ¬Fin15AnchoredAtom3701 chi ∧
      ¬Fin15AnchoredAtom3918 chi ∧
      ¬Fin15AnchoredAtom3919 chi ∧
      ¬Fin15AnchoredAtom3920 chi ∧
      ¬Fin15AnchoredAtom3924 chi ∧
      ¬Fin15AnchoredAtom3925 chi ∧
      ¬Fin15AnchoredAtom3926 chi ∧
      ¬Fin15AnchoredAtom3955 chi ∧
      ¬Fin15AnchoredAtom3956 chi ∧
      ¬Fin15AnchoredAtom3957 chi ∧
      ¬Fin15AnchoredAtom3961 chi ∧
      ¬Fin15AnchoredAtom3990 chi ∧
      ¬Fin15AnchoredAtom3991 chi ∧
      ¬Fin15AnchoredAtom3992 chi ∧
      ¬Fin15AnchoredAtom3996 chi ∧
      ¬Fin15AnchoredAtom4030 chi ∧
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
  refine ⟨{2, 3, 6, 7, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29900
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3620 Fin15AnchoredAtom3622 Fin15AnchoredAtom3623
    Fin15AnchoredAtom3624 Fin15AnchoredAtom3637 Fin15AnchoredAtom3638 Fin15AnchoredAtom3639
    Fin15AnchoredAtom3643 Fin15AnchoredAtom3644 Fin15AnchoredAtom3645 Fin15AnchoredAtom3658
    Fin15AnchoredAtom3659 Fin15AnchoredAtom3660 Fin15AnchoredAtom3664 Fin15AnchoredAtom3665
    Fin15AnchoredAtom3666 Fin15AnchoredAtom3695 Fin15AnchoredAtom3696 Fin15AnchoredAtom3697
    Fin15AnchoredAtom3701 Fin15AnchoredAtom3918 Fin15AnchoredAtom3919 Fin15AnchoredAtom3920
    Fin15AnchoredAtom3924 Fin15AnchoredAtom3925 Fin15AnchoredAtom3926 Fin15AnchoredAtom3955
    Fin15AnchoredAtom3956 Fin15AnchoredAtom3957 Fin15AnchoredAtom3961 Fin15AnchoredAtom3990
    Fin15AnchoredAtom3991 Fin15AnchoredAtom3992 Fin15AnchoredAtom3996 Fin15AnchoredAtom4030
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

theorem fin15Anchored_clause32080 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3631 chi ∧
      ¬Fin15AnchoredAtom3633 chi ∧
      ¬Fin15AnchoredAtom3634 chi ∧
      ¬Fin15AnchoredAtom3635 chi ∧
      ¬Fin15AnchoredAtom3637 chi ∧
      ¬Fin15AnchoredAtom3638 chi ∧
      ¬Fin15AnchoredAtom3639 chi ∧
      ¬Fin15AnchoredAtom3643 chi ∧
      ¬Fin15AnchoredAtom3644 chi ∧
      ¬Fin15AnchoredAtom3645 chi ∧
      ¬Fin15AnchoredAtom3683 chi ∧
      ¬Fin15AnchoredAtom3684 chi ∧
      ¬Fin15AnchoredAtom3685 chi ∧
      ¬Fin15AnchoredAtom3689 chi ∧
      ¬Fin15AnchoredAtom3690 chi ∧
      ¬Fin15AnchoredAtom3691 chi ∧
      ¬Fin15AnchoredAtom3695 chi ∧
      ¬Fin15AnchoredAtom3696 chi ∧
      ¬Fin15AnchoredAtom3697 chi ∧
      ¬Fin15AnchoredAtom3701 chi ∧
      ¬Fin15AnchoredAtom3943 chi ∧
      ¬Fin15AnchoredAtom3944 chi ∧
      ¬Fin15AnchoredAtom3945 chi ∧
      ¬Fin15AnchoredAtom3949 chi ∧
      ¬Fin15AnchoredAtom3950 chi ∧
      ¬Fin15AnchoredAtom3951 chi ∧
      ¬Fin15AnchoredAtom3955 chi ∧
      ¬Fin15AnchoredAtom3956 chi ∧
      ¬Fin15AnchoredAtom3957 chi ∧
      ¬Fin15AnchoredAtom3961 chi ∧
      ¬Fin15AnchoredAtom4020 chi ∧
      ¬Fin15AnchoredAtom4021 chi ∧
      ¬Fin15AnchoredAtom4022 chi ∧
      ¬Fin15AnchoredAtom4026 chi ∧
      ¬Fin15AnchoredAtom4030 chi ∧
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
  refine ⟨{2, 3, 6, 9, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask30284
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3631 Fin15AnchoredAtom3633 Fin15AnchoredAtom3634
    Fin15AnchoredAtom3635 Fin15AnchoredAtom3637 Fin15AnchoredAtom3638 Fin15AnchoredAtom3639
    Fin15AnchoredAtom3643 Fin15AnchoredAtom3644 Fin15AnchoredAtom3645 Fin15AnchoredAtom3683
    Fin15AnchoredAtom3684 Fin15AnchoredAtom3685 Fin15AnchoredAtom3689 Fin15AnchoredAtom3690
    Fin15AnchoredAtom3691 Fin15AnchoredAtom3695 Fin15AnchoredAtom3696 Fin15AnchoredAtom3697
    Fin15AnchoredAtom3701 Fin15AnchoredAtom3943 Fin15AnchoredAtom3944 Fin15AnchoredAtom3945
    Fin15AnchoredAtom3949 Fin15AnchoredAtom3950 Fin15AnchoredAtom3951 Fin15AnchoredAtom3955
    Fin15AnchoredAtom3956 Fin15AnchoredAtom3957 Fin15AnchoredAtom3961 Fin15AnchoredAtom4020
    Fin15AnchoredAtom4021 Fin15AnchoredAtom4022 Fin15AnchoredAtom4026 Fin15AnchoredAtom4030
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

theorem fin15Anchored_clause32081 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3652 chi ∧
      ¬Fin15AnchoredAtom3654 chi ∧
      ¬Fin15AnchoredAtom3655 chi ∧
      ¬Fin15AnchoredAtom3656 chi ∧
      ¬Fin15AnchoredAtom3658 chi ∧
      ¬Fin15AnchoredAtom3659 chi ∧
      ¬Fin15AnchoredAtom3660 chi ∧
      ¬Fin15AnchoredAtom3664 chi ∧
      ¬Fin15AnchoredAtom3665 chi ∧
      ¬Fin15AnchoredAtom3666 chi ∧
      ¬Fin15AnchoredAtom3683 chi ∧
      ¬Fin15AnchoredAtom3684 chi ∧
      ¬Fin15AnchoredAtom3685 chi ∧
      ¬Fin15AnchoredAtom3689 chi ∧
      ¬Fin15AnchoredAtom3690 chi ∧
      ¬Fin15AnchoredAtom3691 chi ∧
      ¬Fin15AnchoredAtom3695 chi ∧
      ¬Fin15AnchoredAtom3696 chi ∧
      ¬Fin15AnchoredAtom3697 chi ∧
      ¬Fin15AnchoredAtom3701 chi ∧
      ¬Fin15AnchoredAtom3978 chi ∧
      ¬Fin15AnchoredAtom3979 chi ∧
      ¬Fin15AnchoredAtom3980 chi ∧
      ¬Fin15AnchoredAtom3984 chi ∧
      ¬Fin15AnchoredAtom3985 chi ∧
      ¬Fin15AnchoredAtom3986 chi ∧
      ¬Fin15AnchoredAtom3990 chi ∧
      ¬Fin15AnchoredAtom3991 chi ∧
      ¬Fin15AnchoredAtom3992 chi ∧
      ¬Fin15AnchoredAtom3996 chi ∧
      ¬Fin15AnchoredAtom4020 chi ∧
      ¬Fin15AnchoredAtom4021 chi ∧
      ¬Fin15AnchoredAtom4022 chi ∧
      ¬Fin15AnchoredAtom4026 chi ∧
      ¬Fin15AnchoredAtom4030 chi ∧
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
  refine ⟨{2, 3, 7, 9, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask30348
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3652 Fin15AnchoredAtom3654 Fin15AnchoredAtom3655
    Fin15AnchoredAtom3656 Fin15AnchoredAtom3658 Fin15AnchoredAtom3659 Fin15AnchoredAtom3660
    Fin15AnchoredAtom3664 Fin15AnchoredAtom3665 Fin15AnchoredAtom3666 Fin15AnchoredAtom3683
    Fin15AnchoredAtom3684 Fin15AnchoredAtom3685 Fin15AnchoredAtom3689 Fin15AnchoredAtom3690
    Fin15AnchoredAtom3691 Fin15AnchoredAtom3695 Fin15AnchoredAtom3696 Fin15AnchoredAtom3697
    Fin15AnchoredAtom3701 Fin15AnchoredAtom3978 Fin15AnchoredAtom3979 Fin15AnchoredAtom3980
    Fin15AnchoredAtom3984 Fin15AnchoredAtom3985 Fin15AnchoredAtom3986 Fin15AnchoredAtom3990
    Fin15AnchoredAtom3991 Fin15AnchoredAtom3992 Fin15AnchoredAtom3996 Fin15AnchoredAtom4020
    Fin15AnchoredAtom4021 Fin15AnchoredAtom4022 Fin15AnchoredAtom4026 Fin15AnchoredAtom4030
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

theorem fin15Anchored_clause32082 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3702 chi ∧
      ¬Fin15AnchoredAtom3704 chi ∧
      ¬Fin15AnchoredAtom3705 chi ∧
      ¬Fin15AnchoredAtom3706 chi ∧
      ¬Fin15AnchoredAtom3711 chi ∧
      ¬Fin15AnchoredAtom3712 chi ∧
      ¬Fin15AnchoredAtom3713 chi ∧
      ¬Fin15AnchoredAtom3723 chi ∧
      ¬Fin15AnchoredAtom3724 chi ∧
      ¬Fin15AnchoredAtom3728 chi ∧
      ¬Fin15AnchoredAtom3739 chi ∧
      ¬Fin15AnchoredAtom3740 chi ∧
      ¬Fin15AnchoredAtom3741 chi ∧
      ¬Fin15AnchoredAtom3751 chi ∧
      ¬Fin15AnchoredAtom3752 chi ∧
      ¬Fin15AnchoredAtom3756 chi ∧
      ¬Fin15AnchoredAtom3772 chi ∧
      ¬Fin15AnchoredAtom3773 chi ∧
      ¬Fin15AnchoredAtom3777 chi ∧
      ¬Fin15AnchoredAtom3802 chi ∧
      ¬Fin15AnchoredAtom3823 chi ∧
      ¬Fin15AnchoredAtom3824 chi ∧
      ¬Fin15AnchoredAtom3825 chi ∧
      ¬Fin15AnchoredAtom3835 chi ∧
      ¬Fin15AnchoredAtom3836 chi ∧
      ¬Fin15AnchoredAtom3840 chi ∧
      ¬Fin15AnchoredAtom3856 chi ∧
      ¬Fin15AnchoredAtom3857 chi ∧
      ¬Fin15AnchoredAtom3861 chi ∧
      ¬Fin15AnchoredAtom3886 chi ∧
      ¬Fin15AnchoredAtom3912 chi ∧
      ¬Fin15AnchoredAtom3913 chi ∧
      ¬Fin15AnchoredAtom3917 chi ∧
      ¬Fin15AnchoredAtom3942 chi ∧
      ¬Fin15AnchoredAtom3977 chi ∧
      ¬Fin15AnchoredAtom4363 chi ∧
      ¬Fin15AnchoredAtom4364 chi ∧
      ¬Fin15AnchoredAtom4365 chi ∧
      ¬Fin15AnchoredAtom4375 chi ∧
      ¬Fin15AnchoredAtom4376 chi ∧
      ¬Fin15AnchoredAtom4380 chi ∧
      ¬Fin15AnchoredAtom4396 chi ∧
      ¬Fin15AnchoredAtom4397 chi ∧
      ¬Fin15AnchoredAtom4401 chi ∧
      ¬Fin15AnchoredAtom4426 chi ∧
      ¬Fin15AnchoredAtom4452 chi ∧
      ¬Fin15AnchoredAtom4453 chi ∧
      ¬Fin15AnchoredAtom4457 chi ∧
      ¬Fin15AnchoredAtom4482 chi ∧
      ¬Fin15AnchoredAtom4517 chi ∧
      ¬Fin15AnchoredAtom4578 chi ∧
      ¬Fin15AnchoredAtom4579 chi ∧
      ¬Fin15AnchoredAtom4583 chi ∧
      ¬Fin15AnchoredAtom4608 chi ∧
      ¬Fin15AnchoredAtom4643 chi ∧
      ¬Fin15AnchoredAtom4713 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 4, 5, 6, 7, 9, 10, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask03828
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3702 Fin15AnchoredAtom3704 Fin15AnchoredAtom3705
    Fin15AnchoredAtom3706 Fin15AnchoredAtom3711 Fin15AnchoredAtom3712 Fin15AnchoredAtom3713
    Fin15AnchoredAtom3723 Fin15AnchoredAtom3724 Fin15AnchoredAtom3728 Fin15AnchoredAtom3739
    Fin15AnchoredAtom3740 Fin15AnchoredAtom3741 Fin15AnchoredAtom3751 Fin15AnchoredAtom3752
    Fin15AnchoredAtom3756 Fin15AnchoredAtom3772 Fin15AnchoredAtom3773 Fin15AnchoredAtom3777
    Fin15AnchoredAtom3802 Fin15AnchoredAtom3823 Fin15AnchoredAtom3824 Fin15AnchoredAtom3825
    Fin15AnchoredAtom3835 Fin15AnchoredAtom3836 Fin15AnchoredAtom3840 Fin15AnchoredAtom3856
    Fin15AnchoredAtom3857 Fin15AnchoredAtom3861 Fin15AnchoredAtom3886 Fin15AnchoredAtom3912
    Fin15AnchoredAtom3913 Fin15AnchoredAtom3917 Fin15AnchoredAtom3942 Fin15AnchoredAtom3977
    Fin15AnchoredAtom4363 Fin15AnchoredAtom4364 Fin15AnchoredAtom4365 Fin15AnchoredAtom4375
    Fin15AnchoredAtom4376 Fin15AnchoredAtom4380 Fin15AnchoredAtom4396 Fin15AnchoredAtom4397
    Fin15AnchoredAtom4401 Fin15AnchoredAtom4426 Fin15AnchoredAtom4452 Fin15AnchoredAtom4453
    Fin15AnchoredAtom4457 Fin15AnchoredAtom4482 Fin15AnchoredAtom4517 Fin15AnchoredAtom4578
    Fin15AnchoredAtom4579 Fin15AnchoredAtom4583 Fin15AnchoredAtom4608 Fin15AnchoredAtom4643
    Fin15AnchoredAtom4713 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause32083 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3702 chi ∧
      ¬Fin15AnchoredAtom3704 chi ∧
      ¬Fin15AnchoredAtom3705 chi ∧
      ¬Fin15AnchoredAtom3707 chi ∧
      ¬Fin15AnchoredAtom3711 chi ∧
      ¬Fin15AnchoredAtom3712 chi ∧
      ¬Fin15AnchoredAtom3714 chi ∧
      ¬Fin15AnchoredAtom3723 chi ∧
      ¬Fin15AnchoredAtom3725 chi ∧
      ¬Fin15AnchoredAtom3729 chi ∧
      ¬Fin15AnchoredAtom3739 chi ∧
      ¬Fin15AnchoredAtom3740 chi ∧
      ¬Fin15AnchoredAtom3742 chi ∧
      ¬Fin15AnchoredAtom3751 chi ∧
      ¬Fin15AnchoredAtom3753 chi ∧
      ¬Fin15AnchoredAtom3757 chi ∧
      ¬Fin15AnchoredAtom3772 chi ∧
      ¬Fin15AnchoredAtom3774 chi ∧
      ¬Fin15AnchoredAtom3778 chi ∧
      ¬Fin15AnchoredAtom3803 chi ∧
      ¬Fin15AnchoredAtom3823 chi ∧
      ¬Fin15AnchoredAtom3824 chi ∧
      ¬Fin15AnchoredAtom3826 chi ∧
      ¬Fin15AnchoredAtom3835 chi ∧
      ¬Fin15AnchoredAtom3837 chi ∧
      ¬Fin15AnchoredAtom3841 chi ∧
      ¬Fin15AnchoredAtom3856 chi ∧
      ¬Fin15AnchoredAtom3858 chi ∧
      ¬Fin15AnchoredAtom3862 chi ∧
      ¬Fin15AnchoredAtom3887 chi ∧
      ¬Fin15AnchoredAtom3912 chi ∧
      ¬Fin15AnchoredAtom3914 chi ∧
      ¬Fin15AnchoredAtom3918 chi ∧
      ¬Fin15AnchoredAtom3943 chi ∧
      ¬Fin15AnchoredAtom3978 chi ∧
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
  refine ⟨{2, 4, 5, 6, 7, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05876
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3702 Fin15AnchoredAtom3704 Fin15AnchoredAtom3705
    Fin15AnchoredAtom3707 Fin15AnchoredAtom3711 Fin15AnchoredAtom3712 Fin15AnchoredAtom3714
    Fin15AnchoredAtom3723 Fin15AnchoredAtom3725 Fin15AnchoredAtom3729 Fin15AnchoredAtom3739
    Fin15AnchoredAtom3740 Fin15AnchoredAtom3742 Fin15AnchoredAtom3751 Fin15AnchoredAtom3753
    Fin15AnchoredAtom3757 Fin15AnchoredAtom3772 Fin15AnchoredAtom3774 Fin15AnchoredAtom3778
    Fin15AnchoredAtom3803 Fin15AnchoredAtom3823 Fin15AnchoredAtom3824 Fin15AnchoredAtom3826
    Fin15AnchoredAtom3835 Fin15AnchoredAtom3837 Fin15AnchoredAtom3841 Fin15AnchoredAtom3856
    Fin15AnchoredAtom3858 Fin15AnchoredAtom3862 Fin15AnchoredAtom3887 Fin15AnchoredAtom3912
    Fin15AnchoredAtom3914 Fin15AnchoredAtom3918 Fin15AnchoredAtom3943 Fin15AnchoredAtom3978
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

theorem fin15Anchored_clause32084 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3702 chi ∧
      ¬Fin15AnchoredAtom3704 chi ∧
      ¬Fin15AnchoredAtom3705 chi ∧
      ¬Fin15AnchoredAtom3708 chi ∧
      ¬Fin15AnchoredAtom3711 chi ∧
      ¬Fin15AnchoredAtom3712 chi ∧
      ¬Fin15AnchoredAtom3715 chi ∧
      ¬Fin15AnchoredAtom3723 chi ∧
      ¬Fin15AnchoredAtom3726 chi ∧
      ¬Fin15AnchoredAtom3730 chi ∧
      ¬Fin15AnchoredAtom3739 chi ∧
      ¬Fin15AnchoredAtom3740 chi ∧
      ¬Fin15AnchoredAtom3743 chi ∧
      ¬Fin15AnchoredAtom3751 chi ∧
      ¬Fin15AnchoredAtom3754 chi ∧
      ¬Fin15AnchoredAtom3758 chi ∧
      ¬Fin15AnchoredAtom3772 chi ∧
      ¬Fin15AnchoredAtom3775 chi ∧
      ¬Fin15AnchoredAtom3779 chi ∧
      ¬Fin15AnchoredAtom3804 chi ∧
      ¬Fin15AnchoredAtom3823 chi ∧
      ¬Fin15AnchoredAtom3824 chi ∧
      ¬Fin15AnchoredAtom3827 chi ∧
      ¬Fin15AnchoredAtom3835 chi ∧
      ¬Fin15AnchoredAtom3838 chi ∧
      ¬Fin15AnchoredAtom3842 chi ∧
      ¬Fin15AnchoredAtom3856 chi ∧
      ¬Fin15AnchoredAtom3859 chi ∧
      ¬Fin15AnchoredAtom3863 chi ∧
      ¬Fin15AnchoredAtom3888 chi ∧
      ¬Fin15AnchoredAtom3912 chi ∧
      ¬Fin15AnchoredAtom3915 chi ∧
      ¬Fin15AnchoredAtom3919 chi ∧
      ¬Fin15AnchoredAtom3944 chi ∧
      ¬Fin15AnchoredAtom3979 chi ∧
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
  refine ⟨{2, 4, 5, 6, 7, 9, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09972
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3702 Fin15AnchoredAtom3704 Fin15AnchoredAtom3705
    Fin15AnchoredAtom3708 Fin15AnchoredAtom3711 Fin15AnchoredAtom3712 Fin15AnchoredAtom3715
    Fin15AnchoredAtom3723 Fin15AnchoredAtom3726 Fin15AnchoredAtom3730 Fin15AnchoredAtom3739
    Fin15AnchoredAtom3740 Fin15AnchoredAtom3743 Fin15AnchoredAtom3751 Fin15AnchoredAtom3754
    Fin15AnchoredAtom3758 Fin15AnchoredAtom3772 Fin15AnchoredAtom3775 Fin15AnchoredAtom3779
    Fin15AnchoredAtom3804 Fin15AnchoredAtom3823 Fin15AnchoredAtom3824 Fin15AnchoredAtom3827
    Fin15AnchoredAtom3835 Fin15AnchoredAtom3838 Fin15AnchoredAtom3842 Fin15AnchoredAtom3856
    Fin15AnchoredAtom3859 Fin15AnchoredAtom3863 Fin15AnchoredAtom3888 Fin15AnchoredAtom3912
    Fin15AnchoredAtom3915 Fin15AnchoredAtom3919 Fin15AnchoredAtom3944 Fin15AnchoredAtom3979
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

theorem fin15Anchored_clause32085 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3702 chi ∧
      ¬Fin15AnchoredAtom3704 chi ∧
      ¬Fin15AnchoredAtom3705 chi ∧
      ¬Fin15AnchoredAtom3709 chi ∧
      ¬Fin15AnchoredAtom3711 chi ∧
      ¬Fin15AnchoredAtom3712 chi ∧
      ¬Fin15AnchoredAtom3716 chi ∧
      ¬Fin15AnchoredAtom3723 chi ∧
      ¬Fin15AnchoredAtom3727 chi ∧
      ¬Fin15AnchoredAtom3731 chi ∧
      ¬Fin15AnchoredAtom3739 chi ∧
      ¬Fin15AnchoredAtom3740 chi ∧
      ¬Fin15AnchoredAtom3744 chi ∧
      ¬Fin15AnchoredAtom3751 chi ∧
      ¬Fin15AnchoredAtom3755 chi ∧
      ¬Fin15AnchoredAtom3759 chi ∧
      ¬Fin15AnchoredAtom3772 chi ∧
      ¬Fin15AnchoredAtom3776 chi ∧
      ¬Fin15AnchoredAtom3780 chi ∧
      ¬Fin15AnchoredAtom3805 chi ∧
      ¬Fin15AnchoredAtom3823 chi ∧
      ¬Fin15AnchoredAtom3824 chi ∧
      ¬Fin15AnchoredAtom3828 chi ∧
      ¬Fin15AnchoredAtom3835 chi ∧
      ¬Fin15AnchoredAtom3839 chi ∧
      ¬Fin15AnchoredAtom3843 chi ∧
      ¬Fin15AnchoredAtom3856 chi ∧
      ¬Fin15AnchoredAtom3860 chi ∧
      ¬Fin15AnchoredAtom3864 chi ∧
      ¬Fin15AnchoredAtom3889 chi ∧
      ¬Fin15AnchoredAtom3912 chi ∧
      ¬Fin15AnchoredAtom3916 chi ∧
      ¬Fin15AnchoredAtom3920 chi ∧
      ¬Fin15AnchoredAtom3945 chi ∧
      ¬Fin15AnchoredAtom3980 chi ∧
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
  refine ⟨{2, 4, 5, 6, 7, 9, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask18164
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3702 Fin15AnchoredAtom3704 Fin15AnchoredAtom3705
    Fin15AnchoredAtom3709 Fin15AnchoredAtom3711 Fin15AnchoredAtom3712 Fin15AnchoredAtom3716
    Fin15AnchoredAtom3723 Fin15AnchoredAtom3727 Fin15AnchoredAtom3731 Fin15AnchoredAtom3739
    Fin15AnchoredAtom3740 Fin15AnchoredAtom3744 Fin15AnchoredAtom3751 Fin15AnchoredAtom3755
    Fin15AnchoredAtom3759 Fin15AnchoredAtom3772 Fin15AnchoredAtom3776 Fin15AnchoredAtom3780
    Fin15AnchoredAtom3805 Fin15AnchoredAtom3823 Fin15AnchoredAtom3824 Fin15AnchoredAtom3828
    Fin15AnchoredAtom3835 Fin15AnchoredAtom3839 Fin15AnchoredAtom3843 Fin15AnchoredAtom3856
    Fin15AnchoredAtom3860 Fin15AnchoredAtom3864 Fin15AnchoredAtom3889 Fin15AnchoredAtom3912
    Fin15AnchoredAtom3916 Fin15AnchoredAtom3920 Fin15AnchoredAtom3945 Fin15AnchoredAtom3980
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

theorem fin15Anchored_clause32086 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3702 chi ∧
      ¬Fin15AnchoredAtom3704 chi ∧
      ¬Fin15AnchoredAtom3707 chi ∧
      ¬Fin15AnchoredAtom3708 chi ∧
      ¬Fin15AnchoredAtom3711 chi ∧
      ¬Fin15AnchoredAtom3714 chi ∧
      ¬Fin15AnchoredAtom3715 chi ∧
      ¬Fin15AnchoredAtom3725 chi ∧
      ¬Fin15AnchoredAtom3726 chi ∧
      ¬Fin15AnchoredAtom3735 chi ∧
      ¬Fin15AnchoredAtom3739 chi ∧
      ¬Fin15AnchoredAtom3742 chi ∧
      ¬Fin15AnchoredAtom3743 chi ∧
      ¬Fin15AnchoredAtom3753 chi ∧
      ¬Fin15AnchoredAtom3754 chi ∧
      ¬Fin15AnchoredAtom3763 chi ∧
      ¬Fin15AnchoredAtom3774 chi ∧
      ¬Fin15AnchoredAtom3775 chi ∧
      ¬Fin15AnchoredAtom3784 chi ∧
      ¬Fin15AnchoredAtom3809 chi ∧
      ¬Fin15AnchoredAtom3823 chi ∧
      ¬Fin15AnchoredAtom3826 chi ∧
      ¬Fin15AnchoredAtom3827 chi ∧
      ¬Fin15AnchoredAtom3837 chi ∧
      ¬Fin15AnchoredAtom3838 chi ∧
      ¬Fin15AnchoredAtom3847 chi ∧
      ¬Fin15AnchoredAtom3858 chi ∧
      ¬Fin15AnchoredAtom3859 chi ∧
      ¬Fin15AnchoredAtom3868 chi ∧
      ¬Fin15AnchoredAtom3893 chi ∧
      ¬Fin15AnchoredAtom3914 chi ∧
      ¬Fin15AnchoredAtom3915 chi ∧
      ¬Fin15AnchoredAtom3924 chi ∧
      ¬Fin15AnchoredAtom3949 chi ∧
      ¬Fin15AnchoredAtom3984 chi ∧
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
  refine ⟨{2, 4, 5, 6, 7, 9, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13044
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3702 Fin15AnchoredAtom3704 Fin15AnchoredAtom3707
    Fin15AnchoredAtom3708 Fin15AnchoredAtom3711 Fin15AnchoredAtom3714 Fin15AnchoredAtom3715
    Fin15AnchoredAtom3725 Fin15AnchoredAtom3726 Fin15AnchoredAtom3735 Fin15AnchoredAtom3739
    Fin15AnchoredAtom3742 Fin15AnchoredAtom3743 Fin15AnchoredAtom3753 Fin15AnchoredAtom3754
    Fin15AnchoredAtom3763 Fin15AnchoredAtom3774 Fin15AnchoredAtom3775 Fin15AnchoredAtom3784
    Fin15AnchoredAtom3809 Fin15AnchoredAtom3823 Fin15AnchoredAtom3826 Fin15AnchoredAtom3827
    Fin15AnchoredAtom3837 Fin15AnchoredAtom3838 Fin15AnchoredAtom3847 Fin15AnchoredAtom3858
    Fin15AnchoredAtom3859 Fin15AnchoredAtom3868 Fin15AnchoredAtom3893 Fin15AnchoredAtom3914
    Fin15AnchoredAtom3915 Fin15AnchoredAtom3924 Fin15AnchoredAtom3949 Fin15AnchoredAtom3984
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

theorem fin15Anchored_clause32087 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3702 chi ∧
      ¬Fin15AnchoredAtom3704 chi ∧
      ¬Fin15AnchoredAtom3707 chi ∧
      ¬Fin15AnchoredAtom3709 chi ∧
      ¬Fin15AnchoredAtom3711 chi ∧
      ¬Fin15AnchoredAtom3714 chi ∧
      ¬Fin15AnchoredAtom3716 chi ∧
      ¬Fin15AnchoredAtom3725 chi ∧
      ¬Fin15AnchoredAtom3727 chi ∧
      ¬Fin15AnchoredAtom3736 chi ∧
      ¬Fin15AnchoredAtom3739 chi ∧
      ¬Fin15AnchoredAtom3742 chi ∧
      ¬Fin15AnchoredAtom3744 chi ∧
      ¬Fin15AnchoredAtom3753 chi ∧
      ¬Fin15AnchoredAtom3755 chi ∧
      ¬Fin15AnchoredAtom3764 chi ∧
      ¬Fin15AnchoredAtom3774 chi ∧
      ¬Fin15AnchoredAtom3776 chi ∧
      ¬Fin15AnchoredAtom3785 chi ∧
      ¬Fin15AnchoredAtom3810 chi ∧
      ¬Fin15AnchoredAtom3823 chi ∧
      ¬Fin15AnchoredAtom3826 chi ∧
      ¬Fin15AnchoredAtom3828 chi ∧
      ¬Fin15AnchoredAtom3837 chi ∧
      ¬Fin15AnchoredAtom3839 chi ∧
      ¬Fin15AnchoredAtom3848 chi ∧
      ¬Fin15AnchoredAtom3858 chi ∧
      ¬Fin15AnchoredAtom3860 chi ∧
      ¬Fin15AnchoredAtom3869 chi ∧
      ¬Fin15AnchoredAtom3894 chi ∧
      ¬Fin15AnchoredAtom3914 chi ∧
      ¬Fin15AnchoredAtom3916 chi ∧
      ¬Fin15AnchoredAtom3925 chi ∧
      ¬Fin15AnchoredAtom3950 chi ∧
      ¬Fin15AnchoredAtom3985 chi ∧
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
  refine ⟨{2, 4, 5, 6, 7, 9, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21236
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3702 Fin15AnchoredAtom3704 Fin15AnchoredAtom3707
    Fin15AnchoredAtom3709 Fin15AnchoredAtom3711 Fin15AnchoredAtom3714 Fin15AnchoredAtom3716
    Fin15AnchoredAtom3725 Fin15AnchoredAtom3727 Fin15AnchoredAtom3736 Fin15AnchoredAtom3739
    Fin15AnchoredAtom3742 Fin15AnchoredAtom3744 Fin15AnchoredAtom3753 Fin15AnchoredAtom3755
    Fin15AnchoredAtom3764 Fin15AnchoredAtom3774 Fin15AnchoredAtom3776 Fin15AnchoredAtom3785
    Fin15AnchoredAtom3810 Fin15AnchoredAtom3823 Fin15AnchoredAtom3826 Fin15AnchoredAtom3828
    Fin15AnchoredAtom3837 Fin15AnchoredAtom3839 Fin15AnchoredAtom3848 Fin15AnchoredAtom3858
    Fin15AnchoredAtom3860 Fin15AnchoredAtom3869 Fin15AnchoredAtom3894 Fin15AnchoredAtom3914
    Fin15AnchoredAtom3916 Fin15AnchoredAtom3925 Fin15AnchoredAtom3950 Fin15AnchoredAtom3985
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

theorem fin15Anchored_clause32088 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3702 chi ∧
      ¬Fin15AnchoredAtom3704 chi ∧
      ¬Fin15AnchoredAtom3708 chi ∧
      ¬Fin15AnchoredAtom3709 chi ∧
      ¬Fin15AnchoredAtom3711 chi ∧
      ¬Fin15AnchoredAtom3715 chi ∧
      ¬Fin15AnchoredAtom3716 chi ∧
      ¬Fin15AnchoredAtom3726 chi ∧
      ¬Fin15AnchoredAtom3727 chi ∧
      ¬Fin15AnchoredAtom3737 chi ∧
      ¬Fin15AnchoredAtom3739 chi ∧
      ¬Fin15AnchoredAtom3743 chi ∧
      ¬Fin15AnchoredAtom3744 chi ∧
      ¬Fin15AnchoredAtom3754 chi ∧
      ¬Fin15AnchoredAtom3755 chi ∧
      ¬Fin15AnchoredAtom3765 chi ∧
      ¬Fin15AnchoredAtom3775 chi ∧
      ¬Fin15AnchoredAtom3776 chi ∧
      ¬Fin15AnchoredAtom3786 chi ∧
      ¬Fin15AnchoredAtom3811 chi ∧
      ¬Fin15AnchoredAtom3823 chi ∧
      ¬Fin15AnchoredAtom3827 chi ∧
      ¬Fin15AnchoredAtom3828 chi ∧
      ¬Fin15AnchoredAtom3838 chi ∧
      ¬Fin15AnchoredAtom3839 chi ∧
      ¬Fin15AnchoredAtom3849 chi ∧
      ¬Fin15AnchoredAtom3859 chi ∧
      ¬Fin15AnchoredAtom3860 chi ∧
      ¬Fin15AnchoredAtom3870 chi ∧
      ¬Fin15AnchoredAtom3895 chi ∧
      ¬Fin15AnchoredAtom3915 chi ∧
      ¬Fin15AnchoredAtom3916 chi ∧
      ¬Fin15AnchoredAtom3926 chi ∧
      ¬Fin15AnchoredAtom3951 chi ∧
      ¬Fin15AnchoredAtom3986 chi ∧
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
  refine ⟨{2, 4, 5, 6, 7, 9, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25332
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3702 Fin15AnchoredAtom3704 Fin15AnchoredAtom3708
    Fin15AnchoredAtom3709 Fin15AnchoredAtom3711 Fin15AnchoredAtom3715 Fin15AnchoredAtom3716
    Fin15AnchoredAtom3726 Fin15AnchoredAtom3727 Fin15AnchoredAtom3737 Fin15AnchoredAtom3739
    Fin15AnchoredAtom3743 Fin15AnchoredAtom3744 Fin15AnchoredAtom3754 Fin15AnchoredAtom3755
    Fin15AnchoredAtom3765 Fin15AnchoredAtom3775 Fin15AnchoredAtom3776 Fin15AnchoredAtom3786
    Fin15AnchoredAtom3811 Fin15AnchoredAtom3823 Fin15AnchoredAtom3827 Fin15AnchoredAtom3828
    Fin15AnchoredAtom3838 Fin15AnchoredAtom3839 Fin15AnchoredAtom3849 Fin15AnchoredAtom3859
    Fin15AnchoredAtom3860 Fin15AnchoredAtom3870 Fin15AnchoredAtom3895 Fin15AnchoredAtom3915
    Fin15AnchoredAtom3916 Fin15AnchoredAtom3926 Fin15AnchoredAtom3951 Fin15AnchoredAtom3986
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

theorem fin15Anchored_clause32089 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3702 chi ∧
      ¬Fin15AnchoredAtom3705 chi ∧
      ¬Fin15AnchoredAtom3706 chi ∧
      ¬Fin15AnchoredAtom3707 chi ∧
      ¬Fin15AnchoredAtom3712 chi ∧
      ¬Fin15AnchoredAtom3713 chi ∧
      ¬Fin15AnchoredAtom3714 chi ∧
      ¬Fin15AnchoredAtom3728 chi ∧
      ¬Fin15AnchoredAtom3729 chi ∧
      ¬Fin15AnchoredAtom3732 chi ∧
      ¬Fin15AnchoredAtom3740 chi ∧
      ¬Fin15AnchoredAtom3741 chi ∧
      ¬Fin15AnchoredAtom3742 chi ∧
      ¬Fin15AnchoredAtom3756 chi ∧
      ¬Fin15AnchoredAtom3757 chi ∧
      ¬Fin15AnchoredAtom3760 chi ∧
      ¬Fin15AnchoredAtom3777 chi ∧
      ¬Fin15AnchoredAtom3778 chi ∧
      ¬Fin15AnchoredAtom3781 chi ∧
      ¬Fin15AnchoredAtom3812 chi ∧
      ¬Fin15AnchoredAtom3824 chi ∧
      ¬Fin15AnchoredAtom3825 chi ∧
      ¬Fin15AnchoredAtom3826 chi ∧
      ¬Fin15AnchoredAtom3840 chi ∧
      ¬Fin15AnchoredAtom3841 chi ∧
      ¬Fin15AnchoredAtom3844 chi ∧
      ¬Fin15AnchoredAtom3861 chi ∧
      ¬Fin15AnchoredAtom3862 chi ∧
      ¬Fin15AnchoredAtom3865 chi ∧
      ¬Fin15AnchoredAtom3896 chi ∧
      ¬Fin15AnchoredAtom3917 chi ∧
      ¬Fin15AnchoredAtom3918 chi ∧
      ¬Fin15AnchoredAtom3921 chi ∧
      ¬Fin15AnchoredAtom3952 chi ∧
      ¬Fin15AnchoredAtom3987 chi ∧
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
  refine ⟨{2, 4, 5, 6, 7, 10, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask07412
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3702 Fin15AnchoredAtom3705 Fin15AnchoredAtom3706
    Fin15AnchoredAtom3707 Fin15AnchoredAtom3712 Fin15AnchoredAtom3713 Fin15AnchoredAtom3714
    Fin15AnchoredAtom3728 Fin15AnchoredAtom3729 Fin15AnchoredAtom3732 Fin15AnchoredAtom3740
    Fin15AnchoredAtom3741 Fin15AnchoredAtom3742 Fin15AnchoredAtom3756 Fin15AnchoredAtom3757
    Fin15AnchoredAtom3760 Fin15AnchoredAtom3777 Fin15AnchoredAtom3778 Fin15AnchoredAtom3781
    Fin15AnchoredAtom3812 Fin15AnchoredAtom3824 Fin15AnchoredAtom3825 Fin15AnchoredAtom3826
    Fin15AnchoredAtom3840 Fin15AnchoredAtom3841 Fin15AnchoredAtom3844 Fin15AnchoredAtom3861
    Fin15AnchoredAtom3862 Fin15AnchoredAtom3865 Fin15AnchoredAtom3896 Fin15AnchoredAtom3917
    Fin15AnchoredAtom3918 Fin15AnchoredAtom3921 Fin15AnchoredAtom3952 Fin15AnchoredAtom3987
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

theorem fin15Anchored_clause32090 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3702 chi ∧
      ¬Fin15AnchoredAtom3705 chi ∧
      ¬Fin15AnchoredAtom3707 chi ∧
      ¬Fin15AnchoredAtom3708 chi ∧
      ¬Fin15AnchoredAtom3712 chi ∧
      ¬Fin15AnchoredAtom3714 chi ∧
      ¬Fin15AnchoredAtom3715 chi ∧
      ¬Fin15AnchoredAtom3729 chi ∧
      ¬Fin15AnchoredAtom3730 chi ∧
      ¬Fin15AnchoredAtom3735 chi ∧
      ¬Fin15AnchoredAtom3740 chi ∧
      ¬Fin15AnchoredAtom3742 chi ∧
      ¬Fin15AnchoredAtom3743 chi ∧
      ¬Fin15AnchoredAtom3757 chi ∧
      ¬Fin15AnchoredAtom3758 chi ∧
      ¬Fin15AnchoredAtom3763 chi ∧
      ¬Fin15AnchoredAtom3778 chi ∧
      ¬Fin15AnchoredAtom3779 chi ∧
      ¬Fin15AnchoredAtom3784 chi ∧
      ¬Fin15AnchoredAtom3815 chi ∧
      ¬Fin15AnchoredAtom3824 chi ∧
      ¬Fin15AnchoredAtom3826 chi ∧
      ¬Fin15AnchoredAtom3827 chi ∧
      ¬Fin15AnchoredAtom3841 chi ∧
      ¬Fin15AnchoredAtom3842 chi ∧
      ¬Fin15AnchoredAtom3847 chi ∧
      ¬Fin15AnchoredAtom3862 chi ∧
      ¬Fin15AnchoredAtom3863 chi ∧
      ¬Fin15AnchoredAtom3868 chi ∧
      ¬Fin15AnchoredAtom3899 chi ∧
      ¬Fin15AnchoredAtom3918 chi ∧
      ¬Fin15AnchoredAtom3919 chi ∧
      ¬Fin15AnchoredAtom3924 chi ∧
      ¬Fin15AnchoredAtom3955 chi ∧
      ¬Fin15AnchoredAtom3990 chi ∧
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
  refine ⟨{2, 4, 5, 6, 7, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13556
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3702 Fin15AnchoredAtom3705 Fin15AnchoredAtom3707
    Fin15AnchoredAtom3708 Fin15AnchoredAtom3712 Fin15AnchoredAtom3714 Fin15AnchoredAtom3715
    Fin15AnchoredAtom3729 Fin15AnchoredAtom3730 Fin15AnchoredAtom3735 Fin15AnchoredAtom3740
    Fin15AnchoredAtom3742 Fin15AnchoredAtom3743 Fin15AnchoredAtom3757 Fin15AnchoredAtom3758
    Fin15AnchoredAtom3763 Fin15AnchoredAtom3778 Fin15AnchoredAtom3779 Fin15AnchoredAtom3784
    Fin15AnchoredAtom3815 Fin15AnchoredAtom3824 Fin15AnchoredAtom3826 Fin15AnchoredAtom3827
    Fin15AnchoredAtom3841 Fin15AnchoredAtom3842 Fin15AnchoredAtom3847 Fin15AnchoredAtom3862
    Fin15AnchoredAtom3863 Fin15AnchoredAtom3868 Fin15AnchoredAtom3899 Fin15AnchoredAtom3918
    Fin15AnchoredAtom3919 Fin15AnchoredAtom3924 Fin15AnchoredAtom3955 Fin15AnchoredAtom3990
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

theorem fin15Anchored_clause32091 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3702 chi ∧
      ¬Fin15AnchoredAtom3705 chi ∧
      ¬Fin15AnchoredAtom3707 chi ∧
      ¬Fin15AnchoredAtom3709 chi ∧
      ¬Fin15AnchoredAtom3712 chi ∧
      ¬Fin15AnchoredAtom3714 chi ∧
      ¬Fin15AnchoredAtom3716 chi ∧
      ¬Fin15AnchoredAtom3729 chi ∧
      ¬Fin15AnchoredAtom3731 chi ∧
      ¬Fin15AnchoredAtom3736 chi ∧
      ¬Fin15AnchoredAtom3740 chi ∧
      ¬Fin15AnchoredAtom3742 chi ∧
      ¬Fin15AnchoredAtom3744 chi ∧
      ¬Fin15AnchoredAtom3757 chi ∧
      ¬Fin15AnchoredAtom3759 chi ∧
      ¬Fin15AnchoredAtom3764 chi ∧
      ¬Fin15AnchoredAtom3778 chi ∧
      ¬Fin15AnchoredAtom3780 chi ∧
      ¬Fin15AnchoredAtom3785 chi ∧
      ¬Fin15AnchoredAtom3816 chi ∧
      ¬Fin15AnchoredAtom3824 chi ∧
      ¬Fin15AnchoredAtom3826 chi ∧
      ¬Fin15AnchoredAtom3828 chi ∧
      ¬Fin15AnchoredAtom3841 chi ∧
      ¬Fin15AnchoredAtom3843 chi ∧
      ¬Fin15AnchoredAtom3848 chi ∧
      ¬Fin15AnchoredAtom3862 chi ∧
      ¬Fin15AnchoredAtom3864 chi ∧
      ¬Fin15AnchoredAtom3869 chi ∧
      ¬Fin15AnchoredAtom3900 chi ∧
      ¬Fin15AnchoredAtom3918 chi ∧
      ¬Fin15AnchoredAtom3920 chi ∧
      ¬Fin15AnchoredAtom3925 chi ∧
      ¬Fin15AnchoredAtom3956 chi ∧
      ¬Fin15AnchoredAtom3991 chi ∧
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
  refine ⟨{2, 4, 5, 6, 7, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21748
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3702 Fin15AnchoredAtom3705 Fin15AnchoredAtom3707
    Fin15AnchoredAtom3709 Fin15AnchoredAtom3712 Fin15AnchoredAtom3714 Fin15AnchoredAtom3716
    Fin15AnchoredAtom3729 Fin15AnchoredAtom3731 Fin15AnchoredAtom3736 Fin15AnchoredAtom3740
    Fin15AnchoredAtom3742 Fin15AnchoredAtom3744 Fin15AnchoredAtom3757 Fin15AnchoredAtom3759
    Fin15AnchoredAtom3764 Fin15AnchoredAtom3778 Fin15AnchoredAtom3780 Fin15AnchoredAtom3785
    Fin15AnchoredAtom3816 Fin15AnchoredAtom3824 Fin15AnchoredAtom3826 Fin15AnchoredAtom3828
    Fin15AnchoredAtom3841 Fin15AnchoredAtom3843 Fin15AnchoredAtom3848 Fin15AnchoredAtom3862
    Fin15AnchoredAtom3864 Fin15AnchoredAtom3869 Fin15AnchoredAtom3900 Fin15AnchoredAtom3918
    Fin15AnchoredAtom3920 Fin15AnchoredAtom3925 Fin15AnchoredAtom3956 Fin15AnchoredAtom3991
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

theorem fin15Anchored_clause32092 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3702 chi ∧
      ¬Fin15AnchoredAtom3705 chi ∧
      ¬Fin15AnchoredAtom3708 chi ∧
      ¬Fin15AnchoredAtom3709 chi ∧
      ¬Fin15AnchoredAtom3712 chi ∧
      ¬Fin15AnchoredAtom3715 chi ∧
      ¬Fin15AnchoredAtom3716 chi ∧
      ¬Fin15AnchoredAtom3730 chi ∧
      ¬Fin15AnchoredAtom3731 chi ∧
      ¬Fin15AnchoredAtom3737 chi ∧
      ¬Fin15AnchoredAtom3740 chi ∧
      ¬Fin15AnchoredAtom3743 chi ∧
      ¬Fin15AnchoredAtom3744 chi ∧
      ¬Fin15AnchoredAtom3758 chi ∧
      ¬Fin15AnchoredAtom3759 chi ∧
      ¬Fin15AnchoredAtom3765 chi ∧
      ¬Fin15AnchoredAtom3779 chi ∧
      ¬Fin15AnchoredAtom3780 chi ∧
      ¬Fin15AnchoredAtom3786 chi ∧
      ¬Fin15AnchoredAtom3817 chi ∧
      ¬Fin15AnchoredAtom3824 chi ∧
      ¬Fin15AnchoredAtom3827 chi ∧
      ¬Fin15AnchoredAtom3828 chi ∧
      ¬Fin15AnchoredAtom3842 chi ∧
      ¬Fin15AnchoredAtom3843 chi ∧
      ¬Fin15AnchoredAtom3849 chi ∧
      ¬Fin15AnchoredAtom3863 chi ∧
      ¬Fin15AnchoredAtom3864 chi ∧
      ¬Fin15AnchoredAtom3870 chi ∧
      ¬Fin15AnchoredAtom3901 chi ∧
      ¬Fin15AnchoredAtom3919 chi ∧
      ¬Fin15AnchoredAtom3920 chi ∧
      ¬Fin15AnchoredAtom3926 chi ∧
      ¬Fin15AnchoredAtom3957 chi ∧
      ¬Fin15AnchoredAtom3992 chi ∧
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
  refine ⟨{2, 4, 5, 6, 7, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25844
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3702 Fin15AnchoredAtom3705 Fin15AnchoredAtom3708
    Fin15AnchoredAtom3709 Fin15AnchoredAtom3712 Fin15AnchoredAtom3715 Fin15AnchoredAtom3716
    Fin15AnchoredAtom3730 Fin15AnchoredAtom3731 Fin15AnchoredAtom3737 Fin15AnchoredAtom3740
    Fin15AnchoredAtom3743 Fin15AnchoredAtom3744 Fin15AnchoredAtom3758 Fin15AnchoredAtom3759
    Fin15AnchoredAtom3765 Fin15AnchoredAtom3779 Fin15AnchoredAtom3780 Fin15AnchoredAtom3786
    Fin15AnchoredAtom3817 Fin15AnchoredAtom3824 Fin15AnchoredAtom3827 Fin15AnchoredAtom3828
    Fin15AnchoredAtom3842 Fin15AnchoredAtom3843 Fin15AnchoredAtom3849 Fin15AnchoredAtom3863
    Fin15AnchoredAtom3864 Fin15AnchoredAtom3870 Fin15AnchoredAtom3901 Fin15AnchoredAtom3919
    Fin15AnchoredAtom3920 Fin15AnchoredAtom3926 Fin15AnchoredAtom3957 Fin15AnchoredAtom3992
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

theorem fin15Anchored_clause32093 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3702 chi ∧
      ¬Fin15AnchoredAtom3707 chi ∧
      ¬Fin15AnchoredAtom3708 chi ∧
      ¬Fin15AnchoredAtom3709 chi ∧
      ¬Fin15AnchoredAtom3714 chi ∧
      ¬Fin15AnchoredAtom3715 chi ∧
      ¬Fin15AnchoredAtom3716 chi ∧
      ¬Fin15AnchoredAtom3735 chi ∧
      ¬Fin15AnchoredAtom3736 chi ∧
      ¬Fin15AnchoredAtom3737 chi ∧
      ¬Fin15AnchoredAtom3742 chi ∧
      ¬Fin15AnchoredAtom3743 chi ∧
      ¬Fin15AnchoredAtom3744 chi ∧
      ¬Fin15AnchoredAtom3763 chi ∧
      ¬Fin15AnchoredAtom3764 chi ∧
      ¬Fin15AnchoredAtom3765 chi ∧
      ¬Fin15AnchoredAtom3784 chi ∧
      ¬Fin15AnchoredAtom3785 chi ∧
      ¬Fin15AnchoredAtom3786 chi ∧
      ¬Fin15AnchoredAtom3821 chi ∧
      ¬Fin15AnchoredAtom3826 chi ∧
      ¬Fin15AnchoredAtom3827 chi ∧
      ¬Fin15AnchoredAtom3828 chi ∧
      ¬Fin15AnchoredAtom3847 chi ∧
      ¬Fin15AnchoredAtom3848 chi ∧
      ¬Fin15AnchoredAtom3849 chi ∧
      ¬Fin15AnchoredAtom3868 chi ∧
      ¬Fin15AnchoredAtom3869 chi ∧
      ¬Fin15AnchoredAtom3870 chi ∧
      ¬Fin15AnchoredAtom3905 chi ∧
      ¬Fin15AnchoredAtom3924 chi ∧
      ¬Fin15AnchoredAtom3925 chi ∧
      ¬Fin15AnchoredAtom3926 chi ∧
      ¬Fin15AnchoredAtom3961 chi ∧
      ¬Fin15AnchoredAtom3996 chi ∧
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
  refine ⟨{2, 4, 5, 6, 7, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask28916
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3702 Fin15AnchoredAtom3707 Fin15AnchoredAtom3708
    Fin15AnchoredAtom3709 Fin15AnchoredAtom3714 Fin15AnchoredAtom3715 Fin15AnchoredAtom3716
    Fin15AnchoredAtom3735 Fin15AnchoredAtom3736 Fin15AnchoredAtom3737 Fin15AnchoredAtom3742
    Fin15AnchoredAtom3743 Fin15AnchoredAtom3744 Fin15AnchoredAtom3763 Fin15AnchoredAtom3764
    Fin15AnchoredAtom3765 Fin15AnchoredAtom3784 Fin15AnchoredAtom3785 Fin15AnchoredAtom3786
    Fin15AnchoredAtom3821 Fin15AnchoredAtom3826 Fin15AnchoredAtom3827 Fin15AnchoredAtom3828
    Fin15AnchoredAtom3847 Fin15AnchoredAtom3848 Fin15AnchoredAtom3849 Fin15AnchoredAtom3868
    Fin15AnchoredAtom3869 Fin15AnchoredAtom3870 Fin15AnchoredAtom3905 Fin15AnchoredAtom3924
    Fin15AnchoredAtom3925 Fin15AnchoredAtom3926 Fin15AnchoredAtom3961 Fin15AnchoredAtom3996
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

theorem fin15Anchored_clause32094 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3704 chi ∧
      ¬Fin15AnchoredAtom3705 chi ∧
      ¬Fin15AnchoredAtom3707 chi ∧
      ¬Fin15AnchoredAtom3708 chi ∧
      ¬Fin15AnchoredAtom3723 chi ∧
      ¬Fin15AnchoredAtom3725 chi ∧
      ¬Fin15AnchoredAtom3726 chi ∧
      ¬Fin15AnchoredAtom3729 chi ∧
      ¬Fin15AnchoredAtom3730 chi ∧
      ¬Fin15AnchoredAtom3735 chi ∧
      ¬Fin15AnchoredAtom3751 chi ∧
      ¬Fin15AnchoredAtom3753 chi ∧
      ¬Fin15AnchoredAtom3754 chi ∧
      ¬Fin15AnchoredAtom3757 chi ∧
      ¬Fin15AnchoredAtom3758 chi ∧
      ¬Fin15AnchoredAtom3763 chi ∧
      ¬Fin15AnchoredAtom3803 chi ∧
      ¬Fin15AnchoredAtom3804 chi ∧
      ¬Fin15AnchoredAtom3809 chi ∧
      ¬Fin15AnchoredAtom3815 chi ∧
      ¬Fin15AnchoredAtom3835 chi ∧
      ¬Fin15AnchoredAtom3837 chi ∧
      ¬Fin15AnchoredAtom3838 chi ∧
      ¬Fin15AnchoredAtom3841 chi ∧
      ¬Fin15AnchoredAtom3842 chi ∧
      ¬Fin15AnchoredAtom3847 chi ∧
      ¬Fin15AnchoredAtom3887 chi ∧
      ¬Fin15AnchoredAtom3888 chi ∧
      ¬Fin15AnchoredAtom3893 chi ∧
      ¬Fin15AnchoredAtom3899 chi ∧
      ¬Fin15AnchoredAtom3943 chi ∧
      ¬Fin15AnchoredAtom3944 chi ∧
      ¬Fin15AnchoredAtom3949 chi ∧
      ¬Fin15AnchoredAtom3955 chi ∧
      ¬Fin15AnchoredAtom4020 chi ∧
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
  refine ⟨{2, 4, 5, 6, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13940
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3704 Fin15AnchoredAtom3705 Fin15AnchoredAtom3707
    Fin15AnchoredAtom3708 Fin15AnchoredAtom3723 Fin15AnchoredAtom3725 Fin15AnchoredAtom3726
    Fin15AnchoredAtom3729 Fin15AnchoredAtom3730 Fin15AnchoredAtom3735 Fin15AnchoredAtom3751
    Fin15AnchoredAtom3753 Fin15AnchoredAtom3754 Fin15AnchoredAtom3757 Fin15AnchoredAtom3758
    Fin15AnchoredAtom3763 Fin15AnchoredAtom3803 Fin15AnchoredAtom3804 Fin15AnchoredAtom3809
    Fin15AnchoredAtom3815 Fin15AnchoredAtom3835 Fin15AnchoredAtom3837 Fin15AnchoredAtom3838
    Fin15AnchoredAtom3841 Fin15AnchoredAtom3842 Fin15AnchoredAtom3847 Fin15AnchoredAtom3887
    Fin15AnchoredAtom3888 Fin15AnchoredAtom3893 Fin15AnchoredAtom3899 Fin15AnchoredAtom3943
    Fin15AnchoredAtom3944 Fin15AnchoredAtom3949 Fin15AnchoredAtom3955 Fin15AnchoredAtom4020
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

theorem fin15Anchored_clause32095 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3704 chi ∧
      ¬Fin15AnchoredAtom3705 chi ∧
      ¬Fin15AnchoredAtom3707 chi ∧
      ¬Fin15AnchoredAtom3709 chi ∧
      ¬Fin15AnchoredAtom3723 chi ∧
      ¬Fin15AnchoredAtom3725 chi ∧
      ¬Fin15AnchoredAtom3727 chi ∧
      ¬Fin15AnchoredAtom3729 chi ∧
      ¬Fin15AnchoredAtom3731 chi ∧
      ¬Fin15AnchoredAtom3736 chi ∧
      ¬Fin15AnchoredAtom3751 chi ∧
      ¬Fin15AnchoredAtom3753 chi ∧
      ¬Fin15AnchoredAtom3755 chi ∧
      ¬Fin15AnchoredAtom3757 chi ∧
      ¬Fin15AnchoredAtom3759 chi ∧
      ¬Fin15AnchoredAtom3764 chi ∧
      ¬Fin15AnchoredAtom3803 chi ∧
      ¬Fin15AnchoredAtom3805 chi ∧
      ¬Fin15AnchoredAtom3810 chi ∧
      ¬Fin15AnchoredAtom3816 chi ∧
      ¬Fin15AnchoredAtom3835 chi ∧
      ¬Fin15AnchoredAtom3837 chi ∧
      ¬Fin15AnchoredAtom3839 chi ∧
      ¬Fin15AnchoredAtom3841 chi ∧
      ¬Fin15AnchoredAtom3843 chi ∧
      ¬Fin15AnchoredAtom3848 chi ∧
      ¬Fin15AnchoredAtom3887 chi ∧
      ¬Fin15AnchoredAtom3889 chi ∧
      ¬Fin15AnchoredAtom3894 chi ∧
      ¬Fin15AnchoredAtom3900 chi ∧
      ¬Fin15AnchoredAtom3943 chi ∧
      ¬Fin15AnchoredAtom3945 chi ∧
      ¬Fin15AnchoredAtom3950 chi ∧
      ¬Fin15AnchoredAtom3956 chi ∧
      ¬Fin15AnchoredAtom4021 chi ∧
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
  refine ⟨{2, 4, 5, 6, 9, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22132
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3704 Fin15AnchoredAtom3705 Fin15AnchoredAtom3707
    Fin15AnchoredAtom3709 Fin15AnchoredAtom3723 Fin15AnchoredAtom3725 Fin15AnchoredAtom3727
    Fin15AnchoredAtom3729 Fin15AnchoredAtom3731 Fin15AnchoredAtom3736 Fin15AnchoredAtom3751
    Fin15AnchoredAtom3753 Fin15AnchoredAtom3755 Fin15AnchoredAtom3757 Fin15AnchoredAtom3759
    Fin15AnchoredAtom3764 Fin15AnchoredAtom3803 Fin15AnchoredAtom3805 Fin15AnchoredAtom3810
    Fin15AnchoredAtom3816 Fin15AnchoredAtom3835 Fin15AnchoredAtom3837 Fin15AnchoredAtom3839
    Fin15AnchoredAtom3841 Fin15AnchoredAtom3843 Fin15AnchoredAtom3848 Fin15AnchoredAtom3887
    Fin15AnchoredAtom3889 Fin15AnchoredAtom3894 Fin15AnchoredAtom3900 Fin15AnchoredAtom3943
    Fin15AnchoredAtom3945 Fin15AnchoredAtom3950 Fin15AnchoredAtom3956 Fin15AnchoredAtom4021
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

theorem fin15Anchored_clause32096 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3704 chi ∧
      ¬Fin15AnchoredAtom3705 chi ∧
      ¬Fin15AnchoredAtom3708 chi ∧
      ¬Fin15AnchoredAtom3709 chi ∧
      ¬Fin15AnchoredAtom3723 chi ∧
      ¬Fin15AnchoredAtom3726 chi ∧
      ¬Fin15AnchoredAtom3727 chi ∧
      ¬Fin15AnchoredAtom3730 chi ∧
      ¬Fin15AnchoredAtom3731 chi ∧
      ¬Fin15AnchoredAtom3737 chi ∧
      ¬Fin15AnchoredAtom3751 chi ∧
      ¬Fin15AnchoredAtom3754 chi ∧
      ¬Fin15AnchoredAtom3755 chi ∧
      ¬Fin15AnchoredAtom3758 chi ∧
      ¬Fin15AnchoredAtom3759 chi ∧
      ¬Fin15AnchoredAtom3765 chi ∧
      ¬Fin15AnchoredAtom3804 chi ∧
      ¬Fin15AnchoredAtom3805 chi ∧
      ¬Fin15AnchoredAtom3811 chi ∧
      ¬Fin15AnchoredAtom3817 chi ∧
      ¬Fin15AnchoredAtom3835 chi ∧
      ¬Fin15AnchoredAtom3838 chi ∧
      ¬Fin15AnchoredAtom3839 chi ∧
      ¬Fin15AnchoredAtom3842 chi ∧
      ¬Fin15AnchoredAtom3843 chi ∧
      ¬Fin15AnchoredAtom3849 chi ∧
      ¬Fin15AnchoredAtom3888 chi ∧
      ¬Fin15AnchoredAtom3889 chi ∧
      ¬Fin15AnchoredAtom3895 chi ∧
      ¬Fin15AnchoredAtom3901 chi ∧
      ¬Fin15AnchoredAtom3944 chi ∧
      ¬Fin15AnchoredAtom3945 chi ∧
      ¬Fin15AnchoredAtom3951 chi ∧
      ¬Fin15AnchoredAtom3957 chi ∧
      ¬Fin15AnchoredAtom4022 chi ∧
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
  refine ⟨{2, 4, 5, 6, 9, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26228
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3704 Fin15AnchoredAtom3705 Fin15AnchoredAtom3708
    Fin15AnchoredAtom3709 Fin15AnchoredAtom3723 Fin15AnchoredAtom3726 Fin15AnchoredAtom3727
    Fin15AnchoredAtom3730 Fin15AnchoredAtom3731 Fin15AnchoredAtom3737 Fin15AnchoredAtom3751
    Fin15AnchoredAtom3754 Fin15AnchoredAtom3755 Fin15AnchoredAtom3758 Fin15AnchoredAtom3759
    Fin15AnchoredAtom3765 Fin15AnchoredAtom3804 Fin15AnchoredAtom3805 Fin15AnchoredAtom3811
    Fin15AnchoredAtom3817 Fin15AnchoredAtom3835 Fin15AnchoredAtom3838 Fin15AnchoredAtom3839
    Fin15AnchoredAtom3842 Fin15AnchoredAtom3843 Fin15AnchoredAtom3849 Fin15AnchoredAtom3888
    Fin15AnchoredAtom3889 Fin15AnchoredAtom3895 Fin15AnchoredAtom3901 Fin15AnchoredAtom3944
    Fin15AnchoredAtom3945 Fin15AnchoredAtom3951 Fin15AnchoredAtom3957 Fin15AnchoredAtom4022
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

theorem fin15Anchored_clause32097 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3704 chi ∧
      ¬Fin15AnchoredAtom3707 chi ∧
      ¬Fin15AnchoredAtom3708 chi ∧
      ¬Fin15AnchoredAtom3709 chi ∧
      ¬Fin15AnchoredAtom3725 chi ∧
      ¬Fin15AnchoredAtom3726 chi ∧
      ¬Fin15AnchoredAtom3727 chi ∧
      ¬Fin15AnchoredAtom3735 chi ∧
      ¬Fin15AnchoredAtom3736 chi ∧
      ¬Fin15AnchoredAtom3737 chi ∧
      ¬Fin15AnchoredAtom3753 chi ∧
      ¬Fin15AnchoredAtom3754 chi ∧
      ¬Fin15AnchoredAtom3755 chi ∧
      ¬Fin15AnchoredAtom3763 chi ∧
      ¬Fin15AnchoredAtom3764 chi ∧
      ¬Fin15AnchoredAtom3765 chi ∧
      ¬Fin15AnchoredAtom3809 chi ∧
      ¬Fin15AnchoredAtom3810 chi ∧
      ¬Fin15AnchoredAtom3811 chi ∧
      ¬Fin15AnchoredAtom3821 chi ∧
      ¬Fin15AnchoredAtom3837 chi ∧
      ¬Fin15AnchoredAtom3838 chi ∧
      ¬Fin15AnchoredAtom3839 chi ∧
      ¬Fin15AnchoredAtom3847 chi ∧
      ¬Fin15AnchoredAtom3848 chi ∧
      ¬Fin15AnchoredAtom3849 chi ∧
      ¬Fin15AnchoredAtom3893 chi ∧
      ¬Fin15AnchoredAtom3894 chi ∧
      ¬Fin15AnchoredAtom3895 chi ∧
      ¬Fin15AnchoredAtom3905 chi ∧
      ¬Fin15AnchoredAtom3949 chi ∧
      ¬Fin15AnchoredAtom3950 chi ∧
      ¬Fin15AnchoredAtom3951 chi ∧
      ¬Fin15AnchoredAtom3961 chi ∧
      ¬Fin15AnchoredAtom4026 chi ∧
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
  refine ⟨{2, 4, 5, 6, 9, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29300
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3704 Fin15AnchoredAtom3707 Fin15AnchoredAtom3708
    Fin15AnchoredAtom3709 Fin15AnchoredAtom3725 Fin15AnchoredAtom3726 Fin15AnchoredAtom3727
    Fin15AnchoredAtom3735 Fin15AnchoredAtom3736 Fin15AnchoredAtom3737 Fin15AnchoredAtom3753
    Fin15AnchoredAtom3754 Fin15AnchoredAtom3755 Fin15AnchoredAtom3763 Fin15AnchoredAtom3764
    Fin15AnchoredAtom3765 Fin15AnchoredAtom3809 Fin15AnchoredAtom3810 Fin15AnchoredAtom3811
    Fin15AnchoredAtom3821 Fin15AnchoredAtom3837 Fin15AnchoredAtom3838 Fin15AnchoredAtom3839
    Fin15AnchoredAtom3847 Fin15AnchoredAtom3848 Fin15AnchoredAtom3849 Fin15AnchoredAtom3893
    Fin15AnchoredAtom3894 Fin15AnchoredAtom3895 Fin15AnchoredAtom3905 Fin15AnchoredAtom3949
    Fin15AnchoredAtom3950 Fin15AnchoredAtom3951 Fin15AnchoredAtom3961 Fin15AnchoredAtom4026
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

theorem fin15Anchored_clause32098 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3705 chi ∧
      ¬Fin15AnchoredAtom3707 chi ∧
      ¬Fin15AnchoredAtom3708 chi ∧
      ¬Fin15AnchoredAtom3709 chi ∧
      ¬Fin15AnchoredAtom3729 chi ∧
      ¬Fin15AnchoredAtom3730 chi ∧
      ¬Fin15AnchoredAtom3731 chi ∧
      ¬Fin15AnchoredAtom3735 chi ∧
      ¬Fin15AnchoredAtom3736 chi ∧
      ¬Fin15AnchoredAtom3737 chi ∧
      ¬Fin15AnchoredAtom3757 chi ∧
      ¬Fin15AnchoredAtom3758 chi ∧
      ¬Fin15AnchoredAtom3759 chi ∧
      ¬Fin15AnchoredAtom3763 chi ∧
      ¬Fin15AnchoredAtom3764 chi ∧
      ¬Fin15AnchoredAtom3765 chi ∧
      ¬Fin15AnchoredAtom3815 chi ∧
      ¬Fin15AnchoredAtom3816 chi ∧
      ¬Fin15AnchoredAtom3817 chi ∧
      ¬Fin15AnchoredAtom3821 chi ∧
      ¬Fin15AnchoredAtom3841 chi ∧
      ¬Fin15AnchoredAtom3842 chi ∧
      ¬Fin15AnchoredAtom3843 chi ∧
      ¬Fin15AnchoredAtom3847 chi ∧
      ¬Fin15AnchoredAtom3848 chi ∧
      ¬Fin15AnchoredAtom3849 chi ∧
      ¬Fin15AnchoredAtom3899 chi ∧
      ¬Fin15AnchoredAtom3900 chi ∧
      ¬Fin15AnchoredAtom3901 chi ∧
      ¬Fin15AnchoredAtom3905 chi ∧
      ¬Fin15AnchoredAtom3955 chi ∧
      ¬Fin15AnchoredAtom3956 chi ∧
      ¬Fin15AnchoredAtom3957 chi ∧
      ¬Fin15AnchoredAtom3961 chi ∧
      ¬Fin15AnchoredAtom4030 chi ∧
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
  refine ⟨{2, 4, 5, 6, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29812
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3705 Fin15AnchoredAtom3707 Fin15AnchoredAtom3708
    Fin15AnchoredAtom3709 Fin15AnchoredAtom3729 Fin15AnchoredAtom3730 Fin15AnchoredAtom3731
    Fin15AnchoredAtom3735 Fin15AnchoredAtom3736 Fin15AnchoredAtom3737 Fin15AnchoredAtom3757
    Fin15AnchoredAtom3758 Fin15AnchoredAtom3759 Fin15AnchoredAtom3763 Fin15AnchoredAtom3764
    Fin15AnchoredAtom3765 Fin15AnchoredAtom3815 Fin15AnchoredAtom3816 Fin15AnchoredAtom3817
    Fin15AnchoredAtom3821 Fin15AnchoredAtom3841 Fin15AnchoredAtom3842 Fin15AnchoredAtom3843
    Fin15AnchoredAtom3847 Fin15AnchoredAtom3848 Fin15AnchoredAtom3849 Fin15AnchoredAtom3899
    Fin15AnchoredAtom3900 Fin15AnchoredAtom3901 Fin15AnchoredAtom3905 Fin15AnchoredAtom3955
    Fin15AnchoredAtom3956 Fin15AnchoredAtom3957 Fin15AnchoredAtom3961 Fin15AnchoredAtom4030
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

theorem fin15Anchored_clause32099 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3711 chi ∧
      ¬Fin15AnchoredAtom3712 chi ∧
      ¬Fin15AnchoredAtom3713 chi ∧
      ¬Fin15AnchoredAtom3715 chi ∧
      ¬Fin15AnchoredAtom3723 chi ∧
      ¬Fin15AnchoredAtom3724 chi ∧
      ¬Fin15AnchoredAtom3726 chi ∧
      ¬Fin15AnchoredAtom3728 chi ∧
      ¬Fin15AnchoredAtom3730 chi ∧
      ¬Fin15AnchoredAtom3733 chi ∧
      ¬Fin15AnchoredAtom3772 chi ∧
      ¬Fin15AnchoredAtom3773 chi ∧
      ¬Fin15AnchoredAtom3775 chi ∧
      ¬Fin15AnchoredAtom3777 chi ∧
      ¬Fin15AnchoredAtom3779 chi ∧
      ¬Fin15AnchoredAtom3782 chi ∧
      ¬Fin15AnchoredAtom3802 chi ∧
      ¬Fin15AnchoredAtom3804 chi ∧
      ¬Fin15AnchoredAtom3807 chi ∧
      ¬Fin15AnchoredAtom3813 chi ∧
      ¬Fin15AnchoredAtom3856 chi ∧
      ¬Fin15AnchoredAtom3857 chi ∧
      ¬Fin15AnchoredAtom3859 chi ∧
      ¬Fin15AnchoredAtom3861 chi ∧
      ¬Fin15AnchoredAtom3863 chi ∧
      ¬Fin15AnchoredAtom3866 chi ∧
      ¬Fin15AnchoredAtom3886 chi ∧
      ¬Fin15AnchoredAtom3888 chi ∧
      ¬Fin15AnchoredAtom3891 chi ∧
      ¬Fin15AnchoredAtom3897 chi ∧
      ¬Fin15AnchoredAtom3977 chi ∧
      ¬Fin15AnchoredAtom3979 chi ∧
      ¬Fin15AnchoredAtom3982 chi ∧
      ¬Fin15AnchoredAtom3988 chi ∧
      ¬Fin15AnchoredAtom4018 chi ∧
      ¬Fin15AnchoredAtom4396 chi ∧
      ¬Fin15AnchoredAtom4397 chi ∧
      ¬Fin15AnchoredAtom4399 chi ∧
      ¬Fin15AnchoredAtom4401 chi ∧
      ¬Fin15AnchoredAtom4403 chi ∧
      ¬Fin15AnchoredAtom4406 chi ∧
      ¬Fin15AnchoredAtom4426 chi ∧
      ¬Fin15AnchoredAtom4428 chi ∧
      ¬Fin15AnchoredAtom4431 chi ∧
      ¬Fin15AnchoredAtom4437 chi ∧
      ¬Fin15AnchoredAtom4517 chi ∧
      ¬Fin15AnchoredAtom4519 chi ∧
      ¬Fin15AnchoredAtom4522 chi ∧
      ¬Fin15AnchoredAtom4528 chi ∧
      ¬Fin15AnchoredAtom4558 chi ∧
      ¬Fin15AnchoredAtom4643 chi ∧
      ¬Fin15AnchoredAtom4645 chi ∧
      ¬Fin15AnchoredAtom4648 chi ∧
      ¬Fin15AnchoredAtom4654 chi ∧
      ¬Fin15AnchoredAtom4684 chi ∧
      ¬Fin15AnchoredAtom4789 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 4, 5, 7, 9, 10, 11, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask11956
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3711 Fin15AnchoredAtom3712 Fin15AnchoredAtom3713
    Fin15AnchoredAtom3715 Fin15AnchoredAtom3723 Fin15AnchoredAtom3724 Fin15AnchoredAtom3726
    Fin15AnchoredAtom3728 Fin15AnchoredAtom3730 Fin15AnchoredAtom3733 Fin15AnchoredAtom3772
    Fin15AnchoredAtom3773 Fin15AnchoredAtom3775 Fin15AnchoredAtom3777 Fin15AnchoredAtom3779
    Fin15AnchoredAtom3782 Fin15AnchoredAtom3802 Fin15AnchoredAtom3804 Fin15AnchoredAtom3807
    Fin15AnchoredAtom3813 Fin15AnchoredAtom3856 Fin15AnchoredAtom3857 Fin15AnchoredAtom3859
    Fin15AnchoredAtom3861 Fin15AnchoredAtom3863 Fin15AnchoredAtom3866 Fin15AnchoredAtom3886
    Fin15AnchoredAtom3888 Fin15AnchoredAtom3891 Fin15AnchoredAtom3897 Fin15AnchoredAtom3977
    Fin15AnchoredAtom3979 Fin15AnchoredAtom3982 Fin15AnchoredAtom3988 Fin15AnchoredAtom4018
    Fin15AnchoredAtom4396 Fin15AnchoredAtom4397 Fin15AnchoredAtom4399 Fin15AnchoredAtom4401
    Fin15AnchoredAtom4403 Fin15AnchoredAtom4406 Fin15AnchoredAtom4426 Fin15AnchoredAtom4428
    Fin15AnchoredAtom4431 Fin15AnchoredAtom4437 Fin15AnchoredAtom4517 Fin15AnchoredAtom4519
    Fin15AnchoredAtom4522 Fin15AnchoredAtom4528 Fin15AnchoredAtom4558 Fin15AnchoredAtom4643
    Fin15AnchoredAtom4645 Fin15AnchoredAtom4648 Fin15AnchoredAtom4654 Fin15AnchoredAtom4684
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

theorem fin15Anchored_clause32100 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3711 chi ∧
      ¬Fin15AnchoredAtom3712 chi ∧
      ¬Fin15AnchoredAtom3714 chi ∧
      ¬Fin15AnchoredAtom3715 chi ∧
      ¬Fin15AnchoredAtom3723 chi ∧
      ¬Fin15AnchoredAtom3725 chi ∧
      ¬Fin15AnchoredAtom3726 chi ∧
      ¬Fin15AnchoredAtom3729 chi ∧
      ¬Fin15AnchoredAtom3730 chi ∧
      ¬Fin15AnchoredAtom3735 chi ∧
      ¬Fin15AnchoredAtom3772 chi ∧
      ¬Fin15AnchoredAtom3774 chi ∧
      ¬Fin15AnchoredAtom3775 chi ∧
      ¬Fin15AnchoredAtom3778 chi ∧
      ¬Fin15AnchoredAtom3779 chi ∧
      ¬Fin15AnchoredAtom3784 chi ∧
      ¬Fin15AnchoredAtom3803 chi ∧
      ¬Fin15AnchoredAtom3804 chi ∧
      ¬Fin15AnchoredAtom3809 chi ∧
      ¬Fin15AnchoredAtom3815 chi ∧
      ¬Fin15AnchoredAtom3856 chi ∧
      ¬Fin15AnchoredAtom3858 chi ∧
      ¬Fin15AnchoredAtom3859 chi ∧
      ¬Fin15AnchoredAtom3862 chi ∧
      ¬Fin15AnchoredAtom3863 chi ∧
      ¬Fin15AnchoredAtom3868 chi ∧
      ¬Fin15AnchoredAtom3887 chi ∧
      ¬Fin15AnchoredAtom3888 chi ∧
      ¬Fin15AnchoredAtom3893 chi ∧
      ¬Fin15AnchoredAtom3899 chi ∧
      ¬Fin15AnchoredAtom3978 chi ∧
      ¬Fin15AnchoredAtom3979 chi ∧
      ¬Fin15AnchoredAtom3984 chi ∧
      ¬Fin15AnchoredAtom3990 chi ∧
      ¬Fin15AnchoredAtom4020 chi ∧
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
  refine ⟨{2, 4, 5, 7, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask14004
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3711 Fin15AnchoredAtom3712 Fin15AnchoredAtom3714
    Fin15AnchoredAtom3715 Fin15AnchoredAtom3723 Fin15AnchoredAtom3725 Fin15AnchoredAtom3726
    Fin15AnchoredAtom3729 Fin15AnchoredAtom3730 Fin15AnchoredAtom3735 Fin15AnchoredAtom3772
    Fin15AnchoredAtom3774 Fin15AnchoredAtom3775 Fin15AnchoredAtom3778 Fin15AnchoredAtom3779
    Fin15AnchoredAtom3784 Fin15AnchoredAtom3803 Fin15AnchoredAtom3804 Fin15AnchoredAtom3809
    Fin15AnchoredAtom3815 Fin15AnchoredAtom3856 Fin15AnchoredAtom3858 Fin15AnchoredAtom3859
    Fin15AnchoredAtom3862 Fin15AnchoredAtom3863 Fin15AnchoredAtom3868 Fin15AnchoredAtom3887
    Fin15AnchoredAtom3888 Fin15AnchoredAtom3893 Fin15AnchoredAtom3899 Fin15AnchoredAtom3978
    Fin15AnchoredAtom3979 Fin15AnchoredAtom3984 Fin15AnchoredAtom3990 Fin15AnchoredAtom4020
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

theorem fin15Anchored_clause32101 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3711 chi ∧
      ¬Fin15AnchoredAtom3712 chi ∧
      ¬Fin15AnchoredAtom3714 chi ∧
      ¬Fin15AnchoredAtom3716 chi ∧
      ¬Fin15AnchoredAtom3723 chi ∧
      ¬Fin15AnchoredAtom3725 chi ∧
      ¬Fin15AnchoredAtom3727 chi ∧
      ¬Fin15AnchoredAtom3729 chi ∧
      ¬Fin15AnchoredAtom3731 chi ∧
      ¬Fin15AnchoredAtom3736 chi ∧
      ¬Fin15AnchoredAtom3772 chi ∧
      ¬Fin15AnchoredAtom3774 chi ∧
      ¬Fin15AnchoredAtom3776 chi ∧
      ¬Fin15AnchoredAtom3778 chi ∧
      ¬Fin15AnchoredAtom3780 chi ∧
      ¬Fin15AnchoredAtom3785 chi ∧
      ¬Fin15AnchoredAtom3803 chi ∧
      ¬Fin15AnchoredAtom3805 chi ∧
      ¬Fin15AnchoredAtom3810 chi ∧
      ¬Fin15AnchoredAtom3816 chi ∧
      ¬Fin15AnchoredAtom3856 chi ∧
      ¬Fin15AnchoredAtom3858 chi ∧
      ¬Fin15AnchoredAtom3860 chi ∧
      ¬Fin15AnchoredAtom3862 chi ∧
      ¬Fin15AnchoredAtom3864 chi ∧
      ¬Fin15AnchoredAtom3869 chi ∧
      ¬Fin15AnchoredAtom3887 chi ∧
      ¬Fin15AnchoredAtom3889 chi ∧
      ¬Fin15AnchoredAtom3894 chi ∧
      ¬Fin15AnchoredAtom3900 chi ∧
      ¬Fin15AnchoredAtom3978 chi ∧
      ¬Fin15AnchoredAtom3980 chi ∧
      ¬Fin15AnchoredAtom3985 chi ∧
      ¬Fin15AnchoredAtom3991 chi ∧
      ¬Fin15AnchoredAtom4021 chi ∧
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
  refine ⟨{2, 4, 5, 7, 9, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22196
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3711 Fin15AnchoredAtom3712 Fin15AnchoredAtom3714
    Fin15AnchoredAtom3716 Fin15AnchoredAtom3723 Fin15AnchoredAtom3725 Fin15AnchoredAtom3727
    Fin15AnchoredAtom3729 Fin15AnchoredAtom3731 Fin15AnchoredAtom3736 Fin15AnchoredAtom3772
    Fin15AnchoredAtom3774 Fin15AnchoredAtom3776 Fin15AnchoredAtom3778 Fin15AnchoredAtom3780
    Fin15AnchoredAtom3785 Fin15AnchoredAtom3803 Fin15AnchoredAtom3805 Fin15AnchoredAtom3810
    Fin15AnchoredAtom3816 Fin15AnchoredAtom3856 Fin15AnchoredAtom3858 Fin15AnchoredAtom3860
    Fin15AnchoredAtom3862 Fin15AnchoredAtom3864 Fin15AnchoredAtom3869 Fin15AnchoredAtom3887
    Fin15AnchoredAtom3889 Fin15AnchoredAtom3894 Fin15AnchoredAtom3900 Fin15AnchoredAtom3978
    Fin15AnchoredAtom3980 Fin15AnchoredAtom3985 Fin15AnchoredAtom3991 Fin15AnchoredAtom4021
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

theorem fin15Anchored_clause32102 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3711 chi ∧
      ¬Fin15AnchoredAtom3712 chi ∧
      ¬Fin15AnchoredAtom3715 chi ∧
      ¬Fin15AnchoredAtom3716 chi ∧
      ¬Fin15AnchoredAtom3723 chi ∧
      ¬Fin15AnchoredAtom3726 chi ∧
      ¬Fin15AnchoredAtom3727 chi ∧
      ¬Fin15AnchoredAtom3730 chi ∧
      ¬Fin15AnchoredAtom3731 chi ∧
      ¬Fin15AnchoredAtom3737 chi ∧
      ¬Fin15AnchoredAtom3772 chi ∧
      ¬Fin15AnchoredAtom3775 chi ∧
      ¬Fin15AnchoredAtom3776 chi ∧
      ¬Fin15AnchoredAtom3779 chi ∧
      ¬Fin15AnchoredAtom3780 chi ∧
      ¬Fin15AnchoredAtom3786 chi ∧
      ¬Fin15AnchoredAtom3804 chi ∧
      ¬Fin15AnchoredAtom3805 chi ∧
      ¬Fin15AnchoredAtom3811 chi ∧
      ¬Fin15AnchoredAtom3817 chi ∧
      ¬Fin15AnchoredAtom3856 chi ∧
      ¬Fin15AnchoredAtom3859 chi ∧
      ¬Fin15AnchoredAtom3860 chi ∧
      ¬Fin15AnchoredAtom3863 chi ∧
      ¬Fin15AnchoredAtom3864 chi ∧
      ¬Fin15AnchoredAtom3870 chi ∧
      ¬Fin15AnchoredAtom3888 chi ∧
      ¬Fin15AnchoredAtom3889 chi ∧
      ¬Fin15AnchoredAtom3895 chi ∧
      ¬Fin15AnchoredAtom3901 chi ∧
      ¬Fin15AnchoredAtom3979 chi ∧
      ¬Fin15AnchoredAtom3980 chi ∧
      ¬Fin15AnchoredAtom3986 chi ∧
      ¬Fin15AnchoredAtom3992 chi ∧
      ¬Fin15AnchoredAtom4022 chi ∧
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
  refine ⟨{2, 4, 5, 7, 9, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26292
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3711 Fin15AnchoredAtom3712 Fin15AnchoredAtom3715
    Fin15AnchoredAtom3716 Fin15AnchoredAtom3723 Fin15AnchoredAtom3726 Fin15AnchoredAtom3727
    Fin15AnchoredAtom3730 Fin15AnchoredAtom3731 Fin15AnchoredAtom3737 Fin15AnchoredAtom3772
    Fin15AnchoredAtom3775 Fin15AnchoredAtom3776 Fin15AnchoredAtom3779 Fin15AnchoredAtom3780
    Fin15AnchoredAtom3786 Fin15AnchoredAtom3804 Fin15AnchoredAtom3805 Fin15AnchoredAtom3811
    Fin15AnchoredAtom3817 Fin15AnchoredAtom3856 Fin15AnchoredAtom3859 Fin15AnchoredAtom3860
    Fin15AnchoredAtom3863 Fin15AnchoredAtom3864 Fin15AnchoredAtom3870 Fin15AnchoredAtom3888
    Fin15AnchoredAtom3889 Fin15AnchoredAtom3895 Fin15AnchoredAtom3901 Fin15AnchoredAtom3979
    Fin15AnchoredAtom3980 Fin15AnchoredAtom3986 Fin15AnchoredAtom3992 Fin15AnchoredAtom4022
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

theorem fin15Anchored_clause32103 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3711 chi ∧
      ¬Fin15AnchoredAtom3713 chi ∧
      ¬Fin15AnchoredAtom3714 chi ∧
      ¬Fin15AnchoredAtom3715 chi ∧
      ¬Fin15AnchoredAtom3724 chi ∧
      ¬Fin15AnchoredAtom3725 chi ∧
      ¬Fin15AnchoredAtom3726 chi ∧
      ¬Fin15AnchoredAtom3732 chi ∧
      ¬Fin15AnchoredAtom3733 chi ∧
      ¬Fin15AnchoredAtom3735 chi ∧
      ¬Fin15AnchoredAtom3773 chi ∧
      ¬Fin15AnchoredAtom3774 chi ∧
      ¬Fin15AnchoredAtom3775 chi ∧
      ¬Fin15AnchoredAtom3781 chi ∧
      ¬Fin15AnchoredAtom3782 chi ∧
      ¬Fin15AnchoredAtom3784 chi ∧
      ¬Fin15AnchoredAtom3806 chi ∧
      ¬Fin15AnchoredAtom3807 chi ∧
      ¬Fin15AnchoredAtom3809 chi ∧
      ¬Fin15AnchoredAtom3818 chi ∧
      ¬Fin15AnchoredAtom3857 chi ∧
      ¬Fin15AnchoredAtom3858 chi ∧
      ¬Fin15AnchoredAtom3859 chi ∧
      ¬Fin15AnchoredAtom3865 chi ∧
      ¬Fin15AnchoredAtom3866 chi ∧
      ¬Fin15AnchoredAtom3868 chi ∧
      ¬Fin15AnchoredAtom3890 chi ∧
      ¬Fin15AnchoredAtom3891 chi ∧
      ¬Fin15AnchoredAtom3893 chi ∧
      ¬Fin15AnchoredAtom3902 chi ∧
      ¬Fin15AnchoredAtom3981 chi ∧
      ¬Fin15AnchoredAtom3982 chi ∧
      ¬Fin15AnchoredAtom3984 chi ∧
      ¬Fin15AnchoredAtom3993 chi ∧
      ¬Fin15AnchoredAtom4023 chi ∧
      ¬Fin15AnchoredAtom4397 chi ∧
      ¬Fin15AnchoredAtom4398 chi ∧
      ¬Fin15AnchoredAtom4399 chi ∧
      ¬Fin15AnchoredAtom4405 chi ∧
      ¬Fin15AnchoredAtom4406 chi ∧
      ¬Fin15AnchoredAtom4408 chi ∧
      ¬Fin15AnchoredAtom4430 chi ∧
      ¬Fin15AnchoredAtom4431 chi ∧
      ¬Fin15AnchoredAtom4433 chi ∧
      ¬Fin15AnchoredAtom4442 chi ∧
      ¬Fin15AnchoredAtom4521 chi ∧
      ¬Fin15AnchoredAtom4522 chi ∧
      ¬Fin15AnchoredAtom4524 chi ∧
      ¬Fin15AnchoredAtom4533 chi ∧
      ¬Fin15AnchoredAtom4563 chi ∧
      ¬Fin15AnchoredAtom4647 chi ∧
      ¬Fin15AnchoredAtom4648 chi ∧
      ¬Fin15AnchoredAtom4650 chi ∧
      ¬Fin15AnchoredAtom4659 chi ∧
      ¬Fin15AnchoredAtom4689 chi ∧
      ¬Fin15AnchoredAtom4794 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 4, 5, 7, 9, 11, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask15028
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3711 Fin15AnchoredAtom3713 Fin15AnchoredAtom3714
    Fin15AnchoredAtom3715 Fin15AnchoredAtom3724 Fin15AnchoredAtom3725 Fin15AnchoredAtom3726
    Fin15AnchoredAtom3732 Fin15AnchoredAtom3733 Fin15AnchoredAtom3735 Fin15AnchoredAtom3773
    Fin15AnchoredAtom3774 Fin15AnchoredAtom3775 Fin15AnchoredAtom3781 Fin15AnchoredAtom3782
    Fin15AnchoredAtom3784 Fin15AnchoredAtom3806 Fin15AnchoredAtom3807 Fin15AnchoredAtom3809
    Fin15AnchoredAtom3818 Fin15AnchoredAtom3857 Fin15AnchoredAtom3858 Fin15AnchoredAtom3859
    Fin15AnchoredAtom3865 Fin15AnchoredAtom3866 Fin15AnchoredAtom3868 Fin15AnchoredAtom3890
    Fin15AnchoredAtom3891 Fin15AnchoredAtom3893 Fin15AnchoredAtom3902 Fin15AnchoredAtom3981
    Fin15AnchoredAtom3982 Fin15AnchoredAtom3984 Fin15AnchoredAtom3993 Fin15AnchoredAtom4023
    Fin15AnchoredAtom4397 Fin15AnchoredAtom4398 Fin15AnchoredAtom4399 Fin15AnchoredAtom4405
    Fin15AnchoredAtom4406 Fin15AnchoredAtom4408 Fin15AnchoredAtom4430 Fin15AnchoredAtom4431
    Fin15AnchoredAtom4433 Fin15AnchoredAtom4442 Fin15AnchoredAtom4521 Fin15AnchoredAtom4522
    Fin15AnchoredAtom4524 Fin15AnchoredAtom4533 Fin15AnchoredAtom4563 Fin15AnchoredAtom4647
    Fin15AnchoredAtom4648 Fin15AnchoredAtom4650 Fin15AnchoredAtom4659 Fin15AnchoredAtom4689
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

theorem fin15Anchored_clause32104 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3711 chi ∧
      ¬Fin15AnchoredAtom3714 chi ∧
      ¬Fin15AnchoredAtom3715 chi ∧
      ¬Fin15AnchoredAtom3716 chi ∧
      ¬Fin15AnchoredAtom3725 chi ∧
      ¬Fin15AnchoredAtom3726 chi ∧
      ¬Fin15AnchoredAtom3727 chi ∧
      ¬Fin15AnchoredAtom3735 chi ∧
      ¬Fin15AnchoredAtom3736 chi ∧
      ¬Fin15AnchoredAtom3737 chi ∧
      ¬Fin15AnchoredAtom3774 chi ∧
      ¬Fin15AnchoredAtom3775 chi ∧
      ¬Fin15AnchoredAtom3776 chi ∧
      ¬Fin15AnchoredAtom3784 chi ∧
      ¬Fin15AnchoredAtom3785 chi ∧
      ¬Fin15AnchoredAtom3786 chi ∧
      ¬Fin15AnchoredAtom3809 chi ∧
      ¬Fin15AnchoredAtom3810 chi ∧
      ¬Fin15AnchoredAtom3811 chi ∧
      ¬Fin15AnchoredAtom3821 chi ∧
      ¬Fin15AnchoredAtom3858 chi ∧
      ¬Fin15AnchoredAtom3859 chi ∧
      ¬Fin15AnchoredAtom3860 chi ∧
      ¬Fin15AnchoredAtom3868 chi ∧
      ¬Fin15AnchoredAtom3869 chi ∧
      ¬Fin15AnchoredAtom3870 chi ∧
      ¬Fin15AnchoredAtom3893 chi ∧
      ¬Fin15AnchoredAtom3894 chi ∧
      ¬Fin15AnchoredAtom3895 chi ∧
      ¬Fin15AnchoredAtom3905 chi ∧
      ¬Fin15AnchoredAtom3984 chi ∧
      ¬Fin15AnchoredAtom3985 chi ∧
      ¬Fin15AnchoredAtom3986 chi ∧
      ¬Fin15AnchoredAtom3996 chi ∧
      ¬Fin15AnchoredAtom4026 chi ∧
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
  refine ⟨{2, 4, 5, 7, 9, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29364
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3711 Fin15AnchoredAtom3714 Fin15AnchoredAtom3715
    Fin15AnchoredAtom3716 Fin15AnchoredAtom3725 Fin15AnchoredAtom3726 Fin15AnchoredAtom3727
    Fin15AnchoredAtom3735 Fin15AnchoredAtom3736 Fin15AnchoredAtom3737 Fin15AnchoredAtom3774
    Fin15AnchoredAtom3775 Fin15AnchoredAtom3776 Fin15AnchoredAtom3784 Fin15AnchoredAtom3785
    Fin15AnchoredAtom3786 Fin15AnchoredAtom3809 Fin15AnchoredAtom3810 Fin15AnchoredAtom3811
    Fin15AnchoredAtom3821 Fin15AnchoredAtom3858 Fin15AnchoredAtom3859 Fin15AnchoredAtom3860
    Fin15AnchoredAtom3868 Fin15AnchoredAtom3869 Fin15AnchoredAtom3870 Fin15AnchoredAtom3893
    Fin15AnchoredAtom3894 Fin15AnchoredAtom3895 Fin15AnchoredAtom3905 Fin15AnchoredAtom3984
    Fin15AnchoredAtom3985 Fin15AnchoredAtom3986 Fin15AnchoredAtom3996 Fin15AnchoredAtom4026
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

theorem fin15Anchored_clause32105 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3712 chi ∧
      ¬Fin15AnchoredAtom3714 chi ∧
      ¬Fin15AnchoredAtom3715 chi ∧
      ¬Fin15AnchoredAtom3716 chi ∧
      ¬Fin15AnchoredAtom3729 chi ∧
      ¬Fin15AnchoredAtom3730 chi ∧
      ¬Fin15AnchoredAtom3731 chi ∧
      ¬Fin15AnchoredAtom3735 chi ∧
      ¬Fin15AnchoredAtom3736 chi ∧
      ¬Fin15AnchoredAtom3737 chi ∧
      ¬Fin15AnchoredAtom3778 chi ∧
      ¬Fin15AnchoredAtom3779 chi ∧
      ¬Fin15AnchoredAtom3780 chi ∧
      ¬Fin15AnchoredAtom3784 chi ∧
      ¬Fin15AnchoredAtom3785 chi ∧
      ¬Fin15AnchoredAtom3786 chi ∧
      ¬Fin15AnchoredAtom3815 chi ∧
      ¬Fin15AnchoredAtom3816 chi ∧
      ¬Fin15AnchoredAtom3817 chi ∧
      ¬Fin15AnchoredAtom3821 chi ∧
      ¬Fin15AnchoredAtom3862 chi ∧
      ¬Fin15AnchoredAtom3863 chi ∧
      ¬Fin15AnchoredAtom3864 chi ∧
      ¬Fin15AnchoredAtom3868 chi ∧
      ¬Fin15AnchoredAtom3869 chi ∧
      ¬Fin15AnchoredAtom3870 chi ∧
      ¬Fin15AnchoredAtom3899 chi ∧
      ¬Fin15AnchoredAtom3900 chi ∧
      ¬Fin15AnchoredAtom3901 chi ∧
      ¬Fin15AnchoredAtom3905 chi ∧
      ¬Fin15AnchoredAtom3990 chi ∧
      ¬Fin15AnchoredAtom3991 chi ∧
      ¬Fin15AnchoredAtom3992 chi ∧
      ¬Fin15AnchoredAtom3996 chi ∧
      ¬Fin15AnchoredAtom4030 chi ∧
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
  refine ⟨{2, 4, 5, 7, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29876
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3712 Fin15AnchoredAtom3714 Fin15AnchoredAtom3715
    Fin15AnchoredAtom3716 Fin15AnchoredAtom3729 Fin15AnchoredAtom3730 Fin15AnchoredAtom3731
    Fin15AnchoredAtom3735 Fin15AnchoredAtom3736 Fin15AnchoredAtom3737 Fin15AnchoredAtom3778
    Fin15AnchoredAtom3779 Fin15AnchoredAtom3780 Fin15AnchoredAtom3784 Fin15AnchoredAtom3785
    Fin15AnchoredAtom3786 Fin15AnchoredAtom3815 Fin15AnchoredAtom3816 Fin15AnchoredAtom3817
    Fin15AnchoredAtom3821 Fin15AnchoredAtom3862 Fin15AnchoredAtom3863 Fin15AnchoredAtom3864
    Fin15AnchoredAtom3868 Fin15AnchoredAtom3869 Fin15AnchoredAtom3870 Fin15AnchoredAtom3899
    Fin15AnchoredAtom3900 Fin15AnchoredAtom3901 Fin15AnchoredAtom3905 Fin15AnchoredAtom3990
    Fin15AnchoredAtom3991 Fin15AnchoredAtom3992 Fin15AnchoredAtom3996 Fin15AnchoredAtom4030
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

theorem fin15Anchored_clause32106 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3723 chi ∧
      ¬Fin15AnchoredAtom3725 chi ∧
      ¬Fin15AnchoredAtom3726 chi ∧
      ¬Fin15AnchoredAtom3727 chi ∧
      ¬Fin15AnchoredAtom3729 chi ∧
      ¬Fin15AnchoredAtom3730 chi ∧
      ¬Fin15AnchoredAtom3731 chi ∧
      ¬Fin15AnchoredAtom3735 chi ∧
      ¬Fin15AnchoredAtom3736 chi ∧
      ¬Fin15AnchoredAtom3737 chi ∧
      ¬Fin15AnchoredAtom3803 chi ∧
      ¬Fin15AnchoredAtom3804 chi ∧
      ¬Fin15AnchoredAtom3805 chi ∧
      ¬Fin15AnchoredAtom3809 chi ∧
      ¬Fin15AnchoredAtom3810 chi ∧
      ¬Fin15AnchoredAtom3811 chi ∧
      ¬Fin15AnchoredAtom3815 chi ∧
      ¬Fin15AnchoredAtom3816 chi ∧
      ¬Fin15AnchoredAtom3817 chi ∧
      ¬Fin15AnchoredAtom3821 chi ∧
      ¬Fin15AnchoredAtom3887 chi ∧
      ¬Fin15AnchoredAtom3888 chi ∧
      ¬Fin15AnchoredAtom3889 chi ∧
      ¬Fin15AnchoredAtom3893 chi ∧
      ¬Fin15AnchoredAtom3894 chi ∧
      ¬Fin15AnchoredAtom3895 chi ∧
      ¬Fin15AnchoredAtom3899 chi ∧
      ¬Fin15AnchoredAtom3900 chi ∧
      ¬Fin15AnchoredAtom3901 chi ∧
      ¬Fin15AnchoredAtom3905 chi ∧
      ¬Fin15AnchoredAtom4020 chi ∧
      ¬Fin15AnchoredAtom4021 chi ∧
      ¬Fin15AnchoredAtom4022 chi ∧
      ¬Fin15AnchoredAtom4026 chi ∧
      ¬Fin15AnchoredAtom4030 chi ∧
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
  refine ⟨{2, 4, 5, 9, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask30260
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3723 Fin15AnchoredAtom3725 Fin15AnchoredAtom3726
    Fin15AnchoredAtom3727 Fin15AnchoredAtom3729 Fin15AnchoredAtom3730 Fin15AnchoredAtom3731
    Fin15AnchoredAtom3735 Fin15AnchoredAtom3736 Fin15AnchoredAtom3737 Fin15AnchoredAtom3803
    Fin15AnchoredAtom3804 Fin15AnchoredAtom3805 Fin15AnchoredAtom3809 Fin15AnchoredAtom3810
    Fin15AnchoredAtom3811 Fin15AnchoredAtom3815 Fin15AnchoredAtom3816 Fin15AnchoredAtom3817
    Fin15AnchoredAtom3821 Fin15AnchoredAtom3887 Fin15AnchoredAtom3888 Fin15AnchoredAtom3889
    Fin15AnchoredAtom3893 Fin15AnchoredAtom3894 Fin15AnchoredAtom3895 Fin15AnchoredAtom3899
    Fin15AnchoredAtom3900 Fin15AnchoredAtom3901 Fin15AnchoredAtom3905 Fin15AnchoredAtom4020
    Fin15AnchoredAtom4021 Fin15AnchoredAtom4022 Fin15AnchoredAtom4026 Fin15AnchoredAtom4030
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

theorem fin15Anchored_clause32107 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3739 chi ∧
      ¬Fin15AnchoredAtom3740 chi ∧
      ¬Fin15AnchoredAtom3741 chi ∧
      ¬Fin15AnchoredAtom3744 chi ∧
      ¬Fin15AnchoredAtom3751 chi ∧
      ¬Fin15AnchoredAtom3752 chi ∧
      ¬Fin15AnchoredAtom3755 chi ∧
      ¬Fin15AnchoredAtom3756 chi ∧
      ¬Fin15AnchoredAtom3759 chi ∧
      ¬Fin15AnchoredAtom3762 chi ∧
      ¬Fin15AnchoredAtom3772 chi ∧
      ¬Fin15AnchoredAtom3773 chi ∧
      ¬Fin15AnchoredAtom3776 chi ∧
      ¬Fin15AnchoredAtom3777 chi ∧
      ¬Fin15AnchoredAtom3780 chi ∧
      ¬Fin15AnchoredAtom3783 chi ∧
      ¬Fin15AnchoredAtom3802 chi ∧
      ¬Fin15AnchoredAtom3805 chi ∧
      ¬Fin15AnchoredAtom3808 chi ∧
      ¬Fin15AnchoredAtom3814 chi ∧
      ¬Fin15AnchoredAtom3912 chi ∧
      ¬Fin15AnchoredAtom3913 chi ∧
      ¬Fin15AnchoredAtom3916 chi ∧
      ¬Fin15AnchoredAtom3917 chi ∧
      ¬Fin15AnchoredAtom3920 chi ∧
      ¬Fin15AnchoredAtom3923 chi ∧
      ¬Fin15AnchoredAtom3942 chi ∧
      ¬Fin15AnchoredAtom3945 chi ∧
      ¬Fin15AnchoredAtom3948 chi ∧
      ¬Fin15AnchoredAtom3954 chi ∧
      ¬Fin15AnchoredAtom3977 chi ∧
      ¬Fin15AnchoredAtom3980 chi ∧
      ¬Fin15AnchoredAtom3983 chi ∧
      ¬Fin15AnchoredAtom3989 chi ∧
      ¬Fin15AnchoredAtom4019 chi ∧
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
  refine ⟨{2, 4, 6, 7, 9, 10, 11, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask20180
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3739 Fin15AnchoredAtom3740 Fin15AnchoredAtom3741
    Fin15AnchoredAtom3744 Fin15AnchoredAtom3751 Fin15AnchoredAtom3752 Fin15AnchoredAtom3755
    Fin15AnchoredAtom3756 Fin15AnchoredAtom3759 Fin15AnchoredAtom3762 Fin15AnchoredAtom3772
    Fin15AnchoredAtom3773 Fin15AnchoredAtom3776 Fin15AnchoredAtom3777 Fin15AnchoredAtom3780
    Fin15AnchoredAtom3783 Fin15AnchoredAtom3802 Fin15AnchoredAtom3805 Fin15AnchoredAtom3808
    Fin15AnchoredAtom3814 Fin15AnchoredAtom3912 Fin15AnchoredAtom3913 Fin15AnchoredAtom3916
    Fin15AnchoredAtom3917 Fin15AnchoredAtom3920 Fin15AnchoredAtom3923 Fin15AnchoredAtom3942
    Fin15AnchoredAtom3945 Fin15AnchoredAtom3948 Fin15AnchoredAtom3954 Fin15AnchoredAtom3977
    Fin15AnchoredAtom3980 Fin15AnchoredAtom3983 Fin15AnchoredAtom3989 Fin15AnchoredAtom4019
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

theorem fin15Anchored_clause32108 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3739 chi ∧
      ¬Fin15AnchoredAtom3740 chi ∧
      ¬Fin15AnchoredAtom3742 chi ∧
      ¬Fin15AnchoredAtom3743 chi ∧
      ¬Fin15AnchoredAtom3751 chi ∧
      ¬Fin15AnchoredAtom3753 chi ∧
      ¬Fin15AnchoredAtom3754 chi ∧
      ¬Fin15AnchoredAtom3757 chi ∧
      ¬Fin15AnchoredAtom3758 chi ∧
      ¬Fin15AnchoredAtom3763 chi ∧
      ¬Fin15AnchoredAtom3772 chi ∧
      ¬Fin15AnchoredAtom3774 chi ∧
      ¬Fin15AnchoredAtom3775 chi ∧
      ¬Fin15AnchoredAtom3778 chi ∧
      ¬Fin15AnchoredAtom3779 chi ∧
      ¬Fin15AnchoredAtom3784 chi ∧
      ¬Fin15AnchoredAtom3803 chi ∧
      ¬Fin15AnchoredAtom3804 chi ∧
      ¬Fin15AnchoredAtom3809 chi ∧
      ¬Fin15AnchoredAtom3815 chi ∧
      ¬Fin15AnchoredAtom3912 chi ∧
      ¬Fin15AnchoredAtom3914 chi ∧
      ¬Fin15AnchoredAtom3915 chi ∧
      ¬Fin15AnchoredAtom3918 chi ∧
      ¬Fin15AnchoredAtom3919 chi ∧
      ¬Fin15AnchoredAtom3924 chi ∧
      ¬Fin15AnchoredAtom3943 chi ∧
      ¬Fin15AnchoredAtom3944 chi ∧
      ¬Fin15AnchoredAtom3949 chi ∧
      ¬Fin15AnchoredAtom3955 chi ∧
      ¬Fin15AnchoredAtom3978 chi ∧
      ¬Fin15AnchoredAtom3979 chi ∧
      ¬Fin15AnchoredAtom3984 chi ∧
      ¬Fin15AnchoredAtom3990 chi ∧
      ¬Fin15AnchoredAtom4020 chi ∧
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
  refine ⟨{2, 4, 6, 7, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask14036
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3739 Fin15AnchoredAtom3740 Fin15AnchoredAtom3742
    Fin15AnchoredAtom3743 Fin15AnchoredAtom3751 Fin15AnchoredAtom3753 Fin15AnchoredAtom3754
    Fin15AnchoredAtom3757 Fin15AnchoredAtom3758 Fin15AnchoredAtom3763 Fin15AnchoredAtom3772
    Fin15AnchoredAtom3774 Fin15AnchoredAtom3775 Fin15AnchoredAtom3778 Fin15AnchoredAtom3779
    Fin15AnchoredAtom3784 Fin15AnchoredAtom3803 Fin15AnchoredAtom3804 Fin15AnchoredAtom3809
    Fin15AnchoredAtom3815 Fin15AnchoredAtom3912 Fin15AnchoredAtom3914 Fin15AnchoredAtom3915
    Fin15AnchoredAtom3918 Fin15AnchoredAtom3919 Fin15AnchoredAtom3924 Fin15AnchoredAtom3943
    Fin15AnchoredAtom3944 Fin15AnchoredAtom3949 Fin15AnchoredAtom3955 Fin15AnchoredAtom3978
    Fin15AnchoredAtom3979 Fin15AnchoredAtom3984 Fin15AnchoredAtom3990 Fin15AnchoredAtom4020
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

theorem fin15Anchored_clause32109 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3739 chi ∧
      ¬Fin15AnchoredAtom3740 chi ∧
      ¬Fin15AnchoredAtom3742 chi ∧
      ¬Fin15AnchoredAtom3744 chi ∧
      ¬Fin15AnchoredAtom3751 chi ∧
      ¬Fin15AnchoredAtom3753 chi ∧
      ¬Fin15AnchoredAtom3755 chi ∧
      ¬Fin15AnchoredAtom3757 chi ∧
      ¬Fin15AnchoredAtom3759 chi ∧
      ¬Fin15AnchoredAtom3764 chi ∧
      ¬Fin15AnchoredAtom3772 chi ∧
      ¬Fin15AnchoredAtom3774 chi ∧
      ¬Fin15AnchoredAtom3776 chi ∧
      ¬Fin15AnchoredAtom3778 chi ∧
      ¬Fin15AnchoredAtom3780 chi ∧
      ¬Fin15AnchoredAtom3785 chi ∧
      ¬Fin15AnchoredAtom3803 chi ∧
      ¬Fin15AnchoredAtom3805 chi ∧
      ¬Fin15AnchoredAtom3810 chi ∧
      ¬Fin15AnchoredAtom3816 chi ∧
      ¬Fin15AnchoredAtom3912 chi ∧
      ¬Fin15AnchoredAtom3914 chi ∧
      ¬Fin15AnchoredAtom3916 chi ∧
      ¬Fin15AnchoredAtom3918 chi ∧
      ¬Fin15AnchoredAtom3920 chi ∧
      ¬Fin15AnchoredAtom3925 chi ∧
      ¬Fin15AnchoredAtom3943 chi ∧
      ¬Fin15AnchoredAtom3945 chi ∧
      ¬Fin15AnchoredAtom3950 chi ∧
      ¬Fin15AnchoredAtom3956 chi ∧
      ¬Fin15AnchoredAtom3978 chi ∧
      ¬Fin15AnchoredAtom3980 chi ∧
      ¬Fin15AnchoredAtom3985 chi ∧
      ¬Fin15AnchoredAtom3991 chi ∧
      ¬Fin15AnchoredAtom4021 chi ∧
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
  refine ⟨{2, 4, 6, 7, 9, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22228
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3739 Fin15AnchoredAtom3740 Fin15AnchoredAtom3742
    Fin15AnchoredAtom3744 Fin15AnchoredAtom3751 Fin15AnchoredAtom3753 Fin15AnchoredAtom3755
    Fin15AnchoredAtom3757 Fin15AnchoredAtom3759 Fin15AnchoredAtom3764 Fin15AnchoredAtom3772
    Fin15AnchoredAtom3774 Fin15AnchoredAtom3776 Fin15AnchoredAtom3778 Fin15AnchoredAtom3780
    Fin15AnchoredAtom3785 Fin15AnchoredAtom3803 Fin15AnchoredAtom3805 Fin15AnchoredAtom3810
    Fin15AnchoredAtom3816 Fin15AnchoredAtom3912 Fin15AnchoredAtom3914 Fin15AnchoredAtom3916
    Fin15AnchoredAtom3918 Fin15AnchoredAtom3920 Fin15AnchoredAtom3925 Fin15AnchoredAtom3943
    Fin15AnchoredAtom3945 Fin15AnchoredAtom3950 Fin15AnchoredAtom3956 Fin15AnchoredAtom3978
    Fin15AnchoredAtom3980 Fin15AnchoredAtom3985 Fin15AnchoredAtom3991 Fin15AnchoredAtom4021
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

theorem fin15Anchored_clause32110 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3739 chi ∧
      ¬Fin15AnchoredAtom3740 chi ∧
      ¬Fin15AnchoredAtom3743 chi ∧
      ¬Fin15AnchoredAtom3744 chi ∧
      ¬Fin15AnchoredAtom3751 chi ∧
      ¬Fin15AnchoredAtom3754 chi ∧
      ¬Fin15AnchoredAtom3755 chi ∧
      ¬Fin15AnchoredAtom3758 chi ∧
      ¬Fin15AnchoredAtom3759 chi ∧
      ¬Fin15AnchoredAtom3765 chi ∧
      ¬Fin15AnchoredAtom3772 chi ∧
      ¬Fin15AnchoredAtom3775 chi ∧
      ¬Fin15AnchoredAtom3776 chi ∧
      ¬Fin15AnchoredAtom3779 chi ∧
      ¬Fin15AnchoredAtom3780 chi ∧
      ¬Fin15AnchoredAtom3786 chi ∧
      ¬Fin15AnchoredAtom3804 chi ∧
      ¬Fin15AnchoredAtom3805 chi ∧
      ¬Fin15AnchoredAtom3811 chi ∧
      ¬Fin15AnchoredAtom3817 chi ∧
      ¬Fin15AnchoredAtom3912 chi ∧
      ¬Fin15AnchoredAtom3915 chi ∧
      ¬Fin15AnchoredAtom3916 chi ∧
      ¬Fin15AnchoredAtom3919 chi ∧
      ¬Fin15AnchoredAtom3920 chi ∧
      ¬Fin15AnchoredAtom3926 chi ∧
      ¬Fin15AnchoredAtom3944 chi ∧
      ¬Fin15AnchoredAtom3945 chi ∧
      ¬Fin15AnchoredAtom3951 chi ∧
      ¬Fin15AnchoredAtom3957 chi ∧
      ¬Fin15AnchoredAtom3979 chi ∧
      ¬Fin15AnchoredAtom3980 chi ∧
      ¬Fin15AnchoredAtom3986 chi ∧
      ¬Fin15AnchoredAtom3992 chi ∧
      ¬Fin15AnchoredAtom4022 chi ∧
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
  refine ⟨{2, 4, 6, 7, 9, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26324
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3739 Fin15AnchoredAtom3740 Fin15AnchoredAtom3743
    Fin15AnchoredAtom3744 Fin15AnchoredAtom3751 Fin15AnchoredAtom3754 Fin15AnchoredAtom3755
    Fin15AnchoredAtom3758 Fin15AnchoredAtom3759 Fin15AnchoredAtom3765 Fin15AnchoredAtom3772
    Fin15AnchoredAtom3775 Fin15AnchoredAtom3776 Fin15AnchoredAtom3779 Fin15AnchoredAtom3780
    Fin15AnchoredAtom3786 Fin15AnchoredAtom3804 Fin15AnchoredAtom3805 Fin15AnchoredAtom3811
    Fin15AnchoredAtom3817 Fin15AnchoredAtom3912 Fin15AnchoredAtom3915 Fin15AnchoredAtom3916
    Fin15AnchoredAtom3919 Fin15AnchoredAtom3920 Fin15AnchoredAtom3926 Fin15AnchoredAtom3944
    Fin15AnchoredAtom3945 Fin15AnchoredAtom3951 Fin15AnchoredAtom3957 Fin15AnchoredAtom3979
    Fin15AnchoredAtom3980 Fin15AnchoredAtom3986 Fin15AnchoredAtom3992 Fin15AnchoredAtom4022
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

theorem fin15Anchored_clause32111 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3739 chi ∧
      ¬Fin15AnchoredAtom3742 chi ∧
      ¬Fin15AnchoredAtom3743 chi ∧
      ¬Fin15AnchoredAtom3744 chi ∧
      ¬Fin15AnchoredAtom3753 chi ∧
      ¬Fin15AnchoredAtom3754 chi ∧
      ¬Fin15AnchoredAtom3755 chi ∧
      ¬Fin15AnchoredAtom3763 chi ∧
      ¬Fin15AnchoredAtom3764 chi ∧
      ¬Fin15AnchoredAtom3765 chi ∧
      ¬Fin15AnchoredAtom3774 chi ∧
      ¬Fin15AnchoredAtom3775 chi ∧
      ¬Fin15AnchoredAtom3776 chi ∧
      ¬Fin15AnchoredAtom3784 chi ∧
      ¬Fin15AnchoredAtom3785 chi ∧
      ¬Fin15AnchoredAtom3786 chi ∧
      ¬Fin15AnchoredAtom3809 chi ∧
      ¬Fin15AnchoredAtom3810 chi ∧
      ¬Fin15AnchoredAtom3811 chi ∧
      ¬Fin15AnchoredAtom3821 chi ∧
      ¬Fin15AnchoredAtom3914 chi ∧
      ¬Fin15AnchoredAtom3915 chi ∧
      ¬Fin15AnchoredAtom3916 chi ∧
      ¬Fin15AnchoredAtom3924 chi ∧
      ¬Fin15AnchoredAtom3925 chi ∧
      ¬Fin15AnchoredAtom3926 chi ∧
      ¬Fin15AnchoredAtom3949 chi ∧
      ¬Fin15AnchoredAtom3950 chi ∧
      ¬Fin15AnchoredAtom3951 chi ∧
      ¬Fin15AnchoredAtom3961 chi ∧
      ¬Fin15AnchoredAtom3984 chi ∧
      ¬Fin15AnchoredAtom3985 chi ∧
      ¬Fin15AnchoredAtom3986 chi ∧
      ¬Fin15AnchoredAtom3996 chi ∧
      ¬Fin15AnchoredAtom4026 chi ∧
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
  refine ⟨{2, 4, 6, 7, 9, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29396
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3739 Fin15AnchoredAtom3742 Fin15AnchoredAtom3743
    Fin15AnchoredAtom3744 Fin15AnchoredAtom3753 Fin15AnchoredAtom3754 Fin15AnchoredAtom3755
    Fin15AnchoredAtom3763 Fin15AnchoredAtom3764 Fin15AnchoredAtom3765 Fin15AnchoredAtom3774
    Fin15AnchoredAtom3775 Fin15AnchoredAtom3776 Fin15AnchoredAtom3784 Fin15AnchoredAtom3785
    Fin15AnchoredAtom3786 Fin15AnchoredAtom3809 Fin15AnchoredAtom3810 Fin15AnchoredAtom3811
    Fin15AnchoredAtom3821 Fin15AnchoredAtom3914 Fin15AnchoredAtom3915 Fin15AnchoredAtom3916
    Fin15AnchoredAtom3924 Fin15AnchoredAtom3925 Fin15AnchoredAtom3926 Fin15AnchoredAtom3949
    Fin15AnchoredAtom3950 Fin15AnchoredAtom3951 Fin15AnchoredAtom3961 Fin15AnchoredAtom3984
    Fin15AnchoredAtom3985 Fin15AnchoredAtom3986 Fin15AnchoredAtom3996 Fin15AnchoredAtom4026
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

theorem fin15Anchored_clause32112 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3740 chi ∧
      ¬Fin15AnchoredAtom3742 chi ∧
      ¬Fin15AnchoredAtom3743 chi ∧
      ¬Fin15AnchoredAtom3744 chi ∧
      ¬Fin15AnchoredAtom3757 chi ∧
      ¬Fin15AnchoredAtom3758 chi ∧
      ¬Fin15AnchoredAtom3759 chi ∧
      ¬Fin15AnchoredAtom3763 chi ∧
      ¬Fin15AnchoredAtom3764 chi ∧
      ¬Fin15AnchoredAtom3765 chi ∧
      ¬Fin15AnchoredAtom3778 chi ∧
      ¬Fin15AnchoredAtom3779 chi ∧
      ¬Fin15AnchoredAtom3780 chi ∧
      ¬Fin15AnchoredAtom3784 chi ∧
      ¬Fin15AnchoredAtom3785 chi ∧
      ¬Fin15AnchoredAtom3786 chi ∧
      ¬Fin15AnchoredAtom3815 chi ∧
      ¬Fin15AnchoredAtom3816 chi ∧
      ¬Fin15AnchoredAtom3817 chi ∧
      ¬Fin15AnchoredAtom3821 chi ∧
      ¬Fin15AnchoredAtom3918 chi ∧
      ¬Fin15AnchoredAtom3919 chi ∧
      ¬Fin15AnchoredAtom3920 chi ∧
      ¬Fin15AnchoredAtom3924 chi ∧
      ¬Fin15AnchoredAtom3925 chi ∧
      ¬Fin15AnchoredAtom3926 chi ∧
      ¬Fin15AnchoredAtom3955 chi ∧
      ¬Fin15AnchoredAtom3956 chi ∧
      ¬Fin15AnchoredAtom3957 chi ∧
      ¬Fin15AnchoredAtom3961 chi ∧
      ¬Fin15AnchoredAtom3990 chi ∧
      ¬Fin15AnchoredAtom3991 chi ∧
      ¬Fin15AnchoredAtom3992 chi ∧
      ¬Fin15AnchoredAtom3996 chi ∧
      ¬Fin15AnchoredAtom4030 chi ∧
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
  refine ⟨{2, 4, 6, 7, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29908
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3740 Fin15AnchoredAtom3742 Fin15AnchoredAtom3743
    Fin15AnchoredAtom3744 Fin15AnchoredAtom3757 Fin15AnchoredAtom3758 Fin15AnchoredAtom3759
    Fin15AnchoredAtom3763 Fin15AnchoredAtom3764 Fin15AnchoredAtom3765 Fin15AnchoredAtom3778
    Fin15AnchoredAtom3779 Fin15AnchoredAtom3780 Fin15AnchoredAtom3784 Fin15AnchoredAtom3785
    Fin15AnchoredAtom3786 Fin15AnchoredAtom3815 Fin15AnchoredAtom3816 Fin15AnchoredAtom3817
    Fin15AnchoredAtom3821 Fin15AnchoredAtom3918 Fin15AnchoredAtom3919 Fin15AnchoredAtom3920
    Fin15AnchoredAtom3924 Fin15AnchoredAtom3925 Fin15AnchoredAtom3926 Fin15AnchoredAtom3955
    Fin15AnchoredAtom3956 Fin15AnchoredAtom3957 Fin15AnchoredAtom3961 Fin15AnchoredAtom3990
    Fin15AnchoredAtom3991 Fin15AnchoredAtom3992 Fin15AnchoredAtom3996 Fin15AnchoredAtom4030
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

theorem fin15Anchored_clause32113 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3746 chi ∧
      ¬Fin15AnchoredAtom3748 chi ∧
      ¬Fin15AnchoredAtom3749 chi ∧
      ¬Fin15AnchoredAtom3750 chi ∧
      ¬Fin15AnchoredAtom3757 chi ∧
      ¬Fin15AnchoredAtom3758 chi ∧
      ¬Fin15AnchoredAtom3759 chi ∧
      ¬Fin15AnchoredAtom3763 chi ∧
      ¬Fin15AnchoredAtom3764 chi ∧
      ¬Fin15AnchoredAtom3765 chi ∧
      ¬Fin15AnchoredAtom3793 chi ∧
      ¬Fin15AnchoredAtom3794 chi ∧
      ¬Fin15AnchoredAtom3795 chi ∧
      ¬Fin15AnchoredAtom3799 chi ∧
      ¬Fin15AnchoredAtom3800 chi ∧
      ¬Fin15AnchoredAtom3801 chi ∧
      ¬Fin15AnchoredAtom3815 chi ∧
      ¬Fin15AnchoredAtom3816 chi ∧
      ¬Fin15AnchoredAtom3817 chi ∧
      ¬Fin15AnchoredAtom3821 chi ∧
      ¬Fin15AnchoredAtom3933 chi ∧
      ¬Fin15AnchoredAtom3934 chi ∧
      ¬Fin15AnchoredAtom3935 chi ∧
      ¬Fin15AnchoredAtom3939 chi ∧
      ¬Fin15AnchoredAtom3940 chi ∧
      ¬Fin15AnchoredAtom3941 chi ∧
      ¬Fin15AnchoredAtom3955 chi ∧
      ¬Fin15AnchoredAtom3956 chi ∧
      ¬Fin15AnchoredAtom3957 chi ∧
      ¬Fin15AnchoredAtom3961 chi ∧
      ¬Fin15AnchoredAtom4010 chi ∧
      ¬Fin15AnchoredAtom4011 chi ∧
      ¬Fin15AnchoredAtom4012 chi ∧
      ¬Fin15AnchoredAtom4016 chi ∧
      ¬Fin15AnchoredAtom4030 chi ∧
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
  refine ⟨{2, 4, 6, 8, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask30036
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3746 Fin15AnchoredAtom3748 Fin15AnchoredAtom3749
    Fin15AnchoredAtom3750 Fin15AnchoredAtom3757 Fin15AnchoredAtom3758 Fin15AnchoredAtom3759
    Fin15AnchoredAtom3763 Fin15AnchoredAtom3764 Fin15AnchoredAtom3765 Fin15AnchoredAtom3793
    Fin15AnchoredAtom3794 Fin15AnchoredAtom3795 Fin15AnchoredAtom3799 Fin15AnchoredAtom3800
    Fin15AnchoredAtom3801 Fin15AnchoredAtom3815 Fin15AnchoredAtom3816 Fin15AnchoredAtom3817
    Fin15AnchoredAtom3821 Fin15AnchoredAtom3933 Fin15AnchoredAtom3934 Fin15AnchoredAtom3935
    Fin15AnchoredAtom3939 Fin15AnchoredAtom3940 Fin15AnchoredAtom3941 Fin15AnchoredAtom3955
    Fin15AnchoredAtom3956 Fin15AnchoredAtom3957 Fin15AnchoredAtom3961 Fin15AnchoredAtom4010
    Fin15AnchoredAtom4011 Fin15AnchoredAtom4012 Fin15AnchoredAtom4016 Fin15AnchoredAtom4030
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

theorem fin15Anchored_clause32114 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3751 chi ∧
      ¬Fin15AnchoredAtom3753 chi ∧
      ¬Fin15AnchoredAtom3754 chi ∧
      ¬Fin15AnchoredAtom3755 chi ∧
      ¬Fin15AnchoredAtom3757 chi ∧
      ¬Fin15AnchoredAtom3758 chi ∧
      ¬Fin15AnchoredAtom3759 chi ∧
      ¬Fin15AnchoredAtom3763 chi ∧
      ¬Fin15AnchoredAtom3764 chi ∧
      ¬Fin15AnchoredAtom3765 chi ∧
      ¬Fin15AnchoredAtom3803 chi ∧
      ¬Fin15AnchoredAtom3804 chi ∧
      ¬Fin15AnchoredAtom3805 chi ∧
      ¬Fin15AnchoredAtom3809 chi ∧
      ¬Fin15AnchoredAtom3810 chi ∧
      ¬Fin15AnchoredAtom3811 chi ∧
      ¬Fin15AnchoredAtom3815 chi ∧
      ¬Fin15AnchoredAtom3816 chi ∧
      ¬Fin15AnchoredAtom3817 chi ∧
      ¬Fin15AnchoredAtom3821 chi ∧
      ¬Fin15AnchoredAtom3943 chi ∧
      ¬Fin15AnchoredAtom3944 chi ∧
      ¬Fin15AnchoredAtom3945 chi ∧
      ¬Fin15AnchoredAtom3949 chi ∧
      ¬Fin15AnchoredAtom3950 chi ∧
      ¬Fin15AnchoredAtom3951 chi ∧
      ¬Fin15AnchoredAtom3955 chi ∧
      ¬Fin15AnchoredAtom3956 chi ∧
      ¬Fin15AnchoredAtom3957 chi ∧
      ¬Fin15AnchoredAtom3961 chi ∧
      ¬Fin15AnchoredAtom4020 chi ∧
      ¬Fin15AnchoredAtom4021 chi ∧
      ¬Fin15AnchoredAtom4022 chi ∧
      ¬Fin15AnchoredAtom4026 chi ∧
      ¬Fin15AnchoredAtom4030 chi ∧
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
  refine ⟨{2, 4, 6, 9, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask30292
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3751 Fin15AnchoredAtom3753 Fin15AnchoredAtom3754
    Fin15AnchoredAtom3755 Fin15AnchoredAtom3757 Fin15AnchoredAtom3758 Fin15AnchoredAtom3759
    Fin15AnchoredAtom3763 Fin15AnchoredAtom3764 Fin15AnchoredAtom3765 Fin15AnchoredAtom3803
    Fin15AnchoredAtom3804 Fin15AnchoredAtom3805 Fin15AnchoredAtom3809 Fin15AnchoredAtom3810
    Fin15AnchoredAtom3811 Fin15AnchoredAtom3815 Fin15AnchoredAtom3816 Fin15AnchoredAtom3817
    Fin15AnchoredAtom3821 Fin15AnchoredAtom3943 Fin15AnchoredAtom3944 Fin15AnchoredAtom3945
    Fin15AnchoredAtom3949 Fin15AnchoredAtom3950 Fin15AnchoredAtom3951 Fin15AnchoredAtom3955
    Fin15AnchoredAtom3956 Fin15AnchoredAtom3957 Fin15AnchoredAtom3961 Fin15AnchoredAtom4020
    Fin15AnchoredAtom4021 Fin15AnchoredAtom4022 Fin15AnchoredAtom4026 Fin15AnchoredAtom4030
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

theorem fin15Anchored_clause32115 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3772 chi ∧
      ¬Fin15AnchoredAtom3774 chi ∧
      ¬Fin15AnchoredAtom3775 chi ∧
      ¬Fin15AnchoredAtom3776 chi ∧
      ¬Fin15AnchoredAtom3778 chi ∧
      ¬Fin15AnchoredAtom3779 chi ∧
      ¬Fin15AnchoredAtom3780 chi ∧
      ¬Fin15AnchoredAtom3784 chi ∧
      ¬Fin15AnchoredAtom3785 chi ∧
      ¬Fin15AnchoredAtom3786 chi ∧
      ¬Fin15AnchoredAtom3803 chi ∧
      ¬Fin15AnchoredAtom3804 chi ∧
      ¬Fin15AnchoredAtom3805 chi ∧
      ¬Fin15AnchoredAtom3809 chi ∧
      ¬Fin15AnchoredAtom3810 chi ∧
      ¬Fin15AnchoredAtom3811 chi ∧
      ¬Fin15AnchoredAtom3815 chi ∧
      ¬Fin15AnchoredAtom3816 chi ∧
      ¬Fin15AnchoredAtom3817 chi ∧
      ¬Fin15AnchoredAtom3821 chi ∧
      ¬Fin15AnchoredAtom3978 chi ∧
      ¬Fin15AnchoredAtom3979 chi ∧
      ¬Fin15AnchoredAtom3980 chi ∧
      ¬Fin15AnchoredAtom3984 chi ∧
      ¬Fin15AnchoredAtom3985 chi ∧
      ¬Fin15AnchoredAtom3986 chi ∧
      ¬Fin15AnchoredAtom3990 chi ∧
      ¬Fin15AnchoredAtom3991 chi ∧
      ¬Fin15AnchoredAtom3992 chi ∧
      ¬Fin15AnchoredAtom3996 chi ∧
      ¬Fin15AnchoredAtom4020 chi ∧
      ¬Fin15AnchoredAtom4021 chi ∧
      ¬Fin15AnchoredAtom4022 chi ∧
      ¬Fin15AnchoredAtom4026 chi ∧
      ¬Fin15AnchoredAtom4030 chi ∧
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
  refine ⟨{2, 4, 7, 9, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask30356
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3772 Fin15AnchoredAtom3774 Fin15AnchoredAtom3775
    Fin15AnchoredAtom3776 Fin15AnchoredAtom3778 Fin15AnchoredAtom3779 Fin15AnchoredAtom3780
    Fin15AnchoredAtom3784 Fin15AnchoredAtom3785 Fin15AnchoredAtom3786 Fin15AnchoredAtom3803
    Fin15AnchoredAtom3804 Fin15AnchoredAtom3805 Fin15AnchoredAtom3809 Fin15AnchoredAtom3810
    Fin15AnchoredAtom3811 Fin15AnchoredAtom3815 Fin15AnchoredAtom3816 Fin15AnchoredAtom3817
    Fin15AnchoredAtom3821 Fin15AnchoredAtom3978 Fin15AnchoredAtom3979 Fin15AnchoredAtom3980
    Fin15AnchoredAtom3984 Fin15AnchoredAtom3985 Fin15AnchoredAtom3986 Fin15AnchoredAtom3990
    Fin15AnchoredAtom3991 Fin15AnchoredAtom3992 Fin15AnchoredAtom3996 Fin15AnchoredAtom4020
    Fin15AnchoredAtom4021 Fin15AnchoredAtom4022 Fin15AnchoredAtom4026 Fin15AnchoredAtom4030
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

theorem fin15Anchored_clause32116 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3823 chi ∧
      ¬Fin15AnchoredAtom3824 chi ∧
      ¬Fin15AnchoredAtom3826 chi ∧
      ¬Fin15AnchoredAtom3827 chi ∧
      ¬Fin15AnchoredAtom3835 chi ∧
      ¬Fin15AnchoredAtom3837 chi ∧
      ¬Fin15AnchoredAtom3838 chi ∧
      ¬Fin15AnchoredAtom3841 chi ∧
      ¬Fin15AnchoredAtom3842 chi ∧
      ¬Fin15AnchoredAtom3847 chi ∧
      ¬Fin15AnchoredAtom3856 chi ∧
      ¬Fin15AnchoredAtom3858 chi ∧
      ¬Fin15AnchoredAtom3859 chi ∧
      ¬Fin15AnchoredAtom3862 chi ∧
      ¬Fin15AnchoredAtom3863 chi ∧
      ¬Fin15AnchoredAtom3868 chi ∧
      ¬Fin15AnchoredAtom3887 chi ∧
      ¬Fin15AnchoredAtom3888 chi ∧
      ¬Fin15AnchoredAtom3893 chi ∧
      ¬Fin15AnchoredAtom3899 chi ∧
      ¬Fin15AnchoredAtom3912 chi ∧
      ¬Fin15AnchoredAtom3914 chi ∧
      ¬Fin15AnchoredAtom3915 chi ∧
      ¬Fin15AnchoredAtom3918 chi ∧
      ¬Fin15AnchoredAtom3919 chi ∧
      ¬Fin15AnchoredAtom3924 chi ∧
      ¬Fin15AnchoredAtom3943 chi ∧
      ¬Fin15AnchoredAtom3944 chi ∧
      ¬Fin15AnchoredAtom3949 chi ∧
      ¬Fin15AnchoredAtom3955 chi ∧
      ¬Fin15AnchoredAtom3978 chi ∧
      ¬Fin15AnchoredAtom3979 chi ∧
      ¬Fin15AnchoredAtom3984 chi ∧
      ¬Fin15AnchoredAtom3990 chi ∧
      ¬Fin15AnchoredAtom4020 chi ∧
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
  refine ⟨{2, 5, 6, 7, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask14052
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3823 Fin15AnchoredAtom3824 Fin15AnchoredAtom3826
    Fin15AnchoredAtom3827 Fin15AnchoredAtom3835 Fin15AnchoredAtom3837 Fin15AnchoredAtom3838
    Fin15AnchoredAtom3841 Fin15AnchoredAtom3842 Fin15AnchoredAtom3847 Fin15AnchoredAtom3856
    Fin15AnchoredAtom3858 Fin15AnchoredAtom3859 Fin15AnchoredAtom3862 Fin15AnchoredAtom3863
    Fin15AnchoredAtom3868 Fin15AnchoredAtom3887 Fin15AnchoredAtom3888 Fin15AnchoredAtom3893
    Fin15AnchoredAtom3899 Fin15AnchoredAtom3912 Fin15AnchoredAtom3914 Fin15AnchoredAtom3915
    Fin15AnchoredAtom3918 Fin15AnchoredAtom3919 Fin15AnchoredAtom3924 Fin15AnchoredAtom3943
    Fin15AnchoredAtom3944 Fin15AnchoredAtom3949 Fin15AnchoredAtom3955 Fin15AnchoredAtom3978
    Fin15AnchoredAtom3979 Fin15AnchoredAtom3984 Fin15AnchoredAtom3990 Fin15AnchoredAtom4020
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

theorem fin15Anchored_clause32117 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3823 chi ∧
      ¬Fin15AnchoredAtom3824 chi ∧
      ¬Fin15AnchoredAtom3826 chi ∧
      ¬Fin15AnchoredAtom3828 chi ∧
      ¬Fin15AnchoredAtom3835 chi ∧
      ¬Fin15AnchoredAtom3837 chi ∧
      ¬Fin15AnchoredAtom3839 chi ∧
      ¬Fin15AnchoredAtom3841 chi ∧
      ¬Fin15AnchoredAtom3843 chi ∧
      ¬Fin15AnchoredAtom3848 chi ∧
      ¬Fin15AnchoredAtom3856 chi ∧
      ¬Fin15AnchoredAtom3858 chi ∧
      ¬Fin15AnchoredAtom3860 chi ∧
      ¬Fin15AnchoredAtom3862 chi ∧
      ¬Fin15AnchoredAtom3864 chi ∧
      ¬Fin15AnchoredAtom3869 chi ∧
      ¬Fin15AnchoredAtom3887 chi ∧
      ¬Fin15AnchoredAtom3889 chi ∧
      ¬Fin15AnchoredAtom3894 chi ∧
      ¬Fin15AnchoredAtom3900 chi ∧
      ¬Fin15AnchoredAtom3912 chi ∧
      ¬Fin15AnchoredAtom3914 chi ∧
      ¬Fin15AnchoredAtom3916 chi ∧
      ¬Fin15AnchoredAtom3918 chi ∧
      ¬Fin15AnchoredAtom3920 chi ∧
      ¬Fin15AnchoredAtom3925 chi ∧
      ¬Fin15AnchoredAtom3943 chi ∧
      ¬Fin15AnchoredAtom3945 chi ∧
      ¬Fin15AnchoredAtom3950 chi ∧
      ¬Fin15AnchoredAtom3956 chi ∧
      ¬Fin15AnchoredAtom3978 chi ∧
      ¬Fin15AnchoredAtom3980 chi ∧
      ¬Fin15AnchoredAtom3985 chi ∧
      ¬Fin15AnchoredAtom3991 chi ∧
      ¬Fin15AnchoredAtom4021 chi ∧
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
  refine ⟨{2, 5, 6, 7, 9, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22244
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3823 Fin15AnchoredAtom3824 Fin15AnchoredAtom3826
    Fin15AnchoredAtom3828 Fin15AnchoredAtom3835 Fin15AnchoredAtom3837 Fin15AnchoredAtom3839
    Fin15AnchoredAtom3841 Fin15AnchoredAtom3843 Fin15AnchoredAtom3848 Fin15AnchoredAtom3856
    Fin15AnchoredAtom3858 Fin15AnchoredAtom3860 Fin15AnchoredAtom3862 Fin15AnchoredAtom3864
    Fin15AnchoredAtom3869 Fin15AnchoredAtom3887 Fin15AnchoredAtom3889 Fin15AnchoredAtom3894
    Fin15AnchoredAtom3900 Fin15AnchoredAtom3912 Fin15AnchoredAtom3914 Fin15AnchoredAtom3916
    Fin15AnchoredAtom3918 Fin15AnchoredAtom3920 Fin15AnchoredAtom3925 Fin15AnchoredAtom3943
    Fin15AnchoredAtom3945 Fin15AnchoredAtom3950 Fin15AnchoredAtom3956 Fin15AnchoredAtom3978
    Fin15AnchoredAtom3980 Fin15AnchoredAtom3985 Fin15AnchoredAtom3991 Fin15AnchoredAtom4021
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

theorem fin15Anchored_clause32118 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3823 chi ∧
      ¬Fin15AnchoredAtom3824 chi ∧
      ¬Fin15AnchoredAtom3827 chi ∧
      ¬Fin15AnchoredAtom3828 chi ∧
      ¬Fin15AnchoredAtom3835 chi ∧
      ¬Fin15AnchoredAtom3838 chi ∧
      ¬Fin15AnchoredAtom3839 chi ∧
      ¬Fin15AnchoredAtom3842 chi ∧
      ¬Fin15AnchoredAtom3843 chi ∧
      ¬Fin15AnchoredAtom3849 chi ∧
      ¬Fin15AnchoredAtom3856 chi ∧
      ¬Fin15AnchoredAtom3859 chi ∧
      ¬Fin15AnchoredAtom3860 chi ∧
      ¬Fin15AnchoredAtom3863 chi ∧
      ¬Fin15AnchoredAtom3864 chi ∧
      ¬Fin15AnchoredAtom3870 chi ∧
      ¬Fin15AnchoredAtom3888 chi ∧
      ¬Fin15AnchoredAtom3889 chi ∧
      ¬Fin15AnchoredAtom3895 chi ∧
      ¬Fin15AnchoredAtom3901 chi ∧
      ¬Fin15AnchoredAtom3912 chi ∧
      ¬Fin15AnchoredAtom3915 chi ∧
      ¬Fin15AnchoredAtom3916 chi ∧
      ¬Fin15AnchoredAtom3919 chi ∧
      ¬Fin15AnchoredAtom3920 chi ∧
      ¬Fin15AnchoredAtom3926 chi ∧
      ¬Fin15AnchoredAtom3944 chi ∧
      ¬Fin15AnchoredAtom3945 chi ∧
      ¬Fin15AnchoredAtom3951 chi ∧
      ¬Fin15AnchoredAtom3957 chi ∧
      ¬Fin15AnchoredAtom3979 chi ∧
      ¬Fin15AnchoredAtom3980 chi ∧
      ¬Fin15AnchoredAtom3986 chi ∧
      ¬Fin15AnchoredAtom3992 chi ∧
      ¬Fin15AnchoredAtom4022 chi ∧
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
  refine ⟨{2, 5, 6, 7, 9, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26340
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3823 Fin15AnchoredAtom3824 Fin15AnchoredAtom3827
    Fin15AnchoredAtom3828 Fin15AnchoredAtom3835 Fin15AnchoredAtom3838 Fin15AnchoredAtom3839
    Fin15AnchoredAtom3842 Fin15AnchoredAtom3843 Fin15AnchoredAtom3849 Fin15AnchoredAtom3856
    Fin15AnchoredAtom3859 Fin15AnchoredAtom3860 Fin15AnchoredAtom3863 Fin15AnchoredAtom3864
    Fin15AnchoredAtom3870 Fin15AnchoredAtom3888 Fin15AnchoredAtom3889 Fin15AnchoredAtom3895
    Fin15AnchoredAtom3901 Fin15AnchoredAtom3912 Fin15AnchoredAtom3915 Fin15AnchoredAtom3916
    Fin15AnchoredAtom3919 Fin15AnchoredAtom3920 Fin15AnchoredAtom3926 Fin15AnchoredAtom3944
    Fin15AnchoredAtom3945 Fin15AnchoredAtom3951 Fin15AnchoredAtom3957 Fin15AnchoredAtom3979
    Fin15AnchoredAtom3980 Fin15AnchoredAtom3986 Fin15AnchoredAtom3992 Fin15AnchoredAtom4022
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

theorem fin15Anchored_clause32119 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3823 chi ∧
      ¬Fin15AnchoredAtom3825 chi ∧
      ¬Fin15AnchoredAtom3826 chi ∧
      ¬Fin15AnchoredAtom3827 chi ∧
      ¬Fin15AnchoredAtom3836 chi ∧
      ¬Fin15AnchoredAtom3837 chi ∧
      ¬Fin15AnchoredAtom3838 chi ∧
      ¬Fin15AnchoredAtom3844 chi ∧
      ¬Fin15AnchoredAtom3845 chi ∧
      ¬Fin15AnchoredAtom3847 chi ∧
      ¬Fin15AnchoredAtom3857 chi ∧
      ¬Fin15AnchoredAtom3858 chi ∧
      ¬Fin15AnchoredAtom3859 chi ∧
      ¬Fin15AnchoredAtom3865 chi ∧
      ¬Fin15AnchoredAtom3866 chi ∧
      ¬Fin15AnchoredAtom3868 chi ∧
      ¬Fin15AnchoredAtom3890 chi ∧
      ¬Fin15AnchoredAtom3891 chi ∧
      ¬Fin15AnchoredAtom3893 chi ∧
      ¬Fin15AnchoredAtom3902 chi ∧
      ¬Fin15AnchoredAtom3913 chi ∧
      ¬Fin15AnchoredAtom3914 chi ∧
      ¬Fin15AnchoredAtom3915 chi ∧
      ¬Fin15AnchoredAtom3921 chi ∧
      ¬Fin15AnchoredAtom3922 chi ∧
      ¬Fin15AnchoredAtom3924 chi ∧
      ¬Fin15AnchoredAtom3946 chi ∧
      ¬Fin15AnchoredAtom3947 chi ∧
      ¬Fin15AnchoredAtom3949 chi ∧
      ¬Fin15AnchoredAtom3958 chi ∧
      ¬Fin15AnchoredAtom3981 chi ∧
      ¬Fin15AnchoredAtom3982 chi ∧
      ¬Fin15AnchoredAtom3984 chi ∧
      ¬Fin15AnchoredAtom3993 chi ∧
      ¬Fin15AnchoredAtom4023 chi ∧
      ¬Fin15AnchoredAtom4579 chi ∧
      ¬Fin15AnchoredAtom4580 chi ∧
      ¬Fin15AnchoredAtom4581 chi ∧
      ¬Fin15AnchoredAtom4587 chi ∧
      ¬Fin15AnchoredAtom4588 chi ∧
      ¬Fin15AnchoredAtom4590 chi ∧
      ¬Fin15AnchoredAtom4612 chi ∧
      ¬Fin15AnchoredAtom4613 chi ∧
      ¬Fin15AnchoredAtom4615 chi ∧
      ¬Fin15AnchoredAtom4624 chi ∧
      ¬Fin15AnchoredAtom4647 chi ∧
      ¬Fin15AnchoredAtom4648 chi ∧
      ¬Fin15AnchoredAtom4650 chi ∧
      ¬Fin15AnchoredAtom4659 chi ∧
      ¬Fin15AnchoredAtom4689 chi ∧
      ¬Fin15AnchoredAtom4717 chi ∧
      ¬Fin15AnchoredAtom4718 chi ∧
      ¬Fin15AnchoredAtom4720 chi ∧
      ¬Fin15AnchoredAtom4729 chi ∧
      ¬Fin15AnchoredAtom4759 chi ∧
      ¬Fin15AnchoredAtom4794 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 5, 6, 7, 9, 11, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask15076
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3823 Fin15AnchoredAtom3825 Fin15AnchoredAtom3826
    Fin15AnchoredAtom3827 Fin15AnchoredAtom3836 Fin15AnchoredAtom3837 Fin15AnchoredAtom3838
    Fin15AnchoredAtom3844 Fin15AnchoredAtom3845 Fin15AnchoredAtom3847 Fin15AnchoredAtom3857
    Fin15AnchoredAtom3858 Fin15AnchoredAtom3859 Fin15AnchoredAtom3865 Fin15AnchoredAtom3866
    Fin15AnchoredAtom3868 Fin15AnchoredAtom3890 Fin15AnchoredAtom3891 Fin15AnchoredAtom3893
    Fin15AnchoredAtom3902 Fin15AnchoredAtom3913 Fin15AnchoredAtom3914 Fin15AnchoredAtom3915
    Fin15AnchoredAtom3921 Fin15AnchoredAtom3922 Fin15AnchoredAtom3924 Fin15AnchoredAtom3946
    Fin15AnchoredAtom3947 Fin15AnchoredAtom3949 Fin15AnchoredAtom3958 Fin15AnchoredAtom3981
    Fin15AnchoredAtom3982 Fin15AnchoredAtom3984 Fin15AnchoredAtom3993 Fin15AnchoredAtom4023
    Fin15AnchoredAtom4579 Fin15AnchoredAtom4580 Fin15AnchoredAtom4581 Fin15AnchoredAtom4587
    Fin15AnchoredAtom4588 Fin15AnchoredAtom4590 Fin15AnchoredAtom4612 Fin15AnchoredAtom4613
    Fin15AnchoredAtom4615 Fin15AnchoredAtom4624 Fin15AnchoredAtom4647 Fin15AnchoredAtom4648
    Fin15AnchoredAtom4650 Fin15AnchoredAtom4659 Fin15AnchoredAtom4689 Fin15AnchoredAtom4717
    Fin15AnchoredAtom4718 Fin15AnchoredAtom4720 Fin15AnchoredAtom4729 Fin15AnchoredAtom4759
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

theorem fin15Anchored_clause32120 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3823 chi ∧
      ¬Fin15AnchoredAtom3826 chi ∧
      ¬Fin15AnchoredAtom3827 chi ∧
      ¬Fin15AnchoredAtom3828 chi ∧
      ¬Fin15AnchoredAtom3837 chi ∧
      ¬Fin15AnchoredAtom3838 chi ∧
      ¬Fin15AnchoredAtom3839 chi ∧
      ¬Fin15AnchoredAtom3847 chi ∧
      ¬Fin15AnchoredAtom3848 chi ∧
      ¬Fin15AnchoredAtom3849 chi ∧
      ¬Fin15AnchoredAtom3858 chi ∧
      ¬Fin15AnchoredAtom3859 chi ∧
      ¬Fin15AnchoredAtom3860 chi ∧
      ¬Fin15AnchoredAtom3868 chi ∧
      ¬Fin15AnchoredAtom3869 chi ∧
      ¬Fin15AnchoredAtom3870 chi ∧
      ¬Fin15AnchoredAtom3893 chi ∧
      ¬Fin15AnchoredAtom3894 chi ∧
      ¬Fin15AnchoredAtom3895 chi ∧
      ¬Fin15AnchoredAtom3905 chi ∧
      ¬Fin15AnchoredAtom3914 chi ∧
      ¬Fin15AnchoredAtom3915 chi ∧
      ¬Fin15AnchoredAtom3916 chi ∧
      ¬Fin15AnchoredAtom3924 chi ∧
      ¬Fin15AnchoredAtom3925 chi ∧
      ¬Fin15AnchoredAtom3926 chi ∧
      ¬Fin15AnchoredAtom3949 chi ∧
      ¬Fin15AnchoredAtom3950 chi ∧
      ¬Fin15AnchoredAtom3951 chi ∧
      ¬Fin15AnchoredAtom3961 chi ∧
      ¬Fin15AnchoredAtom3984 chi ∧
      ¬Fin15AnchoredAtom3985 chi ∧
      ¬Fin15AnchoredAtom3986 chi ∧
      ¬Fin15AnchoredAtom3996 chi ∧
      ¬Fin15AnchoredAtom4026 chi ∧
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
  refine ⟨{2, 5, 6, 7, 9, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29412
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3823 Fin15AnchoredAtom3826 Fin15AnchoredAtom3827
    Fin15AnchoredAtom3828 Fin15AnchoredAtom3837 Fin15AnchoredAtom3838 Fin15AnchoredAtom3839
    Fin15AnchoredAtom3847 Fin15AnchoredAtom3848 Fin15AnchoredAtom3849 Fin15AnchoredAtom3858
    Fin15AnchoredAtom3859 Fin15AnchoredAtom3860 Fin15AnchoredAtom3868 Fin15AnchoredAtom3869
    Fin15AnchoredAtom3870 Fin15AnchoredAtom3893 Fin15AnchoredAtom3894 Fin15AnchoredAtom3895
    Fin15AnchoredAtom3905 Fin15AnchoredAtom3914 Fin15AnchoredAtom3915 Fin15AnchoredAtom3916
    Fin15AnchoredAtom3924 Fin15AnchoredAtom3925 Fin15AnchoredAtom3926 Fin15AnchoredAtom3949
    Fin15AnchoredAtom3950 Fin15AnchoredAtom3951 Fin15AnchoredAtom3961 Fin15AnchoredAtom3984
    Fin15AnchoredAtom3985 Fin15AnchoredAtom3986 Fin15AnchoredAtom3996 Fin15AnchoredAtom4026
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

theorem fin15Anchored_clause32121 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3824 chi ∧
      ¬Fin15AnchoredAtom3826 chi ∧
      ¬Fin15AnchoredAtom3827 chi ∧
      ¬Fin15AnchoredAtom3828 chi ∧
      ¬Fin15AnchoredAtom3841 chi ∧
      ¬Fin15AnchoredAtom3842 chi ∧
      ¬Fin15AnchoredAtom3843 chi ∧
      ¬Fin15AnchoredAtom3847 chi ∧
      ¬Fin15AnchoredAtom3848 chi ∧
      ¬Fin15AnchoredAtom3849 chi ∧
      ¬Fin15AnchoredAtom3862 chi ∧
      ¬Fin15AnchoredAtom3863 chi ∧
      ¬Fin15AnchoredAtom3864 chi ∧
      ¬Fin15AnchoredAtom3868 chi ∧
      ¬Fin15AnchoredAtom3869 chi ∧
      ¬Fin15AnchoredAtom3870 chi ∧
      ¬Fin15AnchoredAtom3899 chi ∧
      ¬Fin15AnchoredAtom3900 chi ∧
      ¬Fin15AnchoredAtom3901 chi ∧
      ¬Fin15AnchoredAtom3905 chi ∧
      ¬Fin15AnchoredAtom3918 chi ∧
      ¬Fin15AnchoredAtom3919 chi ∧
      ¬Fin15AnchoredAtom3920 chi ∧
      ¬Fin15AnchoredAtom3924 chi ∧
      ¬Fin15AnchoredAtom3925 chi ∧
      ¬Fin15AnchoredAtom3926 chi ∧
      ¬Fin15AnchoredAtom3955 chi ∧
      ¬Fin15AnchoredAtom3956 chi ∧
      ¬Fin15AnchoredAtom3957 chi ∧
      ¬Fin15AnchoredAtom3961 chi ∧
      ¬Fin15AnchoredAtom3990 chi ∧
      ¬Fin15AnchoredAtom3991 chi ∧
      ¬Fin15AnchoredAtom3992 chi ∧
      ¬Fin15AnchoredAtom3996 chi ∧
      ¬Fin15AnchoredAtom4030 chi ∧
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
  refine ⟨{2, 5, 6, 7, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29924
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3824 Fin15AnchoredAtom3826 Fin15AnchoredAtom3827
    Fin15AnchoredAtom3828 Fin15AnchoredAtom3841 Fin15AnchoredAtom3842 Fin15AnchoredAtom3843
    Fin15AnchoredAtom3847 Fin15AnchoredAtom3848 Fin15AnchoredAtom3849 Fin15AnchoredAtom3862
    Fin15AnchoredAtom3863 Fin15AnchoredAtom3864 Fin15AnchoredAtom3868 Fin15AnchoredAtom3869
    Fin15AnchoredAtom3870 Fin15AnchoredAtom3899 Fin15AnchoredAtom3900 Fin15AnchoredAtom3901
    Fin15AnchoredAtom3905 Fin15AnchoredAtom3918 Fin15AnchoredAtom3919 Fin15AnchoredAtom3920
    Fin15AnchoredAtom3924 Fin15AnchoredAtom3925 Fin15AnchoredAtom3926 Fin15AnchoredAtom3955
    Fin15AnchoredAtom3956 Fin15AnchoredAtom3957 Fin15AnchoredAtom3961 Fin15AnchoredAtom3990
    Fin15AnchoredAtom3991 Fin15AnchoredAtom3992 Fin15AnchoredAtom3996 Fin15AnchoredAtom4030
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

theorem fin15Anchored_clause32122 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3835 chi ∧
      ¬Fin15AnchoredAtom3837 chi ∧
      ¬Fin15AnchoredAtom3838 chi ∧
      ¬Fin15AnchoredAtom3839 chi ∧
      ¬Fin15AnchoredAtom3841 chi ∧
      ¬Fin15AnchoredAtom3842 chi ∧
      ¬Fin15AnchoredAtom3843 chi ∧
      ¬Fin15AnchoredAtom3847 chi ∧
      ¬Fin15AnchoredAtom3848 chi ∧
      ¬Fin15AnchoredAtom3849 chi ∧
      ¬Fin15AnchoredAtom3887 chi ∧
      ¬Fin15AnchoredAtom3888 chi ∧
      ¬Fin15AnchoredAtom3889 chi ∧
      ¬Fin15AnchoredAtom3893 chi ∧
      ¬Fin15AnchoredAtom3894 chi ∧
      ¬Fin15AnchoredAtom3895 chi ∧
      ¬Fin15AnchoredAtom3899 chi ∧
      ¬Fin15AnchoredAtom3900 chi ∧
      ¬Fin15AnchoredAtom3901 chi ∧
      ¬Fin15AnchoredAtom3905 chi ∧
      ¬Fin15AnchoredAtom3943 chi ∧
      ¬Fin15AnchoredAtom3944 chi ∧
      ¬Fin15AnchoredAtom3945 chi ∧
      ¬Fin15AnchoredAtom3949 chi ∧
      ¬Fin15AnchoredAtom3950 chi ∧
      ¬Fin15AnchoredAtom3951 chi ∧
      ¬Fin15AnchoredAtom3955 chi ∧
      ¬Fin15AnchoredAtom3956 chi ∧
      ¬Fin15AnchoredAtom3957 chi ∧
      ¬Fin15AnchoredAtom3961 chi ∧
      ¬Fin15AnchoredAtom4020 chi ∧
      ¬Fin15AnchoredAtom4021 chi ∧
      ¬Fin15AnchoredAtom4022 chi ∧
      ¬Fin15AnchoredAtom4026 chi ∧
      ¬Fin15AnchoredAtom4030 chi ∧
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
  refine ⟨{2, 5, 6, 9, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask30308
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3835 Fin15AnchoredAtom3837 Fin15AnchoredAtom3838
    Fin15AnchoredAtom3839 Fin15AnchoredAtom3841 Fin15AnchoredAtom3842 Fin15AnchoredAtom3843
    Fin15AnchoredAtom3847 Fin15AnchoredAtom3848 Fin15AnchoredAtom3849 Fin15AnchoredAtom3887
    Fin15AnchoredAtom3888 Fin15AnchoredAtom3889 Fin15AnchoredAtom3893 Fin15AnchoredAtom3894
    Fin15AnchoredAtom3895 Fin15AnchoredAtom3899 Fin15AnchoredAtom3900 Fin15AnchoredAtom3901
    Fin15AnchoredAtom3905 Fin15AnchoredAtom3943 Fin15AnchoredAtom3944 Fin15AnchoredAtom3945
    Fin15AnchoredAtom3949 Fin15AnchoredAtom3950 Fin15AnchoredAtom3951 Fin15AnchoredAtom3955
    Fin15AnchoredAtom3956 Fin15AnchoredAtom3957 Fin15AnchoredAtom3961 Fin15AnchoredAtom4020
    Fin15AnchoredAtom4021 Fin15AnchoredAtom4022 Fin15AnchoredAtom4026 Fin15AnchoredAtom4030
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

theorem fin15Anchored_clause32123 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3856 chi ∧
      ¬Fin15AnchoredAtom3858 chi ∧
      ¬Fin15AnchoredAtom3859 chi ∧
      ¬Fin15AnchoredAtom3860 chi ∧
      ¬Fin15AnchoredAtom3862 chi ∧
      ¬Fin15AnchoredAtom3863 chi ∧
      ¬Fin15AnchoredAtom3864 chi ∧
      ¬Fin15AnchoredAtom3868 chi ∧
      ¬Fin15AnchoredAtom3869 chi ∧
      ¬Fin15AnchoredAtom3870 chi ∧
      ¬Fin15AnchoredAtom3887 chi ∧
      ¬Fin15AnchoredAtom3888 chi ∧
      ¬Fin15AnchoredAtom3889 chi ∧
      ¬Fin15AnchoredAtom3893 chi ∧
      ¬Fin15AnchoredAtom3894 chi ∧
      ¬Fin15AnchoredAtom3895 chi ∧
      ¬Fin15AnchoredAtom3899 chi ∧
      ¬Fin15AnchoredAtom3900 chi ∧
      ¬Fin15AnchoredAtom3901 chi ∧
      ¬Fin15AnchoredAtom3905 chi ∧
      ¬Fin15AnchoredAtom3978 chi ∧
      ¬Fin15AnchoredAtom3979 chi ∧
      ¬Fin15AnchoredAtom3980 chi ∧
      ¬Fin15AnchoredAtom3984 chi ∧
      ¬Fin15AnchoredAtom3985 chi ∧
      ¬Fin15AnchoredAtom3986 chi ∧
      ¬Fin15AnchoredAtom3990 chi ∧
      ¬Fin15AnchoredAtom3991 chi ∧
      ¬Fin15AnchoredAtom3992 chi ∧
      ¬Fin15AnchoredAtom3996 chi ∧
      ¬Fin15AnchoredAtom4020 chi ∧
      ¬Fin15AnchoredAtom4021 chi ∧
      ¬Fin15AnchoredAtom4022 chi ∧
      ¬Fin15AnchoredAtom4026 chi ∧
      ¬Fin15AnchoredAtom4030 chi ∧
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
  refine ⟨{2, 5, 7, 9, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask30372
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3856 Fin15AnchoredAtom3858 Fin15AnchoredAtom3859
    Fin15AnchoredAtom3860 Fin15AnchoredAtom3862 Fin15AnchoredAtom3863 Fin15AnchoredAtom3864
    Fin15AnchoredAtom3868 Fin15AnchoredAtom3869 Fin15AnchoredAtom3870 Fin15AnchoredAtom3887
    Fin15AnchoredAtom3888 Fin15AnchoredAtom3889 Fin15AnchoredAtom3893 Fin15AnchoredAtom3894
    Fin15AnchoredAtom3895 Fin15AnchoredAtom3899 Fin15AnchoredAtom3900 Fin15AnchoredAtom3901
    Fin15AnchoredAtom3905 Fin15AnchoredAtom3978 Fin15AnchoredAtom3979 Fin15AnchoredAtom3980
    Fin15AnchoredAtom3984 Fin15AnchoredAtom3985 Fin15AnchoredAtom3986 Fin15AnchoredAtom3990
    Fin15AnchoredAtom3991 Fin15AnchoredAtom3992 Fin15AnchoredAtom3996 Fin15AnchoredAtom4020
    Fin15AnchoredAtom4021 Fin15AnchoredAtom4022 Fin15AnchoredAtom4026 Fin15AnchoredAtom4030
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

theorem fin15Anchored_clause32124 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3912 chi ∧
      ¬Fin15AnchoredAtom3914 chi ∧
      ¬Fin15AnchoredAtom3915 chi ∧
      ¬Fin15AnchoredAtom3916 chi ∧
      ¬Fin15AnchoredAtom3918 chi ∧
      ¬Fin15AnchoredAtom3919 chi ∧
      ¬Fin15AnchoredAtom3920 chi ∧
      ¬Fin15AnchoredAtom3924 chi ∧
      ¬Fin15AnchoredAtom3925 chi ∧
      ¬Fin15AnchoredAtom3926 chi ∧
      ¬Fin15AnchoredAtom3943 chi ∧
      ¬Fin15AnchoredAtom3944 chi ∧
      ¬Fin15AnchoredAtom3945 chi ∧
      ¬Fin15AnchoredAtom3949 chi ∧
      ¬Fin15AnchoredAtom3950 chi ∧
      ¬Fin15AnchoredAtom3951 chi ∧
      ¬Fin15AnchoredAtom3955 chi ∧
      ¬Fin15AnchoredAtom3956 chi ∧
      ¬Fin15AnchoredAtom3957 chi ∧
      ¬Fin15AnchoredAtom3961 chi ∧
      ¬Fin15AnchoredAtom3978 chi ∧
      ¬Fin15AnchoredAtom3979 chi ∧
      ¬Fin15AnchoredAtom3980 chi ∧
      ¬Fin15AnchoredAtom3984 chi ∧
      ¬Fin15AnchoredAtom3985 chi ∧
      ¬Fin15AnchoredAtom3986 chi ∧
      ¬Fin15AnchoredAtom3990 chi ∧
      ¬Fin15AnchoredAtom3991 chi ∧
      ¬Fin15AnchoredAtom3992 chi ∧
      ¬Fin15AnchoredAtom3996 chi ∧
      ¬Fin15AnchoredAtom4020 chi ∧
      ¬Fin15AnchoredAtom4021 chi ∧
      ¬Fin15AnchoredAtom4022 chi ∧
      ¬Fin15AnchoredAtom4026 chi ∧
      ¬Fin15AnchoredAtom4030 chi ∧
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
  refine ⟨{2, 6, 7, 9, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask30404
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3912 Fin15AnchoredAtom3914 Fin15AnchoredAtom3915
    Fin15AnchoredAtom3916 Fin15AnchoredAtom3918 Fin15AnchoredAtom3919 Fin15AnchoredAtom3920
    Fin15AnchoredAtom3924 Fin15AnchoredAtom3925 Fin15AnchoredAtom3926 Fin15AnchoredAtom3943
    Fin15AnchoredAtom3944 Fin15AnchoredAtom3945 Fin15AnchoredAtom3949 Fin15AnchoredAtom3950
    Fin15AnchoredAtom3951 Fin15AnchoredAtom3955 Fin15AnchoredAtom3956 Fin15AnchoredAtom3957
    Fin15AnchoredAtom3961 Fin15AnchoredAtom3978 Fin15AnchoredAtom3979 Fin15AnchoredAtom3980
    Fin15AnchoredAtom3984 Fin15AnchoredAtom3985 Fin15AnchoredAtom3986 Fin15AnchoredAtom3990
    Fin15AnchoredAtom3991 Fin15AnchoredAtom3992 Fin15AnchoredAtom3996 Fin15AnchoredAtom4020
    Fin15AnchoredAtom4021 Fin15AnchoredAtom4022 Fin15AnchoredAtom4026 Fin15AnchoredAtom4030
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

theorem fin15Anchored_clause32125 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom4032 chi ∧
      ¬Fin15AnchoredAtom4033 chi ∧
      ¬Fin15AnchoredAtom4034 chi ∧
      ¬Fin15AnchoredAtom4035 chi ∧
      ¬Fin15AnchoredAtom4040 chi ∧
      ¬Fin15AnchoredAtom4041 chi ∧
      ¬Fin15AnchoredAtom4042 chi ∧
      ¬Fin15AnchoredAtom4047 chi ∧
      ¬Fin15AnchoredAtom4048 chi ∧
      ¬Fin15AnchoredAtom4053 chi ∧
      ¬Fin15AnchoredAtom4068 chi ∧
      ¬Fin15AnchoredAtom4069 chi ∧
      ¬Fin15AnchoredAtom4070 chi ∧
      ¬Fin15AnchoredAtom4075 chi ∧
      ¬Fin15AnchoredAtom4076 chi ∧
      ¬Fin15AnchoredAtom4081 chi ∧
      ¬Fin15AnchoredAtom4096 chi ∧
      ¬Fin15AnchoredAtom4097 chi ∧
      ¬Fin15AnchoredAtom4102 chi ∧
      ¬Fin15AnchoredAtom4117 chi ∧
      ¬Fin15AnchoredAtom4152 chi ∧
      ¬Fin15AnchoredAtom4153 chi ∧
      ¬Fin15AnchoredAtom4154 chi ∧
      ¬Fin15AnchoredAtom4159 chi ∧
      ¬Fin15AnchoredAtom4160 chi ∧
      ¬Fin15AnchoredAtom4165 chi ∧
      ¬Fin15AnchoredAtom4180 chi ∧
      ¬Fin15AnchoredAtom4181 chi ∧
      ¬Fin15AnchoredAtom4186 chi ∧
      ¬Fin15AnchoredAtom4201 chi ∧
      ¬Fin15AnchoredAtom4236 chi ∧
      ¬Fin15AnchoredAtom4237 chi ∧
      ¬Fin15AnchoredAtom4242 chi ∧
      ¬Fin15AnchoredAtom4257 chi ∧
      ¬Fin15AnchoredAtom4292 chi ∧
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
  refine ⟨{3, 4, 5, 6, 7, 8, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask02040
    polygon hsubset hcard
  unfold Fin15AnchoredAtom4032 Fin15AnchoredAtom4033 Fin15AnchoredAtom4034
    Fin15AnchoredAtom4035 Fin15AnchoredAtom4040 Fin15AnchoredAtom4041 Fin15AnchoredAtom4042
    Fin15AnchoredAtom4047 Fin15AnchoredAtom4048 Fin15AnchoredAtom4053 Fin15AnchoredAtom4068
    Fin15AnchoredAtom4069 Fin15AnchoredAtom4070 Fin15AnchoredAtom4075 Fin15AnchoredAtom4076
    Fin15AnchoredAtom4081 Fin15AnchoredAtom4096 Fin15AnchoredAtom4097 Fin15AnchoredAtom4102
    Fin15AnchoredAtom4117 Fin15AnchoredAtom4152 Fin15AnchoredAtom4153 Fin15AnchoredAtom4154
    Fin15AnchoredAtom4159 Fin15AnchoredAtom4160 Fin15AnchoredAtom4165 Fin15AnchoredAtom4180
    Fin15AnchoredAtom4181 Fin15AnchoredAtom4186 Fin15AnchoredAtom4201 Fin15AnchoredAtom4236
    Fin15AnchoredAtom4237 Fin15AnchoredAtom4242 Fin15AnchoredAtom4257 Fin15AnchoredAtom4292
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

theorem fin15Anchored_clause32126 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom4032 chi ∧
      ¬Fin15AnchoredAtom4033 chi ∧
      ¬Fin15AnchoredAtom4034 chi ∧
      ¬Fin15AnchoredAtom4037 chi ∧
      ¬Fin15AnchoredAtom4040 chi ∧
      ¬Fin15AnchoredAtom4041 chi ∧
      ¬Fin15AnchoredAtom4044 chi ∧
      ¬Fin15AnchoredAtom4047 chi ∧
      ¬Fin15AnchoredAtom4050 chi ∧
      ¬Fin15AnchoredAtom4055 chi ∧
      ¬Fin15AnchoredAtom4068 chi ∧
      ¬Fin15AnchoredAtom4069 chi ∧
      ¬Fin15AnchoredAtom4072 chi ∧
      ¬Fin15AnchoredAtom4075 chi ∧
      ¬Fin15AnchoredAtom4078 chi ∧
      ¬Fin15AnchoredAtom4083 chi ∧
      ¬Fin15AnchoredAtom4096 chi ∧
      ¬Fin15AnchoredAtom4099 chi ∧
      ¬Fin15AnchoredAtom4104 chi ∧
      ¬Fin15AnchoredAtom4119 chi ∧
      ¬Fin15AnchoredAtom4152 chi ∧
      ¬Fin15AnchoredAtom4153 chi ∧
      ¬Fin15AnchoredAtom4156 chi ∧
      ¬Fin15AnchoredAtom4159 chi ∧
      ¬Fin15AnchoredAtom4162 chi ∧
      ¬Fin15AnchoredAtom4167 chi ∧
      ¬Fin15AnchoredAtom4180 chi ∧
      ¬Fin15AnchoredAtom4183 chi ∧
      ¬Fin15AnchoredAtom4188 chi ∧
      ¬Fin15AnchoredAtom4203 chi ∧
      ¬Fin15AnchoredAtom4236 chi ∧
      ¬Fin15AnchoredAtom4239 chi ∧
      ¬Fin15AnchoredAtom4244 chi ∧
      ¬Fin15AnchoredAtom4259 chi ∧
      ¬Fin15AnchoredAtom4294 chi ∧
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
  refine ⟨{3, 4, 5, 6, 7, 8, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05112
    polygon hsubset hcard
  unfold Fin15AnchoredAtom4032 Fin15AnchoredAtom4033 Fin15AnchoredAtom4034
    Fin15AnchoredAtom4037 Fin15AnchoredAtom4040 Fin15AnchoredAtom4041 Fin15AnchoredAtom4044
    Fin15AnchoredAtom4047 Fin15AnchoredAtom4050 Fin15AnchoredAtom4055 Fin15AnchoredAtom4068
    Fin15AnchoredAtom4069 Fin15AnchoredAtom4072 Fin15AnchoredAtom4075 Fin15AnchoredAtom4078
    Fin15AnchoredAtom4083 Fin15AnchoredAtom4096 Fin15AnchoredAtom4099 Fin15AnchoredAtom4104
    Fin15AnchoredAtom4119 Fin15AnchoredAtom4152 Fin15AnchoredAtom4153 Fin15AnchoredAtom4156
    Fin15AnchoredAtom4159 Fin15AnchoredAtom4162 Fin15AnchoredAtom4167 Fin15AnchoredAtom4180
    Fin15AnchoredAtom4183 Fin15AnchoredAtom4188 Fin15AnchoredAtom4203 Fin15AnchoredAtom4236
    Fin15AnchoredAtom4239 Fin15AnchoredAtom4244 Fin15AnchoredAtom4259 Fin15AnchoredAtom4294
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

theorem fin15Anchored_clause32127 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom4032 chi ∧
      ¬Fin15AnchoredAtom4033 chi ∧
      ¬Fin15AnchoredAtom4034 chi ∧
      ¬Fin15AnchoredAtom4039 chi ∧
      ¬Fin15AnchoredAtom4040 chi ∧
      ¬Fin15AnchoredAtom4041 chi ∧
      ¬Fin15AnchoredAtom4046 chi ∧
      ¬Fin15AnchoredAtom4047 chi ∧
      ¬Fin15AnchoredAtom4052 chi ∧
      ¬Fin15AnchoredAtom4057 chi ∧
      ¬Fin15AnchoredAtom4068 chi ∧
      ¬Fin15AnchoredAtom4069 chi ∧
      ¬Fin15AnchoredAtom4074 chi ∧
      ¬Fin15AnchoredAtom4075 chi ∧
      ¬Fin15AnchoredAtom4080 chi ∧
      ¬Fin15AnchoredAtom4085 chi ∧
      ¬Fin15AnchoredAtom4096 chi ∧
      ¬Fin15AnchoredAtom4101 chi ∧
      ¬Fin15AnchoredAtom4106 chi ∧
      ¬Fin15AnchoredAtom4121 chi ∧
      ¬Fin15AnchoredAtom4152 chi ∧
      ¬Fin15AnchoredAtom4153 chi ∧
      ¬Fin15AnchoredAtom4158 chi ∧
      ¬Fin15AnchoredAtom4159 chi ∧
      ¬Fin15AnchoredAtom4164 chi ∧
      ¬Fin15AnchoredAtom4169 chi ∧
      ¬Fin15AnchoredAtom4180 chi ∧
      ¬Fin15AnchoredAtom4185 chi ∧
      ¬Fin15AnchoredAtom4190 chi ∧
      ¬Fin15AnchoredAtom4205 chi ∧
      ¬Fin15AnchoredAtom4236 chi ∧
      ¬Fin15AnchoredAtom4241 chi ∧
      ¬Fin15AnchoredAtom4246 chi ∧
      ¬Fin15AnchoredAtom4261 chi ∧
      ¬Fin15AnchoredAtom4296 chi ∧
      ¬Fin15AnchoredAtom4362 chi ∧
      ¬Fin15AnchoredAtom4363 chi ∧
      ¬Fin15AnchoredAtom4368 chi ∧
      ¬Fin15AnchoredAtom4369 chi ∧
      ¬Fin15AnchoredAtom4374 chi ∧
      ¬Fin15AnchoredAtom4379 chi ∧
      ¬Fin15AnchoredAtom4390 chi ∧
      ¬Fin15AnchoredAtom4395 chi ∧
      ¬Fin15AnchoredAtom4400 chi ∧
      ¬Fin15AnchoredAtom4415 chi ∧
      ¬Fin15AnchoredAtom4446 chi ∧
      ¬Fin15AnchoredAtom4451 chi ∧
      ¬Fin15AnchoredAtom4456 chi ∧
      ¬Fin15AnchoredAtom4471 chi ∧
      ¬Fin15AnchoredAtom4506 chi ∧
      ¬Fin15AnchoredAtom4572 chi ∧
      ¬Fin15AnchoredAtom4577 chi ∧
      ¬Fin15AnchoredAtom4582 chi ∧
      ¬Fin15AnchoredAtom4597 chi ∧
      ¬Fin15AnchoredAtom4632 chi ∧
      ¬Fin15AnchoredAtom4702 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 4, 5, 6, 7, 8, 9, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17400
    polygon hsubset hcard
  unfold Fin15AnchoredAtom4032 Fin15AnchoredAtom4033 Fin15AnchoredAtom4034
    Fin15AnchoredAtom4039 Fin15AnchoredAtom4040 Fin15AnchoredAtom4041 Fin15AnchoredAtom4046
    Fin15AnchoredAtom4047 Fin15AnchoredAtom4052 Fin15AnchoredAtom4057 Fin15AnchoredAtom4068
    Fin15AnchoredAtom4069 Fin15AnchoredAtom4074 Fin15AnchoredAtom4075 Fin15AnchoredAtom4080
    Fin15AnchoredAtom4085 Fin15AnchoredAtom4096 Fin15AnchoredAtom4101 Fin15AnchoredAtom4106
    Fin15AnchoredAtom4121 Fin15AnchoredAtom4152 Fin15AnchoredAtom4153 Fin15AnchoredAtom4158
    Fin15AnchoredAtom4159 Fin15AnchoredAtom4164 Fin15AnchoredAtom4169 Fin15AnchoredAtom4180
    Fin15AnchoredAtom4185 Fin15AnchoredAtom4190 Fin15AnchoredAtom4205 Fin15AnchoredAtom4236
    Fin15AnchoredAtom4241 Fin15AnchoredAtom4246 Fin15AnchoredAtom4261 Fin15AnchoredAtom4296
    Fin15AnchoredAtom4362 Fin15AnchoredAtom4363 Fin15AnchoredAtom4368 Fin15AnchoredAtom4369
    Fin15AnchoredAtom4374 Fin15AnchoredAtom4379 Fin15AnchoredAtom4390 Fin15AnchoredAtom4395
    Fin15AnchoredAtom4400 Fin15AnchoredAtom4415 Fin15AnchoredAtom4446 Fin15AnchoredAtom4451
    Fin15AnchoredAtom4456 Fin15AnchoredAtom4471 Fin15AnchoredAtom4506 Fin15AnchoredAtom4572
    Fin15AnchoredAtom4577 Fin15AnchoredAtom4582 Fin15AnchoredAtom4597 Fin15AnchoredAtom4632
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

end ErdosSzekeres

end
