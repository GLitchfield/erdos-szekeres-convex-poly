module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 248. -/

theorem fin15Anchored_clause31744 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom2865 chi ∧
      ¬Fin15AnchoredAtom2869 chi ∧
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
      ¬Fin15AnchoredAtom3912 chi ∧
      ¬Fin15AnchoredAtom3915 chi ∧
      ¬Fin15AnchoredAtom3919 chi ∧
      ¬Fin15AnchoredAtom3944 chi ∧
      ¬Fin15AnchoredAtom3979 chi ∧
      ¬Fin15AnchoredAtom4242 chi ∧
      ¬Fin15AnchoredAtom4245 chi ∧
      ¬Fin15AnchoredAtom4249 chi ∧
      ¬Fin15AnchoredAtom4274 chi ∧
      ¬Fin15AnchoredAtom4309 chi ∧
      ¬Fin15AnchoredAtom4715 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 3, 6, 7, 9, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09934
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2841 Fin15AnchoredAtom2843 Fin15AnchoredAtom2844
    Fin15AnchoredAtom2847 Fin15AnchoredAtom2850 Fin15AnchoredAtom2851 Fin15AnchoredAtom2854
    Fin15AnchoredAtom2862 Fin15AnchoredAtom2865 Fin15AnchoredAtom2869 Fin15AnchoredAtom2959
    Fin15AnchoredAtom2960 Fin15AnchoredAtom2963 Fin15AnchoredAtom2971 Fin15AnchoredAtom2974
    Fin15AnchoredAtom2978 Fin15AnchoredAtom2992 Fin15AnchoredAtom2995 Fin15AnchoredAtom2999
    Fin15AnchoredAtom3024 Fin15AnchoredAtom3124 Fin15AnchoredAtom3125 Fin15AnchoredAtom3128
    Fin15AnchoredAtom3136 Fin15AnchoredAtom3139 Fin15AnchoredAtom3143 Fin15AnchoredAtom3157
    Fin15AnchoredAtom3160 Fin15AnchoredAtom3164 Fin15AnchoredAtom3189 Fin15AnchoredAtom3417
    Fin15AnchoredAtom3420 Fin15AnchoredAtom3424 Fin15AnchoredAtom3449 Fin15AnchoredAtom3484
    Fin15AnchoredAtom3619 Fin15AnchoredAtom3620 Fin15AnchoredAtom3623 Fin15AnchoredAtom3631
    Fin15AnchoredAtom3634 Fin15AnchoredAtom3638 Fin15AnchoredAtom3652 Fin15AnchoredAtom3655
    Fin15AnchoredAtom3659 Fin15AnchoredAtom3684 Fin15AnchoredAtom3912 Fin15AnchoredAtom3915
    Fin15AnchoredAtom3919 Fin15AnchoredAtom3944 Fin15AnchoredAtom3979 Fin15AnchoredAtom4242
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

theorem fin15Anchored_clause31745 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom2866 chi ∧
      ¬Fin15AnchoredAtom2870 chi ∧
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
      ¬Fin15AnchoredAtom3912 chi ∧
      ¬Fin15AnchoredAtom3916 chi ∧
      ¬Fin15AnchoredAtom3920 chi ∧
      ¬Fin15AnchoredAtom3945 chi ∧
      ¬Fin15AnchoredAtom3980 chi ∧
      ¬Fin15AnchoredAtom4242 chi ∧
      ¬Fin15AnchoredAtom4246 chi ∧
      ¬Fin15AnchoredAtom4250 chi ∧
      ¬Fin15AnchoredAtom4275 chi ∧
      ¬Fin15AnchoredAtom4310 chi ∧
      ¬Fin15AnchoredAtom4716 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 3, 6, 7, 9, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask18126
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2841 Fin15AnchoredAtom2843 Fin15AnchoredAtom2844
    Fin15AnchoredAtom2848 Fin15AnchoredAtom2850 Fin15AnchoredAtom2851 Fin15AnchoredAtom2855
    Fin15AnchoredAtom2862 Fin15AnchoredAtom2866 Fin15AnchoredAtom2870 Fin15AnchoredAtom2959
    Fin15AnchoredAtom2960 Fin15AnchoredAtom2964 Fin15AnchoredAtom2971 Fin15AnchoredAtom2975
    Fin15AnchoredAtom2979 Fin15AnchoredAtom2992 Fin15AnchoredAtom2996 Fin15AnchoredAtom3000
    Fin15AnchoredAtom3025 Fin15AnchoredAtom3124 Fin15AnchoredAtom3125 Fin15AnchoredAtom3129
    Fin15AnchoredAtom3136 Fin15AnchoredAtom3140 Fin15AnchoredAtom3144 Fin15AnchoredAtom3157
    Fin15AnchoredAtom3161 Fin15AnchoredAtom3165 Fin15AnchoredAtom3190 Fin15AnchoredAtom3417
    Fin15AnchoredAtom3421 Fin15AnchoredAtom3425 Fin15AnchoredAtom3450 Fin15AnchoredAtom3485
    Fin15AnchoredAtom3619 Fin15AnchoredAtom3620 Fin15AnchoredAtom3624 Fin15AnchoredAtom3631
    Fin15AnchoredAtom3635 Fin15AnchoredAtom3639 Fin15AnchoredAtom3652 Fin15AnchoredAtom3656
    Fin15AnchoredAtom3660 Fin15AnchoredAtom3685 Fin15AnchoredAtom3912 Fin15AnchoredAtom3916
    Fin15AnchoredAtom3920 Fin15AnchoredAtom3945 Fin15AnchoredAtom3980 Fin15AnchoredAtom4242
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

theorem fin15Anchored_clause31746 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom2864 chi ∧
      ¬Fin15AnchoredAtom2865 chi ∧
      ¬Fin15AnchoredAtom2874 chi ∧
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
      ¬Fin15AnchoredAtom3914 chi ∧
      ¬Fin15AnchoredAtom3915 chi ∧
      ¬Fin15AnchoredAtom3924 chi ∧
      ¬Fin15AnchoredAtom3949 chi ∧
      ¬Fin15AnchoredAtom3984 chi ∧
      ¬Fin15AnchoredAtom4244 chi ∧
      ¬Fin15AnchoredAtom4245 chi ∧
      ¬Fin15AnchoredAtom4254 chi ∧
      ¬Fin15AnchoredAtom4279 chi ∧
      ¬Fin15AnchoredAtom4314 chi ∧
      ¬Fin15AnchoredAtom4720 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 3, 6, 7, 9, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13006
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2841 Fin15AnchoredAtom2843 Fin15AnchoredAtom2846
    Fin15AnchoredAtom2847 Fin15AnchoredAtom2850 Fin15AnchoredAtom2853 Fin15AnchoredAtom2854
    Fin15AnchoredAtom2864 Fin15AnchoredAtom2865 Fin15AnchoredAtom2874 Fin15AnchoredAtom2959
    Fin15AnchoredAtom2962 Fin15AnchoredAtom2963 Fin15AnchoredAtom2973 Fin15AnchoredAtom2974
    Fin15AnchoredAtom2983 Fin15AnchoredAtom2994 Fin15AnchoredAtom2995 Fin15AnchoredAtom3004
    Fin15AnchoredAtom3029 Fin15AnchoredAtom3124 Fin15AnchoredAtom3127 Fin15AnchoredAtom3128
    Fin15AnchoredAtom3138 Fin15AnchoredAtom3139 Fin15AnchoredAtom3148 Fin15AnchoredAtom3159
    Fin15AnchoredAtom3160 Fin15AnchoredAtom3169 Fin15AnchoredAtom3194 Fin15AnchoredAtom3419
    Fin15AnchoredAtom3420 Fin15AnchoredAtom3429 Fin15AnchoredAtom3454 Fin15AnchoredAtom3489
    Fin15AnchoredAtom3619 Fin15AnchoredAtom3622 Fin15AnchoredAtom3623 Fin15AnchoredAtom3633
    Fin15AnchoredAtom3634 Fin15AnchoredAtom3643 Fin15AnchoredAtom3654 Fin15AnchoredAtom3655
    Fin15AnchoredAtom3664 Fin15AnchoredAtom3689 Fin15AnchoredAtom3914 Fin15AnchoredAtom3915
    Fin15AnchoredAtom3924 Fin15AnchoredAtom3949 Fin15AnchoredAtom3984 Fin15AnchoredAtom4244
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

theorem fin15Anchored_clause31747 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom2864 chi ∧
      ¬Fin15AnchoredAtom2866 chi ∧
      ¬Fin15AnchoredAtom2875 chi ∧
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
      ¬Fin15AnchoredAtom3914 chi ∧
      ¬Fin15AnchoredAtom3916 chi ∧
      ¬Fin15AnchoredAtom3925 chi ∧
      ¬Fin15AnchoredAtom3950 chi ∧
      ¬Fin15AnchoredAtom3985 chi ∧
      ¬Fin15AnchoredAtom4244 chi ∧
      ¬Fin15AnchoredAtom4246 chi ∧
      ¬Fin15AnchoredAtom4255 chi ∧
      ¬Fin15AnchoredAtom4280 chi ∧
      ¬Fin15AnchoredAtom4315 chi ∧
      ¬Fin15AnchoredAtom4721 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 3, 6, 7, 9, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21198
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2841 Fin15AnchoredAtom2843 Fin15AnchoredAtom2846
    Fin15AnchoredAtom2848 Fin15AnchoredAtom2850 Fin15AnchoredAtom2853 Fin15AnchoredAtom2855
    Fin15AnchoredAtom2864 Fin15AnchoredAtom2866 Fin15AnchoredAtom2875 Fin15AnchoredAtom2959
    Fin15AnchoredAtom2962 Fin15AnchoredAtom2964 Fin15AnchoredAtom2973 Fin15AnchoredAtom2975
    Fin15AnchoredAtom2984 Fin15AnchoredAtom2994 Fin15AnchoredAtom2996 Fin15AnchoredAtom3005
    Fin15AnchoredAtom3030 Fin15AnchoredAtom3124 Fin15AnchoredAtom3127 Fin15AnchoredAtom3129
    Fin15AnchoredAtom3138 Fin15AnchoredAtom3140 Fin15AnchoredAtom3149 Fin15AnchoredAtom3159
    Fin15AnchoredAtom3161 Fin15AnchoredAtom3170 Fin15AnchoredAtom3195 Fin15AnchoredAtom3419
    Fin15AnchoredAtom3421 Fin15AnchoredAtom3430 Fin15AnchoredAtom3455 Fin15AnchoredAtom3490
    Fin15AnchoredAtom3619 Fin15AnchoredAtom3622 Fin15AnchoredAtom3624 Fin15AnchoredAtom3633
    Fin15AnchoredAtom3635 Fin15AnchoredAtom3644 Fin15AnchoredAtom3654 Fin15AnchoredAtom3656
    Fin15AnchoredAtom3665 Fin15AnchoredAtom3690 Fin15AnchoredAtom3914 Fin15AnchoredAtom3916
    Fin15AnchoredAtom3925 Fin15AnchoredAtom3950 Fin15AnchoredAtom3985 Fin15AnchoredAtom4244
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

theorem fin15Anchored_clause31748 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom2865 chi ∧
      ¬Fin15AnchoredAtom2866 chi ∧
      ¬Fin15AnchoredAtom2876 chi ∧
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
      ¬Fin15AnchoredAtom3915 chi ∧
      ¬Fin15AnchoredAtom3916 chi ∧
      ¬Fin15AnchoredAtom3926 chi ∧
      ¬Fin15AnchoredAtom3951 chi ∧
      ¬Fin15AnchoredAtom3986 chi ∧
      ¬Fin15AnchoredAtom4245 chi ∧
      ¬Fin15AnchoredAtom4246 chi ∧
      ¬Fin15AnchoredAtom4256 chi ∧
      ¬Fin15AnchoredAtom4281 chi ∧
      ¬Fin15AnchoredAtom4316 chi ∧
      ¬Fin15AnchoredAtom4722 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 3, 6, 7, 9, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25294
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2841 Fin15AnchoredAtom2843 Fin15AnchoredAtom2847
    Fin15AnchoredAtom2848 Fin15AnchoredAtom2850 Fin15AnchoredAtom2854 Fin15AnchoredAtom2855
    Fin15AnchoredAtom2865 Fin15AnchoredAtom2866 Fin15AnchoredAtom2876 Fin15AnchoredAtom2959
    Fin15AnchoredAtom2963 Fin15AnchoredAtom2964 Fin15AnchoredAtom2974 Fin15AnchoredAtom2975
    Fin15AnchoredAtom2985 Fin15AnchoredAtom2995 Fin15AnchoredAtom2996 Fin15AnchoredAtom3006
    Fin15AnchoredAtom3031 Fin15AnchoredAtom3124 Fin15AnchoredAtom3128 Fin15AnchoredAtom3129
    Fin15AnchoredAtom3139 Fin15AnchoredAtom3140 Fin15AnchoredAtom3150 Fin15AnchoredAtom3160
    Fin15AnchoredAtom3161 Fin15AnchoredAtom3171 Fin15AnchoredAtom3196 Fin15AnchoredAtom3420
    Fin15AnchoredAtom3421 Fin15AnchoredAtom3431 Fin15AnchoredAtom3456 Fin15AnchoredAtom3491
    Fin15AnchoredAtom3619 Fin15AnchoredAtom3623 Fin15AnchoredAtom3624 Fin15AnchoredAtom3634
    Fin15AnchoredAtom3635 Fin15AnchoredAtom3645 Fin15AnchoredAtom3655 Fin15AnchoredAtom3656
    Fin15AnchoredAtom3666 Fin15AnchoredAtom3691 Fin15AnchoredAtom3915 Fin15AnchoredAtom3916
    Fin15AnchoredAtom3926 Fin15AnchoredAtom3951 Fin15AnchoredAtom3986 Fin15AnchoredAtom4245
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

theorem fin15Anchored_clause31749 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom2868 chi ∧
      ¬Fin15AnchoredAtom2869 chi ∧
      ¬Fin15AnchoredAtom2874 chi ∧
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
      ¬Fin15AnchoredAtom3918 chi ∧
      ¬Fin15AnchoredAtom3919 chi ∧
      ¬Fin15AnchoredAtom3924 chi ∧
      ¬Fin15AnchoredAtom3955 chi ∧
      ¬Fin15AnchoredAtom3990 chi ∧
      ¬Fin15AnchoredAtom4248 chi ∧
      ¬Fin15AnchoredAtom4249 chi ∧
      ¬Fin15AnchoredAtom4254 chi ∧
      ¬Fin15AnchoredAtom4285 chi ∧
      ¬Fin15AnchoredAtom4320 chi ∧
      ¬Fin15AnchoredAtom4726 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 3, 6, 7, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13518
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2841 Fin15AnchoredAtom2844 Fin15AnchoredAtom2846
    Fin15AnchoredAtom2847 Fin15AnchoredAtom2851 Fin15AnchoredAtom2853 Fin15AnchoredAtom2854
    Fin15AnchoredAtom2868 Fin15AnchoredAtom2869 Fin15AnchoredAtom2874 Fin15AnchoredAtom2960
    Fin15AnchoredAtom2962 Fin15AnchoredAtom2963 Fin15AnchoredAtom2977 Fin15AnchoredAtom2978
    Fin15AnchoredAtom2983 Fin15AnchoredAtom2998 Fin15AnchoredAtom2999 Fin15AnchoredAtom3004
    Fin15AnchoredAtom3035 Fin15AnchoredAtom3125 Fin15AnchoredAtom3127 Fin15AnchoredAtom3128
    Fin15AnchoredAtom3142 Fin15AnchoredAtom3143 Fin15AnchoredAtom3148 Fin15AnchoredAtom3163
    Fin15AnchoredAtom3164 Fin15AnchoredAtom3169 Fin15AnchoredAtom3200 Fin15AnchoredAtom3423
    Fin15AnchoredAtom3424 Fin15AnchoredAtom3429 Fin15AnchoredAtom3460 Fin15AnchoredAtom3495
    Fin15AnchoredAtom3620 Fin15AnchoredAtom3622 Fin15AnchoredAtom3623 Fin15AnchoredAtom3637
    Fin15AnchoredAtom3638 Fin15AnchoredAtom3643 Fin15AnchoredAtom3658 Fin15AnchoredAtom3659
    Fin15AnchoredAtom3664 Fin15AnchoredAtom3695 Fin15AnchoredAtom3918 Fin15AnchoredAtom3919
    Fin15AnchoredAtom3924 Fin15AnchoredAtom3955 Fin15AnchoredAtom3990 Fin15AnchoredAtom4248
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

theorem fin15Anchored_clause31750 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom2868 chi ∧
      ¬Fin15AnchoredAtom2870 chi ∧
      ¬Fin15AnchoredAtom2875 chi ∧
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
      ¬Fin15AnchoredAtom3918 chi ∧
      ¬Fin15AnchoredAtom3920 chi ∧
      ¬Fin15AnchoredAtom3925 chi ∧
      ¬Fin15AnchoredAtom3956 chi ∧
      ¬Fin15AnchoredAtom3991 chi ∧
      ¬Fin15AnchoredAtom4248 chi ∧
      ¬Fin15AnchoredAtom4250 chi ∧
      ¬Fin15AnchoredAtom4255 chi ∧
      ¬Fin15AnchoredAtom4286 chi ∧
      ¬Fin15AnchoredAtom4321 chi ∧
      ¬Fin15AnchoredAtom4727 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 3, 6, 7, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21710
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2841 Fin15AnchoredAtom2844 Fin15AnchoredAtom2846
    Fin15AnchoredAtom2848 Fin15AnchoredAtom2851 Fin15AnchoredAtom2853 Fin15AnchoredAtom2855
    Fin15AnchoredAtom2868 Fin15AnchoredAtom2870 Fin15AnchoredAtom2875 Fin15AnchoredAtom2960
    Fin15AnchoredAtom2962 Fin15AnchoredAtom2964 Fin15AnchoredAtom2977 Fin15AnchoredAtom2979
    Fin15AnchoredAtom2984 Fin15AnchoredAtom2998 Fin15AnchoredAtom3000 Fin15AnchoredAtom3005
    Fin15AnchoredAtom3036 Fin15AnchoredAtom3125 Fin15AnchoredAtom3127 Fin15AnchoredAtom3129
    Fin15AnchoredAtom3142 Fin15AnchoredAtom3144 Fin15AnchoredAtom3149 Fin15AnchoredAtom3163
    Fin15AnchoredAtom3165 Fin15AnchoredAtom3170 Fin15AnchoredAtom3201 Fin15AnchoredAtom3423
    Fin15AnchoredAtom3425 Fin15AnchoredAtom3430 Fin15AnchoredAtom3461 Fin15AnchoredAtom3496
    Fin15AnchoredAtom3620 Fin15AnchoredAtom3622 Fin15AnchoredAtom3624 Fin15AnchoredAtom3637
    Fin15AnchoredAtom3639 Fin15AnchoredAtom3644 Fin15AnchoredAtom3658 Fin15AnchoredAtom3660
    Fin15AnchoredAtom3665 Fin15AnchoredAtom3696 Fin15AnchoredAtom3918 Fin15AnchoredAtom3920
    Fin15AnchoredAtom3925 Fin15AnchoredAtom3956 Fin15AnchoredAtom3991 Fin15AnchoredAtom4248
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

theorem fin15Anchored_clause31751 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom2869 chi ∧
      ¬Fin15AnchoredAtom2870 chi ∧
      ¬Fin15AnchoredAtom2876 chi ∧
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
      ¬Fin15AnchoredAtom3919 chi ∧
      ¬Fin15AnchoredAtom3920 chi ∧
      ¬Fin15AnchoredAtom3926 chi ∧
      ¬Fin15AnchoredAtom3957 chi ∧
      ¬Fin15AnchoredAtom3992 chi ∧
      ¬Fin15AnchoredAtom4249 chi ∧
      ¬Fin15AnchoredAtom4250 chi ∧
      ¬Fin15AnchoredAtom4256 chi ∧
      ¬Fin15AnchoredAtom4287 chi ∧
      ¬Fin15AnchoredAtom4322 chi ∧
      ¬Fin15AnchoredAtom4728 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 3, 6, 7, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25806
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2841 Fin15AnchoredAtom2844 Fin15AnchoredAtom2847
    Fin15AnchoredAtom2848 Fin15AnchoredAtom2851 Fin15AnchoredAtom2854 Fin15AnchoredAtom2855
    Fin15AnchoredAtom2869 Fin15AnchoredAtom2870 Fin15AnchoredAtom2876 Fin15AnchoredAtom2960
    Fin15AnchoredAtom2963 Fin15AnchoredAtom2964 Fin15AnchoredAtom2978 Fin15AnchoredAtom2979
    Fin15AnchoredAtom2985 Fin15AnchoredAtom2999 Fin15AnchoredAtom3000 Fin15AnchoredAtom3006
    Fin15AnchoredAtom3037 Fin15AnchoredAtom3125 Fin15AnchoredAtom3128 Fin15AnchoredAtom3129
    Fin15AnchoredAtom3143 Fin15AnchoredAtom3144 Fin15AnchoredAtom3150 Fin15AnchoredAtom3164
    Fin15AnchoredAtom3165 Fin15AnchoredAtom3171 Fin15AnchoredAtom3202 Fin15AnchoredAtom3424
    Fin15AnchoredAtom3425 Fin15AnchoredAtom3431 Fin15AnchoredAtom3462 Fin15AnchoredAtom3497
    Fin15AnchoredAtom3620 Fin15AnchoredAtom3623 Fin15AnchoredAtom3624 Fin15AnchoredAtom3638
    Fin15AnchoredAtom3639 Fin15AnchoredAtom3645 Fin15AnchoredAtom3659 Fin15AnchoredAtom3660
    Fin15AnchoredAtom3666 Fin15AnchoredAtom3697 Fin15AnchoredAtom3919 Fin15AnchoredAtom3920
    Fin15AnchoredAtom3926 Fin15AnchoredAtom3957 Fin15AnchoredAtom3992 Fin15AnchoredAtom4249
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

theorem fin15Anchored_clause31752 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom2874 chi ∧
      ¬Fin15AnchoredAtom2875 chi ∧
      ¬Fin15AnchoredAtom2876 chi ∧
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
      ¬Fin15AnchoredAtom3924 chi ∧
      ¬Fin15AnchoredAtom3925 chi ∧
      ¬Fin15AnchoredAtom3926 chi ∧
      ¬Fin15AnchoredAtom3961 chi ∧
      ¬Fin15AnchoredAtom3996 chi ∧
      ¬Fin15AnchoredAtom4254 chi ∧
      ¬Fin15AnchoredAtom4255 chi ∧
      ¬Fin15AnchoredAtom4256 chi ∧
      ¬Fin15AnchoredAtom4291 chi ∧
      ¬Fin15AnchoredAtom4326 chi ∧
      ¬Fin15AnchoredAtom4732 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 3, 6, 7, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask28878
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2841 Fin15AnchoredAtom2846 Fin15AnchoredAtom2847
    Fin15AnchoredAtom2848 Fin15AnchoredAtom2853 Fin15AnchoredAtom2854 Fin15AnchoredAtom2855
    Fin15AnchoredAtom2874 Fin15AnchoredAtom2875 Fin15AnchoredAtom2876 Fin15AnchoredAtom2962
    Fin15AnchoredAtom2963 Fin15AnchoredAtom2964 Fin15AnchoredAtom2983 Fin15AnchoredAtom2984
    Fin15AnchoredAtom2985 Fin15AnchoredAtom3004 Fin15AnchoredAtom3005 Fin15AnchoredAtom3006
    Fin15AnchoredAtom3041 Fin15AnchoredAtom3127 Fin15AnchoredAtom3128 Fin15AnchoredAtom3129
    Fin15AnchoredAtom3148 Fin15AnchoredAtom3149 Fin15AnchoredAtom3150 Fin15AnchoredAtom3169
    Fin15AnchoredAtom3170 Fin15AnchoredAtom3171 Fin15AnchoredAtom3206 Fin15AnchoredAtom3429
    Fin15AnchoredAtom3430 Fin15AnchoredAtom3431 Fin15AnchoredAtom3466 Fin15AnchoredAtom3501
    Fin15AnchoredAtom3622 Fin15AnchoredAtom3623 Fin15AnchoredAtom3624 Fin15AnchoredAtom3643
    Fin15AnchoredAtom3644 Fin15AnchoredAtom3645 Fin15AnchoredAtom3664 Fin15AnchoredAtom3665
    Fin15AnchoredAtom3666 Fin15AnchoredAtom3701 Fin15AnchoredAtom3924 Fin15AnchoredAtom3925
    Fin15AnchoredAtom3926 Fin15AnchoredAtom3961 Fin15AnchoredAtom3996 Fin15AnchoredAtom4254
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

theorem fin15Anchored_clause31753 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom2864 chi ∧
      ¬Fin15AnchoredAtom2865 chi ∧
      ¬Fin15AnchoredAtom2868 chi ∧
      ¬Fin15AnchoredAtom2869 chi ∧
      ¬Fin15AnchoredAtom2874 chi ∧
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
      ¬Fin15AnchoredAtom3943 chi ∧
      ¬Fin15AnchoredAtom3944 chi ∧
      ¬Fin15AnchoredAtom3949 chi ∧
      ¬Fin15AnchoredAtom3955 chi ∧
      ¬Fin15AnchoredAtom4020 chi ∧
      ¬Fin15AnchoredAtom4273 chi ∧
      ¬Fin15AnchoredAtom4274 chi ∧
      ¬Fin15AnchoredAtom4279 chi ∧
      ¬Fin15AnchoredAtom4285 chi ∧
      ¬Fin15AnchoredAtom4350 chi ∧
      ¬Fin15AnchoredAtom4756 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 3, 6, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13902
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2843 Fin15AnchoredAtom2844 Fin15AnchoredAtom2846
    Fin15AnchoredAtom2847 Fin15AnchoredAtom2862 Fin15AnchoredAtom2864 Fin15AnchoredAtom2865
    Fin15AnchoredAtom2868 Fin15AnchoredAtom2869 Fin15AnchoredAtom2874 Fin15AnchoredAtom2971
    Fin15AnchoredAtom2973 Fin15AnchoredAtom2974 Fin15AnchoredAtom2977 Fin15AnchoredAtom2978
    Fin15AnchoredAtom2983 Fin15AnchoredAtom3023 Fin15AnchoredAtom3024 Fin15AnchoredAtom3029
    Fin15AnchoredAtom3035 Fin15AnchoredAtom3136 Fin15AnchoredAtom3138 Fin15AnchoredAtom3139
    Fin15AnchoredAtom3142 Fin15AnchoredAtom3143 Fin15AnchoredAtom3148 Fin15AnchoredAtom3188
    Fin15AnchoredAtom3189 Fin15AnchoredAtom3194 Fin15AnchoredAtom3200 Fin15AnchoredAtom3448
    Fin15AnchoredAtom3449 Fin15AnchoredAtom3454 Fin15AnchoredAtom3460 Fin15AnchoredAtom3525
    Fin15AnchoredAtom3631 Fin15AnchoredAtom3633 Fin15AnchoredAtom3634 Fin15AnchoredAtom3637
    Fin15AnchoredAtom3638 Fin15AnchoredAtom3643 Fin15AnchoredAtom3683 Fin15AnchoredAtom3684
    Fin15AnchoredAtom3689 Fin15AnchoredAtom3695 Fin15AnchoredAtom3943 Fin15AnchoredAtom3944
    Fin15AnchoredAtom3949 Fin15AnchoredAtom3955 Fin15AnchoredAtom4020 Fin15AnchoredAtom4273
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

theorem fin15Anchored_clause31754 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom2864 chi ∧
      ¬Fin15AnchoredAtom2866 chi ∧
      ¬Fin15AnchoredAtom2868 chi ∧
      ¬Fin15AnchoredAtom2870 chi ∧
      ¬Fin15AnchoredAtom2875 chi ∧
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
      ¬Fin15AnchoredAtom3943 chi ∧
      ¬Fin15AnchoredAtom3945 chi ∧
      ¬Fin15AnchoredAtom3950 chi ∧
      ¬Fin15AnchoredAtom3956 chi ∧
      ¬Fin15AnchoredAtom4021 chi ∧
      ¬Fin15AnchoredAtom4273 chi ∧
      ¬Fin15AnchoredAtom4275 chi ∧
      ¬Fin15AnchoredAtom4280 chi ∧
      ¬Fin15AnchoredAtom4286 chi ∧
      ¬Fin15AnchoredAtom4351 chi ∧
      ¬Fin15AnchoredAtom4757 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 3, 6, 9, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22094
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2843 Fin15AnchoredAtom2844 Fin15AnchoredAtom2846
    Fin15AnchoredAtom2848 Fin15AnchoredAtom2862 Fin15AnchoredAtom2864 Fin15AnchoredAtom2866
    Fin15AnchoredAtom2868 Fin15AnchoredAtom2870 Fin15AnchoredAtom2875 Fin15AnchoredAtom2971
    Fin15AnchoredAtom2973 Fin15AnchoredAtom2975 Fin15AnchoredAtom2977 Fin15AnchoredAtom2979
    Fin15AnchoredAtom2984 Fin15AnchoredAtom3023 Fin15AnchoredAtom3025 Fin15AnchoredAtom3030
    Fin15AnchoredAtom3036 Fin15AnchoredAtom3136 Fin15AnchoredAtom3138 Fin15AnchoredAtom3140
    Fin15AnchoredAtom3142 Fin15AnchoredAtom3144 Fin15AnchoredAtom3149 Fin15AnchoredAtom3188
    Fin15AnchoredAtom3190 Fin15AnchoredAtom3195 Fin15AnchoredAtom3201 Fin15AnchoredAtom3448
    Fin15AnchoredAtom3450 Fin15AnchoredAtom3455 Fin15AnchoredAtom3461 Fin15AnchoredAtom3526
    Fin15AnchoredAtom3631 Fin15AnchoredAtom3633 Fin15AnchoredAtom3635 Fin15AnchoredAtom3637
    Fin15AnchoredAtom3639 Fin15AnchoredAtom3644 Fin15AnchoredAtom3683 Fin15AnchoredAtom3685
    Fin15AnchoredAtom3690 Fin15AnchoredAtom3696 Fin15AnchoredAtom3943 Fin15AnchoredAtom3945
    Fin15AnchoredAtom3950 Fin15AnchoredAtom3956 Fin15AnchoredAtom4021 Fin15AnchoredAtom4273
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

theorem fin15Anchored_clause31755 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom2865 chi ∧
      ¬Fin15AnchoredAtom2866 chi ∧
      ¬Fin15AnchoredAtom2869 chi ∧
      ¬Fin15AnchoredAtom2870 chi ∧
      ¬Fin15AnchoredAtom2876 chi ∧
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
      ¬Fin15AnchoredAtom3944 chi ∧
      ¬Fin15AnchoredAtom3945 chi ∧
      ¬Fin15AnchoredAtom3951 chi ∧
      ¬Fin15AnchoredAtom3957 chi ∧
      ¬Fin15AnchoredAtom4022 chi ∧
      ¬Fin15AnchoredAtom4274 chi ∧
      ¬Fin15AnchoredAtom4275 chi ∧
      ¬Fin15AnchoredAtom4281 chi ∧
      ¬Fin15AnchoredAtom4287 chi ∧
      ¬Fin15AnchoredAtom4352 chi ∧
      ¬Fin15AnchoredAtom4758 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 3, 6, 9, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26190
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2843 Fin15AnchoredAtom2844 Fin15AnchoredAtom2847
    Fin15AnchoredAtom2848 Fin15AnchoredAtom2862 Fin15AnchoredAtom2865 Fin15AnchoredAtom2866
    Fin15AnchoredAtom2869 Fin15AnchoredAtom2870 Fin15AnchoredAtom2876 Fin15AnchoredAtom2971
    Fin15AnchoredAtom2974 Fin15AnchoredAtom2975 Fin15AnchoredAtom2978 Fin15AnchoredAtom2979
    Fin15AnchoredAtom2985 Fin15AnchoredAtom3024 Fin15AnchoredAtom3025 Fin15AnchoredAtom3031
    Fin15AnchoredAtom3037 Fin15AnchoredAtom3136 Fin15AnchoredAtom3139 Fin15AnchoredAtom3140
    Fin15AnchoredAtom3143 Fin15AnchoredAtom3144 Fin15AnchoredAtom3150 Fin15AnchoredAtom3189
    Fin15AnchoredAtom3190 Fin15AnchoredAtom3196 Fin15AnchoredAtom3202 Fin15AnchoredAtom3449
    Fin15AnchoredAtom3450 Fin15AnchoredAtom3456 Fin15AnchoredAtom3462 Fin15AnchoredAtom3527
    Fin15AnchoredAtom3631 Fin15AnchoredAtom3634 Fin15AnchoredAtom3635 Fin15AnchoredAtom3638
    Fin15AnchoredAtom3639 Fin15AnchoredAtom3645 Fin15AnchoredAtom3684 Fin15AnchoredAtom3685
    Fin15AnchoredAtom3691 Fin15AnchoredAtom3697 Fin15AnchoredAtom3944 Fin15AnchoredAtom3945
    Fin15AnchoredAtom3951 Fin15AnchoredAtom3957 Fin15AnchoredAtom4022 Fin15AnchoredAtom4274
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

theorem fin15Anchored_clause31756 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom2864 chi ∧
      ¬Fin15AnchoredAtom2865 chi ∧
      ¬Fin15AnchoredAtom2866 chi ∧
      ¬Fin15AnchoredAtom2874 chi ∧
      ¬Fin15AnchoredAtom2875 chi ∧
      ¬Fin15AnchoredAtom2876 chi ∧
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
      ¬Fin15AnchoredAtom3949 chi ∧
      ¬Fin15AnchoredAtom3950 chi ∧
      ¬Fin15AnchoredAtom3951 chi ∧
      ¬Fin15AnchoredAtom3961 chi ∧
      ¬Fin15AnchoredAtom4026 chi ∧
      ¬Fin15AnchoredAtom4279 chi ∧
      ¬Fin15AnchoredAtom4280 chi ∧
      ¬Fin15AnchoredAtom4281 chi ∧
      ¬Fin15AnchoredAtom4291 chi ∧
      ¬Fin15AnchoredAtom4356 chi ∧
      ¬Fin15AnchoredAtom4762 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 3, 6, 9, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29262
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2843 Fin15AnchoredAtom2846 Fin15AnchoredAtom2847
    Fin15AnchoredAtom2848 Fin15AnchoredAtom2864 Fin15AnchoredAtom2865 Fin15AnchoredAtom2866
    Fin15AnchoredAtom2874 Fin15AnchoredAtom2875 Fin15AnchoredAtom2876 Fin15AnchoredAtom2973
    Fin15AnchoredAtom2974 Fin15AnchoredAtom2975 Fin15AnchoredAtom2983 Fin15AnchoredAtom2984
    Fin15AnchoredAtom2985 Fin15AnchoredAtom3029 Fin15AnchoredAtom3030 Fin15AnchoredAtom3031
    Fin15AnchoredAtom3041 Fin15AnchoredAtom3138 Fin15AnchoredAtom3139 Fin15AnchoredAtom3140
    Fin15AnchoredAtom3148 Fin15AnchoredAtom3149 Fin15AnchoredAtom3150 Fin15AnchoredAtom3194
    Fin15AnchoredAtom3195 Fin15AnchoredAtom3196 Fin15AnchoredAtom3206 Fin15AnchoredAtom3454
    Fin15AnchoredAtom3455 Fin15AnchoredAtom3456 Fin15AnchoredAtom3466 Fin15AnchoredAtom3531
    Fin15AnchoredAtom3633 Fin15AnchoredAtom3634 Fin15AnchoredAtom3635 Fin15AnchoredAtom3643
    Fin15AnchoredAtom3644 Fin15AnchoredAtom3645 Fin15AnchoredAtom3689 Fin15AnchoredAtom3690
    Fin15AnchoredAtom3691 Fin15AnchoredAtom3701 Fin15AnchoredAtom3949 Fin15AnchoredAtom3950
    Fin15AnchoredAtom3951 Fin15AnchoredAtom3961 Fin15AnchoredAtom4026 Fin15AnchoredAtom4279
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

theorem fin15Anchored_clause31757 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom2868 chi ∧
      ¬Fin15AnchoredAtom2869 chi ∧
      ¬Fin15AnchoredAtom2870 chi ∧
      ¬Fin15AnchoredAtom2874 chi ∧
      ¬Fin15AnchoredAtom2875 chi ∧
      ¬Fin15AnchoredAtom2876 chi ∧
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
      ¬Fin15AnchoredAtom3955 chi ∧
      ¬Fin15AnchoredAtom3956 chi ∧
      ¬Fin15AnchoredAtom3957 chi ∧
      ¬Fin15AnchoredAtom3961 chi ∧
      ¬Fin15AnchoredAtom4030 chi ∧
      ¬Fin15AnchoredAtom4285 chi ∧
      ¬Fin15AnchoredAtom4286 chi ∧
      ¬Fin15AnchoredAtom4287 chi ∧
      ¬Fin15AnchoredAtom4291 chi ∧
      ¬Fin15AnchoredAtom4360 chi ∧
      ¬Fin15AnchoredAtom4766 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 3, 6, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29774
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2844 Fin15AnchoredAtom2846 Fin15AnchoredAtom2847
    Fin15AnchoredAtom2848 Fin15AnchoredAtom2868 Fin15AnchoredAtom2869 Fin15AnchoredAtom2870
    Fin15AnchoredAtom2874 Fin15AnchoredAtom2875 Fin15AnchoredAtom2876 Fin15AnchoredAtom2977
    Fin15AnchoredAtom2978 Fin15AnchoredAtom2979 Fin15AnchoredAtom2983 Fin15AnchoredAtom2984
    Fin15AnchoredAtom2985 Fin15AnchoredAtom3035 Fin15AnchoredAtom3036 Fin15AnchoredAtom3037
    Fin15AnchoredAtom3041 Fin15AnchoredAtom3142 Fin15AnchoredAtom3143 Fin15AnchoredAtom3144
    Fin15AnchoredAtom3148 Fin15AnchoredAtom3149 Fin15AnchoredAtom3150 Fin15AnchoredAtom3200
    Fin15AnchoredAtom3201 Fin15AnchoredAtom3202 Fin15AnchoredAtom3206 Fin15AnchoredAtom3460
    Fin15AnchoredAtom3461 Fin15AnchoredAtom3462 Fin15AnchoredAtom3466 Fin15AnchoredAtom3535
    Fin15AnchoredAtom3637 Fin15AnchoredAtom3638 Fin15AnchoredAtom3639 Fin15AnchoredAtom3643
    Fin15AnchoredAtom3644 Fin15AnchoredAtom3645 Fin15AnchoredAtom3695 Fin15AnchoredAtom3696
    Fin15AnchoredAtom3697 Fin15AnchoredAtom3701 Fin15AnchoredAtom3955 Fin15AnchoredAtom3956
    Fin15AnchoredAtom3957 Fin15AnchoredAtom3961 Fin15AnchoredAtom4030 Fin15AnchoredAtom4285
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

theorem fin15Anchored_clause31758 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom2864 chi ∧
      ¬Fin15AnchoredAtom2865 chi ∧
      ¬Fin15AnchoredAtom2868 chi ∧
      ¬Fin15AnchoredAtom2869 chi ∧
      ¬Fin15AnchoredAtom2874 chi ∧
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
      ¬Fin15AnchoredAtom3978 chi ∧
      ¬Fin15AnchoredAtom3979 chi ∧
      ¬Fin15AnchoredAtom3984 chi ∧
      ¬Fin15AnchoredAtom3990 chi ∧
      ¬Fin15AnchoredAtom4020 chi ∧
      ¬Fin15AnchoredAtom4308 chi ∧
      ¬Fin15AnchoredAtom4309 chi ∧
      ¬Fin15AnchoredAtom4314 chi ∧
      ¬Fin15AnchoredAtom4320 chi ∧
      ¬Fin15AnchoredAtom4350 chi ∧
      ¬Fin15AnchoredAtom4791 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 3, 7, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13966
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2850 Fin15AnchoredAtom2851 Fin15AnchoredAtom2853
    Fin15AnchoredAtom2854 Fin15AnchoredAtom2862 Fin15AnchoredAtom2864 Fin15AnchoredAtom2865
    Fin15AnchoredAtom2868 Fin15AnchoredAtom2869 Fin15AnchoredAtom2874 Fin15AnchoredAtom2992
    Fin15AnchoredAtom2994 Fin15AnchoredAtom2995 Fin15AnchoredAtom2998 Fin15AnchoredAtom2999
    Fin15AnchoredAtom3004 Fin15AnchoredAtom3023 Fin15AnchoredAtom3024 Fin15AnchoredAtom3029
    Fin15AnchoredAtom3035 Fin15AnchoredAtom3157 Fin15AnchoredAtom3159 Fin15AnchoredAtom3160
    Fin15AnchoredAtom3163 Fin15AnchoredAtom3164 Fin15AnchoredAtom3169 Fin15AnchoredAtom3188
    Fin15AnchoredAtom3189 Fin15AnchoredAtom3194 Fin15AnchoredAtom3200 Fin15AnchoredAtom3483
    Fin15AnchoredAtom3484 Fin15AnchoredAtom3489 Fin15AnchoredAtom3495 Fin15AnchoredAtom3525
    Fin15AnchoredAtom3652 Fin15AnchoredAtom3654 Fin15AnchoredAtom3655 Fin15AnchoredAtom3658
    Fin15AnchoredAtom3659 Fin15AnchoredAtom3664 Fin15AnchoredAtom3683 Fin15AnchoredAtom3684
    Fin15AnchoredAtom3689 Fin15AnchoredAtom3695 Fin15AnchoredAtom3978 Fin15AnchoredAtom3979
    Fin15AnchoredAtom3984 Fin15AnchoredAtom3990 Fin15AnchoredAtom4020 Fin15AnchoredAtom4308
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

theorem fin15Anchored_clause31759 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom2864 chi ∧
      ¬Fin15AnchoredAtom2866 chi ∧
      ¬Fin15AnchoredAtom2868 chi ∧
      ¬Fin15AnchoredAtom2870 chi ∧
      ¬Fin15AnchoredAtom2875 chi ∧
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
      ¬Fin15AnchoredAtom3978 chi ∧
      ¬Fin15AnchoredAtom3980 chi ∧
      ¬Fin15AnchoredAtom3985 chi ∧
      ¬Fin15AnchoredAtom3991 chi ∧
      ¬Fin15AnchoredAtom4021 chi ∧
      ¬Fin15AnchoredAtom4308 chi ∧
      ¬Fin15AnchoredAtom4310 chi ∧
      ¬Fin15AnchoredAtom4315 chi ∧
      ¬Fin15AnchoredAtom4321 chi ∧
      ¬Fin15AnchoredAtom4351 chi ∧
      ¬Fin15AnchoredAtom4792 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 3, 7, 9, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22158
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2850 Fin15AnchoredAtom2851 Fin15AnchoredAtom2853
    Fin15AnchoredAtom2855 Fin15AnchoredAtom2862 Fin15AnchoredAtom2864 Fin15AnchoredAtom2866
    Fin15AnchoredAtom2868 Fin15AnchoredAtom2870 Fin15AnchoredAtom2875 Fin15AnchoredAtom2992
    Fin15AnchoredAtom2994 Fin15AnchoredAtom2996 Fin15AnchoredAtom2998 Fin15AnchoredAtom3000
    Fin15AnchoredAtom3005 Fin15AnchoredAtom3023 Fin15AnchoredAtom3025 Fin15AnchoredAtom3030
    Fin15AnchoredAtom3036 Fin15AnchoredAtom3157 Fin15AnchoredAtom3159 Fin15AnchoredAtom3161
    Fin15AnchoredAtom3163 Fin15AnchoredAtom3165 Fin15AnchoredAtom3170 Fin15AnchoredAtom3188
    Fin15AnchoredAtom3190 Fin15AnchoredAtom3195 Fin15AnchoredAtom3201 Fin15AnchoredAtom3483
    Fin15AnchoredAtom3485 Fin15AnchoredAtom3490 Fin15AnchoredAtom3496 Fin15AnchoredAtom3526
    Fin15AnchoredAtom3652 Fin15AnchoredAtom3654 Fin15AnchoredAtom3656 Fin15AnchoredAtom3658
    Fin15AnchoredAtom3660 Fin15AnchoredAtom3665 Fin15AnchoredAtom3683 Fin15AnchoredAtom3685
    Fin15AnchoredAtom3690 Fin15AnchoredAtom3696 Fin15AnchoredAtom3978 Fin15AnchoredAtom3980
    Fin15AnchoredAtom3985 Fin15AnchoredAtom3991 Fin15AnchoredAtom4021 Fin15AnchoredAtom4308
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

theorem fin15Anchored_clause31760 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom2865 chi ∧
      ¬Fin15AnchoredAtom2866 chi ∧
      ¬Fin15AnchoredAtom2869 chi ∧
      ¬Fin15AnchoredAtom2870 chi ∧
      ¬Fin15AnchoredAtom2876 chi ∧
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
      ¬Fin15AnchoredAtom3979 chi ∧
      ¬Fin15AnchoredAtom3980 chi ∧
      ¬Fin15AnchoredAtom3986 chi ∧
      ¬Fin15AnchoredAtom3992 chi ∧
      ¬Fin15AnchoredAtom4022 chi ∧
      ¬Fin15AnchoredAtom4309 chi ∧
      ¬Fin15AnchoredAtom4310 chi ∧
      ¬Fin15AnchoredAtom4316 chi ∧
      ¬Fin15AnchoredAtom4322 chi ∧
      ¬Fin15AnchoredAtom4352 chi ∧
      ¬Fin15AnchoredAtom4793 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 3, 7, 9, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26254
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2850 Fin15AnchoredAtom2851 Fin15AnchoredAtom2854
    Fin15AnchoredAtom2855 Fin15AnchoredAtom2862 Fin15AnchoredAtom2865 Fin15AnchoredAtom2866
    Fin15AnchoredAtom2869 Fin15AnchoredAtom2870 Fin15AnchoredAtom2876 Fin15AnchoredAtom2992
    Fin15AnchoredAtom2995 Fin15AnchoredAtom2996 Fin15AnchoredAtom2999 Fin15AnchoredAtom3000
    Fin15AnchoredAtom3006 Fin15AnchoredAtom3024 Fin15AnchoredAtom3025 Fin15AnchoredAtom3031
    Fin15AnchoredAtom3037 Fin15AnchoredAtom3157 Fin15AnchoredAtom3160 Fin15AnchoredAtom3161
    Fin15AnchoredAtom3164 Fin15AnchoredAtom3165 Fin15AnchoredAtom3171 Fin15AnchoredAtom3189
    Fin15AnchoredAtom3190 Fin15AnchoredAtom3196 Fin15AnchoredAtom3202 Fin15AnchoredAtom3484
    Fin15AnchoredAtom3485 Fin15AnchoredAtom3491 Fin15AnchoredAtom3497 Fin15AnchoredAtom3527
    Fin15AnchoredAtom3652 Fin15AnchoredAtom3655 Fin15AnchoredAtom3656 Fin15AnchoredAtom3659
    Fin15AnchoredAtom3660 Fin15AnchoredAtom3666 Fin15AnchoredAtom3684 Fin15AnchoredAtom3685
    Fin15AnchoredAtom3691 Fin15AnchoredAtom3697 Fin15AnchoredAtom3979 Fin15AnchoredAtom3980
    Fin15AnchoredAtom3986 Fin15AnchoredAtom3992 Fin15AnchoredAtom4022 Fin15AnchoredAtom4309
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

theorem fin15Anchored_clause31761 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom2864 chi ∧
      ¬Fin15AnchoredAtom2865 chi ∧
      ¬Fin15AnchoredAtom2866 chi ∧
      ¬Fin15AnchoredAtom2874 chi ∧
      ¬Fin15AnchoredAtom2875 chi ∧
      ¬Fin15AnchoredAtom2876 chi ∧
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
      ¬Fin15AnchoredAtom3984 chi ∧
      ¬Fin15AnchoredAtom3985 chi ∧
      ¬Fin15AnchoredAtom3986 chi ∧
      ¬Fin15AnchoredAtom3996 chi ∧
      ¬Fin15AnchoredAtom4026 chi ∧
      ¬Fin15AnchoredAtom4314 chi ∧
      ¬Fin15AnchoredAtom4315 chi ∧
      ¬Fin15AnchoredAtom4316 chi ∧
      ¬Fin15AnchoredAtom4326 chi ∧
      ¬Fin15AnchoredAtom4356 chi ∧
      ¬Fin15AnchoredAtom4797 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 3, 7, 9, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29326
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2850 Fin15AnchoredAtom2853 Fin15AnchoredAtom2854
    Fin15AnchoredAtom2855 Fin15AnchoredAtom2864 Fin15AnchoredAtom2865 Fin15AnchoredAtom2866
    Fin15AnchoredAtom2874 Fin15AnchoredAtom2875 Fin15AnchoredAtom2876 Fin15AnchoredAtom2994
    Fin15AnchoredAtom2995 Fin15AnchoredAtom2996 Fin15AnchoredAtom3004 Fin15AnchoredAtom3005
    Fin15AnchoredAtom3006 Fin15AnchoredAtom3029 Fin15AnchoredAtom3030 Fin15AnchoredAtom3031
    Fin15AnchoredAtom3041 Fin15AnchoredAtom3159 Fin15AnchoredAtom3160 Fin15AnchoredAtom3161
    Fin15AnchoredAtom3169 Fin15AnchoredAtom3170 Fin15AnchoredAtom3171 Fin15AnchoredAtom3194
    Fin15AnchoredAtom3195 Fin15AnchoredAtom3196 Fin15AnchoredAtom3206 Fin15AnchoredAtom3489
    Fin15AnchoredAtom3490 Fin15AnchoredAtom3491 Fin15AnchoredAtom3501 Fin15AnchoredAtom3531
    Fin15AnchoredAtom3654 Fin15AnchoredAtom3655 Fin15AnchoredAtom3656 Fin15AnchoredAtom3664
    Fin15AnchoredAtom3665 Fin15AnchoredAtom3666 Fin15AnchoredAtom3689 Fin15AnchoredAtom3690
    Fin15AnchoredAtom3691 Fin15AnchoredAtom3701 Fin15AnchoredAtom3984 Fin15AnchoredAtom3985
    Fin15AnchoredAtom3986 Fin15AnchoredAtom3996 Fin15AnchoredAtom4026 Fin15AnchoredAtom4314
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

theorem fin15Anchored_clause31762 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom2868 chi ∧
      ¬Fin15AnchoredAtom2869 chi ∧
      ¬Fin15AnchoredAtom2870 chi ∧
      ¬Fin15AnchoredAtom2874 chi ∧
      ¬Fin15AnchoredAtom2875 chi ∧
      ¬Fin15AnchoredAtom2876 chi ∧
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
      ¬Fin15AnchoredAtom3990 chi ∧
      ¬Fin15AnchoredAtom3991 chi ∧
      ¬Fin15AnchoredAtom3992 chi ∧
      ¬Fin15AnchoredAtom3996 chi ∧
      ¬Fin15AnchoredAtom4030 chi ∧
      ¬Fin15AnchoredAtom4320 chi ∧
      ¬Fin15AnchoredAtom4321 chi ∧
      ¬Fin15AnchoredAtom4322 chi ∧
      ¬Fin15AnchoredAtom4326 chi ∧
      ¬Fin15AnchoredAtom4360 chi ∧
      ¬Fin15AnchoredAtom4801 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 3, 7, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29838
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2851 Fin15AnchoredAtom2853 Fin15AnchoredAtom2854
    Fin15AnchoredAtom2855 Fin15AnchoredAtom2868 Fin15AnchoredAtom2869 Fin15AnchoredAtom2870
    Fin15AnchoredAtom2874 Fin15AnchoredAtom2875 Fin15AnchoredAtom2876 Fin15AnchoredAtom2998
    Fin15AnchoredAtom2999 Fin15AnchoredAtom3000 Fin15AnchoredAtom3004 Fin15AnchoredAtom3005
    Fin15AnchoredAtom3006 Fin15AnchoredAtom3035 Fin15AnchoredAtom3036 Fin15AnchoredAtom3037
    Fin15AnchoredAtom3041 Fin15AnchoredAtom3163 Fin15AnchoredAtom3164 Fin15AnchoredAtom3165
    Fin15AnchoredAtom3169 Fin15AnchoredAtom3170 Fin15AnchoredAtom3171 Fin15AnchoredAtom3200
    Fin15AnchoredAtom3201 Fin15AnchoredAtom3202 Fin15AnchoredAtom3206 Fin15AnchoredAtom3495
    Fin15AnchoredAtom3496 Fin15AnchoredAtom3497 Fin15AnchoredAtom3501 Fin15AnchoredAtom3535
    Fin15AnchoredAtom3658 Fin15AnchoredAtom3659 Fin15AnchoredAtom3660 Fin15AnchoredAtom3664
    Fin15AnchoredAtom3665 Fin15AnchoredAtom3666 Fin15AnchoredAtom3695 Fin15AnchoredAtom3696
    Fin15AnchoredAtom3697 Fin15AnchoredAtom3701 Fin15AnchoredAtom3990 Fin15AnchoredAtom3991
    Fin15AnchoredAtom3992 Fin15AnchoredAtom3996 Fin15AnchoredAtom4030 Fin15AnchoredAtom4320
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

theorem fin15Anchored_clause31763 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom2864 chi ∧
      ¬Fin15AnchoredAtom2865 chi ∧
      ¬Fin15AnchoredAtom2866 chi ∧
      ¬Fin15AnchoredAtom2868 chi ∧
      ¬Fin15AnchoredAtom2869 chi ∧
      ¬Fin15AnchoredAtom2870 chi ∧
      ¬Fin15AnchoredAtom2874 chi ∧
      ¬Fin15AnchoredAtom2875 chi ∧
      ¬Fin15AnchoredAtom2876 chi ∧
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
      ¬Fin15AnchoredAtom4020 chi ∧
      ¬Fin15AnchoredAtom4021 chi ∧
      ¬Fin15AnchoredAtom4022 chi ∧
      ¬Fin15AnchoredAtom4026 chi ∧
      ¬Fin15AnchoredAtom4030 chi ∧
      ¬Fin15AnchoredAtom4350 chi ∧
      ¬Fin15AnchoredAtom4351 chi ∧
      ¬Fin15AnchoredAtom4352 chi ∧
      ¬Fin15AnchoredAtom4356 chi ∧
      ¬Fin15AnchoredAtom4360 chi ∧
      ¬Fin15AnchoredAtom4821 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 3, 9, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask30222
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2862 Fin15AnchoredAtom2864 Fin15AnchoredAtom2865
    Fin15AnchoredAtom2866 Fin15AnchoredAtom2868 Fin15AnchoredAtom2869 Fin15AnchoredAtom2870
    Fin15AnchoredAtom2874 Fin15AnchoredAtom2875 Fin15AnchoredAtom2876 Fin15AnchoredAtom3023
    Fin15AnchoredAtom3024 Fin15AnchoredAtom3025 Fin15AnchoredAtom3029 Fin15AnchoredAtom3030
    Fin15AnchoredAtom3031 Fin15AnchoredAtom3035 Fin15AnchoredAtom3036 Fin15AnchoredAtom3037
    Fin15AnchoredAtom3041 Fin15AnchoredAtom3188 Fin15AnchoredAtom3189 Fin15AnchoredAtom3190
    Fin15AnchoredAtom3194 Fin15AnchoredAtom3195 Fin15AnchoredAtom3196 Fin15AnchoredAtom3200
    Fin15AnchoredAtom3201 Fin15AnchoredAtom3202 Fin15AnchoredAtom3206 Fin15AnchoredAtom3525
    Fin15AnchoredAtom3526 Fin15AnchoredAtom3527 Fin15AnchoredAtom3531 Fin15AnchoredAtom3535
    Fin15AnchoredAtom3683 Fin15AnchoredAtom3684 Fin15AnchoredAtom3685 Fin15AnchoredAtom3689
    Fin15AnchoredAtom3690 Fin15AnchoredAtom3691 Fin15AnchoredAtom3695 Fin15AnchoredAtom3696
    Fin15AnchoredAtom3697 Fin15AnchoredAtom3701 Fin15AnchoredAtom4020 Fin15AnchoredAtom4021
    Fin15AnchoredAtom4022 Fin15AnchoredAtom4026 Fin15AnchoredAtom4030 Fin15AnchoredAtom4350
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

theorem fin15Anchored_clause31764 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2877 chi ∧
      ¬Fin15AnchoredAtom2878 chi ∧
      ¬Fin15AnchoredAtom2880 chi ∧
      ¬Fin15AnchoredAtom2881 chi ∧
      ¬Fin15AnchoredAtom2886 chi ∧
      ¬Fin15AnchoredAtom2888 chi ∧
      ¬Fin15AnchoredAtom2889 chi ∧
      ¬Fin15AnchoredAtom2895 chi ∧
      ¬Fin15AnchoredAtom2896 chi ∧
      ¬Fin15AnchoredAtom2907 chi ∧
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
      ¬Fin15AnchoredAtom3702 chi ∧
      ¬Fin15AnchoredAtom3704 chi ∧
      ¬Fin15AnchoredAtom3705 chi ∧
      ¬Fin15AnchoredAtom3711 chi ∧
      ¬Fin15AnchoredAtom3712 chi ∧
      ¬Fin15AnchoredAtom3723 chi ∧
      ¬Fin15AnchoredAtom3739 chi ∧
      ¬Fin15AnchoredAtom3740 chi ∧
      ¬Fin15AnchoredAtom3751 chi ∧
      ¬Fin15AnchoredAtom3772 chi ∧
      ¬Fin15AnchoredAtom3823 chi ∧
      ¬Fin15AnchoredAtom3824 chi ∧
      ¬Fin15AnchoredAtom3835 chi ∧
      ¬Fin15AnchoredAtom3856 chi ∧
      ¬Fin15AnchoredAtom3912 chi ∧
      ¬Fin15AnchoredAtom4363 chi ∧
      ¬Fin15AnchoredAtom4364 chi ∧
      ¬Fin15AnchoredAtom4375 chi ∧
      ¬Fin15AnchoredAtom4396 chi ∧
      ¬Fin15AnchoredAtom4452 chi ∧
      ¬Fin15AnchoredAtom4578 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 4, 5, 6, 7, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask01782
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2877 Fin15AnchoredAtom2878 Fin15AnchoredAtom2880
    Fin15AnchoredAtom2881 Fin15AnchoredAtom2886 Fin15AnchoredAtom2888 Fin15AnchoredAtom2889
    Fin15AnchoredAtom2895 Fin15AnchoredAtom2896 Fin15AnchoredAtom2907 Fin15AnchoredAtom2922
    Fin15AnchoredAtom2924 Fin15AnchoredAtom2925 Fin15AnchoredAtom2931 Fin15AnchoredAtom2932
    Fin15AnchoredAtom2943 Fin15AnchoredAtom2959 Fin15AnchoredAtom2960 Fin15AnchoredAtom2971
    Fin15AnchoredAtom2992 Fin15AnchoredAtom3207 Fin15AnchoredAtom3209 Fin15AnchoredAtom3210
    Fin15AnchoredAtom3216 Fin15AnchoredAtom3217 Fin15AnchoredAtom3228 Fin15AnchoredAtom3244
    Fin15AnchoredAtom3245 Fin15AnchoredAtom3256 Fin15AnchoredAtom3277 Fin15AnchoredAtom3328
    Fin15AnchoredAtom3329 Fin15AnchoredAtom3340 Fin15AnchoredAtom3361 Fin15AnchoredAtom3417
    Fin15AnchoredAtom3702 Fin15AnchoredAtom3704 Fin15AnchoredAtom3705 Fin15AnchoredAtom3711
    Fin15AnchoredAtom3712 Fin15AnchoredAtom3723 Fin15AnchoredAtom3739 Fin15AnchoredAtom3740
    Fin15AnchoredAtom3751 Fin15AnchoredAtom3772 Fin15AnchoredAtom3823 Fin15AnchoredAtom3824
    Fin15AnchoredAtom3835 Fin15AnchoredAtom3856 Fin15AnchoredAtom3912 Fin15AnchoredAtom4363
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

theorem fin15Anchored_clause31765 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2877 chi ∧
      ¬Fin15AnchoredAtom2878 chi ∧
      ¬Fin15AnchoredAtom2880 chi ∧
      ¬Fin15AnchoredAtom2883 chi ∧
      ¬Fin15AnchoredAtom2886 chi ∧
      ¬Fin15AnchoredAtom2888 chi ∧
      ¬Fin15AnchoredAtom2891 chi ∧
      ¬Fin15AnchoredAtom2895 chi ∧
      ¬Fin15AnchoredAtom2898 chi ∧
      ¬Fin15AnchoredAtom2909 chi ∧
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
      ¬Fin15AnchoredAtom3702 chi ∧
      ¬Fin15AnchoredAtom3704 chi ∧
      ¬Fin15AnchoredAtom3707 chi ∧
      ¬Fin15AnchoredAtom3711 chi ∧
      ¬Fin15AnchoredAtom3714 chi ∧
      ¬Fin15AnchoredAtom3725 chi ∧
      ¬Fin15AnchoredAtom3739 chi ∧
      ¬Fin15AnchoredAtom3742 chi ∧
      ¬Fin15AnchoredAtom3753 chi ∧
      ¬Fin15AnchoredAtom3774 chi ∧
      ¬Fin15AnchoredAtom3823 chi ∧
      ¬Fin15AnchoredAtom3826 chi ∧
      ¬Fin15AnchoredAtom3837 chi ∧
      ¬Fin15AnchoredAtom3858 chi ∧
      ¬Fin15AnchoredAtom3914 chi ∧
      ¬Fin15AnchoredAtom4363 chi ∧
      ¬Fin15AnchoredAtom4366 chi ∧
      ¬Fin15AnchoredAtom4377 chi ∧
      ¬Fin15AnchoredAtom4398 chi ∧
      ¬Fin15AnchoredAtom4454 chi ∧
      ¬Fin15AnchoredAtom4580 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 4, 5, 6, 7, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask04854
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2877 Fin15AnchoredAtom2878 Fin15AnchoredAtom2880
    Fin15AnchoredAtom2883 Fin15AnchoredAtom2886 Fin15AnchoredAtom2888 Fin15AnchoredAtom2891
    Fin15AnchoredAtom2895 Fin15AnchoredAtom2898 Fin15AnchoredAtom2909 Fin15AnchoredAtom2922
    Fin15AnchoredAtom2924 Fin15AnchoredAtom2927 Fin15AnchoredAtom2931 Fin15AnchoredAtom2934
    Fin15AnchoredAtom2945 Fin15AnchoredAtom2959 Fin15AnchoredAtom2962 Fin15AnchoredAtom2973
    Fin15AnchoredAtom2994 Fin15AnchoredAtom3207 Fin15AnchoredAtom3209 Fin15AnchoredAtom3212
    Fin15AnchoredAtom3216 Fin15AnchoredAtom3219 Fin15AnchoredAtom3230 Fin15AnchoredAtom3244
    Fin15AnchoredAtom3247 Fin15AnchoredAtom3258 Fin15AnchoredAtom3279 Fin15AnchoredAtom3328
    Fin15AnchoredAtom3331 Fin15AnchoredAtom3342 Fin15AnchoredAtom3363 Fin15AnchoredAtom3419
    Fin15AnchoredAtom3702 Fin15AnchoredAtom3704 Fin15AnchoredAtom3707 Fin15AnchoredAtom3711
    Fin15AnchoredAtom3714 Fin15AnchoredAtom3725 Fin15AnchoredAtom3739 Fin15AnchoredAtom3742
    Fin15AnchoredAtom3753 Fin15AnchoredAtom3774 Fin15AnchoredAtom3823 Fin15AnchoredAtom3826
    Fin15AnchoredAtom3837 Fin15AnchoredAtom3858 Fin15AnchoredAtom3914 Fin15AnchoredAtom4363
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

theorem fin15Anchored_clause31766 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2877 chi ∧
      ¬Fin15AnchoredAtom2878 chi ∧
      ¬Fin15AnchoredAtom2880 chi ∧
      ¬Fin15AnchoredAtom2884 chi ∧
      ¬Fin15AnchoredAtom2886 chi ∧
      ¬Fin15AnchoredAtom2888 chi ∧
      ¬Fin15AnchoredAtom2892 chi ∧
      ¬Fin15AnchoredAtom2895 chi ∧
      ¬Fin15AnchoredAtom2899 chi ∧
      ¬Fin15AnchoredAtom2910 chi ∧
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
      ¬Fin15AnchoredAtom3702 chi ∧
      ¬Fin15AnchoredAtom3704 chi ∧
      ¬Fin15AnchoredAtom3708 chi ∧
      ¬Fin15AnchoredAtom3711 chi ∧
      ¬Fin15AnchoredAtom3715 chi ∧
      ¬Fin15AnchoredAtom3726 chi ∧
      ¬Fin15AnchoredAtom3739 chi ∧
      ¬Fin15AnchoredAtom3743 chi ∧
      ¬Fin15AnchoredAtom3754 chi ∧
      ¬Fin15AnchoredAtom3775 chi ∧
      ¬Fin15AnchoredAtom3823 chi ∧
      ¬Fin15AnchoredAtom3827 chi ∧
      ¬Fin15AnchoredAtom3838 chi ∧
      ¬Fin15AnchoredAtom3859 chi ∧
      ¬Fin15AnchoredAtom3915 chi ∧
      ¬Fin15AnchoredAtom4363 chi ∧
      ¬Fin15AnchoredAtom4367 chi ∧
      ¬Fin15AnchoredAtom4378 chi ∧
      ¬Fin15AnchoredAtom4399 chi ∧
      ¬Fin15AnchoredAtom4455 chi ∧
      ¬Fin15AnchoredAtom4581 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 4, 5, 6, 7, 9, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask08950
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2877 Fin15AnchoredAtom2878 Fin15AnchoredAtom2880
    Fin15AnchoredAtom2884 Fin15AnchoredAtom2886 Fin15AnchoredAtom2888 Fin15AnchoredAtom2892
    Fin15AnchoredAtom2895 Fin15AnchoredAtom2899 Fin15AnchoredAtom2910 Fin15AnchoredAtom2922
    Fin15AnchoredAtom2924 Fin15AnchoredAtom2928 Fin15AnchoredAtom2931 Fin15AnchoredAtom2935
    Fin15AnchoredAtom2946 Fin15AnchoredAtom2959 Fin15AnchoredAtom2963 Fin15AnchoredAtom2974
    Fin15AnchoredAtom2995 Fin15AnchoredAtom3207 Fin15AnchoredAtom3209 Fin15AnchoredAtom3213
    Fin15AnchoredAtom3216 Fin15AnchoredAtom3220 Fin15AnchoredAtom3231 Fin15AnchoredAtom3244
    Fin15AnchoredAtom3248 Fin15AnchoredAtom3259 Fin15AnchoredAtom3280 Fin15AnchoredAtom3328
    Fin15AnchoredAtom3332 Fin15AnchoredAtom3343 Fin15AnchoredAtom3364 Fin15AnchoredAtom3420
    Fin15AnchoredAtom3702 Fin15AnchoredAtom3704 Fin15AnchoredAtom3708 Fin15AnchoredAtom3711
    Fin15AnchoredAtom3715 Fin15AnchoredAtom3726 Fin15AnchoredAtom3739 Fin15AnchoredAtom3743
    Fin15AnchoredAtom3754 Fin15AnchoredAtom3775 Fin15AnchoredAtom3823 Fin15AnchoredAtom3827
    Fin15AnchoredAtom3838 Fin15AnchoredAtom3859 Fin15AnchoredAtom3915 Fin15AnchoredAtom4363
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

theorem fin15Anchored_clause31767 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2877 chi ∧
      ¬Fin15AnchoredAtom2878 chi ∧
      ¬Fin15AnchoredAtom2880 chi ∧
      ¬Fin15AnchoredAtom2885 chi ∧
      ¬Fin15AnchoredAtom2886 chi ∧
      ¬Fin15AnchoredAtom2888 chi ∧
      ¬Fin15AnchoredAtom2893 chi ∧
      ¬Fin15AnchoredAtom2895 chi ∧
      ¬Fin15AnchoredAtom2900 chi ∧
      ¬Fin15AnchoredAtom2911 chi ∧
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
      ¬Fin15AnchoredAtom3702 chi ∧
      ¬Fin15AnchoredAtom3704 chi ∧
      ¬Fin15AnchoredAtom3709 chi ∧
      ¬Fin15AnchoredAtom3711 chi ∧
      ¬Fin15AnchoredAtom3716 chi ∧
      ¬Fin15AnchoredAtom3727 chi ∧
      ¬Fin15AnchoredAtom3739 chi ∧
      ¬Fin15AnchoredAtom3744 chi ∧
      ¬Fin15AnchoredAtom3755 chi ∧
      ¬Fin15AnchoredAtom3776 chi ∧
      ¬Fin15AnchoredAtom3823 chi ∧
      ¬Fin15AnchoredAtom3828 chi ∧
      ¬Fin15AnchoredAtom3839 chi ∧
      ¬Fin15AnchoredAtom3860 chi ∧
      ¬Fin15AnchoredAtom3916 chi ∧
      ¬Fin15AnchoredAtom4363 chi ∧
      ¬Fin15AnchoredAtom4368 chi ∧
      ¬Fin15AnchoredAtom4379 chi ∧
      ¬Fin15AnchoredAtom4400 chi ∧
      ¬Fin15AnchoredAtom4456 chi ∧
      ¬Fin15AnchoredAtom4582 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 4, 5, 6, 7, 9, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17142
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2877 Fin15AnchoredAtom2878 Fin15AnchoredAtom2880
    Fin15AnchoredAtom2885 Fin15AnchoredAtom2886 Fin15AnchoredAtom2888 Fin15AnchoredAtom2893
    Fin15AnchoredAtom2895 Fin15AnchoredAtom2900 Fin15AnchoredAtom2911 Fin15AnchoredAtom2922
    Fin15AnchoredAtom2924 Fin15AnchoredAtom2929 Fin15AnchoredAtom2931 Fin15AnchoredAtom2936
    Fin15AnchoredAtom2947 Fin15AnchoredAtom2959 Fin15AnchoredAtom2964 Fin15AnchoredAtom2975
    Fin15AnchoredAtom2996 Fin15AnchoredAtom3207 Fin15AnchoredAtom3209 Fin15AnchoredAtom3214
    Fin15AnchoredAtom3216 Fin15AnchoredAtom3221 Fin15AnchoredAtom3232 Fin15AnchoredAtom3244
    Fin15AnchoredAtom3249 Fin15AnchoredAtom3260 Fin15AnchoredAtom3281 Fin15AnchoredAtom3328
    Fin15AnchoredAtom3333 Fin15AnchoredAtom3344 Fin15AnchoredAtom3365 Fin15AnchoredAtom3421
    Fin15AnchoredAtom3702 Fin15AnchoredAtom3704 Fin15AnchoredAtom3709 Fin15AnchoredAtom3711
    Fin15AnchoredAtom3716 Fin15AnchoredAtom3727 Fin15AnchoredAtom3739 Fin15AnchoredAtom3744
    Fin15AnchoredAtom3755 Fin15AnchoredAtom3776 Fin15AnchoredAtom3823 Fin15AnchoredAtom3828
    Fin15AnchoredAtom3839 Fin15AnchoredAtom3860 Fin15AnchoredAtom3916 Fin15AnchoredAtom4363
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

theorem fin15Anchored_clause31768 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2877 chi ∧
      ¬Fin15AnchoredAtom2878 chi ∧
      ¬Fin15AnchoredAtom2881 chi ∧
      ¬Fin15AnchoredAtom2883 chi ∧
      ¬Fin15AnchoredAtom2886 chi ∧
      ¬Fin15AnchoredAtom2889 chi ∧
      ¬Fin15AnchoredAtom2891 chi ∧
      ¬Fin15AnchoredAtom2896 chi ∧
      ¬Fin15AnchoredAtom2898 chi ∧
      ¬Fin15AnchoredAtom2913 chi ∧
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
      ¬Fin15AnchoredAtom3702 chi ∧
      ¬Fin15AnchoredAtom3705 chi ∧
      ¬Fin15AnchoredAtom3707 chi ∧
      ¬Fin15AnchoredAtom3712 chi ∧
      ¬Fin15AnchoredAtom3714 chi ∧
      ¬Fin15AnchoredAtom3729 chi ∧
      ¬Fin15AnchoredAtom3740 chi ∧
      ¬Fin15AnchoredAtom3742 chi ∧
      ¬Fin15AnchoredAtom3757 chi ∧
      ¬Fin15AnchoredAtom3778 chi ∧
      ¬Fin15AnchoredAtom3824 chi ∧
      ¬Fin15AnchoredAtom3826 chi ∧
      ¬Fin15AnchoredAtom3841 chi ∧
      ¬Fin15AnchoredAtom3862 chi ∧
      ¬Fin15AnchoredAtom3918 chi ∧
      ¬Fin15AnchoredAtom4364 chi ∧
      ¬Fin15AnchoredAtom4366 chi ∧
      ¬Fin15AnchoredAtom4381 chi ∧
      ¬Fin15AnchoredAtom4402 chi ∧
      ¬Fin15AnchoredAtom4458 chi ∧
      ¬Fin15AnchoredAtom4584 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 4, 5, 6, 7, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05366
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2877 Fin15AnchoredAtom2878 Fin15AnchoredAtom2881
    Fin15AnchoredAtom2883 Fin15AnchoredAtom2886 Fin15AnchoredAtom2889 Fin15AnchoredAtom2891
    Fin15AnchoredAtom2896 Fin15AnchoredAtom2898 Fin15AnchoredAtom2913 Fin15AnchoredAtom2922
    Fin15AnchoredAtom2925 Fin15AnchoredAtom2927 Fin15AnchoredAtom2932 Fin15AnchoredAtom2934
    Fin15AnchoredAtom2949 Fin15AnchoredAtom2960 Fin15AnchoredAtom2962 Fin15AnchoredAtom2977
    Fin15AnchoredAtom2998 Fin15AnchoredAtom3207 Fin15AnchoredAtom3210 Fin15AnchoredAtom3212
    Fin15AnchoredAtom3217 Fin15AnchoredAtom3219 Fin15AnchoredAtom3234 Fin15AnchoredAtom3245
    Fin15AnchoredAtom3247 Fin15AnchoredAtom3262 Fin15AnchoredAtom3283 Fin15AnchoredAtom3329
    Fin15AnchoredAtom3331 Fin15AnchoredAtom3346 Fin15AnchoredAtom3367 Fin15AnchoredAtom3423
    Fin15AnchoredAtom3702 Fin15AnchoredAtom3705 Fin15AnchoredAtom3707 Fin15AnchoredAtom3712
    Fin15AnchoredAtom3714 Fin15AnchoredAtom3729 Fin15AnchoredAtom3740 Fin15AnchoredAtom3742
    Fin15AnchoredAtom3757 Fin15AnchoredAtom3778 Fin15AnchoredAtom3824 Fin15AnchoredAtom3826
    Fin15AnchoredAtom3841 Fin15AnchoredAtom3862 Fin15AnchoredAtom3918 Fin15AnchoredAtom4364
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

theorem fin15Anchored_clause31769 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2877 chi ∧
      ¬Fin15AnchoredAtom2878 chi ∧
      ¬Fin15AnchoredAtom2881 chi ∧
      ¬Fin15AnchoredAtom2884 chi ∧
      ¬Fin15AnchoredAtom2886 chi ∧
      ¬Fin15AnchoredAtom2889 chi ∧
      ¬Fin15AnchoredAtom2892 chi ∧
      ¬Fin15AnchoredAtom2896 chi ∧
      ¬Fin15AnchoredAtom2899 chi ∧
      ¬Fin15AnchoredAtom2914 chi ∧
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
      ¬Fin15AnchoredAtom4364 chi ∧
      ¬Fin15AnchoredAtom4367 chi ∧
      ¬Fin15AnchoredAtom4382 chi ∧
      ¬Fin15AnchoredAtom4403 chi ∧
      ¬Fin15AnchoredAtom4459 chi ∧
      ¬Fin15AnchoredAtom4585 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 4, 5, 6, 7, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09462
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2877 Fin15AnchoredAtom2878 Fin15AnchoredAtom2881
    Fin15AnchoredAtom2884 Fin15AnchoredAtom2886 Fin15AnchoredAtom2889 Fin15AnchoredAtom2892
    Fin15AnchoredAtom2896 Fin15AnchoredAtom2899 Fin15AnchoredAtom2914 Fin15AnchoredAtom2922
    Fin15AnchoredAtom2925 Fin15AnchoredAtom2928 Fin15AnchoredAtom2932 Fin15AnchoredAtom2935
    Fin15AnchoredAtom2950 Fin15AnchoredAtom2960 Fin15AnchoredAtom2963 Fin15AnchoredAtom2978
    Fin15AnchoredAtom2999 Fin15AnchoredAtom3207 Fin15AnchoredAtom3210 Fin15AnchoredAtom3213
    Fin15AnchoredAtom3217 Fin15AnchoredAtom3220 Fin15AnchoredAtom3235 Fin15AnchoredAtom3245
    Fin15AnchoredAtom3248 Fin15AnchoredAtom3263 Fin15AnchoredAtom3284 Fin15AnchoredAtom3329
    Fin15AnchoredAtom3332 Fin15AnchoredAtom3347 Fin15AnchoredAtom3368 Fin15AnchoredAtom3424
    Fin15AnchoredAtom3702 Fin15AnchoredAtom3705 Fin15AnchoredAtom3708 Fin15AnchoredAtom3712
    Fin15AnchoredAtom3715 Fin15AnchoredAtom3730 Fin15AnchoredAtom3740 Fin15AnchoredAtom3743
    Fin15AnchoredAtom3758 Fin15AnchoredAtom3779 Fin15AnchoredAtom3824 Fin15AnchoredAtom3827
    Fin15AnchoredAtom3842 Fin15AnchoredAtom3863 Fin15AnchoredAtom3919 Fin15AnchoredAtom4364
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

theorem fin15Anchored_clause31770 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2877 chi ∧
      ¬Fin15AnchoredAtom2878 chi ∧
      ¬Fin15AnchoredAtom2881 chi ∧
      ¬Fin15AnchoredAtom2885 chi ∧
      ¬Fin15AnchoredAtom2886 chi ∧
      ¬Fin15AnchoredAtom2889 chi ∧
      ¬Fin15AnchoredAtom2893 chi ∧
      ¬Fin15AnchoredAtom2896 chi ∧
      ¬Fin15AnchoredAtom2900 chi ∧
      ¬Fin15AnchoredAtom2915 chi ∧
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
      ¬Fin15AnchoredAtom4364 chi ∧
      ¬Fin15AnchoredAtom4368 chi ∧
      ¬Fin15AnchoredAtom4383 chi ∧
      ¬Fin15AnchoredAtom4404 chi ∧
      ¬Fin15AnchoredAtom4460 chi ∧
      ¬Fin15AnchoredAtom4586 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 4, 5, 6, 7, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17654
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2877 Fin15AnchoredAtom2878 Fin15AnchoredAtom2881
    Fin15AnchoredAtom2885 Fin15AnchoredAtom2886 Fin15AnchoredAtom2889 Fin15AnchoredAtom2893
    Fin15AnchoredAtom2896 Fin15AnchoredAtom2900 Fin15AnchoredAtom2915 Fin15AnchoredAtom2922
    Fin15AnchoredAtom2925 Fin15AnchoredAtom2929 Fin15AnchoredAtom2932 Fin15AnchoredAtom2936
    Fin15AnchoredAtom2951 Fin15AnchoredAtom2960 Fin15AnchoredAtom2964 Fin15AnchoredAtom2979
    Fin15AnchoredAtom3000 Fin15AnchoredAtom3207 Fin15AnchoredAtom3210 Fin15AnchoredAtom3214
    Fin15AnchoredAtom3217 Fin15AnchoredAtom3221 Fin15AnchoredAtom3236 Fin15AnchoredAtom3245
    Fin15AnchoredAtom3249 Fin15AnchoredAtom3264 Fin15AnchoredAtom3285 Fin15AnchoredAtom3329
    Fin15AnchoredAtom3333 Fin15AnchoredAtom3348 Fin15AnchoredAtom3369 Fin15AnchoredAtom3425
    Fin15AnchoredAtom3702 Fin15AnchoredAtom3705 Fin15AnchoredAtom3709 Fin15AnchoredAtom3712
    Fin15AnchoredAtom3716 Fin15AnchoredAtom3731 Fin15AnchoredAtom3740 Fin15AnchoredAtom3744
    Fin15AnchoredAtom3759 Fin15AnchoredAtom3780 Fin15AnchoredAtom3824 Fin15AnchoredAtom3828
    Fin15AnchoredAtom3843 Fin15AnchoredAtom3864 Fin15AnchoredAtom3920 Fin15AnchoredAtom4364
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

theorem fin15Anchored_clause31771 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2877 chi ∧
      ¬Fin15AnchoredAtom2878 chi ∧
      ¬Fin15AnchoredAtom2883 chi ∧
      ¬Fin15AnchoredAtom2884 chi ∧
      ¬Fin15AnchoredAtom2886 chi ∧
      ¬Fin15AnchoredAtom2891 chi ∧
      ¬Fin15AnchoredAtom2892 chi ∧
      ¬Fin15AnchoredAtom2898 chi ∧
      ¬Fin15AnchoredAtom2899 chi ∧
      ¬Fin15AnchoredAtom2919 chi ∧
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
      ¬Fin15AnchoredAtom4366 chi ∧
      ¬Fin15AnchoredAtom4367 chi ∧
      ¬Fin15AnchoredAtom4387 chi ∧
      ¬Fin15AnchoredAtom4408 chi ∧
      ¬Fin15AnchoredAtom4464 chi ∧
      ¬Fin15AnchoredAtom4590 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 4, 5, 6, 7, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask12534
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2877 Fin15AnchoredAtom2878 Fin15AnchoredAtom2883
    Fin15AnchoredAtom2884 Fin15AnchoredAtom2886 Fin15AnchoredAtom2891 Fin15AnchoredAtom2892
    Fin15AnchoredAtom2898 Fin15AnchoredAtom2899 Fin15AnchoredAtom2919 Fin15AnchoredAtom2922
    Fin15AnchoredAtom2927 Fin15AnchoredAtom2928 Fin15AnchoredAtom2934 Fin15AnchoredAtom2935
    Fin15AnchoredAtom2955 Fin15AnchoredAtom2962 Fin15AnchoredAtom2963 Fin15AnchoredAtom2983
    Fin15AnchoredAtom3004 Fin15AnchoredAtom3207 Fin15AnchoredAtom3212 Fin15AnchoredAtom3213
    Fin15AnchoredAtom3219 Fin15AnchoredAtom3220 Fin15AnchoredAtom3240 Fin15AnchoredAtom3247
    Fin15AnchoredAtom3248 Fin15AnchoredAtom3268 Fin15AnchoredAtom3289 Fin15AnchoredAtom3331
    Fin15AnchoredAtom3332 Fin15AnchoredAtom3352 Fin15AnchoredAtom3373 Fin15AnchoredAtom3429
    Fin15AnchoredAtom3702 Fin15AnchoredAtom3707 Fin15AnchoredAtom3708 Fin15AnchoredAtom3714
    Fin15AnchoredAtom3715 Fin15AnchoredAtom3735 Fin15AnchoredAtom3742 Fin15AnchoredAtom3743
    Fin15AnchoredAtom3763 Fin15AnchoredAtom3784 Fin15AnchoredAtom3826 Fin15AnchoredAtom3827
    Fin15AnchoredAtom3847 Fin15AnchoredAtom3868 Fin15AnchoredAtom3924 Fin15AnchoredAtom4366
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

theorem fin15Anchored_clause31772 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2877 chi ∧
      ¬Fin15AnchoredAtom2878 chi ∧
      ¬Fin15AnchoredAtom2883 chi ∧
      ¬Fin15AnchoredAtom2885 chi ∧
      ¬Fin15AnchoredAtom2886 chi ∧
      ¬Fin15AnchoredAtom2891 chi ∧
      ¬Fin15AnchoredAtom2893 chi ∧
      ¬Fin15AnchoredAtom2898 chi ∧
      ¬Fin15AnchoredAtom2900 chi ∧
      ¬Fin15AnchoredAtom2920 chi ∧
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
      ¬Fin15AnchoredAtom4366 chi ∧
      ¬Fin15AnchoredAtom4368 chi ∧
      ¬Fin15AnchoredAtom4388 chi ∧
      ¬Fin15AnchoredAtom4409 chi ∧
      ¬Fin15AnchoredAtom4465 chi ∧
      ¬Fin15AnchoredAtom4591 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 4, 5, 6, 7, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask20726
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2877 Fin15AnchoredAtom2878 Fin15AnchoredAtom2883
    Fin15AnchoredAtom2885 Fin15AnchoredAtom2886 Fin15AnchoredAtom2891 Fin15AnchoredAtom2893
    Fin15AnchoredAtom2898 Fin15AnchoredAtom2900 Fin15AnchoredAtom2920 Fin15AnchoredAtom2922
    Fin15AnchoredAtom2927 Fin15AnchoredAtom2929 Fin15AnchoredAtom2934 Fin15AnchoredAtom2936
    Fin15AnchoredAtom2956 Fin15AnchoredAtom2962 Fin15AnchoredAtom2964 Fin15AnchoredAtom2984
    Fin15AnchoredAtom3005 Fin15AnchoredAtom3207 Fin15AnchoredAtom3212 Fin15AnchoredAtom3214
    Fin15AnchoredAtom3219 Fin15AnchoredAtom3221 Fin15AnchoredAtom3241 Fin15AnchoredAtom3247
    Fin15AnchoredAtom3249 Fin15AnchoredAtom3269 Fin15AnchoredAtom3290 Fin15AnchoredAtom3331
    Fin15AnchoredAtom3333 Fin15AnchoredAtom3353 Fin15AnchoredAtom3374 Fin15AnchoredAtom3430
    Fin15AnchoredAtom3702 Fin15AnchoredAtom3707 Fin15AnchoredAtom3709 Fin15AnchoredAtom3714
    Fin15AnchoredAtom3716 Fin15AnchoredAtom3736 Fin15AnchoredAtom3742 Fin15AnchoredAtom3744
    Fin15AnchoredAtom3764 Fin15AnchoredAtom3785 Fin15AnchoredAtom3826 Fin15AnchoredAtom3828
    Fin15AnchoredAtom3848 Fin15AnchoredAtom3869 Fin15AnchoredAtom3925 Fin15AnchoredAtom4366
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

theorem fin15Anchored_clause31773 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2877 chi ∧
      ¬Fin15AnchoredAtom2878 chi ∧
      ¬Fin15AnchoredAtom2884 chi ∧
      ¬Fin15AnchoredAtom2885 chi ∧
      ¬Fin15AnchoredAtom2886 chi ∧
      ¬Fin15AnchoredAtom2892 chi ∧
      ¬Fin15AnchoredAtom2893 chi ∧
      ¬Fin15AnchoredAtom2899 chi ∧
      ¬Fin15AnchoredAtom2900 chi ∧
      ¬Fin15AnchoredAtom2921 chi ∧
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
      ¬Fin15AnchoredAtom4367 chi ∧
      ¬Fin15AnchoredAtom4368 chi ∧
      ¬Fin15AnchoredAtom4389 chi ∧
      ¬Fin15AnchoredAtom4410 chi ∧
      ¬Fin15AnchoredAtom4466 chi ∧
      ¬Fin15AnchoredAtom4592 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 4, 5, 6, 7, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask24822
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2877 Fin15AnchoredAtom2878 Fin15AnchoredAtom2884
    Fin15AnchoredAtom2885 Fin15AnchoredAtom2886 Fin15AnchoredAtom2892 Fin15AnchoredAtom2893
    Fin15AnchoredAtom2899 Fin15AnchoredAtom2900 Fin15AnchoredAtom2921 Fin15AnchoredAtom2922
    Fin15AnchoredAtom2928 Fin15AnchoredAtom2929 Fin15AnchoredAtom2935 Fin15AnchoredAtom2936
    Fin15AnchoredAtom2957 Fin15AnchoredAtom2963 Fin15AnchoredAtom2964 Fin15AnchoredAtom2985
    Fin15AnchoredAtom3006 Fin15AnchoredAtom3207 Fin15AnchoredAtom3213 Fin15AnchoredAtom3214
    Fin15AnchoredAtom3220 Fin15AnchoredAtom3221 Fin15AnchoredAtom3242 Fin15AnchoredAtom3248
    Fin15AnchoredAtom3249 Fin15AnchoredAtom3270 Fin15AnchoredAtom3291 Fin15AnchoredAtom3332
    Fin15AnchoredAtom3333 Fin15AnchoredAtom3354 Fin15AnchoredAtom3375 Fin15AnchoredAtom3431
    Fin15AnchoredAtom3702 Fin15AnchoredAtom3708 Fin15AnchoredAtom3709 Fin15AnchoredAtom3715
    Fin15AnchoredAtom3716 Fin15AnchoredAtom3737 Fin15AnchoredAtom3743 Fin15AnchoredAtom3744
    Fin15AnchoredAtom3765 Fin15AnchoredAtom3786 Fin15AnchoredAtom3827 Fin15AnchoredAtom3828
    Fin15AnchoredAtom3849 Fin15AnchoredAtom3870 Fin15AnchoredAtom3926 Fin15AnchoredAtom4367
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

theorem fin15Anchored_clause31774 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2877 chi ∧
      ¬Fin15AnchoredAtom2880 chi ∧
      ¬Fin15AnchoredAtom2881 chi ∧
      ¬Fin15AnchoredAtom2882 chi ∧
      ¬Fin15AnchoredAtom2888 chi ∧
      ¬Fin15AnchoredAtom2889 chi ∧
      ¬Fin15AnchoredAtom2890 chi ∧
      ¬Fin15AnchoredAtom2907 chi ∧
      ¬Fin15AnchoredAtom2908 chi ∧
      ¬Fin15AnchoredAtom2912 chi ∧
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
      ¬Fin15AnchoredAtom3209 chi ∧
      ¬Fin15AnchoredAtom3210 chi ∧
      ¬Fin15AnchoredAtom3211 chi ∧
      ¬Fin15AnchoredAtom3228 chi ∧
      ¬Fin15AnchoredAtom3229 chi ∧
      ¬Fin15AnchoredAtom3233 chi ∧
      ¬Fin15AnchoredAtom3256 chi ∧
      ¬Fin15AnchoredAtom3257 chi ∧
      ¬Fin15AnchoredAtom3261 chi ∧
      ¬Fin15AnchoredAtom3307 chi ∧
      ¬Fin15AnchoredAtom3340 chi ∧
      ¬Fin15AnchoredAtom3341 chi ∧
      ¬Fin15AnchoredAtom3345 chi ∧
      ¬Fin15AnchoredAtom3391 chi ∧
      ¬Fin15AnchoredAtom3447 chi ∧
      ¬Fin15AnchoredAtom3704 chi ∧
      ¬Fin15AnchoredAtom3705 chi ∧
      ¬Fin15AnchoredAtom3706 chi ∧
      ¬Fin15AnchoredAtom3723 chi ∧
      ¬Fin15AnchoredAtom3724 chi ∧
      ¬Fin15AnchoredAtom3728 chi ∧
      ¬Fin15AnchoredAtom3751 chi ∧
      ¬Fin15AnchoredAtom3752 chi ∧
      ¬Fin15AnchoredAtom3756 chi ∧
      ¬Fin15AnchoredAtom3802 chi ∧
      ¬Fin15AnchoredAtom3835 chi ∧
      ¬Fin15AnchoredAtom3836 chi ∧
      ¬Fin15AnchoredAtom3840 chi ∧
      ¬Fin15AnchoredAtom3886 chi ∧
      ¬Fin15AnchoredAtom3942 chi ∧
      ¬Fin15AnchoredAtom4375 chi ∧
      ¬Fin15AnchoredAtom4376 chi ∧
      ¬Fin15AnchoredAtom4380 chi ∧
      ¬Fin15AnchoredAtom4426 chi ∧
      ¬Fin15AnchoredAtom4482 chi ∧
      ¬Fin15AnchoredAtom4608 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 4, 5, 6, 9, 10, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask03702
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2877 Fin15AnchoredAtom2880 Fin15AnchoredAtom2881
    Fin15AnchoredAtom2882 Fin15AnchoredAtom2888 Fin15AnchoredAtom2889 Fin15AnchoredAtom2890
    Fin15AnchoredAtom2907 Fin15AnchoredAtom2908 Fin15AnchoredAtom2912 Fin15AnchoredAtom2924
    Fin15AnchoredAtom2925 Fin15AnchoredAtom2926 Fin15AnchoredAtom2943 Fin15AnchoredAtom2944
    Fin15AnchoredAtom2948 Fin15AnchoredAtom2971 Fin15AnchoredAtom2972 Fin15AnchoredAtom2976
    Fin15AnchoredAtom3022 Fin15AnchoredAtom3209 Fin15AnchoredAtom3210 Fin15AnchoredAtom3211
    Fin15AnchoredAtom3228 Fin15AnchoredAtom3229 Fin15AnchoredAtom3233 Fin15AnchoredAtom3256
    Fin15AnchoredAtom3257 Fin15AnchoredAtom3261 Fin15AnchoredAtom3307 Fin15AnchoredAtom3340
    Fin15AnchoredAtom3341 Fin15AnchoredAtom3345 Fin15AnchoredAtom3391 Fin15AnchoredAtom3447
    Fin15AnchoredAtom3704 Fin15AnchoredAtom3705 Fin15AnchoredAtom3706 Fin15AnchoredAtom3723
    Fin15AnchoredAtom3724 Fin15AnchoredAtom3728 Fin15AnchoredAtom3751 Fin15AnchoredAtom3752
    Fin15AnchoredAtom3756 Fin15AnchoredAtom3802 Fin15AnchoredAtom3835 Fin15AnchoredAtom3836
    Fin15AnchoredAtom3840 Fin15AnchoredAtom3886 Fin15AnchoredAtom3942 Fin15AnchoredAtom4375
    Fin15AnchoredAtom4376 Fin15AnchoredAtom4380 Fin15AnchoredAtom4426 Fin15AnchoredAtom4482
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

theorem fin15Anchored_clause31775 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2877 chi ∧
      ¬Fin15AnchoredAtom2880 chi ∧
      ¬Fin15AnchoredAtom2881 chi ∧
      ¬Fin15AnchoredAtom2883 chi ∧
      ¬Fin15AnchoredAtom2888 chi ∧
      ¬Fin15AnchoredAtom2889 chi ∧
      ¬Fin15AnchoredAtom2891 chi ∧
      ¬Fin15AnchoredAtom2907 chi ∧
      ¬Fin15AnchoredAtom2909 chi ∧
      ¬Fin15AnchoredAtom2913 chi ∧
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
      ¬Fin15AnchoredAtom4375 chi ∧
      ¬Fin15AnchoredAtom4377 chi ∧
      ¬Fin15AnchoredAtom4381 chi ∧
      ¬Fin15AnchoredAtom4427 chi ∧
      ¬Fin15AnchoredAtom4483 chi ∧
      ¬Fin15AnchoredAtom4609 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 4, 5, 6, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05750
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2877 Fin15AnchoredAtom2880 Fin15AnchoredAtom2881
    Fin15AnchoredAtom2883 Fin15AnchoredAtom2888 Fin15AnchoredAtom2889 Fin15AnchoredAtom2891
    Fin15AnchoredAtom2907 Fin15AnchoredAtom2909 Fin15AnchoredAtom2913 Fin15AnchoredAtom2924
    Fin15AnchoredAtom2925 Fin15AnchoredAtom2927 Fin15AnchoredAtom2943 Fin15AnchoredAtom2945
    Fin15AnchoredAtom2949 Fin15AnchoredAtom2971 Fin15AnchoredAtom2973 Fin15AnchoredAtom2977
    Fin15AnchoredAtom3023 Fin15AnchoredAtom3209 Fin15AnchoredAtom3210 Fin15AnchoredAtom3212
    Fin15AnchoredAtom3228 Fin15AnchoredAtom3230 Fin15AnchoredAtom3234 Fin15AnchoredAtom3256
    Fin15AnchoredAtom3258 Fin15AnchoredAtom3262 Fin15AnchoredAtom3308 Fin15AnchoredAtom3340
    Fin15AnchoredAtom3342 Fin15AnchoredAtom3346 Fin15AnchoredAtom3392 Fin15AnchoredAtom3448
    Fin15AnchoredAtom3704 Fin15AnchoredAtom3705 Fin15AnchoredAtom3707 Fin15AnchoredAtom3723
    Fin15AnchoredAtom3725 Fin15AnchoredAtom3729 Fin15AnchoredAtom3751 Fin15AnchoredAtom3753
    Fin15AnchoredAtom3757 Fin15AnchoredAtom3803 Fin15AnchoredAtom3835 Fin15AnchoredAtom3837
    Fin15AnchoredAtom3841 Fin15AnchoredAtom3887 Fin15AnchoredAtom3943 Fin15AnchoredAtom4375
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

theorem fin15Anchored_clause31776 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2877 chi ∧
      ¬Fin15AnchoredAtom2880 chi ∧
      ¬Fin15AnchoredAtom2881 chi ∧
      ¬Fin15AnchoredAtom2884 chi ∧
      ¬Fin15AnchoredAtom2888 chi ∧
      ¬Fin15AnchoredAtom2889 chi ∧
      ¬Fin15AnchoredAtom2892 chi ∧
      ¬Fin15AnchoredAtom2907 chi ∧
      ¬Fin15AnchoredAtom2910 chi ∧
      ¬Fin15AnchoredAtom2914 chi ∧
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
      ¬Fin15AnchoredAtom4375 chi ∧
      ¬Fin15AnchoredAtom4378 chi ∧
      ¬Fin15AnchoredAtom4382 chi ∧
      ¬Fin15AnchoredAtom4428 chi ∧
      ¬Fin15AnchoredAtom4484 chi ∧
      ¬Fin15AnchoredAtom4610 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 4, 5, 6, 9, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09846
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2877 Fin15AnchoredAtom2880 Fin15AnchoredAtom2881
    Fin15AnchoredAtom2884 Fin15AnchoredAtom2888 Fin15AnchoredAtom2889 Fin15AnchoredAtom2892
    Fin15AnchoredAtom2907 Fin15AnchoredAtom2910 Fin15AnchoredAtom2914 Fin15AnchoredAtom2924
    Fin15AnchoredAtom2925 Fin15AnchoredAtom2928 Fin15AnchoredAtom2943 Fin15AnchoredAtom2946
    Fin15AnchoredAtom2950 Fin15AnchoredAtom2971 Fin15AnchoredAtom2974 Fin15AnchoredAtom2978
    Fin15AnchoredAtom3024 Fin15AnchoredAtom3209 Fin15AnchoredAtom3210 Fin15AnchoredAtom3213
    Fin15AnchoredAtom3228 Fin15AnchoredAtom3231 Fin15AnchoredAtom3235 Fin15AnchoredAtom3256
    Fin15AnchoredAtom3259 Fin15AnchoredAtom3263 Fin15AnchoredAtom3309 Fin15AnchoredAtom3340
    Fin15AnchoredAtom3343 Fin15AnchoredAtom3347 Fin15AnchoredAtom3393 Fin15AnchoredAtom3449
    Fin15AnchoredAtom3704 Fin15AnchoredAtom3705 Fin15AnchoredAtom3708 Fin15AnchoredAtom3723
    Fin15AnchoredAtom3726 Fin15AnchoredAtom3730 Fin15AnchoredAtom3751 Fin15AnchoredAtom3754
    Fin15AnchoredAtom3758 Fin15AnchoredAtom3804 Fin15AnchoredAtom3835 Fin15AnchoredAtom3838
    Fin15AnchoredAtom3842 Fin15AnchoredAtom3888 Fin15AnchoredAtom3944 Fin15AnchoredAtom4375
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

theorem fin15Anchored_clause31777 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2877 chi ∧
      ¬Fin15AnchoredAtom2880 chi ∧
      ¬Fin15AnchoredAtom2881 chi ∧
      ¬Fin15AnchoredAtom2885 chi ∧
      ¬Fin15AnchoredAtom2888 chi ∧
      ¬Fin15AnchoredAtom2889 chi ∧
      ¬Fin15AnchoredAtom2893 chi ∧
      ¬Fin15AnchoredAtom2907 chi ∧
      ¬Fin15AnchoredAtom2911 chi ∧
      ¬Fin15AnchoredAtom2915 chi ∧
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
      ¬Fin15AnchoredAtom4375 chi ∧
      ¬Fin15AnchoredAtom4379 chi ∧
      ¬Fin15AnchoredAtom4383 chi ∧
      ¬Fin15AnchoredAtom4429 chi ∧
      ¬Fin15AnchoredAtom4485 chi ∧
      ¬Fin15AnchoredAtom4611 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 4, 5, 6, 9, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask18038
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2877 Fin15AnchoredAtom2880 Fin15AnchoredAtom2881
    Fin15AnchoredAtom2885 Fin15AnchoredAtom2888 Fin15AnchoredAtom2889 Fin15AnchoredAtom2893
    Fin15AnchoredAtom2907 Fin15AnchoredAtom2911 Fin15AnchoredAtom2915 Fin15AnchoredAtom2924
    Fin15AnchoredAtom2925 Fin15AnchoredAtom2929 Fin15AnchoredAtom2943 Fin15AnchoredAtom2947
    Fin15AnchoredAtom2951 Fin15AnchoredAtom2971 Fin15AnchoredAtom2975 Fin15AnchoredAtom2979
    Fin15AnchoredAtom3025 Fin15AnchoredAtom3209 Fin15AnchoredAtom3210 Fin15AnchoredAtom3214
    Fin15AnchoredAtom3228 Fin15AnchoredAtom3232 Fin15AnchoredAtom3236 Fin15AnchoredAtom3256
    Fin15AnchoredAtom3260 Fin15AnchoredAtom3264 Fin15AnchoredAtom3310 Fin15AnchoredAtom3340
    Fin15AnchoredAtom3344 Fin15AnchoredAtom3348 Fin15AnchoredAtom3394 Fin15AnchoredAtom3450
    Fin15AnchoredAtom3704 Fin15AnchoredAtom3705 Fin15AnchoredAtom3709 Fin15AnchoredAtom3723
    Fin15AnchoredAtom3727 Fin15AnchoredAtom3731 Fin15AnchoredAtom3751 Fin15AnchoredAtom3755
    Fin15AnchoredAtom3759 Fin15AnchoredAtom3805 Fin15AnchoredAtom3835 Fin15AnchoredAtom3839
    Fin15AnchoredAtom3843 Fin15AnchoredAtom3889 Fin15AnchoredAtom3945 Fin15AnchoredAtom4375
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

theorem fin15Anchored_clause31778 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2877 chi ∧
      ¬Fin15AnchoredAtom2880 chi ∧
      ¬Fin15AnchoredAtom2883 chi ∧
      ¬Fin15AnchoredAtom2884 chi ∧
      ¬Fin15AnchoredAtom2888 chi ∧
      ¬Fin15AnchoredAtom2891 chi ∧
      ¬Fin15AnchoredAtom2892 chi ∧
      ¬Fin15AnchoredAtom2909 chi ∧
      ¬Fin15AnchoredAtom2910 chi ∧
      ¬Fin15AnchoredAtom2919 chi ∧
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
      ¬Fin15AnchoredAtom4377 chi ∧
      ¬Fin15AnchoredAtom4378 chi ∧
      ¬Fin15AnchoredAtom4387 chi ∧
      ¬Fin15AnchoredAtom4433 chi ∧
      ¬Fin15AnchoredAtom4489 chi ∧
      ¬Fin15AnchoredAtom4615 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 4, 5, 6, 9, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask12918
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2877 Fin15AnchoredAtom2880 Fin15AnchoredAtom2883
    Fin15AnchoredAtom2884 Fin15AnchoredAtom2888 Fin15AnchoredAtom2891 Fin15AnchoredAtom2892
    Fin15AnchoredAtom2909 Fin15AnchoredAtom2910 Fin15AnchoredAtom2919 Fin15AnchoredAtom2924
    Fin15AnchoredAtom2927 Fin15AnchoredAtom2928 Fin15AnchoredAtom2945 Fin15AnchoredAtom2946
    Fin15AnchoredAtom2955 Fin15AnchoredAtom2973 Fin15AnchoredAtom2974 Fin15AnchoredAtom2983
    Fin15AnchoredAtom3029 Fin15AnchoredAtom3209 Fin15AnchoredAtom3212 Fin15AnchoredAtom3213
    Fin15AnchoredAtom3230 Fin15AnchoredAtom3231 Fin15AnchoredAtom3240 Fin15AnchoredAtom3258
    Fin15AnchoredAtom3259 Fin15AnchoredAtom3268 Fin15AnchoredAtom3314 Fin15AnchoredAtom3342
    Fin15AnchoredAtom3343 Fin15AnchoredAtom3352 Fin15AnchoredAtom3398 Fin15AnchoredAtom3454
    Fin15AnchoredAtom3704 Fin15AnchoredAtom3707 Fin15AnchoredAtom3708 Fin15AnchoredAtom3725
    Fin15AnchoredAtom3726 Fin15AnchoredAtom3735 Fin15AnchoredAtom3753 Fin15AnchoredAtom3754
    Fin15AnchoredAtom3763 Fin15AnchoredAtom3809 Fin15AnchoredAtom3837 Fin15AnchoredAtom3838
    Fin15AnchoredAtom3847 Fin15AnchoredAtom3893 Fin15AnchoredAtom3949 Fin15AnchoredAtom4377
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

theorem fin15Anchored_clause31779 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2877 chi ∧
      ¬Fin15AnchoredAtom2880 chi ∧
      ¬Fin15AnchoredAtom2883 chi ∧
      ¬Fin15AnchoredAtom2885 chi ∧
      ¬Fin15AnchoredAtom2888 chi ∧
      ¬Fin15AnchoredAtom2891 chi ∧
      ¬Fin15AnchoredAtom2893 chi ∧
      ¬Fin15AnchoredAtom2909 chi ∧
      ¬Fin15AnchoredAtom2911 chi ∧
      ¬Fin15AnchoredAtom2920 chi ∧
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
      ¬Fin15AnchoredAtom4377 chi ∧
      ¬Fin15AnchoredAtom4379 chi ∧
      ¬Fin15AnchoredAtom4388 chi ∧
      ¬Fin15AnchoredAtom4434 chi ∧
      ¬Fin15AnchoredAtom4490 chi ∧
      ¬Fin15AnchoredAtom4616 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 4, 5, 6, 9, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21110
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2877 Fin15AnchoredAtom2880 Fin15AnchoredAtom2883
    Fin15AnchoredAtom2885 Fin15AnchoredAtom2888 Fin15AnchoredAtom2891 Fin15AnchoredAtom2893
    Fin15AnchoredAtom2909 Fin15AnchoredAtom2911 Fin15AnchoredAtom2920 Fin15AnchoredAtom2924
    Fin15AnchoredAtom2927 Fin15AnchoredAtom2929 Fin15AnchoredAtom2945 Fin15AnchoredAtom2947
    Fin15AnchoredAtom2956 Fin15AnchoredAtom2973 Fin15AnchoredAtom2975 Fin15AnchoredAtom2984
    Fin15AnchoredAtom3030 Fin15AnchoredAtom3209 Fin15AnchoredAtom3212 Fin15AnchoredAtom3214
    Fin15AnchoredAtom3230 Fin15AnchoredAtom3232 Fin15AnchoredAtom3241 Fin15AnchoredAtom3258
    Fin15AnchoredAtom3260 Fin15AnchoredAtom3269 Fin15AnchoredAtom3315 Fin15AnchoredAtom3342
    Fin15AnchoredAtom3344 Fin15AnchoredAtom3353 Fin15AnchoredAtom3399 Fin15AnchoredAtom3455
    Fin15AnchoredAtom3704 Fin15AnchoredAtom3707 Fin15AnchoredAtom3709 Fin15AnchoredAtom3725
    Fin15AnchoredAtom3727 Fin15AnchoredAtom3736 Fin15AnchoredAtom3753 Fin15AnchoredAtom3755
    Fin15AnchoredAtom3764 Fin15AnchoredAtom3810 Fin15AnchoredAtom3837 Fin15AnchoredAtom3839
    Fin15AnchoredAtom3848 Fin15AnchoredAtom3894 Fin15AnchoredAtom3950 Fin15AnchoredAtom4377
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

theorem fin15Anchored_clause31780 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2877 chi ∧
      ¬Fin15AnchoredAtom2880 chi ∧
      ¬Fin15AnchoredAtom2884 chi ∧
      ¬Fin15AnchoredAtom2885 chi ∧
      ¬Fin15AnchoredAtom2888 chi ∧
      ¬Fin15AnchoredAtom2892 chi ∧
      ¬Fin15AnchoredAtom2893 chi ∧
      ¬Fin15AnchoredAtom2910 chi ∧
      ¬Fin15AnchoredAtom2911 chi ∧
      ¬Fin15AnchoredAtom2921 chi ∧
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
      ¬Fin15AnchoredAtom4378 chi ∧
      ¬Fin15AnchoredAtom4379 chi ∧
      ¬Fin15AnchoredAtom4389 chi ∧
      ¬Fin15AnchoredAtom4435 chi ∧
      ¬Fin15AnchoredAtom4491 chi ∧
      ¬Fin15AnchoredAtom4617 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 4, 5, 6, 9, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25206
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2877 Fin15AnchoredAtom2880 Fin15AnchoredAtom2884
    Fin15AnchoredAtom2885 Fin15AnchoredAtom2888 Fin15AnchoredAtom2892 Fin15AnchoredAtom2893
    Fin15AnchoredAtom2910 Fin15AnchoredAtom2911 Fin15AnchoredAtom2921 Fin15AnchoredAtom2924
    Fin15AnchoredAtom2928 Fin15AnchoredAtom2929 Fin15AnchoredAtom2946 Fin15AnchoredAtom2947
    Fin15AnchoredAtom2957 Fin15AnchoredAtom2974 Fin15AnchoredAtom2975 Fin15AnchoredAtom2985
    Fin15AnchoredAtom3031 Fin15AnchoredAtom3209 Fin15AnchoredAtom3213 Fin15AnchoredAtom3214
    Fin15AnchoredAtom3231 Fin15AnchoredAtom3232 Fin15AnchoredAtom3242 Fin15AnchoredAtom3259
    Fin15AnchoredAtom3260 Fin15AnchoredAtom3270 Fin15AnchoredAtom3316 Fin15AnchoredAtom3343
    Fin15AnchoredAtom3344 Fin15AnchoredAtom3354 Fin15AnchoredAtom3400 Fin15AnchoredAtom3456
    Fin15AnchoredAtom3704 Fin15AnchoredAtom3708 Fin15AnchoredAtom3709 Fin15AnchoredAtom3726
    Fin15AnchoredAtom3727 Fin15AnchoredAtom3737 Fin15AnchoredAtom3754 Fin15AnchoredAtom3755
    Fin15AnchoredAtom3765 Fin15AnchoredAtom3811 Fin15AnchoredAtom3838 Fin15AnchoredAtom3839
    Fin15AnchoredAtom3849 Fin15AnchoredAtom3895 Fin15AnchoredAtom3951 Fin15AnchoredAtom4378
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

theorem fin15Anchored_clause31781 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2877 chi ∧
      ¬Fin15AnchoredAtom2881 chi ∧
      ¬Fin15AnchoredAtom2883 chi ∧
      ¬Fin15AnchoredAtom2884 chi ∧
      ¬Fin15AnchoredAtom2889 chi ∧
      ¬Fin15AnchoredAtom2891 chi ∧
      ¬Fin15AnchoredAtom2892 chi ∧
      ¬Fin15AnchoredAtom2913 chi ∧
      ¬Fin15AnchoredAtom2914 chi ∧
      ¬Fin15AnchoredAtom2919 chi ∧
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
      ¬Fin15AnchoredAtom4381 chi ∧
      ¬Fin15AnchoredAtom4382 chi ∧
      ¬Fin15AnchoredAtom4387 chi ∧
      ¬Fin15AnchoredAtom4439 chi ∧
      ¬Fin15AnchoredAtom4495 chi ∧
      ¬Fin15AnchoredAtom4621 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 4, 5, 6, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13430
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2877 Fin15AnchoredAtom2881 Fin15AnchoredAtom2883
    Fin15AnchoredAtom2884 Fin15AnchoredAtom2889 Fin15AnchoredAtom2891 Fin15AnchoredAtom2892
    Fin15AnchoredAtom2913 Fin15AnchoredAtom2914 Fin15AnchoredAtom2919 Fin15AnchoredAtom2925
    Fin15AnchoredAtom2927 Fin15AnchoredAtom2928 Fin15AnchoredAtom2949 Fin15AnchoredAtom2950
    Fin15AnchoredAtom2955 Fin15AnchoredAtom2977 Fin15AnchoredAtom2978 Fin15AnchoredAtom2983
    Fin15AnchoredAtom3035 Fin15AnchoredAtom3210 Fin15AnchoredAtom3212 Fin15AnchoredAtom3213
    Fin15AnchoredAtom3234 Fin15AnchoredAtom3235 Fin15AnchoredAtom3240 Fin15AnchoredAtom3262
    Fin15AnchoredAtom3263 Fin15AnchoredAtom3268 Fin15AnchoredAtom3320 Fin15AnchoredAtom3346
    Fin15AnchoredAtom3347 Fin15AnchoredAtom3352 Fin15AnchoredAtom3404 Fin15AnchoredAtom3460
    Fin15AnchoredAtom3705 Fin15AnchoredAtom3707 Fin15AnchoredAtom3708 Fin15AnchoredAtom3729
    Fin15AnchoredAtom3730 Fin15AnchoredAtom3735 Fin15AnchoredAtom3757 Fin15AnchoredAtom3758
    Fin15AnchoredAtom3763 Fin15AnchoredAtom3815 Fin15AnchoredAtom3841 Fin15AnchoredAtom3842
    Fin15AnchoredAtom3847 Fin15AnchoredAtom3899 Fin15AnchoredAtom3955 Fin15AnchoredAtom4381
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

theorem fin15Anchored_clause31782 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2877 chi ∧
      ¬Fin15AnchoredAtom2881 chi ∧
      ¬Fin15AnchoredAtom2883 chi ∧
      ¬Fin15AnchoredAtom2885 chi ∧
      ¬Fin15AnchoredAtom2889 chi ∧
      ¬Fin15AnchoredAtom2891 chi ∧
      ¬Fin15AnchoredAtom2893 chi ∧
      ¬Fin15AnchoredAtom2913 chi ∧
      ¬Fin15AnchoredAtom2915 chi ∧
      ¬Fin15AnchoredAtom2920 chi ∧
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
      ¬Fin15AnchoredAtom4381 chi ∧
      ¬Fin15AnchoredAtom4383 chi ∧
      ¬Fin15AnchoredAtom4388 chi ∧
      ¬Fin15AnchoredAtom4440 chi ∧
      ¬Fin15AnchoredAtom4496 chi ∧
      ¬Fin15AnchoredAtom4622 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 4, 5, 6, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21622
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2877 Fin15AnchoredAtom2881 Fin15AnchoredAtom2883
    Fin15AnchoredAtom2885 Fin15AnchoredAtom2889 Fin15AnchoredAtom2891 Fin15AnchoredAtom2893
    Fin15AnchoredAtom2913 Fin15AnchoredAtom2915 Fin15AnchoredAtom2920 Fin15AnchoredAtom2925
    Fin15AnchoredAtom2927 Fin15AnchoredAtom2929 Fin15AnchoredAtom2949 Fin15AnchoredAtom2951
    Fin15AnchoredAtom2956 Fin15AnchoredAtom2977 Fin15AnchoredAtom2979 Fin15AnchoredAtom2984
    Fin15AnchoredAtom3036 Fin15AnchoredAtom3210 Fin15AnchoredAtom3212 Fin15AnchoredAtom3214
    Fin15AnchoredAtom3234 Fin15AnchoredAtom3236 Fin15AnchoredAtom3241 Fin15AnchoredAtom3262
    Fin15AnchoredAtom3264 Fin15AnchoredAtom3269 Fin15AnchoredAtom3321 Fin15AnchoredAtom3346
    Fin15AnchoredAtom3348 Fin15AnchoredAtom3353 Fin15AnchoredAtom3405 Fin15AnchoredAtom3461
    Fin15AnchoredAtom3705 Fin15AnchoredAtom3707 Fin15AnchoredAtom3709 Fin15AnchoredAtom3729
    Fin15AnchoredAtom3731 Fin15AnchoredAtom3736 Fin15AnchoredAtom3757 Fin15AnchoredAtom3759
    Fin15AnchoredAtom3764 Fin15AnchoredAtom3816 Fin15AnchoredAtom3841 Fin15AnchoredAtom3843
    Fin15AnchoredAtom3848 Fin15AnchoredAtom3900 Fin15AnchoredAtom3956 Fin15AnchoredAtom4381
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

theorem fin15Anchored_clause31783 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2877 chi ∧
      ¬Fin15AnchoredAtom2881 chi ∧
      ¬Fin15AnchoredAtom2884 chi ∧
      ¬Fin15AnchoredAtom2885 chi ∧
      ¬Fin15AnchoredAtom2889 chi ∧
      ¬Fin15AnchoredAtom2892 chi ∧
      ¬Fin15AnchoredAtom2893 chi ∧
      ¬Fin15AnchoredAtom2914 chi ∧
      ¬Fin15AnchoredAtom2915 chi ∧
      ¬Fin15AnchoredAtom2921 chi ∧
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
      ¬Fin15AnchoredAtom4382 chi ∧
      ¬Fin15AnchoredAtom4383 chi ∧
      ¬Fin15AnchoredAtom4389 chi ∧
      ¬Fin15AnchoredAtom4441 chi ∧
      ¬Fin15AnchoredAtom4497 chi ∧
      ¬Fin15AnchoredAtom4623 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 4, 5, 6, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25718
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2877 Fin15AnchoredAtom2881 Fin15AnchoredAtom2884
    Fin15AnchoredAtom2885 Fin15AnchoredAtom2889 Fin15AnchoredAtom2892 Fin15AnchoredAtom2893
    Fin15AnchoredAtom2914 Fin15AnchoredAtom2915 Fin15AnchoredAtom2921 Fin15AnchoredAtom2925
    Fin15AnchoredAtom2928 Fin15AnchoredAtom2929 Fin15AnchoredAtom2950 Fin15AnchoredAtom2951
    Fin15AnchoredAtom2957 Fin15AnchoredAtom2978 Fin15AnchoredAtom2979 Fin15AnchoredAtom2985
    Fin15AnchoredAtom3037 Fin15AnchoredAtom3210 Fin15AnchoredAtom3213 Fin15AnchoredAtom3214
    Fin15AnchoredAtom3235 Fin15AnchoredAtom3236 Fin15AnchoredAtom3242 Fin15AnchoredAtom3263
    Fin15AnchoredAtom3264 Fin15AnchoredAtom3270 Fin15AnchoredAtom3322 Fin15AnchoredAtom3347
    Fin15AnchoredAtom3348 Fin15AnchoredAtom3354 Fin15AnchoredAtom3406 Fin15AnchoredAtom3462
    Fin15AnchoredAtom3705 Fin15AnchoredAtom3708 Fin15AnchoredAtom3709 Fin15AnchoredAtom3730
    Fin15AnchoredAtom3731 Fin15AnchoredAtom3737 Fin15AnchoredAtom3758 Fin15AnchoredAtom3759
    Fin15AnchoredAtom3765 Fin15AnchoredAtom3817 Fin15AnchoredAtom3842 Fin15AnchoredAtom3843
    Fin15AnchoredAtom3849 Fin15AnchoredAtom3901 Fin15AnchoredAtom3957 Fin15AnchoredAtom4382
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

theorem fin15Anchored_clause31784 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2877 chi ∧
      ¬Fin15AnchoredAtom2883 chi ∧
      ¬Fin15AnchoredAtom2884 chi ∧
      ¬Fin15AnchoredAtom2885 chi ∧
      ¬Fin15AnchoredAtom2891 chi ∧
      ¬Fin15AnchoredAtom2892 chi ∧
      ¬Fin15AnchoredAtom2893 chi ∧
      ¬Fin15AnchoredAtom2919 chi ∧
      ¬Fin15AnchoredAtom2920 chi ∧
      ¬Fin15AnchoredAtom2921 chi ∧
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
      ¬Fin15AnchoredAtom4387 chi ∧
      ¬Fin15AnchoredAtom4388 chi ∧
      ¬Fin15AnchoredAtom4389 chi ∧
      ¬Fin15AnchoredAtom4445 chi ∧
      ¬Fin15AnchoredAtom4501 chi ∧
      ¬Fin15AnchoredAtom4627 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 4, 5, 6, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask28790
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2877 Fin15AnchoredAtom2883 Fin15AnchoredAtom2884
    Fin15AnchoredAtom2885 Fin15AnchoredAtom2891 Fin15AnchoredAtom2892 Fin15AnchoredAtom2893
    Fin15AnchoredAtom2919 Fin15AnchoredAtom2920 Fin15AnchoredAtom2921 Fin15AnchoredAtom2927
    Fin15AnchoredAtom2928 Fin15AnchoredAtom2929 Fin15AnchoredAtom2955 Fin15AnchoredAtom2956
    Fin15AnchoredAtom2957 Fin15AnchoredAtom2983 Fin15AnchoredAtom2984 Fin15AnchoredAtom2985
    Fin15AnchoredAtom3041 Fin15AnchoredAtom3212 Fin15AnchoredAtom3213 Fin15AnchoredAtom3214
    Fin15AnchoredAtom3240 Fin15AnchoredAtom3241 Fin15AnchoredAtom3242 Fin15AnchoredAtom3268
    Fin15AnchoredAtom3269 Fin15AnchoredAtom3270 Fin15AnchoredAtom3326 Fin15AnchoredAtom3352
    Fin15AnchoredAtom3353 Fin15AnchoredAtom3354 Fin15AnchoredAtom3410 Fin15AnchoredAtom3466
    Fin15AnchoredAtom3707 Fin15AnchoredAtom3708 Fin15AnchoredAtom3709 Fin15AnchoredAtom3735
    Fin15AnchoredAtom3736 Fin15AnchoredAtom3737 Fin15AnchoredAtom3763 Fin15AnchoredAtom3764
    Fin15AnchoredAtom3765 Fin15AnchoredAtom3821 Fin15AnchoredAtom3847 Fin15AnchoredAtom3848
    Fin15AnchoredAtom3849 Fin15AnchoredAtom3905 Fin15AnchoredAtom3961 Fin15AnchoredAtom4387
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

theorem fin15Anchored_clause31785 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2878 chi ∧
      ¬Fin15AnchoredAtom2880 chi ∧
      ¬Fin15AnchoredAtom2881 chi ∧
      ¬Fin15AnchoredAtom2883 chi ∧
      ¬Fin15AnchoredAtom2895 chi ∧
      ¬Fin15AnchoredAtom2896 chi ∧
      ¬Fin15AnchoredAtom2898 chi ∧
      ¬Fin15AnchoredAtom2907 chi ∧
      ¬Fin15AnchoredAtom2909 chi ∧
      ¬Fin15AnchoredAtom2913 chi ∧
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
      ¬Fin15AnchoredAtom4396 chi ∧
      ¬Fin15AnchoredAtom4398 chi ∧
      ¬Fin15AnchoredAtom4402 chi ∧
      ¬Fin15AnchoredAtom4427 chi ∧
      ¬Fin15AnchoredAtom4518 chi ∧
      ¬Fin15AnchoredAtom4644 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 4, 5, 7, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05814
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2878 Fin15AnchoredAtom2880 Fin15AnchoredAtom2881
    Fin15AnchoredAtom2883 Fin15AnchoredAtom2895 Fin15AnchoredAtom2896 Fin15AnchoredAtom2898
    Fin15AnchoredAtom2907 Fin15AnchoredAtom2909 Fin15AnchoredAtom2913 Fin15AnchoredAtom2931
    Fin15AnchoredAtom2932 Fin15AnchoredAtom2934 Fin15AnchoredAtom2943 Fin15AnchoredAtom2945
    Fin15AnchoredAtom2949 Fin15AnchoredAtom2992 Fin15AnchoredAtom2994 Fin15AnchoredAtom2998
    Fin15AnchoredAtom3023 Fin15AnchoredAtom3216 Fin15AnchoredAtom3217 Fin15AnchoredAtom3219
    Fin15AnchoredAtom3228 Fin15AnchoredAtom3230 Fin15AnchoredAtom3234 Fin15AnchoredAtom3277
    Fin15AnchoredAtom3279 Fin15AnchoredAtom3283 Fin15AnchoredAtom3308 Fin15AnchoredAtom3361
    Fin15AnchoredAtom3363 Fin15AnchoredAtom3367 Fin15AnchoredAtom3392 Fin15AnchoredAtom3483
    Fin15AnchoredAtom3711 Fin15AnchoredAtom3712 Fin15AnchoredAtom3714 Fin15AnchoredAtom3723
    Fin15AnchoredAtom3725 Fin15AnchoredAtom3729 Fin15AnchoredAtom3772 Fin15AnchoredAtom3774
    Fin15AnchoredAtom3778 Fin15AnchoredAtom3803 Fin15AnchoredAtom3856 Fin15AnchoredAtom3858
    Fin15AnchoredAtom3862 Fin15AnchoredAtom3887 Fin15AnchoredAtom3978 Fin15AnchoredAtom4396
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

theorem fin15Anchored_clause31786 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2878 chi ∧
      ¬Fin15AnchoredAtom2880 chi ∧
      ¬Fin15AnchoredAtom2881 chi ∧
      ¬Fin15AnchoredAtom2884 chi ∧
      ¬Fin15AnchoredAtom2895 chi ∧
      ¬Fin15AnchoredAtom2896 chi ∧
      ¬Fin15AnchoredAtom2899 chi ∧
      ¬Fin15AnchoredAtom2907 chi ∧
      ¬Fin15AnchoredAtom2910 chi ∧
      ¬Fin15AnchoredAtom2914 chi ∧
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
      ¬Fin15AnchoredAtom4396 chi ∧
      ¬Fin15AnchoredAtom4399 chi ∧
      ¬Fin15AnchoredAtom4403 chi ∧
      ¬Fin15AnchoredAtom4428 chi ∧
      ¬Fin15AnchoredAtom4519 chi ∧
      ¬Fin15AnchoredAtom4645 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 4, 5, 7, 9, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09910
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2878 Fin15AnchoredAtom2880 Fin15AnchoredAtom2881
    Fin15AnchoredAtom2884 Fin15AnchoredAtom2895 Fin15AnchoredAtom2896 Fin15AnchoredAtom2899
    Fin15AnchoredAtom2907 Fin15AnchoredAtom2910 Fin15AnchoredAtom2914 Fin15AnchoredAtom2931
    Fin15AnchoredAtom2932 Fin15AnchoredAtom2935 Fin15AnchoredAtom2943 Fin15AnchoredAtom2946
    Fin15AnchoredAtom2950 Fin15AnchoredAtom2992 Fin15AnchoredAtom2995 Fin15AnchoredAtom2999
    Fin15AnchoredAtom3024 Fin15AnchoredAtom3216 Fin15AnchoredAtom3217 Fin15AnchoredAtom3220
    Fin15AnchoredAtom3228 Fin15AnchoredAtom3231 Fin15AnchoredAtom3235 Fin15AnchoredAtom3277
    Fin15AnchoredAtom3280 Fin15AnchoredAtom3284 Fin15AnchoredAtom3309 Fin15AnchoredAtom3361
    Fin15AnchoredAtom3364 Fin15AnchoredAtom3368 Fin15AnchoredAtom3393 Fin15AnchoredAtom3484
    Fin15AnchoredAtom3711 Fin15AnchoredAtom3712 Fin15AnchoredAtom3715 Fin15AnchoredAtom3723
    Fin15AnchoredAtom3726 Fin15AnchoredAtom3730 Fin15AnchoredAtom3772 Fin15AnchoredAtom3775
    Fin15AnchoredAtom3779 Fin15AnchoredAtom3804 Fin15AnchoredAtom3856 Fin15AnchoredAtom3859
    Fin15AnchoredAtom3863 Fin15AnchoredAtom3888 Fin15AnchoredAtom3979 Fin15AnchoredAtom4396
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

theorem fin15Anchored_clause31787 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2878 chi ∧
      ¬Fin15AnchoredAtom2880 chi ∧
      ¬Fin15AnchoredAtom2881 chi ∧
      ¬Fin15AnchoredAtom2885 chi ∧
      ¬Fin15AnchoredAtom2895 chi ∧
      ¬Fin15AnchoredAtom2896 chi ∧
      ¬Fin15AnchoredAtom2900 chi ∧
      ¬Fin15AnchoredAtom2907 chi ∧
      ¬Fin15AnchoredAtom2911 chi ∧
      ¬Fin15AnchoredAtom2915 chi ∧
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
      ¬Fin15AnchoredAtom4396 chi ∧
      ¬Fin15AnchoredAtom4400 chi ∧
      ¬Fin15AnchoredAtom4404 chi ∧
      ¬Fin15AnchoredAtom4429 chi ∧
      ¬Fin15AnchoredAtom4520 chi ∧
      ¬Fin15AnchoredAtom4646 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 4, 5, 7, 9, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask18102
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2878 Fin15AnchoredAtom2880 Fin15AnchoredAtom2881
    Fin15AnchoredAtom2885 Fin15AnchoredAtom2895 Fin15AnchoredAtom2896 Fin15AnchoredAtom2900
    Fin15AnchoredAtom2907 Fin15AnchoredAtom2911 Fin15AnchoredAtom2915 Fin15AnchoredAtom2931
    Fin15AnchoredAtom2932 Fin15AnchoredAtom2936 Fin15AnchoredAtom2943 Fin15AnchoredAtom2947
    Fin15AnchoredAtom2951 Fin15AnchoredAtom2992 Fin15AnchoredAtom2996 Fin15AnchoredAtom3000
    Fin15AnchoredAtom3025 Fin15AnchoredAtom3216 Fin15AnchoredAtom3217 Fin15AnchoredAtom3221
    Fin15AnchoredAtom3228 Fin15AnchoredAtom3232 Fin15AnchoredAtom3236 Fin15AnchoredAtom3277
    Fin15AnchoredAtom3281 Fin15AnchoredAtom3285 Fin15AnchoredAtom3310 Fin15AnchoredAtom3361
    Fin15AnchoredAtom3365 Fin15AnchoredAtom3369 Fin15AnchoredAtom3394 Fin15AnchoredAtom3485
    Fin15AnchoredAtom3711 Fin15AnchoredAtom3712 Fin15AnchoredAtom3716 Fin15AnchoredAtom3723
    Fin15AnchoredAtom3727 Fin15AnchoredAtom3731 Fin15AnchoredAtom3772 Fin15AnchoredAtom3776
    Fin15AnchoredAtom3780 Fin15AnchoredAtom3805 Fin15AnchoredAtom3856 Fin15AnchoredAtom3860
    Fin15AnchoredAtom3864 Fin15AnchoredAtom3889 Fin15AnchoredAtom3980 Fin15AnchoredAtom4396
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

theorem fin15Anchored_clause31788 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2878 chi ∧
      ¬Fin15AnchoredAtom2880 chi ∧
      ¬Fin15AnchoredAtom2883 chi ∧
      ¬Fin15AnchoredAtom2884 chi ∧
      ¬Fin15AnchoredAtom2895 chi ∧
      ¬Fin15AnchoredAtom2898 chi ∧
      ¬Fin15AnchoredAtom2899 chi ∧
      ¬Fin15AnchoredAtom2909 chi ∧
      ¬Fin15AnchoredAtom2910 chi ∧
      ¬Fin15AnchoredAtom2919 chi ∧
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
      ¬Fin15AnchoredAtom4398 chi ∧
      ¬Fin15AnchoredAtom4399 chi ∧
      ¬Fin15AnchoredAtom4408 chi ∧
      ¬Fin15AnchoredAtom4433 chi ∧
      ¬Fin15AnchoredAtom4524 chi ∧
      ¬Fin15AnchoredAtom4650 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 4, 5, 7, 9, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask12982
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2878 Fin15AnchoredAtom2880 Fin15AnchoredAtom2883
    Fin15AnchoredAtom2884 Fin15AnchoredAtom2895 Fin15AnchoredAtom2898 Fin15AnchoredAtom2899
    Fin15AnchoredAtom2909 Fin15AnchoredAtom2910 Fin15AnchoredAtom2919 Fin15AnchoredAtom2931
    Fin15AnchoredAtom2934 Fin15AnchoredAtom2935 Fin15AnchoredAtom2945 Fin15AnchoredAtom2946
    Fin15AnchoredAtom2955 Fin15AnchoredAtom2994 Fin15AnchoredAtom2995 Fin15AnchoredAtom3004
    Fin15AnchoredAtom3029 Fin15AnchoredAtom3216 Fin15AnchoredAtom3219 Fin15AnchoredAtom3220
    Fin15AnchoredAtom3230 Fin15AnchoredAtom3231 Fin15AnchoredAtom3240 Fin15AnchoredAtom3279
    Fin15AnchoredAtom3280 Fin15AnchoredAtom3289 Fin15AnchoredAtom3314 Fin15AnchoredAtom3363
    Fin15AnchoredAtom3364 Fin15AnchoredAtom3373 Fin15AnchoredAtom3398 Fin15AnchoredAtom3489
    Fin15AnchoredAtom3711 Fin15AnchoredAtom3714 Fin15AnchoredAtom3715 Fin15AnchoredAtom3725
    Fin15AnchoredAtom3726 Fin15AnchoredAtom3735 Fin15AnchoredAtom3774 Fin15AnchoredAtom3775
    Fin15AnchoredAtom3784 Fin15AnchoredAtom3809 Fin15AnchoredAtom3858 Fin15AnchoredAtom3859
    Fin15AnchoredAtom3868 Fin15AnchoredAtom3893 Fin15AnchoredAtom3984 Fin15AnchoredAtom4398
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

theorem fin15Anchored_clause31789 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2878 chi ∧
      ¬Fin15AnchoredAtom2880 chi ∧
      ¬Fin15AnchoredAtom2883 chi ∧
      ¬Fin15AnchoredAtom2885 chi ∧
      ¬Fin15AnchoredAtom2895 chi ∧
      ¬Fin15AnchoredAtom2898 chi ∧
      ¬Fin15AnchoredAtom2900 chi ∧
      ¬Fin15AnchoredAtom2909 chi ∧
      ¬Fin15AnchoredAtom2911 chi ∧
      ¬Fin15AnchoredAtom2920 chi ∧
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
      ¬Fin15AnchoredAtom4398 chi ∧
      ¬Fin15AnchoredAtom4400 chi ∧
      ¬Fin15AnchoredAtom4409 chi ∧
      ¬Fin15AnchoredAtom4434 chi ∧
      ¬Fin15AnchoredAtom4525 chi ∧
      ¬Fin15AnchoredAtom4651 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 4, 5, 7, 9, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21174
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2878 Fin15AnchoredAtom2880 Fin15AnchoredAtom2883
    Fin15AnchoredAtom2885 Fin15AnchoredAtom2895 Fin15AnchoredAtom2898 Fin15AnchoredAtom2900
    Fin15AnchoredAtom2909 Fin15AnchoredAtom2911 Fin15AnchoredAtom2920 Fin15AnchoredAtom2931
    Fin15AnchoredAtom2934 Fin15AnchoredAtom2936 Fin15AnchoredAtom2945 Fin15AnchoredAtom2947
    Fin15AnchoredAtom2956 Fin15AnchoredAtom2994 Fin15AnchoredAtom2996 Fin15AnchoredAtom3005
    Fin15AnchoredAtom3030 Fin15AnchoredAtom3216 Fin15AnchoredAtom3219 Fin15AnchoredAtom3221
    Fin15AnchoredAtom3230 Fin15AnchoredAtom3232 Fin15AnchoredAtom3241 Fin15AnchoredAtom3279
    Fin15AnchoredAtom3281 Fin15AnchoredAtom3290 Fin15AnchoredAtom3315 Fin15AnchoredAtom3363
    Fin15AnchoredAtom3365 Fin15AnchoredAtom3374 Fin15AnchoredAtom3399 Fin15AnchoredAtom3490
    Fin15AnchoredAtom3711 Fin15AnchoredAtom3714 Fin15AnchoredAtom3716 Fin15AnchoredAtom3725
    Fin15AnchoredAtom3727 Fin15AnchoredAtom3736 Fin15AnchoredAtom3774 Fin15AnchoredAtom3776
    Fin15AnchoredAtom3785 Fin15AnchoredAtom3810 Fin15AnchoredAtom3858 Fin15AnchoredAtom3860
    Fin15AnchoredAtom3869 Fin15AnchoredAtom3894 Fin15AnchoredAtom3985 Fin15AnchoredAtom4398
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

theorem fin15Anchored_clause31790 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2878 chi ∧
      ¬Fin15AnchoredAtom2880 chi ∧
      ¬Fin15AnchoredAtom2884 chi ∧
      ¬Fin15AnchoredAtom2885 chi ∧
      ¬Fin15AnchoredAtom2895 chi ∧
      ¬Fin15AnchoredAtom2899 chi ∧
      ¬Fin15AnchoredAtom2900 chi ∧
      ¬Fin15AnchoredAtom2910 chi ∧
      ¬Fin15AnchoredAtom2911 chi ∧
      ¬Fin15AnchoredAtom2921 chi ∧
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
      ¬Fin15AnchoredAtom4399 chi ∧
      ¬Fin15AnchoredAtom4400 chi ∧
      ¬Fin15AnchoredAtom4410 chi ∧
      ¬Fin15AnchoredAtom4435 chi ∧
      ¬Fin15AnchoredAtom4526 chi ∧
      ¬Fin15AnchoredAtom4652 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 4, 5, 7, 9, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25270
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2878 Fin15AnchoredAtom2880 Fin15AnchoredAtom2884
    Fin15AnchoredAtom2885 Fin15AnchoredAtom2895 Fin15AnchoredAtom2899 Fin15AnchoredAtom2900
    Fin15AnchoredAtom2910 Fin15AnchoredAtom2911 Fin15AnchoredAtom2921 Fin15AnchoredAtom2931
    Fin15AnchoredAtom2935 Fin15AnchoredAtom2936 Fin15AnchoredAtom2946 Fin15AnchoredAtom2947
    Fin15AnchoredAtom2957 Fin15AnchoredAtom2995 Fin15AnchoredAtom2996 Fin15AnchoredAtom3006
    Fin15AnchoredAtom3031 Fin15AnchoredAtom3216 Fin15AnchoredAtom3220 Fin15AnchoredAtom3221
    Fin15AnchoredAtom3231 Fin15AnchoredAtom3232 Fin15AnchoredAtom3242 Fin15AnchoredAtom3280
    Fin15AnchoredAtom3281 Fin15AnchoredAtom3291 Fin15AnchoredAtom3316 Fin15AnchoredAtom3364
    Fin15AnchoredAtom3365 Fin15AnchoredAtom3375 Fin15AnchoredAtom3400 Fin15AnchoredAtom3491
    Fin15AnchoredAtom3711 Fin15AnchoredAtom3715 Fin15AnchoredAtom3716 Fin15AnchoredAtom3726
    Fin15AnchoredAtom3727 Fin15AnchoredAtom3737 Fin15AnchoredAtom3775 Fin15AnchoredAtom3776
    Fin15AnchoredAtom3786 Fin15AnchoredAtom3811 Fin15AnchoredAtom3859 Fin15AnchoredAtom3860
    Fin15AnchoredAtom3870 Fin15AnchoredAtom3895 Fin15AnchoredAtom3986 Fin15AnchoredAtom4399
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

theorem fin15Anchored_clause31791 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2878 chi ∧
      ¬Fin15AnchoredAtom2881 chi ∧
      ¬Fin15AnchoredAtom2883 chi ∧
      ¬Fin15AnchoredAtom2884 chi ∧
      ¬Fin15AnchoredAtom2896 chi ∧
      ¬Fin15AnchoredAtom2898 chi ∧
      ¬Fin15AnchoredAtom2899 chi ∧
      ¬Fin15AnchoredAtom2913 chi ∧
      ¬Fin15AnchoredAtom2914 chi ∧
      ¬Fin15AnchoredAtom2919 chi ∧
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
      ¬Fin15AnchoredAtom4402 chi ∧
      ¬Fin15AnchoredAtom4403 chi ∧
      ¬Fin15AnchoredAtom4408 chi ∧
      ¬Fin15AnchoredAtom4439 chi ∧
      ¬Fin15AnchoredAtom4530 chi ∧
      ¬Fin15AnchoredAtom4656 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 4, 5, 7, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13494
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2878 Fin15AnchoredAtom2881 Fin15AnchoredAtom2883
    Fin15AnchoredAtom2884 Fin15AnchoredAtom2896 Fin15AnchoredAtom2898 Fin15AnchoredAtom2899
    Fin15AnchoredAtom2913 Fin15AnchoredAtom2914 Fin15AnchoredAtom2919 Fin15AnchoredAtom2932
    Fin15AnchoredAtom2934 Fin15AnchoredAtom2935 Fin15AnchoredAtom2949 Fin15AnchoredAtom2950
    Fin15AnchoredAtom2955 Fin15AnchoredAtom2998 Fin15AnchoredAtom2999 Fin15AnchoredAtom3004
    Fin15AnchoredAtom3035 Fin15AnchoredAtom3217 Fin15AnchoredAtom3219 Fin15AnchoredAtom3220
    Fin15AnchoredAtom3234 Fin15AnchoredAtom3235 Fin15AnchoredAtom3240 Fin15AnchoredAtom3283
    Fin15AnchoredAtom3284 Fin15AnchoredAtom3289 Fin15AnchoredAtom3320 Fin15AnchoredAtom3367
    Fin15AnchoredAtom3368 Fin15AnchoredAtom3373 Fin15AnchoredAtom3404 Fin15AnchoredAtom3495
    Fin15AnchoredAtom3712 Fin15AnchoredAtom3714 Fin15AnchoredAtom3715 Fin15AnchoredAtom3729
    Fin15AnchoredAtom3730 Fin15AnchoredAtom3735 Fin15AnchoredAtom3778 Fin15AnchoredAtom3779
    Fin15AnchoredAtom3784 Fin15AnchoredAtom3815 Fin15AnchoredAtom3862 Fin15AnchoredAtom3863
    Fin15AnchoredAtom3868 Fin15AnchoredAtom3899 Fin15AnchoredAtom3990 Fin15AnchoredAtom4402
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

theorem fin15Anchored_clause31792 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2878 chi ∧
      ¬Fin15AnchoredAtom2881 chi ∧
      ¬Fin15AnchoredAtom2883 chi ∧
      ¬Fin15AnchoredAtom2885 chi ∧
      ¬Fin15AnchoredAtom2896 chi ∧
      ¬Fin15AnchoredAtom2898 chi ∧
      ¬Fin15AnchoredAtom2900 chi ∧
      ¬Fin15AnchoredAtom2913 chi ∧
      ¬Fin15AnchoredAtom2915 chi ∧
      ¬Fin15AnchoredAtom2920 chi ∧
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
      ¬Fin15AnchoredAtom4402 chi ∧
      ¬Fin15AnchoredAtom4404 chi ∧
      ¬Fin15AnchoredAtom4409 chi ∧
      ¬Fin15AnchoredAtom4440 chi ∧
      ¬Fin15AnchoredAtom4531 chi ∧
      ¬Fin15AnchoredAtom4657 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 4, 5, 7, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21686
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2878 Fin15AnchoredAtom2881 Fin15AnchoredAtom2883
    Fin15AnchoredAtom2885 Fin15AnchoredAtom2896 Fin15AnchoredAtom2898 Fin15AnchoredAtom2900
    Fin15AnchoredAtom2913 Fin15AnchoredAtom2915 Fin15AnchoredAtom2920 Fin15AnchoredAtom2932
    Fin15AnchoredAtom2934 Fin15AnchoredAtom2936 Fin15AnchoredAtom2949 Fin15AnchoredAtom2951
    Fin15AnchoredAtom2956 Fin15AnchoredAtom2998 Fin15AnchoredAtom3000 Fin15AnchoredAtom3005
    Fin15AnchoredAtom3036 Fin15AnchoredAtom3217 Fin15AnchoredAtom3219 Fin15AnchoredAtom3221
    Fin15AnchoredAtom3234 Fin15AnchoredAtom3236 Fin15AnchoredAtom3241 Fin15AnchoredAtom3283
    Fin15AnchoredAtom3285 Fin15AnchoredAtom3290 Fin15AnchoredAtom3321 Fin15AnchoredAtom3367
    Fin15AnchoredAtom3369 Fin15AnchoredAtom3374 Fin15AnchoredAtom3405 Fin15AnchoredAtom3496
    Fin15AnchoredAtom3712 Fin15AnchoredAtom3714 Fin15AnchoredAtom3716 Fin15AnchoredAtom3729
    Fin15AnchoredAtom3731 Fin15AnchoredAtom3736 Fin15AnchoredAtom3778 Fin15AnchoredAtom3780
    Fin15AnchoredAtom3785 Fin15AnchoredAtom3816 Fin15AnchoredAtom3862 Fin15AnchoredAtom3864
    Fin15AnchoredAtom3869 Fin15AnchoredAtom3900 Fin15AnchoredAtom3991 Fin15AnchoredAtom4402
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

theorem fin15Anchored_clause31793 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2878 chi ∧
      ¬Fin15AnchoredAtom2881 chi ∧
      ¬Fin15AnchoredAtom2884 chi ∧
      ¬Fin15AnchoredAtom2885 chi ∧
      ¬Fin15AnchoredAtom2896 chi ∧
      ¬Fin15AnchoredAtom2899 chi ∧
      ¬Fin15AnchoredAtom2900 chi ∧
      ¬Fin15AnchoredAtom2914 chi ∧
      ¬Fin15AnchoredAtom2915 chi ∧
      ¬Fin15AnchoredAtom2921 chi ∧
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
      ¬Fin15AnchoredAtom4403 chi ∧
      ¬Fin15AnchoredAtom4404 chi ∧
      ¬Fin15AnchoredAtom4410 chi ∧
      ¬Fin15AnchoredAtom4441 chi ∧
      ¬Fin15AnchoredAtom4532 chi ∧
      ¬Fin15AnchoredAtom4658 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 4, 5, 7, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25782
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2878 Fin15AnchoredAtom2881 Fin15AnchoredAtom2884
    Fin15AnchoredAtom2885 Fin15AnchoredAtom2896 Fin15AnchoredAtom2899 Fin15AnchoredAtom2900
    Fin15AnchoredAtom2914 Fin15AnchoredAtom2915 Fin15AnchoredAtom2921 Fin15AnchoredAtom2932
    Fin15AnchoredAtom2935 Fin15AnchoredAtom2936 Fin15AnchoredAtom2950 Fin15AnchoredAtom2951
    Fin15AnchoredAtom2957 Fin15AnchoredAtom2999 Fin15AnchoredAtom3000 Fin15AnchoredAtom3006
    Fin15AnchoredAtom3037 Fin15AnchoredAtom3217 Fin15AnchoredAtom3220 Fin15AnchoredAtom3221
    Fin15AnchoredAtom3235 Fin15AnchoredAtom3236 Fin15AnchoredAtom3242 Fin15AnchoredAtom3284
    Fin15AnchoredAtom3285 Fin15AnchoredAtom3291 Fin15AnchoredAtom3322 Fin15AnchoredAtom3368
    Fin15AnchoredAtom3369 Fin15AnchoredAtom3375 Fin15AnchoredAtom3406 Fin15AnchoredAtom3497
    Fin15AnchoredAtom3712 Fin15AnchoredAtom3715 Fin15AnchoredAtom3716 Fin15AnchoredAtom3730
    Fin15AnchoredAtom3731 Fin15AnchoredAtom3737 Fin15AnchoredAtom3779 Fin15AnchoredAtom3780
    Fin15AnchoredAtom3786 Fin15AnchoredAtom3817 Fin15AnchoredAtom3863 Fin15AnchoredAtom3864
    Fin15AnchoredAtom3870 Fin15AnchoredAtom3901 Fin15AnchoredAtom3992 Fin15AnchoredAtom4403
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

theorem fin15Anchored_clause31794 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2878 chi ∧
      ¬Fin15AnchoredAtom2883 chi ∧
      ¬Fin15AnchoredAtom2884 chi ∧
      ¬Fin15AnchoredAtom2885 chi ∧
      ¬Fin15AnchoredAtom2898 chi ∧
      ¬Fin15AnchoredAtom2899 chi ∧
      ¬Fin15AnchoredAtom2900 chi ∧
      ¬Fin15AnchoredAtom2919 chi ∧
      ¬Fin15AnchoredAtom2920 chi ∧
      ¬Fin15AnchoredAtom2921 chi ∧
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
      ¬Fin15AnchoredAtom4408 chi ∧
      ¬Fin15AnchoredAtom4409 chi ∧
      ¬Fin15AnchoredAtom4410 chi ∧
      ¬Fin15AnchoredAtom4445 chi ∧
      ¬Fin15AnchoredAtom4536 chi ∧
      ¬Fin15AnchoredAtom4662 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 4, 5, 7, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask28854
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2878 Fin15AnchoredAtom2883 Fin15AnchoredAtom2884
    Fin15AnchoredAtom2885 Fin15AnchoredAtom2898 Fin15AnchoredAtom2899 Fin15AnchoredAtom2900
    Fin15AnchoredAtom2919 Fin15AnchoredAtom2920 Fin15AnchoredAtom2921 Fin15AnchoredAtom2934
    Fin15AnchoredAtom2935 Fin15AnchoredAtom2936 Fin15AnchoredAtom2955 Fin15AnchoredAtom2956
    Fin15AnchoredAtom2957 Fin15AnchoredAtom3004 Fin15AnchoredAtom3005 Fin15AnchoredAtom3006
    Fin15AnchoredAtom3041 Fin15AnchoredAtom3219 Fin15AnchoredAtom3220 Fin15AnchoredAtom3221
    Fin15AnchoredAtom3240 Fin15AnchoredAtom3241 Fin15AnchoredAtom3242 Fin15AnchoredAtom3289
    Fin15AnchoredAtom3290 Fin15AnchoredAtom3291 Fin15AnchoredAtom3326 Fin15AnchoredAtom3373
    Fin15AnchoredAtom3374 Fin15AnchoredAtom3375 Fin15AnchoredAtom3410 Fin15AnchoredAtom3501
    Fin15AnchoredAtom3714 Fin15AnchoredAtom3715 Fin15AnchoredAtom3716 Fin15AnchoredAtom3735
    Fin15AnchoredAtom3736 Fin15AnchoredAtom3737 Fin15AnchoredAtom3784 Fin15AnchoredAtom3785
    Fin15AnchoredAtom3786 Fin15AnchoredAtom3821 Fin15AnchoredAtom3868 Fin15AnchoredAtom3869
    Fin15AnchoredAtom3870 Fin15AnchoredAtom3905 Fin15AnchoredAtom3996 Fin15AnchoredAtom4408
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

theorem fin15Anchored_clause31795 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2880 chi ∧
      ¬Fin15AnchoredAtom2881 chi ∧
      ¬Fin15AnchoredAtom2883 chi ∧
      ¬Fin15AnchoredAtom2884 chi ∧
      ¬Fin15AnchoredAtom2907 chi ∧
      ¬Fin15AnchoredAtom2909 chi ∧
      ¬Fin15AnchoredAtom2910 chi ∧
      ¬Fin15AnchoredAtom2913 chi ∧
      ¬Fin15AnchoredAtom2914 chi ∧
      ¬Fin15AnchoredAtom2919 chi ∧
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
      ¬Fin15AnchoredAtom4427 chi ∧
      ¬Fin15AnchoredAtom4428 chi ∧
      ¬Fin15AnchoredAtom4433 chi ∧
      ¬Fin15AnchoredAtom4439 chi ∧
      ¬Fin15AnchoredAtom4560 chi ∧
      ¬Fin15AnchoredAtom4686 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 4, 5, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13878
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2880 Fin15AnchoredAtom2881 Fin15AnchoredAtom2883
    Fin15AnchoredAtom2884 Fin15AnchoredAtom2907 Fin15AnchoredAtom2909 Fin15AnchoredAtom2910
    Fin15AnchoredAtom2913 Fin15AnchoredAtom2914 Fin15AnchoredAtom2919 Fin15AnchoredAtom2943
    Fin15AnchoredAtom2945 Fin15AnchoredAtom2946 Fin15AnchoredAtom2949 Fin15AnchoredAtom2950
    Fin15AnchoredAtom2955 Fin15AnchoredAtom3023 Fin15AnchoredAtom3024 Fin15AnchoredAtom3029
    Fin15AnchoredAtom3035 Fin15AnchoredAtom3228 Fin15AnchoredAtom3230 Fin15AnchoredAtom3231
    Fin15AnchoredAtom3234 Fin15AnchoredAtom3235 Fin15AnchoredAtom3240 Fin15AnchoredAtom3308
    Fin15AnchoredAtom3309 Fin15AnchoredAtom3314 Fin15AnchoredAtom3320 Fin15AnchoredAtom3392
    Fin15AnchoredAtom3393 Fin15AnchoredAtom3398 Fin15AnchoredAtom3404 Fin15AnchoredAtom3525
    Fin15AnchoredAtom3723 Fin15AnchoredAtom3725 Fin15AnchoredAtom3726 Fin15AnchoredAtom3729
    Fin15AnchoredAtom3730 Fin15AnchoredAtom3735 Fin15AnchoredAtom3803 Fin15AnchoredAtom3804
    Fin15AnchoredAtom3809 Fin15AnchoredAtom3815 Fin15AnchoredAtom3887 Fin15AnchoredAtom3888
    Fin15AnchoredAtom3893 Fin15AnchoredAtom3899 Fin15AnchoredAtom4020 Fin15AnchoredAtom4427
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

theorem fin15Anchored_clause31796 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2880 chi ∧
      ¬Fin15AnchoredAtom2881 chi ∧
      ¬Fin15AnchoredAtom2883 chi ∧
      ¬Fin15AnchoredAtom2885 chi ∧
      ¬Fin15AnchoredAtom2907 chi ∧
      ¬Fin15AnchoredAtom2909 chi ∧
      ¬Fin15AnchoredAtom2911 chi ∧
      ¬Fin15AnchoredAtom2913 chi ∧
      ¬Fin15AnchoredAtom2915 chi ∧
      ¬Fin15AnchoredAtom2920 chi ∧
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
      ¬Fin15AnchoredAtom4427 chi ∧
      ¬Fin15AnchoredAtom4429 chi ∧
      ¬Fin15AnchoredAtom4434 chi ∧
      ¬Fin15AnchoredAtom4440 chi ∧
      ¬Fin15AnchoredAtom4561 chi ∧
      ¬Fin15AnchoredAtom4687 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 4, 5, 9, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22070
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2880 Fin15AnchoredAtom2881 Fin15AnchoredAtom2883
    Fin15AnchoredAtom2885 Fin15AnchoredAtom2907 Fin15AnchoredAtom2909 Fin15AnchoredAtom2911
    Fin15AnchoredAtom2913 Fin15AnchoredAtom2915 Fin15AnchoredAtom2920 Fin15AnchoredAtom2943
    Fin15AnchoredAtom2945 Fin15AnchoredAtom2947 Fin15AnchoredAtom2949 Fin15AnchoredAtom2951
    Fin15AnchoredAtom2956 Fin15AnchoredAtom3023 Fin15AnchoredAtom3025 Fin15AnchoredAtom3030
    Fin15AnchoredAtom3036 Fin15AnchoredAtom3228 Fin15AnchoredAtom3230 Fin15AnchoredAtom3232
    Fin15AnchoredAtom3234 Fin15AnchoredAtom3236 Fin15AnchoredAtom3241 Fin15AnchoredAtom3308
    Fin15AnchoredAtom3310 Fin15AnchoredAtom3315 Fin15AnchoredAtom3321 Fin15AnchoredAtom3392
    Fin15AnchoredAtom3394 Fin15AnchoredAtom3399 Fin15AnchoredAtom3405 Fin15AnchoredAtom3526
    Fin15AnchoredAtom3723 Fin15AnchoredAtom3725 Fin15AnchoredAtom3727 Fin15AnchoredAtom3729
    Fin15AnchoredAtom3731 Fin15AnchoredAtom3736 Fin15AnchoredAtom3803 Fin15AnchoredAtom3805
    Fin15AnchoredAtom3810 Fin15AnchoredAtom3816 Fin15AnchoredAtom3887 Fin15AnchoredAtom3889
    Fin15AnchoredAtom3894 Fin15AnchoredAtom3900 Fin15AnchoredAtom4021 Fin15AnchoredAtom4427
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

theorem fin15Anchored_clause31797 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2880 chi ∧
      ¬Fin15AnchoredAtom2881 chi ∧
      ¬Fin15AnchoredAtom2884 chi ∧
      ¬Fin15AnchoredAtom2885 chi ∧
      ¬Fin15AnchoredAtom2907 chi ∧
      ¬Fin15AnchoredAtom2910 chi ∧
      ¬Fin15AnchoredAtom2911 chi ∧
      ¬Fin15AnchoredAtom2914 chi ∧
      ¬Fin15AnchoredAtom2915 chi ∧
      ¬Fin15AnchoredAtom2921 chi ∧
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
      ¬Fin15AnchoredAtom4428 chi ∧
      ¬Fin15AnchoredAtom4429 chi ∧
      ¬Fin15AnchoredAtom4435 chi ∧
      ¬Fin15AnchoredAtom4441 chi ∧
      ¬Fin15AnchoredAtom4562 chi ∧
      ¬Fin15AnchoredAtom4688 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 4, 5, 9, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26166
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2880 Fin15AnchoredAtom2881 Fin15AnchoredAtom2884
    Fin15AnchoredAtom2885 Fin15AnchoredAtom2907 Fin15AnchoredAtom2910 Fin15AnchoredAtom2911
    Fin15AnchoredAtom2914 Fin15AnchoredAtom2915 Fin15AnchoredAtom2921 Fin15AnchoredAtom2943
    Fin15AnchoredAtom2946 Fin15AnchoredAtom2947 Fin15AnchoredAtom2950 Fin15AnchoredAtom2951
    Fin15AnchoredAtom2957 Fin15AnchoredAtom3024 Fin15AnchoredAtom3025 Fin15AnchoredAtom3031
    Fin15AnchoredAtom3037 Fin15AnchoredAtom3228 Fin15AnchoredAtom3231 Fin15AnchoredAtom3232
    Fin15AnchoredAtom3235 Fin15AnchoredAtom3236 Fin15AnchoredAtom3242 Fin15AnchoredAtom3309
    Fin15AnchoredAtom3310 Fin15AnchoredAtom3316 Fin15AnchoredAtom3322 Fin15AnchoredAtom3393
    Fin15AnchoredAtom3394 Fin15AnchoredAtom3400 Fin15AnchoredAtom3406 Fin15AnchoredAtom3527
    Fin15AnchoredAtom3723 Fin15AnchoredAtom3726 Fin15AnchoredAtom3727 Fin15AnchoredAtom3730
    Fin15AnchoredAtom3731 Fin15AnchoredAtom3737 Fin15AnchoredAtom3804 Fin15AnchoredAtom3805
    Fin15AnchoredAtom3811 Fin15AnchoredAtom3817 Fin15AnchoredAtom3888 Fin15AnchoredAtom3889
    Fin15AnchoredAtom3895 Fin15AnchoredAtom3901 Fin15AnchoredAtom4022 Fin15AnchoredAtom4428
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

theorem fin15Anchored_clause31798 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2880 chi ∧
      ¬Fin15AnchoredAtom2883 chi ∧
      ¬Fin15AnchoredAtom2884 chi ∧
      ¬Fin15AnchoredAtom2885 chi ∧
      ¬Fin15AnchoredAtom2909 chi ∧
      ¬Fin15AnchoredAtom2910 chi ∧
      ¬Fin15AnchoredAtom2911 chi ∧
      ¬Fin15AnchoredAtom2919 chi ∧
      ¬Fin15AnchoredAtom2920 chi ∧
      ¬Fin15AnchoredAtom2921 chi ∧
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
      ¬Fin15AnchoredAtom4433 chi ∧
      ¬Fin15AnchoredAtom4434 chi ∧
      ¬Fin15AnchoredAtom4435 chi ∧
      ¬Fin15AnchoredAtom4445 chi ∧
      ¬Fin15AnchoredAtom4566 chi ∧
      ¬Fin15AnchoredAtom4692 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 4, 5, 9, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29238
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2880 Fin15AnchoredAtom2883 Fin15AnchoredAtom2884
    Fin15AnchoredAtom2885 Fin15AnchoredAtom2909 Fin15AnchoredAtom2910 Fin15AnchoredAtom2911
    Fin15AnchoredAtom2919 Fin15AnchoredAtom2920 Fin15AnchoredAtom2921 Fin15AnchoredAtom2945
    Fin15AnchoredAtom2946 Fin15AnchoredAtom2947 Fin15AnchoredAtom2955 Fin15AnchoredAtom2956
    Fin15AnchoredAtom2957 Fin15AnchoredAtom3029 Fin15AnchoredAtom3030 Fin15AnchoredAtom3031
    Fin15AnchoredAtom3041 Fin15AnchoredAtom3230 Fin15AnchoredAtom3231 Fin15AnchoredAtom3232
    Fin15AnchoredAtom3240 Fin15AnchoredAtom3241 Fin15AnchoredAtom3242 Fin15AnchoredAtom3314
    Fin15AnchoredAtom3315 Fin15AnchoredAtom3316 Fin15AnchoredAtom3326 Fin15AnchoredAtom3398
    Fin15AnchoredAtom3399 Fin15AnchoredAtom3400 Fin15AnchoredAtom3410 Fin15AnchoredAtom3531
    Fin15AnchoredAtom3725 Fin15AnchoredAtom3726 Fin15AnchoredAtom3727 Fin15AnchoredAtom3735
    Fin15AnchoredAtom3736 Fin15AnchoredAtom3737 Fin15AnchoredAtom3809 Fin15AnchoredAtom3810
    Fin15AnchoredAtom3811 Fin15AnchoredAtom3821 Fin15AnchoredAtom3893 Fin15AnchoredAtom3894
    Fin15AnchoredAtom3895 Fin15AnchoredAtom3905 Fin15AnchoredAtom4026 Fin15AnchoredAtom4433
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

theorem fin15Anchored_clause31799 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2881 chi ∧
      ¬Fin15AnchoredAtom2883 chi ∧
      ¬Fin15AnchoredAtom2884 chi ∧
      ¬Fin15AnchoredAtom2885 chi ∧
      ¬Fin15AnchoredAtom2913 chi ∧
      ¬Fin15AnchoredAtom2914 chi ∧
      ¬Fin15AnchoredAtom2915 chi ∧
      ¬Fin15AnchoredAtom2919 chi ∧
      ¬Fin15AnchoredAtom2920 chi ∧
      ¬Fin15AnchoredAtom2921 chi ∧
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
      ¬Fin15AnchoredAtom4439 chi ∧
      ¬Fin15AnchoredAtom4440 chi ∧
      ¬Fin15AnchoredAtom4441 chi ∧
      ¬Fin15AnchoredAtom4445 chi ∧
      ¬Fin15AnchoredAtom4570 chi ∧
      ¬Fin15AnchoredAtom4696 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 4, 5, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29750
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2881 Fin15AnchoredAtom2883 Fin15AnchoredAtom2884
    Fin15AnchoredAtom2885 Fin15AnchoredAtom2913 Fin15AnchoredAtom2914 Fin15AnchoredAtom2915
    Fin15AnchoredAtom2919 Fin15AnchoredAtom2920 Fin15AnchoredAtom2921 Fin15AnchoredAtom2949
    Fin15AnchoredAtom2950 Fin15AnchoredAtom2951 Fin15AnchoredAtom2955 Fin15AnchoredAtom2956
    Fin15AnchoredAtom2957 Fin15AnchoredAtom3035 Fin15AnchoredAtom3036 Fin15AnchoredAtom3037
    Fin15AnchoredAtom3041 Fin15AnchoredAtom3234 Fin15AnchoredAtom3235 Fin15AnchoredAtom3236
    Fin15AnchoredAtom3240 Fin15AnchoredAtom3241 Fin15AnchoredAtom3242 Fin15AnchoredAtom3320
    Fin15AnchoredAtom3321 Fin15AnchoredAtom3322 Fin15AnchoredAtom3326 Fin15AnchoredAtom3404
    Fin15AnchoredAtom3405 Fin15AnchoredAtom3406 Fin15AnchoredAtom3410 Fin15AnchoredAtom3535
    Fin15AnchoredAtom3729 Fin15AnchoredAtom3730 Fin15AnchoredAtom3731 Fin15AnchoredAtom3735
    Fin15AnchoredAtom3736 Fin15AnchoredAtom3737 Fin15AnchoredAtom3815 Fin15AnchoredAtom3816
    Fin15AnchoredAtom3817 Fin15AnchoredAtom3821 Fin15AnchoredAtom3899 Fin15AnchoredAtom3900
    Fin15AnchoredAtom3901 Fin15AnchoredAtom3905 Fin15AnchoredAtom4030 Fin15AnchoredAtom4439
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

theorem fin15Anchored_clause31800 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2886 chi ∧
      ¬Fin15AnchoredAtom2888 chi ∧
      ¬Fin15AnchoredAtom2889 chi ∧
      ¬Fin15AnchoredAtom2891 chi ∧
      ¬Fin15AnchoredAtom2895 chi ∧
      ¬Fin15AnchoredAtom2896 chi ∧
      ¬Fin15AnchoredAtom2898 chi ∧
      ¬Fin15AnchoredAtom2907 chi ∧
      ¬Fin15AnchoredAtom2909 chi ∧
      ¬Fin15AnchoredAtom2913 chi ∧
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
      ¬Fin15AnchoredAtom4452 chi ∧
      ¬Fin15AnchoredAtom4454 chi ∧
      ¬Fin15AnchoredAtom4458 chi ∧
      ¬Fin15AnchoredAtom4483 chi ∧
      ¬Fin15AnchoredAtom4518 chi ∧
      ¬Fin15AnchoredAtom4714 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 4, 6, 7, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05846
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2886 Fin15AnchoredAtom2888 Fin15AnchoredAtom2889
    Fin15AnchoredAtom2891 Fin15AnchoredAtom2895 Fin15AnchoredAtom2896 Fin15AnchoredAtom2898
    Fin15AnchoredAtom2907 Fin15AnchoredAtom2909 Fin15AnchoredAtom2913 Fin15AnchoredAtom2959
    Fin15AnchoredAtom2960 Fin15AnchoredAtom2962 Fin15AnchoredAtom2971 Fin15AnchoredAtom2973
    Fin15AnchoredAtom2977 Fin15AnchoredAtom2992 Fin15AnchoredAtom2994 Fin15AnchoredAtom2998
    Fin15AnchoredAtom3023 Fin15AnchoredAtom3244 Fin15AnchoredAtom3245 Fin15AnchoredAtom3247
    Fin15AnchoredAtom3256 Fin15AnchoredAtom3258 Fin15AnchoredAtom3262 Fin15AnchoredAtom3277
    Fin15AnchoredAtom3279 Fin15AnchoredAtom3283 Fin15AnchoredAtom3308 Fin15AnchoredAtom3417
    Fin15AnchoredAtom3419 Fin15AnchoredAtom3423 Fin15AnchoredAtom3448 Fin15AnchoredAtom3483
    Fin15AnchoredAtom3739 Fin15AnchoredAtom3740 Fin15AnchoredAtom3742 Fin15AnchoredAtom3751
    Fin15AnchoredAtom3753 Fin15AnchoredAtom3757 Fin15AnchoredAtom3772 Fin15AnchoredAtom3774
    Fin15AnchoredAtom3778 Fin15AnchoredAtom3803 Fin15AnchoredAtom3912 Fin15AnchoredAtom3914
    Fin15AnchoredAtom3918 Fin15AnchoredAtom3943 Fin15AnchoredAtom3978 Fin15AnchoredAtom4452
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

theorem fin15Anchored_clause31801 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2886 chi ∧
      ¬Fin15AnchoredAtom2888 chi ∧
      ¬Fin15AnchoredAtom2889 chi ∧
      ¬Fin15AnchoredAtom2892 chi ∧
      ¬Fin15AnchoredAtom2895 chi ∧
      ¬Fin15AnchoredAtom2896 chi ∧
      ¬Fin15AnchoredAtom2899 chi ∧
      ¬Fin15AnchoredAtom2907 chi ∧
      ¬Fin15AnchoredAtom2910 chi ∧
      ¬Fin15AnchoredAtom2914 chi ∧
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
      ¬Fin15AnchoredAtom4452 chi ∧
      ¬Fin15AnchoredAtom4455 chi ∧
      ¬Fin15AnchoredAtom4459 chi ∧
      ¬Fin15AnchoredAtom4484 chi ∧
      ¬Fin15AnchoredAtom4519 chi ∧
      ¬Fin15AnchoredAtom4715 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 4, 6, 7, 9, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09942
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2886 Fin15AnchoredAtom2888 Fin15AnchoredAtom2889
    Fin15AnchoredAtom2892 Fin15AnchoredAtom2895 Fin15AnchoredAtom2896 Fin15AnchoredAtom2899
    Fin15AnchoredAtom2907 Fin15AnchoredAtom2910 Fin15AnchoredAtom2914 Fin15AnchoredAtom2959
    Fin15AnchoredAtom2960 Fin15AnchoredAtom2963 Fin15AnchoredAtom2971 Fin15AnchoredAtom2974
    Fin15AnchoredAtom2978 Fin15AnchoredAtom2992 Fin15AnchoredAtom2995 Fin15AnchoredAtom2999
    Fin15AnchoredAtom3024 Fin15AnchoredAtom3244 Fin15AnchoredAtom3245 Fin15AnchoredAtom3248
    Fin15AnchoredAtom3256 Fin15AnchoredAtom3259 Fin15AnchoredAtom3263 Fin15AnchoredAtom3277
    Fin15AnchoredAtom3280 Fin15AnchoredAtom3284 Fin15AnchoredAtom3309 Fin15AnchoredAtom3417
    Fin15AnchoredAtom3420 Fin15AnchoredAtom3424 Fin15AnchoredAtom3449 Fin15AnchoredAtom3484
    Fin15AnchoredAtom3739 Fin15AnchoredAtom3740 Fin15AnchoredAtom3743 Fin15AnchoredAtom3751
    Fin15AnchoredAtom3754 Fin15AnchoredAtom3758 Fin15AnchoredAtom3772 Fin15AnchoredAtom3775
    Fin15AnchoredAtom3779 Fin15AnchoredAtom3804 Fin15AnchoredAtom3912 Fin15AnchoredAtom3915
    Fin15AnchoredAtom3919 Fin15AnchoredAtom3944 Fin15AnchoredAtom3979 Fin15AnchoredAtom4452
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

theorem fin15Anchored_clause31802 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2886 chi ∧
      ¬Fin15AnchoredAtom2888 chi ∧
      ¬Fin15AnchoredAtom2889 chi ∧
      ¬Fin15AnchoredAtom2893 chi ∧
      ¬Fin15AnchoredAtom2895 chi ∧
      ¬Fin15AnchoredAtom2896 chi ∧
      ¬Fin15AnchoredAtom2900 chi ∧
      ¬Fin15AnchoredAtom2907 chi ∧
      ¬Fin15AnchoredAtom2911 chi ∧
      ¬Fin15AnchoredAtom2915 chi ∧
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
      ¬Fin15AnchoredAtom4452 chi ∧
      ¬Fin15AnchoredAtom4456 chi ∧
      ¬Fin15AnchoredAtom4460 chi ∧
      ¬Fin15AnchoredAtom4485 chi ∧
      ¬Fin15AnchoredAtom4520 chi ∧
      ¬Fin15AnchoredAtom4716 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 4, 6, 7, 9, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask18134
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2886 Fin15AnchoredAtom2888 Fin15AnchoredAtom2889
    Fin15AnchoredAtom2893 Fin15AnchoredAtom2895 Fin15AnchoredAtom2896 Fin15AnchoredAtom2900
    Fin15AnchoredAtom2907 Fin15AnchoredAtom2911 Fin15AnchoredAtom2915 Fin15AnchoredAtom2959
    Fin15AnchoredAtom2960 Fin15AnchoredAtom2964 Fin15AnchoredAtom2971 Fin15AnchoredAtom2975
    Fin15AnchoredAtom2979 Fin15AnchoredAtom2992 Fin15AnchoredAtom2996 Fin15AnchoredAtom3000
    Fin15AnchoredAtom3025 Fin15AnchoredAtom3244 Fin15AnchoredAtom3245 Fin15AnchoredAtom3249
    Fin15AnchoredAtom3256 Fin15AnchoredAtom3260 Fin15AnchoredAtom3264 Fin15AnchoredAtom3277
    Fin15AnchoredAtom3281 Fin15AnchoredAtom3285 Fin15AnchoredAtom3310 Fin15AnchoredAtom3417
    Fin15AnchoredAtom3421 Fin15AnchoredAtom3425 Fin15AnchoredAtom3450 Fin15AnchoredAtom3485
    Fin15AnchoredAtom3739 Fin15AnchoredAtom3740 Fin15AnchoredAtom3744 Fin15AnchoredAtom3751
    Fin15AnchoredAtom3755 Fin15AnchoredAtom3759 Fin15AnchoredAtom3772 Fin15AnchoredAtom3776
    Fin15AnchoredAtom3780 Fin15AnchoredAtom3805 Fin15AnchoredAtom3912 Fin15AnchoredAtom3916
    Fin15AnchoredAtom3920 Fin15AnchoredAtom3945 Fin15AnchoredAtom3980 Fin15AnchoredAtom4452
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

theorem fin15Anchored_clause31803 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2886 chi ∧
      ¬Fin15AnchoredAtom2888 chi ∧
      ¬Fin15AnchoredAtom2891 chi ∧
      ¬Fin15AnchoredAtom2892 chi ∧
      ¬Fin15AnchoredAtom2895 chi ∧
      ¬Fin15AnchoredAtom2898 chi ∧
      ¬Fin15AnchoredAtom2899 chi ∧
      ¬Fin15AnchoredAtom2909 chi ∧
      ¬Fin15AnchoredAtom2910 chi ∧
      ¬Fin15AnchoredAtom2919 chi ∧
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
      ¬Fin15AnchoredAtom4454 chi ∧
      ¬Fin15AnchoredAtom4455 chi ∧
      ¬Fin15AnchoredAtom4464 chi ∧
      ¬Fin15AnchoredAtom4489 chi ∧
      ¬Fin15AnchoredAtom4524 chi ∧
      ¬Fin15AnchoredAtom4720 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 4, 6, 7, 9, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13014
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2886 Fin15AnchoredAtom2888 Fin15AnchoredAtom2891
    Fin15AnchoredAtom2892 Fin15AnchoredAtom2895 Fin15AnchoredAtom2898 Fin15AnchoredAtom2899
    Fin15AnchoredAtom2909 Fin15AnchoredAtom2910 Fin15AnchoredAtom2919 Fin15AnchoredAtom2959
    Fin15AnchoredAtom2962 Fin15AnchoredAtom2963 Fin15AnchoredAtom2973 Fin15AnchoredAtom2974
    Fin15AnchoredAtom2983 Fin15AnchoredAtom2994 Fin15AnchoredAtom2995 Fin15AnchoredAtom3004
    Fin15AnchoredAtom3029 Fin15AnchoredAtom3244 Fin15AnchoredAtom3247 Fin15AnchoredAtom3248
    Fin15AnchoredAtom3258 Fin15AnchoredAtom3259 Fin15AnchoredAtom3268 Fin15AnchoredAtom3279
    Fin15AnchoredAtom3280 Fin15AnchoredAtom3289 Fin15AnchoredAtom3314 Fin15AnchoredAtom3419
    Fin15AnchoredAtom3420 Fin15AnchoredAtom3429 Fin15AnchoredAtom3454 Fin15AnchoredAtom3489
    Fin15AnchoredAtom3739 Fin15AnchoredAtom3742 Fin15AnchoredAtom3743 Fin15AnchoredAtom3753
    Fin15AnchoredAtom3754 Fin15AnchoredAtom3763 Fin15AnchoredAtom3774 Fin15AnchoredAtom3775
    Fin15AnchoredAtom3784 Fin15AnchoredAtom3809 Fin15AnchoredAtom3914 Fin15AnchoredAtom3915
    Fin15AnchoredAtom3924 Fin15AnchoredAtom3949 Fin15AnchoredAtom3984 Fin15AnchoredAtom4454
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

theorem fin15Anchored_clause31804 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2886 chi ∧
      ¬Fin15AnchoredAtom2888 chi ∧
      ¬Fin15AnchoredAtom2891 chi ∧
      ¬Fin15AnchoredAtom2893 chi ∧
      ¬Fin15AnchoredAtom2895 chi ∧
      ¬Fin15AnchoredAtom2898 chi ∧
      ¬Fin15AnchoredAtom2900 chi ∧
      ¬Fin15AnchoredAtom2909 chi ∧
      ¬Fin15AnchoredAtom2911 chi ∧
      ¬Fin15AnchoredAtom2920 chi ∧
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
      ¬Fin15AnchoredAtom4454 chi ∧
      ¬Fin15AnchoredAtom4456 chi ∧
      ¬Fin15AnchoredAtom4465 chi ∧
      ¬Fin15AnchoredAtom4490 chi ∧
      ¬Fin15AnchoredAtom4525 chi ∧
      ¬Fin15AnchoredAtom4721 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 4, 6, 7, 9, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21206
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2886 Fin15AnchoredAtom2888 Fin15AnchoredAtom2891
    Fin15AnchoredAtom2893 Fin15AnchoredAtom2895 Fin15AnchoredAtom2898 Fin15AnchoredAtom2900
    Fin15AnchoredAtom2909 Fin15AnchoredAtom2911 Fin15AnchoredAtom2920 Fin15AnchoredAtom2959
    Fin15AnchoredAtom2962 Fin15AnchoredAtom2964 Fin15AnchoredAtom2973 Fin15AnchoredAtom2975
    Fin15AnchoredAtom2984 Fin15AnchoredAtom2994 Fin15AnchoredAtom2996 Fin15AnchoredAtom3005
    Fin15AnchoredAtom3030 Fin15AnchoredAtom3244 Fin15AnchoredAtom3247 Fin15AnchoredAtom3249
    Fin15AnchoredAtom3258 Fin15AnchoredAtom3260 Fin15AnchoredAtom3269 Fin15AnchoredAtom3279
    Fin15AnchoredAtom3281 Fin15AnchoredAtom3290 Fin15AnchoredAtom3315 Fin15AnchoredAtom3419
    Fin15AnchoredAtom3421 Fin15AnchoredAtom3430 Fin15AnchoredAtom3455 Fin15AnchoredAtom3490
    Fin15AnchoredAtom3739 Fin15AnchoredAtom3742 Fin15AnchoredAtom3744 Fin15AnchoredAtom3753
    Fin15AnchoredAtom3755 Fin15AnchoredAtom3764 Fin15AnchoredAtom3774 Fin15AnchoredAtom3776
    Fin15AnchoredAtom3785 Fin15AnchoredAtom3810 Fin15AnchoredAtom3914 Fin15AnchoredAtom3916
    Fin15AnchoredAtom3925 Fin15AnchoredAtom3950 Fin15AnchoredAtom3985 Fin15AnchoredAtom4454
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

theorem fin15Anchored_clause31805 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2886 chi ∧
      ¬Fin15AnchoredAtom2888 chi ∧
      ¬Fin15AnchoredAtom2892 chi ∧
      ¬Fin15AnchoredAtom2893 chi ∧
      ¬Fin15AnchoredAtom2895 chi ∧
      ¬Fin15AnchoredAtom2899 chi ∧
      ¬Fin15AnchoredAtom2900 chi ∧
      ¬Fin15AnchoredAtom2910 chi ∧
      ¬Fin15AnchoredAtom2911 chi ∧
      ¬Fin15AnchoredAtom2921 chi ∧
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
      ¬Fin15AnchoredAtom4455 chi ∧
      ¬Fin15AnchoredAtom4456 chi ∧
      ¬Fin15AnchoredAtom4466 chi ∧
      ¬Fin15AnchoredAtom4491 chi ∧
      ¬Fin15AnchoredAtom4526 chi ∧
      ¬Fin15AnchoredAtom4722 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 4, 6, 7, 9, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25302
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2886 Fin15AnchoredAtom2888 Fin15AnchoredAtom2892
    Fin15AnchoredAtom2893 Fin15AnchoredAtom2895 Fin15AnchoredAtom2899 Fin15AnchoredAtom2900
    Fin15AnchoredAtom2910 Fin15AnchoredAtom2911 Fin15AnchoredAtom2921 Fin15AnchoredAtom2959
    Fin15AnchoredAtom2963 Fin15AnchoredAtom2964 Fin15AnchoredAtom2974 Fin15AnchoredAtom2975
    Fin15AnchoredAtom2985 Fin15AnchoredAtom2995 Fin15AnchoredAtom2996 Fin15AnchoredAtom3006
    Fin15AnchoredAtom3031 Fin15AnchoredAtom3244 Fin15AnchoredAtom3248 Fin15AnchoredAtom3249
    Fin15AnchoredAtom3259 Fin15AnchoredAtom3260 Fin15AnchoredAtom3270 Fin15AnchoredAtom3280
    Fin15AnchoredAtom3281 Fin15AnchoredAtom3291 Fin15AnchoredAtom3316 Fin15AnchoredAtom3420
    Fin15AnchoredAtom3421 Fin15AnchoredAtom3431 Fin15AnchoredAtom3456 Fin15AnchoredAtom3491
    Fin15AnchoredAtom3739 Fin15AnchoredAtom3743 Fin15AnchoredAtom3744 Fin15AnchoredAtom3754
    Fin15AnchoredAtom3755 Fin15AnchoredAtom3765 Fin15AnchoredAtom3775 Fin15AnchoredAtom3776
    Fin15AnchoredAtom3786 Fin15AnchoredAtom3811 Fin15AnchoredAtom3915 Fin15AnchoredAtom3916
    Fin15AnchoredAtom3926 Fin15AnchoredAtom3951 Fin15AnchoredAtom3986 Fin15AnchoredAtom4455
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

theorem fin15Anchored_clause31806 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2886 chi ∧
      ¬Fin15AnchoredAtom2889 chi ∧
      ¬Fin15AnchoredAtom2891 chi ∧
      ¬Fin15AnchoredAtom2892 chi ∧
      ¬Fin15AnchoredAtom2896 chi ∧
      ¬Fin15AnchoredAtom2898 chi ∧
      ¬Fin15AnchoredAtom2899 chi ∧
      ¬Fin15AnchoredAtom2913 chi ∧
      ¬Fin15AnchoredAtom2914 chi ∧
      ¬Fin15AnchoredAtom2919 chi ∧
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
      ¬Fin15AnchoredAtom4458 chi ∧
      ¬Fin15AnchoredAtom4459 chi ∧
      ¬Fin15AnchoredAtom4464 chi ∧
      ¬Fin15AnchoredAtom4495 chi ∧
      ¬Fin15AnchoredAtom4530 chi ∧
      ¬Fin15AnchoredAtom4726 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 4, 6, 7, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13526
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2886 Fin15AnchoredAtom2889 Fin15AnchoredAtom2891
    Fin15AnchoredAtom2892 Fin15AnchoredAtom2896 Fin15AnchoredAtom2898 Fin15AnchoredAtom2899
    Fin15AnchoredAtom2913 Fin15AnchoredAtom2914 Fin15AnchoredAtom2919 Fin15AnchoredAtom2960
    Fin15AnchoredAtom2962 Fin15AnchoredAtom2963 Fin15AnchoredAtom2977 Fin15AnchoredAtom2978
    Fin15AnchoredAtom2983 Fin15AnchoredAtom2998 Fin15AnchoredAtom2999 Fin15AnchoredAtom3004
    Fin15AnchoredAtom3035 Fin15AnchoredAtom3245 Fin15AnchoredAtom3247 Fin15AnchoredAtom3248
    Fin15AnchoredAtom3262 Fin15AnchoredAtom3263 Fin15AnchoredAtom3268 Fin15AnchoredAtom3283
    Fin15AnchoredAtom3284 Fin15AnchoredAtom3289 Fin15AnchoredAtom3320 Fin15AnchoredAtom3423
    Fin15AnchoredAtom3424 Fin15AnchoredAtom3429 Fin15AnchoredAtom3460 Fin15AnchoredAtom3495
    Fin15AnchoredAtom3740 Fin15AnchoredAtom3742 Fin15AnchoredAtom3743 Fin15AnchoredAtom3757
    Fin15AnchoredAtom3758 Fin15AnchoredAtom3763 Fin15AnchoredAtom3778 Fin15AnchoredAtom3779
    Fin15AnchoredAtom3784 Fin15AnchoredAtom3815 Fin15AnchoredAtom3918 Fin15AnchoredAtom3919
    Fin15AnchoredAtom3924 Fin15AnchoredAtom3955 Fin15AnchoredAtom3990 Fin15AnchoredAtom4458
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

theorem fin15Anchored_clause31807 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2886 chi ∧
      ¬Fin15AnchoredAtom2889 chi ∧
      ¬Fin15AnchoredAtom2891 chi ∧
      ¬Fin15AnchoredAtom2893 chi ∧
      ¬Fin15AnchoredAtom2896 chi ∧
      ¬Fin15AnchoredAtom2898 chi ∧
      ¬Fin15AnchoredAtom2900 chi ∧
      ¬Fin15AnchoredAtom2913 chi ∧
      ¬Fin15AnchoredAtom2915 chi ∧
      ¬Fin15AnchoredAtom2920 chi ∧
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
      ¬Fin15AnchoredAtom4458 chi ∧
      ¬Fin15AnchoredAtom4460 chi ∧
      ¬Fin15AnchoredAtom4465 chi ∧
      ¬Fin15AnchoredAtom4496 chi ∧
      ¬Fin15AnchoredAtom4531 chi ∧
      ¬Fin15AnchoredAtom4727 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 4, 6, 7, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21718
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2886 Fin15AnchoredAtom2889 Fin15AnchoredAtom2891
    Fin15AnchoredAtom2893 Fin15AnchoredAtom2896 Fin15AnchoredAtom2898 Fin15AnchoredAtom2900
    Fin15AnchoredAtom2913 Fin15AnchoredAtom2915 Fin15AnchoredAtom2920 Fin15AnchoredAtom2960
    Fin15AnchoredAtom2962 Fin15AnchoredAtom2964 Fin15AnchoredAtom2977 Fin15AnchoredAtom2979
    Fin15AnchoredAtom2984 Fin15AnchoredAtom2998 Fin15AnchoredAtom3000 Fin15AnchoredAtom3005
    Fin15AnchoredAtom3036 Fin15AnchoredAtom3245 Fin15AnchoredAtom3247 Fin15AnchoredAtom3249
    Fin15AnchoredAtom3262 Fin15AnchoredAtom3264 Fin15AnchoredAtom3269 Fin15AnchoredAtom3283
    Fin15AnchoredAtom3285 Fin15AnchoredAtom3290 Fin15AnchoredAtom3321 Fin15AnchoredAtom3423
    Fin15AnchoredAtom3425 Fin15AnchoredAtom3430 Fin15AnchoredAtom3461 Fin15AnchoredAtom3496
    Fin15AnchoredAtom3740 Fin15AnchoredAtom3742 Fin15AnchoredAtom3744 Fin15AnchoredAtom3757
    Fin15AnchoredAtom3759 Fin15AnchoredAtom3764 Fin15AnchoredAtom3778 Fin15AnchoredAtom3780
    Fin15AnchoredAtom3785 Fin15AnchoredAtom3816 Fin15AnchoredAtom3918 Fin15AnchoredAtom3920
    Fin15AnchoredAtom3925 Fin15AnchoredAtom3956 Fin15AnchoredAtom3991 Fin15AnchoredAtom4458
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

theorem fin15Anchored_clause31808 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2886 chi ∧
      ¬Fin15AnchoredAtom2889 chi ∧
      ¬Fin15AnchoredAtom2892 chi ∧
      ¬Fin15AnchoredAtom2893 chi ∧
      ¬Fin15AnchoredAtom2896 chi ∧
      ¬Fin15AnchoredAtom2899 chi ∧
      ¬Fin15AnchoredAtom2900 chi ∧
      ¬Fin15AnchoredAtom2914 chi ∧
      ¬Fin15AnchoredAtom2915 chi ∧
      ¬Fin15AnchoredAtom2921 chi ∧
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
      ¬Fin15AnchoredAtom4459 chi ∧
      ¬Fin15AnchoredAtom4460 chi ∧
      ¬Fin15AnchoredAtom4466 chi ∧
      ¬Fin15AnchoredAtom4497 chi ∧
      ¬Fin15AnchoredAtom4532 chi ∧
      ¬Fin15AnchoredAtom4728 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 4, 6, 7, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25814
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2886 Fin15AnchoredAtom2889 Fin15AnchoredAtom2892
    Fin15AnchoredAtom2893 Fin15AnchoredAtom2896 Fin15AnchoredAtom2899 Fin15AnchoredAtom2900
    Fin15AnchoredAtom2914 Fin15AnchoredAtom2915 Fin15AnchoredAtom2921 Fin15AnchoredAtom2960
    Fin15AnchoredAtom2963 Fin15AnchoredAtom2964 Fin15AnchoredAtom2978 Fin15AnchoredAtom2979
    Fin15AnchoredAtom2985 Fin15AnchoredAtom2999 Fin15AnchoredAtom3000 Fin15AnchoredAtom3006
    Fin15AnchoredAtom3037 Fin15AnchoredAtom3245 Fin15AnchoredAtom3248 Fin15AnchoredAtom3249
    Fin15AnchoredAtom3263 Fin15AnchoredAtom3264 Fin15AnchoredAtom3270 Fin15AnchoredAtom3284
    Fin15AnchoredAtom3285 Fin15AnchoredAtom3291 Fin15AnchoredAtom3322 Fin15AnchoredAtom3424
    Fin15AnchoredAtom3425 Fin15AnchoredAtom3431 Fin15AnchoredAtom3462 Fin15AnchoredAtom3497
    Fin15AnchoredAtom3740 Fin15AnchoredAtom3743 Fin15AnchoredAtom3744 Fin15AnchoredAtom3758
    Fin15AnchoredAtom3759 Fin15AnchoredAtom3765 Fin15AnchoredAtom3779 Fin15AnchoredAtom3780
    Fin15AnchoredAtom3786 Fin15AnchoredAtom3817 Fin15AnchoredAtom3919 Fin15AnchoredAtom3920
    Fin15AnchoredAtom3926 Fin15AnchoredAtom3957 Fin15AnchoredAtom3992 Fin15AnchoredAtom4459
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

theorem fin15Anchored_clause31809 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2886 chi ∧
      ¬Fin15AnchoredAtom2891 chi ∧
      ¬Fin15AnchoredAtom2892 chi ∧
      ¬Fin15AnchoredAtom2893 chi ∧
      ¬Fin15AnchoredAtom2898 chi ∧
      ¬Fin15AnchoredAtom2899 chi ∧
      ¬Fin15AnchoredAtom2900 chi ∧
      ¬Fin15AnchoredAtom2919 chi ∧
      ¬Fin15AnchoredAtom2920 chi ∧
      ¬Fin15AnchoredAtom2921 chi ∧
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
      ¬Fin15AnchoredAtom4464 chi ∧
      ¬Fin15AnchoredAtom4465 chi ∧
      ¬Fin15AnchoredAtom4466 chi ∧
      ¬Fin15AnchoredAtom4501 chi ∧
      ¬Fin15AnchoredAtom4536 chi ∧
      ¬Fin15AnchoredAtom4732 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 4, 6, 7, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask28886
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2886 Fin15AnchoredAtom2891 Fin15AnchoredAtom2892
    Fin15AnchoredAtom2893 Fin15AnchoredAtom2898 Fin15AnchoredAtom2899 Fin15AnchoredAtom2900
    Fin15AnchoredAtom2919 Fin15AnchoredAtom2920 Fin15AnchoredAtom2921 Fin15AnchoredAtom2962
    Fin15AnchoredAtom2963 Fin15AnchoredAtom2964 Fin15AnchoredAtom2983 Fin15AnchoredAtom2984
    Fin15AnchoredAtom2985 Fin15AnchoredAtom3004 Fin15AnchoredAtom3005 Fin15AnchoredAtom3006
    Fin15AnchoredAtom3041 Fin15AnchoredAtom3247 Fin15AnchoredAtom3248 Fin15AnchoredAtom3249
    Fin15AnchoredAtom3268 Fin15AnchoredAtom3269 Fin15AnchoredAtom3270 Fin15AnchoredAtom3289
    Fin15AnchoredAtom3290 Fin15AnchoredAtom3291 Fin15AnchoredAtom3326 Fin15AnchoredAtom3429
    Fin15AnchoredAtom3430 Fin15AnchoredAtom3431 Fin15AnchoredAtom3466 Fin15AnchoredAtom3501
    Fin15AnchoredAtom3742 Fin15AnchoredAtom3743 Fin15AnchoredAtom3744 Fin15AnchoredAtom3763
    Fin15AnchoredAtom3764 Fin15AnchoredAtom3765 Fin15AnchoredAtom3784 Fin15AnchoredAtom3785
    Fin15AnchoredAtom3786 Fin15AnchoredAtom3821 Fin15AnchoredAtom3924 Fin15AnchoredAtom3925
    Fin15AnchoredAtom3926 Fin15AnchoredAtom3961 Fin15AnchoredAtom3996 Fin15AnchoredAtom4464
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

theorem fin15Anchored_clause31810 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2888 chi ∧
      ¬Fin15AnchoredAtom2889 chi ∧
      ¬Fin15AnchoredAtom2891 chi ∧
      ¬Fin15AnchoredAtom2892 chi ∧
      ¬Fin15AnchoredAtom2907 chi ∧
      ¬Fin15AnchoredAtom2909 chi ∧
      ¬Fin15AnchoredAtom2910 chi ∧
      ¬Fin15AnchoredAtom2913 chi ∧
      ¬Fin15AnchoredAtom2914 chi ∧
      ¬Fin15AnchoredAtom2919 chi ∧
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
      ¬Fin15AnchoredAtom4483 chi ∧
      ¬Fin15AnchoredAtom4484 chi ∧
      ¬Fin15AnchoredAtom4489 chi ∧
      ¬Fin15AnchoredAtom4495 chi ∧
      ¬Fin15AnchoredAtom4560 chi ∧
      ¬Fin15AnchoredAtom4756 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 4, 6, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13910
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2888 Fin15AnchoredAtom2889 Fin15AnchoredAtom2891
    Fin15AnchoredAtom2892 Fin15AnchoredAtom2907 Fin15AnchoredAtom2909 Fin15AnchoredAtom2910
    Fin15AnchoredAtom2913 Fin15AnchoredAtom2914 Fin15AnchoredAtom2919 Fin15AnchoredAtom2971
    Fin15AnchoredAtom2973 Fin15AnchoredAtom2974 Fin15AnchoredAtom2977 Fin15AnchoredAtom2978
    Fin15AnchoredAtom2983 Fin15AnchoredAtom3023 Fin15AnchoredAtom3024 Fin15AnchoredAtom3029
    Fin15AnchoredAtom3035 Fin15AnchoredAtom3256 Fin15AnchoredAtom3258 Fin15AnchoredAtom3259
    Fin15AnchoredAtom3262 Fin15AnchoredAtom3263 Fin15AnchoredAtom3268 Fin15AnchoredAtom3308
    Fin15AnchoredAtom3309 Fin15AnchoredAtom3314 Fin15AnchoredAtom3320 Fin15AnchoredAtom3448
    Fin15AnchoredAtom3449 Fin15AnchoredAtom3454 Fin15AnchoredAtom3460 Fin15AnchoredAtom3525
    Fin15AnchoredAtom3751 Fin15AnchoredAtom3753 Fin15AnchoredAtom3754 Fin15AnchoredAtom3757
    Fin15AnchoredAtom3758 Fin15AnchoredAtom3763 Fin15AnchoredAtom3803 Fin15AnchoredAtom3804
    Fin15AnchoredAtom3809 Fin15AnchoredAtom3815 Fin15AnchoredAtom3943 Fin15AnchoredAtom3944
    Fin15AnchoredAtom3949 Fin15AnchoredAtom3955 Fin15AnchoredAtom4020 Fin15AnchoredAtom4483
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

theorem fin15Anchored_clause31811 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2888 chi ∧
      ¬Fin15AnchoredAtom2889 chi ∧
      ¬Fin15AnchoredAtom2891 chi ∧
      ¬Fin15AnchoredAtom2893 chi ∧
      ¬Fin15AnchoredAtom2907 chi ∧
      ¬Fin15AnchoredAtom2909 chi ∧
      ¬Fin15AnchoredAtom2911 chi ∧
      ¬Fin15AnchoredAtom2913 chi ∧
      ¬Fin15AnchoredAtom2915 chi ∧
      ¬Fin15AnchoredAtom2920 chi ∧
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
      ¬Fin15AnchoredAtom4483 chi ∧
      ¬Fin15AnchoredAtom4485 chi ∧
      ¬Fin15AnchoredAtom4490 chi ∧
      ¬Fin15AnchoredAtom4496 chi ∧
      ¬Fin15AnchoredAtom4561 chi ∧
      ¬Fin15AnchoredAtom4757 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 4, 6, 9, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22102
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2888 Fin15AnchoredAtom2889 Fin15AnchoredAtom2891
    Fin15AnchoredAtom2893 Fin15AnchoredAtom2907 Fin15AnchoredAtom2909 Fin15AnchoredAtom2911
    Fin15AnchoredAtom2913 Fin15AnchoredAtom2915 Fin15AnchoredAtom2920 Fin15AnchoredAtom2971
    Fin15AnchoredAtom2973 Fin15AnchoredAtom2975 Fin15AnchoredAtom2977 Fin15AnchoredAtom2979
    Fin15AnchoredAtom2984 Fin15AnchoredAtom3023 Fin15AnchoredAtom3025 Fin15AnchoredAtom3030
    Fin15AnchoredAtom3036 Fin15AnchoredAtom3256 Fin15AnchoredAtom3258 Fin15AnchoredAtom3260
    Fin15AnchoredAtom3262 Fin15AnchoredAtom3264 Fin15AnchoredAtom3269 Fin15AnchoredAtom3308
    Fin15AnchoredAtom3310 Fin15AnchoredAtom3315 Fin15AnchoredAtom3321 Fin15AnchoredAtom3448
    Fin15AnchoredAtom3450 Fin15AnchoredAtom3455 Fin15AnchoredAtom3461 Fin15AnchoredAtom3526
    Fin15AnchoredAtom3751 Fin15AnchoredAtom3753 Fin15AnchoredAtom3755 Fin15AnchoredAtom3757
    Fin15AnchoredAtom3759 Fin15AnchoredAtom3764 Fin15AnchoredAtom3803 Fin15AnchoredAtom3805
    Fin15AnchoredAtom3810 Fin15AnchoredAtom3816 Fin15AnchoredAtom3943 Fin15AnchoredAtom3945
    Fin15AnchoredAtom3950 Fin15AnchoredAtom3956 Fin15AnchoredAtom4021 Fin15AnchoredAtom4483
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

theorem fin15Anchored_clause31812 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2888 chi ∧
      ¬Fin15AnchoredAtom2889 chi ∧
      ¬Fin15AnchoredAtom2892 chi ∧
      ¬Fin15AnchoredAtom2893 chi ∧
      ¬Fin15AnchoredAtom2907 chi ∧
      ¬Fin15AnchoredAtom2910 chi ∧
      ¬Fin15AnchoredAtom2911 chi ∧
      ¬Fin15AnchoredAtom2914 chi ∧
      ¬Fin15AnchoredAtom2915 chi ∧
      ¬Fin15AnchoredAtom2921 chi ∧
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
      ¬Fin15AnchoredAtom4484 chi ∧
      ¬Fin15AnchoredAtom4485 chi ∧
      ¬Fin15AnchoredAtom4491 chi ∧
      ¬Fin15AnchoredAtom4497 chi ∧
      ¬Fin15AnchoredAtom4562 chi ∧
      ¬Fin15AnchoredAtom4758 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 4, 6, 9, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26198
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2888 Fin15AnchoredAtom2889 Fin15AnchoredAtom2892
    Fin15AnchoredAtom2893 Fin15AnchoredAtom2907 Fin15AnchoredAtom2910 Fin15AnchoredAtom2911
    Fin15AnchoredAtom2914 Fin15AnchoredAtom2915 Fin15AnchoredAtom2921 Fin15AnchoredAtom2971
    Fin15AnchoredAtom2974 Fin15AnchoredAtom2975 Fin15AnchoredAtom2978 Fin15AnchoredAtom2979
    Fin15AnchoredAtom2985 Fin15AnchoredAtom3024 Fin15AnchoredAtom3025 Fin15AnchoredAtom3031
    Fin15AnchoredAtom3037 Fin15AnchoredAtom3256 Fin15AnchoredAtom3259 Fin15AnchoredAtom3260
    Fin15AnchoredAtom3263 Fin15AnchoredAtom3264 Fin15AnchoredAtom3270 Fin15AnchoredAtom3309
    Fin15AnchoredAtom3310 Fin15AnchoredAtom3316 Fin15AnchoredAtom3322 Fin15AnchoredAtom3449
    Fin15AnchoredAtom3450 Fin15AnchoredAtom3456 Fin15AnchoredAtom3462 Fin15AnchoredAtom3527
    Fin15AnchoredAtom3751 Fin15AnchoredAtom3754 Fin15AnchoredAtom3755 Fin15AnchoredAtom3758
    Fin15AnchoredAtom3759 Fin15AnchoredAtom3765 Fin15AnchoredAtom3804 Fin15AnchoredAtom3805
    Fin15AnchoredAtom3811 Fin15AnchoredAtom3817 Fin15AnchoredAtom3944 Fin15AnchoredAtom3945
    Fin15AnchoredAtom3951 Fin15AnchoredAtom3957 Fin15AnchoredAtom4022 Fin15AnchoredAtom4484
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

theorem fin15Anchored_clause31813 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2888 chi ∧
      ¬Fin15AnchoredAtom2891 chi ∧
      ¬Fin15AnchoredAtom2892 chi ∧
      ¬Fin15AnchoredAtom2893 chi ∧
      ¬Fin15AnchoredAtom2909 chi ∧
      ¬Fin15AnchoredAtom2910 chi ∧
      ¬Fin15AnchoredAtom2911 chi ∧
      ¬Fin15AnchoredAtom2919 chi ∧
      ¬Fin15AnchoredAtom2920 chi ∧
      ¬Fin15AnchoredAtom2921 chi ∧
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
      ¬Fin15AnchoredAtom4489 chi ∧
      ¬Fin15AnchoredAtom4490 chi ∧
      ¬Fin15AnchoredAtom4491 chi ∧
      ¬Fin15AnchoredAtom4501 chi ∧
      ¬Fin15AnchoredAtom4566 chi ∧
      ¬Fin15AnchoredAtom4762 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 4, 6, 9, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29270
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2888 Fin15AnchoredAtom2891 Fin15AnchoredAtom2892
    Fin15AnchoredAtom2893 Fin15AnchoredAtom2909 Fin15AnchoredAtom2910 Fin15AnchoredAtom2911
    Fin15AnchoredAtom2919 Fin15AnchoredAtom2920 Fin15AnchoredAtom2921 Fin15AnchoredAtom2973
    Fin15AnchoredAtom2974 Fin15AnchoredAtom2975 Fin15AnchoredAtom2983 Fin15AnchoredAtom2984
    Fin15AnchoredAtom2985 Fin15AnchoredAtom3029 Fin15AnchoredAtom3030 Fin15AnchoredAtom3031
    Fin15AnchoredAtom3041 Fin15AnchoredAtom3258 Fin15AnchoredAtom3259 Fin15AnchoredAtom3260
    Fin15AnchoredAtom3268 Fin15AnchoredAtom3269 Fin15AnchoredAtom3270 Fin15AnchoredAtom3314
    Fin15AnchoredAtom3315 Fin15AnchoredAtom3316 Fin15AnchoredAtom3326 Fin15AnchoredAtom3454
    Fin15AnchoredAtom3455 Fin15AnchoredAtom3456 Fin15AnchoredAtom3466 Fin15AnchoredAtom3531
    Fin15AnchoredAtom3753 Fin15AnchoredAtom3754 Fin15AnchoredAtom3755 Fin15AnchoredAtom3763
    Fin15AnchoredAtom3764 Fin15AnchoredAtom3765 Fin15AnchoredAtom3809 Fin15AnchoredAtom3810
    Fin15AnchoredAtom3811 Fin15AnchoredAtom3821 Fin15AnchoredAtom3949 Fin15AnchoredAtom3950
    Fin15AnchoredAtom3951 Fin15AnchoredAtom3961 Fin15AnchoredAtom4026 Fin15AnchoredAtom4489
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

theorem fin15Anchored_clause31814 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2889 chi ∧
      ¬Fin15AnchoredAtom2891 chi ∧
      ¬Fin15AnchoredAtom2892 chi ∧
      ¬Fin15AnchoredAtom2893 chi ∧
      ¬Fin15AnchoredAtom2913 chi ∧
      ¬Fin15AnchoredAtom2914 chi ∧
      ¬Fin15AnchoredAtom2915 chi ∧
      ¬Fin15AnchoredAtom2919 chi ∧
      ¬Fin15AnchoredAtom2920 chi ∧
      ¬Fin15AnchoredAtom2921 chi ∧
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
      ¬Fin15AnchoredAtom4495 chi ∧
      ¬Fin15AnchoredAtom4496 chi ∧
      ¬Fin15AnchoredAtom4497 chi ∧
      ¬Fin15AnchoredAtom4501 chi ∧
      ¬Fin15AnchoredAtom4570 chi ∧
      ¬Fin15AnchoredAtom4766 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 4, 6, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29782
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2889 Fin15AnchoredAtom2891 Fin15AnchoredAtom2892
    Fin15AnchoredAtom2893 Fin15AnchoredAtom2913 Fin15AnchoredAtom2914 Fin15AnchoredAtom2915
    Fin15AnchoredAtom2919 Fin15AnchoredAtom2920 Fin15AnchoredAtom2921 Fin15AnchoredAtom2977
    Fin15AnchoredAtom2978 Fin15AnchoredAtom2979 Fin15AnchoredAtom2983 Fin15AnchoredAtom2984
    Fin15AnchoredAtom2985 Fin15AnchoredAtom3035 Fin15AnchoredAtom3036 Fin15AnchoredAtom3037
    Fin15AnchoredAtom3041 Fin15AnchoredAtom3262 Fin15AnchoredAtom3263 Fin15AnchoredAtom3264
    Fin15AnchoredAtom3268 Fin15AnchoredAtom3269 Fin15AnchoredAtom3270 Fin15AnchoredAtom3320
    Fin15AnchoredAtom3321 Fin15AnchoredAtom3322 Fin15AnchoredAtom3326 Fin15AnchoredAtom3460
    Fin15AnchoredAtom3461 Fin15AnchoredAtom3462 Fin15AnchoredAtom3466 Fin15AnchoredAtom3535
    Fin15AnchoredAtom3757 Fin15AnchoredAtom3758 Fin15AnchoredAtom3759 Fin15AnchoredAtom3763
    Fin15AnchoredAtom3764 Fin15AnchoredAtom3765 Fin15AnchoredAtom3815 Fin15AnchoredAtom3816
    Fin15AnchoredAtom3817 Fin15AnchoredAtom3821 Fin15AnchoredAtom3955 Fin15AnchoredAtom3956
    Fin15AnchoredAtom3957 Fin15AnchoredAtom3961 Fin15AnchoredAtom4030 Fin15AnchoredAtom4495
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

theorem fin15Anchored_clause31815 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2895 chi ∧
      ¬Fin15AnchoredAtom2896 chi ∧
      ¬Fin15AnchoredAtom2898 chi ∧
      ¬Fin15AnchoredAtom2899 chi ∧
      ¬Fin15AnchoredAtom2907 chi ∧
      ¬Fin15AnchoredAtom2909 chi ∧
      ¬Fin15AnchoredAtom2910 chi ∧
      ¬Fin15AnchoredAtom2913 chi ∧
      ¬Fin15AnchoredAtom2914 chi ∧
      ¬Fin15AnchoredAtom2919 chi ∧
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
      ¬Fin15AnchoredAtom4518 chi ∧
      ¬Fin15AnchoredAtom4519 chi ∧
      ¬Fin15AnchoredAtom4524 chi ∧
      ¬Fin15AnchoredAtom4530 chi ∧
      ¬Fin15AnchoredAtom4560 chi ∧
      ¬Fin15AnchoredAtom4791 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 4, 7, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13974
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2895 Fin15AnchoredAtom2896 Fin15AnchoredAtom2898
    Fin15AnchoredAtom2899 Fin15AnchoredAtom2907 Fin15AnchoredAtom2909 Fin15AnchoredAtom2910
    Fin15AnchoredAtom2913 Fin15AnchoredAtom2914 Fin15AnchoredAtom2919 Fin15AnchoredAtom2992
    Fin15AnchoredAtom2994 Fin15AnchoredAtom2995 Fin15AnchoredAtom2998 Fin15AnchoredAtom2999
    Fin15AnchoredAtom3004 Fin15AnchoredAtom3023 Fin15AnchoredAtom3024 Fin15AnchoredAtom3029
    Fin15AnchoredAtom3035 Fin15AnchoredAtom3277 Fin15AnchoredAtom3279 Fin15AnchoredAtom3280
    Fin15AnchoredAtom3283 Fin15AnchoredAtom3284 Fin15AnchoredAtom3289 Fin15AnchoredAtom3308
    Fin15AnchoredAtom3309 Fin15AnchoredAtom3314 Fin15AnchoredAtom3320 Fin15AnchoredAtom3483
    Fin15AnchoredAtom3484 Fin15AnchoredAtom3489 Fin15AnchoredAtom3495 Fin15AnchoredAtom3525
    Fin15AnchoredAtom3772 Fin15AnchoredAtom3774 Fin15AnchoredAtom3775 Fin15AnchoredAtom3778
    Fin15AnchoredAtom3779 Fin15AnchoredAtom3784 Fin15AnchoredAtom3803 Fin15AnchoredAtom3804
    Fin15AnchoredAtom3809 Fin15AnchoredAtom3815 Fin15AnchoredAtom3978 Fin15AnchoredAtom3979
    Fin15AnchoredAtom3984 Fin15AnchoredAtom3990 Fin15AnchoredAtom4020 Fin15AnchoredAtom4518
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

theorem fin15Anchored_clause31816 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2895 chi ∧
      ¬Fin15AnchoredAtom2896 chi ∧
      ¬Fin15AnchoredAtom2898 chi ∧
      ¬Fin15AnchoredAtom2900 chi ∧
      ¬Fin15AnchoredAtom2907 chi ∧
      ¬Fin15AnchoredAtom2909 chi ∧
      ¬Fin15AnchoredAtom2911 chi ∧
      ¬Fin15AnchoredAtom2913 chi ∧
      ¬Fin15AnchoredAtom2915 chi ∧
      ¬Fin15AnchoredAtom2920 chi ∧
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
      ¬Fin15AnchoredAtom4518 chi ∧
      ¬Fin15AnchoredAtom4520 chi ∧
      ¬Fin15AnchoredAtom4525 chi ∧
      ¬Fin15AnchoredAtom4531 chi ∧
      ¬Fin15AnchoredAtom4561 chi ∧
      ¬Fin15AnchoredAtom4792 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 4, 7, 9, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22166
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2895 Fin15AnchoredAtom2896 Fin15AnchoredAtom2898
    Fin15AnchoredAtom2900 Fin15AnchoredAtom2907 Fin15AnchoredAtom2909 Fin15AnchoredAtom2911
    Fin15AnchoredAtom2913 Fin15AnchoredAtom2915 Fin15AnchoredAtom2920 Fin15AnchoredAtom2992
    Fin15AnchoredAtom2994 Fin15AnchoredAtom2996 Fin15AnchoredAtom2998 Fin15AnchoredAtom3000
    Fin15AnchoredAtom3005 Fin15AnchoredAtom3023 Fin15AnchoredAtom3025 Fin15AnchoredAtom3030
    Fin15AnchoredAtom3036 Fin15AnchoredAtom3277 Fin15AnchoredAtom3279 Fin15AnchoredAtom3281
    Fin15AnchoredAtom3283 Fin15AnchoredAtom3285 Fin15AnchoredAtom3290 Fin15AnchoredAtom3308
    Fin15AnchoredAtom3310 Fin15AnchoredAtom3315 Fin15AnchoredAtom3321 Fin15AnchoredAtom3483
    Fin15AnchoredAtom3485 Fin15AnchoredAtom3490 Fin15AnchoredAtom3496 Fin15AnchoredAtom3526
    Fin15AnchoredAtom3772 Fin15AnchoredAtom3774 Fin15AnchoredAtom3776 Fin15AnchoredAtom3778
    Fin15AnchoredAtom3780 Fin15AnchoredAtom3785 Fin15AnchoredAtom3803 Fin15AnchoredAtom3805
    Fin15AnchoredAtom3810 Fin15AnchoredAtom3816 Fin15AnchoredAtom3978 Fin15AnchoredAtom3980
    Fin15AnchoredAtom3985 Fin15AnchoredAtom3991 Fin15AnchoredAtom4021 Fin15AnchoredAtom4518
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

theorem fin15Anchored_clause31817 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2895 chi ∧
      ¬Fin15AnchoredAtom2896 chi ∧
      ¬Fin15AnchoredAtom2899 chi ∧
      ¬Fin15AnchoredAtom2900 chi ∧
      ¬Fin15AnchoredAtom2907 chi ∧
      ¬Fin15AnchoredAtom2910 chi ∧
      ¬Fin15AnchoredAtom2911 chi ∧
      ¬Fin15AnchoredAtom2914 chi ∧
      ¬Fin15AnchoredAtom2915 chi ∧
      ¬Fin15AnchoredAtom2921 chi ∧
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
      ¬Fin15AnchoredAtom4519 chi ∧
      ¬Fin15AnchoredAtom4520 chi ∧
      ¬Fin15AnchoredAtom4526 chi ∧
      ¬Fin15AnchoredAtom4532 chi ∧
      ¬Fin15AnchoredAtom4562 chi ∧
      ¬Fin15AnchoredAtom4793 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 4, 7, 9, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26262
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2895 Fin15AnchoredAtom2896 Fin15AnchoredAtom2899
    Fin15AnchoredAtom2900 Fin15AnchoredAtom2907 Fin15AnchoredAtom2910 Fin15AnchoredAtom2911
    Fin15AnchoredAtom2914 Fin15AnchoredAtom2915 Fin15AnchoredAtom2921 Fin15AnchoredAtom2992
    Fin15AnchoredAtom2995 Fin15AnchoredAtom2996 Fin15AnchoredAtom2999 Fin15AnchoredAtom3000
    Fin15AnchoredAtom3006 Fin15AnchoredAtom3024 Fin15AnchoredAtom3025 Fin15AnchoredAtom3031
    Fin15AnchoredAtom3037 Fin15AnchoredAtom3277 Fin15AnchoredAtom3280 Fin15AnchoredAtom3281
    Fin15AnchoredAtom3284 Fin15AnchoredAtom3285 Fin15AnchoredAtom3291 Fin15AnchoredAtom3309
    Fin15AnchoredAtom3310 Fin15AnchoredAtom3316 Fin15AnchoredAtom3322 Fin15AnchoredAtom3484
    Fin15AnchoredAtom3485 Fin15AnchoredAtom3491 Fin15AnchoredAtom3497 Fin15AnchoredAtom3527
    Fin15AnchoredAtom3772 Fin15AnchoredAtom3775 Fin15AnchoredAtom3776 Fin15AnchoredAtom3779
    Fin15AnchoredAtom3780 Fin15AnchoredAtom3786 Fin15AnchoredAtom3804 Fin15AnchoredAtom3805
    Fin15AnchoredAtom3811 Fin15AnchoredAtom3817 Fin15AnchoredAtom3979 Fin15AnchoredAtom3980
    Fin15AnchoredAtom3986 Fin15AnchoredAtom3992 Fin15AnchoredAtom4022 Fin15AnchoredAtom4519
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

theorem fin15Anchored_clause31818 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2895 chi ∧
      ¬Fin15AnchoredAtom2898 chi ∧
      ¬Fin15AnchoredAtom2899 chi ∧
      ¬Fin15AnchoredAtom2900 chi ∧
      ¬Fin15AnchoredAtom2909 chi ∧
      ¬Fin15AnchoredAtom2910 chi ∧
      ¬Fin15AnchoredAtom2911 chi ∧
      ¬Fin15AnchoredAtom2919 chi ∧
      ¬Fin15AnchoredAtom2920 chi ∧
      ¬Fin15AnchoredAtom2921 chi ∧
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
      ¬Fin15AnchoredAtom4524 chi ∧
      ¬Fin15AnchoredAtom4525 chi ∧
      ¬Fin15AnchoredAtom4526 chi ∧
      ¬Fin15AnchoredAtom4536 chi ∧
      ¬Fin15AnchoredAtom4566 chi ∧
      ¬Fin15AnchoredAtom4797 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 4, 7, 9, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29334
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2895 Fin15AnchoredAtom2898 Fin15AnchoredAtom2899
    Fin15AnchoredAtom2900 Fin15AnchoredAtom2909 Fin15AnchoredAtom2910 Fin15AnchoredAtom2911
    Fin15AnchoredAtom2919 Fin15AnchoredAtom2920 Fin15AnchoredAtom2921 Fin15AnchoredAtom2994
    Fin15AnchoredAtom2995 Fin15AnchoredAtom2996 Fin15AnchoredAtom3004 Fin15AnchoredAtom3005
    Fin15AnchoredAtom3006 Fin15AnchoredAtom3029 Fin15AnchoredAtom3030 Fin15AnchoredAtom3031
    Fin15AnchoredAtom3041 Fin15AnchoredAtom3279 Fin15AnchoredAtom3280 Fin15AnchoredAtom3281
    Fin15AnchoredAtom3289 Fin15AnchoredAtom3290 Fin15AnchoredAtom3291 Fin15AnchoredAtom3314
    Fin15AnchoredAtom3315 Fin15AnchoredAtom3316 Fin15AnchoredAtom3326 Fin15AnchoredAtom3489
    Fin15AnchoredAtom3490 Fin15AnchoredAtom3491 Fin15AnchoredAtom3501 Fin15AnchoredAtom3531
    Fin15AnchoredAtom3774 Fin15AnchoredAtom3775 Fin15AnchoredAtom3776 Fin15AnchoredAtom3784
    Fin15AnchoredAtom3785 Fin15AnchoredAtom3786 Fin15AnchoredAtom3809 Fin15AnchoredAtom3810
    Fin15AnchoredAtom3811 Fin15AnchoredAtom3821 Fin15AnchoredAtom3984 Fin15AnchoredAtom3985
    Fin15AnchoredAtom3986 Fin15AnchoredAtom3996 Fin15AnchoredAtom4026 Fin15AnchoredAtom4524
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

theorem fin15Anchored_clause31819 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2896 chi ∧
      ¬Fin15AnchoredAtom2898 chi ∧
      ¬Fin15AnchoredAtom2899 chi ∧
      ¬Fin15AnchoredAtom2900 chi ∧
      ¬Fin15AnchoredAtom2913 chi ∧
      ¬Fin15AnchoredAtom2914 chi ∧
      ¬Fin15AnchoredAtom2915 chi ∧
      ¬Fin15AnchoredAtom2919 chi ∧
      ¬Fin15AnchoredAtom2920 chi ∧
      ¬Fin15AnchoredAtom2921 chi ∧
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
      ¬Fin15AnchoredAtom4530 chi ∧
      ¬Fin15AnchoredAtom4531 chi ∧
      ¬Fin15AnchoredAtom4532 chi ∧
      ¬Fin15AnchoredAtom4536 chi ∧
      ¬Fin15AnchoredAtom4570 chi ∧
      ¬Fin15AnchoredAtom4801 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 4, 7, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29846
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2896 Fin15AnchoredAtom2898 Fin15AnchoredAtom2899
    Fin15AnchoredAtom2900 Fin15AnchoredAtom2913 Fin15AnchoredAtom2914 Fin15AnchoredAtom2915
    Fin15AnchoredAtom2919 Fin15AnchoredAtom2920 Fin15AnchoredAtom2921 Fin15AnchoredAtom2998
    Fin15AnchoredAtom2999 Fin15AnchoredAtom3000 Fin15AnchoredAtom3004 Fin15AnchoredAtom3005
    Fin15AnchoredAtom3006 Fin15AnchoredAtom3035 Fin15AnchoredAtom3036 Fin15AnchoredAtom3037
    Fin15AnchoredAtom3041 Fin15AnchoredAtom3283 Fin15AnchoredAtom3284 Fin15AnchoredAtom3285
    Fin15AnchoredAtom3289 Fin15AnchoredAtom3290 Fin15AnchoredAtom3291 Fin15AnchoredAtom3320
    Fin15AnchoredAtom3321 Fin15AnchoredAtom3322 Fin15AnchoredAtom3326 Fin15AnchoredAtom3495
    Fin15AnchoredAtom3496 Fin15AnchoredAtom3497 Fin15AnchoredAtom3501 Fin15AnchoredAtom3535
    Fin15AnchoredAtom3778 Fin15AnchoredAtom3779 Fin15AnchoredAtom3780 Fin15AnchoredAtom3784
    Fin15AnchoredAtom3785 Fin15AnchoredAtom3786 Fin15AnchoredAtom3815 Fin15AnchoredAtom3816
    Fin15AnchoredAtom3817 Fin15AnchoredAtom3821 Fin15AnchoredAtom3990 Fin15AnchoredAtom3991
    Fin15AnchoredAtom3992 Fin15AnchoredAtom3996 Fin15AnchoredAtom4030 Fin15AnchoredAtom4530
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

theorem fin15Anchored_clause31820 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2907 chi ∧
      ¬Fin15AnchoredAtom2909 chi ∧
      ¬Fin15AnchoredAtom2910 chi ∧
      ¬Fin15AnchoredAtom2911 chi ∧
      ¬Fin15AnchoredAtom2913 chi ∧
      ¬Fin15AnchoredAtom2914 chi ∧
      ¬Fin15AnchoredAtom2915 chi ∧
      ¬Fin15AnchoredAtom2919 chi ∧
      ¬Fin15AnchoredAtom2920 chi ∧
      ¬Fin15AnchoredAtom2921 chi ∧
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
      ¬Fin15AnchoredAtom4560 chi ∧
      ¬Fin15AnchoredAtom4561 chi ∧
      ¬Fin15AnchoredAtom4562 chi ∧
      ¬Fin15AnchoredAtom4566 chi ∧
      ¬Fin15AnchoredAtom4570 chi ∧
      ¬Fin15AnchoredAtom4821 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 4, 9, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask30230
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2907 Fin15AnchoredAtom2909 Fin15AnchoredAtom2910
    Fin15AnchoredAtom2911 Fin15AnchoredAtom2913 Fin15AnchoredAtom2914 Fin15AnchoredAtom2915
    Fin15AnchoredAtom2919 Fin15AnchoredAtom2920 Fin15AnchoredAtom2921 Fin15AnchoredAtom3023
    Fin15AnchoredAtom3024 Fin15AnchoredAtom3025 Fin15AnchoredAtom3029 Fin15AnchoredAtom3030
    Fin15AnchoredAtom3031 Fin15AnchoredAtom3035 Fin15AnchoredAtom3036 Fin15AnchoredAtom3037
    Fin15AnchoredAtom3041 Fin15AnchoredAtom3308 Fin15AnchoredAtom3309 Fin15AnchoredAtom3310
    Fin15AnchoredAtom3314 Fin15AnchoredAtom3315 Fin15AnchoredAtom3316 Fin15AnchoredAtom3320
    Fin15AnchoredAtom3321 Fin15AnchoredAtom3322 Fin15AnchoredAtom3326 Fin15AnchoredAtom3525
    Fin15AnchoredAtom3526 Fin15AnchoredAtom3527 Fin15AnchoredAtom3531 Fin15AnchoredAtom3535
    Fin15AnchoredAtom3803 Fin15AnchoredAtom3804 Fin15AnchoredAtom3805 Fin15AnchoredAtom3809
    Fin15AnchoredAtom3810 Fin15AnchoredAtom3811 Fin15AnchoredAtom3815 Fin15AnchoredAtom3816
    Fin15AnchoredAtom3817 Fin15AnchoredAtom3821 Fin15AnchoredAtom4020 Fin15AnchoredAtom4021
    Fin15AnchoredAtom4022 Fin15AnchoredAtom4026 Fin15AnchoredAtom4030 Fin15AnchoredAtom4560
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

theorem fin15Anchored_clause31821 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2922 chi ∧
      ¬Fin15AnchoredAtom2924 chi ∧
      ¬Fin15AnchoredAtom2925 chi ∧
      ¬Fin15AnchoredAtom2927 chi ∧
      ¬Fin15AnchoredAtom2931 chi ∧
      ¬Fin15AnchoredAtom2932 chi ∧
      ¬Fin15AnchoredAtom2934 chi ∧
      ¬Fin15AnchoredAtom2943 chi ∧
      ¬Fin15AnchoredAtom2945 chi ∧
      ¬Fin15AnchoredAtom2949 chi ∧
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
      ¬Fin15AnchoredAtom4578 chi ∧
      ¬Fin15AnchoredAtom4580 chi ∧
      ¬Fin15AnchoredAtom4584 chi ∧
      ¬Fin15AnchoredAtom4609 chi ∧
      ¬Fin15AnchoredAtom4644 chi ∧
      ¬Fin15AnchoredAtom4714 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 5, 6, 7, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05862
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2922 Fin15AnchoredAtom2924 Fin15AnchoredAtom2925
    Fin15AnchoredAtom2927 Fin15AnchoredAtom2931 Fin15AnchoredAtom2932 Fin15AnchoredAtom2934
    Fin15AnchoredAtom2943 Fin15AnchoredAtom2945 Fin15AnchoredAtom2949 Fin15AnchoredAtom2959
    Fin15AnchoredAtom2960 Fin15AnchoredAtom2962 Fin15AnchoredAtom2971 Fin15AnchoredAtom2973
    Fin15AnchoredAtom2977 Fin15AnchoredAtom2992 Fin15AnchoredAtom2994 Fin15AnchoredAtom2998
    Fin15AnchoredAtom3023 Fin15AnchoredAtom3328 Fin15AnchoredAtom3329 Fin15AnchoredAtom3331
    Fin15AnchoredAtom3340 Fin15AnchoredAtom3342 Fin15AnchoredAtom3346 Fin15AnchoredAtom3361
    Fin15AnchoredAtom3363 Fin15AnchoredAtom3367 Fin15AnchoredAtom3392 Fin15AnchoredAtom3417
    Fin15AnchoredAtom3419 Fin15AnchoredAtom3423 Fin15AnchoredAtom3448 Fin15AnchoredAtom3483
    Fin15AnchoredAtom3823 Fin15AnchoredAtom3824 Fin15AnchoredAtom3826 Fin15AnchoredAtom3835
    Fin15AnchoredAtom3837 Fin15AnchoredAtom3841 Fin15AnchoredAtom3856 Fin15AnchoredAtom3858
    Fin15AnchoredAtom3862 Fin15AnchoredAtom3887 Fin15AnchoredAtom3912 Fin15AnchoredAtom3914
    Fin15AnchoredAtom3918 Fin15AnchoredAtom3943 Fin15AnchoredAtom3978 Fin15AnchoredAtom4578
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

theorem fin15Anchored_clause31822 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2922 chi ∧
      ¬Fin15AnchoredAtom2924 chi ∧
      ¬Fin15AnchoredAtom2925 chi ∧
      ¬Fin15AnchoredAtom2928 chi ∧
      ¬Fin15AnchoredAtom2931 chi ∧
      ¬Fin15AnchoredAtom2932 chi ∧
      ¬Fin15AnchoredAtom2935 chi ∧
      ¬Fin15AnchoredAtom2943 chi ∧
      ¬Fin15AnchoredAtom2946 chi ∧
      ¬Fin15AnchoredAtom2950 chi ∧
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
      ¬Fin15AnchoredAtom4578 chi ∧
      ¬Fin15AnchoredAtom4581 chi ∧
      ¬Fin15AnchoredAtom4585 chi ∧
      ¬Fin15AnchoredAtom4610 chi ∧
      ¬Fin15AnchoredAtom4645 chi ∧
      ¬Fin15AnchoredAtom4715 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 5, 6, 7, 9, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09958
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2922 Fin15AnchoredAtom2924 Fin15AnchoredAtom2925
    Fin15AnchoredAtom2928 Fin15AnchoredAtom2931 Fin15AnchoredAtom2932 Fin15AnchoredAtom2935
    Fin15AnchoredAtom2943 Fin15AnchoredAtom2946 Fin15AnchoredAtom2950 Fin15AnchoredAtom2959
    Fin15AnchoredAtom2960 Fin15AnchoredAtom2963 Fin15AnchoredAtom2971 Fin15AnchoredAtom2974
    Fin15AnchoredAtom2978 Fin15AnchoredAtom2992 Fin15AnchoredAtom2995 Fin15AnchoredAtom2999
    Fin15AnchoredAtom3024 Fin15AnchoredAtom3328 Fin15AnchoredAtom3329 Fin15AnchoredAtom3332
    Fin15AnchoredAtom3340 Fin15AnchoredAtom3343 Fin15AnchoredAtom3347 Fin15AnchoredAtom3361
    Fin15AnchoredAtom3364 Fin15AnchoredAtom3368 Fin15AnchoredAtom3393 Fin15AnchoredAtom3417
    Fin15AnchoredAtom3420 Fin15AnchoredAtom3424 Fin15AnchoredAtom3449 Fin15AnchoredAtom3484
    Fin15AnchoredAtom3823 Fin15AnchoredAtom3824 Fin15AnchoredAtom3827 Fin15AnchoredAtom3835
    Fin15AnchoredAtom3838 Fin15AnchoredAtom3842 Fin15AnchoredAtom3856 Fin15AnchoredAtom3859
    Fin15AnchoredAtom3863 Fin15AnchoredAtom3888 Fin15AnchoredAtom3912 Fin15AnchoredAtom3915
    Fin15AnchoredAtom3919 Fin15AnchoredAtom3944 Fin15AnchoredAtom3979 Fin15AnchoredAtom4578
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

theorem fin15Anchored_clause31823 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2922 chi ∧
      ¬Fin15AnchoredAtom2924 chi ∧
      ¬Fin15AnchoredAtom2925 chi ∧
      ¬Fin15AnchoredAtom2929 chi ∧
      ¬Fin15AnchoredAtom2931 chi ∧
      ¬Fin15AnchoredAtom2932 chi ∧
      ¬Fin15AnchoredAtom2936 chi ∧
      ¬Fin15AnchoredAtom2943 chi ∧
      ¬Fin15AnchoredAtom2947 chi ∧
      ¬Fin15AnchoredAtom2951 chi ∧
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
      ¬Fin15AnchoredAtom4578 chi ∧
      ¬Fin15AnchoredAtom4582 chi ∧
      ¬Fin15AnchoredAtom4586 chi ∧
      ¬Fin15AnchoredAtom4611 chi ∧
      ¬Fin15AnchoredAtom4646 chi ∧
      ¬Fin15AnchoredAtom4716 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 5, 6, 7, 9, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask18150
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2922 Fin15AnchoredAtom2924 Fin15AnchoredAtom2925
    Fin15AnchoredAtom2929 Fin15AnchoredAtom2931 Fin15AnchoredAtom2932 Fin15AnchoredAtom2936
    Fin15AnchoredAtom2943 Fin15AnchoredAtom2947 Fin15AnchoredAtom2951 Fin15AnchoredAtom2959
    Fin15AnchoredAtom2960 Fin15AnchoredAtom2964 Fin15AnchoredAtom2971 Fin15AnchoredAtom2975
    Fin15AnchoredAtom2979 Fin15AnchoredAtom2992 Fin15AnchoredAtom2996 Fin15AnchoredAtom3000
    Fin15AnchoredAtom3025 Fin15AnchoredAtom3328 Fin15AnchoredAtom3329 Fin15AnchoredAtom3333
    Fin15AnchoredAtom3340 Fin15AnchoredAtom3344 Fin15AnchoredAtom3348 Fin15AnchoredAtom3361
    Fin15AnchoredAtom3365 Fin15AnchoredAtom3369 Fin15AnchoredAtom3394 Fin15AnchoredAtom3417
    Fin15AnchoredAtom3421 Fin15AnchoredAtom3425 Fin15AnchoredAtom3450 Fin15AnchoredAtom3485
    Fin15AnchoredAtom3823 Fin15AnchoredAtom3824 Fin15AnchoredAtom3828 Fin15AnchoredAtom3835
    Fin15AnchoredAtom3839 Fin15AnchoredAtom3843 Fin15AnchoredAtom3856 Fin15AnchoredAtom3860
    Fin15AnchoredAtom3864 Fin15AnchoredAtom3889 Fin15AnchoredAtom3912 Fin15AnchoredAtom3916
    Fin15AnchoredAtom3920 Fin15AnchoredAtom3945 Fin15AnchoredAtom3980 Fin15AnchoredAtom4578
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

theorem fin15Anchored_clause31824 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2922 chi ∧
      ¬Fin15AnchoredAtom2924 chi ∧
      ¬Fin15AnchoredAtom2927 chi ∧
      ¬Fin15AnchoredAtom2928 chi ∧
      ¬Fin15AnchoredAtom2931 chi ∧
      ¬Fin15AnchoredAtom2934 chi ∧
      ¬Fin15AnchoredAtom2935 chi ∧
      ¬Fin15AnchoredAtom2945 chi ∧
      ¬Fin15AnchoredAtom2946 chi ∧
      ¬Fin15AnchoredAtom2955 chi ∧
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
      ¬Fin15AnchoredAtom4580 chi ∧
      ¬Fin15AnchoredAtom4581 chi ∧
      ¬Fin15AnchoredAtom4590 chi ∧
      ¬Fin15AnchoredAtom4615 chi ∧
      ¬Fin15AnchoredAtom4650 chi ∧
      ¬Fin15AnchoredAtom4720 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 5, 6, 7, 9, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13030
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2922 Fin15AnchoredAtom2924 Fin15AnchoredAtom2927
    Fin15AnchoredAtom2928 Fin15AnchoredAtom2931 Fin15AnchoredAtom2934 Fin15AnchoredAtom2935
    Fin15AnchoredAtom2945 Fin15AnchoredAtom2946 Fin15AnchoredAtom2955 Fin15AnchoredAtom2959
    Fin15AnchoredAtom2962 Fin15AnchoredAtom2963 Fin15AnchoredAtom2973 Fin15AnchoredAtom2974
    Fin15AnchoredAtom2983 Fin15AnchoredAtom2994 Fin15AnchoredAtom2995 Fin15AnchoredAtom3004
    Fin15AnchoredAtom3029 Fin15AnchoredAtom3328 Fin15AnchoredAtom3331 Fin15AnchoredAtom3332
    Fin15AnchoredAtom3342 Fin15AnchoredAtom3343 Fin15AnchoredAtom3352 Fin15AnchoredAtom3363
    Fin15AnchoredAtom3364 Fin15AnchoredAtom3373 Fin15AnchoredAtom3398 Fin15AnchoredAtom3419
    Fin15AnchoredAtom3420 Fin15AnchoredAtom3429 Fin15AnchoredAtom3454 Fin15AnchoredAtom3489
    Fin15AnchoredAtom3823 Fin15AnchoredAtom3826 Fin15AnchoredAtom3827 Fin15AnchoredAtom3837
    Fin15AnchoredAtom3838 Fin15AnchoredAtom3847 Fin15AnchoredAtom3858 Fin15AnchoredAtom3859
    Fin15AnchoredAtom3868 Fin15AnchoredAtom3893 Fin15AnchoredAtom3914 Fin15AnchoredAtom3915
    Fin15AnchoredAtom3924 Fin15AnchoredAtom3949 Fin15AnchoredAtom3984 Fin15AnchoredAtom4580
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

theorem fin15Anchored_clause31825 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2922 chi ∧
      ¬Fin15AnchoredAtom2924 chi ∧
      ¬Fin15AnchoredAtom2927 chi ∧
      ¬Fin15AnchoredAtom2929 chi ∧
      ¬Fin15AnchoredAtom2931 chi ∧
      ¬Fin15AnchoredAtom2934 chi ∧
      ¬Fin15AnchoredAtom2936 chi ∧
      ¬Fin15AnchoredAtom2945 chi ∧
      ¬Fin15AnchoredAtom2947 chi ∧
      ¬Fin15AnchoredAtom2956 chi ∧
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
      ¬Fin15AnchoredAtom4580 chi ∧
      ¬Fin15AnchoredAtom4582 chi ∧
      ¬Fin15AnchoredAtom4591 chi ∧
      ¬Fin15AnchoredAtom4616 chi ∧
      ¬Fin15AnchoredAtom4651 chi ∧
      ¬Fin15AnchoredAtom4721 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 5, 6, 7, 9, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21222
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2922 Fin15AnchoredAtom2924 Fin15AnchoredAtom2927
    Fin15AnchoredAtom2929 Fin15AnchoredAtom2931 Fin15AnchoredAtom2934 Fin15AnchoredAtom2936
    Fin15AnchoredAtom2945 Fin15AnchoredAtom2947 Fin15AnchoredAtom2956 Fin15AnchoredAtom2959
    Fin15AnchoredAtom2962 Fin15AnchoredAtom2964 Fin15AnchoredAtom2973 Fin15AnchoredAtom2975
    Fin15AnchoredAtom2984 Fin15AnchoredAtom2994 Fin15AnchoredAtom2996 Fin15AnchoredAtom3005
    Fin15AnchoredAtom3030 Fin15AnchoredAtom3328 Fin15AnchoredAtom3331 Fin15AnchoredAtom3333
    Fin15AnchoredAtom3342 Fin15AnchoredAtom3344 Fin15AnchoredAtom3353 Fin15AnchoredAtom3363
    Fin15AnchoredAtom3365 Fin15AnchoredAtom3374 Fin15AnchoredAtom3399 Fin15AnchoredAtom3419
    Fin15AnchoredAtom3421 Fin15AnchoredAtom3430 Fin15AnchoredAtom3455 Fin15AnchoredAtom3490
    Fin15AnchoredAtom3823 Fin15AnchoredAtom3826 Fin15AnchoredAtom3828 Fin15AnchoredAtom3837
    Fin15AnchoredAtom3839 Fin15AnchoredAtom3848 Fin15AnchoredAtom3858 Fin15AnchoredAtom3860
    Fin15AnchoredAtom3869 Fin15AnchoredAtom3894 Fin15AnchoredAtom3914 Fin15AnchoredAtom3916
    Fin15AnchoredAtom3925 Fin15AnchoredAtom3950 Fin15AnchoredAtom3985 Fin15AnchoredAtom4580
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

theorem fin15Anchored_clause31826 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2922 chi ∧
      ¬Fin15AnchoredAtom2924 chi ∧
      ¬Fin15AnchoredAtom2928 chi ∧
      ¬Fin15AnchoredAtom2929 chi ∧
      ¬Fin15AnchoredAtom2931 chi ∧
      ¬Fin15AnchoredAtom2935 chi ∧
      ¬Fin15AnchoredAtom2936 chi ∧
      ¬Fin15AnchoredAtom2946 chi ∧
      ¬Fin15AnchoredAtom2947 chi ∧
      ¬Fin15AnchoredAtom2957 chi ∧
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
      ¬Fin15AnchoredAtom4581 chi ∧
      ¬Fin15AnchoredAtom4582 chi ∧
      ¬Fin15AnchoredAtom4592 chi ∧
      ¬Fin15AnchoredAtom4617 chi ∧
      ¬Fin15AnchoredAtom4652 chi ∧
      ¬Fin15AnchoredAtom4722 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 5, 6, 7, 9, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25318
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2922 Fin15AnchoredAtom2924 Fin15AnchoredAtom2928
    Fin15AnchoredAtom2929 Fin15AnchoredAtom2931 Fin15AnchoredAtom2935 Fin15AnchoredAtom2936
    Fin15AnchoredAtom2946 Fin15AnchoredAtom2947 Fin15AnchoredAtom2957 Fin15AnchoredAtom2959
    Fin15AnchoredAtom2963 Fin15AnchoredAtom2964 Fin15AnchoredAtom2974 Fin15AnchoredAtom2975
    Fin15AnchoredAtom2985 Fin15AnchoredAtom2995 Fin15AnchoredAtom2996 Fin15AnchoredAtom3006
    Fin15AnchoredAtom3031 Fin15AnchoredAtom3328 Fin15AnchoredAtom3332 Fin15AnchoredAtom3333
    Fin15AnchoredAtom3343 Fin15AnchoredAtom3344 Fin15AnchoredAtom3354 Fin15AnchoredAtom3364
    Fin15AnchoredAtom3365 Fin15AnchoredAtom3375 Fin15AnchoredAtom3400 Fin15AnchoredAtom3420
    Fin15AnchoredAtom3421 Fin15AnchoredAtom3431 Fin15AnchoredAtom3456 Fin15AnchoredAtom3491
    Fin15AnchoredAtom3823 Fin15AnchoredAtom3827 Fin15AnchoredAtom3828 Fin15AnchoredAtom3838
    Fin15AnchoredAtom3839 Fin15AnchoredAtom3849 Fin15AnchoredAtom3859 Fin15AnchoredAtom3860
    Fin15AnchoredAtom3870 Fin15AnchoredAtom3895 Fin15AnchoredAtom3915 Fin15AnchoredAtom3916
    Fin15AnchoredAtom3926 Fin15AnchoredAtom3951 Fin15AnchoredAtom3986 Fin15AnchoredAtom4581
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

theorem fin15Anchored_clause31827 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2922 chi ∧
      ¬Fin15AnchoredAtom2925 chi ∧
      ¬Fin15AnchoredAtom2927 chi ∧
      ¬Fin15AnchoredAtom2928 chi ∧
      ¬Fin15AnchoredAtom2932 chi ∧
      ¬Fin15AnchoredAtom2934 chi ∧
      ¬Fin15AnchoredAtom2935 chi ∧
      ¬Fin15AnchoredAtom2949 chi ∧
      ¬Fin15AnchoredAtom2950 chi ∧
      ¬Fin15AnchoredAtom2955 chi ∧
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
      ¬Fin15AnchoredAtom4584 chi ∧
      ¬Fin15AnchoredAtom4585 chi ∧
      ¬Fin15AnchoredAtom4590 chi ∧
      ¬Fin15AnchoredAtom4621 chi ∧
      ¬Fin15AnchoredAtom4656 chi ∧
      ¬Fin15AnchoredAtom4726 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 5, 6, 7, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13542
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2922 Fin15AnchoredAtom2925 Fin15AnchoredAtom2927
    Fin15AnchoredAtom2928 Fin15AnchoredAtom2932 Fin15AnchoredAtom2934 Fin15AnchoredAtom2935
    Fin15AnchoredAtom2949 Fin15AnchoredAtom2950 Fin15AnchoredAtom2955 Fin15AnchoredAtom2960
    Fin15AnchoredAtom2962 Fin15AnchoredAtom2963 Fin15AnchoredAtom2977 Fin15AnchoredAtom2978
    Fin15AnchoredAtom2983 Fin15AnchoredAtom2998 Fin15AnchoredAtom2999 Fin15AnchoredAtom3004
    Fin15AnchoredAtom3035 Fin15AnchoredAtom3329 Fin15AnchoredAtom3331 Fin15AnchoredAtom3332
    Fin15AnchoredAtom3346 Fin15AnchoredAtom3347 Fin15AnchoredAtom3352 Fin15AnchoredAtom3367
    Fin15AnchoredAtom3368 Fin15AnchoredAtom3373 Fin15AnchoredAtom3404 Fin15AnchoredAtom3423
    Fin15AnchoredAtom3424 Fin15AnchoredAtom3429 Fin15AnchoredAtom3460 Fin15AnchoredAtom3495
    Fin15AnchoredAtom3824 Fin15AnchoredAtom3826 Fin15AnchoredAtom3827 Fin15AnchoredAtom3841
    Fin15AnchoredAtom3842 Fin15AnchoredAtom3847 Fin15AnchoredAtom3862 Fin15AnchoredAtom3863
    Fin15AnchoredAtom3868 Fin15AnchoredAtom3899 Fin15AnchoredAtom3918 Fin15AnchoredAtom3919
    Fin15AnchoredAtom3924 Fin15AnchoredAtom3955 Fin15AnchoredAtom3990 Fin15AnchoredAtom4584
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

theorem fin15Anchored_clause31828 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2922 chi ∧
      ¬Fin15AnchoredAtom2925 chi ∧
      ¬Fin15AnchoredAtom2927 chi ∧
      ¬Fin15AnchoredAtom2929 chi ∧
      ¬Fin15AnchoredAtom2932 chi ∧
      ¬Fin15AnchoredAtom2934 chi ∧
      ¬Fin15AnchoredAtom2936 chi ∧
      ¬Fin15AnchoredAtom2949 chi ∧
      ¬Fin15AnchoredAtom2951 chi ∧
      ¬Fin15AnchoredAtom2956 chi ∧
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
      ¬Fin15AnchoredAtom4584 chi ∧
      ¬Fin15AnchoredAtom4586 chi ∧
      ¬Fin15AnchoredAtom4591 chi ∧
      ¬Fin15AnchoredAtom4622 chi ∧
      ¬Fin15AnchoredAtom4657 chi ∧
      ¬Fin15AnchoredAtom4727 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 5, 6, 7, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21734
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2922 Fin15AnchoredAtom2925 Fin15AnchoredAtom2927
    Fin15AnchoredAtom2929 Fin15AnchoredAtom2932 Fin15AnchoredAtom2934 Fin15AnchoredAtom2936
    Fin15AnchoredAtom2949 Fin15AnchoredAtom2951 Fin15AnchoredAtom2956 Fin15AnchoredAtom2960
    Fin15AnchoredAtom2962 Fin15AnchoredAtom2964 Fin15AnchoredAtom2977 Fin15AnchoredAtom2979
    Fin15AnchoredAtom2984 Fin15AnchoredAtom2998 Fin15AnchoredAtom3000 Fin15AnchoredAtom3005
    Fin15AnchoredAtom3036 Fin15AnchoredAtom3329 Fin15AnchoredAtom3331 Fin15AnchoredAtom3333
    Fin15AnchoredAtom3346 Fin15AnchoredAtom3348 Fin15AnchoredAtom3353 Fin15AnchoredAtom3367
    Fin15AnchoredAtom3369 Fin15AnchoredAtom3374 Fin15AnchoredAtom3405 Fin15AnchoredAtom3423
    Fin15AnchoredAtom3425 Fin15AnchoredAtom3430 Fin15AnchoredAtom3461 Fin15AnchoredAtom3496
    Fin15AnchoredAtom3824 Fin15AnchoredAtom3826 Fin15AnchoredAtom3828 Fin15AnchoredAtom3841
    Fin15AnchoredAtom3843 Fin15AnchoredAtom3848 Fin15AnchoredAtom3862 Fin15AnchoredAtom3864
    Fin15AnchoredAtom3869 Fin15AnchoredAtom3900 Fin15AnchoredAtom3918 Fin15AnchoredAtom3920
    Fin15AnchoredAtom3925 Fin15AnchoredAtom3956 Fin15AnchoredAtom3991 Fin15AnchoredAtom4584
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

theorem fin15Anchored_clause31829 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2922 chi ∧
      ¬Fin15AnchoredAtom2925 chi ∧
      ¬Fin15AnchoredAtom2928 chi ∧
      ¬Fin15AnchoredAtom2929 chi ∧
      ¬Fin15AnchoredAtom2932 chi ∧
      ¬Fin15AnchoredAtom2935 chi ∧
      ¬Fin15AnchoredAtom2936 chi ∧
      ¬Fin15AnchoredAtom2950 chi ∧
      ¬Fin15AnchoredAtom2951 chi ∧
      ¬Fin15AnchoredAtom2957 chi ∧
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
      ¬Fin15AnchoredAtom4585 chi ∧
      ¬Fin15AnchoredAtom4586 chi ∧
      ¬Fin15AnchoredAtom4592 chi ∧
      ¬Fin15AnchoredAtom4623 chi ∧
      ¬Fin15AnchoredAtom4658 chi ∧
      ¬Fin15AnchoredAtom4728 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 5, 6, 7, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25830
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2922 Fin15AnchoredAtom2925 Fin15AnchoredAtom2928
    Fin15AnchoredAtom2929 Fin15AnchoredAtom2932 Fin15AnchoredAtom2935 Fin15AnchoredAtom2936
    Fin15AnchoredAtom2950 Fin15AnchoredAtom2951 Fin15AnchoredAtom2957 Fin15AnchoredAtom2960
    Fin15AnchoredAtom2963 Fin15AnchoredAtom2964 Fin15AnchoredAtom2978 Fin15AnchoredAtom2979
    Fin15AnchoredAtom2985 Fin15AnchoredAtom2999 Fin15AnchoredAtom3000 Fin15AnchoredAtom3006
    Fin15AnchoredAtom3037 Fin15AnchoredAtom3329 Fin15AnchoredAtom3332 Fin15AnchoredAtom3333
    Fin15AnchoredAtom3347 Fin15AnchoredAtom3348 Fin15AnchoredAtom3354 Fin15AnchoredAtom3368
    Fin15AnchoredAtom3369 Fin15AnchoredAtom3375 Fin15AnchoredAtom3406 Fin15AnchoredAtom3424
    Fin15AnchoredAtom3425 Fin15AnchoredAtom3431 Fin15AnchoredAtom3462 Fin15AnchoredAtom3497
    Fin15AnchoredAtom3824 Fin15AnchoredAtom3827 Fin15AnchoredAtom3828 Fin15AnchoredAtom3842
    Fin15AnchoredAtom3843 Fin15AnchoredAtom3849 Fin15AnchoredAtom3863 Fin15AnchoredAtom3864
    Fin15AnchoredAtom3870 Fin15AnchoredAtom3901 Fin15AnchoredAtom3919 Fin15AnchoredAtom3920
    Fin15AnchoredAtom3926 Fin15AnchoredAtom3957 Fin15AnchoredAtom3992 Fin15AnchoredAtom4585
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

theorem fin15Anchored_clause31830 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2922 chi ∧
      ¬Fin15AnchoredAtom2927 chi ∧
      ¬Fin15AnchoredAtom2928 chi ∧
      ¬Fin15AnchoredAtom2929 chi ∧
      ¬Fin15AnchoredAtom2934 chi ∧
      ¬Fin15AnchoredAtom2935 chi ∧
      ¬Fin15AnchoredAtom2936 chi ∧
      ¬Fin15AnchoredAtom2955 chi ∧
      ¬Fin15AnchoredAtom2956 chi ∧
      ¬Fin15AnchoredAtom2957 chi ∧
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
      ¬Fin15AnchoredAtom4590 chi ∧
      ¬Fin15AnchoredAtom4591 chi ∧
      ¬Fin15AnchoredAtom4592 chi ∧
      ¬Fin15AnchoredAtom4627 chi ∧
      ¬Fin15AnchoredAtom4662 chi ∧
      ¬Fin15AnchoredAtom4732 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 5, 6, 7, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask28902
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2922 Fin15AnchoredAtom2927 Fin15AnchoredAtom2928
    Fin15AnchoredAtom2929 Fin15AnchoredAtom2934 Fin15AnchoredAtom2935 Fin15AnchoredAtom2936
    Fin15AnchoredAtom2955 Fin15AnchoredAtom2956 Fin15AnchoredAtom2957 Fin15AnchoredAtom2962
    Fin15AnchoredAtom2963 Fin15AnchoredAtom2964 Fin15AnchoredAtom2983 Fin15AnchoredAtom2984
    Fin15AnchoredAtom2985 Fin15AnchoredAtom3004 Fin15AnchoredAtom3005 Fin15AnchoredAtom3006
    Fin15AnchoredAtom3041 Fin15AnchoredAtom3331 Fin15AnchoredAtom3332 Fin15AnchoredAtom3333
    Fin15AnchoredAtom3352 Fin15AnchoredAtom3353 Fin15AnchoredAtom3354 Fin15AnchoredAtom3373
    Fin15AnchoredAtom3374 Fin15AnchoredAtom3375 Fin15AnchoredAtom3410 Fin15AnchoredAtom3429
    Fin15AnchoredAtom3430 Fin15AnchoredAtom3431 Fin15AnchoredAtom3466 Fin15AnchoredAtom3501
    Fin15AnchoredAtom3826 Fin15AnchoredAtom3827 Fin15AnchoredAtom3828 Fin15AnchoredAtom3847
    Fin15AnchoredAtom3848 Fin15AnchoredAtom3849 Fin15AnchoredAtom3868 Fin15AnchoredAtom3869
    Fin15AnchoredAtom3870 Fin15AnchoredAtom3905 Fin15AnchoredAtom3924 Fin15AnchoredAtom3925
    Fin15AnchoredAtom3926 Fin15AnchoredAtom3961 Fin15AnchoredAtom3996 Fin15AnchoredAtom4590
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

theorem fin15Anchored_clause31831 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2924 chi ∧
      ¬Fin15AnchoredAtom2925 chi ∧
      ¬Fin15AnchoredAtom2927 chi ∧
      ¬Fin15AnchoredAtom2928 chi ∧
      ¬Fin15AnchoredAtom2943 chi ∧
      ¬Fin15AnchoredAtom2945 chi ∧
      ¬Fin15AnchoredAtom2946 chi ∧
      ¬Fin15AnchoredAtom2949 chi ∧
      ¬Fin15AnchoredAtom2950 chi ∧
      ¬Fin15AnchoredAtom2955 chi ∧
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
      ¬Fin15AnchoredAtom4609 chi ∧
      ¬Fin15AnchoredAtom4610 chi ∧
      ¬Fin15AnchoredAtom4615 chi ∧
      ¬Fin15AnchoredAtom4621 chi ∧
      ¬Fin15AnchoredAtom4686 chi ∧
      ¬Fin15AnchoredAtom4756 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 5, 6, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13926
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2924 Fin15AnchoredAtom2925 Fin15AnchoredAtom2927
    Fin15AnchoredAtom2928 Fin15AnchoredAtom2943 Fin15AnchoredAtom2945 Fin15AnchoredAtom2946
    Fin15AnchoredAtom2949 Fin15AnchoredAtom2950 Fin15AnchoredAtom2955 Fin15AnchoredAtom2971
    Fin15AnchoredAtom2973 Fin15AnchoredAtom2974 Fin15AnchoredAtom2977 Fin15AnchoredAtom2978
    Fin15AnchoredAtom2983 Fin15AnchoredAtom3023 Fin15AnchoredAtom3024 Fin15AnchoredAtom3029
    Fin15AnchoredAtom3035 Fin15AnchoredAtom3340 Fin15AnchoredAtom3342 Fin15AnchoredAtom3343
    Fin15AnchoredAtom3346 Fin15AnchoredAtom3347 Fin15AnchoredAtom3352 Fin15AnchoredAtom3392
    Fin15AnchoredAtom3393 Fin15AnchoredAtom3398 Fin15AnchoredAtom3404 Fin15AnchoredAtom3448
    Fin15AnchoredAtom3449 Fin15AnchoredAtom3454 Fin15AnchoredAtom3460 Fin15AnchoredAtom3525
    Fin15AnchoredAtom3835 Fin15AnchoredAtom3837 Fin15AnchoredAtom3838 Fin15AnchoredAtom3841
    Fin15AnchoredAtom3842 Fin15AnchoredAtom3847 Fin15AnchoredAtom3887 Fin15AnchoredAtom3888
    Fin15AnchoredAtom3893 Fin15AnchoredAtom3899 Fin15AnchoredAtom3943 Fin15AnchoredAtom3944
    Fin15AnchoredAtom3949 Fin15AnchoredAtom3955 Fin15AnchoredAtom4020 Fin15AnchoredAtom4609
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

theorem fin15Anchored_clause31832 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2924 chi ∧
      ¬Fin15AnchoredAtom2925 chi ∧
      ¬Fin15AnchoredAtom2927 chi ∧
      ¬Fin15AnchoredAtom2929 chi ∧
      ¬Fin15AnchoredAtom2943 chi ∧
      ¬Fin15AnchoredAtom2945 chi ∧
      ¬Fin15AnchoredAtom2947 chi ∧
      ¬Fin15AnchoredAtom2949 chi ∧
      ¬Fin15AnchoredAtom2951 chi ∧
      ¬Fin15AnchoredAtom2956 chi ∧
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
      ¬Fin15AnchoredAtom4609 chi ∧
      ¬Fin15AnchoredAtom4611 chi ∧
      ¬Fin15AnchoredAtom4616 chi ∧
      ¬Fin15AnchoredAtom4622 chi ∧
      ¬Fin15AnchoredAtom4687 chi ∧
      ¬Fin15AnchoredAtom4757 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 5, 6, 9, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22118
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2924 Fin15AnchoredAtom2925 Fin15AnchoredAtom2927
    Fin15AnchoredAtom2929 Fin15AnchoredAtom2943 Fin15AnchoredAtom2945 Fin15AnchoredAtom2947
    Fin15AnchoredAtom2949 Fin15AnchoredAtom2951 Fin15AnchoredAtom2956 Fin15AnchoredAtom2971
    Fin15AnchoredAtom2973 Fin15AnchoredAtom2975 Fin15AnchoredAtom2977 Fin15AnchoredAtom2979
    Fin15AnchoredAtom2984 Fin15AnchoredAtom3023 Fin15AnchoredAtom3025 Fin15AnchoredAtom3030
    Fin15AnchoredAtom3036 Fin15AnchoredAtom3340 Fin15AnchoredAtom3342 Fin15AnchoredAtom3344
    Fin15AnchoredAtom3346 Fin15AnchoredAtom3348 Fin15AnchoredAtom3353 Fin15AnchoredAtom3392
    Fin15AnchoredAtom3394 Fin15AnchoredAtom3399 Fin15AnchoredAtom3405 Fin15AnchoredAtom3448
    Fin15AnchoredAtom3450 Fin15AnchoredAtom3455 Fin15AnchoredAtom3461 Fin15AnchoredAtom3526
    Fin15AnchoredAtom3835 Fin15AnchoredAtom3837 Fin15AnchoredAtom3839 Fin15AnchoredAtom3841
    Fin15AnchoredAtom3843 Fin15AnchoredAtom3848 Fin15AnchoredAtom3887 Fin15AnchoredAtom3889
    Fin15AnchoredAtom3894 Fin15AnchoredAtom3900 Fin15AnchoredAtom3943 Fin15AnchoredAtom3945
    Fin15AnchoredAtom3950 Fin15AnchoredAtom3956 Fin15AnchoredAtom4021 Fin15AnchoredAtom4609
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

theorem fin15Anchored_clause31833 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2924 chi ∧
      ¬Fin15AnchoredAtom2925 chi ∧
      ¬Fin15AnchoredAtom2928 chi ∧
      ¬Fin15AnchoredAtom2929 chi ∧
      ¬Fin15AnchoredAtom2943 chi ∧
      ¬Fin15AnchoredAtom2946 chi ∧
      ¬Fin15AnchoredAtom2947 chi ∧
      ¬Fin15AnchoredAtom2950 chi ∧
      ¬Fin15AnchoredAtom2951 chi ∧
      ¬Fin15AnchoredAtom2957 chi ∧
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
      ¬Fin15AnchoredAtom4610 chi ∧
      ¬Fin15AnchoredAtom4611 chi ∧
      ¬Fin15AnchoredAtom4617 chi ∧
      ¬Fin15AnchoredAtom4623 chi ∧
      ¬Fin15AnchoredAtom4688 chi ∧
      ¬Fin15AnchoredAtom4758 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 5, 6, 9, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26214
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2924 Fin15AnchoredAtom2925 Fin15AnchoredAtom2928
    Fin15AnchoredAtom2929 Fin15AnchoredAtom2943 Fin15AnchoredAtom2946 Fin15AnchoredAtom2947
    Fin15AnchoredAtom2950 Fin15AnchoredAtom2951 Fin15AnchoredAtom2957 Fin15AnchoredAtom2971
    Fin15AnchoredAtom2974 Fin15AnchoredAtom2975 Fin15AnchoredAtom2978 Fin15AnchoredAtom2979
    Fin15AnchoredAtom2985 Fin15AnchoredAtom3024 Fin15AnchoredAtom3025 Fin15AnchoredAtom3031
    Fin15AnchoredAtom3037 Fin15AnchoredAtom3340 Fin15AnchoredAtom3343 Fin15AnchoredAtom3344
    Fin15AnchoredAtom3347 Fin15AnchoredAtom3348 Fin15AnchoredAtom3354 Fin15AnchoredAtom3393
    Fin15AnchoredAtom3394 Fin15AnchoredAtom3400 Fin15AnchoredAtom3406 Fin15AnchoredAtom3449
    Fin15AnchoredAtom3450 Fin15AnchoredAtom3456 Fin15AnchoredAtom3462 Fin15AnchoredAtom3527
    Fin15AnchoredAtom3835 Fin15AnchoredAtom3838 Fin15AnchoredAtom3839 Fin15AnchoredAtom3842
    Fin15AnchoredAtom3843 Fin15AnchoredAtom3849 Fin15AnchoredAtom3888 Fin15AnchoredAtom3889
    Fin15AnchoredAtom3895 Fin15AnchoredAtom3901 Fin15AnchoredAtom3944 Fin15AnchoredAtom3945
    Fin15AnchoredAtom3951 Fin15AnchoredAtom3957 Fin15AnchoredAtom4022 Fin15AnchoredAtom4610
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

theorem fin15Anchored_clause31834 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2924 chi ∧
      ¬Fin15AnchoredAtom2927 chi ∧
      ¬Fin15AnchoredAtom2928 chi ∧
      ¬Fin15AnchoredAtom2929 chi ∧
      ¬Fin15AnchoredAtom2945 chi ∧
      ¬Fin15AnchoredAtom2946 chi ∧
      ¬Fin15AnchoredAtom2947 chi ∧
      ¬Fin15AnchoredAtom2955 chi ∧
      ¬Fin15AnchoredAtom2956 chi ∧
      ¬Fin15AnchoredAtom2957 chi ∧
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
      ¬Fin15AnchoredAtom4615 chi ∧
      ¬Fin15AnchoredAtom4616 chi ∧
      ¬Fin15AnchoredAtom4617 chi ∧
      ¬Fin15AnchoredAtom4627 chi ∧
      ¬Fin15AnchoredAtom4692 chi ∧
      ¬Fin15AnchoredAtom4762 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 5, 6, 9, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29286
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2924 Fin15AnchoredAtom2927 Fin15AnchoredAtom2928
    Fin15AnchoredAtom2929 Fin15AnchoredAtom2945 Fin15AnchoredAtom2946 Fin15AnchoredAtom2947
    Fin15AnchoredAtom2955 Fin15AnchoredAtom2956 Fin15AnchoredAtom2957 Fin15AnchoredAtom2973
    Fin15AnchoredAtom2974 Fin15AnchoredAtom2975 Fin15AnchoredAtom2983 Fin15AnchoredAtom2984
    Fin15AnchoredAtom2985 Fin15AnchoredAtom3029 Fin15AnchoredAtom3030 Fin15AnchoredAtom3031
    Fin15AnchoredAtom3041 Fin15AnchoredAtom3342 Fin15AnchoredAtom3343 Fin15AnchoredAtom3344
    Fin15AnchoredAtom3352 Fin15AnchoredAtom3353 Fin15AnchoredAtom3354 Fin15AnchoredAtom3398
    Fin15AnchoredAtom3399 Fin15AnchoredAtom3400 Fin15AnchoredAtom3410 Fin15AnchoredAtom3454
    Fin15AnchoredAtom3455 Fin15AnchoredAtom3456 Fin15AnchoredAtom3466 Fin15AnchoredAtom3531
    Fin15AnchoredAtom3837 Fin15AnchoredAtom3838 Fin15AnchoredAtom3839 Fin15AnchoredAtom3847
    Fin15AnchoredAtom3848 Fin15AnchoredAtom3849 Fin15AnchoredAtom3893 Fin15AnchoredAtom3894
    Fin15AnchoredAtom3895 Fin15AnchoredAtom3905 Fin15AnchoredAtom3949 Fin15AnchoredAtom3950
    Fin15AnchoredAtom3951 Fin15AnchoredAtom3961 Fin15AnchoredAtom4026 Fin15AnchoredAtom4615
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

theorem fin15Anchored_clause31835 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2925 chi ∧
      ¬Fin15AnchoredAtom2927 chi ∧
      ¬Fin15AnchoredAtom2928 chi ∧
      ¬Fin15AnchoredAtom2929 chi ∧
      ¬Fin15AnchoredAtom2949 chi ∧
      ¬Fin15AnchoredAtom2950 chi ∧
      ¬Fin15AnchoredAtom2951 chi ∧
      ¬Fin15AnchoredAtom2955 chi ∧
      ¬Fin15AnchoredAtom2956 chi ∧
      ¬Fin15AnchoredAtom2957 chi ∧
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
      ¬Fin15AnchoredAtom4621 chi ∧
      ¬Fin15AnchoredAtom4622 chi ∧
      ¬Fin15AnchoredAtom4623 chi ∧
      ¬Fin15AnchoredAtom4627 chi ∧
      ¬Fin15AnchoredAtom4696 chi ∧
      ¬Fin15AnchoredAtom4766 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 5, 6, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29798
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2925 Fin15AnchoredAtom2927 Fin15AnchoredAtom2928
    Fin15AnchoredAtom2929 Fin15AnchoredAtom2949 Fin15AnchoredAtom2950 Fin15AnchoredAtom2951
    Fin15AnchoredAtom2955 Fin15AnchoredAtom2956 Fin15AnchoredAtom2957 Fin15AnchoredAtom2977
    Fin15AnchoredAtom2978 Fin15AnchoredAtom2979 Fin15AnchoredAtom2983 Fin15AnchoredAtom2984
    Fin15AnchoredAtom2985 Fin15AnchoredAtom3035 Fin15AnchoredAtom3036 Fin15AnchoredAtom3037
    Fin15AnchoredAtom3041 Fin15AnchoredAtom3346 Fin15AnchoredAtom3347 Fin15AnchoredAtom3348
    Fin15AnchoredAtom3352 Fin15AnchoredAtom3353 Fin15AnchoredAtom3354 Fin15AnchoredAtom3404
    Fin15AnchoredAtom3405 Fin15AnchoredAtom3406 Fin15AnchoredAtom3410 Fin15AnchoredAtom3460
    Fin15AnchoredAtom3461 Fin15AnchoredAtom3462 Fin15AnchoredAtom3466 Fin15AnchoredAtom3535
    Fin15AnchoredAtom3841 Fin15AnchoredAtom3842 Fin15AnchoredAtom3843 Fin15AnchoredAtom3847
    Fin15AnchoredAtom3848 Fin15AnchoredAtom3849 Fin15AnchoredAtom3899 Fin15AnchoredAtom3900
    Fin15AnchoredAtom3901 Fin15AnchoredAtom3905 Fin15AnchoredAtom3955 Fin15AnchoredAtom3956
    Fin15AnchoredAtom3957 Fin15AnchoredAtom3961 Fin15AnchoredAtom4030 Fin15AnchoredAtom4621
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

theorem fin15Anchored_clause31836 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2931 chi ∧
      ¬Fin15AnchoredAtom2932 chi ∧
      ¬Fin15AnchoredAtom2934 chi ∧
      ¬Fin15AnchoredAtom2935 chi ∧
      ¬Fin15AnchoredAtom2943 chi ∧
      ¬Fin15AnchoredAtom2945 chi ∧
      ¬Fin15AnchoredAtom2946 chi ∧
      ¬Fin15AnchoredAtom2949 chi ∧
      ¬Fin15AnchoredAtom2950 chi ∧
      ¬Fin15AnchoredAtom2955 chi ∧
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
      ¬Fin15AnchoredAtom4644 chi ∧
      ¬Fin15AnchoredAtom4645 chi ∧
      ¬Fin15AnchoredAtom4650 chi ∧
      ¬Fin15AnchoredAtom4656 chi ∧
      ¬Fin15AnchoredAtom4686 chi ∧
      ¬Fin15AnchoredAtom4791 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 5, 7, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13990
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2931 Fin15AnchoredAtom2932 Fin15AnchoredAtom2934
    Fin15AnchoredAtom2935 Fin15AnchoredAtom2943 Fin15AnchoredAtom2945 Fin15AnchoredAtom2946
    Fin15AnchoredAtom2949 Fin15AnchoredAtom2950 Fin15AnchoredAtom2955 Fin15AnchoredAtom2992
    Fin15AnchoredAtom2994 Fin15AnchoredAtom2995 Fin15AnchoredAtom2998 Fin15AnchoredAtom2999
    Fin15AnchoredAtom3004 Fin15AnchoredAtom3023 Fin15AnchoredAtom3024 Fin15AnchoredAtom3029
    Fin15AnchoredAtom3035 Fin15AnchoredAtom3361 Fin15AnchoredAtom3363 Fin15AnchoredAtom3364
    Fin15AnchoredAtom3367 Fin15AnchoredAtom3368 Fin15AnchoredAtom3373 Fin15AnchoredAtom3392
    Fin15AnchoredAtom3393 Fin15AnchoredAtom3398 Fin15AnchoredAtom3404 Fin15AnchoredAtom3483
    Fin15AnchoredAtom3484 Fin15AnchoredAtom3489 Fin15AnchoredAtom3495 Fin15AnchoredAtom3525
    Fin15AnchoredAtom3856 Fin15AnchoredAtom3858 Fin15AnchoredAtom3859 Fin15AnchoredAtom3862
    Fin15AnchoredAtom3863 Fin15AnchoredAtom3868 Fin15AnchoredAtom3887 Fin15AnchoredAtom3888
    Fin15AnchoredAtom3893 Fin15AnchoredAtom3899 Fin15AnchoredAtom3978 Fin15AnchoredAtom3979
    Fin15AnchoredAtom3984 Fin15AnchoredAtom3990 Fin15AnchoredAtom4020 Fin15AnchoredAtom4644
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

theorem fin15Anchored_clause31837 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2931 chi ∧
      ¬Fin15AnchoredAtom2932 chi ∧
      ¬Fin15AnchoredAtom2934 chi ∧
      ¬Fin15AnchoredAtom2936 chi ∧
      ¬Fin15AnchoredAtom2943 chi ∧
      ¬Fin15AnchoredAtom2945 chi ∧
      ¬Fin15AnchoredAtom2947 chi ∧
      ¬Fin15AnchoredAtom2949 chi ∧
      ¬Fin15AnchoredAtom2951 chi ∧
      ¬Fin15AnchoredAtom2956 chi ∧
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
      ¬Fin15AnchoredAtom4644 chi ∧
      ¬Fin15AnchoredAtom4646 chi ∧
      ¬Fin15AnchoredAtom4651 chi ∧
      ¬Fin15AnchoredAtom4657 chi ∧
      ¬Fin15AnchoredAtom4687 chi ∧
      ¬Fin15AnchoredAtom4792 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 5, 7, 9, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22182
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2931 Fin15AnchoredAtom2932 Fin15AnchoredAtom2934
    Fin15AnchoredAtom2936 Fin15AnchoredAtom2943 Fin15AnchoredAtom2945 Fin15AnchoredAtom2947
    Fin15AnchoredAtom2949 Fin15AnchoredAtom2951 Fin15AnchoredAtom2956 Fin15AnchoredAtom2992
    Fin15AnchoredAtom2994 Fin15AnchoredAtom2996 Fin15AnchoredAtom2998 Fin15AnchoredAtom3000
    Fin15AnchoredAtom3005 Fin15AnchoredAtom3023 Fin15AnchoredAtom3025 Fin15AnchoredAtom3030
    Fin15AnchoredAtom3036 Fin15AnchoredAtom3361 Fin15AnchoredAtom3363 Fin15AnchoredAtom3365
    Fin15AnchoredAtom3367 Fin15AnchoredAtom3369 Fin15AnchoredAtom3374 Fin15AnchoredAtom3392
    Fin15AnchoredAtom3394 Fin15AnchoredAtom3399 Fin15AnchoredAtom3405 Fin15AnchoredAtom3483
    Fin15AnchoredAtom3485 Fin15AnchoredAtom3490 Fin15AnchoredAtom3496 Fin15AnchoredAtom3526
    Fin15AnchoredAtom3856 Fin15AnchoredAtom3858 Fin15AnchoredAtom3860 Fin15AnchoredAtom3862
    Fin15AnchoredAtom3864 Fin15AnchoredAtom3869 Fin15AnchoredAtom3887 Fin15AnchoredAtom3889
    Fin15AnchoredAtom3894 Fin15AnchoredAtom3900 Fin15AnchoredAtom3978 Fin15AnchoredAtom3980
    Fin15AnchoredAtom3985 Fin15AnchoredAtom3991 Fin15AnchoredAtom4021 Fin15AnchoredAtom4644
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

theorem fin15Anchored_clause31838 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2931 chi ∧
      ¬Fin15AnchoredAtom2932 chi ∧
      ¬Fin15AnchoredAtom2935 chi ∧
      ¬Fin15AnchoredAtom2936 chi ∧
      ¬Fin15AnchoredAtom2943 chi ∧
      ¬Fin15AnchoredAtom2946 chi ∧
      ¬Fin15AnchoredAtom2947 chi ∧
      ¬Fin15AnchoredAtom2950 chi ∧
      ¬Fin15AnchoredAtom2951 chi ∧
      ¬Fin15AnchoredAtom2957 chi ∧
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
      ¬Fin15AnchoredAtom4645 chi ∧
      ¬Fin15AnchoredAtom4646 chi ∧
      ¬Fin15AnchoredAtom4652 chi ∧
      ¬Fin15AnchoredAtom4658 chi ∧
      ¬Fin15AnchoredAtom4688 chi ∧
      ¬Fin15AnchoredAtom4793 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 5, 7, 9, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26278
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2931 Fin15AnchoredAtom2932 Fin15AnchoredAtom2935
    Fin15AnchoredAtom2936 Fin15AnchoredAtom2943 Fin15AnchoredAtom2946 Fin15AnchoredAtom2947
    Fin15AnchoredAtom2950 Fin15AnchoredAtom2951 Fin15AnchoredAtom2957 Fin15AnchoredAtom2992
    Fin15AnchoredAtom2995 Fin15AnchoredAtom2996 Fin15AnchoredAtom2999 Fin15AnchoredAtom3000
    Fin15AnchoredAtom3006 Fin15AnchoredAtom3024 Fin15AnchoredAtom3025 Fin15AnchoredAtom3031
    Fin15AnchoredAtom3037 Fin15AnchoredAtom3361 Fin15AnchoredAtom3364 Fin15AnchoredAtom3365
    Fin15AnchoredAtom3368 Fin15AnchoredAtom3369 Fin15AnchoredAtom3375 Fin15AnchoredAtom3393
    Fin15AnchoredAtom3394 Fin15AnchoredAtom3400 Fin15AnchoredAtom3406 Fin15AnchoredAtom3484
    Fin15AnchoredAtom3485 Fin15AnchoredAtom3491 Fin15AnchoredAtom3497 Fin15AnchoredAtom3527
    Fin15AnchoredAtom3856 Fin15AnchoredAtom3859 Fin15AnchoredAtom3860 Fin15AnchoredAtom3863
    Fin15AnchoredAtom3864 Fin15AnchoredAtom3870 Fin15AnchoredAtom3888 Fin15AnchoredAtom3889
    Fin15AnchoredAtom3895 Fin15AnchoredAtom3901 Fin15AnchoredAtom3979 Fin15AnchoredAtom3980
    Fin15AnchoredAtom3986 Fin15AnchoredAtom3992 Fin15AnchoredAtom4022 Fin15AnchoredAtom4645
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

theorem fin15Anchored_clause31839 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2931 chi ∧
      ¬Fin15AnchoredAtom2934 chi ∧
      ¬Fin15AnchoredAtom2935 chi ∧
      ¬Fin15AnchoredAtom2936 chi ∧
      ¬Fin15AnchoredAtom2945 chi ∧
      ¬Fin15AnchoredAtom2946 chi ∧
      ¬Fin15AnchoredAtom2947 chi ∧
      ¬Fin15AnchoredAtom2955 chi ∧
      ¬Fin15AnchoredAtom2956 chi ∧
      ¬Fin15AnchoredAtom2957 chi ∧
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
      ¬Fin15AnchoredAtom4650 chi ∧
      ¬Fin15AnchoredAtom4651 chi ∧
      ¬Fin15AnchoredAtom4652 chi ∧
      ¬Fin15AnchoredAtom4662 chi ∧
      ¬Fin15AnchoredAtom4692 chi ∧
      ¬Fin15AnchoredAtom4797 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 5, 7, 9, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29350
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2931 Fin15AnchoredAtom2934 Fin15AnchoredAtom2935
    Fin15AnchoredAtom2936 Fin15AnchoredAtom2945 Fin15AnchoredAtom2946 Fin15AnchoredAtom2947
    Fin15AnchoredAtom2955 Fin15AnchoredAtom2956 Fin15AnchoredAtom2957 Fin15AnchoredAtom2994
    Fin15AnchoredAtom2995 Fin15AnchoredAtom2996 Fin15AnchoredAtom3004 Fin15AnchoredAtom3005
    Fin15AnchoredAtom3006 Fin15AnchoredAtom3029 Fin15AnchoredAtom3030 Fin15AnchoredAtom3031
    Fin15AnchoredAtom3041 Fin15AnchoredAtom3363 Fin15AnchoredAtom3364 Fin15AnchoredAtom3365
    Fin15AnchoredAtom3373 Fin15AnchoredAtom3374 Fin15AnchoredAtom3375 Fin15AnchoredAtom3398
    Fin15AnchoredAtom3399 Fin15AnchoredAtom3400 Fin15AnchoredAtom3410 Fin15AnchoredAtom3489
    Fin15AnchoredAtom3490 Fin15AnchoredAtom3491 Fin15AnchoredAtom3501 Fin15AnchoredAtom3531
    Fin15AnchoredAtom3858 Fin15AnchoredAtom3859 Fin15AnchoredAtom3860 Fin15AnchoredAtom3868
    Fin15AnchoredAtom3869 Fin15AnchoredAtom3870 Fin15AnchoredAtom3893 Fin15AnchoredAtom3894
    Fin15AnchoredAtom3895 Fin15AnchoredAtom3905 Fin15AnchoredAtom3984 Fin15AnchoredAtom3985
    Fin15AnchoredAtom3986 Fin15AnchoredAtom3996 Fin15AnchoredAtom4026 Fin15AnchoredAtom4650
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

theorem fin15Anchored_clause31840 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2932 chi ∧
      ¬Fin15AnchoredAtom2934 chi ∧
      ¬Fin15AnchoredAtom2935 chi ∧
      ¬Fin15AnchoredAtom2936 chi ∧
      ¬Fin15AnchoredAtom2949 chi ∧
      ¬Fin15AnchoredAtom2950 chi ∧
      ¬Fin15AnchoredAtom2951 chi ∧
      ¬Fin15AnchoredAtom2955 chi ∧
      ¬Fin15AnchoredAtom2956 chi ∧
      ¬Fin15AnchoredAtom2957 chi ∧
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
      ¬Fin15AnchoredAtom4656 chi ∧
      ¬Fin15AnchoredAtom4657 chi ∧
      ¬Fin15AnchoredAtom4658 chi ∧
      ¬Fin15AnchoredAtom4662 chi ∧
      ¬Fin15AnchoredAtom4696 chi ∧
      ¬Fin15AnchoredAtom4801 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 5, 7, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29862
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2932 Fin15AnchoredAtom2934 Fin15AnchoredAtom2935
    Fin15AnchoredAtom2936 Fin15AnchoredAtom2949 Fin15AnchoredAtom2950 Fin15AnchoredAtom2951
    Fin15AnchoredAtom2955 Fin15AnchoredAtom2956 Fin15AnchoredAtom2957 Fin15AnchoredAtom2998
    Fin15AnchoredAtom2999 Fin15AnchoredAtom3000 Fin15AnchoredAtom3004 Fin15AnchoredAtom3005
    Fin15AnchoredAtom3006 Fin15AnchoredAtom3035 Fin15AnchoredAtom3036 Fin15AnchoredAtom3037
    Fin15AnchoredAtom3041 Fin15AnchoredAtom3367 Fin15AnchoredAtom3368 Fin15AnchoredAtom3369
    Fin15AnchoredAtom3373 Fin15AnchoredAtom3374 Fin15AnchoredAtom3375 Fin15AnchoredAtom3404
    Fin15AnchoredAtom3405 Fin15AnchoredAtom3406 Fin15AnchoredAtom3410 Fin15AnchoredAtom3495
    Fin15AnchoredAtom3496 Fin15AnchoredAtom3497 Fin15AnchoredAtom3501 Fin15AnchoredAtom3535
    Fin15AnchoredAtom3862 Fin15AnchoredAtom3863 Fin15AnchoredAtom3864 Fin15AnchoredAtom3868
    Fin15AnchoredAtom3869 Fin15AnchoredAtom3870 Fin15AnchoredAtom3899 Fin15AnchoredAtom3900
    Fin15AnchoredAtom3901 Fin15AnchoredAtom3905 Fin15AnchoredAtom3990 Fin15AnchoredAtom3991
    Fin15AnchoredAtom3992 Fin15AnchoredAtom3996 Fin15AnchoredAtom4030 Fin15AnchoredAtom4656
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

theorem fin15Anchored_clause31841 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2943 chi ∧
      ¬Fin15AnchoredAtom2945 chi ∧
      ¬Fin15AnchoredAtom2946 chi ∧
      ¬Fin15AnchoredAtom2947 chi ∧
      ¬Fin15AnchoredAtom2949 chi ∧
      ¬Fin15AnchoredAtom2950 chi ∧
      ¬Fin15AnchoredAtom2951 chi ∧
      ¬Fin15AnchoredAtom2955 chi ∧
      ¬Fin15AnchoredAtom2956 chi ∧
      ¬Fin15AnchoredAtom2957 chi ∧
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
      ¬Fin15AnchoredAtom4686 chi ∧
      ¬Fin15AnchoredAtom4687 chi ∧
      ¬Fin15AnchoredAtom4688 chi ∧
      ¬Fin15AnchoredAtom4692 chi ∧
      ¬Fin15AnchoredAtom4696 chi ∧
      ¬Fin15AnchoredAtom4821 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 5, 9, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask30246
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2943 Fin15AnchoredAtom2945 Fin15AnchoredAtom2946
    Fin15AnchoredAtom2947 Fin15AnchoredAtom2949 Fin15AnchoredAtom2950 Fin15AnchoredAtom2951
    Fin15AnchoredAtom2955 Fin15AnchoredAtom2956 Fin15AnchoredAtom2957 Fin15AnchoredAtom3023
    Fin15AnchoredAtom3024 Fin15AnchoredAtom3025 Fin15AnchoredAtom3029 Fin15AnchoredAtom3030
    Fin15AnchoredAtom3031 Fin15AnchoredAtom3035 Fin15AnchoredAtom3036 Fin15AnchoredAtom3037
    Fin15AnchoredAtom3041 Fin15AnchoredAtom3392 Fin15AnchoredAtom3393 Fin15AnchoredAtom3394
    Fin15AnchoredAtom3398 Fin15AnchoredAtom3399 Fin15AnchoredAtom3400 Fin15AnchoredAtom3404
    Fin15AnchoredAtom3405 Fin15AnchoredAtom3406 Fin15AnchoredAtom3410 Fin15AnchoredAtom3525
    Fin15AnchoredAtom3526 Fin15AnchoredAtom3527 Fin15AnchoredAtom3531 Fin15AnchoredAtom3535
    Fin15AnchoredAtom3887 Fin15AnchoredAtom3888 Fin15AnchoredAtom3889 Fin15AnchoredAtom3893
    Fin15AnchoredAtom3894 Fin15AnchoredAtom3895 Fin15AnchoredAtom3899 Fin15AnchoredAtom3900
    Fin15AnchoredAtom3901 Fin15AnchoredAtom3905 Fin15AnchoredAtom4020 Fin15AnchoredAtom4021
    Fin15AnchoredAtom4022 Fin15AnchoredAtom4026 Fin15AnchoredAtom4030 Fin15AnchoredAtom4686
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

theorem fin15Anchored_clause31842 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2959 chi ∧
      ¬Fin15AnchoredAtom2960 chi ∧
      ¬Fin15AnchoredAtom2962 chi ∧
      ¬Fin15AnchoredAtom2963 chi ∧
      ¬Fin15AnchoredAtom2971 chi ∧
      ¬Fin15AnchoredAtom2973 chi ∧
      ¬Fin15AnchoredAtom2974 chi ∧
      ¬Fin15AnchoredAtom2977 chi ∧
      ¬Fin15AnchoredAtom2978 chi ∧
      ¬Fin15AnchoredAtom2983 chi ∧
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
      ¬Fin15AnchoredAtom4714 chi ∧
      ¬Fin15AnchoredAtom4715 chi ∧
      ¬Fin15AnchoredAtom4720 chi ∧
      ¬Fin15AnchoredAtom4726 chi ∧
      ¬Fin15AnchoredAtom4756 chi ∧
      ¬Fin15AnchoredAtom4791 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 6, 7, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask14022
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2959 Fin15AnchoredAtom2960 Fin15AnchoredAtom2962
    Fin15AnchoredAtom2963 Fin15AnchoredAtom2971 Fin15AnchoredAtom2973 Fin15AnchoredAtom2974
    Fin15AnchoredAtom2977 Fin15AnchoredAtom2978 Fin15AnchoredAtom2983 Fin15AnchoredAtom2992
    Fin15AnchoredAtom2994 Fin15AnchoredAtom2995 Fin15AnchoredAtom2998 Fin15AnchoredAtom2999
    Fin15AnchoredAtom3004 Fin15AnchoredAtom3023 Fin15AnchoredAtom3024 Fin15AnchoredAtom3029
    Fin15AnchoredAtom3035 Fin15AnchoredAtom3417 Fin15AnchoredAtom3419 Fin15AnchoredAtom3420
    Fin15AnchoredAtom3423 Fin15AnchoredAtom3424 Fin15AnchoredAtom3429 Fin15AnchoredAtom3448
    Fin15AnchoredAtom3449 Fin15AnchoredAtom3454 Fin15AnchoredAtom3460 Fin15AnchoredAtom3483
    Fin15AnchoredAtom3484 Fin15AnchoredAtom3489 Fin15AnchoredAtom3495 Fin15AnchoredAtom3525
    Fin15AnchoredAtom3912 Fin15AnchoredAtom3914 Fin15AnchoredAtom3915 Fin15AnchoredAtom3918
    Fin15AnchoredAtom3919 Fin15AnchoredAtom3924 Fin15AnchoredAtom3943 Fin15AnchoredAtom3944
    Fin15AnchoredAtom3949 Fin15AnchoredAtom3955 Fin15AnchoredAtom3978 Fin15AnchoredAtom3979
    Fin15AnchoredAtom3984 Fin15AnchoredAtom3990 Fin15AnchoredAtom4020 Fin15AnchoredAtom4714
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

theorem fin15Anchored_clause31843 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2959 chi ∧
      ¬Fin15AnchoredAtom2960 chi ∧
      ¬Fin15AnchoredAtom2962 chi ∧
      ¬Fin15AnchoredAtom2964 chi ∧
      ¬Fin15AnchoredAtom2971 chi ∧
      ¬Fin15AnchoredAtom2973 chi ∧
      ¬Fin15AnchoredAtom2975 chi ∧
      ¬Fin15AnchoredAtom2977 chi ∧
      ¬Fin15AnchoredAtom2979 chi ∧
      ¬Fin15AnchoredAtom2984 chi ∧
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
      ¬Fin15AnchoredAtom4714 chi ∧
      ¬Fin15AnchoredAtom4716 chi ∧
      ¬Fin15AnchoredAtom4721 chi ∧
      ¬Fin15AnchoredAtom4727 chi ∧
      ¬Fin15AnchoredAtom4757 chi ∧
      ¬Fin15AnchoredAtom4792 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 6, 7, 9, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22214
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2959 Fin15AnchoredAtom2960 Fin15AnchoredAtom2962
    Fin15AnchoredAtom2964 Fin15AnchoredAtom2971 Fin15AnchoredAtom2973 Fin15AnchoredAtom2975
    Fin15AnchoredAtom2977 Fin15AnchoredAtom2979 Fin15AnchoredAtom2984 Fin15AnchoredAtom2992
    Fin15AnchoredAtom2994 Fin15AnchoredAtom2996 Fin15AnchoredAtom2998 Fin15AnchoredAtom3000
    Fin15AnchoredAtom3005 Fin15AnchoredAtom3023 Fin15AnchoredAtom3025 Fin15AnchoredAtom3030
    Fin15AnchoredAtom3036 Fin15AnchoredAtom3417 Fin15AnchoredAtom3419 Fin15AnchoredAtom3421
    Fin15AnchoredAtom3423 Fin15AnchoredAtom3425 Fin15AnchoredAtom3430 Fin15AnchoredAtom3448
    Fin15AnchoredAtom3450 Fin15AnchoredAtom3455 Fin15AnchoredAtom3461 Fin15AnchoredAtom3483
    Fin15AnchoredAtom3485 Fin15AnchoredAtom3490 Fin15AnchoredAtom3496 Fin15AnchoredAtom3526
    Fin15AnchoredAtom3912 Fin15AnchoredAtom3914 Fin15AnchoredAtom3916 Fin15AnchoredAtom3918
    Fin15AnchoredAtom3920 Fin15AnchoredAtom3925 Fin15AnchoredAtom3943 Fin15AnchoredAtom3945
    Fin15AnchoredAtom3950 Fin15AnchoredAtom3956 Fin15AnchoredAtom3978 Fin15AnchoredAtom3980
    Fin15AnchoredAtom3985 Fin15AnchoredAtom3991 Fin15AnchoredAtom4021 Fin15AnchoredAtom4714
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

theorem fin15Anchored_clause31844 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2959 chi ∧
      ¬Fin15AnchoredAtom2960 chi ∧
      ¬Fin15AnchoredAtom2963 chi ∧
      ¬Fin15AnchoredAtom2964 chi ∧
      ¬Fin15AnchoredAtom2971 chi ∧
      ¬Fin15AnchoredAtom2974 chi ∧
      ¬Fin15AnchoredAtom2975 chi ∧
      ¬Fin15AnchoredAtom2978 chi ∧
      ¬Fin15AnchoredAtom2979 chi ∧
      ¬Fin15AnchoredAtom2985 chi ∧
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
      ¬Fin15AnchoredAtom4715 chi ∧
      ¬Fin15AnchoredAtom4716 chi ∧
      ¬Fin15AnchoredAtom4722 chi ∧
      ¬Fin15AnchoredAtom4728 chi ∧
      ¬Fin15AnchoredAtom4758 chi ∧
      ¬Fin15AnchoredAtom4793 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 6, 7, 9, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26310
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2959 Fin15AnchoredAtom2960 Fin15AnchoredAtom2963
    Fin15AnchoredAtom2964 Fin15AnchoredAtom2971 Fin15AnchoredAtom2974 Fin15AnchoredAtom2975
    Fin15AnchoredAtom2978 Fin15AnchoredAtom2979 Fin15AnchoredAtom2985 Fin15AnchoredAtom2992
    Fin15AnchoredAtom2995 Fin15AnchoredAtom2996 Fin15AnchoredAtom2999 Fin15AnchoredAtom3000
    Fin15AnchoredAtom3006 Fin15AnchoredAtom3024 Fin15AnchoredAtom3025 Fin15AnchoredAtom3031
    Fin15AnchoredAtom3037 Fin15AnchoredAtom3417 Fin15AnchoredAtom3420 Fin15AnchoredAtom3421
    Fin15AnchoredAtom3424 Fin15AnchoredAtom3425 Fin15AnchoredAtom3431 Fin15AnchoredAtom3449
    Fin15AnchoredAtom3450 Fin15AnchoredAtom3456 Fin15AnchoredAtom3462 Fin15AnchoredAtom3484
    Fin15AnchoredAtom3485 Fin15AnchoredAtom3491 Fin15AnchoredAtom3497 Fin15AnchoredAtom3527
    Fin15AnchoredAtom3912 Fin15AnchoredAtom3915 Fin15AnchoredAtom3916 Fin15AnchoredAtom3919
    Fin15AnchoredAtom3920 Fin15AnchoredAtom3926 Fin15AnchoredAtom3944 Fin15AnchoredAtom3945
    Fin15AnchoredAtom3951 Fin15AnchoredAtom3957 Fin15AnchoredAtom3979 Fin15AnchoredAtom3980
    Fin15AnchoredAtom3986 Fin15AnchoredAtom3992 Fin15AnchoredAtom4022 Fin15AnchoredAtom4715
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

theorem fin15Anchored_clause31845 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2959 chi ∧
      ¬Fin15AnchoredAtom2962 chi ∧
      ¬Fin15AnchoredAtom2963 chi ∧
      ¬Fin15AnchoredAtom2964 chi ∧
      ¬Fin15AnchoredAtom2973 chi ∧
      ¬Fin15AnchoredAtom2974 chi ∧
      ¬Fin15AnchoredAtom2975 chi ∧
      ¬Fin15AnchoredAtom2983 chi ∧
      ¬Fin15AnchoredAtom2984 chi ∧
      ¬Fin15AnchoredAtom2985 chi ∧
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
      ¬Fin15AnchoredAtom4720 chi ∧
      ¬Fin15AnchoredAtom4721 chi ∧
      ¬Fin15AnchoredAtom4722 chi ∧
      ¬Fin15AnchoredAtom4732 chi ∧
      ¬Fin15AnchoredAtom4762 chi ∧
      ¬Fin15AnchoredAtom4797 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 6, 7, 9, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29382
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2959 Fin15AnchoredAtom2962 Fin15AnchoredAtom2963
    Fin15AnchoredAtom2964 Fin15AnchoredAtom2973 Fin15AnchoredAtom2974 Fin15AnchoredAtom2975
    Fin15AnchoredAtom2983 Fin15AnchoredAtom2984 Fin15AnchoredAtom2985 Fin15AnchoredAtom2994
    Fin15AnchoredAtom2995 Fin15AnchoredAtom2996 Fin15AnchoredAtom3004 Fin15AnchoredAtom3005
    Fin15AnchoredAtom3006 Fin15AnchoredAtom3029 Fin15AnchoredAtom3030 Fin15AnchoredAtom3031
    Fin15AnchoredAtom3041 Fin15AnchoredAtom3419 Fin15AnchoredAtom3420 Fin15AnchoredAtom3421
    Fin15AnchoredAtom3429 Fin15AnchoredAtom3430 Fin15AnchoredAtom3431 Fin15AnchoredAtom3454
    Fin15AnchoredAtom3455 Fin15AnchoredAtom3456 Fin15AnchoredAtom3466 Fin15AnchoredAtom3489
    Fin15AnchoredAtom3490 Fin15AnchoredAtom3491 Fin15AnchoredAtom3501 Fin15AnchoredAtom3531
    Fin15AnchoredAtom3914 Fin15AnchoredAtom3915 Fin15AnchoredAtom3916 Fin15AnchoredAtom3924
    Fin15AnchoredAtom3925 Fin15AnchoredAtom3926 Fin15AnchoredAtom3949 Fin15AnchoredAtom3950
    Fin15AnchoredAtom3951 Fin15AnchoredAtom3961 Fin15AnchoredAtom3984 Fin15AnchoredAtom3985
    Fin15AnchoredAtom3986 Fin15AnchoredAtom3996 Fin15AnchoredAtom4026 Fin15AnchoredAtom4720
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

theorem fin15Anchored_clause31846 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2960 chi ∧
      ¬Fin15AnchoredAtom2962 chi ∧
      ¬Fin15AnchoredAtom2963 chi ∧
      ¬Fin15AnchoredAtom2964 chi ∧
      ¬Fin15AnchoredAtom2977 chi ∧
      ¬Fin15AnchoredAtom2978 chi ∧
      ¬Fin15AnchoredAtom2979 chi ∧
      ¬Fin15AnchoredAtom2983 chi ∧
      ¬Fin15AnchoredAtom2984 chi ∧
      ¬Fin15AnchoredAtom2985 chi ∧
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
      ¬Fin15AnchoredAtom4726 chi ∧
      ¬Fin15AnchoredAtom4727 chi ∧
      ¬Fin15AnchoredAtom4728 chi ∧
      ¬Fin15AnchoredAtom4732 chi ∧
      ¬Fin15AnchoredAtom4766 chi ∧
      ¬Fin15AnchoredAtom4801 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 6, 7, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29894
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2960 Fin15AnchoredAtom2962 Fin15AnchoredAtom2963
    Fin15AnchoredAtom2964 Fin15AnchoredAtom2977 Fin15AnchoredAtom2978 Fin15AnchoredAtom2979
    Fin15AnchoredAtom2983 Fin15AnchoredAtom2984 Fin15AnchoredAtom2985 Fin15AnchoredAtom2998
    Fin15AnchoredAtom2999 Fin15AnchoredAtom3000 Fin15AnchoredAtom3004 Fin15AnchoredAtom3005
    Fin15AnchoredAtom3006 Fin15AnchoredAtom3035 Fin15AnchoredAtom3036 Fin15AnchoredAtom3037
    Fin15AnchoredAtom3041 Fin15AnchoredAtom3423 Fin15AnchoredAtom3424 Fin15AnchoredAtom3425
    Fin15AnchoredAtom3429 Fin15AnchoredAtom3430 Fin15AnchoredAtom3431 Fin15AnchoredAtom3460
    Fin15AnchoredAtom3461 Fin15AnchoredAtom3462 Fin15AnchoredAtom3466 Fin15AnchoredAtom3495
    Fin15AnchoredAtom3496 Fin15AnchoredAtom3497 Fin15AnchoredAtom3501 Fin15AnchoredAtom3535
    Fin15AnchoredAtom3918 Fin15AnchoredAtom3919 Fin15AnchoredAtom3920 Fin15AnchoredAtom3924
    Fin15AnchoredAtom3925 Fin15AnchoredAtom3926 Fin15AnchoredAtom3955 Fin15AnchoredAtom3956
    Fin15AnchoredAtom3957 Fin15AnchoredAtom3961 Fin15AnchoredAtom3990 Fin15AnchoredAtom3991
    Fin15AnchoredAtom3992 Fin15AnchoredAtom3996 Fin15AnchoredAtom4030 Fin15AnchoredAtom4726
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

theorem fin15Anchored_clause31847 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2971 chi ∧
      ¬Fin15AnchoredAtom2973 chi ∧
      ¬Fin15AnchoredAtom2974 chi ∧
      ¬Fin15AnchoredAtom2975 chi ∧
      ¬Fin15AnchoredAtom2977 chi ∧
      ¬Fin15AnchoredAtom2978 chi ∧
      ¬Fin15AnchoredAtom2979 chi ∧
      ¬Fin15AnchoredAtom2983 chi ∧
      ¬Fin15AnchoredAtom2984 chi ∧
      ¬Fin15AnchoredAtom2985 chi ∧
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
      ¬Fin15AnchoredAtom4756 chi ∧
      ¬Fin15AnchoredAtom4757 chi ∧
      ¬Fin15AnchoredAtom4758 chi ∧
      ¬Fin15AnchoredAtom4762 chi ∧
      ¬Fin15AnchoredAtom4766 chi ∧
      ¬Fin15AnchoredAtom4821 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 6, 9, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask30278
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2971 Fin15AnchoredAtom2973 Fin15AnchoredAtom2974
    Fin15AnchoredAtom2975 Fin15AnchoredAtom2977 Fin15AnchoredAtom2978 Fin15AnchoredAtom2979
    Fin15AnchoredAtom2983 Fin15AnchoredAtom2984 Fin15AnchoredAtom2985 Fin15AnchoredAtom3023
    Fin15AnchoredAtom3024 Fin15AnchoredAtom3025 Fin15AnchoredAtom3029 Fin15AnchoredAtom3030
    Fin15AnchoredAtom3031 Fin15AnchoredAtom3035 Fin15AnchoredAtom3036 Fin15AnchoredAtom3037
    Fin15AnchoredAtom3041 Fin15AnchoredAtom3448 Fin15AnchoredAtom3449 Fin15AnchoredAtom3450
    Fin15AnchoredAtom3454 Fin15AnchoredAtom3455 Fin15AnchoredAtom3456 Fin15AnchoredAtom3460
    Fin15AnchoredAtom3461 Fin15AnchoredAtom3462 Fin15AnchoredAtom3466 Fin15AnchoredAtom3525
    Fin15AnchoredAtom3526 Fin15AnchoredAtom3527 Fin15AnchoredAtom3531 Fin15AnchoredAtom3535
    Fin15AnchoredAtom3943 Fin15AnchoredAtom3944 Fin15AnchoredAtom3945 Fin15AnchoredAtom3949
    Fin15AnchoredAtom3950 Fin15AnchoredAtom3951 Fin15AnchoredAtom3955 Fin15AnchoredAtom3956
    Fin15AnchoredAtom3957 Fin15AnchoredAtom3961 Fin15AnchoredAtom4020 Fin15AnchoredAtom4021
    Fin15AnchoredAtom4022 Fin15AnchoredAtom4026 Fin15AnchoredAtom4030 Fin15AnchoredAtom4756
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

theorem fin15Anchored_clause31848 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom2992 chi ∧
      ¬Fin15AnchoredAtom2994 chi ∧
      ¬Fin15AnchoredAtom2995 chi ∧
      ¬Fin15AnchoredAtom2996 chi ∧
      ¬Fin15AnchoredAtom2998 chi ∧
      ¬Fin15AnchoredAtom2999 chi ∧
      ¬Fin15AnchoredAtom3000 chi ∧
      ¬Fin15AnchoredAtom3004 chi ∧
      ¬Fin15AnchoredAtom3005 chi ∧
      ¬Fin15AnchoredAtom3006 chi ∧
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
      ¬Fin15AnchoredAtom4791 chi ∧
      ¬Fin15AnchoredAtom4792 chi ∧
      ¬Fin15AnchoredAtom4793 chi ∧
      ¬Fin15AnchoredAtom4797 chi ∧
      ¬Fin15AnchoredAtom4801 chi ∧
      ¬Fin15AnchoredAtom4821 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 2, 7, 9, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask30342
    polygon hsubset hcard
  unfold Fin15AnchoredAtom2992 Fin15AnchoredAtom2994 Fin15AnchoredAtom2995
    Fin15AnchoredAtom2996 Fin15AnchoredAtom2998 Fin15AnchoredAtom2999 Fin15AnchoredAtom3000
    Fin15AnchoredAtom3004 Fin15AnchoredAtom3005 Fin15AnchoredAtom3006 Fin15AnchoredAtom3023
    Fin15AnchoredAtom3024 Fin15AnchoredAtom3025 Fin15AnchoredAtom3029 Fin15AnchoredAtom3030
    Fin15AnchoredAtom3031 Fin15AnchoredAtom3035 Fin15AnchoredAtom3036 Fin15AnchoredAtom3037
    Fin15AnchoredAtom3041 Fin15AnchoredAtom3483 Fin15AnchoredAtom3484 Fin15AnchoredAtom3485
    Fin15AnchoredAtom3489 Fin15AnchoredAtom3490 Fin15AnchoredAtom3491 Fin15AnchoredAtom3495
    Fin15AnchoredAtom3496 Fin15AnchoredAtom3497 Fin15AnchoredAtom3501 Fin15AnchoredAtom3525
    Fin15AnchoredAtom3526 Fin15AnchoredAtom3527 Fin15AnchoredAtom3531 Fin15AnchoredAtom3535
    Fin15AnchoredAtom3978 Fin15AnchoredAtom3979 Fin15AnchoredAtom3980 Fin15AnchoredAtom3984
    Fin15AnchoredAtom3985 Fin15AnchoredAtom3986 Fin15AnchoredAtom3990 Fin15AnchoredAtom3991
    Fin15AnchoredAtom3992 Fin15AnchoredAtom3996 Fin15AnchoredAtom4020 Fin15AnchoredAtom4021
    Fin15AnchoredAtom4022 Fin15AnchoredAtom4026 Fin15AnchoredAtom4030 Fin15AnchoredAtom4791
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

theorem fin15Anchored_clause31849 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3042 chi ∧
      ¬Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom3044 chi ∧
      ¬Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom3051 chi ∧
      ¬Fin15AnchoredAtom3052 chi ∧
      ¬Fin15AnchoredAtom3057 chi ∧
      ¬Fin15AnchoredAtom3059 chi ∧
      ¬Fin15AnchoredAtom3064 chi ∧
      ¬Fin15AnchoredAtom3070 chi ∧
      ¬Fin15AnchoredAtom3087 chi ∧
      ¬Fin15AnchoredAtom3088 chi ∧
      ¬Fin15AnchoredAtom3093 chi ∧
      ¬Fin15AnchoredAtom3095 chi ∧
      ¬Fin15AnchoredAtom3100 chi ∧
      ¬Fin15AnchoredAtom3106 chi ∧
      ¬Fin15AnchoredAtom3123 chi ∧
      ¬Fin15AnchoredAtom3128 chi ∧
      ¬Fin15AnchoredAtom3134 chi ∧
      ¬Fin15AnchoredAtom3155 chi ∧
      ¬Fin15AnchoredAtom3207 chi ∧
      ¬Fin15AnchoredAtom3208 chi ∧
      ¬Fin15AnchoredAtom3213 chi ∧
      ¬Fin15AnchoredAtom3215 chi ∧
      ¬Fin15AnchoredAtom3220 chi ∧
      ¬Fin15AnchoredAtom3226 chi ∧
      ¬Fin15AnchoredAtom3243 chi ∧
      ¬Fin15AnchoredAtom3248 chi ∧
      ¬Fin15AnchoredAtom3254 chi ∧
      ¬Fin15AnchoredAtom3275 chi ∧
      ¬Fin15AnchoredAtom3327 chi ∧
      ¬Fin15AnchoredAtom3332 chi ∧
      ¬Fin15AnchoredAtom3338 chi ∧
      ¬Fin15AnchoredAtom3359 chi ∧
      ¬Fin15AnchoredAtom3415 chi ∧
      ¬Fin15AnchoredAtom4032 chi ∧
      ¬Fin15AnchoredAtom4033 chi ∧
      ¬Fin15AnchoredAtom4038 chi ∧
      ¬Fin15AnchoredAtom4040 chi ∧
      ¬Fin15AnchoredAtom4045 chi ∧
      ¬Fin15AnchoredAtom4051 chi ∧
      ¬Fin15AnchoredAtom4068 chi ∧
      ¬Fin15AnchoredAtom4073 chi ∧
      ¬Fin15AnchoredAtom4079 chi ∧
      ¬Fin15AnchoredAtom4100 chi ∧
      ¬Fin15AnchoredAtom4152 chi ∧
      ¬Fin15AnchoredAtom4157 chi ∧
      ¬Fin15AnchoredAtom4163 chi ∧
      ¬Fin15AnchoredAtom4184 chi ∧
      ¬Fin15AnchoredAtom4240 chi ∧
      ¬Fin15AnchoredAtom4362 chi ∧
      ¬Fin15AnchoredAtom4367 chi ∧
      ¬Fin15AnchoredAtom4373 chi ∧
      ¬Fin15AnchoredAtom4394 chi ∧
      ¬Fin15AnchoredAtom4450 chi ∧
      ¬Fin15AnchoredAtom4576 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 3, 4, 5, 6, 7, 8, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask08698
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3042 Fin15AnchoredAtom3043 Fin15AnchoredAtom3044
    Fin15AnchoredAtom3049 Fin15AnchoredAtom3051 Fin15AnchoredAtom3052 Fin15AnchoredAtom3057
    Fin15AnchoredAtom3059 Fin15AnchoredAtom3064 Fin15AnchoredAtom3070 Fin15AnchoredAtom3087
    Fin15AnchoredAtom3088 Fin15AnchoredAtom3093 Fin15AnchoredAtom3095 Fin15AnchoredAtom3100
    Fin15AnchoredAtom3106 Fin15AnchoredAtom3123 Fin15AnchoredAtom3128 Fin15AnchoredAtom3134
    Fin15AnchoredAtom3155 Fin15AnchoredAtom3207 Fin15AnchoredAtom3208 Fin15AnchoredAtom3213
    Fin15AnchoredAtom3215 Fin15AnchoredAtom3220 Fin15AnchoredAtom3226 Fin15AnchoredAtom3243
    Fin15AnchoredAtom3248 Fin15AnchoredAtom3254 Fin15AnchoredAtom3275 Fin15AnchoredAtom3327
    Fin15AnchoredAtom3332 Fin15AnchoredAtom3338 Fin15AnchoredAtom3359 Fin15AnchoredAtom3415
    Fin15AnchoredAtom4032 Fin15AnchoredAtom4033 Fin15AnchoredAtom4038 Fin15AnchoredAtom4040
    Fin15AnchoredAtom4045 Fin15AnchoredAtom4051 Fin15AnchoredAtom4068 Fin15AnchoredAtom4073
    Fin15AnchoredAtom4079 Fin15AnchoredAtom4100 Fin15AnchoredAtom4152 Fin15AnchoredAtom4157
    Fin15AnchoredAtom4163 Fin15AnchoredAtom4184 Fin15AnchoredAtom4240 Fin15AnchoredAtom4362
    Fin15AnchoredAtom4367 Fin15AnchoredAtom4373 Fin15AnchoredAtom4394 Fin15AnchoredAtom4450
    Fin15AnchoredAtom4576 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause31850 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3042 chi ∧
      ¬Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom3051 chi ∧
      ¬Fin15AnchoredAtom3053 chi ∧
      ¬Fin15AnchoredAtom3054 chi ∧
      ¬Fin15AnchoredAtom3060 chi ∧
      ¬Fin15AnchoredAtom3061 chi ∧
      ¬Fin15AnchoredAtom3072 chi ∧
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
      ¬Fin15AnchoredAtom4032 chi ∧
      ¬Fin15AnchoredAtom4034 chi ∧
      ¬Fin15AnchoredAtom4035 chi ∧
      ¬Fin15AnchoredAtom4041 chi ∧
      ¬Fin15AnchoredAtom4042 chi ∧
      ¬Fin15AnchoredAtom4053 chi ∧
      ¬Fin15AnchoredAtom4069 chi ∧
      ¬Fin15AnchoredAtom4070 chi ∧
      ¬Fin15AnchoredAtom4081 chi ∧
      ¬Fin15AnchoredAtom4102 chi ∧
      ¬Fin15AnchoredAtom4153 chi ∧
      ¬Fin15AnchoredAtom4154 chi ∧
      ¬Fin15AnchoredAtom4165 chi ∧
      ¬Fin15AnchoredAtom4186 chi ∧
      ¬Fin15AnchoredAtom4242 chi ∧
      ¬Fin15AnchoredAtom4363 chi ∧
      ¬Fin15AnchoredAtom4364 chi ∧
      ¬Fin15AnchoredAtom4375 chi ∧
      ¬Fin15AnchoredAtom4396 chi ∧
      ¬Fin15AnchoredAtom4452 chi ∧
      ¬Fin15AnchoredAtom4578 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 3, 4, 5, 6, 7, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask01786
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3042 Fin15AnchoredAtom3043 Fin15AnchoredAtom3045
    Fin15AnchoredAtom3046 Fin15AnchoredAtom3051 Fin15AnchoredAtom3053 Fin15AnchoredAtom3054
    Fin15AnchoredAtom3060 Fin15AnchoredAtom3061 Fin15AnchoredAtom3072 Fin15AnchoredAtom3087
    Fin15AnchoredAtom3089 Fin15AnchoredAtom3090 Fin15AnchoredAtom3096 Fin15AnchoredAtom3097
    Fin15AnchoredAtom3108 Fin15AnchoredAtom3124 Fin15AnchoredAtom3125 Fin15AnchoredAtom3136
    Fin15AnchoredAtom3157 Fin15AnchoredAtom3207 Fin15AnchoredAtom3209 Fin15AnchoredAtom3210
    Fin15AnchoredAtom3216 Fin15AnchoredAtom3217 Fin15AnchoredAtom3228 Fin15AnchoredAtom3244
    Fin15AnchoredAtom3245 Fin15AnchoredAtom3256 Fin15AnchoredAtom3277 Fin15AnchoredAtom3328
    Fin15AnchoredAtom3329 Fin15AnchoredAtom3340 Fin15AnchoredAtom3361 Fin15AnchoredAtom3417
    Fin15AnchoredAtom4032 Fin15AnchoredAtom4034 Fin15AnchoredAtom4035 Fin15AnchoredAtom4041
    Fin15AnchoredAtom4042 Fin15AnchoredAtom4053 Fin15AnchoredAtom4069 Fin15AnchoredAtom4070
    Fin15AnchoredAtom4081 Fin15AnchoredAtom4102 Fin15AnchoredAtom4153 Fin15AnchoredAtom4154
    Fin15AnchoredAtom4165 Fin15AnchoredAtom4186 Fin15AnchoredAtom4242 Fin15AnchoredAtom4363
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

theorem fin15Anchored_clause31851 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3042 chi ∧
      ¬Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom3048 chi ∧
      ¬Fin15AnchoredAtom3051 chi ∧
      ¬Fin15AnchoredAtom3053 chi ∧
      ¬Fin15AnchoredAtom3056 chi ∧
      ¬Fin15AnchoredAtom3060 chi ∧
      ¬Fin15AnchoredAtom3063 chi ∧
      ¬Fin15AnchoredAtom3074 chi ∧
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
      ¬Fin15AnchoredAtom4032 chi ∧
      ¬Fin15AnchoredAtom4034 chi ∧
      ¬Fin15AnchoredAtom4037 chi ∧
      ¬Fin15AnchoredAtom4041 chi ∧
      ¬Fin15AnchoredAtom4044 chi ∧
      ¬Fin15AnchoredAtom4055 chi ∧
      ¬Fin15AnchoredAtom4069 chi ∧
      ¬Fin15AnchoredAtom4072 chi ∧
      ¬Fin15AnchoredAtom4083 chi ∧
      ¬Fin15AnchoredAtom4104 chi ∧
      ¬Fin15AnchoredAtom4153 chi ∧
      ¬Fin15AnchoredAtom4156 chi ∧
      ¬Fin15AnchoredAtom4167 chi ∧
      ¬Fin15AnchoredAtom4188 chi ∧
      ¬Fin15AnchoredAtom4244 chi ∧
      ¬Fin15AnchoredAtom4363 chi ∧
      ¬Fin15AnchoredAtom4366 chi ∧
      ¬Fin15AnchoredAtom4377 chi ∧
      ¬Fin15AnchoredAtom4398 chi ∧
      ¬Fin15AnchoredAtom4454 chi ∧
      ¬Fin15AnchoredAtom4580 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 3, 4, 5, 6, 7, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask04858
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3042 Fin15AnchoredAtom3043 Fin15AnchoredAtom3045
    Fin15AnchoredAtom3048 Fin15AnchoredAtom3051 Fin15AnchoredAtom3053 Fin15AnchoredAtom3056
    Fin15AnchoredAtom3060 Fin15AnchoredAtom3063 Fin15AnchoredAtom3074 Fin15AnchoredAtom3087
    Fin15AnchoredAtom3089 Fin15AnchoredAtom3092 Fin15AnchoredAtom3096 Fin15AnchoredAtom3099
    Fin15AnchoredAtom3110 Fin15AnchoredAtom3124 Fin15AnchoredAtom3127 Fin15AnchoredAtom3138
    Fin15AnchoredAtom3159 Fin15AnchoredAtom3207 Fin15AnchoredAtom3209 Fin15AnchoredAtom3212
    Fin15AnchoredAtom3216 Fin15AnchoredAtom3219 Fin15AnchoredAtom3230 Fin15AnchoredAtom3244
    Fin15AnchoredAtom3247 Fin15AnchoredAtom3258 Fin15AnchoredAtom3279 Fin15AnchoredAtom3328
    Fin15AnchoredAtom3331 Fin15AnchoredAtom3342 Fin15AnchoredAtom3363 Fin15AnchoredAtom3419
    Fin15AnchoredAtom4032 Fin15AnchoredAtom4034 Fin15AnchoredAtom4037 Fin15AnchoredAtom4041
    Fin15AnchoredAtom4044 Fin15AnchoredAtom4055 Fin15AnchoredAtom4069 Fin15AnchoredAtom4072
    Fin15AnchoredAtom4083 Fin15AnchoredAtom4104 Fin15AnchoredAtom4153 Fin15AnchoredAtom4156
    Fin15AnchoredAtom4167 Fin15AnchoredAtom4188 Fin15AnchoredAtom4244 Fin15AnchoredAtom4363
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

theorem fin15Anchored_clause31852 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3042 chi ∧
      ¬Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom3051 chi ∧
      ¬Fin15AnchoredAtom3053 chi ∧
      ¬Fin15AnchoredAtom3057 chi ∧
      ¬Fin15AnchoredAtom3060 chi ∧
      ¬Fin15AnchoredAtom3064 chi ∧
      ¬Fin15AnchoredAtom3075 chi ∧
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
      ¬Fin15AnchoredAtom4032 chi ∧
      ¬Fin15AnchoredAtom4034 chi ∧
      ¬Fin15AnchoredAtom4038 chi ∧
      ¬Fin15AnchoredAtom4041 chi ∧
      ¬Fin15AnchoredAtom4045 chi ∧
      ¬Fin15AnchoredAtom4056 chi ∧
      ¬Fin15AnchoredAtom4069 chi ∧
      ¬Fin15AnchoredAtom4073 chi ∧
      ¬Fin15AnchoredAtom4084 chi ∧
      ¬Fin15AnchoredAtom4105 chi ∧
      ¬Fin15AnchoredAtom4153 chi ∧
      ¬Fin15AnchoredAtom4157 chi ∧
      ¬Fin15AnchoredAtom4168 chi ∧
      ¬Fin15AnchoredAtom4189 chi ∧
      ¬Fin15AnchoredAtom4245 chi ∧
      ¬Fin15AnchoredAtom4363 chi ∧
      ¬Fin15AnchoredAtom4367 chi ∧
      ¬Fin15AnchoredAtom4378 chi ∧
      ¬Fin15AnchoredAtom4399 chi ∧
      ¬Fin15AnchoredAtom4455 chi ∧
      ¬Fin15AnchoredAtom4581 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 3, 4, 5, 6, 7, 9, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask08954
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3042 Fin15AnchoredAtom3043 Fin15AnchoredAtom3045
    Fin15AnchoredAtom3049 Fin15AnchoredAtom3051 Fin15AnchoredAtom3053 Fin15AnchoredAtom3057
    Fin15AnchoredAtom3060 Fin15AnchoredAtom3064 Fin15AnchoredAtom3075 Fin15AnchoredAtom3087
    Fin15AnchoredAtom3089 Fin15AnchoredAtom3093 Fin15AnchoredAtom3096 Fin15AnchoredAtom3100
    Fin15AnchoredAtom3111 Fin15AnchoredAtom3124 Fin15AnchoredAtom3128 Fin15AnchoredAtom3139
    Fin15AnchoredAtom3160 Fin15AnchoredAtom3207 Fin15AnchoredAtom3209 Fin15AnchoredAtom3213
    Fin15AnchoredAtom3216 Fin15AnchoredAtom3220 Fin15AnchoredAtom3231 Fin15AnchoredAtom3244
    Fin15AnchoredAtom3248 Fin15AnchoredAtom3259 Fin15AnchoredAtom3280 Fin15AnchoredAtom3328
    Fin15AnchoredAtom3332 Fin15AnchoredAtom3343 Fin15AnchoredAtom3364 Fin15AnchoredAtom3420
    Fin15AnchoredAtom4032 Fin15AnchoredAtom4034 Fin15AnchoredAtom4038 Fin15AnchoredAtom4041
    Fin15AnchoredAtom4045 Fin15AnchoredAtom4056 Fin15AnchoredAtom4069 Fin15AnchoredAtom4073
    Fin15AnchoredAtom4084 Fin15AnchoredAtom4105 Fin15AnchoredAtom4153 Fin15AnchoredAtom4157
    Fin15AnchoredAtom4168 Fin15AnchoredAtom4189 Fin15AnchoredAtom4245 Fin15AnchoredAtom4363
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

theorem fin15Anchored_clause31853 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3042 chi ∧
      ¬Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom3050 chi ∧
      ¬Fin15AnchoredAtom3051 chi ∧
      ¬Fin15AnchoredAtom3053 chi ∧
      ¬Fin15AnchoredAtom3058 chi ∧
      ¬Fin15AnchoredAtom3060 chi ∧
      ¬Fin15AnchoredAtom3065 chi ∧
      ¬Fin15AnchoredAtom3076 chi ∧
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
      ¬Fin15AnchoredAtom4032 chi ∧
      ¬Fin15AnchoredAtom4034 chi ∧
      ¬Fin15AnchoredAtom4039 chi ∧
      ¬Fin15AnchoredAtom4041 chi ∧
      ¬Fin15AnchoredAtom4046 chi ∧
      ¬Fin15AnchoredAtom4057 chi ∧
      ¬Fin15AnchoredAtom4069 chi ∧
      ¬Fin15AnchoredAtom4074 chi ∧
      ¬Fin15AnchoredAtom4085 chi ∧
      ¬Fin15AnchoredAtom4106 chi ∧
      ¬Fin15AnchoredAtom4153 chi ∧
      ¬Fin15AnchoredAtom4158 chi ∧
      ¬Fin15AnchoredAtom4169 chi ∧
      ¬Fin15AnchoredAtom4190 chi ∧
      ¬Fin15AnchoredAtom4246 chi ∧
      ¬Fin15AnchoredAtom4363 chi ∧
      ¬Fin15AnchoredAtom4368 chi ∧
      ¬Fin15AnchoredAtom4379 chi ∧
      ¬Fin15AnchoredAtom4400 chi ∧
      ¬Fin15AnchoredAtom4456 chi ∧
      ¬Fin15AnchoredAtom4582 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 3, 4, 5, 6, 7, 9, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17146
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3042 Fin15AnchoredAtom3043 Fin15AnchoredAtom3045
    Fin15AnchoredAtom3050 Fin15AnchoredAtom3051 Fin15AnchoredAtom3053 Fin15AnchoredAtom3058
    Fin15AnchoredAtom3060 Fin15AnchoredAtom3065 Fin15AnchoredAtom3076 Fin15AnchoredAtom3087
    Fin15AnchoredAtom3089 Fin15AnchoredAtom3094 Fin15AnchoredAtom3096 Fin15AnchoredAtom3101
    Fin15AnchoredAtom3112 Fin15AnchoredAtom3124 Fin15AnchoredAtom3129 Fin15AnchoredAtom3140
    Fin15AnchoredAtom3161 Fin15AnchoredAtom3207 Fin15AnchoredAtom3209 Fin15AnchoredAtom3214
    Fin15AnchoredAtom3216 Fin15AnchoredAtom3221 Fin15AnchoredAtom3232 Fin15AnchoredAtom3244
    Fin15AnchoredAtom3249 Fin15AnchoredAtom3260 Fin15AnchoredAtom3281 Fin15AnchoredAtom3328
    Fin15AnchoredAtom3333 Fin15AnchoredAtom3344 Fin15AnchoredAtom3365 Fin15AnchoredAtom3421
    Fin15AnchoredAtom4032 Fin15AnchoredAtom4034 Fin15AnchoredAtom4039 Fin15AnchoredAtom4041
    Fin15AnchoredAtom4046 Fin15AnchoredAtom4057 Fin15AnchoredAtom4069 Fin15AnchoredAtom4074
    Fin15AnchoredAtom4085 Fin15AnchoredAtom4106 Fin15AnchoredAtom4153 Fin15AnchoredAtom4158
    Fin15AnchoredAtom4169 Fin15AnchoredAtom4190 Fin15AnchoredAtom4246 Fin15AnchoredAtom4363
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

theorem fin15Anchored_clause31854 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3042 chi ∧
      ¬Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom3048 chi ∧
      ¬Fin15AnchoredAtom3051 chi ∧
      ¬Fin15AnchoredAtom3054 chi ∧
      ¬Fin15AnchoredAtom3056 chi ∧
      ¬Fin15AnchoredAtom3061 chi ∧
      ¬Fin15AnchoredAtom3063 chi ∧
      ¬Fin15AnchoredAtom3078 chi ∧
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
      ¬Fin15AnchoredAtom4032 chi ∧
      ¬Fin15AnchoredAtom4035 chi ∧
      ¬Fin15AnchoredAtom4037 chi ∧
      ¬Fin15AnchoredAtom4042 chi ∧
      ¬Fin15AnchoredAtom4044 chi ∧
      ¬Fin15AnchoredAtom4059 chi ∧
      ¬Fin15AnchoredAtom4070 chi ∧
      ¬Fin15AnchoredAtom4072 chi ∧
      ¬Fin15AnchoredAtom4087 chi ∧
      ¬Fin15AnchoredAtom4108 chi ∧
      ¬Fin15AnchoredAtom4154 chi ∧
      ¬Fin15AnchoredAtom4156 chi ∧
      ¬Fin15AnchoredAtom4171 chi ∧
      ¬Fin15AnchoredAtom4192 chi ∧
      ¬Fin15AnchoredAtom4248 chi ∧
      ¬Fin15AnchoredAtom4364 chi ∧
      ¬Fin15AnchoredAtom4366 chi ∧
      ¬Fin15AnchoredAtom4381 chi ∧
      ¬Fin15AnchoredAtom4402 chi ∧
      ¬Fin15AnchoredAtom4458 chi ∧
      ¬Fin15AnchoredAtom4584 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 3, 4, 5, 6, 7, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05370
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3042 Fin15AnchoredAtom3043 Fin15AnchoredAtom3046
    Fin15AnchoredAtom3048 Fin15AnchoredAtom3051 Fin15AnchoredAtom3054 Fin15AnchoredAtom3056
    Fin15AnchoredAtom3061 Fin15AnchoredAtom3063 Fin15AnchoredAtom3078 Fin15AnchoredAtom3087
    Fin15AnchoredAtom3090 Fin15AnchoredAtom3092 Fin15AnchoredAtom3097 Fin15AnchoredAtom3099
    Fin15AnchoredAtom3114 Fin15AnchoredAtom3125 Fin15AnchoredAtom3127 Fin15AnchoredAtom3142
    Fin15AnchoredAtom3163 Fin15AnchoredAtom3207 Fin15AnchoredAtom3210 Fin15AnchoredAtom3212
    Fin15AnchoredAtom3217 Fin15AnchoredAtom3219 Fin15AnchoredAtom3234 Fin15AnchoredAtom3245
    Fin15AnchoredAtom3247 Fin15AnchoredAtom3262 Fin15AnchoredAtom3283 Fin15AnchoredAtom3329
    Fin15AnchoredAtom3331 Fin15AnchoredAtom3346 Fin15AnchoredAtom3367 Fin15AnchoredAtom3423
    Fin15AnchoredAtom4032 Fin15AnchoredAtom4035 Fin15AnchoredAtom4037 Fin15AnchoredAtom4042
    Fin15AnchoredAtom4044 Fin15AnchoredAtom4059 Fin15AnchoredAtom4070 Fin15AnchoredAtom4072
    Fin15AnchoredAtom4087 Fin15AnchoredAtom4108 Fin15AnchoredAtom4154 Fin15AnchoredAtom4156
    Fin15AnchoredAtom4171 Fin15AnchoredAtom4192 Fin15AnchoredAtom4248 Fin15AnchoredAtom4364
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

theorem fin15Anchored_clause31855 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3042 chi ∧
      ¬Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom3051 chi ∧
      ¬Fin15AnchoredAtom3054 chi ∧
      ¬Fin15AnchoredAtom3057 chi ∧
      ¬Fin15AnchoredAtom3061 chi ∧
      ¬Fin15AnchoredAtom3064 chi ∧
      ¬Fin15AnchoredAtom3079 chi ∧
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
  refine ⟨{1, 3, 4, 5, 6, 7, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09466
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3042 Fin15AnchoredAtom3043 Fin15AnchoredAtom3046
    Fin15AnchoredAtom3049 Fin15AnchoredAtom3051 Fin15AnchoredAtom3054 Fin15AnchoredAtom3057
    Fin15AnchoredAtom3061 Fin15AnchoredAtom3064 Fin15AnchoredAtom3079 Fin15AnchoredAtom3087
    Fin15AnchoredAtom3090 Fin15AnchoredAtom3093 Fin15AnchoredAtom3097 Fin15AnchoredAtom3100
    Fin15AnchoredAtom3115 Fin15AnchoredAtom3125 Fin15AnchoredAtom3128 Fin15AnchoredAtom3143
    Fin15AnchoredAtom3164 Fin15AnchoredAtom3207 Fin15AnchoredAtom3210 Fin15AnchoredAtom3213
    Fin15AnchoredAtom3217 Fin15AnchoredAtom3220 Fin15AnchoredAtom3235 Fin15AnchoredAtom3245
    Fin15AnchoredAtom3248 Fin15AnchoredAtom3263 Fin15AnchoredAtom3284 Fin15AnchoredAtom3329
    Fin15AnchoredAtom3332 Fin15AnchoredAtom3347 Fin15AnchoredAtom3368 Fin15AnchoredAtom3424
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

theorem fin15Anchored_clause31856 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3042 chi ∧
      ¬Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom3050 chi ∧
      ¬Fin15AnchoredAtom3051 chi ∧
      ¬Fin15AnchoredAtom3054 chi ∧
      ¬Fin15AnchoredAtom3058 chi ∧
      ¬Fin15AnchoredAtom3061 chi ∧
      ¬Fin15AnchoredAtom3065 chi ∧
      ¬Fin15AnchoredAtom3080 chi ∧
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
  refine ⟨{1, 3, 4, 5, 6, 7, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17658
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3042 Fin15AnchoredAtom3043 Fin15AnchoredAtom3046
    Fin15AnchoredAtom3050 Fin15AnchoredAtom3051 Fin15AnchoredAtom3054 Fin15AnchoredAtom3058
    Fin15AnchoredAtom3061 Fin15AnchoredAtom3065 Fin15AnchoredAtom3080 Fin15AnchoredAtom3087
    Fin15AnchoredAtom3090 Fin15AnchoredAtom3094 Fin15AnchoredAtom3097 Fin15AnchoredAtom3101
    Fin15AnchoredAtom3116 Fin15AnchoredAtom3125 Fin15AnchoredAtom3129 Fin15AnchoredAtom3144
    Fin15AnchoredAtom3165 Fin15AnchoredAtom3207 Fin15AnchoredAtom3210 Fin15AnchoredAtom3214
    Fin15AnchoredAtom3217 Fin15AnchoredAtom3221 Fin15AnchoredAtom3236 Fin15AnchoredAtom3245
    Fin15AnchoredAtom3249 Fin15AnchoredAtom3264 Fin15AnchoredAtom3285 Fin15AnchoredAtom3329
    Fin15AnchoredAtom3333 Fin15AnchoredAtom3348 Fin15AnchoredAtom3369 Fin15AnchoredAtom3425
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

theorem fin15Anchored_clause31857 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3042 chi ∧
      ¬Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom3048 chi ∧
      ¬Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom3051 chi ∧
      ¬Fin15AnchoredAtom3056 chi ∧
      ¬Fin15AnchoredAtom3057 chi ∧
      ¬Fin15AnchoredAtom3063 chi ∧
      ¬Fin15AnchoredAtom3064 chi ∧
      ¬Fin15AnchoredAtom3084 chi ∧
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
  refine ⟨{1, 3, 4, 5, 6, 7, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask12538
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3042 Fin15AnchoredAtom3043 Fin15AnchoredAtom3048
    Fin15AnchoredAtom3049 Fin15AnchoredAtom3051 Fin15AnchoredAtom3056 Fin15AnchoredAtom3057
    Fin15AnchoredAtom3063 Fin15AnchoredAtom3064 Fin15AnchoredAtom3084 Fin15AnchoredAtom3087
    Fin15AnchoredAtom3092 Fin15AnchoredAtom3093 Fin15AnchoredAtom3099 Fin15AnchoredAtom3100
    Fin15AnchoredAtom3120 Fin15AnchoredAtom3127 Fin15AnchoredAtom3128 Fin15AnchoredAtom3148
    Fin15AnchoredAtom3169 Fin15AnchoredAtom3207 Fin15AnchoredAtom3212 Fin15AnchoredAtom3213
    Fin15AnchoredAtom3219 Fin15AnchoredAtom3220 Fin15AnchoredAtom3240 Fin15AnchoredAtom3247
    Fin15AnchoredAtom3248 Fin15AnchoredAtom3268 Fin15AnchoredAtom3289 Fin15AnchoredAtom3331
    Fin15AnchoredAtom3332 Fin15AnchoredAtom3352 Fin15AnchoredAtom3373 Fin15AnchoredAtom3429
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

theorem fin15Anchored_clause31858 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3042 chi ∧
      ¬Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom3048 chi ∧
      ¬Fin15AnchoredAtom3050 chi ∧
      ¬Fin15AnchoredAtom3051 chi ∧
      ¬Fin15AnchoredAtom3056 chi ∧
      ¬Fin15AnchoredAtom3058 chi ∧
      ¬Fin15AnchoredAtom3063 chi ∧
      ¬Fin15AnchoredAtom3065 chi ∧
      ¬Fin15AnchoredAtom3085 chi ∧
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
  refine ⟨{1, 3, 4, 5, 6, 7, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask20730
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3042 Fin15AnchoredAtom3043 Fin15AnchoredAtom3048
    Fin15AnchoredAtom3050 Fin15AnchoredAtom3051 Fin15AnchoredAtom3056 Fin15AnchoredAtom3058
    Fin15AnchoredAtom3063 Fin15AnchoredAtom3065 Fin15AnchoredAtom3085 Fin15AnchoredAtom3087
    Fin15AnchoredAtom3092 Fin15AnchoredAtom3094 Fin15AnchoredAtom3099 Fin15AnchoredAtom3101
    Fin15AnchoredAtom3121 Fin15AnchoredAtom3127 Fin15AnchoredAtom3129 Fin15AnchoredAtom3149
    Fin15AnchoredAtom3170 Fin15AnchoredAtom3207 Fin15AnchoredAtom3212 Fin15AnchoredAtom3214
    Fin15AnchoredAtom3219 Fin15AnchoredAtom3221 Fin15AnchoredAtom3241 Fin15AnchoredAtom3247
    Fin15AnchoredAtom3249 Fin15AnchoredAtom3269 Fin15AnchoredAtom3290 Fin15AnchoredAtom3331
    Fin15AnchoredAtom3333 Fin15AnchoredAtom3353 Fin15AnchoredAtom3374 Fin15AnchoredAtom3430
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

theorem fin15Anchored_clause31859 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3042 chi ∧
      ¬Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom3050 chi ∧
      ¬Fin15AnchoredAtom3051 chi ∧
      ¬Fin15AnchoredAtom3057 chi ∧
      ¬Fin15AnchoredAtom3058 chi ∧
      ¬Fin15AnchoredAtom3064 chi ∧
      ¬Fin15AnchoredAtom3065 chi ∧
      ¬Fin15AnchoredAtom3086 chi ∧
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
  refine ⟨{1, 3, 4, 5, 6, 7, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask24826
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3042 Fin15AnchoredAtom3043 Fin15AnchoredAtom3049
    Fin15AnchoredAtom3050 Fin15AnchoredAtom3051 Fin15AnchoredAtom3057 Fin15AnchoredAtom3058
    Fin15AnchoredAtom3064 Fin15AnchoredAtom3065 Fin15AnchoredAtom3086 Fin15AnchoredAtom3087
    Fin15AnchoredAtom3093 Fin15AnchoredAtom3094 Fin15AnchoredAtom3100 Fin15AnchoredAtom3101
    Fin15AnchoredAtom3122 Fin15AnchoredAtom3128 Fin15AnchoredAtom3129 Fin15AnchoredAtom3150
    Fin15AnchoredAtom3171 Fin15AnchoredAtom3207 Fin15AnchoredAtom3213 Fin15AnchoredAtom3214
    Fin15AnchoredAtom3220 Fin15AnchoredAtom3221 Fin15AnchoredAtom3242 Fin15AnchoredAtom3248
    Fin15AnchoredAtom3249 Fin15AnchoredAtom3270 Fin15AnchoredAtom3291 Fin15AnchoredAtom3332
    Fin15AnchoredAtom3333 Fin15AnchoredAtom3354 Fin15AnchoredAtom3375 Fin15AnchoredAtom3431
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

theorem fin15Anchored_clause31860 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3042 chi ∧
      ¬Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom3048 chi ∧
      ¬Fin15AnchoredAtom3053 chi ∧
      ¬Fin15AnchoredAtom3054 chi ∧
      ¬Fin15AnchoredAtom3056 chi ∧
      ¬Fin15AnchoredAtom3072 chi ∧
      ¬Fin15AnchoredAtom3074 chi ∧
      ¬Fin15AnchoredAtom3078 chi ∧
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
  refine ⟨{1, 3, 4, 5, 6, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05754
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3042 Fin15AnchoredAtom3045 Fin15AnchoredAtom3046
    Fin15AnchoredAtom3048 Fin15AnchoredAtom3053 Fin15AnchoredAtom3054 Fin15AnchoredAtom3056
    Fin15AnchoredAtom3072 Fin15AnchoredAtom3074 Fin15AnchoredAtom3078 Fin15AnchoredAtom3089
    Fin15AnchoredAtom3090 Fin15AnchoredAtom3092 Fin15AnchoredAtom3108 Fin15AnchoredAtom3110
    Fin15AnchoredAtom3114 Fin15AnchoredAtom3136 Fin15AnchoredAtom3138 Fin15AnchoredAtom3142
    Fin15AnchoredAtom3188 Fin15AnchoredAtom3209 Fin15AnchoredAtom3210 Fin15AnchoredAtom3212
    Fin15AnchoredAtom3228 Fin15AnchoredAtom3230 Fin15AnchoredAtom3234 Fin15AnchoredAtom3256
    Fin15AnchoredAtom3258 Fin15AnchoredAtom3262 Fin15AnchoredAtom3308 Fin15AnchoredAtom3340
    Fin15AnchoredAtom3342 Fin15AnchoredAtom3346 Fin15AnchoredAtom3392 Fin15AnchoredAtom3448
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

theorem fin15Anchored_clause31861 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3042 chi ∧
      ¬Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom3053 chi ∧
      ¬Fin15AnchoredAtom3054 chi ∧
      ¬Fin15AnchoredAtom3057 chi ∧
      ¬Fin15AnchoredAtom3072 chi ∧
      ¬Fin15AnchoredAtom3075 chi ∧
      ¬Fin15AnchoredAtom3079 chi ∧
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
  refine ⟨{1, 3, 4, 5, 6, 9, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09850
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3042 Fin15AnchoredAtom3045 Fin15AnchoredAtom3046
    Fin15AnchoredAtom3049 Fin15AnchoredAtom3053 Fin15AnchoredAtom3054 Fin15AnchoredAtom3057
    Fin15AnchoredAtom3072 Fin15AnchoredAtom3075 Fin15AnchoredAtom3079 Fin15AnchoredAtom3089
    Fin15AnchoredAtom3090 Fin15AnchoredAtom3093 Fin15AnchoredAtom3108 Fin15AnchoredAtom3111
    Fin15AnchoredAtom3115 Fin15AnchoredAtom3136 Fin15AnchoredAtom3139 Fin15AnchoredAtom3143
    Fin15AnchoredAtom3189 Fin15AnchoredAtom3209 Fin15AnchoredAtom3210 Fin15AnchoredAtom3213
    Fin15AnchoredAtom3228 Fin15AnchoredAtom3231 Fin15AnchoredAtom3235 Fin15AnchoredAtom3256
    Fin15AnchoredAtom3259 Fin15AnchoredAtom3263 Fin15AnchoredAtom3309 Fin15AnchoredAtom3340
    Fin15AnchoredAtom3343 Fin15AnchoredAtom3347 Fin15AnchoredAtom3393 Fin15AnchoredAtom3449
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

theorem fin15Anchored_clause31862 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3042 chi ∧
      ¬Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom3050 chi ∧
      ¬Fin15AnchoredAtom3053 chi ∧
      ¬Fin15AnchoredAtom3054 chi ∧
      ¬Fin15AnchoredAtom3058 chi ∧
      ¬Fin15AnchoredAtom3072 chi ∧
      ¬Fin15AnchoredAtom3076 chi ∧
      ¬Fin15AnchoredAtom3080 chi ∧
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
  refine ⟨{1, 3, 4, 5, 6, 9, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask18042
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3042 Fin15AnchoredAtom3045 Fin15AnchoredAtom3046
    Fin15AnchoredAtom3050 Fin15AnchoredAtom3053 Fin15AnchoredAtom3054 Fin15AnchoredAtom3058
    Fin15AnchoredAtom3072 Fin15AnchoredAtom3076 Fin15AnchoredAtom3080 Fin15AnchoredAtom3089
    Fin15AnchoredAtom3090 Fin15AnchoredAtom3094 Fin15AnchoredAtom3108 Fin15AnchoredAtom3112
    Fin15AnchoredAtom3116 Fin15AnchoredAtom3136 Fin15AnchoredAtom3140 Fin15AnchoredAtom3144
    Fin15AnchoredAtom3190 Fin15AnchoredAtom3209 Fin15AnchoredAtom3210 Fin15AnchoredAtom3214
    Fin15AnchoredAtom3228 Fin15AnchoredAtom3232 Fin15AnchoredAtom3236 Fin15AnchoredAtom3256
    Fin15AnchoredAtom3260 Fin15AnchoredAtom3264 Fin15AnchoredAtom3310 Fin15AnchoredAtom3340
    Fin15AnchoredAtom3344 Fin15AnchoredAtom3348 Fin15AnchoredAtom3394 Fin15AnchoredAtom3450
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

theorem fin15Anchored_clause31863 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3042 chi ∧
      ¬Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom3048 chi ∧
      ¬Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom3053 chi ∧
      ¬Fin15AnchoredAtom3056 chi ∧
      ¬Fin15AnchoredAtom3057 chi ∧
      ¬Fin15AnchoredAtom3074 chi ∧
      ¬Fin15AnchoredAtom3075 chi ∧
      ¬Fin15AnchoredAtom3084 chi ∧
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
  refine ⟨{1, 3, 4, 5, 6, 9, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask12922
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3042 Fin15AnchoredAtom3045 Fin15AnchoredAtom3048
    Fin15AnchoredAtom3049 Fin15AnchoredAtom3053 Fin15AnchoredAtom3056 Fin15AnchoredAtom3057
    Fin15AnchoredAtom3074 Fin15AnchoredAtom3075 Fin15AnchoredAtom3084 Fin15AnchoredAtom3089
    Fin15AnchoredAtom3092 Fin15AnchoredAtom3093 Fin15AnchoredAtom3110 Fin15AnchoredAtom3111
    Fin15AnchoredAtom3120 Fin15AnchoredAtom3138 Fin15AnchoredAtom3139 Fin15AnchoredAtom3148
    Fin15AnchoredAtom3194 Fin15AnchoredAtom3209 Fin15AnchoredAtom3212 Fin15AnchoredAtom3213
    Fin15AnchoredAtom3230 Fin15AnchoredAtom3231 Fin15AnchoredAtom3240 Fin15AnchoredAtom3258
    Fin15AnchoredAtom3259 Fin15AnchoredAtom3268 Fin15AnchoredAtom3314 Fin15AnchoredAtom3342
    Fin15AnchoredAtom3343 Fin15AnchoredAtom3352 Fin15AnchoredAtom3398 Fin15AnchoredAtom3454
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

theorem fin15Anchored_clause31864 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3042 chi ∧
      ¬Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom3048 chi ∧
      ¬Fin15AnchoredAtom3050 chi ∧
      ¬Fin15AnchoredAtom3053 chi ∧
      ¬Fin15AnchoredAtom3056 chi ∧
      ¬Fin15AnchoredAtom3058 chi ∧
      ¬Fin15AnchoredAtom3074 chi ∧
      ¬Fin15AnchoredAtom3076 chi ∧
      ¬Fin15AnchoredAtom3085 chi ∧
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
  refine ⟨{1, 3, 4, 5, 6, 9, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21114
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3042 Fin15AnchoredAtom3045 Fin15AnchoredAtom3048
    Fin15AnchoredAtom3050 Fin15AnchoredAtom3053 Fin15AnchoredAtom3056 Fin15AnchoredAtom3058
    Fin15AnchoredAtom3074 Fin15AnchoredAtom3076 Fin15AnchoredAtom3085 Fin15AnchoredAtom3089
    Fin15AnchoredAtom3092 Fin15AnchoredAtom3094 Fin15AnchoredAtom3110 Fin15AnchoredAtom3112
    Fin15AnchoredAtom3121 Fin15AnchoredAtom3138 Fin15AnchoredAtom3140 Fin15AnchoredAtom3149
    Fin15AnchoredAtom3195 Fin15AnchoredAtom3209 Fin15AnchoredAtom3212 Fin15AnchoredAtom3214
    Fin15AnchoredAtom3230 Fin15AnchoredAtom3232 Fin15AnchoredAtom3241 Fin15AnchoredAtom3258
    Fin15AnchoredAtom3260 Fin15AnchoredAtom3269 Fin15AnchoredAtom3315 Fin15AnchoredAtom3342
    Fin15AnchoredAtom3344 Fin15AnchoredAtom3353 Fin15AnchoredAtom3399 Fin15AnchoredAtom3455
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

theorem fin15Anchored_clause31865 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3042 chi ∧
      ¬Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom3050 chi ∧
      ¬Fin15AnchoredAtom3053 chi ∧
      ¬Fin15AnchoredAtom3057 chi ∧
      ¬Fin15AnchoredAtom3058 chi ∧
      ¬Fin15AnchoredAtom3075 chi ∧
      ¬Fin15AnchoredAtom3076 chi ∧
      ¬Fin15AnchoredAtom3086 chi ∧
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
  refine ⟨{1, 3, 4, 5, 6, 9, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25210
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3042 Fin15AnchoredAtom3045 Fin15AnchoredAtom3049
    Fin15AnchoredAtom3050 Fin15AnchoredAtom3053 Fin15AnchoredAtom3057 Fin15AnchoredAtom3058
    Fin15AnchoredAtom3075 Fin15AnchoredAtom3076 Fin15AnchoredAtom3086 Fin15AnchoredAtom3089
    Fin15AnchoredAtom3093 Fin15AnchoredAtom3094 Fin15AnchoredAtom3111 Fin15AnchoredAtom3112
    Fin15AnchoredAtom3122 Fin15AnchoredAtom3139 Fin15AnchoredAtom3140 Fin15AnchoredAtom3150
    Fin15AnchoredAtom3196 Fin15AnchoredAtom3209 Fin15AnchoredAtom3213 Fin15AnchoredAtom3214
    Fin15AnchoredAtom3231 Fin15AnchoredAtom3232 Fin15AnchoredAtom3242 Fin15AnchoredAtom3259
    Fin15AnchoredAtom3260 Fin15AnchoredAtom3270 Fin15AnchoredAtom3316 Fin15AnchoredAtom3343
    Fin15AnchoredAtom3344 Fin15AnchoredAtom3354 Fin15AnchoredAtom3400 Fin15AnchoredAtom3456
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

theorem fin15Anchored_clause31866 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3042 chi ∧
      ¬Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom3048 chi ∧
      ¬Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom3054 chi ∧
      ¬Fin15AnchoredAtom3056 chi ∧
      ¬Fin15AnchoredAtom3057 chi ∧
      ¬Fin15AnchoredAtom3078 chi ∧
      ¬Fin15AnchoredAtom3079 chi ∧
      ¬Fin15AnchoredAtom3084 chi ∧
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
  refine ⟨{1, 3, 4, 5, 6, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13434
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3042 Fin15AnchoredAtom3046 Fin15AnchoredAtom3048
    Fin15AnchoredAtom3049 Fin15AnchoredAtom3054 Fin15AnchoredAtom3056 Fin15AnchoredAtom3057
    Fin15AnchoredAtom3078 Fin15AnchoredAtom3079 Fin15AnchoredAtom3084 Fin15AnchoredAtom3090
    Fin15AnchoredAtom3092 Fin15AnchoredAtom3093 Fin15AnchoredAtom3114 Fin15AnchoredAtom3115
    Fin15AnchoredAtom3120 Fin15AnchoredAtom3142 Fin15AnchoredAtom3143 Fin15AnchoredAtom3148
    Fin15AnchoredAtom3200 Fin15AnchoredAtom3210 Fin15AnchoredAtom3212 Fin15AnchoredAtom3213
    Fin15AnchoredAtom3234 Fin15AnchoredAtom3235 Fin15AnchoredAtom3240 Fin15AnchoredAtom3262
    Fin15AnchoredAtom3263 Fin15AnchoredAtom3268 Fin15AnchoredAtom3320 Fin15AnchoredAtom3346
    Fin15AnchoredAtom3347 Fin15AnchoredAtom3352 Fin15AnchoredAtom3404 Fin15AnchoredAtom3460
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

theorem fin15Anchored_clause31867 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3042 chi ∧
      ¬Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom3048 chi ∧
      ¬Fin15AnchoredAtom3050 chi ∧
      ¬Fin15AnchoredAtom3054 chi ∧
      ¬Fin15AnchoredAtom3056 chi ∧
      ¬Fin15AnchoredAtom3058 chi ∧
      ¬Fin15AnchoredAtom3078 chi ∧
      ¬Fin15AnchoredAtom3080 chi ∧
      ¬Fin15AnchoredAtom3085 chi ∧
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
  refine ⟨{1, 3, 4, 5, 6, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21626
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3042 Fin15AnchoredAtom3046 Fin15AnchoredAtom3048
    Fin15AnchoredAtom3050 Fin15AnchoredAtom3054 Fin15AnchoredAtom3056 Fin15AnchoredAtom3058
    Fin15AnchoredAtom3078 Fin15AnchoredAtom3080 Fin15AnchoredAtom3085 Fin15AnchoredAtom3090
    Fin15AnchoredAtom3092 Fin15AnchoredAtom3094 Fin15AnchoredAtom3114 Fin15AnchoredAtom3116
    Fin15AnchoredAtom3121 Fin15AnchoredAtom3142 Fin15AnchoredAtom3144 Fin15AnchoredAtom3149
    Fin15AnchoredAtom3201 Fin15AnchoredAtom3210 Fin15AnchoredAtom3212 Fin15AnchoredAtom3214
    Fin15AnchoredAtom3234 Fin15AnchoredAtom3236 Fin15AnchoredAtom3241 Fin15AnchoredAtom3262
    Fin15AnchoredAtom3264 Fin15AnchoredAtom3269 Fin15AnchoredAtom3321 Fin15AnchoredAtom3346
    Fin15AnchoredAtom3348 Fin15AnchoredAtom3353 Fin15AnchoredAtom3405 Fin15AnchoredAtom3461
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

theorem fin15Anchored_clause31868 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3042 chi ∧
      ¬Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom3050 chi ∧
      ¬Fin15AnchoredAtom3054 chi ∧
      ¬Fin15AnchoredAtom3057 chi ∧
      ¬Fin15AnchoredAtom3058 chi ∧
      ¬Fin15AnchoredAtom3079 chi ∧
      ¬Fin15AnchoredAtom3080 chi ∧
      ¬Fin15AnchoredAtom3086 chi ∧
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
  refine ⟨{1, 3, 4, 5, 6, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25722
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3042 Fin15AnchoredAtom3046 Fin15AnchoredAtom3049
    Fin15AnchoredAtom3050 Fin15AnchoredAtom3054 Fin15AnchoredAtom3057 Fin15AnchoredAtom3058
    Fin15AnchoredAtom3079 Fin15AnchoredAtom3080 Fin15AnchoredAtom3086 Fin15AnchoredAtom3090
    Fin15AnchoredAtom3093 Fin15AnchoredAtom3094 Fin15AnchoredAtom3115 Fin15AnchoredAtom3116
    Fin15AnchoredAtom3122 Fin15AnchoredAtom3143 Fin15AnchoredAtom3144 Fin15AnchoredAtom3150
    Fin15AnchoredAtom3202 Fin15AnchoredAtom3210 Fin15AnchoredAtom3213 Fin15AnchoredAtom3214
    Fin15AnchoredAtom3235 Fin15AnchoredAtom3236 Fin15AnchoredAtom3242 Fin15AnchoredAtom3263
    Fin15AnchoredAtom3264 Fin15AnchoredAtom3270 Fin15AnchoredAtom3322 Fin15AnchoredAtom3347
    Fin15AnchoredAtom3348 Fin15AnchoredAtom3354 Fin15AnchoredAtom3406 Fin15AnchoredAtom3462
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

theorem fin15Anchored_clause31869 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3042 chi ∧
      ¬Fin15AnchoredAtom3048 chi ∧
      ¬Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom3050 chi ∧
      ¬Fin15AnchoredAtom3056 chi ∧
      ¬Fin15AnchoredAtom3057 chi ∧
      ¬Fin15AnchoredAtom3058 chi ∧
      ¬Fin15AnchoredAtom3084 chi ∧
      ¬Fin15AnchoredAtom3085 chi ∧
      ¬Fin15AnchoredAtom3086 chi ∧
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
  refine ⟨{1, 3, 4, 5, 6, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask28794
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3042 Fin15AnchoredAtom3048 Fin15AnchoredAtom3049
    Fin15AnchoredAtom3050 Fin15AnchoredAtom3056 Fin15AnchoredAtom3057 Fin15AnchoredAtom3058
    Fin15AnchoredAtom3084 Fin15AnchoredAtom3085 Fin15AnchoredAtom3086 Fin15AnchoredAtom3092
    Fin15AnchoredAtom3093 Fin15AnchoredAtom3094 Fin15AnchoredAtom3120 Fin15AnchoredAtom3121
    Fin15AnchoredAtom3122 Fin15AnchoredAtom3148 Fin15AnchoredAtom3149 Fin15AnchoredAtom3150
    Fin15AnchoredAtom3206 Fin15AnchoredAtom3212 Fin15AnchoredAtom3213 Fin15AnchoredAtom3214
    Fin15AnchoredAtom3240 Fin15AnchoredAtom3241 Fin15AnchoredAtom3242 Fin15AnchoredAtom3268
    Fin15AnchoredAtom3269 Fin15AnchoredAtom3270 Fin15AnchoredAtom3326 Fin15AnchoredAtom3352
    Fin15AnchoredAtom3353 Fin15AnchoredAtom3354 Fin15AnchoredAtom3410 Fin15AnchoredAtom3466
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

theorem fin15Anchored_clause31870 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom3044 chi ∧
      ¬Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom3059 chi ∧
      ¬Fin15AnchoredAtom3060 chi ∧
      ¬Fin15AnchoredAtom3064 chi ∧
      ¬Fin15AnchoredAtom3066 chi ∧
      ¬Fin15AnchoredAtom3070 chi ∧
      ¬Fin15AnchoredAtom3075 chi ∧
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
      ¬Fin15AnchoredAtom3215 chi ∧
      ¬Fin15AnchoredAtom3216 chi ∧
      ¬Fin15AnchoredAtom3220 chi ∧
      ¬Fin15AnchoredAtom3222 chi ∧
      ¬Fin15AnchoredAtom3226 chi ∧
      ¬Fin15AnchoredAtom3231 chi ∧
      ¬Fin15AnchoredAtom3271 chi ∧
      ¬Fin15AnchoredAtom3275 chi ∧
      ¬Fin15AnchoredAtom3280 chi ∧
      ¬Fin15AnchoredAtom3295 chi ∧
      ¬Fin15AnchoredAtom3355 chi ∧
      ¬Fin15AnchoredAtom3359 chi ∧
      ¬Fin15AnchoredAtom3364 chi ∧
      ¬Fin15AnchoredAtom3379 chi ∧
      ¬Fin15AnchoredAtom3470 chi ∧
      ¬Fin15AnchoredAtom4040 chi ∧
      ¬Fin15AnchoredAtom4041 chi ∧
      ¬Fin15AnchoredAtom4045 chi ∧
      ¬Fin15AnchoredAtom4047 chi ∧
      ¬Fin15AnchoredAtom4051 chi ∧
      ¬Fin15AnchoredAtom4056 chi ∧
      ¬Fin15AnchoredAtom4096 chi ∧
      ¬Fin15AnchoredAtom4100 chi ∧
      ¬Fin15AnchoredAtom4105 chi ∧
      ¬Fin15AnchoredAtom4120 chi ∧
      ¬Fin15AnchoredAtom4180 chi ∧
      ¬Fin15AnchoredAtom4184 chi ∧
      ¬Fin15AnchoredAtom4189 chi ∧
      ¬Fin15AnchoredAtom4204 chi ∧
      ¬Fin15AnchoredAtom4295 chi ∧
      ¬Fin15AnchoredAtom4390 chi ∧
      ¬Fin15AnchoredAtom4394 chi ∧
      ¬Fin15AnchoredAtom4399 chi ∧
      ¬Fin15AnchoredAtom4414 chi ∧
      ¬Fin15AnchoredAtom4505 chi ∧
      ¬Fin15AnchoredAtom4631 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 3, 4, 5, 7, 8, 9, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09146
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3043 Fin15AnchoredAtom3044 Fin15AnchoredAtom3045
    Fin15AnchoredAtom3049 Fin15AnchoredAtom3059 Fin15AnchoredAtom3060 Fin15AnchoredAtom3064
    Fin15AnchoredAtom3066 Fin15AnchoredAtom3070 Fin15AnchoredAtom3075 Fin15AnchoredAtom3095
    Fin15AnchoredAtom3096 Fin15AnchoredAtom3100 Fin15AnchoredAtom3102 Fin15AnchoredAtom3106
    Fin15AnchoredAtom3111 Fin15AnchoredAtom3151 Fin15AnchoredAtom3155 Fin15AnchoredAtom3160
    Fin15AnchoredAtom3175 Fin15AnchoredAtom3215 Fin15AnchoredAtom3216 Fin15AnchoredAtom3220
    Fin15AnchoredAtom3222 Fin15AnchoredAtom3226 Fin15AnchoredAtom3231 Fin15AnchoredAtom3271
    Fin15AnchoredAtom3275 Fin15AnchoredAtom3280 Fin15AnchoredAtom3295 Fin15AnchoredAtom3355
    Fin15AnchoredAtom3359 Fin15AnchoredAtom3364 Fin15AnchoredAtom3379 Fin15AnchoredAtom3470
    Fin15AnchoredAtom4040 Fin15AnchoredAtom4041 Fin15AnchoredAtom4045 Fin15AnchoredAtom4047
    Fin15AnchoredAtom4051 Fin15AnchoredAtom4056 Fin15AnchoredAtom4096 Fin15AnchoredAtom4100
    Fin15AnchoredAtom4105 Fin15AnchoredAtom4120 Fin15AnchoredAtom4180 Fin15AnchoredAtom4184
    Fin15AnchoredAtom4189 Fin15AnchoredAtom4204 Fin15AnchoredAtom4295 Fin15AnchoredAtom4390
    Fin15AnchoredAtom4394 Fin15AnchoredAtom4399 Fin15AnchoredAtom4414 Fin15AnchoredAtom4505
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

theorem fin15Anchored_clause31871 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom3044 chi ∧
      ¬Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom3059 chi ∧
      ¬Fin15AnchoredAtom3061 chi ∧
      ¬Fin15AnchoredAtom3064 chi ∧
      ¬Fin15AnchoredAtom3067 chi ∧
      ¬Fin15AnchoredAtom3070 chi ∧
      ¬Fin15AnchoredAtom3079 chi ∧
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
      ¬Fin15AnchoredAtom4040 chi ∧
      ¬Fin15AnchoredAtom4042 chi ∧
      ¬Fin15AnchoredAtom4045 chi ∧
      ¬Fin15AnchoredAtom4048 chi ∧
      ¬Fin15AnchoredAtom4051 chi ∧
      ¬Fin15AnchoredAtom4060 chi ∧
      ¬Fin15AnchoredAtom4097 chi ∧
      ¬Fin15AnchoredAtom4100 chi ∧
      ¬Fin15AnchoredAtom4109 chi ∧
      ¬Fin15AnchoredAtom4124 chi ∧
      ¬Fin15AnchoredAtom4181 chi ∧
      ¬Fin15AnchoredAtom4184 chi ∧
      ¬Fin15AnchoredAtom4193 chi ∧
      ¬Fin15AnchoredAtom4208 chi ∧
      ¬Fin15AnchoredAtom4299 chi ∧
      ¬Fin15AnchoredAtom4391 chi ∧
      ¬Fin15AnchoredAtom4394 chi ∧
      ¬Fin15AnchoredAtom4403 chi ∧
      ¬Fin15AnchoredAtom4418 chi ∧
      ¬Fin15AnchoredAtom4509 chi ∧
      ¬Fin15AnchoredAtom4635 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 3, 4, 5, 7, 8, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09658
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3043 Fin15AnchoredAtom3044 Fin15AnchoredAtom3046
    Fin15AnchoredAtom3049 Fin15AnchoredAtom3059 Fin15AnchoredAtom3061 Fin15AnchoredAtom3064
    Fin15AnchoredAtom3067 Fin15AnchoredAtom3070 Fin15AnchoredAtom3079 Fin15AnchoredAtom3095
    Fin15AnchoredAtom3097 Fin15AnchoredAtom3100 Fin15AnchoredAtom3103 Fin15AnchoredAtom3106
    Fin15AnchoredAtom3115 Fin15AnchoredAtom3152 Fin15AnchoredAtom3155 Fin15AnchoredAtom3164
    Fin15AnchoredAtom3179 Fin15AnchoredAtom3215 Fin15AnchoredAtom3217 Fin15AnchoredAtom3220
    Fin15AnchoredAtom3223 Fin15AnchoredAtom3226 Fin15AnchoredAtom3235 Fin15AnchoredAtom3272
    Fin15AnchoredAtom3275 Fin15AnchoredAtom3284 Fin15AnchoredAtom3299 Fin15AnchoredAtom3356
    Fin15AnchoredAtom3359 Fin15AnchoredAtom3368 Fin15AnchoredAtom3383 Fin15AnchoredAtom3474
    Fin15AnchoredAtom4040 Fin15AnchoredAtom4042 Fin15AnchoredAtom4045 Fin15AnchoredAtom4048
    Fin15AnchoredAtom4051 Fin15AnchoredAtom4060 Fin15AnchoredAtom4097 Fin15AnchoredAtom4100
    Fin15AnchoredAtom4109 Fin15AnchoredAtom4124 Fin15AnchoredAtom4181 Fin15AnchoredAtom4184
    Fin15AnchoredAtom4193 Fin15AnchoredAtom4208 Fin15AnchoredAtom4299 Fin15AnchoredAtom4391
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

end ErdosSzekeres

end
