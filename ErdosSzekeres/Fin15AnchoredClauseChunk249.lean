module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 249. -/

theorem fin15Anchored_clause31872 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom3048 chi ∧
      ¬Fin15AnchoredAtom3060 chi ∧
      ¬Fin15AnchoredAtom3061 chi ∧
      ¬Fin15AnchoredAtom3063 chi ∧
      ¬Fin15AnchoredAtom3072 chi ∧
      ¬Fin15AnchoredAtom3074 chi ∧
      ¬Fin15AnchoredAtom3078 chi ∧
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
  refine ⟨{1, 3, 4, 5, 7, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05818
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3043 Fin15AnchoredAtom3045 Fin15AnchoredAtom3046
    Fin15AnchoredAtom3048 Fin15AnchoredAtom3060 Fin15AnchoredAtom3061 Fin15AnchoredAtom3063
    Fin15AnchoredAtom3072 Fin15AnchoredAtom3074 Fin15AnchoredAtom3078 Fin15AnchoredAtom3096
    Fin15AnchoredAtom3097 Fin15AnchoredAtom3099 Fin15AnchoredAtom3108 Fin15AnchoredAtom3110
    Fin15AnchoredAtom3114 Fin15AnchoredAtom3157 Fin15AnchoredAtom3159 Fin15AnchoredAtom3163
    Fin15AnchoredAtom3188 Fin15AnchoredAtom3216 Fin15AnchoredAtom3217 Fin15AnchoredAtom3219
    Fin15AnchoredAtom3228 Fin15AnchoredAtom3230 Fin15AnchoredAtom3234 Fin15AnchoredAtom3277
    Fin15AnchoredAtom3279 Fin15AnchoredAtom3283 Fin15AnchoredAtom3308 Fin15AnchoredAtom3361
    Fin15AnchoredAtom3363 Fin15AnchoredAtom3367 Fin15AnchoredAtom3392 Fin15AnchoredAtom3483
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

theorem fin15Anchored_clause31873 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom3060 chi ∧
      ¬Fin15AnchoredAtom3061 chi ∧
      ¬Fin15AnchoredAtom3064 chi ∧
      ¬Fin15AnchoredAtom3072 chi ∧
      ¬Fin15AnchoredAtom3075 chi ∧
      ¬Fin15AnchoredAtom3079 chi ∧
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
  refine ⟨{1, 3, 4, 5, 7, 9, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09914
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3043 Fin15AnchoredAtom3045 Fin15AnchoredAtom3046
    Fin15AnchoredAtom3049 Fin15AnchoredAtom3060 Fin15AnchoredAtom3061 Fin15AnchoredAtom3064
    Fin15AnchoredAtom3072 Fin15AnchoredAtom3075 Fin15AnchoredAtom3079 Fin15AnchoredAtom3096
    Fin15AnchoredAtom3097 Fin15AnchoredAtom3100 Fin15AnchoredAtom3108 Fin15AnchoredAtom3111
    Fin15AnchoredAtom3115 Fin15AnchoredAtom3157 Fin15AnchoredAtom3160 Fin15AnchoredAtom3164
    Fin15AnchoredAtom3189 Fin15AnchoredAtom3216 Fin15AnchoredAtom3217 Fin15AnchoredAtom3220
    Fin15AnchoredAtom3228 Fin15AnchoredAtom3231 Fin15AnchoredAtom3235 Fin15AnchoredAtom3277
    Fin15AnchoredAtom3280 Fin15AnchoredAtom3284 Fin15AnchoredAtom3309 Fin15AnchoredAtom3361
    Fin15AnchoredAtom3364 Fin15AnchoredAtom3368 Fin15AnchoredAtom3393 Fin15AnchoredAtom3484
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

theorem fin15Anchored_clause31874 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom3050 chi ∧
      ¬Fin15AnchoredAtom3060 chi ∧
      ¬Fin15AnchoredAtom3061 chi ∧
      ¬Fin15AnchoredAtom3065 chi ∧
      ¬Fin15AnchoredAtom3072 chi ∧
      ¬Fin15AnchoredAtom3076 chi ∧
      ¬Fin15AnchoredAtom3080 chi ∧
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
  refine ⟨{1, 3, 4, 5, 7, 9, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask18106
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3043 Fin15AnchoredAtom3045 Fin15AnchoredAtom3046
    Fin15AnchoredAtom3050 Fin15AnchoredAtom3060 Fin15AnchoredAtom3061 Fin15AnchoredAtom3065
    Fin15AnchoredAtom3072 Fin15AnchoredAtom3076 Fin15AnchoredAtom3080 Fin15AnchoredAtom3096
    Fin15AnchoredAtom3097 Fin15AnchoredAtom3101 Fin15AnchoredAtom3108 Fin15AnchoredAtom3112
    Fin15AnchoredAtom3116 Fin15AnchoredAtom3157 Fin15AnchoredAtom3161 Fin15AnchoredAtom3165
    Fin15AnchoredAtom3190 Fin15AnchoredAtom3216 Fin15AnchoredAtom3217 Fin15AnchoredAtom3221
    Fin15AnchoredAtom3228 Fin15AnchoredAtom3232 Fin15AnchoredAtom3236 Fin15AnchoredAtom3277
    Fin15AnchoredAtom3281 Fin15AnchoredAtom3285 Fin15AnchoredAtom3310 Fin15AnchoredAtom3361
    Fin15AnchoredAtom3365 Fin15AnchoredAtom3369 Fin15AnchoredAtom3394 Fin15AnchoredAtom3485
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

theorem fin15Anchored_clause31875 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom3048 chi ∧
      ¬Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom3060 chi ∧
      ¬Fin15AnchoredAtom3063 chi ∧
      ¬Fin15AnchoredAtom3064 chi ∧
      ¬Fin15AnchoredAtom3074 chi ∧
      ¬Fin15AnchoredAtom3075 chi ∧
      ¬Fin15AnchoredAtom3084 chi ∧
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
  refine ⟨{1, 3, 4, 5, 7, 9, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask12986
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3043 Fin15AnchoredAtom3045 Fin15AnchoredAtom3048
    Fin15AnchoredAtom3049 Fin15AnchoredAtom3060 Fin15AnchoredAtom3063 Fin15AnchoredAtom3064
    Fin15AnchoredAtom3074 Fin15AnchoredAtom3075 Fin15AnchoredAtom3084 Fin15AnchoredAtom3096
    Fin15AnchoredAtom3099 Fin15AnchoredAtom3100 Fin15AnchoredAtom3110 Fin15AnchoredAtom3111
    Fin15AnchoredAtom3120 Fin15AnchoredAtom3159 Fin15AnchoredAtom3160 Fin15AnchoredAtom3169
    Fin15AnchoredAtom3194 Fin15AnchoredAtom3216 Fin15AnchoredAtom3219 Fin15AnchoredAtom3220
    Fin15AnchoredAtom3230 Fin15AnchoredAtom3231 Fin15AnchoredAtom3240 Fin15AnchoredAtom3279
    Fin15AnchoredAtom3280 Fin15AnchoredAtom3289 Fin15AnchoredAtom3314 Fin15AnchoredAtom3363
    Fin15AnchoredAtom3364 Fin15AnchoredAtom3373 Fin15AnchoredAtom3398 Fin15AnchoredAtom3489
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

theorem fin15Anchored_clause31876 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom3048 chi ∧
      ¬Fin15AnchoredAtom3050 chi ∧
      ¬Fin15AnchoredAtom3060 chi ∧
      ¬Fin15AnchoredAtom3063 chi ∧
      ¬Fin15AnchoredAtom3065 chi ∧
      ¬Fin15AnchoredAtom3074 chi ∧
      ¬Fin15AnchoredAtom3076 chi ∧
      ¬Fin15AnchoredAtom3085 chi ∧
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
  refine ⟨{1, 3, 4, 5, 7, 9, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21178
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3043 Fin15AnchoredAtom3045 Fin15AnchoredAtom3048
    Fin15AnchoredAtom3050 Fin15AnchoredAtom3060 Fin15AnchoredAtom3063 Fin15AnchoredAtom3065
    Fin15AnchoredAtom3074 Fin15AnchoredAtom3076 Fin15AnchoredAtom3085 Fin15AnchoredAtom3096
    Fin15AnchoredAtom3099 Fin15AnchoredAtom3101 Fin15AnchoredAtom3110 Fin15AnchoredAtom3112
    Fin15AnchoredAtom3121 Fin15AnchoredAtom3159 Fin15AnchoredAtom3161 Fin15AnchoredAtom3170
    Fin15AnchoredAtom3195 Fin15AnchoredAtom3216 Fin15AnchoredAtom3219 Fin15AnchoredAtom3221
    Fin15AnchoredAtom3230 Fin15AnchoredAtom3232 Fin15AnchoredAtom3241 Fin15AnchoredAtom3279
    Fin15AnchoredAtom3281 Fin15AnchoredAtom3290 Fin15AnchoredAtom3315 Fin15AnchoredAtom3363
    Fin15AnchoredAtom3365 Fin15AnchoredAtom3374 Fin15AnchoredAtom3399 Fin15AnchoredAtom3490
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

theorem fin15Anchored_clause31877 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom3050 chi ∧
      ¬Fin15AnchoredAtom3060 chi ∧
      ¬Fin15AnchoredAtom3064 chi ∧
      ¬Fin15AnchoredAtom3065 chi ∧
      ¬Fin15AnchoredAtom3075 chi ∧
      ¬Fin15AnchoredAtom3076 chi ∧
      ¬Fin15AnchoredAtom3086 chi ∧
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
  refine ⟨{1, 3, 4, 5, 7, 9, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25274
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3043 Fin15AnchoredAtom3045 Fin15AnchoredAtom3049
    Fin15AnchoredAtom3050 Fin15AnchoredAtom3060 Fin15AnchoredAtom3064 Fin15AnchoredAtom3065
    Fin15AnchoredAtom3075 Fin15AnchoredAtom3076 Fin15AnchoredAtom3086 Fin15AnchoredAtom3096
    Fin15AnchoredAtom3100 Fin15AnchoredAtom3101 Fin15AnchoredAtom3111 Fin15AnchoredAtom3112
    Fin15AnchoredAtom3122 Fin15AnchoredAtom3160 Fin15AnchoredAtom3161 Fin15AnchoredAtom3171
    Fin15AnchoredAtom3196 Fin15AnchoredAtom3216 Fin15AnchoredAtom3220 Fin15AnchoredAtom3221
    Fin15AnchoredAtom3231 Fin15AnchoredAtom3232 Fin15AnchoredAtom3242 Fin15AnchoredAtom3280
    Fin15AnchoredAtom3281 Fin15AnchoredAtom3291 Fin15AnchoredAtom3316 Fin15AnchoredAtom3364
    Fin15AnchoredAtom3365 Fin15AnchoredAtom3375 Fin15AnchoredAtom3400 Fin15AnchoredAtom3491
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

theorem fin15Anchored_clause31878 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom3048 chi ∧
      ¬Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom3061 chi ∧
      ¬Fin15AnchoredAtom3063 chi ∧
      ¬Fin15AnchoredAtom3064 chi ∧
      ¬Fin15AnchoredAtom3078 chi ∧
      ¬Fin15AnchoredAtom3079 chi ∧
      ¬Fin15AnchoredAtom3084 chi ∧
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
  refine ⟨{1, 3, 4, 5, 7, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13498
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3043 Fin15AnchoredAtom3046 Fin15AnchoredAtom3048
    Fin15AnchoredAtom3049 Fin15AnchoredAtom3061 Fin15AnchoredAtom3063 Fin15AnchoredAtom3064
    Fin15AnchoredAtom3078 Fin15AnchoredAtom3079 Fin15AnchoredAtom3084 Fin15AnchoredAtom3097
    Fin15AnchoredAtom3099 Fin15AnchoredAtom3100 Fin15AnchoredAtom3114 Fin15AnchoredAtom3115
    Fin15AnchoredAtom3120 Fin15AnchoredAtom3163 Fin15AnchoredAtom3164 Fin15AnchoredAtom3169
    Fin15AnchoredAtom3200 Fin15AnchoredAtom3217 Fin15AnchoredAtom3219 Fin15AnchoredAtom3220
    Fin15AnchoredAtom3234 Fin15AnchoredAtom3235 Fin15AnchoredAtom3240 Fin15AnchoredAtom3283
    Fin15AnchoredAtom3284 Fin15AnchoredAtom3289 Fin15AnchoredAtom3320 Fin15AnchoredAtom3367
    Fin15AnchoredAtom3368 Fin15AnchoredAtom3373 Fin15AnchoredAtom3404 Fin15AnchoredAtom3495
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

theorem fin15Anchored_clause31879 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom3048 chi ∧
      ¬Fin15AnchoredAtom3050 chi ∧
      ¬Fin15AnchoredAtom3061 chi ∧
      ¬Fin15AnchoredAtom3063 chi ∧
      ¬Fin15AnchoredAtom3065 chi ∧
      ¬Fin15AnchoredAtom3078 chi ∧
      ¬Fin15AnchoredAtom3080 chi ∧
      ¬Fin15AnchoredAtom3085 chi ∧
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
  refine ⟨{1, 3, 4, 5, 7, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21690
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3043 Fin15AnchoredAtom3046 Fin15AnchoredAtom3048
    Fin15AnchoredAtom3050 Fin15AnchoredAtom3061 Fin15AnchoredAtom3063 Fin15AnchoredAtom3065
    Fin15AnchoredAtom3078 Fin15AnchoredAtom3080 Fin15AnchoredAtom3085 Fin15AnchoredAtom3097
    Fin15AnchoredAtom3099 Fin15AnchoredAtom3101 Fin15AnchoredAtom3114 Fin15AnchoredAtom3116
    Fin15AnchoredAtom3121 Fin15AnchoredAtom3163 Fin15AnchoredAtom3165 Fin15AnchoredAtom3170
    Fin15AnchoredAtom3201 Fin15AnchoredAtom3217 Fin15AnchoredAtom3219 Fin15AnchoredAtom3221
    Fin15AnchoredAtom3234 Fin15AnchoredAtom3236 Fin15AnchoredAtom3241 Fin15AnchoredAtom3283
    Fin15AnchoredAtom3285 Fin15AnchoredAtom3290 Fin15AnchoredAtom3321 Fin15AnchoredAtom3367
    Fin15AnchoredAtom3369 Fin15AnchoredAtom3374 Fin15AnchoredAtom3405 Fin15AnchoredAtom3496
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

theorem fin15Anchored_clause31880 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom3050 chi ∧
      ¬Fin15AnchoredAtom3061 chi ∧
      ¬Fin15AnchoredAtom3064 chi ∧
      ¬Fin15AnchoredAtom3065 chi ∧
      ¬Fin15AnchoredAtom3079 chi ∧
      ¬Fin15AnchoredAtom3080 chi ∧
      ¬Fin15AnchoredAtom3086 chi ∧
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
  refine ⟨{1, 3, 4, 5, 7, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25786
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3043 Fin15AnchoredAtom3046 Fin15AnchoredAtom3049
    Fin15AnchoredAtom3050 Fin15AnchoredAtom3061 Fin15AnchoredAtom3064 Fin15AnchoredAtom3065
    Fin15AnchoredAtom3079 Fin15AnchoredAtom3080 Fin15AnchoredAtom3086 Fin15AnchoredAtom3097
    Fin15AnchoredAtom3100 Fin15AnchoredAtom3101 Fin15AnchoredAtom3115 Fin15AnchoredAtom3116
    Fin15AnchoredAtom3122 Fin15AnchoredAtom3164 Fin15AnchoredAtom3165 Fin15AnchoredAtom3171
    Fin15AnchoredAtom3202 Fin15AnchoredAtom3217 Fin15AnchoredAtom3220 Fin15AnchoredAtom3221
    Fin15AnchoredAtom3235 Fin15AnchoredAtom3236 Fin15AnchoredAtom3242 Fin15AnchoredAtom3284
    Fin15AnchoredAtom3285 Fin15AnchoredAtom3291 Fin15AnchoredAtom3322 Fin15AnchoredAtom3368
    Fin15AnchoredAtom3369 Fin15AnchoredAtom3375 Fin15AnchoredAtom3406 Fin15AnchoredAtom3497
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

theorem fin15Anchored_clause31881 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom3048 chi ∧
      ¬Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom3050 chi ∧
      ¬Fin15AnchoredAtom3063 chi ∧
      ¬Fin15AnchoredAtom3064 chi ∧
      ¬Fin15AnchoredAtom3065 chi ∧
      ¬Fin15AnchoredAtom3084 chi ∧
      ¬Fin15AnchoredAtom3085 chi ∧
      ¬Fin15AnchoredAtom3086 chi ∧
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
  refine ⟨{1, 3, 4, 5, 7, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask28858
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3043 Fin15AnchoredAtom3048 Fin15AnchoredAtom3049
    Fin15AnchoredAtom3050 Fin15AnchoredAtom3063 Fin15AnchoredAtom3064 Fin15AnchoredAtom3065
    Fin15AnchoredAtom3084 Fin15AnchoredAtom3085 Fin15AnchoredAtom3086 Fin15AnchoredAtom3099
    Fin15AnchoredAtom3100 Fin15AnchoredAtom3101 Fin15AnchoredAtom3120 Fin15AnchoredAtom3121
    Fin15AnchoredAtom3122 Fin15AnchoredAtom3169 Fin15AnchoredAtom3170 Fin15AnchoredAtom3171
    Fin15AnchoredAtom3206 Fin15AnchoredAtom3219 Fin15AnchoredAtom3220 Fin15AnchoredAtom3221
    Fin15AnchoredAtom3240 Fin15AnchoredAtom3241 Fin15AnchoredAtom3242 Fin15AnchoredAtom3289
    Fin15AnchoredAtom3290 Fin15AnchoredAtom3291 Fin15AnchoredAtom3326 Fin15AnchoredAtom3373
    Fin15AnchoredAtom3374 Fin15AnchoredAtom3375 Fin15AnchoredAtom3410 Fin15AnchoredAtom3501
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

theorem fin15Anchored_clause31882 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3044 chi ∧
      ¬Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom3066 chi ∧
      ¬Fin15AnchoredAtom3067 chi ∧
      ¬Fin15AnchoredAtom3070 chi ∧
      ¬Fin15AnchoredAtom3072 chi ∧
      ¬Fin15AnchoredAtom3075 chi ∧
      ¬Fin15AnchoredAtom3079 chi ∧
      ¬Fin15AnchoredAtom3102 chi ∧
      ¬Fin15AnchoredAtom3103 chi ∧
      ¬Fin15AnchoredAtom3106 chi ∧
      ¬Fin15AnchoredAtom3108 chi ∧
      ¬Fin15AnchoredAtom3111 chi ∧
      ¬Fin15AnchoredAtom3115 chi ∧
      ¬Fin15AnchoredAtom3172 chi ∧
      ¬Fin15AnchoredAtom3175 chi ∧
      ¬Fin15AnchoredAtom3179 chi ∧
      ¬Fin15AnchoredAtom3189 chi ∧
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
      ¬Fin15AnchoredAtom4047 chi ∧
      ¬Fin15AnchoredAtom4048 chi ∧
      ¬Fin15AnchoredAtom4051 chi ∧
      ¬Fin15AnchoredAtom4053 chi ∧
      ¬Fin15AnchoredAtom4056 chi ∧
      ¬Fin15AnchoredAtom4060 chi ∧
      ¬Fin15AnchoredAtom4117 chi ∧
      ¬Fin15AnchoredAtom4120 chi ∧
      ¬Fin15AnchoredAtom4124 chi ∧
      ¬Fin15AnchoredAtom4134 chi ∧
      ¬Fin15AnchoredAtom4201 chi ∧
      ¬Fin15AnchoredAtom4204 chi ∧
      ¬Fin15AnchoredAtom4208 chi ∧
      ¬Fin15AnchoredAtom4218 chi ∧
      ¬Fin15AnchoredAtom4329 chi ∧
      ¬Fin15AnchoredAtom4411 chi ∧
      ¬Fin15AnchoredAtom4414 chi ∧
      ¬Fin15AnchoredAtom4418 chi ∧
      ¬Fin15AnchoredAtom4428 chi ∧
      ¬Fin15AnchoredAtom4539 chi ∧
      ¬Fin15AnchoredAtom4665 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 3, 4, 5, 8, 9, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask10042
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3044 Fin15AnchoredAtom3045 Fin15AnchoredAtom3046
    Fin15AnchoredAtom3049 Fin15AnchoredAtom3066 Fin15AnchoredAtom3067 Fin15AnchoredAtom3070
    Fin15AnchoredAtom3072 Fin15AnchoredAtom3075 Fin15AnchoredAtom3079 Fin15AnchoredAtom3102
    Fin15AnchoredAtom3103 Fin15AnchoredAtom3106 Fin15AnchoredAtom3108 Fin15AnchoredAtom3111
    Fin15AnchoredAtom3115 Fin15AnchoredAtom3172 Fin15AnchoredAtom3175 Fin15AnchoredAtom3179
    Fin15AnchoredAtom3189 Fin15AnchoredAtom3222 Fin15AnchoredAtom3223 Fin15AnchoredAtom3226
    Fin15AnchoredAtom3228 Fin15AnchoredAtom3231 Fin15AnchoredAtom3235 Fin15AnchoredAtom3292
    Fin15AnchoredAtom3295 Fin15AnchoredAtom3299 Fin15AnchoredAtom3309 Fin15AnchoredAtom3376
    Fin15AnchoredAtom3379 Fin15AnchoredAtom3383 Fin15AnchoredAtom3393 Fin15AnchoredAtom3504
    Fin15AnchoredAtom4047 Fin15AnchoredAtom4048 Fin15AnchoredAtom4051 Fin15AnchoredAtom4053
    Fin15AnchoredAtom4056 Fin15AnchoredAtom4060 Fin15AnchoredAtom4117 Fin15AnchoredAtom4120
    Fin15AnchoredAtom4124 Fin15AnchoredAtom4134 Fin15AnchoredAtom4201 Fin15AnchoredAtom4204
    Fin15AnchoredAtom4208 Fin15AnchoredAtom4218 Fin15AnchoredAtom4329 Fin15AnchoredAtom4411
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

theorem fin15Anchored_clause31883 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3044 chi ∧
      ¬Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom3050 chi ∧
      ¬Fin15AnchoredAtom3066 chi ∧
      ¬Fin15AnchoredAtom3070 chi ∧
      ¬Fin15AnchoredAtom3071 chi ∧
      ¬Fin15AnchoredAtom3075 chi ∧
      ¬Fin15AnchoredAtom3076 chi ∧
      ¬Fin15AnchoredAtom3086 chi ∧
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
      ¬Fin15AnchoredAtom3222 chi ∧
      ¬Fin15AnchoredAtom3226 chi ∧
      ¬Fin15AnchoredAtom3227 chi ∧
      ¬Fin15AnchoredAtom3231 chi ∧
      ¬Fin15AnchoredAtom3232 chi ∧
      ¬Fin15AnchoredAtom3242 chi ∧
      ¬Fin15AnchoredAtom3295 chi ∧
      ¬Fin15AnchoredAtom3296 chi ∧
      ¬Fin15AnchoredAtom3306 chi ∧
      ¬Fin15AnchoredAtom3316 chi ∧
      ¬Fin15AnchoredAtom3379 chi ∧
      ¬Fin15AnchoredAtom3380 chi ∧
      ¬Fin15AnchoredAtom3390 chi ∧
      ¬Fin15AnchoredAtom3400 chi ∧
      ¬Fin15AnchoredAtom3511 chi ∧
      ¬Fin15AnchoredAtom4047 chi ∧
      ¬Fin15AnchoredAtom4051 chi ∧
      ¬Fin15AnchoredAtom4052 chi ∧
      ¬Fin15AnchoredAtom4056 chi ∧
      ¬Fin15AnchoredAtom4057 chi ∧
      ¬Fin15AnchoredAtom4067 chi ∧
      ¬Fin15AnchoredAtom4120 chi ∧
      ¬Fin15AnchoredAtom4121 chi ∧
      ¬Fin15AnchoredAtom4131 chi ∧
      ¬Fin15AnchoredAtom4141 chi ∧
      ¬Fin15AnchoredAtom4204 chi ∧
      ¬Fin15AnchoredAtom4205 chi ∧
      ¬Fin15AnchoredAtom4215 chi ∧
      ¬Fin15AnchoredAtom4225 chi ∧
      ¬Fin15AnchoredAtom4336 chi ∧
      ¬Fin15AnchoredAtom4414 chi ∧
      ¬Fin15AnchoredAtom4415 chi ∧
      ¬Fin15AnchoredAtom4425 chi ∧
      ¬Fin15AnchoredAtom4435 chi ∧
      ¬Fin15AnchoredAtom4546 chi ∧
      ¬Fin15AnchoredAtom4672 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 3, 4, 5, 8, 9, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25402
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3044 Fin15AnchoredAtom3045 Fin15AnchoredAtom3049
    Fin15AnchoredAtom3050 Fin15AnchoredAtom3066 Fin15AnchoredAtom3070 Fin15AnchoredAtom3071
    Fin15AnchoredAtom3075 Fin15AnchoredAtom3076 Fin15AnchoredAtom3086 Fin15AnchoredAtom3102
    Fin15AnchoredAtom3106 Fin15AnchoredAtom3107 Fin15AnchoredAtom3111 Fin15AnchoredAtom3112
    Fin15AnchoredAtom3122 Fin15AnchoredAtom3175 Fin15AnchoredAtom3176 Fin15AnchoredAtom3186
    Fin15AnchoredAtom3196 Fin15AnchoredAtom3222 Fin15AnchoredAtom3226 Fin15AnchoredAtom3227
    Fin15AnchoredAtom3231 Fin15AnchoredAtom3232 Fin15AnchoredAtom3242 Fin15AnchoredAtom3295
    Fin15AnchoredAtom3296 Fin15AnchoredAtom3306 Fin15AnchoredAtom3316 Fin15AnchoredAtom3379
    Fin15AnchoredAtom3380 Fin15AnchoredAtom3390 Fin15AnchoredAtom3400 Fin15AnchoredAtom3511
    Fin15AnchoredAtom4047 Fin15AnchoredAtom4051 Fin15AnchoredAtom4052 Fin15AnchoredAtom4056
    Fin15AnchoredAtom4057 Fin15AnchoredAtom4067 Fin15AnchoredAtom4120 Fin15AnchoredAtom4121
    Fin15AnchoredAtom4131 Fin15AnchoredAtom4141 Fin15AnchoredAtom4204 Fin15AnchoredAtom4205
    Fin15AnchoredAtom4215 Fin15AnchoredAtom4225 Fin15AnchoredAtom4336 Fin15AnchoredAtom4414
    Fin15AnchoredAtom4415 Fin15AnchoredAtom4425 Fin15AnchoredAtom4435 Fin15AnchoredAtom4546
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

theorem fin15Anchored_clause31884 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom3048 chi ∧
      ¬Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom3072 chi ∧
      ¬Fin15AnchoredAtom3074 chi ∧
      ¬Fin15AnchoredAtom3075 chi ∧
      ¬Fin15AnchoredAtom3078 chi ∧
      ¬Fin15AnchoredAtom3079 chi ∧
      ¬Fin15AnchoredAtom3084 chi ∧
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
  refine ⟨{1, 3, 4, 5, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13882
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3045 Fin15AnchoredAtom3046 Fin15AnchoredAtom3048
    Fin15AnchoredAtom3049 Fin15AnchoredAtom3072 Fin15AnchoredAtom3074 Fin15AnchoredAtom3075
    Fin15AnchoredAtom3078 Fin15AnchoredAtom3079 Fin15AnchoredAtom3084 Fin15AnchoredAtom3108
    Fin15AnchoredAtom3110 Fin15AnchoredAtom3111 Fin15AnchoredAtom3114 Fin15AnchoredAtom3115
    Fin15AnchoredAtom3120 Fin15AnchoredAtom3188 Fin15AnchoredAtom3189 Fin15AnchoredAtom3194
    Fin15AnchoredAtom3200 Fin15AnchoredAtom3228 Fin15AnchoredAtom3230 Fin15AnchoredAtom3231
    Fin15AnchoredAtom3234 Fin15AnchoredAtom3235 Fin15AnchoredAtom3240 Fin15AnchoredAtom3308
    Fin15AnchoredAtom3309 Fin15AnchoredAtom3314 Fin15AnchoredAtom3320 Fin15AnchoredAtom3392
    Fin15AnchoredAtom3393 Fin15AnchoredAtom3398 Fin15AnchoredAtom3404 Fin15AnchoredAtom3525
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

theorem fin15Anchored_clause31885 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom3048 chi ∧
      ¬Fin15AnchoredAtom3050 chi ∧
      ¬Fin15AnchoredAtom3072 chi ∧
      ¬Fin15AnchoredAtom3074 chi ∧
      ¬Fin15AnchoredAtom3076 chi ∧
      ¬Fin15AnchoredAtom3078 chi ∧
      ¬Fin15AnchoredAtom3080 chi ∧
      ¬Fin15AnchoredAtom3085 chi ∧
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
  refine ⟨{1, 3, 4, 5, 9, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22074
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3045 Fin15AnchoredAtom3046 Fin15AnchoredAtom3048
    Fin15AnchoredAtom3050 Fin15AnchoredAtom3072 Fin15AnchoredAtom3074 Fin15AnchoredAtom3076
    Fin15AnchoredAtom3078 Fin15AnchoredAtom3080 Fin15AnchoredAtom3085 Fin15AnchoredAtom3108
    Fin15AnchoredAtom3110 Fin15AnchoredAtom3112 Fin15AnchoredAtom3114 Fin15AnchoredAtom3116
    Fin15AnchoredAtom3121 Fin15AnchoredAtom3188 Fin15AnchoredAtom3190 Fin15AnchoredAtom3195
    Fin15AnchoredAtom3201 Fin15AnchoredAtom3228 Fin15AnchoredAtom3230 Fin15AnchoredAtom3232
    Fin15AnchoredAtom3234 Fin15AnchoredAtom3236 Fin15AnchoredAtom3241 Fin15AnchoredAtom3308
    Fin15AnchoredAtom3310 Fin15AnchoredAtom3315 Fin15AnchoredAtom3321 Fin15AnchoredAtom3392
    Fin15AnchoredAtom3394 Fin15AnchoredAtom3399 Fin15AnchoredAtom3405 Fin15AnchoredAtom3526
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

theorem fin15Anchored_clause31886 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom3050 chi ∧
      ¬Fin15AnchoredAtom3072 chi ∧
      ¬Fin15AnchoredAtom3075 chi ∧
      ¬Fin15AnchoredAtom3076 chi ∧
      ¬Fin15AnchoredAtom3079 chi ∧
      ¬Fin15AnchoredAtom3080 chi ∧
      ¬Fin15AnchoredAtom3086 chi ∧
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
  refine ⟨{1, 3, 4, 5, 9, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26170
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3045 Fin15AnchoredAtom3046 Fin15AnchoredAtom3049
    Fin15AnchoredAtom3050 Fin15AnchoredAtom3072 Fin15AnchoredAtom3075 Fin15AnchoredAtom3076
    Fin15AnchoredAtom3079 Fin15AnchoredAtom3080 Fin15AnchoredAtom3086 Fin15AnchoredAtom3108
    Fin15AnchoredAtom3111 Fin15AnchoredAtom3112 Fin15AnchoredAtom3115 Fin15AnchoredAtom3116
    Fin15AnchoredAtom3122 Fin15AnchoredAtom3189 Fin15AnchoredAtom3190 Fin15AnchoredAtom3196
    Fin15AnchoredAtom3202 Fin15AnchoredAtom3228 Fin15AnchoredAtom3231 Fin15AnchoredAtom3232
    Fin15AnchoredAtom3235 Fin15AnchoredAtom3236 Fin15AnchoredAtom3242 Fin15AnchoredAtom3309
    Fin15AnchoredAtom3310 Fin15AnchoredAtom3316 Fin15AnchoredAtom3322 Fin15AnchoredAtom3393
    Fin15AnchoredAtom3394 Fin15AnchoredAtom3400 Fin15AnchoredAtom3406 Fin15AnchoredAtom3527
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

theorem fin15Anchored_clause31887 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom3048 chi ∧
      ¬Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom3050 chi ∧
      ¬Fin15AnchoredAtom3074 chi ∧
      ¬Fin15AnchoredAtom3075 chi ∧
      ¬Fin15AnchoredAtom3076 chi ∧
      ¬Fin15AnchoredAtom3084 chi ∧
      ¬Fin15AnchoredAtom3085 chi ∧
      ¬Fin15AnchoredAtom3086 chi ∧
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
  refine ⟨{1, 3, 4, 5, 9, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29242
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3045 Fin15AnchoredAtom3048 Fin15AnchoredAtom3049
    Fin15AnchoredAtom3050 Fin15AnchoredAtom3074 Fin15AnchoredAtom3075 Fin15AnchoredAtom3076
    Fin15AnchoredAtom3084 Fin15AnchoredAtom3085 Fin15AnchoredAtom3086 Fin15AnchoredAtom3110
    Fin15AnchoredAtom3111 Fin15AnchoredAtom3112 Fin15AnchoredAtom3120 Fin15AnchoredAtom3121
    Fin15AnchoredAtom3122 Fin15AnchoredAtom3194 Fin15AnchoredAtom3195 Fin15AnchoredAtom3196
    Fin15AnchoredAtom3206 Fin15AnchoredAtom3230 Fin15AnchoredAtom3231 Fin15AnchoredAtom3232
    Fin15AnchoredAtom3240 Fin15AnchoredAtom3241 Fin15AnchoredAtom3242 Fin15AnchoredAtom3314
    Fin15AnchoredAtom3315 Fin15AnchoredAtom3316 Fin15AnchoredAtom3326 Fin15AnchoredAtom3398
    Fin15AnchoredAtom3399 Fin15AnchoredAtom3400 Fin15AnchoredAtom3410 Fin15AnchoredAtom3531
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

theorem fin15Anchored_clause31888 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom3048 chi ∧
      ¬Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom3050 chi ∧
      ¬Fin15AnchoredAtom3078 chi ∧
      ¬Fin15AnchoredAtom3079 chi ∧
      ¬Fin15AnchoredAtom3080 chi ∧
      ¬Fin15AnchoredAtom3084 chi ∧
      ¬Fin15AnchoredAtom3085 chi ∧
      ¬Fin15AnchoredAtom3086 chi ∧
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
  refine ⟨{1, 3, 4, 5, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29754
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3046 Fin15AnchoredAtom3048 Fin15AnchoredAtom3049
    Fin15AnchoredAtom3050 Fin15AnchoredAtom3078 Fin15AnchoredAtom3079 Fin15AnchoredAtom3080
    Fin15AnchoredAtom3084 Fin15AnchoredAtom3085 Fin15AnchoredAtom3086 Fin15AnchoredAtom3114
    Fin15AnchoredAtom3115 Fin15AnchoredAtom3116 Fin15AnchoredAtom3120 Fin15AnchoredAtom3121
    Fin15AnchoredAtom3122 Fin15AnchoredAtom3200 Fin15AnchoredAtom3201 Fin15AnchoredAtom3202
    Fin15AnchoredAtom3206 Fin15AnchoredAtom3234 Fin15AnchoredAtom3235 Fin15AnchoredAtom3236
    Fin15AnchoredAtom3240 Fin15AnchoredAtom3241 Fin15AnchoredAtom3242 Fin15AnchoredAtom3320
    Fin15AnchoredAtom3321 Fin15AnchoredAtom3322 Fin15AnchoredAtom3326 Fin15AnchoredAtom3404
    Fin15AnchoredAtom3405 Fin15AnchoredAtom3406 Fin15AnchoredAtom3410 Fin15AnchoredAtom3535
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

theorem fin15Anchored_clause31889 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3051 chi ∧
      ¬Fin15AnchoredAtom3052 chi ∧
      ¬Fin15AnchoredAtom3054 chi ∧
      ¬Fin15AnchoredAtom3056 chi ∧
      ¬Fin15AnchoredAtom3059 chi ∧
      ¬Fin15AnchoredAtom3061 chi ∧
      ¬Fin15AnchoredAtom3063 chi ∧
      ¬Fin15AnchoredAtom3067 chi ∧
      ¬Fin15AnchoredAtom3069 chi ∧
      ¬Fin15AnchoredAtom3078 chi ∧
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
      ¬Fin15AnchoredAtom4068 chi ∧
      ¬Fin15AnchoredAtom4070 chi ∧
      ¬Fin15AnchoredAtom4072 chi ∧
      ¬Fin15AnchoredAtom4076 chi ∧
      ¬Fin15AnchoredAtom4078 chi ∧
      ¬Fin15AnchoredAtom4087 chi ∧
      ¬Fin15AnchoredAtom4097 chi ∧
      ¬Fin15AnchoredAtom4099 chi ∧
      ¬Fin15AnchoredAtom4108 chi ∧
      ¬Fin15AnchoredAtom4123 chi ∧
      ¬Fin15AnchoredAtom4237 chi ∧
      ¬Fin15AnchoredAtom4239 chi ∧
      ¬Fin15AnchoredAtom4248 chi ∧
      ¬Fin15AnchoredAtom4263 chi ∧
      ¬Fin15AnchoredAtom4298 chi ∧
      ¬Fin15AnchoredAtom4447 chi ∧
      ¬Fin15AnchoredAtom4449 chi ∧
      ¬Fin15AnchoredAtom4458 chi ∧
      ¬Fin15AnchoredAtom4473 chi ∧
      ¬Fin15AnchoredAtom4508 chi ∧
      ¬Fin15AnchoredAtom4704 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 3, 4, 6, 7, 8, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05594
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3051 Fin15AnchoredAtom3052 Fin15AnchoredAtom3054
    Fin15AnchoredAtom3056 Fin15AnchoredAtom3059 Fin15AnchoredAtom3061 Fin15AnchoredAtom3063
    Fin15AnchoredAtom3067 Fin15AnchoredAtom3069 Fin15AnchoredAtom3078 Fin15AnchoredAtom3123
    Fin15AnchoredAtom3125 Fin15AnchoredAtom3127 Fin15AnchoredAtom3131 Fin15AnchoredAtom3133
    Fin15AnchoredAtom3142 Fin15AnchoredAtom3152 Fin15AnchoredAtom3154 Fin15AnchoredAtom3163
    Fin15AnchoredAtom3178 Fin15AnchoredAtom3243 Fin15AnchoredAtom3245 Fin15AnchoredAtom3247
    Fin15AnchoredAtom3251 Fin15AnchoredAtom3253 Fin15AnchoredAtom3262 Fin15AnchoredAtom3272
    Fin15AnchoredAtom3274 Fin15AnchoredAtom3283 Fin15AnchoredAtom3298 Fin15AnchoredAtom3412
    Fin15AnchoredAtom3414 Fin15AnchoredAtom3423 Fin15AnchoredAtom3438 Fin15AnchoredAtom3473
    Fin15AnchoredAtom4068 Fin15AnchoredAtom4070 Fin15AnchoredAtom4072 Fin15AnchoredAtom4076
    Fin15AnchoredAtom4078 Fin15AnchoredAtom4087 Fin15AnchoredAtom4097 Fin15AnchoredAtom4099
    Fin15AnchoredAtom4108 Fin15AnchoredAtom4123 Fin15AnchoredAtom4237 Fin15AnchoredAtom4239
    Fin15AnchoredAtom4248 Fin15AnchoredAtom4263 Fin15AnchoredAtom4298 Fin15AnchoredAtom4447
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

theorem fin15Anchored_clause31890 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3051 chi ∧
      ¬Fin15AnchoredAtom3053 chi ∧
      ¬Fin15AnchoredAtom3054 chi ∧
      ¬Fin15AnchoredAtom3056 chi ∧
      ¬Fin15AnchoredAtom3060 chi ∧
      ¬Fin15AnchoredAtom3061 chi ∧
      ¬Fin15AnchoredAtom3063 chi ∧
      ¬Fin15AnchoredAtom3072 chi ∧
      ¬Fin15AnchoredAtom3074 chi ∧
      ¬Fin15AnchoredAtom3078 chi ∧
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
  refine ⟨{1, 3, 4, 6, 7, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05850
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3051 Fin15AnchoredAtom3053 Fin15AnchoredAtom3054
    Fin15AnchoredAtom3056 Fin15AnchoredAtom3060 Fin15AnchoredAtom3061 Fin15AnchoredAtom3063
    Fin15AnchoredAtom3072 Fin15AnchoredAtom3074 Fin15AnchoredAtom3078 Fin15AnchoredAtom3124
    Fin15AnchoredAtom3125 Fin15AnchoredAtom3127 Fin15AnchoredAtom3136 Fin15AnchoredAtom3138
    Fin15AnchoredAtom3142 Fin15AnchoredAtom3157 Fin15AnchoredAtom3159 Fin15AnchoredAtom3163
    Fin15AnchoredAtom3188 Fin15AnchoredAtom3244 Fin15AnchoredAtom3245 Fin15AnchoredAtom3247
    Fin15AnchoredAtom3256 Fin15AnchoredAtom3258 Fin15AnchoredAtom3262 Fin15AnchoredAtom3277
    Fin15AnchoredAtom3279 Fin15AnchoredAtom3283 Fin15AnchoredAtom3308 Fin15AnchoredAtom3417
    Fin15AnchoredAtom3419 Fin15AnchoredAtom3423 Fin15AnchoredAtom3448 Fin15AnchoredAtom3483
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

theorem fin15Anchored_clause31891 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3051 chi ∧
      ¬Fin15AnchoredAtom3053 chi ∧
      ¬Fin15AnchoredAtom3054 chi ∧
      ¬Fin15AnchoredAtom3057 chi ∧
      ¬Fin15AnchoredAtom3060 chi ∧
      ¬Fin15AnchoredAtom3061 chi ∧
      ¬Fin15AnchoredAtom3064 chi ∧
      ¬Fin15AnchoredAtom3072 chi ∧
      ¬Fin15AnchoredAtom3075 chi ∧
      ¬Fin15AnchoredAtom3079 chi ∧
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
  refine ⟨{1, 3, 4, 6, 7, 9, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09946
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3051 Fin15AnchoredAtom3053 Fin15AnchoredAtom3054
    Fin15AnchoredAtom3057 Fin15AnchoredAtom3060 Fin15AnchoredAtom3061 Fin15AnchoredAtom3064
    Fin15AnchoredAtom3072 Fin15AnchoredAtom3075 Fin15AnchoredAtom3079 Fin15AnchoredAtom3124
    Fin15AnchoredAtom3125 Fin15AnchoredAtom3128 Fin15AnchoredAtom3136 Fin15AnchoredAtom3139
    Fin15AnchoredAtom3143 Fin15AnchoredAtom3157 Fin15AnchoredAtom3160 Fin15AnchoredAtom3164
    Fin15AnchoredAtom3189 Fin15AnchoredAtom3244 Fin15AnchoredAtom3245 Fin15AnchoredAtom3248
    Fin15AnchoredAtom3256 Fin15AnchoredAtom3259 Fin15AnchoredAtom3263 Fin15AnchoredAtom3277
    Fin15AnchoredAtom3280 Fin15AnchoredAtom3284 Fin15AnchoredAtom3309 Fin15AnchoredAtom3417
    Fin15AnchoredAtom3420 Fin15AnchoredAtom3424 Fin15AnchoredAtom3449 Fin15AnchoredAtom3484
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

theorem fin15Anchored_clause31892 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3051 chi ∧
      ¬Fin15AnchoredAtom3053 chi ∧
      ¬Fin15AnchoredAtom3054 chi ∧
      ¬Fin15AnchoredAtom3058 chi ∧
      ¬Fin15AnchoredAtom3060 chi ∧
      ¬Fin15AnchoredAtom3061 chi ∧
      ¬Fin15AnchoredAtom3065 chi ∧
      ¬Fin15AnchoredAtom3072 chi ∧
      ¬Fin15AnchoredAtom3076 chi ∧
      ¬Fin15AnchoredAtom3080 chi ∧
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
  refine ⟨{1, 3, 4, 6, 7, 9, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask18138
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3051 Fin15AnchoredAtom3053 Fin15AnchoredAtom3054
    Fin15AnchoredAtom3058 Fin15AnchoredAtom3060 Fin15AnchoredAtom3061 Fin15AnchoredAtom3065
    Fin15AnchoredAtom3072 Fin15AnchoredAtom3076 Fin15AnchoredAtom3080 Fin15AnchoredAtom3124
    Fin15AnchoredAtom3125 Fin15AnchoredAtom3129 Fin15AnchoredAtom3136 Fin15AnchoredAtom3140
    Fin15AnchoredAtom3144 Fin15AnchoredAtom3157 Fin15AnchoredAtom3161 Fin15AnchoredAtom3165
    Fin15AnchoredAtom3190 Fin15AnchoredAtom3244 Fin15AnchoredAtom3245 Fin15AnchoredAtom3249
    Fin15AnchoredAtom3256 Fin15AnchoredAtom3260 Fin15AnchoredAtom3264 Fin15AnchoredAtom3277
    Fin15AnchoredAtom3281 Fin15AnchoredAtom3285 Fin15AnchoredAtom3310 Fin15AnchoredAtom3417
    Fin15AnchoredAtom3421 Fin15AnchoredAtom3425 Fin15AnchoredAtom3450 Fin15AnchoredAtom3485
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

theorem fin15Anchored_clause31893 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3051 chi ∧
      ¬Fin15AnchoredAtom3053 chi ∧
      ¬Fin15AnchoredAtom3056 chi ∧
      ¬Fin15AnchoredAtom3057 chi ∧
      ¬Fin15AnchoredAtom3060 chi ∧
      ¬Fin15AnchoredAtom3063 chi ∧
      ¬Fin15AnchoredAtom3064 chi ∧
      ¬Fin15AnchoredAtom3074 chi ∧
      ¬Fin15AnchoredAtom3075 chi ∧
      ¬Fin15AnchoredAtom3084 chi ∧
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
  refine ⟨{1, 3, 4, 6, 7, 9, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13018
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3051 Fin15AnchoredAtom3053 Fin15AnchoredAtom3056
    Fin15AnchoredAtom3057 Fin15AnchoredAtom3060 Fin15AnchoredAtom3063 Fin15AnchoredAtom3064
    Fin15AnchoredAtom3074 Fin15AnchoredAtom3075 Fin15AnchoredAtom3084 Fin15AnchoredAtom3124
    Fin15AnchoredAtom3127 Fin15AnchoredAtom3128 Fin15AnchoredAtom3138 Fin15AnchoredAtom3139
    Fin15AnchoredAtom3148 Fin15AnchoredAtom3159 Fin15AnchoredAtom3160 Fin15AnchoredAtom3169
    Fin15AnchoredAtom3194 Fin15AnchoredAtom3244 Fin15AnchoredAtom3247 Fin15AnchoredAtom3248
    Fin15AnchoredAtom3258 Fin15AnchoredAtom3259 Fin15AnchoredAtom3268 Fin15AnchoredAtom3279
    Fin15AnchoredAtom3280 Fin15AnchoredAtom3289 Fin15AnchoredAtom3314 Fin15AnchoredAtom3419
    Fin15AnchoredAtom3420 Fin15AnchoredAtom3429 Fin15AnchoredAtom3454 Fin15AnchoredAtom3489
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

theorem fin15Anchored_clause31894 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3051 chi ∧
      ¬Fin15AnchoredAtom3053 chi ∧
      ¬Fin15AnchoredAtom3056 chi ∧
      ¬Fin15AnchoredAtom3058 chi ∧
      ¬Fin15AnchoredAtom3060 chi ∧
      ¬Fin15AnchoredAtom3063 chi ∧
      ¬Fin15AnchoredAtom3065 chi ∧
      ¬Fin15AnchoredAtom3074 chi ∧
      ¬Fin15AnchoredAtom3076 chi ∧
      ¬Fin15AnchoredAtom3085 chi ∧
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
  refine ⟨{1, 3, 4, 6, 7, 9, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21210
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3051 Fin15AnchoredAtom3053 Fin15AnchoredAtom3056
    Fin15AnchoredAtom3058 Fin15AnchoredAtom3060 Fin15AnchoredAtom3063 Fin15AnchoredAtom3065
    Fin15AnchoredAtom3074 Fin15AnchoredAtom3076 Fin15AnchoredAtom3085 Fin15AnchoredAtom3124
    Fin15AnchoredAtom3127 Fin15AnchoredAtom3129 Fin15AnchoredAtom3138 Fin15AnchoredAtom3140
    Fin15AnchoredAtom3149 Fin15AnchoredAtom3159 Fin15AnchoredAtom3161 Fin15AnchoredAtom3170
    Fin15AnchoredAtom3195 Fin15AnchoredAtom3244 Fin15AnchoredAtom3247 Fin15AnchoredAtom3249
    Fin15AnchoredAtom3258 Fin15AnchoredAtom3260 Fin15AnchoredAtom3269 Fin15AnchoredAtom3279
    Fin15AnchoredAtom3281 Fin15AnchoredAtom3290 Fin15AnchoredAtom3315 Fin15AnchoredAtom3419
    Fin15AnchoredAtom3421 Fin15AnchoredAtom3430 Fin15AnchoredAtom3455 Fin15AnchoredAtom3490
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

theorem fin15Anchored_clause31895 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3051 chi ∧
      ¬Fin15AnchoredAtom3053 chi ∧
      ¬Fin15AnchoredAtom3057 chi ∧
      ¬Fin15AnchoredAtom3058 chi ∧
      ¬Fin15AnchoredAtom3060 chi ∧
      ¬Fin15AnchoredAtom3064 chi ∧
      ¬Fin15AnchoredAtom3065 chi ∧
      ¬Fin15AnchoredAtom3075 chi ∧
      ¬Fin15AnchoredAtom3076 chi ∧
      ¬Fin15AnchoredAtom3086 chi ∧
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
  refine ⟨{1, 3, 4, 6, 7, 9, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25306
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3051 Fin15AnchoredAtom3053 Fin15AnchoredAtom3057
    Fin15AnchoredAtom3058 Fin15AnchoredAtom3060 Fin15AnchoredAtom3064 Fin15AnchoredAtom3065
    Fin15AnchoredAtom3075 Fin15AnchoredAtom3076 Fin15AnchoredAtom3086 Fin15AnchoredAtom3124
    Fin15AnchoredAtom3128 Fin15AnchoredAtom3129 Fin15AnchoredAtom3139 Fin15AnchoredAtom3140
    Fin15AnchoredAtom3150 Fin15AnchoredAtom3160 Fin15AnchoredAtom3161 Fin15AnchoredAtom3171
    Fin15AnchoredAtom3196 Fin15AnchoredAtom3244 Fin15AnchoredAtom3248 Fin15AnchoredAtom3249
    Fin15AnchoredAtom3259 Fin15AnchoredAtom3260 Fin15AnchoredAtom3270 Fin15AnchoredAtom3280
    Fin15AnchoredAtom3281 Fin15AnchoredAtom3291 Fin15AnchoredAtom3316 Fin15AnchoredAtom3420
    Fin15AnchoredAtom3421 Fin15AnchoredAtom3431 Fin15AnchoredAtom3456 Fin15AnchoredAtom3491
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

theorem fin15Anchored_clause31896 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3051 chi ∧
      ¬Fin15AnchoredAtom3054 chi ∧
      ¬Fin15AnchoredAtom3056 chi ∧
      ¬Fin15AnchoredAtom3057 chi ∧
      ¬Fin15AnchoredAtom3061 chi ∧
      ¬Fin15AnchoredAtom3063 chi ∧
      ¬Fin15AnchoredAtom3064 chi ∧
      ¬Fin15AnchoredAtom3078 chi ∧
      ¬Fin15AnchoredAtom3079 chi ∧
      ¬Fin15AnchoredAtom3084 chi ∧
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
  refine ⟨{1, 3, 4, 6, 7, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13530
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3051 Fin15AnchoredAtom3054 Fin15AnchoredAtom3056
    Fin15AnchoredAtom3057 Fin15AnchoredAtom3061 Fin15AnchoredAtom3063 Fin15AnchoredAtom3064
    Fin15AnchoredAtom3078 Fin15AnchoredAtom3079 Fin15AnchoredAtom3084 Fin15AnchoredAtom3125
    Fin15AnchoredAtom3127 Fin15AnchoredAtom3128 Fin15AnchoredAtom3142 Fin15AnchoredAtom3143
    Fin15AnchoredAtom3148 Fin15AnchoredAtom3163 Fin15AnchoredAtom3164 Fin15AnchoredAtom3169
    Fin15AnchoredAtom3200 Fin15AnchoredAtom3245 Fin15AnchoredAtom3247 Fin15AnchoredAtom3248
    Fin15AnchoredAtom3262 Fin15AnchoredAtom3263 Fin15AnchoredAtom3268 Fin15AnchoredAtom3283
    Fin15AnchoredAtom3284 Fin15AnchoredAtom3289 Fin15AnchoredAtom3320 Fin15AnchoredAtom3423
    Fin15AnchoredAtom3424 Fin15AnchoredAtom3429 Fin15AnchoredAtom3460 Fin15AnchoredAtom3495
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

theorem fin15Anchored_clause31897 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3051 chi ∧
      ¬Fin15AnchoredAtom3054 chi ∧
      ¬Fin15AnchoredAtom3056 chi ∧
      ¬Fin15AnchoredAtom3058 chi ∧
      ¬Fin15AnchoredAtom3061 chi ∧
      ¬Fin15AnchoredAtom3063 chi ∧
      ¬Fin15AnchoredAtom3065 chi ∧
      ¬Fin15AnchoredAtom3078 chi ∧
      ¬Fin15AnchoredAtom3080 chi ∧
      ¬Fin15AnchoredAtom3085 chi ∧
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
  refine ⟨{1, 3, 4, 6, 7, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21722
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3051 Fin15AnchoredAtom3054 Fin15AnchoredAtom3056
    Fin15AnchoredAtom3058 Fin15AnchoredAtom3061 Fin15AnchoredAtom3063 Fin15AnchoredAtom3065
    Fin15AnchoredAtom3078 Fin15AnchoredAtom3080 Fin15AnchoredAtom3085 Fin15AnchoredAtom3125
    Fin15AnchoredAtom3127 Fin15AnchoredAtom3129 Fin15AnchoredAtom3142 Fin15AnchoredAtom3144
    Fin15AnchoredAtom3149 Fin15AnchoredAtom3163 Fin15AnchoredAtom3165 Fin15AnchoredAtom3170
    Fin15AnchoredAtom3201 Fin15AnchoredAtom3245 Fin15AnchoredAtom3247 Fin15AnchoredAtom3249
    Fin15AnchoredAtom3262 Fin15AnchoredAtom3264 Fin15AnchoredAtom3269 Fin15AnchoredAtom3283
    Fin15AnchoredAtom3285 Fin15AnchoredAtom3290 Fin15AnchoredAtom3321 Fin15AnchoredAtom3423
    Fin15AnchoredAtom3425 Fin15AnchoredAtom3430 Fin15AnchoredAtom3461 Fin15AnchoredAtom3496
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

theorem fin15Anchored_clause31898 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3051 chi ∧
      ¬Fin15AnchoredAtom3054 chi ∧
      ¬Fin15AnchoredAtom3057 chi ∧
      ¬Fin15AnchoredAtom3058 chi ∧
      ¬Fin15AnchoredAtom3061 chi ∧
      ¬Fin15AnchoredAtom3064 chi ∧
      ¬Fin15AnchoredAtom3065 chi ∧
      ¬Fin15AnchoredAtom3079 chi ∧
      ¬Fin15AnchoredAtom3080 chi ∧
      ¬Fin15AnchoredAtom3086 chi ∧
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
  refine ⟨{1, 3, 4, 6, 7, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25818
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3051 Fin15AnchoredAtom3054 Fin15AnchoredAtom3057
    Fin15AnchoredAtom3058 Fin15AnchoredAtom3061 Fin15AnchoredAtom3064 Fin15AnchoredAtom3065
    Fin15AnchoredAtom3079 Fin15AnchoredAtom3080 Fin15AnchoredAtom3086 Fin15AnchoredAtom3125
    Fin15AnchoredAtom3128 Fin15AnchoredAtom3129 Fin15AnchoredAtom3143 Fin15AnchoredAtom3144
    Fin15AnchoredAtom3150 Fin15AnchoredAtom3164 Fin15AnchoredAtom3165 Fin15AnchoredAtom3171
    Fin15AnchoredAtom3202 Fin15AnchoredAtom3245 Fin15AnchoredAtom3248 Fin15AnchoredAtom3249
    Fin15AnchoredAtom3263 Fin15AnchoredAtom3264 Fin15AnchoredAtom3270 Fin15AnchoredAtom3284
    Fin15AnchoredAtom3285 Fin15AnchoredAtom3291 Fin15AnchoredAtom3322 Fin15AnchoredAtom3424
    Fin15AnchoredAtom3425 Fin15AnchoredAtom3431 Fin15AnchoredAtom3462 Fin15AnchoredAtom3497
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

theorem fin15Anchored_clause31899 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3051 chi ∧
      ¬Fin15AnchoredAtom3056 chi ∧
      ¬Fin15AnchoredAtom3057 chi ∧
      ¬Fin15AnchoredAtom3058 chi ∧
      ¬Fin15AnchoredAtom3063 chi ∧
      ¬Fin15AnchoredAtom3064 chi ∧
      ¬Fin15AnchoredAtom3065 chi ∧
      ¬Fin15AnchoredAtom3084 chi ∧
      ¬Fin15AnchoredAtom3085 chi ∧
      ¬Fin15AnchoredAtom3086 chi ∧
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
  refine ⟨{1, 3, 4, 6, 7, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask28890
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3051 Fin15AnchoredAtom3056 Fin15AnchoredAtom3057
    Fin15AnchoredAtom3058 Fin15AnchoredAtom3063 Fin15AnchoredAtom3064 Fin15AnchoredAtom3065
    Fin15AnchoredAtom3084 Fin15AnchoredAtom3085 Fin15AnchoredAtom3086 Fin15AnchoredAtom3127
    Fin15AnchoredAtom3128 Fin15AnchoredAtom3129 Fin15AnchoredAtom3148 Fin15AnchoredAtom3149
    Fin15AnchoredAtom3150 Fin15AnchoredAtom3169 Fin15AnchoredAtom3170 Fin15AnchoredAtom3171
    Fin15AnchoredAtom3206 Fin15AnchoredAtom3247 Fin15AnchoredAtom3248 Fin15AnchoredAtom3249
    Fin15AnchoredAtom3268 Fin15AnchoredAtom3269 Fin15AnchoredAtom3270 Fin15AnchoredAtom3289
    Fin15AnchoredAtom3290 Fin15AnchoredAtom3291 Fin15AnchoredAtom3326 Fin15AnchoredAtom3429
    Fin15AnchoredAtom3430 Fin15AnchoredAtom3431 Fin15AnchoredAtom3466 Fin15AnchoredAtom3501
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

theorem fin15Anchored_clause31900 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3053 chi ∧
      ¬Fin15AnchoredAtom3054 chi ∧
      ¬Fin15AnchoredAtom3056 chi ∧
      ¬Fin15AnchoredAtom3057 chi ∧
      ¬Fin15AnchoredAtom3072 chi ∧
      ¬Fin15AnchoredAtom3074 chi ∧
      ¬Fin15AnchoredAtom3075 chi ∧
      ¬Fin15AnchoredAtom3078 chi ∧
      ¬Fin15AnchoredAtom3079 chi ∧
      ¬Fin15AnchoredAtom3084 chi ∧
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
  refine ⟨{1, 3, 4, 6, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13914
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3053 Fin15AnchoredAtom3054 Fin15AnchoredAtom3056
    Fin15AnchoredAtom3057 Fin15AnchoredAtom3072 Fin15AnchoredAtom3074 Fin15AnchoredAtom3075
    Fin15AnchoredAtom3078 Fin15AnchoredAtom3079 Fin15AnchoredAtom3084 Fin15AnchoredAtom3136
    Fin15AnchoredAtom3138 Fin15AnchoredAtom3139 Fin15AnchoredAtom3142 Fin15AnchoredAtom3143
    Fin15AnchoredAtom3148 Fin15AnchoredAtom3188 Fin15AnchoredAtom3189 Fin15AnchoredAtom3194
    Fin15AnchoredAtom3200 Fin15AnchoredAtom3256 Fin15AnchoredAtom3258 Fin15AnchoredAtom3259
    Fin15AnchoredAtom3262 Fin15AnchoredAtom3263 Fin15AnchoredAtom3268 Fin15AnchoredAtom3308
    Fin15AnchoredAtom3309 Fin15AnchoredAtom3314 Fin15AnchoredAtom3320 Fin15AnchoredAtom3448
    Fin15AnchoredAtom3449 Fin15AnchoredAtom3454 Fin15AnchoredAtom3460 Fin15AnchoredAtom3525
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

theorem fin15Anchored_clause31901 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3053 chi ∧
      ¬Fin15AnchoredAtom3054 chi ∧
      ¬Fin15AnchoredAtom3056 chi ∧
      ¬Fin15AnchoredAtom3058 chi ∧
      ¬Fin15AnchoredAtom3072 chi ∧
      ¬Fin15AnchoredAtom3074 chi ∧
      ¬Fin15AnchoredAtom3076 chi ∧
      ¬Fin15AnchoredAtom3078 chi ∧
      ¬Fin15AnchoredAtom3080 chi ∧
      ¬Fin15AnchoredAtom3085 chi ∧
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
  refine ⟨{1, 3, 4, 6, 9, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22106
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3053 Fin15AnchoredAtom3054 Fin15AnchoredAtom3056
    Fin15AnchoredAtom3058 Fin15AnchoredAtom3072 Fin15AnchoredAtom3074 Fin15AnchoredAtom3076
    Fin15AnchoredAtom3078 Fin15AnchoredAtom3080 Fin15AnchoredAtom3085 Fin15AnchoredAtom3136
    Fin15AnchoredAtom3138 Fin15AnchoredAtom3140 Fin15AnchoredAtom3142 Fin15AnchoredAtom3144
    Fin15AnchoredAtom3149 Fin15AnchoredAtom3188 Fin15AnchoredAtom3190 Fin15AnchoredAtom3195
    Fin15AnchoredAtom3201 Fin15AnchoredAtom3256 Fin15AnchoredAtom3258 Fin15AnchoredAtom3260
    Fin15AnchoredAtom3262 Fin15AnchoredAtom3264 Fin15AnchoredAtom3269 Fin15AnchoredAtom3308
    Fin15AnchoredAtom3310 Fin15AnchoredAtom3315 Fin15AnchoredAtom3321 Fin15AnchoredAtom3448
    Fin15AnchoredAtom3450 Fin15AnchoredAtom3455 Fin15AnchoredAtom3461 Fin15AnchoredAtom3526
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

theorem fin15Anchored_clause31902 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3053 chi ∧
      ¬Fin15AnchoredAtom3054 chi ∧
      ¬Fin15AnchoredAtom3057 chi ∧
      ¬Fin15AnchoredAtom3058 chi ∧
      ¬Fin15AnchoredAtom3072 chi ∧
      ¬Fin15AnchoredAtom3075 chi ∧
      ¬Fin15AnchoredAtom3076 chi ∧
      ¬Fin15AnchoredAtom3079 chi ∧
      ¬Fin15AnchoredAtom3080 chi ∧
      ¬Fin15AnchoredAtom3086 chi ∧
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
  refine ⟨{1, 3, 4, 6, 9, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26202
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3053 Fin15AnchoredAtom3054 Fin15AnchoredAtom3057
    Fin15AnchoredAtom3058 Fin15AnchoredAtom3072 Fin15AnchoredAtom3075 Fin15AnchoredAtom3076
    Fin15AnchoredAtom3079 Fin15AnchoredAtom3080 Fin15AnchoredAtom3086 Fin15AnchoredAtom3136
    Fin15AnchoredAtom3139 Fin15AnchoredAtom3140 Fin15AnchoredAtom3143 Fin15AnchoredAtom3144
    Fin15AnchoredAtom3150 Fin15AnchoredAtom3189 Fin15AnchoredAtom3190 Fin15AnchoredAtom3196
    Fin15AnchoredAtom3202 Fin15AnchoredAtom3256 Fin15AnchoredAtom3259 Fin15AnchoredAtom3260
    Fin15AnchoredAtom3263 Fin15AnchoredAtom3264 Fin15AnchoredAtom3270 Fin15AnchoredAtom3309
    Fin15AnchoredAtom3310 Fin15AnchoredAtom3316 Fin15AnchoredAtom3322 Fin15AnchoredAtom3449
    Fin15AnchoredAtom3450 Fin15AnchoredAtom3456 Fin15AnchoredAtom3462 Fin15AnchoredAtom3527
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

theorem fin15Anchored_clause31903 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3053 chi ∧
      ¬Fin15AnchoredAtom3056 chi ∧
      ¬Fin15AnchoredAtom3057 chi ∧
      ¬Fin15AnchoredAtom3058 chi ∧
      ¬Fin15AnchoredAtom3074 chi ∧
      ¬Fin15AnchoredAtom3075 chi ∧
      ¬Fin15AnchoredAtom3076 chi ∧
      ¬Fin15AnchoredAtom3084 chi ∧
      ¬Fin15AnchoredAtom3085 chi ∧
      ¬Fin15AnchoredAtom3086 chi ∧
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
  refine ⟨{1, 3, 4, 6, 9, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29274
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3053 Fin15AnchoredAtom3056 Fin15AnchoredAtom3057
    Fin15AnchoredAtom3058 Fin15AnchoredAtom3074 Fin15AnchoredAtom3075 Fin15AnchoredAtom3076
    Fin15AnchoredAtom3084 Fin15AnchoredAtom3085 Fin15AnchoredAtom3086 Fin15AnchoredAtom3138
    Fin15AnchoredAtom3139 Fin15AnchoredAtom3140 Fin15AnchoredAtom3148 Fin15AnchoredAtom3149
    Fin15AnchoredAtom3150 Fin15AnchoredAtom3194 Fin15AnchoredAtom3195 Fin15AnchoredAtom3196
    Fin15AnchoredAtom3206 Fin15AnchoredAtom3258 Fin15AnchoredAtom3259 Fin15AnchoredAtom3260
    Fin15AnchoredAtom3268 Fin15AnchoredAtom3269 Fin15AnchoredAtom3270 Fin15AnchoredAtom3314
    Fin15AnchoredAtom3315 Fin15AnchoredAtom3316 Fin15AnchoredAtom3326 Fin15AnchoredAtom3454
    Fin15AnchoredAtom3455 Fin15AnchoredAtom3456 Fin15AnchoredAtom3466 Fin15AnchoredAtom3531
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

theorem fin15Anchored_clause31904 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3054 chi ∧
      ¬Fin15AnchoredAtom3056 chi ∧
      ¬Fin15AnchoredAtom3057 chi ∧
      ¬Fin15AnchoredAtom3058 chi ∧
      ¬Fin15AnchoredAtom3078 chi ∧
      ¬Fin15AnchoredAtom3079 chi ∧
      ¬Fin15AnchoredAtom3080 chi ∧
      ¬Fin15AnchoredAtom3084 chi ∧
      ¬Fin15AnchoredAtom3085 chi ∧
      ¬Fin15AnchoredAtom3086 chi ∧
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
  refine ⟨{1, 3, 4, 6, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29786
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3054 Fin15AnchoredAtom3056 Fin15AnchoredAtom3057
    Fin15AnchoredAtom3058 Fin15AnchoredAtom3078 Fin15AnchoredAtom3079 Fin15AnchoredAtom3080
    Fin15AnchoredAtom3084 Fin15AnchoredAtom3085 Fin15AnchoredAtom3086 Fin15AnchoredAtom3142
    Fin15AnchoredAtom3143 Fin15AnchoredAtom3144 Fin15AnchoredAtom3148 Fin15AnchoredAtom3149
    Fin15AnchoredAtom3150 Fin15AnchoredAtom3200 Fin15AnchoredAtom3201 Fin15AnchoredAtom3202
    Fin15AnchoredAtom3206 Fin15AnchoredAtom3262 Fin15AnchoredAtom3263 Fin15AnchoredAtom3264
    Fin15AnchoredAtom3268 Fin15AnchoredAtom3269 Fin15AnchoredAtom3270 Fin15AnchoredAtom3320
    Fin15AnchoredAtom3321 Fin15AnchoredAtom3322 Fin15AnchoredAtom3326 Fin15AnchoredAtom3460
    Fin15AnchoredAtom3461 Fin15AnchoredAtom3462 Fin15AnchoredAtom3466 Fin15AnchoredAtom3535
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

theorem fin15Anchored_clause31905 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3060 chi ∧
      ¬Fin15AnchoredAtom3061 chi ∧
      ¬Fin15AnchoredAtom3063 chi ∧
      ¬Fin15AnchoredAtom3064 chi ∧
      ¬Fin15AnchoredAtom3072 chi ∧
      ¬Fin15AnchoredAtom3074 chi ∧
      ¬Fin15AnchoredAtom3075 chi ∧
      ¬Fin15AnchoredAtom3078 chi ∧
      ¬Fin15AnchoredAtom3079 chi ∧
      ¬Fin15AnchoredAtom3084 chi ∧
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
  refine ⟨{1, 3, 4, 7, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13978
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3060 Fin15AnchoredAtom3061 Fin15AnchoredAtom3063
    Fin15AnchoredAtom3064 Fin15AnchoredAtom3072 Fin15AnchoredAtom3074 Fin15AnchoredAtom3075
    Fin15AnchoredAtom3078 Fin15AnchoredAtom3079 Fin15AnchoredAtom3084 Fin15AnchoredAtom3157
    Fin15AnchoredAtom3159 Fin15AnchoredAtom3160 Fin15AnchoredAtom3163 Fin15AnchoredAtom3164
    Fin15AnchoredAtom3169 Fin15AnchoredAtom3188 Fin15AnchoredAtom3189 Fin15AnchoredAtom3194
    Fin15AnchoredAtom3200 Fin15AnchoredAtom3277 Fin15AnchoredAtom3279 Fin15AnchoredAtom3280
    Fin15AnchoredAtom3283 Fin15AnchoredAtom3284 Fin15AnchoredAtom3289 Fin15AnchoredAtom3308
    Fin15AnchoredAtom3309 Fin15AnchoredAtom3314 Fin15AnchoredAtom3320 Fin15AnchoredAtom3483
    Fin15AnchoredAtom3484 Fin15AnchoredAtom3489 Fin15AnchoredAtom3495 Fin15AnchoredAtom3525
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

theorem fin15Anchored_clause31906 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3060 chi ∧
      ¬Fin15AnchoredAtom3061 chi ∧
      ¬Fin15AnchoredAtom3063 chi ∧
      ¬Fin15AnchoredAtom3065 chi ∧
      ¬Fin15AnchoredAtom3072 chi ∧
      ¬Fin15AnchoredAtom3074 chi ∧
      ¬Fin15AnchoredAtom3076 chi ∧
      ¬Fin15AnchoredAtom3078 chi ∧
      ¬Fin15AnchoredAtom3080 chi ∧
      ¬Fin15AnchoredAtom3085 chi ∧
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
  refine ⟨{1, 3, 4, 7, 9, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22170
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3060 Fin15AnchoredAtom3061 Fin15AnchoredAtom3063
    Fin15AnchoredAtom3065 Fin15AnchoredAtom3072 Fin15AnchoredAtom3074 Fin15AnchoredAtom3076
    Fin15AnchoredAtom3078 Fin15AnchoredAtom3080 Fin15AnchoredAtom3085 Fin15AnchoredAtom3157
    Fin15AnchoredAtom3159 Fin15AnchoredAtom3161 Fin15AnchoredAtom3163 Fin15AnchoredAtom3165
    Fin15AnchoredAtom3170 Fin15AnchoredAtom3188 Fin15AnchoredAtom3190 Fin15AnchoredAtom3195
    Fin15AnchoredAtom3201 Fin15AnchoredAtom3277 Fin15AnchoredAtom3279 Fin15AnchoredAtom3281
    Fin15AnchoredAtom3283 Fin15AnchoredAtom3285 Fin15AnchoredAtom3290 Fin15AnchoredAtom3308
    Fin15AnchoredAtom3310 Fin15AnchoredAtom3315 Fin15AnchoredAtom3321 Fin15AnchoredAtom3483
    Fin15AnchoredAtom3485 Fin15AnchoredAtom3490 Fin15AnchoredAtom3496 Fin15AnchoredAtom3526
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

theorem fin15Anchored_clause31907 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3060 chi ∧
      ¬Fin15AnchoredAtom3061 chi ∧
      ¬Fin15AnchoredAtom3064 chi ∧
      ¬Fin15AnchoredAtom3065 chi ∧
      ¬Fin15AnchoredAtom3072 chi ∧
      ¬Fin15AnchoredAtom3075 chi ∧
      ¬Fin15AnchoredAtom3076 chi ∧
      ¬Fin15AnchoredAtom3079 chi ∧
      ¬Fin15AnchoredAtom3080 chi ∧
      ¬Fin15AnchoredAtom3086 chi ∧
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
  refine ⟨{1, 3, 4, 7, 9, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26266
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3060 Fin15AnchoredAtom3061 Fin15AnchoredAtom3064
    Fin15AnchoredAtom3065 Fin15AnchoredAtom3072 Fin15AnchoredAtom3075 Fin15AnchoredAtom3076
    Fin15AnchoredAtom3079 Fin15AnchoredAtom3080 Fin15AnchoredAtom3086 Fin15AnchoredAtom3157
    Fin15AnchoredAtom3160 Fin15AnchoredAtom3161 Fin15AnchoredAtom3164 Fin15AnchoredAtom3165
    Fin15AnchoredAtom3171 Fin15AnchoredAtom3189 Fin15AnchoredAtom3190 Fin15AnchoredAtom3196
    Fin15AnchoredAtom3202 Fin15AnchoredAtom3277 Fin15AnchoredAtom3280 Fin15AnchoredAtom3281
    Fin15AnchoredAtom3284 Fin15AnchoredAtom3285 Fin15AnchoredAtom3291 Fin15AnchoredAtom3309
    Fin15AnchoredAtom3310 Fin15AnchoredAtom3316 Fin15AnchoredAtom3322 Fin15AnchoredAtom3484
    Fin15AnchoredAtom3485 Fin15AnchoredAtom3491 Fin15AnchoredAtom3497 Fin15AnchoredAtom3527
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

theorem fin15Anchored_clause31908 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3060 chi ∧
      ¬Fin15AnchoredAtom3063 chi ∧
      ¬Fin15AnchoredAtom3064 chi ∧
      ¬Fin15AnchoredAtom3065 chi ∧
      ¬Fin15AnchoredAtom3074 chi ∧
      ¬Fin15AnchoredAtom3075 chi ∧
      ¬Fin15AnchoredAtom3076 chi ∧
      ¬Fin15AnchoredAtom3084 chi ∧
      ¬Fin15AnchoredAtom3085 chi ∧
      ¬Fin15AnchoredAtom3086 chi ∧
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
  refine ⟨{1, 3, 4, 7, 9, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29338
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3060 Fin15AnchoredAtom3063 Fin15AnchoredAtom3064
    Fin15AnchoredAtom3065 Fin15AnchoredAtom3074 Fin15AnchoredAtom3075 Fin15AnchoredAtom3076
    Fin15AnchoredAtom3084 Fin15AnchoredAtom3085 Fin15AnchoredAtom3086 Fin15AnchoredAtom3159
    Fin15AnchoredAtom3160 Fin15AnchoredAtom3161 Fin15AnchoredAtom3169 Fin15AnchoredAtom3170
    Fin15AnchoredAtom3171 Fin15AnchoredAtom3194 Fin15AnchoredAtom3195 Fin15AnchoredAtom3196
    Fin15AnchoredAtom3206 Fin15AnchoredAtom3279 Fin15AnchoredAtom3280 Fin15AnchoredAtom3281
    Fin15AnchoredAtom3289 Fin15AnchoredAtom3290 Fin15AnchoredAtom3291 Fin15AnchoredAtom3314
    Fin15AnchoredAtom3315 Fin15AnchoredAtom3316 Fin15AnchoredAtom3326 Fin15AnchoredAtom3489
    Fin15AnchoredAtom3490 Fin15AnchoredAtom3491 Fin15AnchoredAtom3501 Fin15AnchoredAtom3531
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

theorem fin15Anchored_clause31909 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3061 chi ∧
      ¬Fin15AnchoredAtom3063 chi ∧
      ¬Fin15AnchoredAtom3064 chi ∧
      ¬Fin15AnchoredAtom3065 chi ∧
      ¬Fin15AnchoredAtom3078 chi ∧
      ¬Fin15AnchoredAtom3079 chi ∧
      ¬Fin15AnchoredAtom3080 chi ∧
      ¬Fin15AnchoredAtom3084 chi ∧
      ¬Fin15AnchoredAtom3085 chi ∧
      ¬Fin15AnchoredAtom3086 chi ∧
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
  refine ⟨{1, 3, 4, 7, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29850
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3061 Fin15AnchoredAtom3063 Fin15AnchoredAtom3064
    Fin15AnchoredAtom3065 Fin15AnchoredAtom3078 Fin15AnchoredAtom3079 Fin15AnchoredAtom3080
    Fin15AnchoredAtom3084 Fin15AnchoredAtom3085 Fin15AnchoredAtom3086 Fin15AnchoredAtom3163
    Fin15AnchoredAtom3164 Fin15AnchoredAtom3165 Fin15AnchoredAtom3169 Fin15AnchoredAtom3170
    Fin15AnchoredAtom3171 Fin15AnchoredAtom3200 Fin15AnchoredAtom3201 Fin15AnchoredAtom3202
    Fin15AnchoredAtom3206 Fin15AnchoredAtom3283 Fin15AnchoredAtom3284 Fin15AnchoredAtom3285
    Fin15AnchoredAtom3289 Fin15AnchoredAtom3290 Fin15AnchoredAtom3291 Fin15AnchoredAtom3320
    Fin15AnchoredAtom3321 Fin15AnchoredAtom3322 Fin15AnchoredAtom3326 Fin15AnchoredAtom3495
    Fin15AnchoredAtom3496 Fin15AnchoredAtom3497 Fin15AnchoredAtom3501 Fin15AnchoredAtom3535
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

theorem fin15Anchored_clause31910 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3066 chi ∧
      ¬Fin15AnchoredAtom3067 chi ∧
      ¬Fin15AnchoredAtom3069 chi ∧
      ¬Fin15AnchoredAtom3070 chi ∧
      ¬Fin15AnchoredAtom3072 chi ∧
      ¬Fin15AnchoredAtom3074 chi ∧
      ¬Fin15AnchoredAtom3075 chi ∧
      ¬Fin15AnchoredAtom3078 chi ∧
      ¬Fin15AnchoredAtom3079 chi ∧
      ¬Fin15AnchoredAtom3084 chi ∧
      ¬Fin15AnchoredAtom3172 chi ∧
      ¬Fin15AnchoredAtom3174 chi ∧
      ¬Fin15AnchoredAtom3175 chi ∧
      ¬Fin15AnchoredAtom3178 chi ∧
      ¬Fin15AnchoredAtom3179 chi ∧
      ¬Fin15AnchoredAtom3184 chi ∧
      ¬Fin15AnchoredAtom3188 chi ∧
      ¬Fin15AnchoredAtom3189 chi ∧
      ¬Fin15AnchoredAtom3194 chi ∧
      ¬Fin15AnchoredAtom3200 chi ∧
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
      ¬Fin15AnchoredAtom4117 chi ∧
      ¬Fin15AnchoredAtom4119 chi ∧
      ¬Fin15AnchoredAtom4120 chi ∧
      ¬Fin15AnchoredAtom4123 chi ∧
      ¬Fin15AnchoredAtom4124 chi ∧
      ¬Fin15AnchoredAtom4129 chi ∧
      ¬Fin15AnchoredAtom4133 chi ∧
      ¬Fin15AnchoredAtom4134 chi ∧
      ¬Fin15AnchoredAtom4139 chi ∧
      ¬Fin15AnchoredAtom4145 chi ∧
      ¬Fin15AnchoredAtom4328 chi ∧
      ¬Fin15AnchoredAtom4329 chi ∧
      ¬Fin15AnchoredAtom4334 chi ∧
      ¬Fin15AnchoredAtom4340 chi ∧
      ¬Fin15AnchoredAtom4350 chi ∧
      ¬Fin15AnchoredAtom4538 chi ∧
      ¬Fin15AnchoredAtom4539 chi ∧
      ¬Fin15AnchoredAtom4544 chi ∧
      ¬Fin15AnchoredAtom4550 chi ∧
      ¬Fin15AnchoredAtom4560 chi ∧
      ¬Fin15AnchoredAtom4806 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 3, 4, 8, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask14106
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3066 Fin15AnchoredAtom3067 Fin15AnchoredAtom3069
    Fin15AnchoredAtom3070 Fin15AnchoredAtom3072 Fin15AnchoredAtom3074 Fin15AnchoredAtom3075
    Fin15AnchoredAtom3078 Fin15AnchoredAtom3079 Fin15AnchoredAtom3084 Fin15AnchoredAtom3172
    Fin15AnchoredAtom3174 Fin15AnchoredAtom3175 Fin15AnchoredAtom3178 Fin15AnchoredAtom3179
    Fin15AnchoredAtom3184 Fin15AnchoredAtom3188 Fin15AnchoredAtom3189 Fin15AnchoredAtom3194
    Fin15AnchoredAtom3200 Fin15AnchoredAtom3292 Fin15AnchoredAtom3294 Fin15AnchoredAtom3295
    Fin15AnchoredAtom3298 Fin15AnchoredAtom3299 Fin15AnchoredAtom3304 Fin15AnchoredAtom3308
    Fin15AnchoredAtom3309 Fin15AnchoredAtom3314 Fin15AnchoredAtom3320 Fin15AnchoredAtom3503
    Fin15AnchoredAtom3504 Fin15AnchoredAtom3509 Fin15AnchoredAtom3515 Fin15AnchoredAtom3525
    Fin15AnchoredAtom4117 Fin15AnchoredAtom4119 Fin15AnchoredAtom4120 Fin15AnchoredAtom4123
    Fin15AnchoredAtom4124 Fin15AnchoredAtom4129 Fin15AnchoredAtom4133 Fin15AnchoredAtom4134
    Fin15AnchoredAtom4139 Fin15AnchoredAtom4145 Fin15AnchoredAtom4328 Fin15AnchoredAtom4329
    Fin15AnchoredAtom4334 Fin15AnchoredAtom4340 Fin15AnchoredAtom4350 Fin15AnchoredAtom4538
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

theorem fin15Anchored_clause31911 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3072 chi ∧
      ¬Fin15AnchoredAtom3074 chi ∧
      ¬Fin15AnchoredAtom3075 chi ∧
      ¬Fin15AnchoredAtom3076 chi ∧
      ¬Fin15AnchoredAtom3078 chi ∧
      ¬Fin15AnchoredAtom3079 chi ∧
      ¬Fin15AnchoredAtom3080 chi ∧
      ¬Fin15AnchoredAtom3084 chi ∧
      ¬Fin15AnchoredAtom3085 chi ∧
      ¬Fin15AnchoredAtom3086 chi ∧
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
  refine ⟨{1, 3, 4, 9, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask30234
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3072 Fin15AnchoredAtom3074 Fin15AnchoredAtom3075
    Fin15AnchoredAtom3076 Fin15AnchoredAtom3078 Fin15AnchoredAtom3079 Fin15AnchoredAtom3080
    Fin15AnchoredAtom3084 Fin15AnchoredAtom3085 Fin15AnchoredAtom3086 Fin15AnchoredAtom3188
    Fin15AnchoredAtom3189 Fin15AnchoredAtom3190 Fin15AnchoredAtom3194 Fin15AnchoredAtom3195
    Fin15AnchoredAtom3196 Fin15AnchoredAtom3200 Fin15AnchoredAtom3201 Fin15AnchoredAtom3202
    Fin15AnchoredAtom3206 Fin15AnchoredAtom3308 Fin15AnchoredAtom3309 Fin15AnchoredAtom3310
    Fin15AnchoredAtom3314 Fin15AnchoredAtom3315 Fin15AnchoredAtom3316 Fin15AnchoredAtom3320
    Fin15AnchoredAtom3321 Fin15AnchoredAtom3322 Fin15AnchoredAtom3326 Fin15AnchoredAtom3525
    Fin15AnchoredAtom3526 Fin15AnchoredAtom3527 Fin15AnchoredAtom3531 Fin15AnchoredAtom3535
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

theorem fin15Anchored_clause31912 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3087 chi ∧
      ¬Fin15AnchoredAtom3089 chi ∧
      ¬Fin15AnchoredAtom3090 chi ∧
      ¬Fin15AnchoredAtom3092 chi ∧
      ¬Fin15AnchoredAtom3096 chi ∧
      ¬Fin15AnchoredAtom3097 chi ∧
      ¬Fin15AnchoredAtom3099 chi ∧
      ¬Fin15AnchoredAtom3108 chi ∧
      ¬Fin15AnchoredAtom3110 chi ∧
      ¬Fin15AnchoredAtom3114 chi ∧
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
  refine ⟨{1, 3, 5, 6, 7, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05866
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3087 Fin15AnchoredAtom3089 Fin15AnchoredAtom3090
    Fin15AnchoredAtom3092 Fin15AnchoredAtom3096 Fin15AnchoredAtom3097 Fin15AnchoredAtom3099
    Fin15AnchoredAtom3108 Fin15AnchoredAtom3110 Fin15AnchoredAtom3114 Fin15AnchoredAtom3124
    Fin15AnchoredAtom3125 Fin15AnchoredAtom3127 Fin15AnchoredAtom3136 Fin15AnchoredAtom3138
    Fin15AnchoredAtom3142 Fin15AnchoredAtom3157 Fin15AnchoredAtom3159 Fin15AnchoredAtom3163
    Fin15AnchoredAtom3188 Fin15AnchoredAtom3328 Fin15AnchoredAtom3329 Fin15AnchoredAtom3331
    Fin15AnchoredAtom3340 Fin15AnchoredAtom3342 Fin15AnchoredAtom3346 Fin15AnchoredAtom3361
    Fin15AnchoredAtom3363 Fin15AnchoredAtom3367 Fin15AnchoredAtom3392 Fin15AnchoredAtom3417
    Fin15AnchoredAtom3419 Fin15AnchoredAtom3423 Fin15AnchoredAtom3448 Fin15AnchoredAtom3483
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

theorem fin15Anchored_clause31913 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3087 chi ∧
      ¬Fin15AnchoredAtom3089 chi ∧
      ¬Fin15AnchoredAtom3090 chi ∧
      ¬Fin15AnchoredAtom3093 chi ∧
      ¬Fin15AnchoredAtom3096 chi ∧
      ¬Fin15AnchoredAtom3097 chi ∧
      ¬Fin15AnchoredAtom3100 chi ∧
      ¬Fin15AnchoredAtom3108 chi ∧
      ¬Fin15AnchoredAtom3111 chi ∧
      ¬Fin15AnchoredAtom3115 chi ∧
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
  refine ⟨{1, 3, 5, 6, 7, 9, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09962
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3087 Fin15AnchoredAtom3089 Fin15AnchoredAtom3090
    Fin15AnchoredAtom3093 Fin15AnchoredAtom3096 Fin15AnchoredAtom3097 Fin15AnchoredAtom3100
    Fin15AnchoredAtom3108 Fin15AnchoredAtom3111 Fin15AnchoredAtom3115 Fin15AnchoredAtom3124
    Fin15AnchoredAtom3125 Fin15AnchoredAtom3128 Fin15AnchoredAtom3136 Fin15AnchoredAtom3139
    Fin15AnchoredAtom3143 Fin15AnchoredAtom3157 Fin15AnchoredAtom3160 Fin15AnchoredAtom3164
    Fin15AnchoredAtom3189 Fin15AnchoredAtom3328 Fin15AnchoredAtom3329 Fin15AnchoredAtom3332
    Fin15AnchoredAtom3340 Fin15AnchoredAtom3343 Fin15AnchoredAtom3347 Fin15AnchoredAtom3361
    Fin15AnchoredAtom3364 Fin15AnchoredAtom3368 Fin15AnchoredAtom3393 Fin15AnchoredAtom3417
    Fin15AnchoredAtom3420 Fin15AnchoredAtom3424 Fin15AnchoredAtom3449 Fin15AnchoredAtom3484
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

theorem fin15Anchored_clause31914 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3087 chi ∧
      ¬Fin15AnchoredAtom3089 chi ∧
      ¬Fin15AnchoredAtom3090 chi ∧
      ¬Fin15AnchoredAtom3094 chi ∧
      ¬Fin15AnchoredAtom3096 chi ∧
      ¬Fin15AnchoredAtom3097 chi ∧
      ¬Fin15AnchoredAtom3101 chi ∧
      ¬Fin15AnchoredAtom3108 chi ∧
      ¬Fin15AnchoredAtom3112 chi ∧
      ¬Fin15AnchoredAtom3116 chi ∧
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
  refine ⟨{1, 3, 5, 6, 7, 9, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask18154
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3087 Fin15AnchoredAtom3089 Fin15AnchoredAtom3090
    Fin15AnchoredAtom3094 Fin15AnchoredAtom3096 Fin15AnchoredAtom3097 Fin15AnchoredAtom3101
    Fin15AnchoredAtom3108 Fin15AnchoredAtom3112 Fin15AnchoredAtom3116 Fin15AnchoredAtom3124
    Fin15AnchoredAtom3125 Fin15AnchoredAtom3129 Fin15AnchoredAtom3136 Fin15AnchoredAtom3140
    Fin15AnchoredAtom3144 Fin15AnchoredAtom3157 Fin15AnchoredAtom3161 Fin15AnchoredAtom3165
    Fin15AnchoredAtom3190 Fin15AnchoredAtom3328 Fin15AnchoredAtom3329 Fin15AnchoredAtom3333
    Fin15AnchoredAtom3340 Fin15AnchoredAtom3344 Fin15AnchoredAtom3348 Fin15AnchoredAtom3361
    Fin15AnchoredAtom3365 Fin15AnchoredAtom3369 Fin15AnchoredAtom3394 Fin15AnchoredAtom3417
    Fin15AnchoredAtom3421 Fin15AnchoredAtom3425 Fin15AnchoredAtom3450 Fin15AnchoredAtom3485
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

theorem fin15Anchored_clause31915 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3087 chi ∧
      ¬Fin15AnchoredAtom3089 chi ∧
      ¬Fin15AnchoredAtom3092 chi ∧
      ¬Fin15AnchoredAtom3093 chi ∧
      ¬Fin15AnchoredAtom3096 chi ∧
      ¬Fin15AnchoredAtom3099 chi ∧
      ¬Fin15AnchoredAtom3100 chi ∧
      ¬Fin15AnchoredAtom3110 chi ∧
      ¬Fin15AnchoredAtom3111 chi ∧
      ¬Fin15AnchoredAtom3120 chi ∧
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
  refine ⟨{1, 3, 5, 6, 7, 9, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13034
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3087 Fin15AnchoredAtom3089 Fin15AnchoredAtom3092
    Fin15AnchoredAtom3093 Fin15AnchoredAtom3096 Fin15AnchoredAtom3099 Fin15AnchoredAtom3100
    Fin15AnchoredAtom3110 Fin15AnchoredAtom3111 Fin15AnchoredAtom3120 Fin15AnchoredAtom3124
    Fin15AnchoredAtom3127 Fin15AnchoredAtom3128 Fin15AnchoredAtom3138 Fin15AnchoredAtom3139
    Fin15AnchoredAtom3148 Fin15AnchoredAtom3159 Fin15AnchoredAtom3160 Fin15AnchoredAtom3169
    Fin15AnchoredAtom3194 Fin15AnchoredAtom3328 Fin15AnchoredAtom3331 Fin15AnchoredAtom3332
    Fin15AnchoredAtom3342 Fin15AnchoredAtom3343 Fin15AnchoredAtom3352 Fin15AnchoredAtom3363
    Fin15AnchoredAtom3364 Fin15AnchoredAtom3373 Fin15AnchoredAtom3398 Fin15AnchoredAtom3419
    Fin15AnchoredAtom3420 Fin15AnchoredAtom3429 Fin15AnchoredAtom3454 Fin15AnchoredAtom3489
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

theorem fin15Anchored_clause31916 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3087 chi ∧
      ¬Fin15AnchoredAtom3089 chi ∧
      ¬Fin15AnchoredAtom3092 chi ∧
      ¬Fin15AnchoredAtom3094 chi ∧
      ¬Fin15AnchoredAtom3096 chi ∧
      ¬Fin15AnchoredAtom3099 chi ∧
      ¬Fin15AnchoredAtom3101 chi ∧
      ¬Fin15AnchoredAtom3110 chi ∧
      ¬Fin15AnchoredAtom3112 chi ∧
      ¬Fin15AnchoredAtom3121 chi ∧
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
  refine ⟨{1, 3, 5, 6, 7, 9, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21226
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3087 Fin15AnchoredAtom3089 Fin15AnchoredAtom3092
    Fin15AnchoredAtom3094 Fin15AnchoredAtom3096 Fin15AnchoredAtom3099 Fin15AnchoredAtom3101
    Fin15AnchoredAtom3110 Fin15AnchoredAtom3112 Fin15AnchoredAtom3121 Fin15AnchoredAtom3124
    Fin15AnchoredAtom3127 Fin15AnchoredAtom3129 Fin15AnchoredAtom3138 Fin15AnchoredAtom3140
    Fin15AnchoredAtom3149 Fin15AnchoredAtom3159 Fin15AnchoredAtom3161 Fin15AnchoredAtom3170
    Fin15AnchoredAtom3195 Fin15AnchoredAtom3328 Fin15AnchoredAtom3331 Fin15AnchoredAtom3333
    Fin15AnchoredAtom3342 Fin15AnchoredAtom3344 Fin15AnchoredAtom3353 Fin15AnchoredAtom3363
    Fin15AnchoredAtom3365 Fin15AnchoredAtom3374 Fin15AnchoredAtom3399 Fin15AnchoredAtom3419
    Fin15AnchoredAtom3421 Fin15AnchoredAtom3430 Fin15AnchoredAtom3455 Fin15AnchoredAtom3490
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

theorem fin15Anchored_clause31917 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3087 chi ∧
      ¬Fin15AnchoredAtom3089 chi ∧
      ¬Fin15AnchoredAtom3093 chi ∧
      ¬Fin15AnchoredAtom3094 chi ∧
      ¬Fin15AnchoredAtom3096 chi ∧
      ¬Fin15AnchoredAtom3100 chi ∧
      ¬Fin15AnchoredAtom3101 chi ∧
      ¬Fin15AnchoredAtom3111 chi ∧
      ¬Fin15AnchoredAtom3112 chi ∧
      ¬Fin15AnchoredAtom3122 chi ∧
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
  refine ⟨{1, 3, 5, 6, 7, 9, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25322
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3087 Fin15AnchoredAtom3089 Fin15AnchoredAtom3093
    Fin15AnchoredAtom3094 Fin15AnchoredAtom3096 Fin15AnchoredAtom3100 Fin15AnchoredAtom3101
    Fin15AnchoredAtom3111 Fin15AnchoredAtom3112 Fin15AnchoredAtom3122 Fin15AnchoredAtom3124
    Fin15AnchoredAtom3128 Fin15AnchoredAtom3129 Fin15AnchoredAtom3139 Fin15AnchoredAtom3140
    Fin15AnchoredAtom3150 Fin15AnchoredAtom3160 Fin15AnchoredAtom3161 Fin15AnchoredAtom3171
    Fin15AnchoredAtom3196 Fin15AnchoredAtom3328 Fin15AnchoredAtom3332 Fin15AnchoredAtom3333
    Fin15AnchoredAtom3343 Fin15AnchoredAtom3344 Fin15AnchoredAtom3354 Fin15AnchoredAtom3364
    Fin15AnchoredAtom3365 Fin15AnchoredAtom3375 Fin15AnchoredAtom3400 Fin15AnchoredAtom3420
    Fin15AnchoredAtom3421 Fin15AnchoredAtom3431 Fin15AnchoredAtom3456 Fin15AnchoredAtom3491
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

theorem fin15Anchored_clause31918 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3087 chi ∧
      ¬Fin15AnchoredAtom3090 chi ∧
      ¬Fin15AnchoredAtom3092 chi ∧
      ¬Fin15AnchoredAtom3093 chi ∧
      ¬Fin15AnchoredAtom3097 chi ∧
      ¬Fin15AnchoredAtom3099 chi ∧
      ¬Fin15AnchoredAtom3100 chi ∧
      ¬Fin15AnchoredAtom3114 chi ∧
      ¬Fin15AnchoredAtom3115 chi ∧
      ¬Fin15AnchoredAtom3120 chi ∧
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
  refine ⟨{1, 3, 5, 6, 7, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13546
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3087 Fin15AnchoredAtom3090 Fin15AnchoredAtom3092
    Fin15AnchoredAtom3093 Fin15AnchoredAtom3097 Fin15AnchoredAtom3099 Fin15AnchoredAtom3100
    Fin15AnchoredAtom3114 Fin15AnchoredAtom3115 Fin15AnchoredAtom3120 Fin15AnchoredAtom3125
    Fin15AnchoredAtom3127 Fin15AnchoredAtom3128 Fin15AnchoredAtom3142 Fin15AnchoredAtom3143
    Fin15AnchoredAtom3148 Fin15AnchoredAtom3163 Fin15AnchoredAtom3164 Fin15AnchoredAtom3169
    Fin15AnchoredAtom3200 Fin15AnchoredAtom3329 Fin15AnchoredAtom3331 Fin15AnchoredAtom3332
    Fin15AnchoredAtom3346 Fin15AnchoredAtom3347 Fin15AnchoredAtom3352 Fin15AnchoredAtom3367
    Fin15AnchoredAtom3368 Fin15AnchoredAtom3373 Fin15AnchoredAtom3404 Fin15AnchoredAtom3423
    Fin15AnchoredAtom3424 Fin15AnchoredAtom3429 Fin15AnchoredAtom3460 Fin15AnchoredAtom3495
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

theorem fin15Anchored_clause31919 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3087 chi ∧
      ¬Fin15AnchoredAtom3090 chi ∧
      ¬Fin15AnchoredAtom3092 chi ∧
      ¬Fin15AnchoredAtom3094 chi ∧
      ¬Fin15AnchoredAtom3097 chi ∧
      ¬Fin15AnchoredAtom3099 chi ∧
      ¬Fin15AnchoredAtom3101 chi ∧
      ¬Fin15AnchoredAtom3114 chi ∧
      ¬Fin15AnchoredAtom3116 chi ∧
      ¬Fin15AnchoredAtom3121 chi ∧
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
  refine ⟨{1, 3, 5, 6, 7, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21738
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3087 Fin15AnchoredAtom3090 Fin15AnchoredAtom3092
    Fin15AnchoredAtom3094 Fin15AnchoredAtom3097 Fin15AnchoredAtom3099 Fin15AnchoredAtom3101
    Fin15AnchoredAtom3114 Fin15AnchoredAtom3116 Fin15AnchoredAtom3121 Fin15AnchoredAtom3125
    Fin15AnchoredAtom3127 Fin15AnchoredAtom3129 Fin15AnchoredAtom3142 Fin15AnchoredAtom3144
    Fin15AnchoredAtom3149 Fin15AnchoredAtom3163 Fin15AnchoredAtom3165 Fin15AnchoredAtom3170
    Fin15AnchoredAtom3201 Fin15AnchoredAtom3329 Fin15AnchoredAtom3331 Fin15AnchoredAtom3333
    Fin15AnchoredAtom3346 Fin15AnchoredAtom3348 Fin15AnchoredAtom3353 Fin15AnchoredAtom3367
    Fin15AnchoredAtom3369 Fin15AnchoredAtom3374 Fin15AnchoredAtom3405 Fin15AnchoredAtom3423
    Fin15AnchoredAtom3425 Fin15AnchoredAtom3430 Fin15AnchoredAtom3461 Fin15AnchoredAtom3496
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

theorem fin15Anchored_clause31920 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3087 chi ∧
      ¬Fin15AnchoredAtom3090 chi ∧
      ¬Fin15AnchoredAtom3093 chi ∧
      ¬Fin15AnchoredAtom3094 chi ∧
      ¬Fin15AnchoredAtom3097 chi ∧
      ¬Fin15AnchoredAtom3100 chi ∧
      ¬Fin15AnchoredAtom3101 chi ∧
      ¬Fin15AnchoredAtom3115 chi ∧
      ¬Fin15AnchoredAtom3116 chi ∧
      ¬Fin15AnchoredAtom3122 chi ∧
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
  refine ⟨{1, 3, 5, 6, 7, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25834
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3087 Fin15AnchoredAtom3090 Fin15AnchoredAtom3093
    Fin15AnchoredAtom3094 Fin15AnchoredAtom3097 Fin15AnchoredAtom3100 Fin15AnchoredAtom3101
    Fin15AnchoredAtom3115 Fin15AnchoredAtom3116 Fin15AnchoredAtom3122 Fin15AnchoredAtom3125
    Fin15AnchoredAtom3128 Fin15AnchoredAtom3129 Fin15AnchoredAtom3143 Fin15AnchoredAtom3144
    Fin15AnchoredAtom3150 Fin15AnchoredAtom3164 Fin15AnchoredAtom3165 Fin15AnchoredAtom3171
    Fin15AnchoredAtom3202 Fin15AnchoredAtom3329 Fin15AnchoredAtom3332 Fin15AnchoredAtom3333
    Fin15AnchoredAtom3347 Fin15AnchoredAtom3348 Fin15AnchoredAtom3354 Fin15AnchoredAtom3368
    Fin15AnchoredAtom3369 Fin15AnchoredAtom3375 Fin15AnchoredAtom3406 Fin15AnchoredAtom3424
    Fin15AnchoredAtom3425 Fin15AnchoredAtom3431 Fin15AnchoredAtom3462 Fin15AnchoredAtom3497
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

theorem fin15Anchored_clause31921 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3087 chi ∧
      ¬Fin15AnchoredAtom3092 chi ∧
      ¬Fin15AnchoredAtom3093 chi ∧
      ¬Fin15AnchoredAtom3094 chi ∧
      ¬Fin15AnchoredAtom3099 chi ∧
      ¬Fin15AnchoredAtom3100 chi ∧
      ¬Fin15AnchoredAtom3101 chi ∧
      ¬Fin15AnchoredAtom3120 chi ∧
      ¬Fin15AnchoredAtom3121 chi ∧
      ¬Fin15AnchoredAtom3122 chi ∧
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
  refine ⟨{1, 3, 5, 6, 7, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask28906
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3087 Fin15AnchoredAtom3092 Fin15AnchoredAtom3093
    Fin15AnchoredAtom3094 Fin15AnchoredAtom3099 Fin15AnchoredAtom3100 Fin15AnchoredAtom3101
    Fin15AnchoredAtom3120 Fin15AnchoredAtom3121 Fin15AnchoredAtom3122 Fin15AnchoredAtom3127
    Fin15AnchoredAtom3128 Fin15AnchoredAtom3129 Fin15AnchoredAtom3148 Fin15AnchoredAtom3149
    Fin15AnchoredAtom3150 Fin15AnchoredAtom3169 Fin15AnchoredAtom3170 Fin15AnchoredAtom3171
    Fin15AnchoredAtom3206 Fin15AnchoredAtom3331 Fin15AnchoredAtom3332 Fin15AnchoredAtom3333
    Fin15AnchoredAtom3352 Fin15AnchoredAtom3353 Fin15AnchoredAtom3354 Fin15AnchoredAtom3373
    Fin15AnchoredAtom3374 Fin15AnchoredAtom3375 Fin15AnchoredAtom3410 Fin15AnchoredAtom3429
    Fin15AnchoredAtom3430 Fin15AnchoredAtom3431 Fin15AnchoredAtom3466 Fin15AnchoredAtom3501
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

theorem fin15Anchored_clause31922 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3088 chi ∧
      ¬Fin15AnchoredAtom3089 chi ∧
      ¬Fin15AnchoredAtom3090 chi ∧
      ¬Fin15AnchoredAtom3093 chi ∧
      ¬Fin15AnchoredAtom3102 chi ∧
      ¬Fin15AnchoredAtom3103 chi ∧
      ¬Fin15AnchoredAtom3106 chi ∧
      ¬Fin15AnchoredAtom3108 chi ∧
      ¬Fin15AnchoredAtom3111 chi ∧
      ¬Fin15AnchoredAtom3115 chi ∧
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
      ¬Fin15AnchoredAtom3334 chi ∧
      ¬Fin15AnchoredAtom3335 chi ∧
      ¬Fin15AnchoredAtom3338 chi ∧
      ¬Fin15AnchoredAtom3340 chi ∧
      ¬Fin15AnchoredAtom3343 chi ∧
      ¬Fin15AnchoredAtom3347 chi ∧
      ¬Fin15AnchoredAtom3376 chi ∧
      ¬Fin15AnchoredAtom3379 chi ∧
      ¬Fin15AnchoredAtom3383 chi ∧
      ¬Fin15AnchoredAtom3393 chi ∧
      ¬Fin15AnchoredAtom3432 chi ∧
      ¬Fin15AnchoredAtom3435 chi ∧
      ¬Fin15AnchoredAtom3439 chi ∧
      ¬Fin15AnchoredAtom3449 chi ∧
      ¬Fin15AnchoredAtom3504 chi ∧
      ¬Fin15AnchoredAtom4159 chi ∧
      ¬Fin15AnchoredAtom4160 chi ∧
      ¬Fin15AnchoredAtom4163 chi ∧
      ¬Fin15AnchoredAtom4165 chi ∧
      ¬Fin15AnchoredAtom4168 chi ∧
      ¬Fin15AnchoredAtom4172 chi ∧
      ¬Fin15AnchoredAtom4201 chi ∧
      ¬Fin15AnchoredAtom4204 chi ∧
      ¬Fin15AnchoredAtom4208 chi ∧
      ¬Fin15AnchoredAtom4218 chi ∧
      ¬Fin15AnchoredAtom4257 chi ∧
      ¬Fin15AnchoredAtom4260 chi ∧
      ¬Fin15AnchoredAtom4264 chi ∧
      ¬Fin15AnchoredAtom4274 chi ∧
      ¬Fin15AnchoredAtom4329 chi ∧
      ¬Fin15AnchoredAtom4593 chi ∧
      ¬Fin15AnchoredAtom4596 chi ∧
      ¬Fin15AnchoredAtom4600 chi ∧
      ¬Fin15AnchoredAtom4610 chi ∧
      ¬Fin15AnchoredAtom4665 chi ∧
      ¬Fin15AnchoredAtom4735 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 3, 5, 6, 8, 9, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask10090
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3088 Fin15AnchoredAtom3089 Fin15AnchoredAtom3090
    Fin15AnchoredAtom3093 Fin15AnchoredAtom3102 Fin15AnchoredAtom3103 Fin15AnchoredAtom3106
    Fin15AnchoredAtom3108 Fin15AnchoredAtom3111 Fin15AnchoredAtom3115 Fin15AnchoredAtom3130
    Fin15AnchoredAtom3131 Fin15AnchoredAtom3134 Fin15AnchoredAtom3136 Fin15AnchoredAtom3139
    Fin15AnchoredAtom3143 Fin15AnchoredAtom3172 Fin15AnchoredAtom3175 Fin15AnchoredAtom3179
    Fin15AnchoredAtom3189 Fin15AnchoredAtom3334 Fin15AnchoredAtom3335 Fin15AnchoredAtom3338
    Fin15AnchoredAtom3340 Fin15AnchoredAtom3343 Fin15AnchoredAtom3347 Fin15AnchoredAtom3376
    Fin15AnchoredAtom3379 Fin15AnchoredAtom3383 Fin15AnchoredAtom3393 Fin15AnchoredAtom3432
    Fin15AnchoredAtom3435 Fin15AnchoredAtom3439 Fin15AnchoredAtom3449 Fin15AnchoredAtom3504
    Fin15AnchoredAtom4159 Fin15AnchoredAtom4160 Fin15AnchoredAtom4163 Fin15AnchoredAtom4165
    Fin15AnchoredAtom4168 Fin15AnchoredAtom4172 Fin15AnchoredAtom4201 Fin15AnchoredAtom4204
    Fin15AnchoredAtom4208 Fin15AnchoredAtom4218 Fin15AnchoredAtom4257 Fin15AnchoredAtom4260
    Fin15AnchoredAtom4264 Fin15AnchoredAtom4274 Fin15AnchoredAtom4329 Fin15AnchoredAtom4593
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

theorem fin15Anchored_clause31923 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3089 chi ∧
      ¬Fin15AnchoredAtom3090 chi ∧
      ¬Fin15AnchoredAtom3092 chi ∧
      ¬Fin15AnchoredAtom3093 chi ∧
      ¬Fin15AnchoredAtom3108 chi ∧
      ¬Fin15AnchoredAtom3110 chi ∧
      ¬Fin15AnchoredAtom3111 chi ∧
      ¬Fin15AnchoredAtom3114 chi ∧
      ¬Fin15AnchoredAtom3115 chi ∧
      ¬Fin15AnchoredAtom3120 chi ∧
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
  refine ⟨{1, 3, 5, 6, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13930
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3089 Fin15AnchoredAtom3090 Fin15AnchoredAtom3092
    Fin15AnchoredAtom3093 Fin15AnchoredAtom3108 Fin15AnchoredAtom3110 Fin15AnchoredAtom3111
    Fin15AnchoredAtom3114 Fin15AnchoredAtom3115 Fin15AnchoredAtom3120 Fin15AnchoredAtom3136
    Fin15AnchoredAtom3138 Fin15AnchoredAtom3139 Fin15AnchoredAtom3142 Fin15AnchoredAtom3143
    Fin15AnchoredAtom3148 Fin15AnchoredAtom3188 Fin15AnchoredAtom3189 Fin15AnchoredAtom3194
    Fin15AnchoredAtom3200 Fin15AnchoredAtom3340 Fin15AnchoredAtom3342 Fin15AnchoredAtom3343
    Fin15AnchoredAtom3346 Fin15AnchoredAtom3347 Fin15AnchoredAtom3352 Fin15AnchoredAtom3392
    Fin15AnchoredAtom3393 Fin15AnchoredAtom3398 Fin15AnchoredAtom3404 Fin15AnchoredAtom3448
    Fin15AnchoredAtom3449 Fin15AnchoredAtom3454 Fin15AnchoredAtom3460 Fin15AnchoredAtom3525
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

theorem fin15Anchored_clause31924 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3089 chi ∧
      ¬Fin15AnchoredAtom3090 chi ∧
      ¬Fin15AnchoredAtom3092 chi ∧
      ¬Fin15AnchoredAtom3094 chi ∧
      ¬Fin15AnchoredAtom3108 chi ∧
      ¬Fin15AnchoredAtom3110 chi ∧
      ¬Fin15AnchoredAtom3112 chi ∧
      ¬Fin15AnchoredAtom3114 chi ∧
      ¬Fin15AnchoredAtom3116 chi ∧
      ¬Fin15AnchoredAtom3121 chi ∧
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
  refine ⟨{1, 3, 5, 6, 9, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22122
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3089 Fin15AnchoredAtom3090 Fin15AnchoredAtom3092
    Fin15AnchoredAtom3094 Fin15AnchoredAtom3108 Fin15AnchoredAtom3110 Fin15AnchoredAtom3112
    Fin15AnchoredAtom3114 Fin15AnchoredAtom3116 Fin15AnchoredAtom3121 Fin15AnchoredAtom3136
    Fin15AnchoredAtom3138 Fin15AnchoredAtom3140 Fin15AnchoredAtom3142 Fin15AnchoredAtom3144
    Fin15AnchoredAtom3149 Fin15AnchoredAtom3188 Fin15AnchoredAtom3190 Fin15AnchoredAtom3195
    Fin15AnchoredAtom3201 Fin15AnchoredAtom3340 Fin15AnchoredAtom3342 Fin15AnchoredAtom3344
    Fin15AnchoredAtom3346 Fin15AnchoredAtom3348 Fin15AnchoredAtom3353 Fin15AnchoredAtom3392
    Fin15AnchoredAtom3394 Fin15AnchoredAtom3399 Fin15AnchoredAtom3405 Fin15AnchoredAtom3448
    Fin15AnchoredAtom3450 Fin15AnchoredAtom3455 Fin15AnchoredAtom3461 Fin15AnchoredAtom3526
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

theorem fin15Anchored_clause31925 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3089 chi ∧
      ¬Fin15AnchoredAtom3090 chi ∧
      ¬Fin15AnchoredAtom3093 chi ∧
      ¬Fin15AnchoredAtom3094 chi ∧
      ¬Fin15AnchoredAtom3108 chi ∧
      ¬Fin15AnchoredAtom3111 chi ∧
      ¬Fin15AnchoredAtom3112 chi ∧
      ¬Fin15AnchoredAtom3115 chi ∧
      ¬Fin15AnchoredAtom3116 chi ∧
      ¬Fin15AnchoredAtom3122 chi ∧
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
  refine ⟨{1, 3, 5, 6, 9, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26218
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3089 Fin15AnchoredAtom3090 Fin15AnchoredAtom3093
    Fin15AnchoredAtom3094 Fin15AnchoredAtom3108 Fin15AnchoredAtom3111 Fin15AnchoredAtom3112
    Fin15AnchoredAtom3115 Fin15AnchoredAtom3116 Fin15AnchoredAtom3122 Fin15AnchoredAtom3136
    Fin15AnchoredAtom3139 Fin15AnchoredAtom3140 Fin15AnchoredAtom3143 Fin15AnchoredAtom3144
    Fin15AnchoredAtom3150 Fin15AnchoredAtom3189 Fin15AnchoredAtom3190 Fin15AnchoredAtom3196
    Fin15AnchoredAtom3202 Fin15AnchoredAtom3340 Fin15AnchoredAtom3343 Fin15AnchoredAtom3344
    Fin15AnchoredAtom3347 Fin15AnchoredAtom3348 Fin15AnchoredAtom3354 Fin15AnchoredAtom3393
    Fin15AnchoredAtom3394 Fin15AnchoredAtom3400 Fin15AnchoredAtom3406 Fin15AnchoredAtom3449
    Fin15AnchoredAtom3450 Fin15AnchoredAtom3456 Fin15AnchoredAtom3462 Fin15AnchoredAtom3527
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

theorem fin15Anchored_clause31926 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3089 chi ∧
      ¬Fin15AnchoredAtom3092 chi ∧
      ¬Fin15AnchoredAtom3093 chi ∧
      ¬Fin15AnchoredAtom3094 chi ∧
      ¬Fin15AnchoredAtom3110 chi ∧
      ¬Fin15AnchoredAtom3111 chi ∧
      ¬Fin15AnchoredAtom3112 chi ∧
      ¬Fin15AnchoredAtom3120 chi ∧
      ¬Fin15AnchoredAtom3121 chi ∧
      ¬Fin15AnchoredAtom3122 chi ∧
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
  refine ⟨{1, 3, 5, 6, 9, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29290
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3089 Fin15AnchoredAtom3092 Fin15AnchoredAtom3093
    Fin15AnchoredAtom3094 Fin15AnchoredAtom3110 Fin15AnchoredAtom3111 Fin15AnchoredAtom3112
    Fin15AnchoredAtom3120 Fin15AnchoredAtom3121 Fin15AnchoredAtom3122 Fin15AnchoredAtom3138
    Fin15AnchoredAtom3139 Fin15AnchoredAtom3140 Fin15AnchoredAtom3148 Fin15AnchoredAtom3149
    Fin15AnchoredAtom3150 Fin15AnchoredAtom3194 Fin15AnchoredAtom3195 Fin15AnchoredAtom3196
    Fin15AnchoredAtom3206 Fin15AnchoredAtom3342 Fin15AnchoredAtom3343 Fin15AnchoredAtom3344
    Fin15AnchoredAtom3352 Fin15AnchoredAtom3353 Fin15AnchoredAtom3354 Fin15AnchoredAtom3398
    Fin15AnchoredAtom3399 Fin15AnchoredAtom3400 Fin15AnchoredAtom3410 Fin15AnchoredAtom3454
    Fin15AnchoredAtom3455 Fin15AnchoredAtom3456 Fin15AnchoredAtom3466 Fin15AnchoredAtom3531
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

theorem fin15Anchored_clause31927 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3090 chi ∧
      ¬Fin15AnchoredAtom3092 chi ∧
      ¬Fin15AnchoredAtom3093 chi ∧
      ¬Fin15AnchoredAtom3094 chi ∧
      ¬Fin15AnchoredAtom3114 chi ∧
      ¬Fin15AnchoredAtom3115 chi ∧
      ¬Fin15AnchoredAtom3116 chi ∧
      ¬Fin15AnchoredAtom3120 chi ∧
      ¬Fin15AnchoredAtom3121 chi ∧
      ¬Fin15AnchoredAtom3122 chi ∧
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
  refine ⟨{1, 3, 5, 6, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29802
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3090 Fin15AnchoredAtom3092 Fin15AnchoredAtom3093
    Fin15AnchoredAtom3094 Fin15AnchoredAtom3114 Fin15AnchoredAtom3115 Fin15AnchoredAtom3116
    Fin15AnchoredAtom3120 Fin15AnchoredAtom3121 Fin15AnchoredAtom3122 Fin15AnchoredAtom3142
    Fin15AnchoredAtom3143 Fin15AnchoredAtom3144 Fin15AnchoredAtom3148 Fin15AnchoredAtom3149
    Fin15AnchoredAtom3150 Fin15AnchoredAtom3200 Fin15AnchoredAtom3201 Fin15AnchoredAtom3202
    Fin15AnchoredAtom3206 Fin15AnchoredAtom3346 Fin15AnchoredAtom3347 Fin15AnchoredAtom3348
    Fin15AnchoredAtom3352 Fin15AnchoredAtom3353 Fin15AnchoredAtom3354 Fin15AnchoredAtom3404
    Fin15AnchoredAtom3405 Fin15AnchoredAtom3406 Fin15AnchoredAtom3410 Fin15AnchoredAtom3460
    Fin15AnchoredAtom3461 Fin15AnchoredAtom3462 Fin15AnchoredAtom3466 Fin15AnchoredAtom3535
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

theorem fin15Anchored_clause31928 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3096 chi ∧
      ¬Fin15AnchoredAtom3097 chi ∧
      ¬Fin15AnchoredAtom3099 chi ∧
      ¬Fin15AnchoredAtom3100 chi ∧
      ¬Fin15AnchoredAtom3108 chi ∧
      ¬Fin15AnchoredAtom3110 chi ∧
      ¬Fin15AnchoredAtom3111 chi ∧
      ¬Fin15AnchoredAtom3114 chi ∧
      ¬Fin15AnchoredAtom3115 chi ∧
      ¬Fin15AnchoredAtom3120 chi ∧
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
  refine ⟨{1, 3, 5, 7, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13994
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3096 Fin15AnchoredAtom3097 Fin15AnchoredAtom3099
    Fin15AnchoredAtom3100 Fin15AnchoredAtom3108 Fin15AnchoredAtom3110 Fin15AnchoredAtom3111
    Fin15AnchoredAtom3114 Fin15AnchoredAtom3115 Fin15AnchoredAtom3120 Fin15AnchoredAtom3157
    Fin15AnchoredAtom3159 Fin15AnchoredAtom3160 Fin15AnchoredAtom3163 Fin15AnchoredAtom3164
    Fin15AnchoredAtom3169 Fin15AnchoredAtom3188 Fin15AnchoredAtom3189 Fin15AnchoredAtom3194
    Fin15AnchoredAtom3200 Fin15AnchoredAtom3361 Fin15AnchoredAtom3363 Fin15AnchoredAtom3364
    Fin15AnchoredAtom3367 Fin15AnchoredAtom3368 Fin15AnchoredAtom3373 Fin15AnchoredAtom3392
    Fin15AnchoredAtom3393 Fin15AnchoredAtom3398 Fin15AnchoredAtom3404 Fin15AnchoredAtom3483
    Fin15AnchoredAtom3484 Fin15AnchoredAtom3489 Fin15AnchoredAtom3495 Fin15AnchoredAtom3525
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

theorem fin15Anchored_clause31929 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3096 chi ∧
      ¬Fin15AnchoredAtom3097 chi ∧
      ¬Fin15AnchoredAtom3099 chi ∧
      ¬Fin15AnchoredAtom3101 chi ∧
      ¬Fin15AnchoredAtom3108 chi ∧
      ¬Fin15AnchoredAtom3110 chi ∧
      ¬Fin15AnchoredAtom3112 chi ∧
      ¬Fin15AnchoredAtom3114 chi ∧
      ¬Fin15AnchoredAtom3116 chi ∧
      ¬Fin15AnchoredAtom3121 chi ∧
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
  refine ⟨{1, 3, 5, 7, 9, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22186
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3096 Fin15AnchoredAtom3097 Fin15AnchoredAtom3099
    Fin15AnchoredAtom3101 Fin15AnchoredAtom3108 Fin15AnchoredAtom3110 Fin15AnchoredAtom3112
    Fin15AnchoredAtom3114 Fin15AnchoredAtom3116 Fin15AnchoredAtom3121 Fin15AnchoredAtom3157
    Fin15AnchoredAtom3159 Fin15AnchoredAtom3161 Fin15AnchoredAtom3163 Fin15AnchoredAtom3165
    Fin15AnchoredAtom3170 Fin15AnchoredAtom3188 Fin15AnchoredAtom3190 Fin15AnchoredAtom3195
    Fin15AnchoredAtom3201 Fin15AnchoredAtom3361 Fin15AnchoredAtom3363 Fin15AnchoredAtom3365
    Fin15AnchoredAtom3367 Fin15AnchoredAtom3369 Fin15AnchoredAtom3374 Fin15AnchoredAtom3392
    Fin15AnchoredAtom3394 Fin15AnchoredAtom3399 Fin15AnchoredAtom3405 Fin15AnchoredAtom3483
    Fin15AnchoredAtom3485 Fin15AnchoredAtom3490 Fin15AnchoredAtom3496 Fin15AnchoredAtom3526
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

theorem fin15Anchored_clause31930 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3096 chi ∧
      ¬Fin15AnchoredAtom3097 chi ∧
      ¬Fin15AnchoredAtom3100 chi ∧
      ¬Fin15AnchoredAtom3101 chi ∧
      ¬Fin15AnchoredAtom3108 chi ∧
      ¬Fin15AnchoredAtom3111 chi ∧
      ¬Fin15AnchoredAtom3112 chi ∧
      ¬Fin15AnchoredAtom3115 chi ∧
      ¬Fin15AnchoredAtom3116 chi ∧
      ¬Fin15AnchoredAtom3122 chi ∧
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
  refine ⟨{1, 3, 5, 7, 9, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26282
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3096 Fin15AnchoredAtom3097 Fin15AnchoredAtom3100
    Fin15AnchoredAtom3101 Fin15AnchoredAtom3108 Fin15AnchoredAtom3111 Fin15AnchoredAtom3112
    Fin15AnchoredAtom3115 Fin15AnchoredAtom3116 Fin15AnchoredAtom3122 Fin15AnchoredAtom3157
    Fin15AnchoredAtom3160 Fin15AnchoredAtom3161 Fin15AnchoredAtom3164 Fin15AnchoredAtom3165
    Fin15AnchoredAtom3171 Fin15AnchoredAtom3189 Fin15AnchoredAtom3190 Fin15AnchoredAtom3196
    Fin15AnchoredAtom3202 Fin15AnchoredAtom3361 Fin15AnchoredAtom3364 Fin15AnchoredAtom3365
    Fin15AnchoredAtom3368 Fin15AnchoredAtom3369 Fin15AnchoredAtom3375 Fin15AnchoredAtom3393
    Fin15AnchoredAtom3394 Fin15AnchoredAtom3400 Fin15AnchoredAtom3406 Fin15AnchoredAtom3484
    Fin15AnchoredAtom3485 Fin15AnchoredAtom3491 Fin15AnchoredAtom3497 Fin15AnchoredAtom3527
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

theorem fin15Anchored_clause31931 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3096 chi ∧
      ¬Fin15AnchoredAtom3098 chi ∧
      ¬Fin15AnchoredAtom3099 chi ∧
      ¬Fin15AnchoredAtom3101 chi ∧
      ¬Fin15AnchoredAtom3109 chi ∧
      ¬Fin15AnchoredAtom3110 chi ∧
      ¬Fin15AnchoredAtom3112 chi ∧
      ¬Fin15AnchoredAtom3117 chi ∧
      ¬Fin15AnchoredAtom3119 chi ∧
      ¬Fin15AnchoredAtom3121 chi ∧
      ¬Fin15AnchoredAtom3158 chi ∧
      ¬Fin15AnchoredAtom3159 chi ∧
      ¬Fin15AnchoredAtom3161 chi ∧
      ¬Fin15AnchoredAtom3166 chi ∧
      ¬Fin15AnchoredAtom3168 chi ∧
      ¬Fin15AnchoredAtom3170 chi ∧
      ¬Fin15AnchoredAtom3191 chi ∧
      ¬Fin15AnchoredAtom3193 chi ∧
      ¬Fin15AnchoredAtom3195 chi ∧
      ¬Fin15AnchoredAtom3204 chi ∧
      ¬Fin15AnchoredAtom3362 chi ∧
      ¬Fin15AnchoredAtom3363 chi ∧
      ¬Fin15AnchoredAtom3365 chi ∧
      ¬Fin15AnchoredAtom3370 chi ∧
      ¬Fin15AnchoredAtom3372 chi ∧
      ¬Fin15AnchoredAtom3374 chi ∧
      ¬Fin15AnchoredAtom3395 chi ∧
      ¬Fin15AnchoredAtom3397 chi ∧
      ¬Fin15AnchoredAtom3399 chi ∧
      ¬Fin15AnchoredAtom3408 chi ∧
      ¬Fin15AnchoredAtom3486 chi ∧
      ¬Fin15AnchoredAtom3488 chi ∧
      ¬Fin15AnchoredAtom3490 chi ∧
      ¬Fin15AnchoredAtom3499 chi ∧
      ¬Fin15AnchoredAtom3529 chi ∧
      ¬Fin15AnchoredAtom4187 chi ∧
      ¬Fin15AnchoredAtom4188 chi ∧
      ¬Fin15AnchoredAtom4190 chi ∧
      ¬Fin15AnchoredAtom4195 chi ∧
      ¬Fin15AnchoredAtom4197 chi ∧
      ¬Fin15AnchoredAtom4199 chi ∧
      ¬Fin15AnchoredAtom4220 chi ∧
      ¬Fin15AnchoredAtom4222 chi ∧
      ¬Fin15AnchoredAtom4224 chi ∧
      ¬Fin15AnchoredAtom4233 chi ∧
      ¬Fin15AnchoredAtom4311 chi ∧
      ¬Fin15AnchoredAtom4313 chi ∧
      ¬Fin15AnchoredAtom4315 chi ∧
      ¬Fin15AnchoredAtom4324 chi ∧
      ¬Fin15AnchoredAtom4354 chi ∧
      ¬Fin15AnchoredAtom4647 chi ∧
      ¬Fin15AnchoredAtom4649 chi ∧
      ¬Fin15AnchoredAtom4651 chi ∧
      ¬Fin15AnchoredAtom4660 chi ∧
      ¬Fin15AnchoredAtom4690 chi ∧
      ¬Fin15AnchoredAtom4795 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 3, 5, 7, 9, 11, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask23210
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3096 Fin15AnchoredAtom3098 Fin15AnchoredAtom3099
    Fin15AnchoredAtom3101 Fin15AnchoredAtom3109 Fin15AnchoredAtom3110 Fin15AnchoredAtom3112
    Fin15AnchoredAtom3117 Fin15AnchoredAtom3119 Fin15AnchoredAtom3121 Fin15AnchoredAtom3158
    Fin15AnchoredAtom3159 Fin15AnchoredAtom3161 Fin15AnchoredAtom3166 Fin15AnchoredAtom3168
    Fin15AnchoredAtom3170 Fin15AnchoredAtom3191 Fin15AnchoredAtom3193 Fin15AnchoredAtom3195
    Fin15AnchoredAtom3204 Fin15AnchoredAtom3362 Fin15AnchoredAtom3363 Fin15AnchoredAtom3365
    Fin15AnchoredAtom3370 Fin15AnchoredAtom3372 Fin15AnchoredAtom3374 Fin15AnchoredAtom3395
    Fin15AnchoredAtom3397 Fin15AnchoredAtom3399 Fin15AnchoredAtom3408 Fin15AnchoredAtom3486
    Fin15AnchoredAtom3488 Fin15AnchoredAtom3490 Fin15AnchoredAtom3499 Fin15AnchoredAtom3529
    Fin15AnchoredAtom4187 Fin15AnchoredAtom4188 Fin15AnchoredAtom4190 Fin15AnchoredAtom4195
    Fin15AnchoredAtom4197 Fin15AnchoredAtom4199 Fin15AnchoredAtom4220 Fin15AnchoredAtom4222
    Fin15AnchoredAtom4224 Fin15AnchoredAtom4233 Fin15AnchoredAtom4311 Fin15AnchoredAtom4313
    Fin15AnchoredAtom4315 Fin15AnchoredAtom4324 Fin15AnchoredAtom4354 Fin15AnchoredAtom4647
    Fin15AnchoredAtom4649 Fin15AnchoredAtom4651 Fin15AnchoredAtom4660 Fin15AnchoredAtom4690
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

theorem fin15Anchored_clause31932 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3096 chi ∧
      ¬Fin15AnchoredAtom3099 chi ∧
      ¬Fin15AnchoredAtom3100 chi ∧
      ¬Fin15AnchoredAtom3101 chi ∧
      ¬Fin15AnchoredAtom3110 chi ∧
      ¬Fin15AnchoredAtom3111 chi ∧
      ¬Fin15AnchoredAtom3112 chi ∧
      ¬Fin15AnchoredAtom3120 chi ∧
      ¬Fin15AnchoredAtom3121 chi ∧
      ¬Fin15AnchoredAtom3122 chi ∧
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
  refine ⟨{1, 3, 5, 7, 9, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29354
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3096 Fin15AnchoredAtom3099 Fin15AnchoredAtom3100
    Fin15AnchoredAtom3101 Fin15AnchoredAtom3110 Fin15AnchoredAtom3111 Fin15AnchoredAtom3112
    Fin15AnchoredAtom3120 Fin15AnchoredAtom3121 Fin15AnchoredAtom3122 Fin15AnchoredAtom3159
    Fin15AnchoredAtom3160 Fin15AnchoredAtom3161 Fin15AnchoredAtom3169 Fin15AnchoredAtom3170
    Fin15AnchoredAtom3171 Fin15AnchoredAtom3194 Fin15AnchoredAtom3195 Fin15AnchoredAtom3196
    Fin15AnchoredAtom3206 Fin15AnchoredAtom3363 Fin15AnchoredAtom3364 Fin15AnchoredAtom3365
    Fin15AnchoredAtom3373 Fin15AnchoredAtom3374 Fin15AnchoredAtom3375 Fin15AnchoredAtom3398
    Fin15AnchoredAtom3399 Fin15AnchoredAtom3400 Fin15AnchoredAtom3410 Fin15AnchoredAtom3489
    Fin15AnchoredAtom3490 Fin15AnchoredAtom3491 Fin15AnchoredAtom3501 Fin15AnchoredAtom3531
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

theorem fin15Anchored_clause31933 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3097 chi ∧
      ¬Fin15AnchoredAtom3099 chi ∧
      ¬Fin15AnchoredAtom3100 chi ∧
      ¬Fin15AnchoredAtom3101 chi ∧
      ¬Fin15AnchoredAtom3114 chi ∧
      ¬Fin15AnchoredAtom3115 chi ∧
      ¬Fin15AnchoredAtom3116 chi ∧
      ¬Fin15AnchoredAtom3120 chi ∧
      ¬Fin15AnchoredAtom3121 chi ∧
      ¬Fin15AnchoredAtom3122 chi ∧
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
  refine ⟨{1, 3, 5, 7, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29866
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3097 Fin15AnchoredAtom3099 Fin15AnchoredAtom3100
    Fin15AnchoredAtom3101 Fin15AnchoredAtom3114 Fin15AnchoredAtom3115 Fin15AnchoredAtom3116
    Fin15AnchoredAtom3120 Fin15AnchoredAtom3121 Fin15AnchoredAtom3122 Fin15AnchoredAtom3163
    Fin15AnchoredAtom3164 Fin15AnchoredAtom3165 Fin15AnchoredAtom3169 Fin15AnchoredAtom3170
    Fin15AnchoredAtom3171 Fin15AnchoredAtom3200 Fin15AnchoredAtom3201 Fin15AnchoredAtom3202
    Fin15AnchoredAtom3206 Fin15AnchoredAtom3367 Fin15AnchoredAtom3368 Fin15AnchoredAtom3369
    Fin15AnchoredAtom3373 Fin15AnchoredAtom3374 Fin15AnchoredAtom3375 Fin15AnchoredAtom3404
    Fin15AnchoredAtom3405 Fin15AnchoredAtom3406 Fin15AnchoredAtom3410 Fin15AnchoredAtom3495
    Fin15AnchoredAtom3496 Fin15AnchoredAtom3497 Fin15AnchoredAtom3501 Fin15AnchoredAtom3535
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

theorem fin15Anchored_clause31934 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3108 chi ∧
      ¬Fin15AnchoredAtom3110 chi ∧
      ¬Fin15AnchoredAtom3111 chi ∧
      ¬Fin15AnchoredAtom3112 chi ∧
      ¬Fin15AnchoredAtom3114 chi ∧
      ¬Fin15AnchoredAtom3115 chi ∧
      ¬Fin15AnchoredAtom3116 chi ∧
      ¬Fin15AnchoredAtom3120 chi ∧
      ¬Fin15AnchoredAtom3121 chi ∧
      ¬Fin15AnchoredAtom3122 chi ∧
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
  refine ⟨{1, 3, 5, 9, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask30250
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3108 Fin15AnchoredAtom3110 Fin15AnchoredAtom3111
    Fin15AnchoredAtom3112 Fin15AnchoredAtom3114 Fin15AnchoredAtom3115 Fin15AnchoredAtom3116
    Fin15AnchoredAtom3120 Fin15AnchoredAtom3121 Fin15AnchoredAtom3122 Fin15AnchoredAtom3188
    Fin15AnchoredAtom3189 Fin15AnchoredAtom3190 Fin15AnchoredAtom3194 Fin15AnchoredAtom3195
    Fin15AnchoredAtom3196 Fin15AnchoredAtom3200 Fin15AnchoredAtom3201 Fin15AnchoredAtom3202
    Fin15AnchoredAtom3206 Fin15AnchoredAtom3392 Fin15AnchoredAtom3393 Fin15AnchoredAtom3394
    Fin15AnchoredAtom3398 Fin15AnchoredAtom3399 Fin15AnchoredAtom3400 Fin15AnchoredAtom3404
    Fin15AnchoredAtom3405 Fin15AnchoredAtom3406 Fin15AnchoredAtom3410 Fin15AnchoredAtom3525
    Fin15AnchoredAtom3526 Fin15AnchoredAtom3527 Fin15AnchoredAtom3531 Fin15AnchoredAtom3535
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

theorem fin15Anchored_clause31935 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3124 chi ∧
      ¬Fin15AnchoredAtom3125 chi ∧
      ¬Fin15AnchoredAtom3127 chi ∧
      ¬Fin15AnchoredAtom3128 chi ∧
      ¬Fin15AnchoredAtom3136 chi ∧
      ¬Fin15AnchoredAtom3138 chi ∧
      ¬Fin15AnchoredAtom3139 chi ∧
      ¬Fin15AnchoredAtom3142 chi ∧
      ¬Fin15AnchoredAtom3143 chi ∧
      ¬Fin15AnchoredAtom3148 chi ∧
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
  refine ⟨{1, 3, 6, 7, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask14026
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3124 Fin15AnchoredAtom3125 Fin15AnchoredAtom3127
    Fin15AnchoredAtom3128 Fin15AnchoredAtom3136 Fin15AnchoredAtom3138 Fin15AnchoredAtom3139
    Fin15AnchoredAtom3142 Fin15AnchoredAtom3143 Fin15AnchoredAtom3148 Fin15AnchoredAtom3157
    Fin15AnchoredAtom3159 Fin15AnchoredAtom3160 Fin15AnchoredAtom3163 Fin15AnchoredAtom3164
    Fin15AnchoredAtom3169 Fin15AnchoredAtom3188 Fin15AnchoredAtom3189 Fin15AnchoredAtom3194
    Fin15AnchoredAtom3200 Fin15AnchoredAtom3417 Fin15AnchoredAtom3419 Fin15AnchoredAtom3420
    Fin15AnchoredAtom3423 Fin15AnchoredAtom3424 Fin15AnchoredAtom3429 Fin15AnchoredAtom3448
    Fin15AnchoredAtom3449 Fin15AnchoredAtom3454 Fin15AnchoredAtom3460 Fin15AnchoredAtom3483
    Fin15AnchoredAtom3484 Fin15AnchoredAtom3489 Fin15AnchoredAtom3495 Fin15AnchoredAtom3525
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

theorem fin15Anchored_clause31936 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3124 chi ∧
      ¬Fin15AnchoredAtom3125 chi ∧
      ¬Fin15AnchoredAtom3127 chi ∧
      ¬Fin15AnchoredAtom3129 chi ∧
      ¬Fin15AnchoredAtom3136 chi ∧
      ¬Fin15AnchoredAtom3138 chi ∧
      ¬Fin15AnchoredAtom3140 chi ∧
      ¬Fin15AnchoredAtom3142 chi ∧
      ¬Fin15AnchoredAtom3144 chi ∧
      ¬Fin15AnchoredAtom3149 chi ∧
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
  refine ⟨{1, 3, 6, 7, 9, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22218
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3124 Fin15AnchoredAtom3125 Fin15AnchoredAtom3127
    Fin15AnchoredAtom3129 Fin15AnchoredAtom3136 Fin15AnchoredAtom3138 Fin15AnchoredAtom3140
    Fin15AnchoredAtom3142 Fin15AnchoredAtom3144 Fin15AnchoredAtom3149 Fin15AnchoredAtom3157
    Fin15AnchoredAtom3159 Fin15AnchoredAtom3161 Fin15AnchoredAtom3163 Fin15AnchoredAtom3165
    Fin15AnchoredAtom3170 Fin15AnchoredAtom3188 Fin15AnchoredAtom3190 Fin15AnchoredAtom3195
    Fin15AnchoredAtom3201 Fin15AnchoredAtom3417 Fin15AnchoredAtom3419 Fin15AnchoredAtom3421
    Fin15AnchoredAtom3423 Fin15AnchoredAtom3425 Fin15AnchoredAtom3430 Fin15AnchoredAtom3448
    Fin15AnchoredAtom3450 Fin15AnchoredAtom3455 Fin15AnchoredAtom3461 Fin15AnchoredAtom3483
    Fin15AnchoredAtom3485 Fin15AnchoredAtom3490 Fin15AnchoredAtom3496 Fin15AnchoredAtom3526
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

theorem fin15Anchored_clause31937 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3124 chi ∧
      ¬Fin15AnchoredAtom3125 chi ∧
      ¬Fin15AnchoredAtom3128 chi ∧
      ¬Fin15AnchoredAtom3129 chi ∧
      ¬Fin15AnchoredAtom3136 chi ∧
      ¬Fin15AnchoredAtom3139 chi ∧
      ¬Fin15AnchoredAtom3140 chi ∧
      ¬Fin15AnchoredAtom3143 chi ∧
      ¬Fin15AnchoredAtom3144 chi ∧
      ¬Fin15AnchoredAtom3150 chi ∧
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
  refine ⟨{1, 3, 6, 7, 9, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26314
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3124 Fin15AnchoredAtom3125 Fin15AnchoredAtom3128
    Fin15AnchoredAtom3129 Fin15AnchoredAtom3136 Fin15AnchoredAtom3139 Fin15AnchoredAtom3140
    Fin15AnchoredAtom3143 Fin15AnchoredAtom3144 Fin15AnchoredAtom3150 Fin15AnchoredAtom3157
    Fin15AnchoredAtom3160 Fin15AnchoredAtom3161 Fin15AnchoredAtom3164 Fin15AnchoredAtom3165
    Fin15AnchoredAtom3171 Fin15AnchoredAtom3189 Fin15AnchoredAtom3190 Fin15AnchoredAtom3196
    Fin15AnchoredAtom3202 Fin15AnchoredAtom3417 Fin15AnchoredAtom3420 Fin15AnchoredAtom3421
    Fin15AnchoredAtom3424 Fin15AnchoredAtom3425 Fin15AnchoredAtom3431 Fin15AnchoredAtom3449
    Fin15AnchoredAtom3450 Fin15AnchoredAtom3456 Fin15AnchoredAtom3462 Fin15AnchoredAtom3484
    Fin15AnchoredAtom3485 Fin15AnchoredAtom3491 Fin15AnchoredAtom3497 Fin15AnchoredAtom3527
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

theorem fin15Anchored_clause31938 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3124 chi ∧
      ¬Fin15AnchoredAtom3127 chi ∧
      ¬Fin15AnchoredAtom3128 chi ∧
      ¬Fin15AnchoredAtom3129 chi ∧
      ¬Fin15AnchoredAtom3138 chi ∧
      ¬Fin15AnchoredAtom3139 chi ∧
      ¬Fin15AnchoredAtom3140 chi ∧
      ¬Fin15AnchoredAtom3148 chi ∧
      ¬Fin15AnchoredAtom3149 chi ∧
      ¬Fin15AnchoredAtom3150 chi ∧
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
  refine ⟨{1, 3, 6, 7, 9, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29386
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3124 Fin15AnchoredAtom3127 Fin15AnchoredAtom3128
    Fin15AnchoredAtom3129 Fin15AnchoredAtom3138 Fin15AnchoredAtom3139 Fin15AnchoredAtom3140
    Fin15AnchoredAtom3148 Fin15AnchoredAtom3149 Fin15AnchoredAtom3150 Fin15AnchoredAtom3159
    Fin15AnchoredAtom3160 Fin15AnchoredAtom3161 Fin15AnchoredAtom3169 Fin15AnchoredAtom3170
    Fin15AnchoredAtom3171 Fin15AnchoredAtom3194 Fin15AnchoredAtom3195 Fin15AnchoredAtom3196
    Fin15AnchoredAtom3206 Fin15AnchoredAtom3419 Fin15AnchoredAtom3420 Fin15AnchoredAtom3421
    Fin15AnchoredAtom3429 Fin15AnchoredAtom3430 Fin15AnchoredAtom3431 Fin15AnchoredAtom3454
    Fin15AnchoredAtom3455 Fin15AnchoredAtom3456 Fin15AnchoredAtom3466 Fin15AnchoredAtom3489
    Fin15AnchoredAtom3490 Fin15AnchoredAtom3491 Fin15AnchoredAtom3501 Fin15AnchoredAtom3531
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

theorem fin15Anchored_clause31939 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3125 chi ∧
      ¬Fin15AnchoredAtom3127 chi ∧
      ¬Fin15AnchoredAtom3128 chi ∧
      ¬Fin15AnchoredAtom3129 chi ∧
      ¬Fin15AnchoredAtom3142 chi ∧
      ¬Fin15AnchoredAtom3143 chi ∧
      ¬Fin15AnchoredAtom3144 chi ∧
      ¬Fin15AnchoredAtom3148 chi ∧
      ¬Fin15AnchoredAtom3149 chi ∧
      ¬Fin15AnchoredAtom3150 chi ∧
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
  refine ⟨{1, 3, 6, 7, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29898
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3125 Fin15AnchoredAtom3127 Fin15AnchoredAtom3128
    Fin15AnchoredAtom3129 Fin15AnchoredAtom3142 Fin15AnchoredAtom3143 Fin15AnchoredAtom3144
    Fin15AnchoredAtom3148 Fin15AnchoredAtom3149 Fin15AnchoredAtom3150 Fin15AnchoredAtom3163
    Fin15AnchoredAtom3164 Fin15AnchoredAtom3165 Fin15AnchoredAtom3169 Fin15AnchoredAtom3170
    Fin15AnchoredAtom3171 Fin15AnchoredAtom3200 Fin15AnchoredAtom3201 Fin15AnchoredAtom3202
    Fin15AnchoredAtom3206 Fin15AnchoredAtom3423 Fin15AnchoredAtom3424 Fin15AnchoredAtom3425
    Fin15AnchoredAtom3429 Fin15AnchoredAtom3430 Fin15AnchoredAtom3431 Fin15AnchoredAtom3460
    Fin15AnchoredAtom3461 Fin15AnchoredAtom3462 Fin15AnchoredAtom3466 Fin15AnchoredAtom3495
    Fin15AnchoredAtom3496 Fin15AnchoredAtom3497 Fin15AnchoredAtom3501 Fin15AnchoredAtom3535
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

theorem fin15Anchored_clause31940 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3136 chi ∧
      ¬Fin15AnchoredAtom3138 chi ∧
      ¬Fin15AnchoredAtom3139 chi ∧
      ¬Fin15AnchoredAtom3140 chi ∧
      ¬Fin15AnchoredAtom3142 chi ∧
      ¬Fin15AnchoredAtom3143 chi ∧
      ¬Fin15AnchoredAtom3144 chi ∧
      ¬Fin15AnchoredAtom3148 chi ∧
      ¬Fin15AnchoredAtom3149 chi ∧
      ¬Fin15AnchoredAtom3150 chi ∧
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
  refine ⟨{1, 3, 6, 9, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask30282
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3136 Fin15AnchoredAtom3138 Fin15AnchoredAtom3139
    Fin15AnchoredAtom3140 Fin15AnchoredAtom3142 Fin15AnchoredAtom3143 Fin15AnchoredAtom3144
    Fin15AnchoredAtom3148 Fin15AnchoredAtom3149 Fin15AnchoredAtom3150 Fin15AnchoredAtom3188
    Fin15AnchoredAtom3189 Fin15AnchoredAtom3190 Fin15AnchoredAtom3194 Fin15AnchoredAtom3195
    Fin15AnchoredAtom3196 Fin15AnchoredAtom3200 Fin15AnchoredAtom3201 Fin15AnchoredAtom3202
    Fin15AnchoredAtom3206 Fin15AnchoredAtom3448 Fin15AnchoredAtom3449 Fin15AnchoredAtom3450
    Fin15AnchoredAtom3454 Fin15AnchoredAtom3455 Fin15AnchoredAtom3456 Fin15AnchoredAtom3460
    Fin15AnchoredAtom3461 Fin15AnchoredAtom3462 Fin15AnchoredAtom3466 Fin15AnchoredAtom3525
    Fin15AnchoredAtom3526 Fin15AnchoredAtom3527 Fin15AnchoredAtom3531 Fin15AnchoredAtom3535
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

theorem fin15Anchored_clause31941 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3151 chi ∧
      ¬Fin15AnchoredAtom3152 chi ∧
      ¬Fin15AnchoredAtom3154 chi ∧
      ¬Fin15AnchoredAtom3155 chi ∧
      ¬Fin15AnchoredAtom3157 chi ∧
      ¬Fin15AnchoredAtom3159 chi ∧
      ¬Fin15AnchoredAtom3160 chi ∧
      ¬Fin15AnchoredAtom3163 chi ∧
      ¬Fin15AnchoredAtom3164 chi ∧
      ¬Fin15AnchoredAtom3169 chi ∧
      ¬Fin15AnchoredAtom3172 chi ∧
      ¬Fin15AnchoredAtom3174 chi ∧
      ¬Fin15AnchoredAtom3175 chi ∧
      ¬Fin15AnchoredAtom3178 chi ∧
      ¬Fin15AnchoredAtom3179 chi ∧
      ¬Fin15AnchoredAtom3184 chi ∧
      ¬Fin15AnchoredAtom3188 chi ∧
      ¬Fin15AnchoredAtom3189 chi ∧
      ¬Fin15AnchoredAtom3194 chi ∧
      ¬Fin15AnchoredAtom3200 chi ∧
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
  refine ⟨{1, 3, 7, 8, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask14218
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3151 Fin15AnchoredAtom3152 Fin15AnchoredAtom3154
    Fin15AnchoredAtom3155 Fin15AnchoredAtom3157 Fin15AnchoredAtom3159 Fin15AnchoredAtom3160
    Fin15AnchoredAtom3163 Fin15AnchoredAtom3164 Fin15AnchoredAtom3169 Fin15AnchoredAtom3172
    Fin15AnchoredAtom3174 Fin15AnchoredAtom3175 Fin15AnchoredAtom3178 Fin15AnchoredAtom3179
    Fin15AnchoredAtom3184 Fin15AnchoredAtom3188 Fin15AnchoredAtom3189 Fin15AnchoredAtom3194
    Fin15AnchoredAtom3200 Fin15AnchoredAtom3467 Fin15AnchoredAtom3469 Fin15AnchoredAtom3470
    Fin15AnchoredAtom3473 Fin15AnchoredAtom3474 Fin15AnchoredAtom3479 Fin15AnchoredAtom3483
    Fin15AnchoredAtom3484 Fin15AnchoredAtom3489 Fin15AnchoredAtom3495 Fin15AnchoredAtom3503
    Fin15AnchoredAtom3504 Fin15AnchoredAtom3509 Fin15AnchoredAtom3515 Fin15AnchoredAtom3525
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

theorem fin15Anchored_clause31942 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3151 chi ∧
      ¬Fin15AnchoredAtom3154 chi ∧
      ¬Fin15AnchoredAtom3155 chi ∧
      ¬Fin15AnchoredAtom3156 chi ∧
      ¬Fin15AnchoredAtom3159 chi ∧
      ¬Fin15AnchoredAtom3160 chi ∧
      ¬Fin15AnchoredAtom3161 chi ∧
      ¬Fin15AnchoredAtom3169 chi ∧
      ¬Fin15AnchoredAtom3170 chi ∧
      ¬Fin15AnchoredAtom3171 chi ∧
      ¬Fin15AnchoredAtom3174 chi ∧
      ¬Fin15AnchoredAtom3175 chi ∧
      ¬Fin15AnchoredAtom3176 chi ∧
      ¬Fin15AnchoredAtom3184 chi ∧
      ¬Fin15AnchoredAtom3185 chi ∧
      ¬Fin15AnchoredAtom3186 chi ∧
      ¬Fin15AnchoredAtom3194 chi ∧
      ¬Fin15AnchoredAtom3195 chi ∧
      ¬Fin15AnchoredAtom3196 chi ∧
      ¬Fin15AnchoredAtom3206 chi ∧
      ¬Fin15AnchoredAtom3469 chi ∧
      ¬Fin15AnchoredAtom3470 chi ∧
      ¬Fin15AnchoredAtom3471 chi ∧
      ¬Fin15AnchoredAtom3479 chi ∧
      ¬Fin15AnchoredAtom3480 chi ∧
      ¬Fin15AnchoredAtom3481 chi ∧
      ¬Fin15AnchoredAtom3489 chi ∧
      ¬Fin15AnchoredAtom3490 chi ∧
      ¬Fin15AnchoredAtom3491 chi ∧
      ¬Fin15AnchoredAtom3501 chi ∧
      ¬Fin15AnchoredAtom3509 chi ∧
      ¬Fin15AnchoredAtom3510 chi ∧
      ¬Fin15AnchoredAtom3511 chi ∧
      ¬Fin15AnchoredAtom3521 chi ∧
      ¬Fin15AnchoredAtom3531 chi ∧
      ¬Fin15AnchoredAtom4294 chi ∧
      ¬Fin15AnchoredAtom4295 chi ∧
      ¬Fin15AnchoredAtom4296 chi ∧
      ¬Fin15AnchoredAtom4304 chi ∧
      ¬Fin15AnchoredAtom4305 chi ∧
      ¬Fin15AnchoredAtom4306 chi ∧
      ¬Fin15AnchoredAtom4314 chi ∧
      ¬Fin15AnchoredAtom4315 chi ∧
      ¬Fin15AnchoredAtom4316 chi ∧
      ¬Fin15AnchoredAtom4326 chi ∧
      ¬Fin15AnchoredAtom4334 chi ∧
      ¬Fin15AnchoredAtom4335 chi ∧
      ¬Fin15AnchoredAtom4336 chi ∧
      ¬Fin15AnchoredAtom4346 chi ∧
      ¬Fin15AnchoredAtom4356 chi ∧
      ¬Fin15AnchoredAtom4775 chi ∧
      ¬Fin15AnchoredAtom4776 chi ∧
      ¬Fin15AnchoredAtom4777 chi ∧
      ¬Fin15AnchoredAtom4787 chi ∧
      ¬Fin15AnchoredAtom4797 chi ∧
      ¬Fin15AnchoredAtom4812 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 3, 7, 8, 9, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29578
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3151 Fin15AnchoredAtom3154 Fin15AnchoredAtom3155
    Fin15AnchoredAtom3156 Fin15AnchoredAtom3159 Fin15AnchoredAtom3160 Fin15AnchoredAtom3161
    Fin15AnchoredAtom3169 Fin15AnchoredAtom3170 Fin15AnchoredAtom3171 Fin15AnchoredAtom3174
    Fin15AnchoredAtom3175 Fin15AnchoredAtom3176 Fin15AnchoredAtom3184 Fin15AnchoredAtom3185
    Fin15AnchoredAtom3186 Fin15AnchoredAtom3194 Fin15AnchoredAtom3195 Fin15AnchoredAtom3196
    Fin15AnchoredAtom3206 Fin15AnchoredAtom3469 Fin15AnchoredAtom3470 Fin15AnchoredAtom3471
    Fin15AnchoredAtom3479 Fin15AnchoredAtom3480 Fin15AnchoredAtom3481 Fin15AnchoredAtom3489
    Fin15AnchoredAtom3490 Fin15AnchoredAtom3491 Fin15AnchoredAtom3501 Fin15AnchoredAtom3509
    Fin15AnchoredAtom3510 Fin15AnchoredAtom3511 Fin15AnchoredAtom3521 Fin15AnchoredAtom3531
    Fin15AnchoredAtom4294 Fin15AnchoredAtom4295 Fin15AnchoredAtom4296 Fin15AnchoredAtom4304
    Fin15AnchoredAtom4305 Fin15AnchoredAtom4306 Fin15AnchoredAtom4314 Fin15AnchoredAtom4315
    Fin15AnchoredAtom4316 Fin15AnchoredAtom4326 Fin15AnchoredAtom4334 Fin15AnchoredAtom4335
    Fin15AnchoredAtom4336 Fin15AnchoredAtom4346 Fin15AnchoredAtom4356 Fin15AnchoredAtom4775
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

theorem fin15Anchored_clause31943 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3152 chi ∧
      ¬Fin15AnchoredAtom3154 chi ∧
      ¬Fin15AnchoredAtom3155 chi ∧
      ¬Fin15AnchoredAtom3156 chi ∧
      ¬Fin15AnchoredAtom3163 chi ∧
      ¬Fin15AnchoredAtom3164 chi ∧
      ¬Fin15AnchoredAtom3165 chi ∧
      ¬Fin15AnchoredAtom3169 chi ∧
      ¬Fin15AnchoredAtom3170 chi ∧
      ¬Fin15AnchoredAtom3171 chi ∧
      ¬Fin15AnchoredAtom3178 chi ∧
      ¬Fin15AnchoredAtom3179 chi ∧
      ¬Fin15AnchoredAtom3180 chi ∧
      ¬Fin15AnchoredAtom3184 chi ∧
      ¬Fin15AnchoredAtom3185 chi ∧
      ¬Fin15AnchoredAtom3186 chi ∧
      ¬Fin15AnchoredAtom3200 chi ∧
      ¬Fin15AnchoredAtom3201 chi ∧
      ¬Fin15AnchoredAtom3202 chi ∧
      ¬Fin15AnchoredAtom3206 chi ∧
      ¬Fin15AnchoredAtom3473 chi ∧
      ¬Fin15AnchoredAtom3474 chi ∧
      ¬Fin15AnchoredAtom3475 chi ∧
      ¬Fin15AnchoredAtom3479 chi ∧
      ¬Fin15AnchoredAtom3480 chi ∧
      ¬Fin15AnchoredAtom3481 chi ∧
      ¬Fin15AnchoredAtom3495 chi ∧
      ¬Fin15AnchoredAtom3496 chi ∧
      ¬Fin15AnchoredAtom3497 chi ∧
      ¬Fin15AnchoredAtom3501 chi ∧
      ¬Fin15AnchoredAtom3515 chi ∧
      ¬Fin15AnchoredAtom3516 chi ∧
      ¬Fin15AnchoredAtom3517 chi ∧
      ¬Fin15AnchoredAtom3521 chi ∧
      ¬Fin15AnchoredAtom3535 chi ∧
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
  refine ⟨{1, 3, 7, 8, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask30090
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3152 Fin15AnchoredAtom3154 Fin15AnchoredAtom3155
    Fin15AnchoredAtom3156 Fin15AnchoredAtom3163 Fin15AnchoredAtom3164 Fin15AnchoredAtom3165
    Fin15AnchoredAtom3169 Fin15AnchoredAtom3170 Fin15AnchoredAtom3171 Fin15AnchoredAtom3178
    Fin15AnchoredAtom3179 Fin15AnchoredAtom3180 Fin15AnchoredAtom3184 Fin15AnchoredAtom3185
    Fin15AnchoredAtom3186 Fin15AnchoredAtom3200 Fin15AnchoredAtom3201 Fin15AnchoredAtom3202
    Fin15AnchoredAtom3206 Fin15AnchoredAtom3473 Fin15AnchoredAtom3474 Fin15AnchoredAtom3475
    Fin15AnchoredAtom3479 Fin15AnchoredAtom3480 Fin15AnchoredAtom3481 Fin15AnchoredAtom3495
    Fin15AnchoredAtom3496 Fin15AnchoredAtom3497 Fin15AnchoredAtom3501 Fin15AnchoredAtom3515
    Fin15AnchoredAtom3516 Fin15AnchoredAtom3517 Fin15AnchoredAtom3521 Fin15AnchoredAtom3535
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

theorem fin15Anchored_clause31944 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3157 chi ∧
      ¬Fin15AnchoredAtom3159 chi ∧
      ¬Fin15AnchoredAtom3160 chi ∧
      ¬Fin15AnchoredAtom3161 chi ∧
      ¬Fin15AnchoredAtom3163 chi ∧
      ¬Fin15AnchoredAtom3164 chi ∧
      ¬Fin15AnchoredAtom3165 chi ∧
      ¬Fin15AnchoredAtom3169 chi ∧
      ¬Fin15AnchoredAtom3170 chi ∧
      ¬Fin15AnchoredAtom3171 chi ∧
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
  refine ⟨{1, 3, 7, 9, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask30346
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3157 Fin15AnchoredAtom3159 Fin15AnchoredAtom3160
    Fin15AnchoredAtom3161 Fin15AnchoredAtom3163 Fin15AnchoredAtom3164 Fin15AnchoredAtom3165
    Fin15AnchoredAtom3169 Fin15AnchoredAtom3170 Fin15AnchoredAtom3171 Fin15AnchoredAtom3188
    Fin15AnchoredAtom3189 Fin15AnchoredAtom3190 Fin15AnchoredAtom3194 Fin15AnchoredAtom3195
    Fin15AnchoredAtom3196 Fin15AnchoredAtom3200 Fin15AnchoredAtom3201 Fin15AnchoredAtom3202
    Fin15AnchoredAtom3206 Fin15AnchoredAtom3483 Fin15AnchoredAtom3484 Fin15AnchoredAtom3485
    Fin15AnchoredAtom3489 Fin15AnchoredAtom3490 Fin15AnchoredAtom3491 Fin15AnchoredAtom3495
    Fin15AnchoredAtom3496 Fin15AnchoredAtom3497 Fin15AnchoredAtom3501 Fin15AnchoredAtom3525
    Fin15AnchoredAtom3526 Fin15AnchoredAtom3527 Fin15AnchoredAtom3531 Fin15AnchoredAtom3535
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

theorem fin15Anchored_clause31945 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3207 chi ∧
      ¬Fin15AnchoredAtom3208 chi ∧
      ¬Fin15AnchoredAtom3210 chi ∧
      ¬Fin15AnchoredAtom3212 chi ∧
      ¬Fin15AnchoredAtom3215 chi ∧
      ¬Fin15AnchoredAtom3217 chi ∧
      ¬Fin15AnchoredAtom3219 chi ∧
      ¬Fin15AnchoredAtom3223 chi ∧
      ¬Fin15AnchoredAtom3225 chi ∧
      ¬Fin15AnchoredAtom3234 chi ∧
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
  refine ⟨{1, 4, 5, 6, 7, 8, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05618
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3207 Fin15AnchoredAtom3208 Fin15AnchoredAtom3210
    Fin15AnchoredAtom3212 Fin15AnchoredAtom3215 Fin15AnchoredAtom3217 Fin15AnchoredAtom3219
    Fin15AnchoredAtom3223 Fin15AnchoredAtom3225 Fin15AnchoredAtom3234 Fin15AnchoredAtom3243
    Fin15AnchoredAtom3245 Fin15AnchoredAtom3247 Fin15AnchoredAtom3251 Fin15AnchoredAtom3253
    Fin15AnchoredAtom3262 Fin15AnchoredAtom3272 Fin15AnchoredAtom3274 Fin15AnchoredAtom3283
    Fin15AnchoredAtom3298 Fin15AnchoredAtom3327 Fin15AnchoredAtom3329 Fin15AnchoredAtom3331
    Fin15AnchoredAtom3335 Fin15AnchoredAtom3337 Fin15AnchoredAtom3346 Fin15AnchoredAtom3356
    Fin15AnchoredAtom3358 Fin15AnchoredAtom3367 Fin15AnchoredAtom3382 Fin15AnchoredAtom3412
    Fin15AnchoredAtom3414 Fin15AnchoredAtom3423 Fin15AnchoredAtom3438 Fin15AnchoredAtom3473
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

theorem fin15Anchored_clause31946 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3207 chi ∧
      ¬Fin15AnchoredAtom3208 chi ∧
      ¬Fin15AnchoredAtom3210 chi ∧
      ¬Fin15AnchoredAtom3213 chi ∧
      ¬Fin15AnchoredAtom3215 chi ∧
      ¬Fin15AnchoredAtom3217 chi ∧
      ¬Fin15AnchoredAtom3220 chi ∧
      ¬Fin15AnchoredAtom3223 chi ∧
      ¬Fin15AnchoredAtom3226 chi ∧
      ¬Fin15AnchoredAtom3235 chi ∧
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
  refine ⟨{1, 4, 5, 6, 7, 8, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09714
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3207 Fin15AnchoredAtom3208 Fin15AnchoredAtom3210
    Fin15AnchoredAtom3213 Fin15AnchoredAtom3215 Fin15AnchoredAtom3217 Fin15AnchoredAtom3220
    Fin15AnchoredAtom3223 Fin15AnchoredAtom3226 Fin15AnchoredAtom3235 Fin15AnchoredAtom3243
    Fin15AnchoredAtom3245 Fin15AnchoredAtom3248 Fin15AnchoredAtom3251 Fin15AnchoredAtom3254
    Fin15AnchoredAtom3263 Fin15AnchoredAtom3272 Fin15AnchoredAtom3275 Fin15AnchoredAtom3284
    Fin15AnchoredAtom3299 Fin15AnchoredAtom3327 Fin15AnchoredAtom3329 Fin15AnchoredAtom3332
    Fin15AnchoredAtom3335 Fin15AnchoredAtom3338 Fin15AnchoredAtom3347 Fin15AnchoredAtom3356
    Fin15AnchoredAtom3359 Fin15AnchoredAtom3368 Fin15AnchoredAtom3383 Fin15AnchoredAtom3412
    Fin15AnchoredAtom3415 Fin15AnchoredAtom3424 Fin15AnchoredAtom3439 Fin15AnchoredAtom3474
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

theorem fin15Anchored_clause31947 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3207 chi ∧
      ¬Fin15AnchoredAtom3208 chi ∧
      ¬Fin15AnchoredAtom3210 chi ∧
      ¬Fin15AnchoredAtom3214 chi ∧
      ¬Fin15AnchoredAtom3215 chi ∧
      ¬Fin15AnchoredAtom3217 chi ∧
      ¬Fin15AnchoredAtom3221 chi ∧
      ¬Fin15AnchoredAtom3223 chi ∧
      ¬Fin15AnchoredAtom3227 chi ∧
      ¬Fin15AnchoredAtom3236 chi ∧
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
      ¬Fin15AnchoredAtom3327 chi ∧
      ¬Fin15AnchoredAtom3329 chi ∧
      ¬Fin15AnchoredAtom3333 chi ∧
      ¬Fin15AnchoredAtom3335 chi ∧
      ¬Fin15AnchoredAtom3339 chi ∧
      ¬Fin15AnchoredAtom3348 chi ∧
      ¬Fin15AnchoredAtom3356 chi ∧
      ¬Fin15AnchoredAtom3360 chi ∧
      ¬Fin15AnchoredAtom3369 chi ∧
      ¬Fin15AnchoredAtom3384 chi ∧
      ¬Fin15AnchoredAtom3412 chi ∧
      ¬Fin15AnchoredAtom3416 chi ∧
      ¬Fin15AnchoredAtom3425 chi ∧
      ¬Fin15AnchoredAtom3440 chi ∧
      ¬Fin15AnchoredAtom3475 chi ∧
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
  refine ⟨{1, 4, 5, 6, 7, 8, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17906
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3207 Fin15AnchoredAtom3208 Fin15AnchoredAtom3210
    Fin15AnchoredAtom3214 Fin15AnchoredAtom3215 Fin15AnchoredAtom3217 Fin15AnchoredAtom3221
    Fin15AnchoredAtom3223 Fin15AnchoredAtom3227 Fin15AnchoredAtom3236 Fin15AnchoredAtom3243
    Fin15AnchoredAtom3245 Fin15AnchoredAtom3249 Fin15AnchoredAtom3251 Fin15AnchoredAtom3255
    Fin15AnchoredAtom3264 Fin15AnchoredAtom3272 Fin15AnchoredAtom3276 Fin15AnchoredAtom3285
    Fin15AnchoredAtom3300 Fin15AnchoredAtom3327 Fin15AnchoredAtom3329 Fin15AnchoredAtom3333
    Fin15AnchoredAtom3335 Fin15AnchoredAtom3339 Fin15AnchoredAtom3348 Fin15AnchoredAtom3356
    Fin15AnchoredAtom3360 Fin15AnchoredAtom3369 Fin15AnchoredAtom3384 Fin15AnchoredAtom3412
    Fin15AnchoredAtom3416 Fin15AnchoredAtom3425 Fin15AnchoredAtom3440 Fin15AnchoredAtom3475
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

theorem fin15Anchored_clause31948 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3207 chi ∧
      ¬Fin15AnchoredAtom3208 chi ∧
      ¬Fin15AnchoredAtom3213 chi ∧
      ¬Fin15AnchoredAtom3214 chi ∧
      ¬Fin15AnchoredAtom3215 chi ∧
      ¬Fin15AnchoredAtom3220 chi ∧
      ¬Fin15AnchoredAtom3221 chi ∧
      ¬Fin15AnchoredAtom3226 chi ∧
      ¬Fin15AnchoredAtom3227 chi ∧
      ¬Fin15AnchoredAtom3242 chi ∧
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
      ¬Fin15AnchoredAtom3327 chi ∧
      ¬Fin15AnchoredAtom3332 chi ∧
      ¬Fin15AnchoredAtom3333 chi ∧
      ¬Fin15AnchoredAtom3338 chi ∧
      ¬Fin15AnchoredAtom3339 chi ∧
      ¬Fin15AnchoredAtom3354 chi ∧
      ¬Fin15AnchoredAtom3359 chi ∧
      ¬Fin15AnchoredAtom3360 chi ∧
      ¬Fin15AnchoredAtom3375 chi ∧
      ¬Fin15AnchoredAtom3390 chi ∧
      ¬Fin15AnchoredAtom3415 chi ∧
      ¬Fin15AnchoredAtom3416 chi ∧
      ¬Fin15AnchoredAtom3431 chi ∧
      ¬Fin15AnchoredAtom3446 chi ∧
      ¬Fin15AnchoredAtom3481 chi ∧
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
  refine ⟨{1, 4, 5, 6, 7, 8, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25074
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3207 Fin15AnchoredAtom3208 Fin15AnchoredAtom3213
    Fin15AnchoredAtom3214 Fin15AnchoredAtom3215 Fin15AnchoredAtom3220 Fin15AnchoredAtom3221
    Fin15AnchoredAtom3226 Fin15AnchoredAtom3227 Fin15AnchoredAtom3242 Fin15AnchoredAtom3243
    Fin15AnchoredAtom3248 Fin15AnchoredAtom3249 Fin15AnchoredAtom3254 Fin15AnchoredAtom3255
    Fin15AnchoredAtom3270 Fin15AnchoredAtom3275 Fin15AnchoredAtom3276 Fin15AnchoredAtom3291
    Fin15AnchoredAtom3306 Fin15AnchoredAtom3327 Fin15AnchoredAtom3332 Fin15AnchoredAtom3333
    Fin15AnchoredAtom3338 Fin15AnchoredAtom3339 Fin15AnchoredAtom3354 Fin15AnchoredAtom3359
    Fin15AnchoredAtom3360 Fin15AnchoredAtom3375 Fin15AnchoredAtom3390 Fin15AnchoredAtom3415
    Fin15AnchoredAtom3416 Fin15AnchoredAtom3431 Fin15AnchoredAtom3446 Fin15AnchoredAtom3481
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

theorem fin15Anchored_clause31949 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3207 chi ∧
      ¬Fin15AnchoredAtom3209 chi ∧
      ¬Fin15AnchoredAtom3210 chi ∧
      ¬Fin15AnchoredAtom3212 chi ∧
      ¬Fin15AnchoredAtom3216 chi ∧
      ¬Fin15AnchoredAtom3217 chi ∧
      ¬Fin15AnchoredAtom3219 chi ∧
      ¬Fin15AnchoredAtom3228 chi ∧
      ¬Fin15AnchoredAtom3230 chi ∧
      ¬Fin15AnchoredAtom3234 chi ∧
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
  refine ⟨{1, 4, 5, 6, 7, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05874
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3207 Fin15AnchoredAtom3209 Fin15AnchoredAtom3210
    Fin15AnchoredAtom3212 Fin15AnchoredAtom3216 Fin15AnchoredAtom3217 Fin15AnchoredAtom3219
    Fin15AnchoredAtom3228 Fin15AnchoredAtom3230 Fin15AnchoredAtom3234 Fin15AnchoredAtom3244
    Fin15AnchoredAtom3245 Fin15AnchoredAtom3247 Fin15AnchoredAtom3256 Fin15AnchoredAtom3258
    Fin15AnchoredAtom3262 Fin15AnchoredAtom3277 Fin15AnchoredAtom3279 Fin15AnchoredAtom3283
    Fin15AnchoredAtom3308 Fin15AnchoredAtom3328 Fin15AnchoredAtom3329 Fin15AnchoredAtom3331
    Fin15AnchoredAtom3340 Fin15AnchoredAtom3342 Fin15AnchoredAtom3346 Fin15AnchoredAtom3361
    Fin15AnchoredAtom3363 Fin15AnchoredAtom3367 Fin15AnchoredAtom3392 Fin15AnchoredAtom3417
    Fin15AnchoredAtom3419 Fin15AnchoredAtom3423 Fin15AnchoredAtom3448 Fin15AnchoredAtom3483
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

theorem fin15Anchored_clause31950 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3207 chi ∧
      ¬Fin15AnchoredAtom3209 chi ∧
      ¬Fin15AnchoredAtom3210 chi ∧
      ¬Fin15AnchoredAtom3213 chi ∧
      ¬Fin15AnchoredAtom3216 chi ∧
      ¬Fin15AnchoredAtom3217 chi ∧
      ¬Fin15AnchoredAtom3220 chi ∧
      ¬Fin15AnchoredAtom3228 chi ∧
      ¬Fin15AnchoredAtom3231 chi ∧
      ¬Fin15AnchoredAtom3235 chi ∧
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
  refine ⟨{1, 4, 5, 6, 7, 9, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09970
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3207 Fin15AnchoredAtom3209 Fin15AnchoredAtom3210
    Fin15AnchoredAtom3213 Fin15AnchoredAtom3216 Fin15AnchoredAtom3217 Fin15AnchoredAtom3220
    Fin15AnchoredAtom3228 Fin15AnchoredAtom3231 Fin15AnchoredAtom3235 Fin15AnchoredAtom3244
    Fin15AnchoredAtom3245 Fin15AnchoredAtom3248 Fin15AnchoredAtom3256 Fin15AnchoredAtom3259
    Fin15AnchoredAtom3263 Fin15AnchoredAtom3277 Fin15AnchoredAtom3280 Fin15AnchoredAtom3284
    Fin15AnchoredAtom3309 Fin15AnchoredAtom3328 Fin15AnchoredAtom3329 Fin15AnchoredAtom3332
    Fin15AnchoredAtom3340 Fin15AnchoredAtom3343 Fin15AnchoredAtom3347 Fin15AnchoredAtom3361
    Fin15AnchoredAtom3364 Fin15AnchoredAtom3368 Fin15AnchoredAtom3393 Fin15AnchoredAtom3417
    Fin15AnchoredAtom3420 Fin15AnchoredAtom3424 Fin15AnchoredAtom3449 Fin15AnchoredAtom3484
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

theorem fin15Anchored_clause31951 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3207 chi ∧
      ¬Fin15AnchoredAtom3209 chi ∧
      ¬Fin15AnchoredAtom3210 chi ∧
      ¬Fin15AnchoredAtom3214 chi ∧
      ¬Fin15AnchoredAtom3216 chi ∧
      ¬Fin15AnchoredAtom3217 chi ∧
      ¬Fin15AnchoredAtom3221 chi ∧
      ¬Fin15AnchoredAtom3228 chi ∧
      ¬Fin15AnchoredAtom3232 chi ∧
      ¬Fin15AnchoredAtom3236 chi ∧
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
  refine ⟨{1, 4, 5, 6, 7, 9, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask18162
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3207 Fin15AnchoredAtom3209 Fin15AnchoredAtom3210
    Fin15AnchoredAtom3214 Fin15AnchoredAtom3216 Fin15AnchoredAtom3217 Fin15AnchoredAtom3221
    Fin15AnchoredAtom3228 Fin15AnchoredAtom3232 Fin15AnchoredAtom3236 Fin15AnchoredAtom3244
    Fin15AnchoredAtom3245 Fin15AnchoredAtom3249 Fin15AnchoredAtom3256 Fin15AnchoredAtom3260
    Fin15AnchoredAtom3264 Fin15AnchoredAtom3277 Fin15AnchoredAtom3281 Fin15AnchoredAtom3285
    Fin15AnchoredAtom3310 Fin15AnchoredAtom3328 Fin15AnchoredAtom3329 Fin15AnchoredAtom3333
    Fin15AnchoredAtom3340 Fin15AnchoredAtom3344 Fin15AnchoredAtom3348 Fin15AnchoredAtom3361
    Fin15AnchoredAtom3365 Fin15AnchoredAtom3369 Fin15AnchoredAtom3394 Fin15AnchoredAtom3417
    Fin15AnchoredAtom3421 Fin15AnchoredAtom3425 Fin15AnchoredAtom3450 Fin15AnchoredAtom3485
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

theorem fin15Anchored_clause31952 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3207 chi ∧
      ¬Fin15AnchoredAtom3209 chi ∧
      ¬Fin15AnchoredAtom3212 chi ∧
      ¬Fin15AnchoredAtom3213 chi ∧
      ¬Fin15AnchoredAtom3216 chi ∧
      ¬Fin15AnchoredAtom3219 chi ∧
      ¬Fin15AnchoredAtom3220 chi ∧
      ¬Fin15AnchoredAtom3230 chi ∧
      ¬Fin15AnchoredAtom3231 chi ∧
      ¬Fin15AnchoredAtom3240 chi ∧
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
  refine ⟨{1, 4, 5, 6, 7, 9, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13042
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3207 Fin15AnchoredAtom3209 Fin15AnchoredAtom3212
    Fin15AnchoredAtom3213 Fin15AnchoredAtom3216 Fin15AnchoredAtom3219 Fin15AnchoredAtom3220
    Fin15AnchoredAtom3230 Fin15AnchoredAtom3231 Fin15AnchoredAtom3240 Fin15AnchoredAtom3244
    Fin15AnchoredAtom3247 Fin15AnchoredAtom3248 Fin15AnchoredAtom3258 Fin15AnchoredAtom3259
    Fin15AnchoredAtom3268 Fin15AnchoredAtom3279 Fin15AnchoredAtom3280 Fin15AnchoredAtom3289
    Fin15AnchoredAtom3314 Fin15AnchoredAtom3328 Fin15AnchoredAtom3331 Fin15AnchoredAtom3332
    Fin15AnchoredAtom3342 Fin15AnchoredAtom3343 Fin15AnchoredAtom3352 Fin15AnchoredAtom3363
    Fin15AnchoredAtom3364 Fin15AnchoredAtom3373 Fin15AnchoredAtom3398 Fin15AnchoredAtom3419
    Fin15AnchoredAtom3420 Fin15AnchoredAtom3429 Fin15AnchoredAtom3454 Fin15AnchoredAtom3489
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

theorem fin15Anchored_clause31953 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3207 chi ∧
      ¬Fin15AnchoredAtom3209 chi ∧
      ¬Fin15AnchoredAtom3212 chi ∧
      ¬Fin15AnchoredAtom3214 chi ∧
      ¬Fin15AnchoredAtom3216 chi ∧
      ¬Fin15AnchoredAtom3219 chi ∧
      ¬Fin15AnchoredAtom3221 chi ∧
      ¬Fin15AnchoredAtom3230 chi ∧
      ¬Fin15AnchoredAtom3232 chi ∧
      ¬Fin15AnchoredAtom3241 chi ∧
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
  refine ⟨{1, 4, 5, 6, 7, 9, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21234
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3207 Fin15AnchoredAtom3209 Fin15AnchoredAtom3212
    Fin15AnchoredAtom3214 Fin15AnchoredAtom3216 Fin15AnchoredAtom3219 Fin15AnchoredAtom3221
    Fin15AnchoredAtom3230 Fin15AnchoredAtom3232 Fin15AnchoredAtom3241 Fin15AnchoredAtom3244
    Fin15AnchoredAtom3247 Fin15AnchoredAtom3249 Fin15AnchoredAtom3258 Fin15AnchoredAtom3260
    Fin15AnchoredAtom3269 Fin15AnchoredAtom3279 Fin15AnchoredAtom3281 Fin15AnchoredAtom3290
    Fin15AnchoredAtom3315 Fin15AnchoredAtom3328 Fin15AnchoredAtom3331 Fin15AnchoredAtom3333
    Fin15AnchoredAtom3342 Fin15AnchoredAtom3344 Fin15AnchoredAtom3353 Fin15AnchoredAtom3363
    Fin15AnchoredAtom3365 Fin15AnchoredAtom3374 Fin15AnchoredAtom3399 Fin15AnchoredAtom3419
    Fin15AnchoredAtom3421 Fin15AnchoredAtom3430 Fin15AnchoredAtom3455 Fin15AnchoredAtom3490
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

theorem fin15Anchored_clause31954 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3207 chi ∧
      ¬Fin15AnchoredAtom3209 chi ∧
      ¬Fin15AnchoredAtom3213 chi ∧
      ¬Fin15AnchoredAtom3214 chi ∧
      ¬Fin15AnchoredAtom3216 chi ∧
      ¬Fin15AnchoredAtom3220 chi ∧
      ¬Fin15AnchoredAtom3221 chi ∧
      ¬Fin15AnchoredAtom3231 chi ∧
      ¬Fin15AnchoredAtom3232 chi ∧
      ¬Fin15AnchoredAtom3242 chi ∧
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
  refine ⟨{1, 4, 5, 6, 7, 9, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25330
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3207 Fin15AnchoredAtom3209 Fin15AnchoredAtom3213
    Fin15AnchoredAtom3214 Fin15AnchoredAtom3216 Fin15AnchoredAtom3220 Fin15AnchoredAtom3221
    Fin15AnchoredAtom3231 Fin15AnchoredAtom3232 Fin15AnchoredAtom3242 Fin15AnchoredAtom3244
    Fin15AnchoredAtom3248 Fin15AnchoredAtom3249 Fin15AnchoredAtom3259 Fin15AnchoredAtom3260
    Fin15AnchoredAtom3270 Fin15AnchoredAtom3280 Fin15AnchoredAtom3281 Fin15AnchoredAtom3291
    Fin15AnchoredAtom3316 Fin15AnchoredAtom3328 Fin15AnchoredAtom3332 Fin15AnchoredAtom3333
    Fin15AnchoredAtom3343 Fin15AnchoredAtom3344 Fin15AnchoredAtom3354 Fin15AnchoredAtom3364
    Fin15AnchoredAtom3365 Fin15AnchoredAtom3375 Fin15AnchoredAtom3400 Fin15AnchoredAtom3420
    Fin15AnchoredAtom3421 Fin15AnchoredAtom3431 Fin15AnchoredAtom3456 Fin15AnchoredAtom3491
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

theorem fin15Anchored_clause31955 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3207 chi ∧
      ¬Fin15AnchoredAtom3210 chi ∧
      ¬Fin15AnchoredAtom3212 chi ∧
      ¬Fin15AnchoredAtom3213 chi ∧
      ¬Fin15AnchoredAtom3217 chi ∧
      ¬Fin15AnchoredAtom3219 chi ∧
      ¬Fin15AnchoredAtom3220 chi ∧
      ¬Fin15AnchoredAtom3234 chi ∧
      ¬Fin15AnchoredAtom3235 chi ∧
      ¬Fin15AnchoredAtom3240 chi ∧
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
  refine ⟨{1, 4, 5, 6, 7, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13554
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3207 Fin15AnchoredAtom3210 Fin15AnchoredAtom3212
    Fin15AnchoredAtom3213 Fin15AnchoredAtom3217 Fin15AnchoredAtom3219 Fin15AnchoredAtom3220
    Fin15AnchoredAtom3234 Fin15AnchoredAtom3235 Fin15AnchoredAtom3240 Fin15AnchoredAtom3245
    Fin15AnchoredAtom3247 Fin15AnchoredAtom3248 Fin15AnchoredAtom3262 Fin15AnchoredAtom3263
    Fin15AnchoredAtom3268 Fin15AnchoredAtom3283 Fin15AnchoredAtom3284 Fin15AnchoredAtom3289
    Fin15AnchoredAtom3320 Fin15AnchoredAtom3329 Fin15AnchoredAtom3331 Fin15AnchoredAtom3332
    Fin15AnchoredAtom3346 Fin15AnchoredAtom3347 Fin15AnchoredAtom3352 Fin15AnchoredAtom3367
    Fin15AnchoredAtom3368 Fin15AnchoredAtom3373 Fin15AnchoredAtom3404 Fin15AnchoredAtom3423
    Fin15AnchoredAtom3424 Fin15AnchoredAtom3429 Fin15AnchoredAtom3460 Fin15AnchoredAtom3495
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

theorem fin15Anchored_clause31956 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3207 chi ∧
      ¬Fin15AnchoredAtom3210 chi ∧
      ¬Fin15AnchoredAtom3212 chi ∧
      ¬Fin15AnchoredAtom3214 chi ∧
      ¬Fin15AnchoredAtom3217 chi ∧
      ¬Fin15AnchoredAtom3219 chi ∧
      ¬Fin15AnchoredAtom3221 chi ∧
      ¬Fin15AnchoredAtom3234 chi ∧
      ¬Fin15AnchoredAtom3236 chi ∧
      ¬Fin15AnchoredAtom3241 chi ∧
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
  refine ⟨{1, 4, 5, 6, 7, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21746
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3207 Fin15AnchoredAtom3210 Fin15AnchoredAtom3212
    Fin15AnchoredAtom3214 Fin15AnchoredAtom3217 Fin15AnchoredAtom3219 Fin15AnchoredAtom3221
    Fin15AnchoredAtom3234 Fin15AnchoredAtom3236 Fin15AnchoredAtom3241 Fin15AnchoredAtom3245
    Fin15AnchoredAtom3247 Fin15AnchoredAtom3249 Fin15AnchoredAtom3262 Fin15AnchoredAtom3264
    Fin15AnchoredAtom3269 Fin15AnchoredAtom3283 Fin15AnchoredAtom3285 Fin15AnchoredAtom3290
    Fin15AnchoredAtom3321 Fin15AnchoredAtom3329 Fin15AnchoredAtom3331 Fin15AnchoredAtom3333
    Fin15AnchoredAtom3346 Fin15AnchoredAtom3348 Fin15AnchoredAtom3353 Fin15AnchoredAtom3367
    Fin15AnchoredAtom3369 Fin15AnchoredAtom3374 Fin15AnchoredAtom3405 Fin15AnchoredAtom3423
    Fin15AnchoredAtom3425 Fin15AnchoredAtom3430 Fin15AnchoredAtom3461 Fin15AnchoredAtom3496
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

theorem fin15Anchored_clause31957 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3207 chi ∧
      ¬Fin15AnchoredAtom3210 chi ∧
      ¬Fin15AnchoredAtom3213 chi ∧
      ¬Fin15AnchoredAtom3214 chi ∧
      ¬Fin15AnchoredAtom3217 chi ∧
      ¬Fin15AnchoredAtom3220 chi ∧
      ¬Fin15AnchoredAtom3221 chi ∧
      ¬Fin15AnchoredAtom3235 chi ∧
      ¬Fin15AnchoredAtom3236 chi ∧
      ¬Fin15AnchoredAtom3242 chi ∧
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
  refine ⟨{1, 4, 5, 6, 7, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25842
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3207 Fin15AnchoredAtom3210 Fin15AnchoredAtom3213
    Fin15AnchoredAtom3214 Fin15AnchoredAtom3217 Fin15AnchoredAtom3220 Fin15AnchoredAtom3221
    Fin15AnchoredAtom3235 Fin15AnchoredAtom3236 Fin15AnchoredAtom3242 Fin15AnchoredAtom3245
    Fin15AnchoredAtom3248 Fin15AnchoredAtom3249 Fin15AnchoredAtom3263 Fin15AnchoredAtom3264
    Fin15AnchoredAtom3270 Fin15AnchoredAtom3284 Fin15AnchoredAtom3285 Fin15AnchoredAtom3291
    Fin15AnchoredAtom3322 Fin15AnchoredAtom3329 Fin15AnchoredAtom3332 Fin15AnchoredAtom3333
    Fin15AnchoredAtom3347 Fin15AnchoredAtom3348 Fin15AnchoredAtom3354 Fin15AnchoredAtom3368
    Fin15AnchoredAtom3369 Fin15AnchoredAtom3375 Fin15AnchoredAtom3406 Fin15AnchoredAtom3424
    Fin15AnchoredAtom3425 Fin15AnchoredAtom3431 Fin15AnchoredAtom3462 Fin15AnchoredAtom3497
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

theorem fin15Anchored_clause31958 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3207 chi ∧
      ¬Fin15AnchoredAtom3212 chi ∧
      ¬Fin15AnchoredAtom3213 chi ∧
      ¬Fin15AnchoredAtom3214 chi ∧
      ¬Fin15AnchoredAtom3219 chi ∧
      ¬Fin15AnchoredAtom3220 chi ∧
      ¬Fin15AnchoredAtom3221 chi ∧
      ¬Fin15AnchoredAtom3240 chi ∧
      ¬Fin15AnchoredAtom3241 chi ∧
      ¬Fin15AnchoredAtom3242 chi ∧
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
  refine ⟨{1, 4, 5, 6, 7, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask28914
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3207 Fin15AnchoredAtom3212 Fin15AnchoredAtom3213
    Fin15AnchoredAtom3214 Fin15AnchoredAtom3219 Fin15AnchoredAtom3220 Fin15AnchoredAtom3221
    Fin15AnchoredAtom3240 Fin15AnchoredAtom3241 Fin15AnchoredAtom3242 Fin15AnchoredAtom3247
    Fin15AnchoredAtom3248 Fin15AnchoredAtom3249 Fin15AnchoredAtom3268 Fin15AnchoredAtom3269
    Fin15AnchoredAtom3270 Fin15AnchoredAtom3289 Fin15AnchoredAtom3290 Fin15AnchoredAtom3291
    Fin15AnchoredAtom3326 Fin15AnchoredAtom3331 Fin15AnchoredAtom3332 Fin15AnchoredAtom3333
    Fin15AnchoredAtom3352 Fin15AnchoredAtom3353 Fin15AnchoredAtom3354 Fin15AnchoredAtom3373
    Fin15AnchoredAtom3374 Fin15AnchoredAtom3375 Fin15AnchoredAtom3410 Fin15AnchoredAtom3429
    Fin15AnchoredAtom3430 Fin15AnchoredAtom3431 Fin15AnchoredAtom3466 Fin15AnchoredAtom3501
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

theorem fin15Anchored_clause31959 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3209 chi ∧
      ¬Fin15AnchoredAtom3210 chi ∧
      ¬Fin15AnchoredAtom3212 chi ∧
      ¬Fin15AnchoredAtom3213 chi ∧
      ¬Fin15AnchoredAtom3228 chi ∧
      ¬Fin15AnchoredAtom3230 chi ∧
      ¬Fin15AnchoredAtom3231 chi ∧
      ¬Fin15AnchoredAtom3234 chi ∧
      ¬Fin15AnchoredAtom3235 chi ∧
      ¬Fin15AnchoredAtom3240 chi ∧
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
  refine ⟨{1, 4, 5, 6, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13938
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3209 Fin15AnchoredAtom3210 Fin15AnchoredAtom3212
    Fin15AnchoredAtom3213 Fin15AnchoredAtom3228 Fin15AnchoredAtom3230 Fin15AnchoredAtom3231
    Fin15AnchoredAtom3234 Fin15AnchoredAtom3235 Fin15AnchoredAtom3240 Fin15AnchoredAtom3256
    Fin15AnchoredAtom3258 Fin15AnchoredAtom3259 Fin15AnchoredAtom3262 Fin15AnchoredAtom3263
    Fin15AnchoredAtom3268 Fin15AnchoredAtom3308 Fin15AnchoredAtom3309 Fin15AnchoredAtom3314
    Fin15AnchoredAtom3320 Fin15AnchoredAtom3340 Fin15AnchoredAtom3342 Fin15AnchoredAtom3343
    Fin15AnchoredAtom3346 Fin15AnchoredAtom3347 Fin15AnchoredAtom3352 Fin15AnchoredAtom3392
    Fin15AnchoredAtom3393 Fin15AnchoredAtom3398 Fin15AnchoredAtom3404 Fin15AnchoredAtom3448
    Fin15AnchoredAtom3449 Fin15AnchoredAtom3454 Fin15AnchoredAtom3460 Fin15AnchoredAtom3525
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

theorem fin15Anchored_clause31960 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3209 chi ∧
      ¬Fin15AnchoredAtom3210 chi ∧
      ¬Fin15AnchoredAtom3212 chi ∧
      ¬Fin15AnchoredAtom3214 chi ∧
      ¬Fin15AnchoredAtom3228 chi ∧
      ¬Fin15AnchoredAtom3230 chi ∧
      ¬Fin15AnchoredAtom3232 chi ∧
      ¬Fin15AnchoredAtom3234 chi ∧
      ¬Fin15AnchoredAtom3236 chi ∧
      ¬Fin15AnchoredAtom3241 chi ∧
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
  refine ⟨{1, 4, 5, 6, 9, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22130
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3209 Fin15AnchoredAtom3210 Fin15AnchoredAtom3212
    Fin15AnchoredAtom3214 Fin15AnchoredAtom3228 Fin15AnchoredAtom3230 Fin15AnchoredAtom3232
    Fin15AnchoredAtom3234 Fin15AnchoredAtom3236 Fin15AnchoredAtom3241 Fin15AnchoredAtom3256
    Fin15AnchoredAtom3258 Fin15AnchoredAtom3260 Fin15AnchoredAtom3262 Fin15AnchoredAtom3264
    Fin15AnchoredAtom3269 Fin15AnchoredAtom3308 Fin15AnchoredAtom3310 Fin15AnchoredAtom3315
    Fin15AnchoredAtom3321 Fin15AnchoredAtom3340 Fin15AnchoredAtom3342 Fin15AnchoredAtom3344
    Fin15AnchoredAtom3346 Fin15AnchoredAtom3348 Fin15AnchoredAtom3353 Fin15AnchoredAtom3392
    Fin15AnchoredAtom3394 Fin15AnchoredAtom3399 Fin15AnchoredAtom3405 Fin15AnchoredAtom3448
    Fin15AnchoredAtom3450 Fin15AnchoredAtom3455 Fin15AnchoredAtom3461 Fin15AnchoredAtom3526
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

theorem fin15Anchored_clause31961 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3209 chi ∧
      ¬Fin15AnchoredAtom3210 chi ∧
      ¬Fin15AnchoredAtom3213 chi ∧
      ¬Fin15AnchoredAtom3214 chi ∧
      ¬Fin15AnchoredAtom3228 chi ∧
      ¬Fin15AnchoredAtom3231 chi ∧
      ¬Fin15AnchoredAtom3232 chi ∧
      ¬Fin15AnchoredAtom3235 chi ∧
      ¬Fin15AnchoredAtom3236 chi ∧
      ¬Fin15AnchoredAtom3242 chi ∧
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
  refine ⟨{1, 4, 5, 6, 9, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26226
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3209 Fin15AnchoredAtom3210 Fin15AnchoredAtom3213
    Fin15AnchoredAtom3214 Fin15AnchoredAtom3228 Fin15AnchoredAtom3231 Fin15AnchoredAtom3232
    Fin15AnchoredAtom3235 Fin15AnchoredAtom3236 Fin15AnchoredAtom3242 Fin15AnchoredAtom3256
    Fin15AnchoredAtom3259 Fin15AnchoredAtom3260 Fin15AnchoredAtom3263 Fin15AnchoredAtom3264
    Fin15AnchoredAtom3270 Fin15AnchoredAtom3309 Fin15AnchoredAtom3310 Fin15AnchoredAtom3316
    Fin15AnchoredAtom3322 Fin15AnchoredAtom3340 Fin15AnchoredAtom3343 Fin15AnchoredAtom3344
    Fin15AnchoredAtom3347 Fin15AnchoredAtom3348 Fin15AnchoredAtom3354 Fin15AnchoredAtom3393
    Fin15AnchoredAtom3394 Fin15AnchoredAtom3400 Fin15AnchoredAtom3406 Fin15AnchoredAtom3449
    Fin15AnchoredAtom3450 Fin15AnchoredAtom3456 Fin15AnchoredAtom3462 Fin15AnchoredAtom3527
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

theorem fin15Anchored_clause31962 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3209 chi ∧
      ¬Fin15AnchoredAtom3212 chi ∧
      ¬Fin15AnchoredAtom3213 chi ∧
      ¬Fin15AnchoredAtom3214 chi ∧
      ¬Fin15AnchoredAtom3230 chi ∧
      ¬Fin15AnchoredAtom3231 chi ∧
      ¬Fin15AnchoredAtom3232 chi ∧
      ¬Fin15AnchoredAtom3240 chi ∧
      ¬Fin15AnchoredAtom3241 chi ∧
      ¬Fin15AnchoredAtom3242 chi ∧
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
  refine ⟨{1, 4, 5, 6, 9, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29298
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3209 Fin15AnchoredAtom3212 Fin15AnchoredAtom3213
    Fin15AnchoredAtom3214 Fin15AnchoredAtom3230 Fin15AnchoredAtom3231 Fin15AnchoredAtom3232
    Fin15AnchoredAtom3240 Fin15AnchoredAtom3241 Fin15AnchoredAtom3242 Fin15AnchoredAtom3258
    Fin15AnchoredAtom3259 Fin15AnchoredAtom3260 Fin15AnchoredAtom3268 Fin15AnchoredAtom3269
    Fin15AnchoredAtom3270 Fin15AnchoredAtom3314 Fin15AnchoredAtom3315 Fin15AnchoredAtom3316
    Fin15AnchoredAtom3326 Fin15AnchoredAtom3342 Fin15AnchoredAtom3343 Fin15AnchoredAtom3344
    Fin15AnchoredAtom3352 Fin15AnchoredAtom3353 Fin15AnchoredAtom3354 Fin15AnchoredAtom3398
    Fin15AnchoredAtom3399 Fin15AnchoredAtom3400 Fin15AnchoredAtom3410 Fin15AnchoredAtom3454
    Fin15AnchoredAtom3455 Fin15AnchoredAtom3456 Fin15AnchoredAtom3466 Fin15AnchoredAtom3531
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

theorem fin15Anchored_clause31963 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3210 chi ∧
      ¬Fin15AnchoredAtom3212 chi ∧
      ¬Fin15AnchoredAtom3213 chi ∧
      ¬Fin15AnchoredAtom3214 chi ∧
      ¬Fin15AnchoredAtom3234 chi ∧
      ¬Fin15AnchoredAtom3235 chi ∧
      ¬Fin15AnchoredAtom3236 chi ∧
      ¬Fin15AnchoredAtom3240 chi ∧
      ¬Fin15AnchoredAtom3241 chi ∧
      ¬Fin15AnchoredAtom3242 chi ∧
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
  refine ⟨{1, 4, 5, 6, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29810
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3210 Fin15AnchoredAtom3212 Fin15AnchoredAtom3213
    Fin15AnchoredAtom3214 Fin15AnchoredAtom3234 Fin15AnchoredAtom3235 Fin15AnchoredAtom3236
    Fin15AnchoredAtom3240 Fin15AnchoredAtom3241 Fin15AnchoredAtom3242 Fin15AnchoredAtom3262
    Fin15AnchoredAtom3263 Fin15AnchoredAtom3264 Fin15AnchoredAtom3268 Fin15AnchoredAtom3269
    Fin15AnchoredAtom3270 Fin15AnchoredAtom3320 Fin15AnchoredAtom3321 Fin15AnchoredAtom3322
    Fin15AnchoredAtom3326 Fin15AnchoredAtom3346 Fin15AnchoredAtom3347 Fin15AnchoredAtom3348
    Fin15AnchoredAtom3352 Fin15AnchoredAtom3353 Fin15AnchoredAtom3354 Fin15AnchoredAtom3404
    Fin15AnchoredAtom3405 Fin15AnchoredAtom3406 Fin15AnchoredAtom3410 Fin15AnchoredAtom3460
    Fin15AnchoredAtom3461 Fin15AnchoredAtom3462 Fin15AnchoredAtom3466 Fin15AnchoredAtom3535
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

theorem fin15Anchored_clause31964 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3216 chi ∧
      ¬Fin15AnchoredAtom3217 chi ∧
      ¬Fin15AnchoredAtom3219 chi ∧
      ¬Fin15AnchoredAtom3220 chi ∧
      ¬Fin15AnchoredAtom3228 chi ∧
      ¬Fin15AnchoredAtom3230 chi ∧
      ¬Fin15AnchoredAtom3231 chi ∧
      ¬Fin15AnchoredAtom3234 chi ∧
      ¬Fin15AnchoredAtom3235 chi ∧
      ¬Fin15AnchoredAtom3240 chi ∧
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
  refine ⟨{1, 4, 5, 7, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask14002
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3216 Fin15AnchoredAtom3217 Fin15AnchoredAtom3219
    Fin15AnchoredAtom3220 Fin15AnchoredAtom3228 Fin15AnchoredAtom3230 Fin15AnchoredAtom3231
    Fin15AnchoredAtom3234 Fin15AnchoredAtom3235 Fin15AnchoredAtom3240 Fin15AnchoredAtom3277
    Fin15AnchoredAtom3279 Fin15AnchoredAtom3280 Fin15AnchoredAtom3283 Fin15AnchoredAtom3284
    Fin15AnchoredAtom3289 Fin15AnchoredAtom3308 Fin15AnchoredAtom3309 Fin15AnchoredAtom3314
    Fin15AnchoredAtom3320 Fin15AnchoredAtom3361 Fin15AnchoredAtom3363 Fin15AnchoredAtom3364
    Fin15AnchoredAtom3367 Fin15AnchoredAtom3368 Fin15AnchoredAtom3373 Fin15AnchoredAtom3392
    Fin15AnchoredAtom3393 Fin15AnchoredAtom3398 Fin15AnchoredAtom3404 Fin15AnchoredAtom3483
    Fin15AnchoredAtom3484 Fin15AnchoredAtom3489 Fin15AnchoredAtom3495 Fin15AnchoredAtom3525
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

theorem fin15Anchored_clause31965 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3216 chi ∧
      ¬Fin15AnchoredAtom3217 chi ∧
      ¬Fin15AnchoredAtom3219 chi ∧
      ¬Fin15AnchoredAtom3221 chi ∧
      ¬Fin15AnchoredAtom3228 chi ∧
      ¬Fin15AnchoredAtom3230 chi ∧
      ¬Fin15AnchoredAtom3232 chi ∧
      ¬Fin15AnchoredAtom3234 chi ∧
      ¬Fin15AnchoredAtom3236 chi ∧
      ¬Fin15AnchoredAtom3241 chi ∧
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
  refine ⟨{1, 4, 5, 7, 9, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22194
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3216 Fin15AnchoredAtom3217 Fin15AnchoredAtom3219
    Fin15AnchoredAtom3221 Fin15AnchoredAtom3228 Fin15AnchoredAtom3230 Fin15AnchoredAtom3232
    Fin15AnchoredAtom3234 Fin15AnchoredAtom3236 Fin15AnchoredAtom3241 Fin15AnchoredAtom3277
    Fin15AnchoredAtom3279 Fin15AnchoredAtom3281 Fin15AnchoredAtom3283 Fin15AnchoredAtom3285
    Fin15AnchoredAtom3290 Fin15AnchoredAtom3308 Fin15AnchoredAtom3310 Fin15AnchoredAtom3315
    Fin15AnchoredAtom3321 Fin15AnchoredAtom3361 Fin15AnchoredAtom3363 Fin15AnchoredAtom3365
    Fin15AnchoredAtom3367 Fin15AnchoredAtom3369 Fin15AnchoredAtom3374 Fin15AnchoredAtom3392
    Fin15AnchoredAtom3394 Fin15AnchoredAtom3399 Fin15AnchoredAtom3405 Fin15AnchoredAtom3483
    Fin15AnchoredAtom3485 Fin15AnchoredAtom3490 Fin15AnchoredAtom3496 Fin15AnchoredAtom3526
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

theorem fin15Anchored_clause31966 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3216 chi ∧
      ¬Fin15AnchoredAtom3217 chi ∧
      ¬Fin15AnchoredAtom3220 chi ∧
      ¬Fin15AnchoredAtom3221 chi ∧
      ¬Fin15AnchoredAtom3228 chi ∧
      ¬Fin15AnchoredAtom3231 chi ∧
      ¬Fin15AnchoredAtom3232 chi ∧
      ¬Fin15AnchoredAtom3235 chi ∧
      ¬Fin15AnchoredAtom3236 chi ∧
      ¬Fin15AnchoredAtom3242 chi ∧
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
  refine ⟨{1, 4, 5, 7, 9, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26290
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3216 Fin15AnchoredAtom3217 Fin15AnchoredAtom3220
    Fin15AnchoredAtom3221 Fin15AnchoredAtom3228 Fin15AnchoredAtom3231 Fin15AnchoredAtom3232
    Fin15AnchoredAtom3235 Fin15AnchoredAtom3236 Fin15AnchoredAtom3242 Fin15AnchoredAtom3277
    Fin15AnchoredAtom3280 Fin15AnchoredAtom3281 Fin15AnchoredAtom3284 Fin15AnchoredAtom3285
    Fin15AnchoredAtom3291 Fin15AnchoredAtom3309 Fin15AnchoredAtom3310 Fin15AnchoredAtom3316
    Fin15AnchoredAtom3322 Fin15AnchoredAtom3361 Fin15AnchoredAtom3364 Fin15AnchoredAtom3365
    Fin15AnchoredAtom3368 Fin15AnchoredAtom3369 Fin15AnchoredAtom3375 Fin15AnchoredAtom3393
    Fin15AnchoredAtom3394 Fin15AnchoredAtom3400 Fin15AnchoredAtom3406 Fin15AnchoredAtom3484
    Fin15AnchoredAtom3485 Fin15AnchoredAtom3491 Fin15AnchoredAtom3497 Fin15AnchoredAtom3527
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

theorem fin15Anchored_clause31967 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3216 chi ∧
      ¬Fin15AnchoredAtom3218 chi ∧
      ¬Fin15AnchoredAtom3219 chi ∧
      ¬Fin15AnchoredAtom3220 chi ∧
      ¬Fin15AnchoredAtom3229 chi ∧
      ¬Fin15AnchoredAtom3230 chi ∧
      ¬Fin15AnchoredAtom3231 chi ∧
      ¬Fin15AnchoredAtom3237 chi ∧
      ¬Fin15AnchoredAtom3238 chi ∧
      ¬Fin15AnchoredAtom3240 chi ∧
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
      ¬Fin15AnchoredAtom3362 chi ∧
      ¬Fin15AnchoredAtom3363 chi ∧
      ¬Fin15AnchoredAtom3364 chi ∧
      ¬Fin15AnchoredAtom3370 chi ∧
      ¬Fin15AnchoredAtom3371 chi ∧
      ¬Fin15AnchoredAtom3373 chi ∧
      ¬Fin15AnchoredAtom3395 chi ∧
      ¬Fin15AnchoredAtom3396 chi ∧
      ¬Fin15AnchoredAtom3398 chi ∧
      ¬Fin15AnchoredAtom3407 chi ∧
      ¬Fin15AnchoredAtom3486 chi ∧
      ¬Fin15AnchoredAtom3487 chi ∧
      ¬Fin15AnchoredAtom3489 chi ∧
      ¬Fin15AnchoredAtom3498 chi ∧
      ¬Fin15AnchoredAtom3528 chi ∧
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
  refine ⟨{1, 4, 5, 7, 9, 11, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask15026
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3216 Fin15AnchoredAtom3218 Fin15AnchoredAtom3219
    Fin15AnchoredAtom3220 Fin15AnchoredAtom3229 Fin15AnchoredAtom3230 Fin15AnchoredAtom3231
    Fin15AnchoredAtom3237 Fin15AnchoredAtom3238 Fin15AnchoredAtom3240 Fin15AnchoredAtom3278
    Fin15AnchoredAtom3279 Fin15AnchoredAtom3280 Fin15AnchoredAtom3286 Fin15AnchoredAtom3287
    Fin15AnchoredAtom3289 Fin15AnchoredAtom3311 Fin15AnchoredAtom3312 Fin15AnchoredAtom3314
    Fin15AnchoredAtom3323 Fin15AnchoredAtom3362 Fin15AnchoredAtom3363 Fin15AnchoredAtom3364
    Fin15AnchoredAtom3370 Fin15AnchoredAtom3371 Fin15AnchoredAtom3373 Fin15AnchoredAtom3395
    Fin15AnchoredAtom3396 Fin15AnchoredAtom3398 Fin15AnchoredAtom3407 Fin15AnchoredAtom3486
    Fin15AnchoredAtom3487 Fin15AnchoredAtom3489 Fin15AnchoredAtom3498 Fin15AnchoredAtom3528
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

theorem fin15Anchored_clause31968 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3216 chi ∧
      ¬Fin15AnchoredAtom3219 chi ∧
      ¬Fin15AnchoredAtom3220 chi ∧
      ¬Fin15AnchoredAtom3221 chi ∧
      ¬Fin15AnchoredAtom3230 chi ∧
      ¬Fin15AnchoredAtom3231 chi ∧
      ¬Fin15AnchoredAtom3232 chi ∧
      ¬Fin15AnchoredAtom3240 chi ∧
      ¬Fin15AnchoredAtom3241 chi ∧
      ¬Fin15AnchoredAtom3242 chi ∧
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
  refine ⟨{1, 4, 5, 7, 9, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29362
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3216 Fin15AnchoredAtom3219 Fin15AnchoredAtom3220
    Fin15AnchoredAtom3221 Fin15AnchoredAtom3230 Fin15AnchoredAtom3231 Fin15AnchoredAtom3232
    Fin15AnchoredAtom3240 Fin15AnchoredAtom3241 Fin15AnchoredAtom3242 Fin15AnchoredAtom3279
    Fin15AnchoredAtom3280 Fin15AnchoredAtom3281 Fin15AnchoredAtom3289 Fin15AnchoredAtom3290
    Fin15AnchoredAtom3291 Fin15AnchoredAtom3314 Fin15AnchoredAtom3315 Fin15AnchoredAtom3316
    Fin15AnchoredAtom3326 Fin15AnchoredAtom3363 Fin15AnchoredAtom3364 Fin15AnchoredAtom3365
    Fin15AnchoredAtom3373 Fin15AnchoredAtom3374 Fin15AnchoredAtom3375 Fin15AnchoredAtom3398
    Fin15AnchoredAtom3399 Fin15AnchoredAtom3400 Fin15AnchoredAtom3410 Fin15AnchoredAtom3489
    Fin15AnchoredAtom3490 Fin15AnchoredAtom3491 Fin15AnchoredAtom3501 Fin15AnchoredAtom3531
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

theorem fin15Anchored_clause31969 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3217 chi ∧
      ¬Fin15AnchoredAtom3219 chi ∧
      ¬Fin15AnchoredAtom3220 chi ∧
      ¬Fin15AnchoredAtom3221 chi ∧
      ¬Fin15AnchoredAtom3234 chi ∧
      ¬Fin15AnchoredAtom3235 chi ∧
      ¬Fin15AnchoredAtom3236 chi ∧
      ¬Fin15AnchoredAtom3240 chi ∧
      ¬Fin15AnchoredAtom3241 chi ∧
      ¬Fin15AnchoredAtom3242 chi ∧
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
  refine ⟨{1, 4, 5, 7, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29874
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3217 Fin15AnchoredAtom3219 Fin15AnchoredAtom3220
    Fin15AnchoredAtom3221 Fin15AnchoredAtom3234 Fin15AnchoredAtom3235 Fin15AnchoredAtom3236
    Fin15AnchoredAtom3240 Fin15AnchoredAtom3241 Fin15AnchoredAtom3242 Fin15AnchoredAtom3283
    Fin15AnchoredAtom3284 Fin15AnchoredAtom3285 Fin15AnchoredAtom3289 Fin15AnchoredAtom3290
    Fin15AnchoredAtom3291 Fin15AnchoredAtom3320 Fin15AnchoredAtom3321 Fin15AnchoredAtom3322
    Fin15AnchoredAtom3326 Fin15AnchoredAtom3367 Fin15AnchoredAtom3368 Fin15AnchoredAtom3369
    Fin15AnchoredAtom3373 Fin15AnchoredAtom3374 Fin15AnchoredAtom3375 Fin15AnchoredAtom3404
    Fin15AnchoredAtom3405 Fin15AnchoredAtom3406 Fin15AnchoredAtom3410 Fin15AnchoredAtom3495
    Fin15AnchoredAtom3496 Fin15AnchoredAtom3497 Fin15AnchoredAtom3501 Fin15AnchoredAtom3535
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

theorem fin15Anchored_clause31970 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3228 chi ∧
      ¬Fin15AnchoredAtom3230 chi ∧
      ¬Fin15AnchoredAtom3231 chi ∧
      ¬Fin15AnchoredAtom3232 chi ∧
      ¬Fin15AnchoredAtom3234 chi ∧
      ¬Fin15AnchoredAtom3235 chi ∧
      ¬Fin15AnchoredAtom3236 chi ∧
      ¬Fin15AnchoredAtom3240 chi ∧
      ¬Fin15AnchoredAtom3241 chi ∧
      ¬Fin15AnchoredAtom3242 chi ∧
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
  refine ⟨{1, 4, 5, 9, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask30258
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3228 Fin15AnchoredAtom3230 Fin15AnchoredAtom3231
    Fin15AnchoredAtom3232 Fin15AnchoredAtom3234 Fin15AnchoredAtom3235 Fin15AnchoredAtom3236
    Fin15AnchoredAtom3240 Fin15AnchoredAtom3241 Fin15AnchoredAtom3242 Fin15AnchoredAtom3308
    Fin15AnchoredAtom3309 Fin15AnchoredAtom3310 Fin15AnchoredAtom3314 Fin15AnchoredAtom3315
    Fin15AnchoredAtom3316 Fin15AnchoredAtom3320 Fin15AnchoredAtom3321 Fin15AnchoredAtom3322
    Fin15AnchoredAtom3326 Fin15AnchoredAtom3392 Fin15AnchoredAtom3393 Fin15AnchoredAtom3394
    Fin15AnchoredAtom3398 Fin15AnchoredAtom3399 Fin15AnchoredAtom3400 Fin15AnchoredAtom3404
    Fin15AnchoredAtom3405 Fin15AnchoredAtom3406 Fin15AnchoredAtom3410 Fin15AnchoredAtom3525
    Fin15AnchoredAtom3526 Fin15AnchoredAtom3527 Fin15AnchoredAtom3531 Fin15AnchoredAtom3535
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

theorem fin15Anchored_clause31971 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3243 chi ∧
      ¬Fin15AnchoredAtom3244 chi ∧
      ¬Fin15AnchoredAtom3248 chi ∧
      ¬Fin15AnchoredAtom3249 chi ∧
      ¬Fin15AnchoredAtom3250 chi ∧
      ¬Fin15AnchoredAtom3254 chi ∧
      ¬Fin15AnchoredAtom3255 chi ∧
      ¬Fin15AnchoredAtom3259 chi ∧
      ¬Fin15AnchoredAtom3260 chi ∧
      ¬Fin15AnchoredAtom3270 chi ∧
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
  refine ⟨{1, 4, 6, 7, 8, 9, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25554
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3243 Fin15AnchoredAtom3244 Fin15AnchoredAtom3248
    Fin15AnchoredAtom3249 Fin15AnchoredAtom3250 Fin15AnchoredAtom3254 Fin15AnchoredAtom3255
    Fin15AnchoredAtom3259 Fin15AnchoredAtom3260 Fin15AnchoredAtom3270 Fin15AnchoredAtom3271
    Fin15AnchoredAtom3275 Fin15AnchoredAtom3276 Fin15AnchoredAtom3280 Fin15AnchoredAtom3281
    Fin15AnchoredAtom3291 Fin15AnchoredAtom3295 Fin15AnchoredAtom3296 Fin15AnchoredAtom3306
    Fin15AnchoredAtom3316 Fin15AnchoredAtom3411 Fin15AnchoredAtom3415 Fin15AnchoredAtom3416
    Fin15AnchoredAtom3420 Fin15AnchoredAtom3421 Fin15AnchoredAtom3431 Fin15AnchoredAtom3435
    Fin15AnchoredAtom3436 Fin15AnchoredAtom3446 Fin15AnchoredAtom3456 Fin15AnchoredAtom3470
    Fin15AnchoredAtom3471 Fin15AnchoredAtom3481 Fin15AnchoredAtom3491 Fin15AnchoredAtom3511
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

theorem fin15Anchored_clause31972 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3244 chi ∧
      ¬Fin15AnchoredAtom3245 chi ∧
      ¬Fin15AnchoredAtom3247 chi ∧
      ¬Fin15AnchoredAtom3248 chi ∧
      ¬Fin15AnchoredAtom3256 chi ∧
      ¬Fin15AnchoredAtom3258 chi ∧
      ¬Fin15AnchoredAtom3259 chi ∧
      ¬Fin15AnchoredAtom3262 chi ∧
      ¬Fin15AnchoredAtom3263 chi ∧
      ¬Fin15AnchoredAtom3268 chi ∧
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
  refine ⟨{1, 4, 6, 7, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask14034
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3244 Fin15AnchoredAtom3245 Fin15AnchoredAtom3247
    Fin15AnchoredAtom3248 Fin15AnchoredAtom3256 Fin15AnchoredAtom3258 Fin15AnchoredAtom3259
    Fin15AnchoredAtom3262 Fin15AnchoredAtom3263 Fin15AnchoredAtom3268 Fin15AnchoredAtom3277
    Fin15AnchoredAtom3279 Fin15AnchoredAtom3280 Fin15AnchoredAtom3283 Fin15AnchoredAtom3284
    Fin15AnchoredAtom3289 Fin15AnchoredAtom3308 Fin15AnchoredAtom3309 Fin15AnchoredAtom3314
    Fin15AnchoredAtom3320 Fin15AnchoredAtom3417 Fin15AnchoredAtom3419 Fin15AnchoredAtom3420
    Fin15AnchoredAtom3423 Fin15AnchoredAtom3424 Fin15AnchoredAtom3429 Fin15AnchoredAtom3448
    Fin15AnchoredAtom3449 Fin15AnchoredAtom3454 Fin15AnchoredAtom3460 Fin15AnchoredAtom3483
    Fin15AnchoredAtom3484 Fin15AnchoredAtom3489 Fin15AnchoredAtom3495 Fin15AnchoredAtom3525
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

theorem fin15Anchored_clause31973 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3244 chi ∧
      ¬Fin15AnchoredAtom3245 chi ∧
      ¬Fin15AnchoredAtom3247 chi ∧
      ¬Fin15AnchoredAtom3249 chi ∧
      ¬Fin15AnchoredAtom3256 chi ∧
      ¬Fin15AnchoredAtom3258 chi ∧
      ¬Fin15AnchoredAtom3260 chi ∧
      ¬Fin15AnchoredAtom3262 chi ∧
      ¬Fin15AnchoredAtom3264 chi ∧
      ¬Fin15AnchoredAtom3269 chi ∧
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
  refine ⟨{1, 4, 6, 7, 9, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22226
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3244 Fin15AnchoredAtom3245 Fin15AnchoredAtom3247
    Fin15AnchoredAtom3249 Fin15AnchoredAtom3256 Fin15AnchoredAtom3258 Fin15AnchoredAtom3260
    Fin15AnchoredAtom3262 Fin15AnchoredAtom3264 Fin15AnchoredAtom3269 Fin15AnchoredAtom3277
    Fin15AnchoredAtom3279 Fin15AnchoredAtom3281 Fin15AnchoredAtom3283 Fin15AnchoredAtom3285
    Fin15AnchoredAtom3290 Fin15AnchoredAtom3308 Fin15AnchoredAtom3310 Fin15AnchoredAtom3315
    Fin15AnchoredAtom3321 Fin15AnchoredAtom3417 Fin15AnchoredAtom3419 Fin15AnchoredAtom3421
    Fin15AnchoredAtom3423 Fin15AnchoredAtom3425 Fin15AnchoredAtom3430 Fin15AnchoredAtom3448
    Fin15AnchoredAtom3450 Fin15AnchoredAtom3455 Fin15AnchoredAtom3461 Fin15AnchoredAtom3483
    Fin15AnchoredAtom3485 Fin15AnchoredAtom3490 Fin15AnchoredAtom3496 Fin15AnchoredAtom3526
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

theorem fin15Anchored_clause31974 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3244 chi ∧
      ¬Fin15AnchoredAtom3245 chi ∧
      ¬Fin15AnchoredAtom3248 chi ∧
      ¬Fin15AnchoredAtom3249 chi ∧
      ¬Fin15AnchoredAtom3256 chi ∧
      ¬Fin15AnchoredAtom3259 chi ∧
      ¬Fin15AnchoredAtom3260 chi ∧
      ¬Fin15AnchoredAtom3263 chi ∧
      ¬Fin15AnchoredAtom3264 chi ∧
      ¬Fin15AnchoredAtom3270 chi ∧
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
  refine ⟨{1, 4, 6, 7, 9, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26322
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3244 Fin15AnchoredAtom3245 Fin15AnchoredAtom3248
    Fin15AnchoredAtom3249 Fin15AnchoredAtom3256 Fin15AnchoredAtom3259 Fin15AnchoredAtom3260
    Fin15AnchoredAtom3263 Fin15AnchoredAtom3264 Fin15AnchoredAtom3270 Fin15AnchoredAtom3277
    Fin15AnchoredAtom3280 Fin15AnchoredAtom3281 Fin15AnchoredAtom3284 Fin15AnchoredAtom3285
    Fin15AnchoredAtom3291 Fin15AnchoredAtom3309 Fin15AnchoredAtom3310 Fin15AnchoredAtom3316
    Fin15AnchoredAtom3322 Fin15AnchoredAtom3417 Fin15AnchoredAtom3420 Fin15AnchoredAtom3421
    Fin15AnchoredAtom3424 Fin15AnchoredAtom3425 Fin15AnchoredAtom3431 Fin15AnchoredAtom3449
    Fin15AnchoredAtom3450 Fin15AnchoredAtom3456 Fin15AnchoredAtom3462 Fin15AnchoredAtom3484
    Fin15AnchoredAtom3485 Fin15AnchoredAtom3491 Fin15AnchoredAtom3497 Fin15AnchoredAtom3527
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

theorem fin15Anchored_clause31975 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3244 chi ∧
      ¬Fin15AnchoredAtom3247 chi ∧
      ¬Fin15AnchoredAtom3248 chi ∧
      ¬Fin15AnchoredAtom3249 chi ∧
      ¬Fin15AnchoredAtom3258 chi ∧
      ¬Fin15AnchoredAtom3259 chi ∧
      ¬Fin15AnchoredAtom3260 chi ∧
      ¬Fin15AnchoredAtom3268 chi ∧
      ¬Fin15AnchoredAtom3269 chi ∧
      ¬Fin15AnchoredAtom3270 chi ∧
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
  refine ⟨{1, 4, 6, 7, 9, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29394
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3244 Fin15AnchoredAtom3247 Fin15AnchoredAtom3248
    Fin15AnchoredAtom3249 Fin15AnchoredAtom3258 Fin15AnchoredAtom3259 Fin15AnchoredAtom3260
    Fin15AnchoredAtom3268 Fin15AnchoredAtom3269 Fin15AnchoredAtom3270 Fin15AnchoredAtom3279
    Fin15AnchoredAtom3280 Fin15AnchoredAtom3281 Fin15AnchoredAtom3289 Fin15AnchoredAtom3290
    Fin15AnchoredAtom3291 Fin15AnchoredAtom3314 Fin15AnchoredAtom3315 Fin15AnchoredAtom3316
    Fin15AnchoredAtom3326 Fin15AnchoredAtom3419 Fin15AnchoredAtom3420 Fin15AnchoredAtom3421
    Fin15AnchoredAtom3429 Fin15AnchoredAtom3430 Fin15AnchoredAtom3431 Fin15AnchoredAtom3454
    Fin15AnchoredAtom3455 Fin15AnchoredAtom3456 Fin15AnchoredAtom3466 Fin15AnchoredAtom3489
    Fin15AnchoredAtom3490 Fin15AnchoredAtom3491 Fin15AnchoredAtom3501 Fin15AnchoredAtom3531
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

theorem fin15Anchored_clause31976 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3245 chi ∧
      ¬Fin15AnchoredAtom3247 chi ∧
      ¬Fin15AnchoredAtom3248 chi ∧
      ¬Fin15AnchoredAtom3249 chi ∧
      ¬Fin15AnchoredAtom3262 chi ∧
      ¬Fin15AnchoredAtom3263 chi ∧
      ¬Fin15AnchoredAtom3264 chi ∧
      ¬Fin15AnchoredAtom3268 chi ∧
      ¬Fin15AnchoredAtom3269 chi ∧
      ¬Fin15AnchoredAtom3270 chi ∧
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
  refine ⟨{1, 4, 6, 7, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29906
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3245 Fin15AnchoredAtom3247 Fin15AnchoredAtom3248
    Fin15AnchoredAtom3249 Fin15AnchoredAtom3262 Fin15AnchoredAtom3263 Fin15AnchoredAtom3264
    Fin15AnchoredAtom3268 Fin15AnchoredAtom3269 Fin15AnchoredAtom3270 Fin15AnchoredAtom3283
    Fin15AnchoredAtom3284 Fin15AnchoredAtom3285 Fin15AnchoredAtom3289 Fin15AnchoredAtom3290
    Fin15AnchoredAtom3291 Fin15AnchoredAtom3320 Fin15AnchoredAtom3321 Fin15AnchoredAtom3322
    Fin15AnchoredAtom3326 Fin15AnchoredAtom3423 Fin15AnchoredAtom3424 Fin15AnchoredAtom3425
    Fin15AnchoredAtom3429 Fin15AnchoredAtom3430 Fin15AnchoredAtom3431 Fin15AnchoredAtom3460
    Fin15AnchoredAtom3461 Fin15AnchoredAtom3462 Fin15AnchoredAtom3466 Fin15AnchoredAtom3495
    Fin15AnchoredAtom3496 Fin15AnchoredAtom3497 Fin15AnchoredAtom3501 Fin15AnchoredAtom3535
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

theorem fin15Anchored_clause31977 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3256 chi ∧
      ¬Fin15AnchoredAtom3258 chi ∧
      ¬Fin15AnchoredAtom3259 chi ∧
      ¬Fin15AnchoredAtom3260 chi ∧
      ¬Fin15AnchoredAtom3262 chi ∧
      ¬Fin15AnchoredAtom3263 chi ∧
      ¬Fin15AnchoredAtom3264 chi ∧
      ¬Fin15AnchoredAtom3268 chi ∧
      ¬Fin15AnchoredAtom3269 chi ∧
      ¬Fin15AnchoredAtom3270 chi ∧
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
  refine ⟨{1, 4, 6, 9, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask30290
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3256 Fin15AnchoredAtom3258 Fin15AnchoredAtom3259
    Fin15AnchoredAtom3260 Fin15AnchoredAtom3262 Fin15AnchoredAtom3263 Fin15AnchoredAtom3264
    Fin15AnchoredAtom3268 Fin15AnchoredAtom3269 Fin15AnchoredAtom3270 Fin15AnchoredAtom3308
    Fin15AnchoredAtom3309 Fin15AnchoredAtom3310 Fin15AnchoredAtom3314 Fin15AnchoredAtom3315
    Fin15AnchoredAtom3316 Fin15AnchoredAtom3320 Fin15AnchoredAtom3321 Fin15AnchoredAtom3322
    Fin15AnchoredAtom3326 Fin15AnchoredAtom3448 Fin15AnchoredAtom3449 Fin15AnchoredAtom3450
    Fin15AnchoredAtom3454 Fin15AnchoredAtom3455 Fin15AnchoredAtom3456 Fin15AnchoredAtom3460
    Fin15AnchoredAtom3461 Fin15AnchoredAtom3462 Fin15AnchoredAtom3466 Fin15AnchoredAtom3525
    Fin15AnchoredAtom3526 Fin15AnchoredAtom3527 Fin15AnchoredAtom3531 Fin15AnchoredAtom3535
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

theorem fin15Anchored_clause31978 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3271 chi ∧
      ¬Fin15AnchoredAtom3274 chi ∧
      ¬Fin15AnchoredAtom3275 chi ∧
      ¬Fin15AnchoredAtom3276 chi ∧
      ¬Fin15AnchoredAtom3279 chi ∧
      ¬Fin15AnchoredAtom3280 chi ∧
      ¬Fin15AnchoredAtom3281 chi ∧
      ¬Fin15AnchoredAtom3289 chi ∧
      ¬Fin15AnchoredAtom3290 chi ∧
      ¬Fin15AnchoredAtom3291 chi ∧
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
      ¬Fin15AnchoredAtom3469 chi ∧
      ¬Fin15AnchoredAtom3470 chi ∧
      ¬Fin15AnchoredAtom3471 chi ∧
      ¬Fin15AnchoredAtom3479 chi ∧
      ¬Fin15AnchoredAtom3480 chi ∧
      ¬Fin15AnchoredAtom3481 chi ∧
      ¬Fin15AnchoredAtom3489 chi ∧
      ¬Fin15AnchoredAtom3490 chi ∧
      ¬Fin15AnchoredAtom3491 chi ∧
      ¬Fin15AnchoredAtom3501 chi ∧
      ¬Fin15AnchoredAtom3509 chi ∧
      ¬Fin15AnchoredAtom3510 chi ∧
      ¬Fin15AnchoredAtom3511 chi ∧
      ¬Fin15AnchoredAtom3521 chi ∧
      ¬Fin15AnchoredAtom3531 chi ∧
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
  refine ⟨{1, 4, 7, 8, 9, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29586
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3271 Fin15AnchoredAtom3274 Fin15AnchoredAtom3275
    Fin15AnchoredAtom3276 Fin15AnchoredAtom3279 Fin15AnchoredAtom3280 Fin15AnchoredAtom3281
    Fin15AnchoredAtom3289 Fin15AnchoredAtom3290 Fin15AnchoredAtom3291 Fin15AnchoredAtom3294
    Fin15AnchoredAtom3295 Fin15AnchoredAtom3296 Fin15AnchoredAtom3304 Fin15AnchoredAtom3305
    Fin15AnchoredAtom3306 Fin15AnchoredAtom3314 Fin15AnchoredAtom3315 Fin15AnchoredAtom3316
    Fin15AnchoredAtom3326 Fin15AnchoredAtom3469 Fin15AnchoredAtom3470 Fin15AnchoredAtom3471
    Fin15AnchoredAtom3479 Fin15AnchoredAtom3480 Fin15AnchoredAtom3481 Fin15AnchoredAtom3489
    Fin15AnchoredAtom3490 Fin15AnchoredAtom3491 Fin15AnchoredAtom3501 Fin15AnchoredAtom3509
    Fin15AnchoredAtom3510 Fin15AnchoredAtom3511 Fin15AnchoredAtom3521 Fin15AnchoredAtom3531
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

theorem fin15Anchored_clause31979 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3277 chi ∧
      ¬Fin15AnchoredAtom3279 chi ∧
      ¬Fin15AnchoredAtom3280 chi ∧
      ¬Fin15AnchoredAtom3281 chi ∧
      ¬Fin15AnchoredAtom3283 chi ∧
      ¬Fin15AnchoredAtom3284 chi ∧
      ¬Fin15AnchoredAtom3285 chi ∧
      ¬Fin15AnchoredAtom3289 chi ∧
      ¬Fin15AnchoredAtom3290 chi ∧
      ¬Fin15AnchoredAtom3291 chi ∧
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
  refine ⟨{1, 4, 7, 9, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask30354
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3277 Fin15AnchoredAtom3279 Fin15AnchoredAtom3280
    Fin15AnchoredAtom3281 Fin15AnchoredAtom3283 Fin15AnchoredAtom3284 Fin15AnchoredAtom3285
    Fin15AnchoredAtom3289 Fin15AnchoredAtom3290 Fin15AnchoredAtom3291 Fin15AnchoredAtom3308
    Fin15AnchoredAtom3309 Fin15AnchoredAtom3310 Fin15AnchoredAtom3314 Fin15AnchoredAtom3315
    Fin15AnchoredAtom3316 Fin15AnchoredAtom3320 Fin15AnchoredAtom3321 Fin15AnchoredAtom3322
    Fin15AnchoredAtom3326 Fin15AnchoredAtom3483 Fin15AnchoredAtom3484 Fin15AnchoredAtom3485
    Fin15AnchoredAtom3489 Fin15AnchoredAtom3490 Fin15AnchoredAtom3491 Fin15AnchoredAtom3495
    Fin15AnchoredAtom3496 Fin15AnchoredAtom3497 Fin15AnchoredAtom3501 Fin15AnchoredAtom3525
    Fin15AnchoredAtom3526 Fin15AnchoredAtom3527 Fin15AnchoredAtom3531 Fin15AnchoredAtom3535
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

theorem fin15Anchored_clause31980 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3327 chi ∧
      ¬Fin15AnchoredAtom3329 chi ∧
      ¬Fin15AnchoredAtom3332 chi ∧
      ¬Fin15AnchoredAtom3333 chi ∧
      ¬Fin15AnchoredAtom3335 chi ∧
      ¬Fin15AnchoredAtom3338 chi ∧
      ¬Fin15AnchoredAtom3339 chi ∧
      ¬Fin15AnchoredAtom3347 chi ∧
      ¬Fin15AnchoredAtom3348 chi ∧
      ¬Fin15AnchoredAtom3354 chi ∧
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
      ¬Fin15AnchoredAtom3412 chi ∧
      ¬Fin15AnchoredAtom3415 chi ∧
      ¬Fin15AnchoredAtom3416 chi ∧
      ¬Fin15AnchoredAtom3424 chi ∧
      ¬Fin15AnchoredAtom3425 chi ∧
      ¬Fin15AnchoredAtom3431 chi ∧
      ¬Fin15AnchoredAtom3439 chi ∧
      ¬Fin15AnchoredAtom3440 chi ∧
      ¬Fin15AnchoredAtom3446 chi ∧
      ¬Fin15AnchoredAtom3462 chi ∧
      ¬Fin15AnchoredAtom3474 chi ∧
      ¬Fin15AnchoredAtom3475 chi ∧
      ¬Fin15AnchoredAtom3481 chi ∧
      ¬Fin15AnchoredAtom3497 chi ∧
      ¬Fin15AnchoredAtom3517 chi ∧
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
  refine ⟨{1, 5, 6, 7, 8, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26082
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3327 Fin15AnchoredAtom3329 Fin15AnchoredAtom3332
    Fin15AnchoredAtom3333 Fin15AnchoredAtom3335 Fin15AnchoredAtom3338 Fin15AnchoredAtom3339
    Fin15AnchoredAtom3347 Fin15AnchoredAtom3348 Fin15AnchoredAtom3354 Fin15AnchoredAtom3356
    Fin15AnchoredAtom3359 Fin15AnchoredAtom3360 Fin15AnchoredAtom3368 Fin15AnchoredAtom3369
    Fin15AnchoredAtom3375 Fin15AnchoredAtom3383 Fin15AnchoredAtom3384 Fin15AnchoredAtom3390
    Fin15AnchoredAtom3406 Fin15AnchoredAtom3412 Fin15AnchoredAtom3415 Fin15AnchoredAtom3416
    Fin15AnchoredAtom3424 Fin15AnchoredAtom3425 Fin15AnchoredAtom3431 Fin15AnchoredAtom3439
    Fin15AnchoredAtom3440 Fin15AnchoredAtom3446 Fin15AnchoredAtom3462 Fin15AnchoredAtom3474
    Fin15AnchoredAtom3475 Fin15AnchoredAtom3481 Fin15AnchoredAtom3497 Fin15AnchoredAtom3517
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

theorem fin15Anchored_clause31981 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3328 chi ∧
      ¬Fin15AnchoredAtom3329 chi ∧
      ¬Fin15AnchoredAtom3331 chi ∧
      ¬Fin15AnchoredAtom3332 chi ∧
      ¬Fin15AnchoredAtom3340 chi ∧
      ¬Fin15AnchoredAtom3342 chi ∧
      ¬Fin15AnchoredAtom3343 chi ∧
      ¬Fin15AnchoredAtom3346 chi ∧
      ¬Fin15AnchoredAtom3347 chi ∧
      ¬Fin15AnchoredAtom3352 chi ∧
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
  refine ⟨{1, 5, 6, 7, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask14050
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3328 Fin15AnchoredAtom3329 Fin15AnchoredAtom3331
    Fin15AnchoredAtom3332 Fin15AnchoredAtom3340 Fin15AnchoredAtom3342 Fin15AnchoredAtom3343
    Fin15AnchoredAtom3346 Fin15AnchoredAtom3347 Fin15AnchoredAtom3352 Fin15AnchoredAtom3361
    Fin15AnchoredAtom3363 Fin15AnchoredAtom3364 Fin15AnchoredAtom3367 Fin15AnchoredAtom3368
    Fin15AnchoredAtom3373 Fin15AnchoredAtom3392 Fin15AnchoredAtom3393 Fin15AnchoredAtom3398
    Fin15AnchoredAtom3404 Fin15AnchoredAtom3417 Fin15AnchoredAtom3419 Fin15AnchoredAtom3420
    Fin15AnchoredAtom3423 Fin15AnchoredAtom3424 Fin15AnchoredAtom3429 Fin15AnchoredAtom3448
    Fin15AnchoredAtom3449 Fin15AnchoredAtom3454 Fin15AnchoredAtom3460 Fin15AnchoredAtom3483
    Fin15AnchoredAtom3484 Fin15AnchoredAtom3489 Fin15AnchoredAtom3495 Fin15AnchoredAtom3525
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

theorem fin15Anchored_clause31982 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3328 chi ∧
      ¬Fin15AnchoredAtom3329 chi ∧
      ¬Fin15AnchoredAtom3331 chi ∧
      ¬Fin15AnchoredAtom3333 chi ∧
      ¬Fin15AnchoredAtom3340 chi ∧
      ¬Fin15AnchoredAtom3342 chi ∧
      ¬Fin15AnchoredAtom3344 chi ∧
      ¬Fin15AnchoredAtom3346 chi ∧
      ¬Fin15AnchoredAtom3348 chi ∧
      ¬Fin15AnchoredAtom3353 chi ∧
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
  refine ⟨{1, 5, 6, 7, 9, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask22242
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3328 Fin15AnchoredAtom3329 Fin15AnchoredAtom3331
    Fin15AnchoredAtom3333 Fin15AnchoredAtom3340 Fin15AnchoredAtom3342 Fin15AnchoredAtom3344
    Fin15AnchoredAtom3346 Fin15AnchoredAtom3348 Fin15AnchoredAtom3353 Fin15AnchoredAtom3361
    Fin15AnchoredAtom3363 Fin15AnchoredAtom3365 Fin15AnchoredAtom3367 Fin15AnchoredAtom3369
    Fin15AnchoredAtom3374 Fin15AnchoredAtom3392 Fin15AnchoredAtom3394 Fin15AnchoredAtom3399
    Fin15AnchoredAtom3405 Fin15AnchoredAtom3417 Fin15AnchoredAtom3419 Fin15AnchoredAtom3421
    Fin15AnchoredAtom3423 Fin15AnchoredAtom3425 Fin15AnchoredAtom3430 Fin15AnchoredAtom3448
    Fin15AnchoredAtom3450 Fin15AnchoredAtom3455 Fin15AnchoredAtom3461 Fin15AnchoredAtom3483
    Fin15AnchoredAtom3485 Fin15AnchoredAtom3490 Fin15AnchoredAtom3496 Fin15AnchoredAtom3526
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

theorem fin15Anchored_clause31983 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3328 chi ∧
      ¬Fin15AnchoredAtom3329 chi ∧
      ¬Fin15AnchoredAtom3332 chi ∧
      ¬Fin15AnchoredAtom3333 chi ∧
      ¬Fin15AnchoredAtom3340 chi ∧
      ¬Fin15AnchoredAtom3343 chi ∧
      ¬Fin15AnchoredAtom3344 chi ∧
      ¬Fin15AnchoredAtom3347 chi ∧
      ¬Fin15AnchoredAtom3348 chi ∧
      ¬Fin15AnchoredAtom3354 chi ∧
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
  refine ⟨{1, 5, 6, 7, 9, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26338
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3328 Fin15AnchoredAtom3329 Fin15AnchoredAtom3332
    Fin15AnchoredAtom3333 Fin15AnchoredAtom3340 Fin15AnchoredAtom3343 Fin15AnchoredAtom3344
    Fin15AnchoredAtom3347 Fin15AnchoredAtom3348 Fin15AnchoredAtom3354 Fin15AnchoredAtom3361
    Fin15AnchoredAtom3364 Fin15AnchoredAtom3365 Fin15AnchoredAtom3368 Fin15AnchoredAtom3369
    Fin15AnchoredAtom3375 Fin15AnchoredAtom3393 Fin15AnchoredAtom3394 Fin15AnchoredAtom3400
    Fin15AnchoredAtom3406 Fin15AnchoredAtom3417 Fin15AnchoredAtom3420 Fin15AnchoredAtom3421
    Fin15AnchoredAtom3424 Fin15AnchoredAtom3425 Fin15AnchoredAtom3431 Fin15AnchoredAtom3449
    Fin15AnchoredAtom3450 Fin15AnchoredAtom3456 Fin15AnchoredAtom3462 Fin15AnchoredAtom3484
    Fin15AnchoredAtom3485 Fin15AnchoredAtom3491 Fin15AnchoredAtom3497 Fin15AnchoredAtom3527
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

theorem fin15Anchored_clause31984 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3328 chi ∧
      ¬Fin15AnchoredAtom3331 chi ∧
      ¬Fin15AnchoredAtom3332 chi ∧
      ¬Fin15AnchoredAtom3333 chi ∧
      ¬Fin15AnchoredAtom3342 chi ∧
      ¬Fin15AnchoredAtom3343 chi ∧
      ¬Fin15AnchoredAtom3344 chi ∧
      ¬Fin15AnchoredAtom3352 chi ∧
      ¬Fin15AnchoredAtom3353 chi ∧
      ¬Fin15AnchoredAtom3354 chi ∧
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
  refine ⟨{1, 5, 6, 7, 9, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29410
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3328 Fin15AnchoredAtom3331 Fin15AnchoredAtom3332
    Fin15AnchoredAtom3333 Fin15AnchoredAtom3342 Fin15AnchoredAtom3343 Fin15AnchoredAtom3344
    Fin15AnchoredAtom3352 Fin15AnchoredAtom3353 Fin15AnchoredAtom3354 Fin15AnchoredAtom3363
    Fin15AnchoredAtom3364 Fin15AnchoredAtom3365 Fin15AnchoredAtom3373 Fin15AnchoredAtom3374
    Fin15AnchoredAtom3375 Fin15AnchoredAtom3398 Fin15AnchoredAtom3399 Fin15AnchoredAtom3400
    Fin15AnchoredAtom3410 Fin15AnchoredAtom3419 Fin15AnchoredAtom3420 Fin15AnchoredAtom3421
    Fin15AnchoredAtom3429 Fin15AnchoredAtom3430 Fin15AnchoredAtom3431 Fin15AnchoredAtom3454
    Fin15AnchoredAtom3455 Fin15AnchoredAtom3456 Fin15AnchoredAtom3466 Fin15AnchoredAtom3489
    Fin15AnchoredAtom3490 Fin15AnchoredAtom3491 Fin15AnchoredAtom3501 Fin15AnchoredAtom3531
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

theorem fin15Anchored_clause31985 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3329 chi ∧
      ¬Fin15AnchoredAtom3331 chi ∧
      ¬Fin15AnchoredAtom3332 chi ∧
      ¬Fin15AnchoredAtom3333 chi ∧
      ¬Fin15AnchoredAtom3346 chi ∧
      ¬Fin15AnchoredAtom3347 chi ∧
      ¬Fin15AnchoredAtom3348 chi ∧
      ¬Fin15AnchoredAtom3352 chi ∧
      ¬Fin15AnchoredAtom3353 chi ∧
      ¬Fin15AnchoredAtom3354 chi ∧
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
  refine ⟨{1, 5, 6, 7, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29922
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3329 Fin15AnchoredAtom3331 Fin15AnchoredAtom3332
    Fin15AnchoredAtom3333 Fin15AnchoredAtom3346 Fin15AnchoredAtom3347 Fin15AnchoredAtom3348
    Fin15AnchoredAtom3352 Fin15AnchoredAtom3353 Fin15AnchoredAtom3354 Fin15AnchoredAtom3367
    Fin15AnchoredAtom3368 Fin15AnchoredAtom3369 Fin15AnchoredAtom3373 Fin15AnchoredAtom3374
    Fin15AnchoredAtom3375 Fin15AnchoredAtom3404 Fin15AnchoredAtom3405 Fin15AnchoredAtom3406
    Fin15AnchoredAtom3410 Fin15AnchoredAtom3423 Fin15AnchoredAtom3424 Fin15AnchoredAtom3425
    Fin15AnchoredAtom3429 Fin15AnchoredAtom3430 Fin15AnchoredAtom3431 Fin15AnchoredAtom3460
    Fin15AnchoredAtom3461 Fin15AnchoredAtom3462 Fin15AnchoredAtom3466 Fin15AnchoredAtom3495
    Fin15AnchoredAtom3496 Fin15AnchoredAtom3497 Fin15AnchoredAtom3501 Fin15AnchoredAtom3535
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

theorem fin15Anchored_clause31986 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3334 chi ∧
      ¬Fin15AnchoredAtom3335 chi ∧
      ¬Fin15AnchoredAtom3337 chi ∧
      ¬Fin15AnchoredAtom3338 chi ∧
      ¬Fin15AnchoredAtom3340 chi ∧
      ¬Fin15AnchoredAtom3342 chi ∧
      ¬Fin15AnchoredAtom3343 chi ∧
      ¬Fin15AnchoredAtom3346 chi ∧
      ¬Fin15AnchoredAtom3347 chi ∧
      ¬Fin15AnchoredAtom3352 chi ∧
      ¬Fin15AnchoredAtom3376 chi ∧
      ¬Fin15AnchoredAtom3378 chi ∧
      ¬Fin15AnchoredAtom3379 chi ∧
      ¬Fin15AnchoredAtom3382 chi ∧
      ¬Fin15AnchoredAtom3383 chi ∧
      ¬Fin15AnchoredAtom3388 chi ∧
      ¬Fin15AnchoredAtom3392 chi ∧
      ¬Fin15AnchoredAtom3393 chi ∧
      ¬Fin15AnchoredAtom3398 chi ∧
      ¬Fin15AnchoredAtom3404 chi ∧
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
  refine ⟨{1, 5, 6, 8, 9, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask14178
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3334 Fin15AnchoredAtom3335 Fin15AnchoredAtom3337
    Fin15AnchoredAtom3338 Fin15AnchoredAtom3340 Fin15AnchoredAtom3342 Fin15AnchoredAtom3343
    Fin15AnchoredAtom3346 Fin15AnchoredAtom3347 Fin15AnchoredAtom3352 Fin15AnchoredAtom3376
    Fin15AnchoredAtom3378 Fin15AnchoredAtom3379 Fin15AnchoredAtom3382 Fin15AnchoredAtom3383
    Fin15AnchoredAtom3388 Fin15AnchoredAtom3392 Fin15AnchoredAtom3393 Fin15AnchoredAtom3398
    Fin15AnchoredAtom3404 Fin15AnchoredAtom3432 Fin15AnchoredAtom3434 Fin15AnchoredAtom3435
    Fin15AnchoredAtom3438 Fin15AnchoredAtom3439 Fin15AnchoredAtom3444 Fin15AnchoredAtom3448
    Fin15AnchoredAtom3449 Fin15AnchoredAtom3454 Fin15AnchoredAtom3460 Fin15AnchoredAtom3503
    Fin15AnchoredAtom3504 Fin15AnchoredAtom3509 Fin15AnchoredAtom3515 Fin15AnchoredAtom3525
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

theorem fin15Anchored_clause31987 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3334 chi ∧
      ¬Fin15AnchoredAtom3335 chi ∧
      ¬Fin15AnchoredAtom3338 chi ∧
      ¬Fin15AnchoredAtom3339 chi ∧
      ¬Fin15AnchoredAtom3340 chi ∧
      ¬Fin15AnchoredAtom3343 chi ∧
      ¬Fin15AnchoredAtom3344 chi ∧
      ¬Fin15AnchoredAtom3347 chi ∧
      ¬Fin15AnchoredAtom3348 chi ∧
      ¬Fin15AnchoredAtom3354 chi ∧
      ¬Fin15AnchoredAtom3376 chi ∧
      ¬Fin15AnchoredAtom3379 chi ∧
      ¬Fin15AnchoredAtom3380 chi ∧
      ¬Fin15AnchoredAtom3383 chi ∧
      ¬Fin15AnchoredAtom3384 chi ∧
      ¬Fin15AnchoredAtom3390 chi ∧
      ¬Fin15AnchoredAtom3393 chi ∧
      ¬Fin15AnchoredAtom3394 chi ∧
      ¬Fin15AnchoredAtom3400 chi ∧
      ¬Fin15AnchoredAtom3406 chi ∧
      ¬Fin15AnchoredAtom3432 chi ∧
      ¬Fin15AnchoredAtom3435 chi ∧
      ¬Fin15AnchoredAtom3436 chi ∧
      ¬Fin15AnchoredAtom3439 chi ∧
      ¬Fin15AnchoredAtom3440 chi ∧
      ¬Fin15AnchoredAtom3446 chi ∧
      ¬Fin15AnchoredAtom3449 chi ∧
      ¬Fin15AnchoredAtom3450 chi ∧
      ¬Fin15AnchoredAtom3456 chi ∧
      ¬Fin15AnchoredAtom3462 chi ∧
      ¬Fin15AnchoredAtom3504 chi ∧
      ¬Fin15AnchoredAtom3505 chi ∧
      ¬Fin15AnchoredAtom3511 chi ∧
      ¬Fin15AnchoredAtom3517 chi ∧
      ¬Fin15AnchoredAtom3527 chi ∧
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
  refine ⟨{1, 5, 6, 8, 9, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26466
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3334 Fin15AnchoredAtom3335 Fin15AnchoredAtom3338
    Fin15AnchoredAtom3339 Fin15AnchoredAtom3340 Fin15AnchoredAtom3343 Fin15AnchoredAtom3344
    Fin15AnchoredAtom3347 Fin15AnchoredAtom3348 Fin15AnchoredAtom3354 Fin15AnchoredAtom3376
    Fin15AnchoredAtom3379 Fin15AnchoredAtom3380 Fin15AnchoredAtom3383 Fin15AnchoredAtom3384
    Fin15AnchoredAtom3390 Fin15AnchoredAtom3393 Fin15AnchoredAtom3394 Fin15AnchoredAtom3400
    Fin15AnchoredAtom3406 Fin15AnchoredAtom3432 Fin15AnchoredAtom3435 Fin15AnchoredAtom3436
    Fin15AnchoredAtom3439 Fin15AnchoredAtom3440 Fin15AnchoredAtom3446 Fin15AnchoredAtom3449
    Fin15AnchoredAtom3450 Fin15AnchoredAtom3456 Fin15AnchoredAtom3462 Fin15AnchoredAtom3504
    Fin15AnchoredAtom3505 Fin15AnchoredAtom3511 Fin15AnchoredAtom3517 Fin15AnchoredAtom3527
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

theorem fin15Anchored_clause31988 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3334 chi ∧
      ¬Fin15AnchoredAtom3337 chi ∧
      ¬Fin15AnchoredAtom3338 chi ∧
      ¬Fin15AnchoredAtom3339 chi ∧
      ¬Fin15AnchoredAtom3342 chi ∧
      ¬Fin15AnchoredAtom3343 chi ∧
      ¬Fin15AnchoredAtom3344 chi ∧
      ¬Fin15AnchoredAtom3352 chi ∧
      ¬Fin15AnchoredAtom3353 chi ∧
      ¬Fin15AnchoredAtom3354 chi ∧
      ¬Fin15AnchoredAtom3378 chi ∧
      ¬Fin15AnchoredAtom3379 chi ∧
      ¬Fin15AnchoredAtom3380 chi ∧
      ¬Fin15AnchoredAtom3388 chi ∧
      ¬Fin15AnchoredAtom3389 chi ∧
      ¬Fin15AnchoredAtom3390 chi ∧
      ¬Fin15AnchoredAtom3398 chi ∧
      ¬Fin15AnchoredAtom3399 chi ∧
      ¬Fin15AnchoredAtom3400 chi ∧
      ¬Fin15AnchoredAtom3410 chi ∧
      ¬Fin15AnchoredAtom3434 chi ∧
      ¬Fin15AnchoredAtom3435 chi ∧
      ¬Fin15AnchoredAtom3436 chi ∧
      ¬Fin15AnchoredAtom3444 chi ∧
      ¬Fin15AnchoredAtom3445 chi ∧
      ¬Fin15AnchoredAtom3446 chi ∧
      ¬Fin15AnchoredAtom3454 chi ∧
      ¬Fin15AnchoredAtom3455 chi ∧
      ¬Fin15AnchoredAtom3456 chi ∧
      ¬Fin15AnchoredAtom3466 chi ∧
      ¬Fin15AnchoredAtom3509 chi ∧
      ¬Fin15AnchoredAtom3510 chi ∧
      ¬Fin15AnchoredAtom3511 chi ∧
      ¬Fin15AnchoredAtom3521 chi ∧
      ¬Fin15AnchoredAtom3531 chi ∧
      ¬Fin15AnchoredAtom4595 chi ∧
      ¬Fin15AnchoredAtom4596 chi ∧
      ¬Fin15AnchoredAtom4597 chi ∧
      ¬Fin15AnchoredAtom4605 chi ∧
      ¬Fin15AnchoredAtom4606 chi ∧
      ¬Fin15AnchoredAtom4607 chi ∧
      ¬Fin15AnchoredAtom4615 chi ∧
      ¬Fin15AnchoredAtom4616 chi ∧
      ¬Fin15AnchoredAtom4617 chi ∧
      ¬Fin15AnchoredAtom4627 chi ∧
      ¬Fin15AnchoredAtom4670 chi ∧
      ¬Fin15AnchoredAtom4671 chi ∧
      ¬Fin15AnchoredAtom4672 chi ∧
      ¬Fin15AnchoredAtom4682 chi ∧
      ¬Fin15AnchoredAtom4692 chi ∧
      ¬Fin15AnchoredAtom4740 chi ∧
      ¬Fin15AnchoredAtom4741 chi ∧
      ¬Fin15AnchoredAtom4742 chi ∧
      ¬Fin15AnchoredAtom4752 chi ∧
      ¬Fin15AnchoredAtom4762 chi ∧
      ¬Fin15AnchoredAtom4812 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 5, 6, 8, 9, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29538
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3334 Fin15AnchoredAtom3337 Fin15AnchoredAtom3338
    Fin15AnchoredAtom3339 Fin15AnchoredAtom3342 Fin15AnchoredAtom3343 Fin15AnchoredAtom3344
    Fin15AnchoredAtom3352 Fin15AnchoredAtom3353 Fin15AnchoredAtom3354 Fin15AnchoredAtom3378
    Fin15AnchoredAtom3379 Fin15AnchoredAtom3380 Fin15AnchoredAtom3388 Fin15AnchoredAtom3389
    Fin15AnchoredAtom3390 Fin15AnchoredAtom3398 Fin15AnchoredAtom3399 Fin15AnchoredAtom3400
    Fin15AnchoredAtom3410 Fin15AnchoredAtom3434 Fin15AnchoredAtom3435 Fin15AnchoredAtom3436
    Fin15AnchoredAtom3444 Fin15AnchoredAtom3445 Fin15AnchoredAtom3446 Fin15AnchoredAtom3454
    Fin15AnchoredAtom3455 Fin15AnchoredAtom3456 Fin15AnchoredAtom3466 Fin15AnchoredAtom3509
    Fin15AnchoredAtom3510 Fin15AnchoredAtom3511 Fin15AnchoredAtom3521 Fin15AnchoredAtom3531
    Fin15AnchoredAtom4595 Fin15AnchoredAtom4596 Fin15AnchoredAtom4597 Fin15AnchoredAtom4605
    Fin15AnchoredAtom4606 Fin15AnchoredAtom4607 Fin15AnchoredAtom4615 Fin15AnchoredAtom4616
    Fin15AnchoredAtom4617 Fin15AnchoredAtom4627 Fin15AnchoredAtom4670 Fin15AnchoredAtom4671
    Fin15AnchoredAtom4672 Fin15AnchoredAtom4682 Fin15AnchoredAtom4692 Fin15AnchoredAtom4740
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

theorem fin15Anchored_clause31989 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3340 chi ∧
      ¬Fin15AnchoredAtom3342 chi ∧
      ¬Fin15AnchoredAtom3343 chi ∧
      ¬Fin15AnchoredAtom3344 chi ∧
      ¬Fin15AnchoredAtom3346 chi ∧
      ¬Fin15AnchoredAtom3347 chi ∧
      ¬Fin15AnchoredAtom3348 chi ∧
      ¬Fin15AnchoredAtom3352 chi ∧
      ¬Fin15AnchoredAtom3353 chi ∧
      ¬Fin15AnchoredAtom3354 chi ∧
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
  refine ⟨{1, 5, 6, 9, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask30306
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3340 Fin15AnchoredAtom3342 Fin15AnchoredAtom3343
    Fin15AnchoredAtom3344 Fin15AnchoredAtom3346 Fin15AnchoredAtom3347 Fin15AnchoredAtom3348
    Fin15AnchoredAtom3352 Fin15AnchoredAtom3353 Fin15AnchoredAtom3354 Fin15AnchoredAtom3392
    Fin15AnchoredAtom3393 Fin15AnchoredAtom3394 Fin15AnchoredAtom3398 Fin15AnchoredAtom3399
    Fin15AnchoredAtom3400 Fin15AnchoredAtom3404 Fin15AnchoredAtom3405 Fin15AnchoredAtom3406
    Fin15AnchoredAtom3410 Fin15AnchoredAtom3448 Fin15AnchoredAtom3449 Fin15AnchoredAtom3450
    Fin15AnchoredAtom3454 Fin15AnchoredAtom3455 Fin15AnchoredAtom3456 Fin15AnchoredAtom3460
    Fin15AnchoredAtom3461 Fin15AnchoredAtom3462 Fin15AnchoredAtom3466 Fin15AnchoredAtom3525
    Fin15AnchoredAtom3526 Fin15AnchoredAtom3527 Fin15AnchoredAtom3531 Fin15AnchoredAtom3535
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

theorem fin15Anchored_clause31990 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3355 chi ∧
      ¬Fin15AnchoredAtom3356 chi ∧
      ¬Fin15AnchoredAtom3359 chi ∧
      ¬Fin15AnchoredAtom3360 chi ∧
      ¬Fin15AnchoredAtom3361 chi ∧
      ¬Fin15AnchoredAtom3364 chi ∧
      ¬Fin15AnchoredAtom3365 chi ∧
      ¬Fin15AnchoredAtom3368 chi ∧
      ¬Fin15AnchoredAtom3369 chi ∧
      ¬Fin15AnchoredAtom3375 chi ∧
      ¬Fin15AnchoredAtom3376 chi ∧
      ¬Fin15AnchoredAtom3379 chi ∧
      ¬Fin15AnchoredAtom3380 chi ∧
      ¬Fin15AnchoredAtom3383 chi ∧
      ¬Fin15AnchoredAtom3384 chi ∧
      ¬Fin15AnchoredAtom3390 chi ∧
      ¬Fin15AnchoredAtom3393 chi ∧
      ¬Fin15AnchoredAtom3394 chi ∧
      ¬Fin15AnchoredAtom3400 chi ∧
      ¬Fin15AnchoredAtom3406 chi ∧
      ¬Fin15AnchoredAtom3467 chi ∧
      ¬Fin15AnchoredAtom3470 chi ∧
      ¬Fin15AnchoredAtom3471 chi ∧
      ¬Fin15AnchoredAtom3474 chi ∧
      ¬Fin15AnchoredAtom3475 chi ∧
      ¬Fin15AnchoredAtom3481 chi ∧
      ¬Fin15AnchoredAtom3484 chi ∧
      ¬Fin15AnchoredAtom3485 chi ∧
      ¬Fin15AnchoredAtom3491 chi ∧
      ¬Fin15AnchoredAtom3497 chi ∧
      ¬Fin15AnchoredAtom3504 chi ∧
      ¬Fin15AnchoredAtom3505 chi ∧
      ¬Fin15AnchoredAtom3511 chi ∧
      ¬Fin15AnchoredAtom3517 chi ∧
      ¬Fin15AnchoredAtom3527 chi ∧
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
  refine ⟨{1, 5, 7, 8, 9, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask26530
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3355 Fin15AnchoredAtom3356 Fin15AnchoredAtom3359
    Fin15AnchoredAtom3360 Fin15AnchoredAtom3361 Fin15AnchoredAtom3364 Fin15AnchoredAtom3365
    Fin15AnchoredAtom3368 Fin15AnchoredAtom3369 Fin15AnchoredAtom3375 Fin15AnchoredAtom3376
    Fin15AnchoredAtom3379 Fin15AnchoredAtom3380 Fin15AnchoredAtom3383 Fin15AnchoredAtom3384
    Fin15AnchoredAtom3390 Fin15AnchoredAtom3393 Fin15AnchoredAtom3394 Fin15AnchoredAtom3400
    Fin15AnchoredAtom3406 Fin15AnchoredAtom3467 Fin15AnchoredAtom3470 Fin15AnchoredAtom3471
    Fin15AnchoredAtom3474 Fin15AnchoredAtom3475 Fin15AnchoredAtom3481 Fin15AnchoredAtom3484
    Fin15AnchoredAtom3485 Fin15AnchoredAtom3491 Fin15AnchoredAtom3497 Fin15AnchoredAtom3504
    Fin15AnchoredAtom3505 Fin15AnchoredAtom3511 Fin15AnchoredAtom3517 Fin15AnchoredAtom3527
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

theorem fin15Anchored_clause31991 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3361 chi ∧
      ¬Fin15AnchoredAtom3363 chi ∧
      ¬Fin15AnchoredAtom3364 chi ∧
      ¬Fin15AnchoredAtom3365 chi ∧
      ¬Fin15AnchoredAtom3367 chi ∧
      ¬Fin15AnchoredAtom3368 chi ∧
      ¬Fin15AnchoredAtom3369 chi ∧
      ¬Fin15AnchoredAtom3373 chi ∧
      ¬Fin15AnchoredAtom3374 chi ∧
      ¬Fin15AnchoredAtom3375 chi ∧
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
  refine ⟨{1, 5, 7, 9, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask30370
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3361 Fin15AnchoredAtom3363 Fin15AnchoredAtom3364
    Fin15AnchoredAtom3365 Fin15AnchoredAtom3367 Fin15AnchoredAtom3368 Fin15AnchoredAtom3369
    Fin15AnchoredAtom3373 Fin15AnchoredAtom3374 Fin15AnchoredAtom3375 Fin15AnchoredAtom3392
    Fin15AnchoredAtom3393 Fin15AnchoredAtom3394 Fin15AnchoredAtom3398 Fin15AnchoredAtom3399
    Fin15AnchoredAtom3400 Fin15AnchoredAtom3404 Fin15AnchoredAtom3405 Fin15AnchoredAtom3406
    Fin15AnchoredAtom3410 Fin15AnchoredAtom3483 Fin15AnchoredAtom3484 Fin15AnchoredAtom3485
    Fin15AnchoredAtom3489 Fin15AnchoredAtom3490 Fin15AnchoredAtom3491 Fin15AnchoredAtom3495
    Fin15AnchoredAtom3496 Fin15AnchoredAtom3497 Fin15AnchoredAtom3501 Fin15AnchoredAtom3525
    Fin15AnchoredAtom3526 Fin15AnchoredAtom3527 Fin15AnchoredAtom3531 Fin15AnchoredAtom3535
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

theorem fin15Anchored_clause31992 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3376 chi ∧
      ¬Fin15AnchoredAtom3378 chi ∧
      ¬Fin15AnchoredAtom3379 chi ∧
      ¬Fin15AnchoredAtom3380 chi ∧
      ¬Fin15AnchoredAtom3382 chi ∧
      ¬Fin15AnchoredAtom3383 chi ∧
      ¬Fin15AnchoredAtom3384 chi ∧
      ¬Fin15AnchoredAtom3388 chi ∧
      ¬Fin15AnchoredAtom3389 chi ∧
      ¬Fin15AnchoredAtom3390 chi ∧
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
      ¬Fin15AnchoredAtom3503 chi ∧
      ¬Fin15AnchoredAtom3504 chi ∧
      ¬Fin15AnchoredAtom3505 chi ∧
      ¬Fin15AnchoredAtom3509 chi ∧
      ¬Fin15AnchoredAtom3510 chi ∧
      ¬Fin15AnchoredAtom3511 chi ∧
      ¬Fin15AnchoredAtom3515 chi ∧
      ¬Fin15AnchoredAtom3516 chi ∧
      ¬Fin15AnchoredAtom3517 chi ∧
      ¬Fin15AnchoredAtom3521 chi ∧
      ¬Fin15AnchoredAtom3525 chi ∧
      ¬Fin15AnchoredAtom3526 chi ∧
      ¬Fin15AnchoredAtom3527 chi ∧
      ¬Fin15AnchoredAtom3531 chi ∧
      ¬Fin15AnchoredAtom3535 chi ∧
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
  refine ⟨{1, 5, 8, 9, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask30498
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3376 Fin15AnchoredAtom3378 Fin15AnchoredAtom3379
    Fin15AnchoredAtom3380 Fin15AnchoredAtom3382 Fin15AnchoredAtom3383 Fin15AnchoredAtom3384
    Fin15AnchoredAtom3388 Fin15AnchoredAtom3389 Fin15AnchoredAtom3390 Fin15AnchoredAtom3392
    Fin15AnchoredAtom3393 Fin15AnchoredAtom3394 Fin15AnchoredAtom3398 Fin15AnchoredAtom3399
    Fin15AnchoredAtom3400 Fin15AnchoredAtom3404 Fin15AnchoredAtom3405 Fin15AnchoredAtom3406
    Fin15AnchoredAtom3410 Fin15AnchoredAtom3503 Fin15AnchoredAtom3504 Fin15AnchoredAtom3505
    Fin15AnchoredAtom3509 Fin15AnchoredAtom3510 Fin15AnchoredAtom3511 Fin15AnchoredAtom3515
    Fin15AnchoredAtom3516 Fin15AnchoredAtom3517 Fin15AnchoredAtom3521 Fin15AnchoredAtom3525
    Fin15AnchoredAtom3526 Fin15AnchoredAtom3527 Fin15AnchoredAtom3531 Fin15AnchoredAtom3535
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

theorem fin15Anchored_clause31993 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3411 chi ∧
      ¬Fin15AnchoredAtom3414 chi ∧
      ¬Fin15AnchoredAtom3415 chi ∧
      ¬Fin15AnchoredAtom3416 chi ∧
      ¬Fin15AnchoredAtom3419 chi ∧
      ¬Fin15AnchoredAtom3420 chi ∧
      ¬Fin15AnchoredAtom3421 chi ∧
      ¬Fin15AnchoredAtom3429 chi ∧
      ¬Fin15AnchoredAtom3430 chi ∧
      ¬Fin15AnchoredAtom3431 chi ∧
      ¬Fin15AnchoredAtom3434 chi ∧
      ¬Fin15AnchoredAtom3435 chi ∧
      ¬Fin15AnchoredAtom3436 chi ∧
      ¬Fin15AnchoredAtom3444 chi ∧
      ¬Fin15AnchoredAtom3445 chi ∧
      ¬Fin15AnchoredAtom3446 chi ∧
      ¬Fin15AnchoredAtom3454 chi ∧
      ¬Fin15AnchoredAtom3455 chi ∧
      ¬Fin15AnchoredAtom3456 chi ∧
      ¬Fin15AnchoredAtom3466 chi ∧
      ¬Fin15AnchoredAtom3469 chi ∧
      ¬Fin15AnchoredAtom3470 chi ∧
      ¬Fin15AnchoredAtom3471 chi ∧
      ¬Fin15AnchoredAtom3479 chi ∧
      ¬Fin15AnchoredAtom3480 chi ∧
      ¬Fin15AnchoredAtom3481 chi ∧
      ¬Fin15AnchoredAtom3489 chi ∧
      ¬Fin15AnchoredAtom3490 chi ∧
      ¬Fin15AnchoredAtom3491 chi ∧
      ¬Fin15AnchoredAtom3501 chi ∧
      ¬Fin15AnchoredAtom3509 chi ∧
      ¬Fin15AnchoredAtom3510 chi ∧
      ¬Fin15AnchoredAtom3511 chi ∧
      ¬Fin15AnchoredAtom3521 chi ∧
      ¬Fin15AnchoredAtom3531 chi ∧
      ¬Fin15AnchoredAtom4700 chi ∧
      ¬Fin15AnchoredAtom4701 chi ∧
      ¬Fin15AnchoredAtom4702 chi ∧
      ¬Fin15AnchoredAtom4710 chi ∧
      ¬Fin15AnchoredAtom4711 chi ∧
      ¬Fin15AnchoredAtom4712 chi ∧
      ¬Fin15AnchoredAtom4720 chi ∧
      ¬Fin15AnchoredAtom4721 chi ∧
      ¬Fin15AnchoredAtom4722 chi ∧
      ¬Fin15AnchoredAtom4732 chi ∧
      ¬Fin15AnchoredAtom4740 chi ∧
      ¬Fin15AnchoredAtom4741 chi ∧
      ¬Fin15AnchoredAtom4742 chi ∧
      ¬Fin15AnchoredAtom4752 chi ∧
      ¬Fin15AnchoredAtom4762 chi ∧
      ¬Fin15AnchoredAtom4775 chi ∧
      ¬Fin15AnchoredAtom4776 chi ∧
      ¬Fin15AnchoredAtom4777 chi ∧
      ¬Fin15AnchoredAtom4787 chi ∧
      ¬Fin15AnchoredAtom4797 chi ∧
      ¬Fin15AnchoredAtom4812 chi) := by
  intro hbad
  apply hno
  refine ⟨{1, 6, 7, 8, 9, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask29634
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3411 Fin15AnchoredAtom3414 Fin15AnchoredAtom3415
    Fin15AnchoredAtom3416 Fin15AnchoredAtom3419 Fin15AnchoredAtom3420 Fin15AnchoredAtom3421
    Fin15AnchoredAtom3429 Fin15AnchoredAtom3430 Fin15AnchoredAtom3431 Fin15AnchoredAtom3434
    Fin15AnchoredAtom3435 Fin15AnchoredAtom3436 Fin15AnchoredAtom3444 Fin15AnchoredAtom3445
    Fin15AnchoredAtom3446 Fin15AnchoredAtom3454 Fin15AnchoredAtom3455 Fin15AnchoredAtom3456
    Fin15AnchoredAtom3466 Fin15AnchoredAtom3469 Fin15AnchoredAtom3470 Fin15AnchoredAtom3471
    Fin15AnchoredAtom3479 Fin15AnchoredAtom3480 Fin15AnchoredAtom3481 Fin15AnchoredAtom3489
    Fin15AnchoredAtom3490 Fin15AnchoredAtom3491 Fin15AnchoredAtom3501 Fin15AnchoredAtom3509
    Fin15AnchoredAtom3510 Fin15AnchoredAtom3511 Fin15AnchoredAtom3521 Fin15AnchoredAtom3531
    Fin15AnchoredAtom4700 Fin15AnchoredAtom4701 Fin15AnchoredAtom4702 Fin15AnchoredAtom4710
    Fin15AnchoredAtom4711 Fin15AnchoredAtom4712 Fin15AnchoredAtom4720 Fin15AnchoredAtom4721
    Fin15AnchoredAtom4722 Fin15AnchoredAtom4732 Fin15AnchoredAtom4740 Fin15AnchoredAtom4741
    Fin15AnchoredAtom4742 Fin15AnchoredAtom4752 Fin15AnchoredAtom4762 Fin15AnchoredAtom4775
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

theorem fin15Anchored_clause31994 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3417 chi ∧
      ¬Fin15AnchoredAtom3419 chi ∧
      ¬Fin15AnchoredAtom3420 chi ∧
      ¬Fin15AnchoredAtom3421 chi ∧
      ¬Fin15AnchoredAtom3423 chi ∧
      ¬Fin15AnchoredAtom3424 chi ∧
      ¬Fin15AnchoredAtom3425 chi ∧
      ¬Fin15AnchoredAtom3429 chi ∧
      ¬Fin15AnchoredAtom3430 chi ∧
      ¬Fin15AnchoredAtom3431 chi ∧
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
  refine ⟨{1, 6, 7, 9, 10, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask30402
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3417 Fin15AnchoredAtom3419 Fin15AnchoredAtom3420
    Fin15AnchoredAtom3421 Fin15AnchoredAtom3423 Fin15AnchoredAtom3424 Fin15AnchoredAtom3425
    Fin15AnchoredAtom3429 Fin15AnchoredAtom3430 Fin15AnchoredAtom3431 Fin15AnchoredAtom3448
    Fin15AnchoredAtom3449 Fin15AnchoredAtom3450 Fin15AnchoredAtom3454 Fin15AnchoredAtom3455
    Fin15AnchoredAtom3456 Fin15AnchoredAtom3460 Fin15AnchoredAtom3461 Fin15AnchoredAtom3462
    Fin15AnchoredAtom3466 Fin15AnchoredAtom3483 Fin15AnchoredAtom3484 Fin15AnchoredAtom3485
    Fin15AnchoredAtom3489 Fin15AnchoredAtom3490 Fin15AnchoredAtom3491 Fin15AnchoredAtom3495
    Fin15AnchoredAtom3496 Fin15AnchoredAtom3497 Fin15AnchoredAtom3501 Fin15AnchoredAtom3525
    Fin15AnchoredAtom3526 Fin15AnchoredAtom3527 Fin15AnchoredAtom3531 Fin15AnchoredAtom3535
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

theorem fin15Anchored_clause31995 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3537 chi ∧
      ¬Fin15AnchoredAtom3538 chi ∧
      ¬Fin15AnchoredAtom3540 chi ∧
      ¬Fin15AnchoredAtom3541 chi ∧
      ¬Fin15AnchoredAtom3546 chi ∧
      ¬Fin15AnchoredAtom3548 chi ∧
      ¬Fin15AnchoredAtom3549 chi ∧
      ¬Fin15AnchoredAtom3555 chi ∧
      ¬Fin15AnchoredAtom3556 chi ∧
      ¬Fin15AnchoredAtom3567 chi ∧
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
  refine ⟨{2, 3, 4, 5, 6, 7, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask01788
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3537 Fin15AnchoredAtom3538 Fin15AnchoredAtom3540
    Fin15AnchoredAtom3541 Fin15AnchoredAtom3546 Fin15AnchoredAtom3548 Fin15AnchoredAtom3549
    Fin15AnchoredAtom3555 Fin15AnchoredAtom3556 Fin15AnchoredAtom3567 Fin15AnchoredAtom3582
    Fin15AnchoredAtom3584 Fin15AnchoredAtom3585 Fin15AnchoredAtom3591 Fin15AnchoredAtom3592
    Fin15AnchoredAtom3603 Fin15AnchoredAtom3619 Fin15AnchoredAtom3620 Fin15AnchoredAtom3631
    Fin15AnchoredAtom3652 Fin15AnchoredAtom3702 Fin15AnchoredAtom3704 Fin15AnchoredAtom3705
    Fin15AnchoredAtom3711 Fin15AnchoredAtom3712 Fin15AnchoredAtom3723 Fin15AnchoredAtom3739
    Fin15AnchoredAtom3740 Fin15AnchoredAtom3751 Fin15AnchoredAtom3772 Fin15AnchoredAtom3823
    Fin15AnchoredAtom3824 Fin15AnchoredAtom3835 Fin15AnchoredAtom3856 Fin15AnchoredAtom3912
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

theorem fin15Anchored_clause31996 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3537 chi ∧
      ¬Fin15AnchoredAtom3538 chi ∧
      ¬Fin15AnchoredAtom3540 chi ∧
      ¬Fin15AnchoredAtom3543 chi ∧
      ¬Fin15AnchoredAtom3546 chi ∧
      ¬Fin15AnchoredAtom3548 chi ∧
      ¬Fin15AnchoredAtom3551 chi ∧
      ¬Fin15AnchoredAtom3555 chi ∧
      ¬Fin15AnchoredAtom3558 chi ∧
      ¬Fin15AnchoredAtom3569 chi ∧
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
  refine ⟨{2, 3, 4, 5, 6, 7, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask04860
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3537 Fin15AnchoredAtom3538 Fin15AnchoredAtom3540
    Fin15AnchoredAtom3543 Fin15AnchoredAtom3546 Fin15AnchoredAtom3548 Fin15AnchoredAtom3551
    Fin15AnchoredAtom3555 Fin15AnchoredAtom3558 Fin15AnchoredAtom3569 Fin15AnchoredAtom3582
    Fin15AnchoredAtom3584 Fin15AnchoredAtom3587 Fin15AnchoredAtom3591 Fin15AnchoredAtom3594
    Fin15AnchoredAtom3605 Fin15AnchoredAtom3619 Fin15AnchoredAtom3622 Fin15AnchoredAtom3633
    Fin15AnchoredAtom3654 Fin15AnchoredAtom3702 Fin15AnchoredAtom3704 Fin15AnchoredAtom3707
    Fin15AnchoredAtom3711 Fin15AnchoredAtom3714 Fin15AnchoredAtom3725 Fin15AnchoredAtom3739
    Fin15AnchoredAtom3742 Fin15AnchoredAtom3753 Fin15AnchoredAtom3774 Fin15AnchoredAtom3823
    Fin15AnchoredAtom3826 Fin15AnchoredAtom3837 Fin15AnchoredAtom3858 Fin15AnchoredAtom3914
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

theorem fin15Anchored_clause31997 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3537 chi ∧
      ¬Fin15AnchoredAtom3538 chi ∧
      ¬Fin15AnchoredAtom3540 chi ∧
      ¬Fin15AnchoredAtom3544 chi ∧
      ¬Fin15AnchoredAtom3546 chi ∧
      ¬Fin15AnchoredAtom3548 chi ∧
      ¬Fin15AnchoredAtom3552 chi ∧
      ¬Fin15AnchoredAtom3555 chi ∧
      ¬Fin15AnchoredAtom3559 chi ∧
      ¬Fin15AnchoredAtom3570 chi ∧
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
  refine ⟨{2, 3, 4, 5, 6, 7, 9, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask08956
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3537 Fin15AnchoredAtom3538 Fin15AnchoredAtom3540
    Fin15AnchoredAtom3544 Fin15AnchoredAtom3546 Fin15AnchoredAtom3548 Fin15AnchoredAtom3552
    Fin15AnchoredAtom3555 Fin15AnchoredAtom3559 Fin15AnchoredAtom3570 Fin15AnchoredAtom3582
    Fin15AnchoredAtom3584 Fin15AnchoredAtom3588 Fin15AnchoredAtom3591 Fin15AnchoredAtom3595
    Fin15AnchoredAtom3606 Fin15AnchoredAtom3619 Fin15AnchoredAtom3623 Fin15AnchoredAtom3634
    Fin15AnchoredAtom3655 Fin15AnchoredAtom3702 Fin15AnchoredAtom3704 Fin15AnchoredAtom3708
    Fin15AnchoredAtom3711 Fin15AnchoredAtom3715 Fin15AnchoredAtom3726 Fin15AnchoredAtom3739
    Fin15AnchoredAtom3743 Fin15AnchoredAtom3754 Fin15AnchoredAtom3775 Fin15AnchoredAtom3823
    Fin15AnchoredAtom3827 Fin15AnchoredAtom3838 Fin15AnchoredAtom3859 Fin15AnchoredAtom3915
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

theorem fin15Anchored_clause31998 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3537 chi ∧
      ¬Fin15AnchoredAtom3538 chi ∧
      ¬Fin15AnchoredAtom3540 chi ∧
      ¬Fin15AnchoredAtom3545 chi ∧
      ¬Fin15AnchoredAtom3546 chi ∧
      ¬Fin15AnchoredAtom3548 chi ∧
      ¬Fin15AnchoredAtom3553 chi ∧
      ¬Fin15AnchoredAtom3555 chi ∧
      ¬Fin15AnchoredAtom3560 chi ∧
      ¬Fin15AnchoredAtom3571 chi ∧
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
  refine ⟨{2, 3, 4, 5, 6, 7, 9, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17148
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3537 Fin15AnchoredAtom3538 Fin15AnchoredAtom3540
    Fin15AnchoredAtom3545 Fin15AnchoredAtom3546 Fin15AnchoredAtom3548 Fin15AnchoredAtom3553
    Fin15AnchoredAtom3555 Fin15AnchoredAtom3560 Fin15AnchoredAtom3571 Fin15AnchoredAtom3582
    Fin15AnchoredAtom3584 Fin15AnchoredAtom3589 Fin15AnchoredAtom3591 Fin15AnchoredAtom3596
    Fin15AnchoredAtom3607 Fin15AnchoredAtom3619 Fin15AnchoredAtom3624 Fin15AnchoredAtom3635
    Fin15AnchoredAtom3656 Fin15AnchoredAtom3702 Fin15AnchoredAtom3704 Fin15AnchoredAtom3709
    Fin15AnchoredAtom3711 Fin15AnchoredAtom3716 Fin15AnchoredAtom3727 Fin15AnchoredAtom3739
    Fin15AnchoredAtom3744 Fin15AnchoredAtom3755 Fin15AnchoredAtom3776 Fin15AnchoredAtom3823
    Fin15AnchoredAtom3828 Fin15AnchoredAtom3839 Fin15AnchoredAtom3860 Fin15AnchoredAtom3916
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

theorem fin15Anchored_clause31999 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom3537 chi ∧
      ¬Fin15AnchoredAtom3538 chi ∧
      ¬Fin15AnchoredAtom3541 chi ∧
      ¬Fin15AnchoredAtom3543 chi ∧
      ¬Fin15AnchoredAtom3546 chi ∧
      ¬Fin15AnchoredAtom3549 chi ∧
      ¬Fin15AnchoredAtom3551 chi ∧
      ¬Fin15AnchoredAtom3556 chi ∧
      ¬Fin15AnchoredAtom3558 chi ∧
      ¬Fin15AnchoredAtom3573 chi ∧
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
  refine ⟨{2, 3, 4, 5, 6, 7, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05372
    polygon hsubset hcard
  unfold Fin15AnchoredAtom3537 Fin15AnchoredAtom3538 Fin15AnchoredAtom3541
    Fin15AnchoredAtom3543 Fin15AnchoredAtom3546 Fin15AnchoredAtom3549 Fin15AnchoredAtom3551
    Fin15AnchoredAtom3556 Fin15AnchoredAtom3558 Fin15AnchoredAtom3573 Fin15AnchoredAtom3582
    Fin15AnchoredAtom3585 Fin15AnchoredAtom3587 Fin15AnchoredAtom3592 Fin15AnchoredAtom3594
    Fin15AnchoredAtom3609 Fin15AnchoredAtom3620 Fin15AnchoredAtom3622 Fin15AnchoredAtom3637
    Fin15AnchoredAtom3658 Fin15AnchoredAtom3702 Fin15AnchoredAtom3705 Fin15AnchoredAtom3707
    Fin15AnchoredAtom3712 Fin15AnchoredAtom3714 Fin15AnchoredAtom3729 Fin15AnchoredAtom3740
    Fin15AnchoredAtom3742 Fin15AnchoredAtom3757 Fin15AnchoredAtom3778 Fin15AnchoredAtom3824
    Fin15AnchoredAtom3826 Fin15AnchoredAtom3841 Fin15AnchoredAtom3862 Fin15AnchoredAtom3918
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

end ErdosSzekeres

end
