module

public import ErdosSzekeres.Fin15AnchoredClauseChunk230
public import ErdosSzekeres.Fin15AnchoredClauseChunk231
public import ErdosSzekeres.Fin15AnchoredClauseChunk232

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 117. -/

theorem fin15Anchored_rejectSemanticSegment117
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom2992 chi ∧
      Fin15AnchoredAtom2996 chi ∧
      Fin15AnchoredAtom3000 chi ∧
      Fin15AnchoredAtom3025 chi ∧
      Fin15AnchoredAtom3485 chi ∧
      Fin15AnchoredAtom3980 chi) ∨
      ((Fin15AnchoredAtom2994 chi ∧
      Fin15AnchoredAtom2995 chi ∧
      Fin15AnchoredAtom3004 chi ∧
      Fin15AnchoredAtom3029 chi ∧
      Fin15AnchoredAtom3489 chi ∧
      Fin15AnchoredAtom3984 chi) ∨
      (Fin15AnchoredAtom2994 chi ∧
      Fin15AnchoredAtom2996 chi ∧
      Fin15AnchoredAtom3005 chi ∧
      Fin15AnchoredAtom3030 chi ∧
      Fin15AnchoredAtom3490 chi ∧
      Fin15AnchoredAtom3985 chi))) ∨
      (((Fin15AnchoredAtom2995 chi ∧
      Fin15AnchoredAtom2996 chi ∧
      Fin15AnchoredAtom3006 chi ∧
      Fin15AnchoredAtom3031 chi ∧
      Fin15AnchoredAtom3491 chi ∧
      Fin15AnchoredAtom3986 chi) ∨
      (Fin15AnchoredAtom2998 chi ∧
      Fin15AnchoredAtom2999 chi ∧
      Fin15AnchoredAtom3004 chi ∧
      Fin15AnchoredAtom3035 chi ∧
      Fin15AnchoredAtom3495 chi ∧
      Fin15AnchoredAtom3990 chi)) ∨
      ((Fin15AnchoredAtom2998 chi ∧
      Fin15AnchoredAtom3000 chi ∧
      Fin15AnchoredAtom3005 chi ∧
      Fin15AnchoredAtom3036 chi ∧
      Fin15AnchoredAtom3496 chi ∧
      Fin15AnchoredAtom3991 chi) ∨
      (Fin15AnchoredAtom2999 chi ∧
      Fin15AnchoredAtom3000 chi ∧
      Fin15AnchoredAtom3006 chi ∧
      Fin15AnchoredAtom3037 chi ∧
      Fin15AnchoredAtom3497 chi ∧
      Fin15AnchoredAtom3992 chi)))) ∨
      ((((Fin15AnchoredAtom3004 chi ∧
      Fin15AnchoredAtom3005 chi ∧
      Fin15AnchoredAtom3006 chi ∧
      Fin15AnchoredAtom3041 chi ∧
      Fin15AnchoredAtom3501 chi ∧
      Fin15AnchoredAtom3996 chi) ∨
      (Fin15AnchoredAtom3022 chi ∧
      Fin15AnchoredAtom3023 chi ∧
      Fin15AnchoredAtom3026 chi ∧
      Fin15AnchoredAtom3032 chi ∧
      Fin15AnchoredAtom3522 chi ∧
      Fin15AnchoredAtom4017 chi)) ∨
      ((Fin15AnchoredAtom3023 chi ∧
      Fin15AnchoredAtom3024 chi ∧
      Fin15AnchoredAtom3029 chi ∧
      Fin15AnchoredAtom3035 chi ∧
      Fin15AnchoredAtom3525 chi ∧
      Fin15AnchoredAtom4020 chi) ∨
      (Fin15AnchoredAtom3023 chi ∧
      Fin15AnchoredAtom3025 chi ∧
      Fin15AnchoredAtom3030 chi ∧
      Fin15AnchoredAtom3036 chi ∧
      Fin15AnchoredAtom3526 chi ∧
      Fin15AnchoredAtom4021 chi))) ∨
      (((Fin15AnchoredAtom3024 chi ∧
      Fin15AnchoredAtom3025 chi ∧
      Fin15AnchoredAtom3031 chi ∧
      Fin15AnchoredAtom3037 chi ∧
      Fin15AnchoredAtom3527 chi ∧
      Fin15AnchoredAtom4022 chi) ∨
      (Fin15AnchoredAtom3029 chi ∧
      Fin15AnchoredAtom3030 chi ∧
      Fin15AnchoredAtom3031 chi ∧
      Fin15AnchoredAtom3041 chi ∧
      Fin15AnchoredAtom3531 chi ∧
      Fin15AnchoredAtom4026 chi)) ∨
      ((Fin15AnchoredAtom3035 chi ∧
      Fin15AnchoredAtom3036 chi ∧
      Fin15AnchoredAtom3037 chi ∧
      Fin15AnchoredAtom3041 chi ∧
      Fin15AnchoredAtom3535 chi ∧
      Fin15AnchoredAtom4030 chi) ∨
      (Fin15AnchoredAtom3042 chi ∧
      Fin15AnchoredAtom3043 chi ∧
      Fin15AnchoredAtom3051 chi ∧
      Fin15AnchoredAtom3087 chi ∧
      Fin15AnchoredAtom3207 chi ∧
      Fin15AnchoredAtom4032 chi))))) ∨
      (((((Fin15AnchoredAtom3042 chi ∧
      Fin15AnchoredAtom3044 chi ∧
      Fin15AnchoredAtom3052 chi ∧
      Fin15AnchoredAtom3088 chi ∧
      Fin15AnchoredAtom3208 chi ∧
      Fin15AnchoredAtom4033 chi) ∨
      (Fin15AnchoredAtom3042 chi ∧
      Fin15AnchoredAtom3045 chi ∧
      Fin15AnchoredAtom3053 chi ∧
      Fin15AnchoredAtom3089 chi ∧
      Fin15AnchoredAtom3209 chi ∧
      Fin15AnchoredAtom4034 chi)) ∨
      ((Fin15AnchoredAtom3042 chi ∧
      Fin15AnchoredAtom3046 chi ∧
      Fin15AnchoredAtom3054 chi ∧
      Fin15AnchoredAtom3090 chi ∧
      Fin15AnchoredAtom3210 chi ∧
      Fin15AnchoredAtom4035 chi) ∨
      (Fin15AnchoredAtom3042 chi ∧
      Fin15AnchoredAtom3048 chi ∧
      Fin15AnchoredAtom3056 chi ∧
      Fin15AnchoredAtom3092 chi ∧
      Fin15AnchoredAtom3212 chi ∧
      Fin15AnchoredAtom4037 chi))) ∨
      (((Fin15AnchoredAtom3042 chi ∧
      Fin15AnchoredAtom3049 chi ∧
      Fin15AnchoredAtom3057 chi ∧
      Fin15AnchoredAtom3093 chi ∧
      Fin15AnchoredAtom3213 chi ∧
      Fin15AnchoredAtom4038 chi) ∨
      (Fin15AnchoredAtom3042 chi ∧
      Fin15AnchoredAtom3050 chi ∧
      Fin15AnchoredAtom3058 chi ∧
      Fin15AnchoredAtom3094 chi ∧
      Fin15AnchoredAtom3214 chi ∧
      Fin15AnchoredAtom4039 chi)) ∨
      ((Fin15AnchoredAtom3043 chi ∧
      Fin15AnchoredAtom3044 chi ∧
      Fin15AnchoredAtom3059 chi ∧
      Fin15AnchoredAtom3095 chi ∧
      Fin15AnchoredAtom3215 chi ∧
      Fin15AnchoredAtom4040 chi) ∨
      (Fin15AnchoredAtom3043 chi ∧
      Fin15AnchoredAtom3045 chi ∧
      Fin15AnchoredAtom3060 chi ∧
      Fin15AnchoredAtom3096 chi ∧
      Fin15AnchoredAtom3216 chi ∧
      Fin15AnchoredAtom4041 chi)))) ∨
      ((((Fin15AnchoredAtom3043 chi ∧
      Fin15AnchoredAtom3046 chi ∧
      Fin15AnchoredAtom3061 chi ∧
      Fin15AnchoredAtom3097 chi ∧
      Fin15AnchoredAtom3217 chi ∧
      Fin15AnchoredAtom4042 chi) ∨
      (Fin15AnchoredAtom3043 chi ∧
      Fin15AnchoredAtom3048 chi ∧
      Fin15AnchoredAtom3063 chi ∧
      Fin15AnchoredAtom3099 chi ∧
      Fin15AnchoredAtom3219 chi ∧
      Fin15AnchoredAtom4044 chi)) ∨
      ((Fin15AnchoredAtom3043 chi ∧
      Fin15AnchoredAtom3049 chi ∧
      Fin15AnchoredAtom3064 chi ∧
      Fin15AnchoredAtom3100 chi ∧
      Fin15AnchoredAtom3220 chi ∧
      Fin15AnchoredAtom4045 chi) ∨
      (Fin15AnchoredAtom3043 chi ∧
      Fin15AnchoredAtom3050 chi ∧
      Fin15AnchoredAtom3065 chi ∧
      Fin15AnchoredAtom3101 chi ∧
      Fin15AnchoredAtom3221 chi ∧
      Fin15AnchoredAtom4046 chi))) ∨
      (((Fin15AnchoredAtom3044 chi ∧
      Fin15AnchoredAtom3046 chi ∧
      Fin15AnchoredAtom3067 chi ∧
      Fin15AnchoredAtom3103 chi ∧
      Fin15AnchoredAtom3223 chi ∧
      Fin15AnchoredAtom4048 chi) ∨
      (Fin15AnchoredAtom3044 chi ∧
      Fin15AnchoredAtom3048 chi ∧
      Fin15AnchoredAtom3069 chi ∧
      Fin15AnchoredAtom3105 chi ∧
      Fin15AnchoredAtom3225 chi ∧
      Fin15AnchoredAtom4050 chi)) ∨
      ((Fin15AnchoredAtom3044 chi ∧
      Fin15AnchoredAtom3049 chi ∧
      Fin15AnchoredAtom3070 chi ∧
      Fin15AnchoredAtom3106 chi ∧
      Fin15AnchoredAtom3226 chi ∧
      Fin15AnchoredAtom4051 chi) ∨
      (Fin15AnchoredAtom3044 chi ∧
      Fin15AnchoredAtom3050 chi ∧
      Fin15AnchoredAtom3071 chi ∧
      Fin15AnchoredAtom3107 chi ∧
      Fin15AnchoredAtom3227 chi ∧
      Fin15AnchoredAtom4052 chi)))))) ∨
      ((((((Fin15AnchoredAtom3045 chi ∧
      Fin15AnchoredAtom3046 chi ∧
      Fin15AnchoredAtom3072 chi ∧
      Fin15AnchoredAtom3108 chi ∧
      Fin15AnchoredAtom3228 chi ∧
      Fin15AnchoredAtom4053 chi) ∨
      (Fin15AnchoredAtom3045 chi ∧
      Fin15AnchoredAtom3048 chi ∧
      Fin15AnchoredAtom3074 chi ∧
      Fin15AnchoredAtom3110 chi ∧
      Fin15AnchoredAtom3230 chi ∧
      Fin15AnchoredAtom4055 chi)) ∨
      ((Fin15AnchoredAtom3045 chi ∧
      Fin15AnchoredAtom3049 chi ∧
      Fin15AnchoredAtom3075 chi ∧
      Fin15AnchoredAtom3111 chi ∧
      Fin15AnchoredAtom3231 chi ∧
      Fin15AnchoredAtom4056 chi) ∨
      (Fin15AnchoredAtom3045 chi ∧
      Fin15AnchoredAtom3050 chi ∧
      Fin15AnchoredAtom3076 chi ∧
      Fin15AnchoredAtom3112 chi ∧
      Fin15AnchoredAtom3232 chi ∧
      Fin15AnchoredAtom4057 chi))) ∨
      (((Fin15AnchoredAtom3046 chi ∧
      Fin15AnchoredAtom3048 chi ∧
      Fin15AnchoredAtom3078 chi ∧
      Fin15AnchoredAtom3114 chi ∧
      Fin15AnchoredAtom3234 chi ∧
      Fin15AnchoredAtom4059 chi) ∨
      (Fin15AnchoredAtom3046 chi ∧
      Fin15AnchoredAtom3049 chi ∧
      Fin15AnchoredAtom3079 chi ∧
      Fin15AnchoredAtom3115 chi ∧
      Fin15AnchoredAtom3235 chi ∧
      Fin15AnchoredAtom4060 chi)) ∨
      ((Fin15AnchoredAtom3046 chi ∧
      Fin15AnchoredAtom3050 chi ∧
      Fin15AnchoredAtom3080 chi ∧
      Fin15AnchoredAtom3116 chi ∧
      Fin15AnchoredAtom3236 chi ∧
      Fin15AnchoredAtom4061 chi) ∨
      (Fin15AnchoredAtom3048 chi ∧
      Fin15AnchoredAtom3049 chi ∧
      Fin15AnchoredAtom3084 chi ∧
      Fin15AnchoredAtom3120 chi ∧
      Fin15AnchoredAtom3240 chi ∧
      Fin15AnchoredAtom4065 chi)))) ∨
      ((((Fin15AnchoredAtom3048 chi ∧
      Fin15AnchoredAtom3050 chi ∧
      Fin15AnchoredAtom3085 chi ∧
      Fin15AnchoredAtom3121 chi ∧
      Fin15AnchoredAtom3241 chi ∧
      Fin15AnchoredAtom4066 chi) ∨
      (Fin15AnchoredAtom3049 chi ∧
      Fin15AnchoredAtom3050 chi ∧
      Fin15AnchoredAtom3086 chi ∧
      Fin15AnchoredAtom3122 chi ∧
      Fin15AnchoredAtom3242 chi ∧
      Fin15AnchoredAtom4067 chi)) ∨
      ((Fin15AnchoredAtom3051 chi ∧
      Fin15AnchoredAtom3052 chi ∧
      Fin15AnchoredAtom3059 chi ∧
      Fin15AnchoredAtom3123 chi ∧
      Fin15AnchoredAtom3243 chi ∧
      Fin15AnchoredAtom4068 chi) ∨
      (Fin15AnchoredAtom3051 chi ∧
      Fin15AnchoredAtom3053 chi ∧
      Fin15AnchoredAtom3060 chi ∧
      Fin15AnchoredAtom3124 chi ∧
      Fin15AnchoredAtom3244 chi ∧
      Fin15AnchoredAtom4069 chi))) ∨
      (((Fin15AnchoredAtom3051 chi ∧
      Fin15AnchoredAtom3054 chi ∧
      Fin15AnchoredAtom3061 chi ∧
      Fin15AnchoredAtom3125 chi ∧
      Fin15AnchoredAtom3245 chi ∧
      Fin15AnchoredAtom4070 chi) ∨
      (Fin15AnchoredAtom3051 chi ∧
      Fin15AnchoredAtom3056 chi ∧
      Fin15AnchoredAtom3063 chi ∧
      Fin15AnchoredAtom3127 chi ∧
      Fin15AnchoredAtom3247 chi ∧
      Fin15AnchoredAtom4072 chi)) ∨
      ((Fin15AnchoredAtom3051 chi ∧
      Fin15AnchoredAtom3057 chi ∧
      Fin15AnchoredAtom3064 chi ∧
      Fin15AnchoredAtom3128 chi ∧
      Fin15AnchoredAtom3248 chi ∧
      Fin15AnchoredAtom4073 chi) ∨
      (Fin15AnchoredAtom3051 chi ∧
      Fin15AnchoredAtom3058 chi ∧
      Fin15AnchoredAtom3065 chi ∧
      Fin15AnchoredAtom3129 chi ∧
      Fin15AnchoredAtom3249 chi ∧
      Fin15AnchoredAtom4074 chi))))) ∨
      (((((Fin15AnchoredAtom3052 chi ∧
      Fin15AnchoredAtom3053 chi ∧
      Fin15AnchoredAtom3066 chi ∧
      Fin15AnchoredAtom3130 chi ∧
      Fin15AnchoredAtom3250 chi ∧
      Fin15AnchoredAtom4075 chi) ∨
      (Fin15AnchoredAtom3052 chi ∧
      Fin15AnchoredAtom3054 chi ∧
      Fin15AnchoredAtom3067 chi ∧
      Fin15AnchoredAtom3131 chi ∧
      Fin15AnchoredAtom3251 chi ∧
      Fin15AnchoredAtom4076 chi)) ∨
      ((Fin15AnchoredAtom3052 chi ∧
      Fin15AnchoredAtom3057 chi ∧
      Fin15AnchoredAtom3070 chi ∧
      Fin15AnchoredAtom3134 chi ∧
      Fin15AnchoredAtom3254 chi ∧
      Fin15AnchoredAtom4079 chi) ∨
      (Fin15AnchoredAtom3053 chi ∧
      Fin15AnchoredAtom3054 chi ∧
      Fin15AnchoredAtom3072 chi ∧
      Fin15AnchoredAtom3136 chi ∧
      Fin15AnchoredAtom3256 chi ∧
      Fin15AnchoredAtom4081 chi))) ∨
      (((Fin15AnchoredAtom3053 chi ∧
      Fin15AnchoredAtom3056 chi ∧
      Fin15AnchoredAtom3074 chi ∧
      Fin15AnchoredAtom3138 chi ∧
      Fin15AnchoredAtom3258 chi ∧
      Fin15AnchoredAtom4083 chi) ∨
      (Fin15AnchoredAtom3053 chi ∧
      Fin15AnchoredAtom3057 chi ∧
      Fin15AnchoredAtom3075 chi ∧
      Fin15AnchoredAtom3139 chi ∧
      Fin15AnchoredAtom3259 chi ∧
      Fin15AnchoredAtom4084 chi)) ∨
      ((Fin15AnchoredAtom3053 chi ∧
      Fin15AnchoredAtom3058 chi ∧
      Fin15AnchoredAtom3076 chi ∧
      Fin15AnchoredAtom3140 chi ∧
      Fin15AnchoredAtom3260 chi ∧
      Fin15AnchoredAtom4085 chi) ∨
      (Fin15AnchoredAtom3054 chi ∧
      Fin15AnchoredAtom3056 chi ∧
      Fin15AnchoredAtom3078 chi ∧
      Fin15AnchoredAtom3142 chi ∧
      Fin15AnchoredAtom3262 chi ∧
      Fin15AnchoredAtom4087 chi)))) ∨
      ((((Fin15AnchoredAtom3054 chi ∧
      Fin15AnchoredAtom3057 chi ∧
      Fin15AnchoredAtom3079 chi ∧
      Fin15AnchoredAtom3143 chi ∧
      Fin15AnchoredAtom3263 chi ∧
      Fin15AnchoredAtom4088 chi) ∨
      (Fin15AnchoredAtom3054 chi ∧
      Fin15AnchoredAtom3058 chi ∧
      Fin15AnchoredAtom3080 chi ∧
      Fin15AnchoredAtom3144 chi ∧
      Fin15AnchoredAtom3264 chi ∧
      Fin15AnchoredAtom4089 chi)) ∨
      ((Fin15AnchoredAtom3056 chi ∧
      Fin15AnchoredAtom3057 chi ∧
      Fin15AnchoredAtom3084 chi ∧
      Fin15AnchoredAtom3148 chi ∧
      Fin15AnchoredAtom3268 chi ∧
      Fin15AnchoredAtom4093 chi) ∨
      (Fin15AnchoredAtom3056 chi ∧
      Fin15AnchoredAtom3058 chi ∧
      Fin15AnchoredAtom3085 chi ∧
      Fin15AnchoredAtom3149 chi ∧
      Fin15AnchoredAtom3269 chi ∧
      Fin15AnchoredAtom4094 chi))) ∨
      (((Fin15AnchoredAtom3057 chi ∧
      Fin15AnchoredAtom3058 chi ∧
      Fin15AnchoredAtom3086 chi ∧
      Fin15AnchoredAtom3150 chi ∧
      Fin15AnchoredAtom3270 chi ∧
      Fin15AnchoredAtom4095 chi) ∨
      (Fin15AnchoredAtom3059 chi ∧
      Fin15AnchoredAtom3060 chi ∧
      Fin15AnchoredAtom3066 chi ∧
      Fin15AnchoredAtom3151 chi ∧
      Fin15AnchoredAtom3271 chi ∧
      Fin15AnchoredAtom4096 chi)) ∨
      ((Fin15AnchoredAtom3059 chi ∧
      Fin15AnchoredAtom3061 chi ∧
      Fin15AnchoredAtom3067 chi ∧
      Fin15AnchoredAtom3152 chi ∧
      Fin15AnchoredAtom3272 chi ∧
      Fin15AnchoredAtom4097 chi) ∨
      (Fin15AnchoredAtom3059 chi ∧
      Fin15AnchoredAtom3063 chi ∧
      Fin15AnchoredAtom3069 chi ∧
      Fin15AnchoredAtom3154 chi ∧
      Fin15AnchoredAtom3274 chi ∧
      Fin15AnchoredAtom4099 chi))))))) ∨
      ((((((Fin15AnchoredAtom3059 chi ∧
      Fin15AnchoredAtom3064 chi ∧
      Fin15AnchoredAtom3070 chi ∧
      Fin15AnchoredAtom3155 chi ∧
      Fin15AnchoredAtom3275 chi ∧
      Fin15AnchoredAtom4100 chi) ∨
      ((Fin15AnchoredAtom3060 chi ∧
      Fin15AnchoredAtom3061 chi ∧
      Fin15AnchoredAtom3072 chi ∧
      Fin15AnchoredAtom3157 chi ∧
      Fin15AnchoredAtom3277 chi ∧
      Fin15AnchoredAtom4102 chi) ∨
      (Fin15AnchoredAtom3060 chi ∧
      Fin15AnchoredAtom3063 chi ∧
      Fin15AnchoredAtom3074 chi ∧
      Fin15AnchoredAtom3159 chi ∧
      Fin15AnchoredAtom3279 chi ∧
      Fin15AnchoredAtom4104 chi))) ∨
      (((Fin15AnchoredAtom3060 chi ∧
      Fin15AnchoredAtom3064 chi ∧
      Fin15AnchoredAtom3075 chi ∧
      Fin15AnchoredAtom3160 chi ∧
      Fin15AnchoredAtom3280 chi ∧
      Fin15AnchoredAtom4105 chi) ∨
      (Fin15AnchoredAtom3060 chi ∧
      Fin15AnchoredAtom3065 chi ∧
      Fin15AnchoredAtom3076 chi ∧
      Fin15AnchoredAtom3161 chi ∧
      Fin15AnchoredAtom3281 chi ∧
      Fin15AnchoredAtom4106 chi)) ∨
      ((Fin15AnchoredAtom3061 chi ∧
      Fin15AnchoredAtom3063 chi ∧
      Fin15AnchoredAtom3078 chi ∧
      Fin15AnchoredAtom3163 chi ∧
      Fin15AnchoredAtom3283 chi ∧
      Fin15AnchoredAtom4108 chi) ∨
      (Fin15AnchoredAtom3061 chi ∧
      Fin15AnchoredAtom3064 chi ∧
      Fin15AnchoredAtom3079 chi ∧
      Fin15AnchoredAtom3164 chi ∧
      Fin15AnchoredAtom3284 chi ∧
      Fin15AnchoredAtom4109 chi)))) ∨
      ((((Fin15AnchoredAtom3061 chi ∧
      Fin15AnchoredAtom3065 chi ∧
      Fin15AnchoredAtom3080 chi ∧
      Fin15AnchoredAtom3165 chi ∧
      Fin15AnchoredAtom3285 chi ∧
      Fin15AnchoredAtom4110 chi) ∨
      (Fin15AnchoredAtom3062 chi ∧
      Fin15AnchoredAtom3063 chi ∧
      Fin15AnchoredAtom3081 chi ∧
      Fin15AnchoredAtom3166 chi ∧
      Fin15AnchoredAtom3286 chi ∧
      Fin15AnchoredAtom4111 chi)) ∨
      ((Fin15AnchoredAtom3063 chi ∧
      Fin15AnchoredAtom3064 chi ∧
      Fin15AnchoredAtom3084 chi ∧
      Fin15AnchoredAtom3169 chi ∧
      Fin15AnchoredAtom3289 chi ∧
      Fin15AnchoredAtom4114 chi) ∨
      (Fin15AnchoredAtom3063 chi ∧
      Fin15AnchoredAtom3065 chi ∧
      Fin15AnchoredAtom3085 chi ∧
      Fin15AnchoredAtom3170 chi ∧
      Fin15AnchoredAtom3290 chi ∧
      Fin15AnchoredAtom4115 chi))) ∨
      (((Fin15AnchoredAtom3064 chi ∧
      Fin15AnchoredAtom3065 chi ∧
      Fin15AnchoredAtom3086 chi ∧
      Fin15AnchoredAtom3171 chi ∧
      Fin15AnchoredAtom3291 chi ∧
      Fin15AnchoredAtom4116 chi) ∨
      (Fin15AnchoredAtom3066 chi ∧
      Fin15AnchoredAtom3067 chi ∧
      Fin15AnchoredAtom3072 chi ∧
      Fin15AnchoredAtom3172 chi ∧
      Fin15AnchoredAtom3292 chi ∧
      Fin15AnchoredAtom4117 chi)) ∨
      ((Fin15AnchoredAtom3066 chi ∧
      Fin15AnchoredAtom3070 chi ∧
      Fin15AnchoredAtom3075 chi ∧
      Fin15AnchoredAtom3175 chi ∧
      Fin15AnchoredAtom3295 chi ∧
      Fin15AnchoredAtom4120 chi) ∨
      (Fin15AnchoredAtom3067 chi ∧
      Fin15AnchoredAtom3069 chi ∧
      Fin15AnchoredAtom3078 chi ∧
      Fin15AnchoredAtom3178 chi ∧
      Fin15AnchoredAtom3298 chi ∧
      Fin15AnchoredAtom4123 chi))))) ∨
      (((((Fin15AnchoredAtom3067 chi ∧
      Fin15AnchoredAtom3070 chi ∧
      Fin15AnchoredAtom3079 chi ∧
      Fin15AnchoredAtom3179 chi ∧
      Fin15AnchoredAtom3299 chi ∧
      Fin15AnchoredAtom4124 chi) ∨
      (Fin15AnchoredAtom3069 chi ∧
      Fin15AnchoredAtom3070 chi ∧
      Fin15AnchoredAtom3084 chi ∧
      Fin15AnchoredAtom3184 chi ∧
      Fin15AnchoredAtom3304 chi ∧
      Fin15AnchoredAtom4129 chi)) ∨
      ((Fin15AnchoredAtom3069 chi ∧
      Fin15AnchoredAtom3071 chi ∧
      Fin15AnchoredAtom3085 chi ∧
      Fin15AnchoredAtom3185 chi ∧
      Fin15AnchoredAtom3305 chi ∧
      Fin15AnchoredAtom4130 chi) ∨
      (Fin15AnchoredAtom3070 chi ∧
      Fin15AnchoredAtom3071 chi ∧
      Fin15AnchoredAtom3086 chi ∧
      Fin15AnchoredAtom3186 chi ∧
      Fin15AnchoredAtom3306 chi ∧
      Fin15AnchoredAtom4131 chi))) ∨
      (((Fin15AnchoredAtom3072 chi ∧
      Fin15AnchoredAtom3074 chi ∧
      Fin15AnchoredAtom3078 chi ∧
      Fin15AnchoredAtom3188 chi ∧
      Fin15AnchoredAtom3308 chi ∧
      Fin15AnchoredAtom4133 chi) ∨
      (Fin15AnchoredAtom3072 chi ∧
      Fin15AnchoredAtom3075 chi ∧
      Fin15AnchoredAtom3079 chi ∧
      Fin15AnchoredAtom3189 chi ∧
      Fin15AnchoredAtom3309 chi ∧
      Fin15AnchoredAtom4134 chi)) ∨
      ((Fin15AnchoredAtom3072 chi ∧
      Fin15AnchoredAtom3076 chi ∧
      Fin15AnchoredAtom3080 chi ∧
      Fin15AnchoredAtom3190 chi ∧
      Fin15AnchoredAtom3310 chi ∧
      Fin15AnchoredAtom4135 chi) ∨
      (Fin15AnchoredAtom3073 chi ∧
      Fin15AnchoredAtom3074 chi ∧
      Fin15AnchoredAtom3081 chi ∧
      Fin15AnchoredAtom3191 chi ∧
      Fin15AnchoredAtom3311 chi ∧
      Fin15AnchoredAtom4136 chi)))) ∨
      ((((Fin15AnchoredAtom3074 chi ∧
      Fin15AnchoredAtom3075 chi ∧
      Fin15AnchoredAtom3084 chi ∧
      Fin15AnchoredAtom3194 chi ∧
      Fin15AnchoredAtom3314 chi ∧
      Fin15AnchoredAtom4139 chi) ∨
      (Fin15AnchoredAtom3074 chi ∧
      Fin15AnchoredAtom3076 chi ∧
      Fin15AnchoredAtom3085 chi ∧
      Fin15AnchoredAtom3195 chi ∧
      Fin15AnchoredAtom3315 chi ∧
      Fin15AnchoredAtom4140 chi)) ∨
      ((Fin15AnchoredAtom3075 chi ∧
      Fin15AnchoredAtom3076 chi ∧
      Fin15AnchoredAtom3086 chi ∧
      Fin15AnchoredAtom3196 chi ∧
      Fin15AnchoredAtom3316 chi ∧
      Fin15AnchoredAtom4141 chi) ∨
      (Fin15AnchoredAtom3078 chi ∧
      Fin15AnchoredAtom3079 chi ∧
      Fin15AnchoredAtom3084 chi ∧
      Fin15AnchoredAtom3200 chi ∧
      Fin15AnchoredAtom3320 chi ∧
      Fin15AnchoredAtom4145 chi))) ∨
      (((Fin15AnchoredAtom3078 chi ∧
      Fin15AnchoredAtom3080 chi ∧
      Fin15AnchoredAtom3085 chi ∧
      Fin15AnchoredAtom3201 chi ∧
      Fin15AnchoredAtom3321 chi ∧
      Fin15AnchoredAtom4146 chi) ∨
      (Fin15AnchoredAtom3079 chi ∧
      Fin15AnchoredAtom3080 chi ∧
      Fin15AnchoredAtom3086 chi ∧
      Fin15AnchoredAtom3202 chi ∧
      Fin15AnchoredAtom3322 chi ∧
      Fin15AnchoredAtom4147 chi)) ∨
      ((Fin15AnchoredAtom3084 chi ∧
      Fin15AnchoredAtom3085 chi ∧
      Fin15AnchoredAtom3086 chi ∧
      Fin15AnchoredAtom3206 chi ∧
      Fin15AnchoredAtom3326 chi ∧
      Fin15AnchoredAtom4151 chi) ∨
      (Fin15AnchoredAtom3087 chi ∧
      Fin15AnchoredAtom3088 chi ∧
      Fin15AnchoredAtom3095 chi ∧
      Fin15AnchoredAtom3123 chi ∧
      Fin15AnchoredAtom3327 chi ∧
      Fin15AnchoredAtom4152 chi)))))) ∨
      ((((((Fin15AnchoredAtom3087 chi ∧
      Fin15AnchoredAtom3089 chi ∧
      Fin15AnchoredAtom3096 chi ∧
      Fin15AnchoredAtom3124 chi ∧
      Fin15AnchoredAtom3328 chi ∧
      Fin15AnchoredAtom4153 chi) ∨
      (Fin15AnchoredAtom3087 chi ∧
      Fin15AnchoredAtom3090 chi ∧
      Fin15AnchoredAtom3097 chi ∧
      Fin15AnchoredAtom3125 chi ∧
      Fin15AnchoredAtom3329 chi ∧
      Fin15AnchoredAtom4154 chi)) ∨
      ((Fin15AnchoredAtom3087 chi ∧
      Fin15AnchoredAtom3092 chi ∧
      Fin15AnchoredAtom3099 chi ∧
      Fin15AnchoredAtom3127 chi ∧
      Fin15AnchoredAtom3331 chi ∧
      Fin15AnchoredAtom4156 chi) ∨
      (Fin15AnchoredAtom3087 chi ∧
      Fin15AnchoredAtom3093 chi ∧
      Fin15AnchoredAtom3100 chi ∧
      Fin15AnchoredAtom3128 chi ∧
      Fin15AnchoredAtom3332 chi ∧
      Fin15AnchoredAtom4157 chi))) ∨
      (((Fin15AnchoredAtom3087 chi ∧
      Fin15AnchoredAtom3094 chi ∧
      Fin15AnchoredAtom3101 chi ∧
      Fin15AnchoredAtom3129 chi ∧
      Fin15AnchoredAtom3333 chi ∧
      Fin15AnchoredAtom4158 chi) ∨
      (Fin15AnchoredAtom3088 chi ∧
      Fin15AnchoredAtom3089 chi ∧
      Fin15AnchoredAtom3102 chi ∧
      Fin15AnchoredAtom3130 chi ∧
      Fin15AnchoredAtom3334 chi ∧
      Fin15AnchoredAtom4159 chi)) ∨
      ((Fin15AnchoredAtom3088 chi ∧
      Fin15AnchoredAtom3093 chi ∧
      Fin15AnchoredAtom3106 chi ∧
      Fin15AnchoredAtom3134 chi ∧
      Fin15AnchoredAtom3338 chi ∧
      Fin15AnchoredAtom4163 chi) ∨
      (Fin15AnchoredAtom3089 chi ∧
      Fin15AnchoredAtom3090 chi ∧
      Fin15AnchoredAtom3108 chi ∧
      Fin15AnchoredAtom3136 chi ∧
      Fin15AnchoredAtom3340 chi ∧
      Fin15AnchoredAtom4165 chi)))) ∨
      ((((Fin15AnchoredAtom3089 chi ∧
      Fin15AnchoredAtom3092 chi ∧
      Fin15AnchoredAtom3110 chi ∧
      Fin15AnchoredAtom3138 chi ∧
      Fin15AnchoredAtom3342 chi ∧
      Fin15AnchoredAtom4167 chi) ∨
      (Fin15AnchoredAtom3089 chi ∧
      Fin15AnchoredAtom3093 chi ∧
      Fin15AnchoredAtom3111 chi ∧
      Fin15AnchoredAtom3139 chi ∧
      Fin15AnchoredAtom3343 chi ∧
      Fin15AnchoredAtom4168 chi)) ∨
      ((Fin15AnchoredAtom3089 chi ∧
      Fin15AnchoredAtom3094 chi ∧
      Fin15AnchoredAtom3112 chi ∧
      Fin15AnchoredAtom3140 chi ∧
      Fin15AnchoredAtom3344 chi ∧
      Fin15AnchoredAtom4169 chi) ∨
      (Fin15AnchoredAtom3090 chi ∧
      Fin15AnchoredAtom3092 chi ∧
      Fin15AnchoredAtom3114 chi ∧
      Fin15AnchoredAtom3142 chi ∧
      Fin15AnchoredAtom3346 chi ∧
      Fin15AnchoredAtom4171 chi))) ∨
      (((Fin15AnchoredAtom3090 chi ∧
      Fin15AnchoredAtom3093 chi ∧
      Fin15AnchoredAtom3115 chi ∧
      Fin15AnchoredAtom3143 chi ∧
      Fin15AnchoredAtom3347 chi ∧
      Fin15AnchoredAtom4172 chi) ∨
      (Fin15AnchoredAtom3090 chi ∧
      Fin15AnchoredAtom3094 chi ∧
      Fin15AnchoredAtom3116 chi ∧
      Fin15AnchoredAtom3144 chi ∧
      Fin15AnchoredAtom3348 chi ∧
      Fin15AnchoredAtom4173 chi)) ∨
      ((Fin15AnchoredAtom3091 chi ∧
      Fin15AnchoredAtom3092 chi ∧
      Fin15AnchoredAtom3117 chi ∧
      Fin15AnchoredAtom3145 chi ∧
      Fin15AnchoredAtom3349 chi ∧
      Fin15AnchoredAtom4174 chi) ∨
      (Fin15AnchoredAtom3092 chi ∧
      Fin15AnchoredAtom3093 chi ∧
      Fin15AnchoredAtom3120 chi ∧
      Fin15AnchoredAtom3148 chi ∧
      Fin15AnchoredAtom3352 chi ∧
      Fin15AnchoredAtom4177 chi))))) ∨
      (((((Fin15AnchoredAtom3092 chi ∧
      Fin15AnchoredAtom3094 chi ∧
      Fin15AnchoredAtom3121 chi ∧
      Fin15AnchoredAtom3149 chi ∧
      Fin15AnchoredAtom3353 chi ∧
      Fin15AnchoredAtom4178 chi) ∨
      (Fin15AnchoredAtom3093 chi ∧
      Fin15AnchoredAtom3094 chi ∧
      Fin15AnchoredAtom3122 chi ∧
      Fin15AnchoredAtom3150 chi ∧
      Fin15AnchoredAtom3354 chi ∧
      Fin15AnchoredAtom4179 chi)) ∨
      ((Fin15AnchoredAtom3095 chi ∧
      Fin15AnchoredAtom3096 chi ∧
      Fin15AnchoredAtom3102 chi ∧
      Fin15AnchoredAtom3151 chi ∧
      Fin15AnchoredAtom3355 chi ∧
      Fin15AnchoredAtom4180 chi) ∨
      (Fin15AnchoredAtom3095 chi ∧
      Fin15AnchoredAtom3097 chi ∧
      Fin15AnchoredAtom3103 chi ∧
      Fin15AnchoredAtom3152 chi ∧
      Fin15AnchoredAtom3356 chi ∧
      Fin15AnchoredAtom4181 chi))) ∨
      (((Fin15AnchoredAtom3095 chi ∧
      Fin15AnchoredAtom3099 chi ∧
      Fin15AnchoredAtom3105 chi ∧
      Fin15AnchoredAtom3154 chi ∧
      Fin15AnchoredAtom3358 chi ∧
      Fin15AnchoredAtom4183 chi) ∨
      (Fin15AnchoredAtom3095 chi ∧
      Fin15AnchoredAtom3100 chi ∧
      Fin15AnchoredAtom3106 chi ∧
      Fin15AnchoredAtom3155 chi ∧
      Fin15AnchoredAtom3359 chi ∧
      Fin15AnchoredAtom4184 chi)) ∨
      ((Fin15AnchoredAtom3096 chi ∧
      Fin15AnchoredAtom3097 chi ∧
      Fin15AnchoredAtom3108 chi ∧
      Fin15AnchoredAtom3157 chi ∧
      Fin15AnchoredAtom3361 chi ∧
      Fin15AnchoredAtom4186 chi) ∨
      (Fin15AnchoredAtom3096 chi ∧
      Fin15AnchoredAtom3099 chi ∧
      Fin15AnchoredAtom3110 chi ∧
      Fin15AnchoredAtom3159 chi ∧
      Fin15AnchoredAtom3363 chi ∧
      Fin15AnchoredAtom4188 chi)))) ∨
      ((((Fin15AnchoredAtom3096 chi ∧
      Fin15AnchoredAtom3100 chi ∧
      Fin15AnchoredAtom3111 chi ∧
      Fin15AnchoredAtom3160 chi ∧
      Fin15AnchoredAtom3364 chi ∧
      Fin15AnchoredAtom4189 chi) ∨
      (Fin15AnchoredAtom3096 chi ∧
      Fin15AnchoredAtom3101 chi ∧
      Fin15AnchoredAtom3112 chi ∧
      Fin15AnchoredAtom3161 chi ∧
      Fin15AnchoredAtom3365 chi ∧
      Fin15AnchoredAtom4190 chi)) ∨
      ((Fin15AnchoredAtom3097 chi ∧
      Fin15AnchoredAtom3099 chi ∧
      Fin15AnchoredAtom3114 chi ∧
      Fin15AnchoredAtom3163 chi ∧
      Fin15AnchoredAtom3367 chi ∧
      Fin15AnchoredAtom4192 chi) ∨
      (Fin15AnchoredAtom3097 chi ∧
      Fin15AnchoredAtom3100 chi ∧
      Fin15AnchoredAtom3115 chi ∧
      Fin15AnchoredAtom3164 chi ∧
      Fin15AnchoredAtom3368 chi ∧
      Fin15AnchoredAtom4193 chi))) ∨
      (((Fin15AnchoredAtom3097 chi ∧
      Fin15AnchoredAtom3101 chi ∧
      Fin15AnchoredAtom3116 chi ∧
      Fin15AnchoredAtom3165 chi ∧
      Fin15AnchoredAtom3369 chi ∧
      Fin15AnchoredAtom4194 chi) ∨
      (Fin15AnchoredAtom3099 chi ∧
      Fin15AnchoredAtom3100 chi ∧
      Fin15AnchoredAtom3120 chi ∧
      Fin15AnchoredAtom3169 chi ∧
      Fin15AnchoredAtom3373 chi ∧
      Fin15AnchoredAtom4198 chi)) ∨
      ((Fin15AnchoredAtom3099 chi ∧
      Fin15AnchoredAtom3101 chi ∧
      Fin15AnchoredAtom3121 chi ∧
      Fin15AnchoredAtom3170 chi ∧
      Fin15AnchoredAtom3374 chi ∧
      Fin15AnchoredAtom4199 chi) ∨
      (Fin15AnchoredAtom3100 chi ∧
      Fin15AnchoredAtom3101 chi ∧
      Fin15AnchoredAtom3122 chi ∧
      Fin15AnchoredAtom3171 chi ∧
      Fin15AnchoredAtom3375 chi ∧
      Fin15AnchoredAtom4200 chi)))))))) ∨
      (((((((Fin15AnchoredAtom3102 chi ∧
      Fin15AnchoredAtom3103 chi ∧
      Fin15AnchoredAtom3108 chi ∧
      Fin15AnchoredAtom3172 chi ∧
      Fin15AnchoredAtom3376 chi ∧
      Fin15AnchoredAtom4201 chi) ∨
      ((Fin15AnchoredAtom3102 chi ∧
      Fin15AnchoredAtom3105 chi ∧
      Fin15AnchoredAtom3110 chi ∧
      Fin15AnchoredAtom3174 chi ∧
      Fin15AnchoredAtom3378 chi ∧
      Fin15AnchoredAtom4203 chi) ∨
      (Fin15AnchoredAtom3102 chi ∧
      Fin15AnchoredAtom3106 chi ∧
      Fin15AnchoredAtom3111 chi ∧
      Fin15AnchoredAtom3175 chi ∧
      Fin15AnchoredAtom3379 chi ∧
      Fin15AnchoredAtom4204 chi))) ∨
      (((Fin15AnchoredAtom3103 chi ∧
      Fin15AnchoredAtom3106 chi ∧
      Fin15AnchoredAtom3115 chi ∧
      Fin15AnchoredAtom3179 chi ∧
      Fin15AnchoredAtom3383 chi ∧
      Fin15AnchoredAtom4208 chi) ∨
      (Fin15AnchoredAtom3105 chi ∧
      Fin15AnchoredAtom3106 chi ∧
      Fin15AnchoredAtom3120 chi ∧
      Fin15AnchoredAtom3184 chi ∧
      Fin15AnchoredAtom3388 chi ∧
      Fin15AnchoredAtom4213 chi)) ∨
      ((Fin15AnchoredAtom3106 chi ∧
      Fin15AnchoredAtom3107 chi ∧
      Fin15AnchoredAtom3122 chi ∧
      Fin15AnchoredAtom3186 chi ∧
      Fin15AnchoredAtom3390 chi ∧
      Fin15AnchoredAtom4215 chi) ∨
      (Fin15AnchoredAtom3108 chi ∧
      Fin15AnchoredAtom3110 chi ∧
      Fin15AnchoredAtom3114 chi ∧
      Fin15AnchoredAtom3188 chi ∧
      Fin15AnchoredAtom3392 chi ∧
      Fin15AnchoredAtom4217 chi)))) ∨
      ((((Fin15AnchoredAtom3108 chi ∧
      Fin15AnchoredAtom3111 chi ∧
      Fin15AnchoredAtom3115 chi ∧
      Fin15AnchoredAtom3189 chi ∧
      Fin15AnchoredAtom3393 chi ∧
      Fin15AnchoredAtom4218 chi) ∨
      (Fin15AnchoredAtom3108 chi ∧
      Fin15AnchoredAtom3112 chi ∧
      Fin15AnchoredAtom3116 chi ∧
      Fin15AnchoredAtom3190 chi ∧
      Fin15AnchoredAtom3394 chi ∧
      Fin15AnchoredAtom4219 chi)) ∨
      ((Fin15AnchoredAtom3110 chi ∧
      Fin15AnchoredAtom3111 chi ∧
      Fin15AnchoredAtom3120 chi ∧
      Fin15AnchoredAtom3194 chi ∧
      Fin15AnchoredAtom3398 chi ∧
      Fin15AnchoredAtom4223 chi) ∨
      (Fin15AnchoredAtom3110 chi ∧
      Fin15AnchoredAtom3112 chi ∧
      Fin15AnchoredAtom3121 chi ∧
      Fin15AnchoredAtom3195 chi ∧
      Fin15AnchoredAtom3399 chi ∧
      Fin15AnchoredAtom4224 chi))) ∨
      (((Fin15AnchoredAtom3111 chi ∧
      Fin15AnchoredAtom3112 chi ∧
      Fin15AnchoredAtom3122 chi ∧
      Fin15AnchoredAtom3196 chi ∧
      Fin15AnchoredAtom3400 chi ∧
      Fin15AnchoredAtom4225 chi) ∨
      (Fin15AnchoredAtom3114 chi ∧
      Fin15AnchoredAtom3115 chi ∧
      Fin15AnchoredAtom3120 chi ∧
      Fin15AnchoredAtom3200 chi ∧
      Fin15AnchoredAtom3404 chi ∧
      Fin15AnchoredAtom4229 chi)) ∨
      ((Fin15AnchoredAtom3114 chi ∧
      Fin15AnchoredAtom3116 chi ∧
      Fin15AnchoredAtom3121 chi ∧
      Fin15AnchoredAtom3201 chi ∧
      Fin15AnchoredAtom3405 chi ∧
      Fin15AnchoredAtom4230 chi) ∨
      (Fin15AnchoredAtom3115 chi ∧
      Fin15AnchoredAtom3116 chi ∧
      Fin15AnchoredAtom3122 chi ∧
      Fin15AnchoredAtom3202 chi ∧
      Fin15AnchoredAtom3406 chi ∧
      Fin15AnchoredAtom4231 chi))))) ∨
      (((((Fin15AnchoredAtom3120 chi ∧
      Fin15AnchoredAtom3121 chi ∧
      Fin15AnchoredAtom3122 chi ∧
      Fin15AnchoredAtom3206 chi ∧
      Fin15AnchoredAtom3410 chi ∧
      Fin15AnchoredAtom4235 chi) ∨
      (Fin15AnchoredAtom3123 chi ∧
      Fin15AnchoredAtom3124 chi ∧
      Fin15AnchoredAtom3130 chi ∧
      Fin15AnchoredAtom3151 chi ∧
      Fin15AnchoredAtom3411 chi ∧
      Fin15AnchoredAtom4236 chi)) ∨
      ((Fin15AnchoredAtom3123 chi ∧
      Fin15AnchoredAtom3128 chi ∧
      Fin15AnchoredAtom3134 chi ∧
      Fin15AnchoredAtom3155 chi ∧
      Fin15AnchoredAtom3415 chi ∧
      Fin15AnchoredAtom4240 chi) ∨
      (Fin15AnchoredAtom3124 chi ∧
      Fin15AnchoredAtom3125 chi ∧
      Fin15AnchoredAtom3136 chi ∧
      Fin15AnchoredAtom3157 chi ∧
      Fin15AnchoredAtom3417 chi ∧
      Fin15AnchoredAtom4242 chi))) ∨
      (((Fin15AnchoredAtom3124 chi ∧
      Fin15AnchoredAtom3127 chi ∧
      Fin15AnchoredAtom3138 chi ∧
      Fin15AnchoredAtom3159 chi ∧
      Fin15AnchoredAtom3419 chi ∧
      Fin15AnchoredAtom4244 chi) ∨
      (Fin15AnchoredAtom3124 chi ∧
      Fin15AnchoredAtom3128 chi ∧
      Fin15AnchoredAtom3139 chi ∧
      Fin15AnchoredAtom3160 chi ∧
      Fin15AnchoredAtom3420 chi ∧
      Fin15AnchoredAtom4245 chi)) ∨
      ((Fin15AnchoredAtom3124 chi ∧
      Fin15AnchoredAtom3129 chi ∧
      Fin15AnchoredAtom3140 chi ∧
      Fin15AnchoredAtom3161 chi ∧
      Fin15AnchoredAtom3421 chi ∧
      Fin15AnchoredAtom4246 chi) ∨
      (Fin15AnchoredAtom3125 chi ∧
      Fin15AnchoredAtom3127 chi ∧
      Fin15AnchoredAtom3142 chi ∧
      Fin15AnchoredAtom3163 chi ∧
      Fin15AnchoredAtom3423 chi ∧
      Fin15AnchoredAtom4248 chi)))) ∨
      ((((Fin15AnchoredAtom3125 chi ∧
      Fin15AnchoredAtom3128 chi ∧
      Fin15AnchoredAtom3143 chi ∧
      Fin15AnchoredAtom3164 chi ∧
      Fin15AnchoredAtom3424 chi ∧
      Fin15AnchoredAtom4249 chi) ∨
      (Fin15AnchoredAtom3125 chi ∧
      Fin15AnchoredAtom3129 chi ∧
      Fin15AnchoredAtom3144 chi ∧
      Fin15AnchoredAtom3165 chi ∧
      Fin15AnchoredAtom3425 chi ∧
      Fin15AnchoredAtom4250 chi)) ∨
      ((Fin15AnchoredAtom3127 chi ∧
      Fin15AnchoredAtom3128 chi ∧
      Fin15AnchoredAtom3148 chi ∧
      Fin15AnchoredAtom3169 chi ∧
      Fin15AnchoredAtom3429 chi ∧
      Fin15AnchoredAtom4254 chi) ∨
      (Fin15AnchoredAtom3127 chi ∧
      Fin15AnchoredAtom3129 chi ∧
      Fin15AnchoredAtom3149 chi ∧
      Fin15AnchoredAtom3170 chi ∧
      Fin15AnchoredAtom3430 chi ∧
      Fin15AnchoredAtom4255 chi))) ∨
      (((Fin15AnchoredAtom3128 chi ∧
      Fin15AnchoredAtom3129 chi ∧
      Fin15AnchoredAtom3150 chi ∧
      Fin15AnchoredAtom3171 chi ∧
      Fin15AnchoredAtom3431 chi ∧
      Fin15AnchoredAtom4256 chi) ∨
      (Fin15AnchoredAtom3130 chi ∧
      Fin15AnchoredAtom3133 chi ∧
      Fin15AnchoredAtom3138 chi ∧
      Fin15AnchoredAtom3174 chi ∧
      Fin15AnchoredAtom3434 chi ∧
      Fin15AnchoredAtom4259 chi)) ∨
      ((Fin15AnchoredAtom3130 chi ∧
      Fin15AnchoredAtom3134 chi ∧
      Fin15AnchoredAtom3139 chi ∧
      Fin15AnchoredAtom3175 chi ∧
      Fin15AnchoredAtom3435 chi ∧
      Fin15AnchoredAtom4260 chi) ∨
      (Fin15AnchoredAtom3131 chi ∧
      Fin15AnchoredAtom3133 chi ∧
      Fin15AnchoredAtom3142 chi ∧
      Fin15AnchoredAtom3178 chi ∧
      Fin15AnchoredAtom3438 chi ∧
      Fin15AnchoredAtom4263 chi)))))) ∨
      ((((((Fin15AnchoredAtom3133 chi ∧
      Fin15AnchoredAtom3134 chi ∧
      Fin15AnchoredAtom3148 chi ∧
      Fin15AnchoredAtom3184 chi ∧
      Fin15AnchoredAtom3444 chi ∧
      Fin15AnchoredAtom4269 chi) ∨
      (Fin15AnchoredAtom3134 chi ∧
      Fin15AnchoredAtom3135 chi ∧
      Fin15AnchoredAtom3150 chi ∧
      Fin15AnchoredAtom3186 chi ∧
      Fin15AnchoredAtom3446 chi ∧
      Fin15AnchoredAtom4271 chi)) ∨
      ((Fin15AnchoredAtom3136 chi ∧
      Fin15AnchoredAtom3138 chi ∧
      Fin15AnchoredAtom3142 chi ∧
      Fin15AnchoredAtom3188 chi ∧
      Fin15AnchoredAtom3448 chi ∧
      Fin15AnchoredAtom4273 chi) ∨
      (Fin15AnchoredAtom3136 chi ∧
      Fin15AnchoredAtom3139 chi ∧
      Fin15AnchoredAtom3143 chi ∧
      Fin15AnchoredAtom3189 chi ∧
      Fin15AnchoredAtom3449 chi ∧
      Fin15AnchoredAtom4274 chi))) ∨
      (((Fin15AnchoredAtom3136 chi ∧
      Fin15AnchoredAtom3140 chi ∧
      Fin15AnchoredAtom3144 chi ∧
      Fin15AnchoredAtom3190 chi ∧
      Fin15AnchoredAtom3450 chi ∧
      Fin15AnchoredAtom4275 chi) ∨
      (Fin15AnchoredAtom3138 chi ∧
      Fin15AnchoredAtom3139 chi ∧
      Fin15AnchoredAtom3148 chi ∧
      Fin15AnchoredAtom3194 chi ∧
      Fin15AnchoredAtom3454 chi ∧
      Fin15AnchoredAtom4279 chi)) ∨
      ((Fin15AnchoredAtom3138 chi ∧
      Fin15AnchoredAtom3140 chi ∧
      Fin15AnchoredAtom3149 chi ∧
      Fin15AnchoredAtom3195 chi ∧
      Fin15AnchoredAtom3455 chi ∧
      Fin15AnchoredAtom4280 chi) ∨
      (Fin15AnchoredAtom3139 chi ∧
      Fin15AnchoredAtom3140 chi ∧
      Fin15AnchoredAtom3150 chi ∧
      Fin15AnchoredAtom3196 chi ∧
      Fin15AnchoredAtom3456 chi ∧
      Fin15AnchoredAtom4281 chi)))) ∨
      ((((Fin15AnchoredAtom3142 chi ∧
      Fin15AnchoredAtom3143 chi ∧
      Fin15AnchoredAtom3148 chi ∧
      Fin15AnchoredAtom3200 chi ∧
      Fin15AnchoredAtom3460 chi ∧
      Fin15AnchoredAtom4285 chi) ∨
      (Fin15AnchoredAtom3142 chi ∧
      Fin15AnchoredAtom3144 chi ∧
      Fin15AnchoredAtom3149 chi ∧
      Fin15AnchoredAtom3201 chi ∧
      Fin15AnchoredAtom3461 chi ∧
      Fin15AnchoredAtom4286 chi)) ∨
      ((Fin15AnchoredAtom3143 chi ∧
      Fin15AnchoredAtom3144 chi ∧
      Fin15AnchoredAtom3150 chi ∧
      Fin15AnchoredAtom3202 chi ∧
      Fin15AnchoredAtom3462 chi ∧
      Fin15AnchoredAtom4287 chi) ∨
      (Fin15AnchoredAtom3148 chi ∧
      Fin15AnchoredAtom3149 chi ∧
      Fin15AnchoredAtom3150 chi ∧
      Fin15AnchoredAtom3206 chi ∧
      Fin15AnchoredAtom3466 chi ∧
      Fin15AnchoredAtom4291 chi))) ∨
      (((Fin15AnchoredAtom3151 chi ∧
      Fin15AnchoredAtom3152 chi ∧
      Fin15AnchoredAtom3157 chi ∧
      Fin15AnchoredAtom3172 chi ∧
      Fin15AnchoredAtom3467 chi ∧
      Fin15AnchoredAtom4292 chi) ∨
      (Fin15AnchoredAtom3152 chi ∧
      Fin15AnchoredAtom3154 chi ∧
      Fin15AnchoredAtom3163 chi ∧
      Fin15AnchoredAtom3178 chi ∧
      Fin15AnchoredAtom3473 chi ∧
      Fin15AnchoredAtom4298 chi)) ∨
      ((Fin15AnchoredAtom3154 chi ∧
      Fin15AnchoredAtom3155 chi ∧
      Fin15AnchoredAtom3169 chi ∧
      Fin15AnchoredAtom3184 chi ∧
      Fin15AnchoredAtom3479 chi ∧
      Fin15AnchoredAtom4304 chi) ∨
      (Fin15AnchoredAtom3155 chi ∧
      Fin15AnchoredAtom3156 chi ∧
      Fin15AnchoredAtom3171 chi ∧
      Fin15AnchoredAtom3186 chi ∧
      Fin15AnchoredAtom3481 chi ∧
      Fin15AnchoredAtom4306 chi))))) ∨
      (((((Fin15AnchoredAtom3157 chi ∧
      Fin15AnchoredAtom3159 chi ∧
      Fin15AnchoredAtom3163 chi ∧
      Fin15AnchoredAtom3188 chi ∧
      Fin15AnchoredAtom3483 chi ∧
      Fin15AnchoredAtom4308 chi) ∨
      (Fin15AnchoredAtom3157 chi ∧
      Fin15AnchoredAtom3160 chi ∧
      Fin15AnchoredAtom3164 chi ∧
      Fin15AnchoredAtom3189 chi ∧
      Fin15AnchoredAtom3484 chi ∧
      Fin15AnchoredAtom4309 chi)) ∨
      ((Fin15AnchoredAtom3157 chi ∧
      Fin15AnchoredAtom3161 chi ∧
      Fin15AnchoredAtom3165 chi ∧
      Fin15AnchoredAtom3190 chi ∧
      Fin15AnchoredAtom3485 chi ∧
      Fin15AnchoredAtom4310 chi) ∨
      (Fin15AnchoredAtom3159 chi ∧
      Fin15AnchoredAtom3160 chi ∧
      Fin15AnchoredAtom3169 chi ∧
      Fin15AnchoredAtom3194 chi ∧
      Fin15AnchoredAtom3489 chi ∧
      Fin15AnchoredAtom4314 chi))) ∨
      (((Fin15AnchoredAtom3159 chi ∧
      Fin15AnchoredAtom3161 chi ∧
      Fin15AnchoredAtom3170 chi ∧
      Fin15AnchoredAtom3195 chi ∧
      Fin15AnchoredAtom3490 chi ∧
      Fin15AnchoredAtom4315 chi) ∨
      (Fin15AnchoredAtom3160 chi ∧
      Fin15AnchoredAtom3161 chi ∧
      Fin15AnchoredAtom3171 chi ∧
      Fin15AnchoredAtom3196 chi ∧
      Fin15AnchoredAtom3491 chi ∧
      Fin15AnchoredAtom4316 chi)) ∨
      ((Fin15AnchoredAtom3163 chi ∧
      Fin15AnchoredAtom3164 chi ∧
      Fin15AnchoredAtom3169 chi ∧
      Fin15AnchoredAtom3200 chi ∧
      Fin15AnchoredAtom3495 chi ∧
      Fin15AnchoredAtom4320 chi) ∨
      (Fin15AnchoredAtom3163 chi ∧
      Fin15AnchoredAtom3165 chi ∧
      Fin15AnchoredAtom3170 chi ∧
      Fin15AnchoredAtom3201 chi ∧
      Fin15AnchoredAtom3496 chi ∧
      Fin15AnchoredAtom4321 chi)))) ∨
      ((((Fin15AnchoredAtom3164 chi ∧
      Fin15AnchoredAtom3165 chi ∧
      Fin15AnchoredAtom3171 chi ∧
      Fin15AnchoredAtom3202 chi ∧
      Fin15AnchoredAtom3497 chi ∧
      Fin15AnchoredAtom4322 chi) ∨
      (Fin15AnchoredAtom3169 chi ∧
      Fin15AnchoredAtom3170 chi ∧
      Fin15AnchoredAtom3171 chi ∧
      Fin15AnchoredAtom3206 chi ∧
      Fin15AnchoredAtom3501 chi ∧
      Fin15AnchoredAtom4326 chi)) ∨
      ((Fin15AnchoredAtom3172 chi ∧
      Fin15AnchoredAtom3175 chi ∧
      Fin15AnchoredAtom3179 chi ∧
      Fin15AnchoredAtom3189 chi ∧
      Fin15AnchoredAtom3504 chi ∧
      Fin15AnchoredAtom4329 chi) ∨
      (Fin15AnchoredAtom3174 chi ∧
      Fin15AnchoredAtom3175 chi ∧
      Fin15AnchoredAtom3184 chi ∧
      Fin15AnchoredAtom3194 chi ∧
      Fin15AnchoredAtom3509 chi ∧
      Fin15AnchoredAtom4334 chi))) ∨
      (((Fin15AnchoredAtom3174 chi ∧
      Fin15AnchoredAtom3176 chi ∧
      Fin15AnchoredAtom3185 chi ∧
      Fin15AnchoredAtom3195 chi ∧
      Fin15AnchoredAtom3510 chi ∧
      Fin15AnchoredAtom4335 chi) ∨
      (Fin15AnchoredAtom3178 chi ∧
      Fin15AnchoredAtom3179 chi ∧
      Fin15AnchoredAtom3184 chi ∧
      Fin15AnchoredAtom3200 chi ∧
      Fin15AnchoredAtom3515 chi ∧
      Fin15AnchoredAtom4340 chi)) ∨
      ((Fin15AnchoredAtom3179 chi ∧
      Fin15AnchoredAtom3180 chi ∧
      Fin15AnchoredAtom3186 chi ∧
      Fin15AnchoredAtom3202 chi ∧
      Fin15AnchoredAtom3517 chi ∧
      Fin15AnchoredAtom4342 chi) ∨
      (Fin15AnchoredAtom3188 chi ∧
      Fin15AnchoredAtom3189 chi ∧
      Fin15AnchoredAtom3194 chi ∧
      Fin15AnchoredAtom3200 chi ∧
      Fin15AnchoredAtom3525 chi ∧
      Fin15AnchoredAtom4350 chi))))))) ∨
      (((((((Fin15AnchoredAtom3188 chi ∧
      Fin15AnchoredAtom3190 chi ∧
      Fin15AnchoredAtom3195 chi ∧
      Fin15AnchoredAtom3201 chi ∧
      Fin15AnchoredAtom3526 chi ∧
      Fin15AnchoredAtom4351 chi) ∨
      (Fin15AnchoredAtom3189 chi ∧
      Fin15AnchoredAtom3190 chi ∧
      Fin15AnchoredAtom3196 chi ∧
      Fin15AnchoredAtom3202 chi ∧
      Fin15AnchoredAtom3527 chi ∧
      Fin15AnchoredAtom4352 chi)) ∨
      ((Fin15AnchoredAtom3194 chi ∧
      Fin15AnchoredAtom3195 chi ∧
      Fin15AnchoredAtom3196 chi ∧
      Fin15AnchoredAtom3206 chi ∧
      Fin15AnchoredAtom3531 chi ∧
      Fin15AnchoredAtom4356 chi) ∨
      (Fin15AnchoredAtom3200 chi ∧
      Fin15AnchoredAtom3201 chi ∧
      Fin15AnchoredAtom3202 chi ∧
      Fin15AnchoredAtom3206 chi ∧
      Fin15AnchoredAtom3535 chi ∧
      Fin15AnchoredAtom4360 chi))) ∨
      (((Fin15AnchoredAtom3207 chi ∧
      Fin15AnchoredAtom3208 chi ∧
      Fin15AnchoredAtom3215 chi ∧
      Fin15AnchoredAtom3243 chi ∧
      Fin15AnchoredAtom3327 chi ∧
      Fin15AnchoredAtom4362 chi) ∨
      (Fin15AnchoredAtom3207 chi ∧
      Fin15AnchoredAtom3209 chi ∧
      Fin15AnchoredAtom3216 chi ∧
      Fin15AnchoredAtom3244 chi ∧
      Fin15AnchoredAtom3328 chi ∧
      Fin15AnchoredAtom4363 chi)) ∨
      ((Fin15AnchoredAtom3207 chi ∧
      Fin15AnchoredAtom3210 chi ∧
      Fin15AnchoredAtom3217 chi ∧
      Fin15AnchoredAtom3245 chi ∧
      Fin15AnchoredAtom3329 chi ∧
      Fin15AnchoredAtom4364 chi) ∨
      (Fin15AnchoredAtom3207 chi ∧
      Fin15AnchoredAtom3212 chi ∧
      Fin15AnchoredAtom3219 chi ∧
      Fin15AnchoredAtom3247 chi ∧
      Fin15AnchoredAtom3331 chi ∧
      Fin15AnchoredAtom4366 chi)))) ∨
      ((((Fin15AnchoredAtom3207 chi ∧
      Fin15AnchoredAtom3213 chi ∧
      Fin15AnchoredAtom3220 chi ∧
      Fin15AnchoredAtom3248 chi ∧
      Fin15AnchoredAtom3332 chi ∧
      Fin15AnchoredAtom4367 chi) ∨
      (Fin15AnchoredAtom3207 chi ∧
      Fin15AnchoredAtom3214 chi ∧
      Fin15AnchoredAtom3221 chi ∧
      Fin15AnchoredAtom3249 chi ∧
      Fin15AnchoredAtom3333 chi ∧
      Fin15AnchoredAtom4368 chi)) ∨
      ((Fin15AnchoredAtom3208 chi ∧
      Fin15AnchoredAtom3209 chi ∧
      Fin15AnchoredAtom3222 chi ∧
      Fin15AnchoredAtom3250 chi ∧
      Fin15AnchoredAtom3334 chi ∧
      Fin15AnchoredAtom4369 chi) ∨
      (Fin15AnchoredAtom3208 chi ∧
      Fin15AnchoredAtom3210 chi ∧
      Fin15AnchoredAtom3223 chi ∧
      Fin15AnchoredAtom3251 chi ∧
      Fin15AnchoredAtom3335 chi ∧
      Fin15AnchoredAtom4370 chi))) ∨
      (((Fin15AnchoredAtom3209 chi ∧
      Fin15AnchoredAtom3210 chi ∧
      Fin15AnchoredAtom3228 chi ∧
      Fin15AnchoredAtom3256 chi ∧
      Fin15AnchoredAtom3340 chi ∧
      Fin15AnchoredAtom4375 chi) ∨
      (Fin15AnchoredAtom3209 chi ∧
      Fin15AnchoredAtom3212 chi ∧
      Fin15AnchoredAtom3230 chi ∧
      Fin15AnchoredAtom3258 chi ∧
      Fin15AnchoredAtom3342 chi ∧
      Fin15AnchoredAtom4377 chi)) ∨
      ((Fin15AnchoredAtom3209 chi ∧
      Fin15AnchoredAtom3213 chi ∧
      Fin15AnchoredAtom3231 chi ∧
      Fin15AnchoredAtom3259 chi ∧
      Fin15AnchoredAtom3343 chi ∧
      Fin15AnchoredAtom4378 chi) ∨
      (Fin15AnchoredAtom3209 chi ∧
      Fin15AnchoredAtom3214 chi ∧
      Fin15AnchoredAtom3232 chi ∧
      Fin15AnchoredAtom3260 chi ∧
      Fin15AnchoredAtom3344 chi ∧
      Fin15AnchoredAtom4379 chi))))) ∨
      (((((Fin15AnchoredAtom3210 chi ∧
      Fin15AnchoredAtom3212 chi ∧
      Fin15AnchoredAtom3234 chi ∧
      Fin15AnchoredAtom3262 chi ∧
      Fin15AnchoredAtom3346 chi ∧
      Fin15AnchoredAtom4381 chi) ∨
      (Fin15AnchoredAtom3210 chi ∧
      Fin15AnchoredAtom3213 chi ∧
      Fin15AnchoredAtom3235 chi ∧
      Fin15AnchoredAtom3263 chi ∧
      Fin15AnchoredAtom3347 chi ∧
      Fin15AnchoredAtom4382 chi)) ∨
      ((Fin15AnchoredAtom3210 chi ∧
      Fin15AnchoredAtom3214 chi ∧
      Fin15AnchoredAtom3236 chi ∧
      Fin15AnchoredAtom3264 chi ∧
      Fin15AnchoredAtom3348 chi ∧
      Fin15AnchoredAtom4383 chi) ∨
      (Fin15AnchoredAtom3212 chi ∧
      Fin15AnchoredAtom3213 chi ∧
      Fin15AnchoredAtom3240 chi ∧
      Fin15AnchoredAtom3268 chi ∧
      Fin15AnchoredAtom3352 chi ∧
      Fin15AnchoredAtom4387 chi))) ∨
      (((Fin15AnchoredAtom3212 chi ∧
      Fin15AnchoredAtom3214 chi ∧
      Fin15AnchoredAtom3241 chi ∧
      Fin15AnchoredAtom3269 chi ∧
      Fin15AnchoredAtom3353 chi ∧
      Fin15AnchoredAtom4388 chi) ∨
      (Fin15AnchoredAtom3213 chi ∧
      Fin15AnchoredAtom3214 chi ∧
      Fin15AnchoredAtom3242 chi ∧
      Fin15AnchoredAtom3270 chi ∧
      Fin15AnchoredAtom3354 chi ∧
      Fin15AnchoredAtom4389 chi)) ∨
      ((Fin15AnchoredAtom3216 chi ∧
      Fin15AnchoredAtom3217 chi ∧
      Fin15AnchoredAtom3228 chi ∧
      Fin15AnchoredAtom3277 chi ∧
      Fin15AnchoredAtom3361 chi ∧
      Fin15AnchoredAtom4396 chi) ∨
      (Fin15AnchoredAtom3216 chi ∧
      Fin15AnchoredAtom3219 chi ∧
      Fin15AnchoredAtom3230 chi ∧
      Fin15AnchoredAtom3279 chi ∧
      Fin15AnchoredAtom3363 chi ∧
      Fin15AnchoredAtom4398 chi)))) ∨
      ((((Fin15AnchoredAtom3216 chi ∧
      Fin15AnchoredAtom3220 chi ∧
      Fin15AnchoredAtom3231 chi ∧
      Fin15AnchoredAtom3280 chi ∧
      Fin15AnchoredAtom3364 chi ∧
      Fin15AnchoredAtom4399 chi) ∨
      (Fin15AnchoredAtom3216 chi ∧
      Fin15AnchoredAtom3221 chi ∧
      Fin15AnchoredAtom3232 chi ∧
      Fin15AnchoredAtom3281 chi ∧
      Fin15AnchoredAtom3365 chi ∧
      Fin15AnchoredAtom4400 chi)) ∨
      ((Fin15AnchoredAtom3217 chi ∧
      Fin15AnchoredAtom3219 chi ∧
      Fin15AnchoredAtom3234 chi ∧
      Fin15AnchoredAtom3283 chi ∧
      Fin15AnchoredAtom3367 chi ∧
      Fin15AnchoredAtom4402 chi) ∨
      (Fin15AnchoredAtom3217 chi ∧
      Fin15AnchoredAtom3220 chi ∧
      Fin15AnchoredAtom3235 chi ∧
      Fin15AnchoredAtom3284 chi ∧
      Fin15AnchoredAtom3368 chi ∧
      Fin15AnchoredAtom4403 chi))) ∨
      (((Fin15AnchoredAtom3217 chi ∧
      Fin15AnchoredAtom3221 chi ∧
      Fin15AnchoredAtom3236 chi ∧
      Fin15AnchoredAtom3285 chi ∧
      Fin15AnchoredAtom3369 chi ∧
      Fin15AnchoredAtom4404 chi) ∨
      (Fin15AnchoredAtom3219 chi ∧
      Fin15AnchoredAtom3220 chi ∧
      Fin15AnchoredAtom3240 chi ∧
      Fin15AnchoredAtom3289 chi ∧
      Fin15AnchoredAtom3373 chi ∧
      Fin15AnchoredAtom4408 chi)) ∨
      ((Fin15AnchoredAtom3219 chi ∧
      Fin15AnchoredAtom3221 chi ∧
      Fin15AnchoredAtom3241 chi ∧
      Fin15AnchoredAtom3290 chi ∧
      Fin15AnchoredAtom3374 chi ∧
      Fin15AnchoredAtom4409 chi) ∨
      (Fin15AnchoredAtom3220 chi ∧
      Fin15AnchoredAtom3221 chi ∧
      Fin15AnchoredAtom3242 chi ∧
      Fin15AnchoredAtom3291 chi ∧
      Fin15AnchoredAtom3375 chi ∧
      Fin15AnchoredAtom4410 chi)))))) ∨
      ((((((Fin15AnchoredAtom3222 chi ∧
      Fin15AnchoredAtom3223 chi ∧
      Fin15AnchoredAtom3228 chi ∧
      Fin15AnchoredAtom3292 chi ∧
      Fin15AnchoredAtom3376 chi ∧
      Fin15AnchoredAtom4411 chi) ∨
      (Fin15AnchoredAtom3222 chi ∧
      Fin15AnchoredAtom3226 chi ∧
      Fin15AnchoredAtom3231 chi ∧
      Fin15AnchoredAtom3295 chi ∧
      Fin15AnchoredAtom3379 chi ∧
      Fin15AnchoredAtom4414 chi)) ∨
      ((Fin15AnchoredAtom3223 chi ∧
      Fin15AnchoredAtom3226 chi ∧
      Fin15AnchoredAtom3235 chi ∧
      Fin15AnchoredAtom3299 chi ∧
      Fin15AnchoredAtom3383 chi ∧
      Fin15AnchoredAtom4418 chi) ∨
      (Fin15AnchoredAtom3225 chi ∧
      Fin15AnchoredAtom3226 chi ∧
      Fin15AnchoredAtom3240 chi ∧
      Fin15AnchoredAtom3304 chi ∧
      Fin15AnchoredAtom3388 chi ∧
      Fin15AnchoredAtom4423 chi))) ∨
      (((Fin15AnchoredAtom3226 chi ∧
      Fin15AnchoredAtom3227 chi ∧
      Fin15AnchoredAtom3242 chi ∧
      Fin15AnchoredAtom3306 chi ∧
      Fin15AnchoredAtom3390 chi ∧
      Fin15AnchoredAtom4425 chi) ∨
      (Fin15AnchoredAtom3228 chi ∧
      Fin15AnchoredAtom3230 chi ∧
      Fin15AnchoredAtom3234 chi ∧
      Fin15AnchoredAtom3308 chi ∧
      Fin15AnchoredAtom3392 chi ∧
      Fin15AnchoredAtom4427 chi)) ∨
      ((Fin15AnchoredAtom3228 chi ∧
      Fin15AnchoredAtom3231 chi ∧
      Fin15AnchoredAtom3235 chi ∧
      Fin15AnchoredAtom3309 chi ∧
      Fin15AnchoredAtom3393 chi ∧
      Fin15AnchoredAtom4428 chi) ∨
      (Fin15AnchoredAtom3228 chi ∧
      Fin15AnchoredAtom3232 chi ∧
      Fin15AnchoredAtom3236 chi ∧
      Fin15AnchoredAtom3310 chi ∧
      Fin15AnchoredAtom3394 chi ∧
      Fin15AnchoredAtom4429 chi)))) ∨
      ((((Fin15AnchoredAtom3230 chi ∧
      Fin15AnchoredAtom3231 chi ∧
      Fin15AnchoredAtom3240 chi ∧
      Fin15AnchoredAtom3314 chi ∧
      Fin15AnchoredAtom3398 chi ∧
      Fin15AnchoredAtom4433 chi) ∨
      (Fin15AnchoredAtom3230 chi ∧
      Fin15AnchoredAtom3232 chi ∧
      Fin15AnchoredAtom3241 chi ∧
      Fin15AnchoredAtom3315 chi ∧
      Fin15AnchoredAtom3399 chi ∧
      Fin15AnchoredAtom4434 chi)) ∨
      ((Fin15AnchoredAtom3231 chi ∧
      Fin15AnchoredAtom3232 chi ∧
      Fin15AnchoredAtom3242 chi ∧
      Fin15AnchoredAtom3316 chi ∧
      Fin15AnchoredAtom3400 chi ∧
      Fin15AnchoredAtom4435 chi) ∨
      (Fin15AnchoredAtom3234 chi ∧
      Fin15AnchoredAtom3235 chi ∧
      Fin15AnchoredAtom3240 chi ∧
      Fin15AnchoredAtom3320 chi ∧
      Fin15AnchoredAtom3404 chi ∧
      Fin15AnchoredAtom4439 chi))) ∨
      (((Fin15AnchoredAtom3234 chi ∧
      Fin15AnchoredAtom3236 chi ∧
      Fin15AnchoredAtom3241 chi ∧
      Fin15AnchoredAtom3321 chi ∧
      Fin15AnchoredAtom3405 chi ∧
      Fin15AnchoredAtom4440 chi) ∨
      (Fin15AnchoredAtom3235 chi ∧
      Fin15AnchoredAtom3236 chi ∧
      Fin15AnchoredAtom3242 chi ∧
      Fin15AnchoredAtom3322 chi ∧
      Fin15AnchoredAtom3406 chi ∧
      Fin15AnchoredAtom4441 chi)) ∨
      ((Fin15AnchoredAtom3240 chi ∧
      Fin15AnchoredAtom3241 chi ∧
      Fin15AnchoredAtom3242 chi ∧
      Fin15AnchoredAtom3326 chi ∧
      Fin15AnchoredAtom3410 chi ∧
      Fin15AnchoredAtom4445 chi) ∨
      (Fin15AnchoredAtom3243 chi ∧
      Fin15AnchoredAtom3249 chi ∧
      Fin15AnchoredAtom3255 chi ∧
      Fin15AnchoredAtom3276 chi ∧
      Fin15AnchoredAtom3416 chi ∧
      Fin15AnchoredAtom4451 chi))))) ∨
      (((((Fin15AnchoredAtom3244 chi ∧
      Fin15AnchoredAtom3245 chi ∧
      Fin15AnchoredAtom3256 chi ∧
      Fin15AnchoredAtom3277 chi ∧
      Fin15AnchoredAtom3417 chi ∧
      Fin15AnchoredAtom4452 chi) ∨
      (Fin15AnchoredAtom3244 chi ∧
      Fin15AnchoredAtom3247 chi ∧
      Fin15AnchoredAtom3258 chi ∧
      Fin15AnchoredAtom3279 chi ∧
      Fin15AnchoredAtom3419 chi ∧
      Fin15AnchoredAtom4454 chi)) ∨
      ((Fin15AnchoredAtom3244 chi ∧
      Fin15AnchoredAtom3248 chi ∧
      Fin15AnchoredAtom3259 chi ∧
      Fin15AnchoredAtom3280 chi ∧
      Fin15AnchoredAtom3420 chi ∧
      Fin15AnchoredAtom4455 chi) ∨
      (Fin15AnchoredAtom3244 chi ∧
      Fin15AnchoredAtom3249 chi ∧
      Fin15AnchoredAtom3260 chi ∧
      Fin15AnchoredAtom3281 chi ∧
      Fin15AnchoredAtom3421 chi ∧
      Fin15AnchoredAtom4456 chi))) ∨
      (((Fin15AnchoredAtom3245 chi ∧
      Fin15AnchoredAtom3247 chi ∧
      Fin15AnchoredAtom3262 chi ∧
      Fin15AnchoredAtom3283 chi ∧
      Fin15AnchoredAtom3423 chi ∧
      Fin15AnchoredAtom4458 chi) ∨
      (Fin15AnchoredAtom3245 chi ∧
      Fin15AnchoredAtom3248 chi ∧
      Fin15AnchoredAtom3263 chi ∧
      Fin15AnchoredAtom3284 chi ∧
      Fin15AnchoredAtom3424 chi ∧
      Fin15AnchoredAtom4459 chi)) ∨
      ((Fin15AnchoredAtom3245 chi ∧
      Fin15AnchoredAtom3249 chi ∧
      Fin15AnchoredAtom3264 chi ∧
      Fin15AnchoredAtom3285 chi ∧
      Fin15AnchoredAtom3425 chi ∧
      Fin15AnchoredAtom4460 chi) ∨
      (Fin15AnchoredAtom3247 chi ∧
      Fin15AnchoredAtom3248 chi ∧
      Fin15AnchoredAtom3268 chi ∧
      Fin15AnchoredAtom3289 chi ∧
      Fin15AnchoredAtom3429 chi ∧
      Fin15AnchoredAtom4464 chi)))) ∨
      ((((Fin15AnchoredAtom3247 chi ∧
      Fin15AnchoredAtom3249 chi ∧
      Fin15AnchoredAtom3269 chi ∧
      Fin15AnchoredAtom3290 chi ∧
      Fin15AnchoredAtom3430 chi ∧
      Fin15AnchoredAtom4465 chi) ∨
      (Fin15AnchoredAtom3248 chi ∧
      Fin15AnchoredAtom3249 chi ∧
      Fin15AnchoredAtom3270 chi ∧
      Fin15AnchoredAtom3291 chi ∧
      Fin15AnchoredAtom3431 chi ∧
      Fin15AnchoredAtom4466 chi)) ∨
      ((Fin15AnchoredAtom3250 chi ∧
      Fin15AnchoredAtom3251 chi ∧
      Fin15AnchoredAtom3256 chi ∧
      Fin15AnchoredAtom3292 chi ∧
      Fin15AnchoredAtom3432 chi ∧
      Fin15AnchoredAtom4467 chi) ∨
      (Fin15AnchoredAtom3250 chi ∧
      Fin15AnchoredAtom3254 chi ∧
      Fin15AnchoredAtom3259 chi ∧
      Fin15AnchoredAtom3295 chi ∧
      Fin15AnchoredAtom3435 chi ∧
      Fin15AnchoredAtom4470 chi))) ∨
      (((Fin15AnchoredAtom3251 chi ∧
      Fin15AnchoredAtom3254 chi ∧
      Fin15AnchoredAtom3263 chi ∧
      Fin15AnchoredAtom3299 chi ∧
      Fin15AnchoredAtom3439 chi ∧
      Fin15AnchoredAtom4474 chi) ∨
      (Fin15AnchoredAtom3253 chi ∧
      Fin15AnchoredAtom3254 chi ∧
      Fin15AnchoredAtom3268 chi ∧
      Fin15AnchoredAtom3304 chi ∧
      Fin15AnchoredAtom3444 chi ∧
      Fin15AnchoredAtom4479 chi)) ∨
      ((Fin15AnchoredAtom3254 chi ∧
      Fin15AnchoredAtom3255 chi ∧
      Fin15AnchoredAtom3270 chi ∧
      Fin15AnchoredAtom3306 chi ∧
      Fin15AnchoredAtom3446 chi ∧
      Fin15AnchoredAtom4481 chi) ∨
      (Fin15AnchoredAtom3256 chi ∧
      Fin15AnchoredAtom3258 chi ∧
      Fin15AnchoredAtom3262 chi ∧
      Fin15AnchoredAtom3308 chi ∧
      Fin15AnchoredAtom3448 chi ∧
      Fin15AnchoredAtom4483 chi)))))))))) := by
  intro hbad
  rcases hbad with hbad | hbad
  ·
    rcases hbad with hbad | hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact fin15Anchored_clause29531 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29532 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29533 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29534 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29535 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29536 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29537 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29538 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29539 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29540 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29541 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29542 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29543 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29544 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29545 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29546 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29547 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29548 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29549 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29550 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29551 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29552 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29553 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29554 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29555 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29556 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29557 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29558 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29559 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29560 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29561 chi hnoStrong hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29562 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29563 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29564 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29565 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29566 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29567 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29568 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29569 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29570 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29571 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29572 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29573 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29574 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29575 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29576 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29577 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29578 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29579 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29580 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29581 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29582 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29583 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29584 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29585 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29586 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29587 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29588 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29589 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29590 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29591 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29592 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29593 chi hnoStrong hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact fin15Anchored_clause29594 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29595 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29596 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29597 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29598 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29599 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29600 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29601 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29602 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29603 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29604 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29605 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29606 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29607 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29608 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29609 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29610 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29611 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29612 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29613 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29614 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29615 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29616 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29617 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29618 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29619 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29620 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29621 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29622 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29623 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29624 chi hnoStrong hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29625 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29626 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29627 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29628 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29629 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29630 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29631 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29632 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29633 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29634 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29635 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29636 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29637 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29638 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29639 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29640 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29641 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29642 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29643 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29644 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29645 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29646 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29647 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29648 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29649 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29650 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29651 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29652 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29653 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29654 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29655 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29656 chi hnoStrong hbad
  ·
    rcases hbad with hbad | hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact fin15Anchored_clause29657 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29658 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29659 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29660 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29661 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29662 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29663 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29664 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29665 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29666 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29667 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29668 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29669 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29670 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29671 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29672 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29673 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29674 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29675 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29676 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29677 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29678 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29679 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29680 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29681 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29682 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29683 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29684 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29685 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29686 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29687 chi hnoStrong hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29688 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29689 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29690 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29691 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29692 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29693 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29694 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29695 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29696 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29697 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29698 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29699 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29700 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29701 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29702 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29703 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29704 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29705 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29706 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29707 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29708 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29709 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29710 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29711 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29712 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29713 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29714 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29715 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29716 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29717 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29718 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29719 chi hnoStrong hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29720 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29721 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29722 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29723 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29724 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29725 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29726 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29727 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29728 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29729 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29730 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29731 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29732 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29733 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29734 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29735 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29736 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29737 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29738 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29739 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29740 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29741 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29742 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29743 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29744 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29745 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29746 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29747 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29748 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29749 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29750 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29751 chi hnoStrong hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29752 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29753 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29754 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29755 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29756 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29757 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29758 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29759 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29760 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29761 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29762 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29763 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29764 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29765 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29766 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29767 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29768 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29769 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29770 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29771 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29772 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29773 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29774 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29775 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29776 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29777 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29778 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29779 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29780 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29781 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29782 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29783 chi hnoStrong hbad

end ErdosSzekeres

end
