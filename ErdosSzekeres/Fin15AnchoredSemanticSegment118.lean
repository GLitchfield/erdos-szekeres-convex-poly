module

public import ErdosSzekeres.Fin15AnchoredClauseChunk232
public import ErdosSzekeres.Fin15AnchoredClauseChunk233
public import ErdosSzekeres.Fin15AnchoredClauseChunk234

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 118. -/

theorem fin15Anchored_rejectSemanticSegment118
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom3256 chi ∧
      Fin15AnchoredAtom3259 chi ∧
      Fin15AnchoredAtom3263 chi ∧
      Fin15AnchoredAtom3309 chi ∧
      Fin15AnchoredAtom3449 chi ∧
      Fin15AnchoredAtom4484 chi) ∨
      ((Fin15AnchoredAtom3256 chi ∧
      Fin15AnchoredAtom3260 chi ∧
      Fin15AnchoredAtom3264 chi ∧
      Fin15AnchoredAtom3310 chi ∧
      Fin15AnchoredAtom3450 chi ∧
      Fin15AnchoredAtom4485 chi) ∨
      (Fin15AnchoredAtom3258 chi ∧
      Fin15AnchoredAtom3259 chi ∧
      Fin15AnchoredAtom3268 chi ∧
      Fin15AnchoredAtom3314 chi ∧
      Fin15AnchoredAtom3454 chi ∧
      Fin15AnchoredAtom4489 chi))) ∨
      (((Fin15AnchoredAtom3258 chi ∧
      Fin15AnchoredAtom3260 chi ∧
      Fin15AnchoredAtom3269 chi ∧
      Fin15AnchoredAtom3315 chi ∧
      Fin15AnchoredAtom3455 chi ∧
      Fin15AnchoredAtom4490 chi) ∨
      (Fin15AnchoredAtom3259 chi ∧
      Fin15AnchoredAtom3260 chi ∧
      Fin15AnchoredAtom3270 chi ∧
      Fin15AnchoredAtom3316 chi ∧
      Fin15AnchoredAtom3456 chi ∧
      Fin15AnchoredAtom4491 chi)) ∨
      ((Fin15AnchoredAtom3262 chi ∧
      Fin15AnchoredAtom3263 chi ∧
      Fin15AnchoredAtom3268 chi ∧
      Fin15AnchoredAtom3320 chi ∧
      Fin15AnchoredAtom3460 chi ∧
      Fin15AnchoredAtom4495 chi) ∨
      (Fin15AnchoredAtom3262 chi ∧
      Fin15AnchoredAtom3264 chi ∧
      Fin15AnchoredAtom3269 chi ∧
      Fin15AnchoredAtom3321 chi ∧
      Fin15AnchoredAtom3461 chi ∧
      Fin15AnchoredAtom4496 chi)))) ∨
      ((((Fin15AnchoredAtom3263 chi ∧
      Fin15AnchoredAtom3264 chi ∧
      Fin15AnchoredAtom3270 chi ∧
      Fin15AnchoredAtom3322 chi ∧
      Fin15AnchoredAtom3462 chi ∧
      Fin15AnchoredAtom4497 chi) ∨
      (Fin15AnchoredAtom3268 chi ∧
      Fin15AnchoredAtom3269 chi ∧
      Fin15AnchoredAtom3270 chi ∧
      Fin15AnchoredAtom3326 chi ∧
      Fin15AnchoredAtom3466 chi ∧
      Fin15AnchoredAtom4501 chi)) ∨
      ((Fin15AnchoredAtom3271 chi ∧
      Fin15AnchoredAtom3272 chi ∧
      Fin15AnchoredAtom3277 chi ∧
      Fin15AnchoredAtom3292 chi ∧
      Fin15AnchoredAtom3467 chi ∧
      Fin15AnchoredAtom4502 chi) ∨
      (Fin15AnchoredAtom3271 chi ∧
      Fin15AnchoredAtom3276 chi ∧
      Fin15AnchoredAtom3281 chi ∧
      Fin15AnchoredAtom3296 chi ∧
      Fin15AnchoredAtom3471 chi ∧
      Fin15AnchoredAtom4506 chi))) ∨
      (((Fin15AnchoredAtom3274 chi ∧
      Fin15AnchoredAtom3275 chi ∧
      Fin15AnchoredAtom3289 chi ∧
      Fin15AnchoredAtom3304 chi ∧
      Fin15AnchoredAtom3479 chi ∧
      Fin15AnchoredAtom4514 chi) ∨
      (Fin15AnchoredAtom3275 chi ∧
      Fin15AnchoredAtom3276 chi ∧
      Fin15AnchoredAtom3291 chi ∧
      Fin15AnchoredAtom3306 chi ∧
      Fin15AnchoredAtom3481 chi ∧
      Fin15AnchoredAtom4516 chi)) ∨
      ((Fin15AnchoredAtom3277 chi ∧
      Fin15AnchoredAtom3279 chi ∧
      Fin15AnchoredAtom3283 chi ∧
      Fin15AnchoredAtom3308 chi ∧
      Fin15AnchoredAtom3483 chi ∧
      Fin15AnchoredAtom4518 chi) ∨
      (Fin15AnchoredAtom3277 chi ∧
      Fin15AnchoredAtom3280 chi ∧
      Fin15AnchoredAtom3284 chi ∧
      Fin15AnchoredAtom3309 chi ∧
      Fin15AnchoredAtom3484 chi ∧
      Fin15AnchoredAtom4519 chi))))) ∨
      (((((Fin15AnchoredAtom3277 chi ∧
      Fin15AnchoredAtom3281 chi ∧
      Fin15AnchoredAtom3285 chi ∧
      Fin15AnchoredAtom3310 chi ∧
      Fin15AnchoredAtom3485 chi ∧
      Fin15AnchoredAtom4520 chi) ∨
      (Fin15AnchoredAtom3279 chi ∧
      Fin15AnchoredAtom3280 chi ∧
      Fin15AnchoredAtom3289 chi ∧
      Fin15AnchoredAtom3314 chi ∧
      Fin15AnchoredAtom3489 chi ∧
      Fin15AnchoredAtom4524 chi)) ∨
      ((Fin15AnchoredAtom3279 chi ∧
      Fin15AnchoredAtom3281 chi ∧
      Fin15AnchoredAtom3290 chi ∧
      Fin15AnchoredAtom3315 chi ∧
      Fin15AnchoredAtom3490 chi ∧
      Fin15AnchoredAtom4525 chi) ∨
      (Fin15AnchoredAtom3280 chi ∧
      Fin15AnchoredAtom3281 chi ∧
      Fin15AnchoredAtom3291 chi ∧
      Fin15AnchoredAtom3316 chi ∧
      Fin15AnchoredAtom3491 chi ∧
      Fin15AnchoredAtom4526 chi))) ∨
      (((Fin15AnchoredAtom3283 chi ∧
      Fin15AnchoredAtom3284 chi ∧
      Fin15AnchoredAtom3289 chi ∧
      Fin15AnchoredAtom3320 chi ∧
      Fin15AnchoredAtom3495 chi ∧
      Fin15AnchoredAtom4530 chi) ∨
      (Fin15AnchoredAtom3283 chi ∧
      Fin15AnchoredAtom3285 chi ∧
      Fin15AnchoredAtom3290 chi ∧
      Fin15AnchoredAtom3321 chi ∧
      Fin15AnchoredAtom3496 chi ∧
      Fin15AnchoredAtom4531 chi)) ∨
      ((Fin15AnchoredAtom3284 chi ∧
      Fin15AnchoredAtom3285 chi ∧
      Fin15AnchoredAtom3291 chi ∧
      Fin15AnchoredAtom3322 chi ∧
      Fin15AnchoredAtom3497 chi ∧
      Fin15AnchoredAtom4532 chi) ∨
      (Fin15AnchoredAtom3289 chi ∧
      Fin15AnchoredAtom3290 chi ∧
      Fin15AnchoredAtom3291 chi ∧
      Fin15AnchoredAtom3326 chi ∧
      Fin15AnchoredAtom3501 chi ∧
      Fin15AnchoredAtom4536 chi)))) ∨
      ((((Fin15AnchoredAtom3294 chi ∧
      Fin15AnchoredAtom3295 chi ∧
      Fin15AnchoredAtom3304 chi ∧
      Fin15AnchoredAtom3314 chi ∧
      Fin15AnchoredAtom3509 chi ∧
      Fin15AnchoredAtom4544 chi) ∨
      (Fin15AnchoredAtom3294 chi ∧
      Fin15AnchoredAtom3296 chi ∧
      Fin15AnchoredAtom3305 chi ∧
      Fin15AnchoredAtom3315 chi ∧
      Fin15AnchoredAtom3510 chi ∧
      Fin15AnchoredAtom4545 chi)) ∨
      ((Fin15AnchoredAtom3298 chi ∧
      Fin15AnchoredAtom3299 chi ∧
      Fin15AnchoredAtom3304 chi ∧
      Fin15AnchoredAtom3320 chi ∧
      Fin15AnchoredAtom3515 chi ∧
      Fin15AnchoredAtom4550 chi) ∨
      (Fin15AnchoredAtom3308 chi ∧
      Fin15AnchoredAtom3309 chi ∧
      Fin15AnchoredAtom3314 chi ∧
      Fin15AnchoredAtom3320 chi ∧
      Fin15AnchoredAtom3525 chi ∧
      Fin15AnchoredAtom4560 chi))) ∨
      (((Fin15AnchoredAtom3308 chi ∧
      Fin15AnchoredAtom3310 chi ∧
      Fin15AnchoredAtom3315 chi ∧
      Fin15AnchoredAtom3321 chi ∧
      Fin15AnchoredAtom3526 chi ∧
      Fin15AnchoredAtom4561 chi) ∨
      (Fin15AnchoredAtom3309 chi ∧
      Fin15AnchoredAtom3310 chi ∧
      Fin15AnchoredAtom3316 chi ∧
      Fin15AnchoredAtom3322 chi ∧
      Fin15AnchoredAtom3527 chi ∧
      Fin15AnchoredAtom4562 chi)) ∨
      ((Fin15AnchoredAtom3314 chi ∧
      Fin15AnchoredAtom3315 chi ∧
      Fin15AnchoredAtom3316 chi ∧
      Fin15AnchoredAtom3326 chi ∧
      Fin15AnchoredAtom3531 chi ∧
      Fin15AnchoredAtom4566 chi) ∨
      (Fin15AnchoredAtom3320 chi ∧
      Fin15AnchoredAtom3321 chi ∧
      Fin15AnchoredAtom3322 chi ∧
      Fin15AnchoredAtom3326 chi ∧
      Fin15AnchoredAtom3535 chi ∧
      Fin15AnchoredAtom4570 chi)))))) ∨
      ((((((Fin15AnchoredAtom3328 chi ∧
      Fin15AnchoredAtom3329 chi ∧
      Fin15AnchoredAtom3340 chi ∧
      Fin15AnchoredAtom3361 chi ∧
      Fin15AnchoredAtom3417 chi ∧
      Fin15AnchoredAtom4578 chi) ∨
      (Fin15AnchoredAtom3328 chi ∧
      Fin15AnchoredAtom3331 chi ∧
      Fin15AnchoredAtom3342 chi ∧
      Fin15AnchoredAtom3363 chi ∧
      Fin15AnchoredAtom3419 chi ∧
      Fin15AnchoredAtom4580 chi)) ∨
      ((Fin15AnchoredAtom3328 chi ∧
      Fin15AnchoredAtom3332 chi ∧
      Fin15AnchoredAtom3343 chi ∧
      Fin15AnchoredAtom3364 chi ∧
      Fin15AnchoredAtom3420 chi ∧
      Fin15AnchoredAtom4581 chi) ∨
      (Fin15AnchoredAtom3328 chi ∧
      Fin15AnchoredAtom3333 chi ∧
      Fin15AnchoredAtom3344 chi ∧
      Fin15AnchoredAtom3365 chi ∧
      Fin15AnchoredAtom3421 chi ∧
      Fin15AnchoredAtom4582 chi))) ∨
      (((Fin15AnchoredAtom3329 chi ∧
      Fin15AnchoredAtom3331 chi ∧
      Fin15AnchoredAtom3346 chi ∧
      Fin15AnchoredAtom3367 chi ∧
      Fin15AnchoredAtom3423 chi ∧
      Fin15AnchoredAtom4584 chi) ∨
      (Fin15AnchoredAtom3329 chi ∧
      Fin15AnchoredAtom3332 chi ∧
      Fin15AnchoredAtom3347 chi ∧
      Fin15AnchoredAtom3368 chi ∧
      Fin15AnchoredAtom3424 chi ∧
      Fin15AnchoredAtom4585 chi)) ∨
      ((Fin15AnchoredAtom3329 chi ∧
      Fin15AnchoredAtom3333 chi ∧
      Fin15AnchoredAtom3348 chi ∧
      Fin15AnchoredAtom3369 chi ∧
      Fin15AnchoredAtom3425 chi ∧
      Fin15AnchoredAtom4586 chi) ∨
      (Fin15AnchoredAtom3331 chi ∧
      Fin15AnchoredAtom3332 chi ∧
      Fin15AnchoredAtom3352 chi ∧
      Fin15AnchoredAtom3373 chi ∧
      Fin15AnchoredAtom3429 chi ∧
      Fin15AnchoredAtom4590 chi)))) ∨
      ((((Fin15AnchoredAtom3331 chi ∧
      Fin15AnchoredAtom3333 chi ∧
      Fin15AnchoredAtom3353 chi ∧
      Fin15AnchoredAtom3374 chi ∧
      Fin15AnchoredAtom3430 chi ∧
      Fin15AnchoredAtom4591 chi) ∨
      (Fin15AnchoredAtom3332 chi ∧
      Fin15AnchoredAtom3333 chi ∧
      Fin15AnchoredAtom3354 chi ∧
      Fin15AnchoredAtom3375 chi ∧
      Fin15AnchoredAtom3431 chi ∧
      Fin15AnchoredAtom4592 chi)) ∨
      ((Fin15AnchoredAtom3334 chi ∧
      Fin15AnchoredAtom3337 chi ∧
      Fin15AnchoredAtom3342 chi ∧
      Fin15AnchoredAtom3378 chi ∧
      Fin15AnchoredAtom3434 chi ∧
      Fin15AnchoredAtom4595 chi) ∨
      (Fin15AnchoredAtom3335 chi ∧
      Fin15AnchoredAtom3338 chi ∧
      Fin15AnchoredAtom3347 chi ∧
      Fin15AnchoredAtom3383 chi ∧
      Fin15AnchoredAtom3439 chi ∧
      Fin15AnchoredAtom4600 chi))) ∨
      (((Fin15AnchoredAtom3337 chi ∧
      Fin15AnchoredAtom3338 chi ∧
      Fin15AnchoredAtom3352 chi ∧
      Fin15AnchoredAtom3388 chi ∧
      Fin15AnchoredAtom3444 chi ∧
      Fin15AnchoredAtom4605 chi) ∨
      (Fin15AnchoredAtom3340 chi ∧
      Fin15AnchoredAtom3342 chi ∧
      Fin15AnchoredAtom3346 chi ∧
      Fin15AnchoredAtom3392 chi ∧
      Fin15AnchoredAtom3448 chi ∧
      Fin15AnchoredAtom4609 chi)) ∨
      ((Fin15AnchoredAtom3340 chi ∧
      Fin15AnchoredAtom3343 chi ∧
      Fin15AnchoredAtom3347 chi ∧
      Fin15AnchoredAtom3393 chi ∧
      Fin15AnchoredAtom3449 chi ∧
      Fin15AnchoredAtom4610 chi) ∨
      (Fin15AnchoredAtom3340 chi ∧
      Fin15AnchoredAtom3344 chi ∧
      Fin15AnchoredAtom3348 chi ∧
      Fin15AnchoredAtom3394 chi ∧
      Fin15AnchoredAtom3450 chi ∧
      Fin15AnchoredAtom4611 chi))))) ∨
      (((((Fin15AnchoredAtom3342 chi ∧
      Fin15AnchoredAtom3343 chi ∧
      Fin15AnchoredAtom3352 chi ∧
      Fin15AnchoredAtom3398 chi ∧
      Fin15AnchoredAtom3454 chi ∧
      Fin15AnchoredAtom4615 chi) ∨
      (Fin15AnchoredAtom3342 chi ∧
      Fin15AnchoredAtom3344 chi ∧
      Fin15AnchoredAtom3353 chi ∧
      Fin15AnchoredAtom3399 chi ∧
      Fin15AnchoredAtom3455 chi ∧
      Fin15AnchoredAtom4616 chi)) ∨
      ((Fin15AnchoredAtom3343 chi ∧
      Fin15AnchoredAtom3344 chi ∧
      Fin15AnchoredAtom3354 chi ∧
      Fin15AnchoredAtom3400 chi ∧
      Fin15AnchoredAtom3456 chi ∧
      Fin15AnchoredAtom4617 chi) ∨
      (Fin15AnchoredAtom3346 chi ∧
      Fin15AnchoredAtom3347 chi ∧
      Fin15AnchoredAtom3352 chi ∧
      Fin15AnchoredAtom3404 chi ∧
      Fin15AnchoredAtom3460 chi ∧
      Fin15AnchoredAtom4621 chi))) ∨
      (((Fin15AnchoredAtom3346 chi ∧
      Fin15AnchoredAtom3348 chi ∧
      Fin15AnchoredAtom3353 chi ∧
      Fin15AnchoredAtom3405 chi ∧
      Fin15AnchoredAtom3461 chi ∧
      Fin15AnchoredAtom4622 chi) ∨
      (Fin15AnchoredAtom3347 chi ∧
      Fin15AnchoredAtom3348 chi ∧
      Fin15AnchoredAtom3354 chi ∧
      Fin15AnchoredAtom3406 chi ∧
      Fin15AnchoredAtom3462 chi ∧
      Fin15AnchoredAtom4623 chi)) ∨
      ((Fin15AnchoredAtom3352 chi ∧
      Fin15AnchoredAtom3353 chi ∧
      Fin15AnchoredAtom3354 chi ∧
      Fin15AnchoredAtom3410 chi ∧
      Fin15AnchoredAtom3466 chi ∧
      Fin15AnchoredAtom4627 chi) ∨
      (Fin15AnchoredAtom3355 chi ∧
      Fin15AnchoredAtom3356 chi ∧
      Fin15AnchoredAtom3361 chi ∧
      Fin15AnchoredAtom3376 chi ∧
      Fin15AnchoredAtom3467 chi ∧
      Fin15AnchoredAtom4628 chi)))) ∨
      ((((Fin15AnchoredAtom3361 chi ∧
      Fin15AnchoredAtom3363 chi ∧
      Fin15AnchoredAtom3367 chi ∧
      Fin15AnchoredAtom3392 chi ∧
      Fin15AnchoredAtom3483 chi ∧
      Fin15AnchoredAtom4644 chi) ∨
      (Fin15AnchoredAtom3361 chi ∧
      Fin15AnchoredAtom3364 chi ∧
      Fin15AnchoredAtom3368 chi ∧
      Fin15AnchoredAtom3393 chi ∧
      Fin15AnchoredAtom3484 chi ∧
      Fin15AnchoredAtom4645 chi)) ∨
      ((Fin15AnchoredAtom3361 chi ∧
      Fin15AnchoredAtom3365 chi ∧
      Fin15AnchoredAtom3369 chi ∧
      Fin15AnchoredAtom3394 chi ∧
      Fin15AnchoredAtom3485 chi ∧
      Fin15AnchoredAtom4646 chi) ∨
      (Fin15AnchoredAtom3363 chi ∧
      Fin15AnchoredAtom3364 chi ∧
      Fin15AnchoredAtom3373 chi ∧
      Fin15AnchoredAtom3398 chi ∧
      Fin15AnchoredAtom3489 chi ∧
      Fin15AnchoredAtom4650 chi))) ∨
      (((Fin15AnchoredAtom3363 chi ∧
      Fin15AnchoredAtom3365 chi ∧
      Fin15AnchoredAtom3374 chi ∧
      Fin15AnchoredAtom3399 chi ∧
      Fin15AnchoredAtom3490 chi ∧
      Fin15AnchoredAtom4651 chi) ∨
      (Fin15AnchoredAtom3364 chi ∧
      Fin15AnchoredAtom3365 chi ∧
      Fin15AnchoredAtom3375 chi ∧
      Fin15AnchoredAtom3400 chi ∧
      Fin15AnchoredAtom3491 chi ∧
      Fin15AnchoredAtom4652 chi)) ∨
      ((Fin15AnchoredAtom3367 chi ∧
      Fin15AnchoredAtom3368 chi ∧
      Fin15AnchoredAtom3373 chi ∧
      Fin15AnchoredAtom3404 chi ∧
      Fin15AnchoredAtom3495 chi ∧
      Fin15AnchoredAtom4656 chi) ∨
      (Fin15AnchoredAtom3367 chi ∧
      Fin15AnchoredAtom3369 chi ∧
      Fin15AnchoredAtom3374 chi ∧
      Fin15AnchoredAtom3405 chi ∧
      Fin15AnchoredAtom3496 chi ∧
      Fin15AnchoredAtom4657 chi))))))) ∨
      ((((((Fin15AnchoredAtom3368 chi ∧
      Fin15AnchoredAtom3369 chi ∧
      Fin15AnchoredAtom3375 chi ∧
      Fin15AnchoredAtom3406 chi ∧
      Fin15AnchoredAtom3497 chi ∧
      Fin15AnchoredAtom4658 chi) ∨
      ((Fin15AnchoredAtom3373 chi ∧
      Fin15AnchoredAtom3374 chi ∧
      Fin15AnchoredAtom3375 chi ∧
      Fin15AnchoredAtom3410 chi ∧
      Fin15AnchoredAtom3501 chi ∧
      Fin15AnchoredAtom4662 chi) ∨
      (Fin15AnchoredAtom3382 chi ∧
      Fin15AnchoredAtom3383 chi ∧
      Fin15AnchoredAtom3388 chi ∧
      Fin15AnchoredAtom3404 chi ∧
      Fin15AnchoredAtom3515 chi ∧
      Fin15AnchoredAtom4676 chi))) ∨
      (((Fin15AnchoredAtom3392 chi ∧
      Fin15AnchoredAtom3393 chi ∧
      Fin15AnchoredAtom3398 chi ∧
      Fin15AnchoredAtom3404 chi ∧
      Fin15AnchoredAtom3525 chi ∧
      Fin15AnchoredAtom4686 chi) ∨
      (Fin15AnchoredAtom3392 chi ∧
      Fin15AnchoredAtom3394 chi ∧
      Fin15AnchoredAtom3399 chi ∧
      Fin15AnchoredAtom3405 chi ∧
      Fin15AnchoredAtom3526 chi ∧
      Fin15AnchoredAtom4687 chi)) ∨
      ((Fin15AnchoredAtom3393 chi ∧
      Fin15AnchoredAtom3394 chi ∧
      Fin15AnchoredAtom3400 chi ∧
      Fin15AnchoredAtom3406 chi ∧
      Fin15AnchoredAtom3527 chi ∧
      Fin15AnchoredAtom4688 chi) ∨
      (Fin15AnchoredAtom3398 chi ∧
      Fin15AnchoredAtom3399 chi ∧
      Fin15AnchoredAtom3400 chi ∧
      Fin15AnchoredAtom3410 chi ∧
      Fin15AnchoredAtom3531 chi ∧
      Fin15AnchoredAtom4692 chi)))) ∨
      ((((Fin15AnchoredAtom3404 chi ∧
      Fin15AnchoredAtom3405 chi ∧
      Fin15AnchoredAtom3406 chi ∧
      Fin15AnchoredAtom3410 chi ∧
      Fin15AnchoredAtom3535 chi ∧
      Fin15AnchoredAtom4696 chi) ∨
      (Fin15AnchoredAtom3412 chi ∧
      Fin15AnchoredAtom3414 chi ∧
      Fin15AnchoredAtom3423 chi ∧
      Fin15AnchoredAtom3438 chi ∧
      Fin15AnchoredAtom3473 chi ∧
      Fin15AnchoredAtom4704 chi)) ∨
      ((Fin15AnchoredAtom3414 chi ∧
      Fin15AnchoredAtom3415 chi ∧
      Fin15AnchoredAtom3429 chi ∧
      Fin15AnchoredAtom3444 chi ∧
      Fin15AnchoredAtom3479 chi ∧
      Fin15AnchoredAtom4710 chi) ∨
      (Fin15AnchoredAtom3417 chi ∧
      Fin15AnchoredAtom3419 chi ∧
      Fin15AnchoredAtom3423 chi ∧
      Fin15AnchoredAtom3448 chi ∧
      Fin15AnchoredAtom3483 chi ∧
      Fin15AnchoredAtom4714 chi))) ∨
      (((Fin15AnchoredAtom3417 chi ∧
      Fin15AnchoredAtom3420 chi ∧
      Fin15AnchoredAtom3424 chi ∧
      Fin15AnchoredAtom3449 chi ∧
      Fin15AnchoredAtom3484 chi ∧
      Fin15AnchoredAtom4715 chi) ∨
      (Fin15AnchoredAtom3417 chi ∧
      Fin15AnchoredAtom3421 chi ∧
      Fin15AnchoredAtom3425 chi ∧
      Fin15AnchoredAtom3450 chi ∧
      Fin15AnchoredAtom3485 chi ∧
      Fin15AnchoredAtom4716 chi)) ∨
      ((Fin15AnchoredAtom3418 chi ∧
      Fin15AnchoredAtom3419 chi ∧
      Fin15AnchoredAtom3426 chi ∧
      Fin15AnchoredAtom3451 chi ∧
      Fin15AnchoredAtom3486 chi ∧
      Fin15AnchoredAtom4717 chi) ∨
      (Fin15AnchoredAtom3419 chi ∧
      Fin15AnchoredAtom3420 chi ∧
      Fin15AnchoredAtom3429 chi ∧
      Fin15AnchoredAtom3454 chi ∧
      Fin15AnchoredAtom3489 chi ∧
      Fin15AnchoredAtom4720 chi))))) ∨
      (((((Fin15AnchoredAtom3419 chi ∧
      Fin15AnchoredAtom3421 chi ∧
      Fin15AnchoredAtom3430 chi ∧
      Fin15AnchoredAtom3455 chi ∧
      Fin15AnchoredAtom3490 chi ∧
      Fin15AnchoredAtom4721 chi) ∨
      (Fin15AnchoredAtom3420 chi ∧
      Fin15AnchoredAtom3421 chi ∧
      Fin15AnchoredAtom3431 chi ∧
      Fin15AnchoredAtom3456 chi ∧
      Fin15AnchoredAtom3491 chi ∧
      Fin15AnchoredAtom4722 chi)) ∨
      ((Fin15AnchoredAtom3423 chi ∧
      Fin15AnchoredAtom3424 chi ∧
      Fin15AnchoredAtom3429 chi ∧
      Fin15AnchoredAtom3460 chi ∧
      Fin15AnchoredAtom3495 chi ∧
      Fin15AnchoredAtom4726 chi) ∨
      (Fin15AnchoredAtom3423 chi ∧
      Fin15AnchoredAtom3425 chi ∧
      Fin15AnchoredAtom3430 chi ∧
      Fin15AnchoredAtom3461 chi ∧
      Fin15AnchoredAtom3496 chi ∧
      Fin15AnchoredAtom4727 chi))) ∨
      (((Fin15AnchoredAtom3424 chi ∧
      Fin15AnchoredAtom3425 chi ∧
      Fin15AnchoredAtom3431 chi ∧
      Fin15AnchoredAtom3462 chi ∧
      Fin15AnchoredAtom3497 chi ∧
      Fin15AnchoredAtom4728 chi) ∨
      (Fin15AnchoredAtom3429 chi ∧
      Fin15AnchoredAtom3430 chi ∧
      Fin15AnchoredAtom3431 chi ∧
      Fin15AnchoredAtom3466 chi ∧
      Fin15AnchoredAtom3501 chi ∧
      Fin15AnchoredAtom4732 chi)) ∨
      ((Fin15AnchoredAtom3434 chi ∧
      Fin15AnchoredAtom3435 chi ∧
      Fin15AnchoredAtom3444 chi ∧
      Fin15AnchoredAtom3454 chi ∧
      Fin15AnchoredAtom3509 chi ∧
      Fin15AnchoredAtom4740 chi) ∨
      (Fin15AnchoredAtom3438 chi ∧
      Fin15AnchoredAtom3439 chi ∧
      Fin15AnchoredAtom3444 chi ∧
      Fin15AnchoredAtom3460 chi ∧
      Fin15AnchoredAtom3515 chi ∧
      Fin15AnchoredAtom4746 chi)))) ∨
      ((((Fin15AnchoredAtom3448 chi ∧
      Fin15AnchoredAtom3449 chi ∧
      Fin15AnchoredAtom3454 chi ∧
      Fin15AnchoredAtom3460 chi ∧
      Fin15AnchoredAtom3525 chi ∧
      Fin15AnchoredAtom4756 chi) ∨
      (Fin15AnchoredAtom3448 chi ∧
      Fin15AnchoredAtom3450 chi ∧
      Fin15AnchoredAtom3455 chi ∧
      Fin15AnchoredAtom3461 chi ∧
      Fin15AnchoredAtom3526 chi ∧
      Fin15AnchoredAtom4757 chi)) ∨
      ((Fin15AnchoredAtom3449 chi ∧
      Fin15AnchoredAtom3450 chi ∧
      Fin15AnchoredAtom3456 chi ∧
      Fin15AnchoredAtom3462 chi ∧
      Fin15AnchoredAtom3527 chi ∧
      Fin15AnchoredAtom4758 chi) ∨
      (Fin15AnchoredAtom3454 chi ∧
      Fin15AnchoredAtom3455 chi ∧
      Fin15AnchoredAtom3456 chi ∧
      Fin15AnchoredAtom3466 chi ∧
      Fin15AnchoredAtom3531 chi ∧
      Fin15AnchoredAtom4762 chi))) ∨
      (((Fin15AnchoredAtom3460 chi ∧
      Fin15AnchoredAtom3461 chi ∧
      Fin15AnchoredAtom3462 chi ∧
      Fin15AnchoredAtom3466 chi ∧
      Fin15AnchoredAtom3535 chi ∧
      Fin15AnchoredAtom4766 chi) ∨
      (Fin15AnchoredAtom3483 chi ∧
      Fin15AnchoredAtom3484 chi ∧
      Fin15AnchoredAtom3489 chi ∧
      Fin15AnchoredAtom3495 chi ∧
      Fin15AnchoredAtom3525 chi ∧
      Fin15AnchoredAtom4791 chi)) ∨
      ((Fin15AnchoredAtom3483 chi ∧
      Fin15AnchoredAtom3485 chi ∧
      Fin15AnchoredAtom3490 chi ∧
      Fin15AnchoredAtom3496 chi ∧
      Fin15AnchoredAtom3526 chi ∧
      Fin15AnchoredAtom4792 chi) ∨
      (Fin15AnchoredAtom3484 chi ∧
      Fin15AnchoredAtom3485 chi ∧
      Fin15AnchoredAtom3491 chi ∧
      Fin15AnchoredAtom3497 chi ∧
      Fin15AnchoredAtom3527 chi ∧
      Fin15AnchoredAtom4793 chi)))))) ∨
      ((((((Fin15AnchoredAtom3489 chi ∧
      Fin15AnchoredAtom3490 chi ∧
      Fin15AnchoredAtom3491 chi ∧
      Fin15AnchoredAtom3501 chi ∧
      Fin15AnchoredAtom3531 chi ∧
      Fin15AnchoredAtom4797 chi) ∨
      (Fin15AnchoredAtom3495 chi ∧
      Fin15AnchoredAtom3496 chi ∧
      Fin15AnchoredAtom3497 chi ∧
      Fin15AnchoredAtom3501 chi ∧
      Fin15AnchoredAtom3535 chi ∧
      Fin15AnchoredAtom4801 chi)) ∨
      ((Fin15AnchoredAtom3503 chi ∧
      Fin15AnchoredAtom3504 chi ∧
      Fin15AnchoredAtom3509 chi ∧
      Fin15AnchoredAtom3515 chi ∧
      Fin15AnchoredAtom3525 chi ∧
      Fin15AnchoredAtom4806 chi) ∨
      (Fin15AnchoredAtom3525 chi ∧
      Fin15AnchoredAtom3526 chi ∧
      Fin15AnchoredAtom3527 chi ∧
      Fin15AnchoredAtom3531 chi ∧
      Fin15AnchoredAtom3535 chi ∧
      Fin15AnchoredAtom4821 chi))) ∨
      (((Fin15AnchoredAtom3537 chi ∧
      Fin15AnchoredAtom3538 chi ∧
      Fin15AnchoredAtom3546 chi ∧
      Fin15AnchoredAtom3582 chi ∧
      Fin15AnchoredAtom3702 chi ∧
      Fin15AnchoredAtom4032 chi) ∨
      (Fin15AnchoredAtom3537 chi ∧
      Fin15AnchoredAtom3540 chi ∧
      Fin15AnchoredAtom3548 chi ∧
      Fin15AnchoredAtom3584 chi ∧
      Fin15AnchoredAtom3704 chi ∧
      Fin15AnchoredAtom4034 chi)) ∨
      ((Fin15AnchoredAtom3537 chi ∧
      Fin15AnchoredAtom3541 chi ∧
      Fin15AnchoredAtom3549 chi ∧
      Fin15AnchoredAtom3585 chi ∧
      Fin15AnchoredAtom3705 chi ∧
      Fin15AnchoredAtom4035 chi) ∨
      (Fin15AnchoredAtom3537 chi ∧
      Fin15AnchoredAtom3543 chi ∧
      Fin15AnchoredAtom3551 chi ∧
      Fin15AnchoredAtom3587 chi ∧
      Fin15AnchoredAtom3707 chi ∧
      Fin15AnchoredAtom4037 chi)))) ∨
      ((((Fin15AnchoredAtom3537 chi ∧
      Fin15AnchoredAtom3544 chi ∧
      Fin15AnchoredAtom3552 chi ∧
      Fin15AnchoredAtom3588 chi ∧
      Fin15AnchoredAtom3708 chi ∧
      Fin15AnchoredAtom4038 chi) ∨
      (Fin15AnchoredAtom3537 chi ∧
      Fin15AnchoredAtom3545 chi ∧
      Fin15AnchoredAtom3553 chi ∧
      Fin15AnchoredAtom3589 chi ∧
      Fin15AnchoredAtom3709 chi ∧
      Fin15AnchoredAtom4039 chi)) ∨
      ((Fin15AnchoredAtom3538 chi ∧
      Fin15AnchoredAtom3540 chi ∧
      Fin15AnchoredAtom3555 chi ∧
      Fin15AnchoredAtom3591 chi ∧
      Fin15AnchoredAtom3711 chi ∧
      Fin15AnchoredAtom4041 chi) ∨
      (Fin15AnchoredAtom3538 chi ∧
      Fin15AnchoredAtom3541 chi ∧
      Fin15AnchoredAtom3556 chi ∧
      Fin15AnchoredAtom3592 chi ∧
      Fin15AnchoredAtom3712 chi ∧
      Fin15AnchoredAtom4042 chi))) ∨
      (((Fin15AnchoredAtom3538 chi ∧
      Fin15AnchoredAtom3543 chi ∧
      Fin15AnchoredAtom3558 chi ∧
      Fin15AnchoredAtom3594 chi ∧
      Fin15AnchoredAtom3714 chi ∧
      Fin15AnchoredAtom4044 chi) ∨
      (Fin15AnchoredAtom3538 chi ∧
      Fin15AnchoredAtom3544 chi ∧
      Fin15AnchoredAtom3559 chi ∧
      Fin15AnchoredAtom3595 chi ∧
      Fin15AnchoredAtom3715 chi ∧
      Fin15AnchoredAtom4045 chi)) ∨
      ((Fin15AnchoredAtom3538 chi ∧
      Fin15AnchoredAtom3545 chi ∧
      Fin15AnchoredAtom3560 chi ∧
      Fin15AnchoredAtom3596 chi ∧
      Fin15AnchoredAtom3716 chi ∧
      Fin15AnchoredAtom4046 chi) ∨
      (Fin15AnchoredAtom3540 chi ∧
      Fin15AnchoredAtom3541 chi ∧
      Fin15AnchoredAtom3567 chi ∧
      Fin15AnchoredAtom3603 chi ∧
      Fin15AnchoredAtom3723 chi ∧
      Fin15AnchoredAtom4053 chi))))) ∨
      (((((Fin15AnchoredAtom3540 chi ∧
      Fin15AnchoredAtom3543 chi ∧
      Fin15AnchoredAtom3569 chi ∧
      Fin15AnchoredAtom3605 chi ∧
      Fin15AnchoredAtom3725 chi ∧
      Fin15AnchoredAtom4055 chi) ∨
      (Fin15AnchoredAtom3540 chi ∧
      Fin15AnchoredAtom3544 chi ∧
      Fin15AnchoredAtom3570 chi ∧
      Fin15AnchoredAtom3606 chi ∧
      Fin15AnchoredAtom3726 chi ∧
      Fin15AnchoredAtom4056 chi)) ∨
      ((Fin15AnchoredAtom3540 chi ∧
      Fin15AnchoredAtom3545 chi ∧
      Fin15AnchoredAtom3571 chi ∧
      Fin15AnchoredAtom3607 chi ∧
      Fin15AnchoredAtom3727 chi ∧
      Fin15AnchoredAtom4057 chi) ∨
      (Fin15AnchoredAtom3541 chi ∧
      Fin15AnchoredAtom3543 chi ∧
      Fin15AnchoredAtom3573 chi ∧
      Fin15AnchoredAtom3609 chi ∧
      Fin15AnchoredAtom3729 chi ∧
      Fin15AnchoredAtom4059 chi))) ∨
      (((Fin15AnchoredAtom3541 chi ∧
      Fin15AnchoredAtom3544 chi ∧
      Fin15AnchoredAtom3574 chi ∧
      Fin15AnchoredAtom3610 chi ∧
      Fin15AnchoredAtom3730 chi ∧
      Fin15AnchoredAtom4060 chi) ∨
      (Fin15AnchoredAtom3541 chi ∧
      Fin15AnchoredAtom3545 chi ∧
      Fin15AnchoredAtom3575 chi ∧
      Fin15AnchoredAtom3611 chi ∧
      Fin15AnchoredAtom3731 chi ∧
      Fin15AnchoredAtom4061 chi)) ∨
      ((Fin15AnchoredAtom3543 chi ∧
      Fin15AnchoredAtom3544 chi ∧
      Fin15AnchoredAtom3579 chi ∧
      Fin15AnchoredAtom3615 chi ∧
      Fin15AnchoredAtom3735 chi ∧
      Fin15AnchoredAtom4065 chi) ∨
      (Fin15AnchoredAtom3543 chi ∧
      Fin15AnchoredAtom3545 chi ∧
      Fin15AnchoredAtom3580 chi ∧
      Fin15AnchoredAtom3616 chi ∧
      Fin15AnchoredAtom3736 chi ∧
      Fin15AnchoredAtom4066 chi)))) ∨
      ((((Fin15AnchoredAtom3544 chi ∧
      Fin15AnchoredAtom3545 chi ∧
      Fin15AnchoredAtom3581 chi ∧
      Fin15AnchoredAtom3617 chi ∧
      Fin15AnchoredAtom3737 chi ∧
      Fin15AnchoredAtom4067 chi) ∨
      (Fin15AnchoredAtom3546 chi ∧
      Fin15AnchoredAtom3548 chi ∧
      Fin15AnchoredAtom3555 chi ∧
      Fin15AnchoredAtom3619 chi ∧
      Fin15AnchoredAtom3739 chi ∧
      Fin15AnchoredAtom4069 chi)) ∨
      ((Fin15AnchoredAtom3546 chi ∧
      Fin15AnchoredAtom3549 chi ∧
      Fin15AnchoredAtom3556 chi ∧
      Fin15AnchoredAtom3620 chi ∧
      Fin15AnchoredAtom3740 chi ∧
      Fin15AnchoredAtom4070 chi) ∨
      (Fin15AnchoredAtom3546 chi ∧
      Fin15AnchoredAtom3551 chi ∧
      Fin15AnchoredAtom3558 chi ∧
      Fin15AnchoredAtom3622 chi ∧
      Fin15AnchoredAtom3742 chi ∧
      Fin15AnchoredAtom4072 chi))) ∨
      (((Fin15AnchoredAtom3546 chi ∧
      Fin15AnchoredAtom3552 chi ∧
      Fin15AnchoredAtom3559 chi ∧
      Fin15AnchoredAtom3623 chi ∧
      Fin15AnchoredAtom3743 chi ∧
      Fin15AnchoredAtom4073 chi) ∨
      (Fin15AnchoredAtom3546 chi ∧
      Fin15AnchoredAtom3553 chi ∧
      Fin15AnchoredAtom3560 chi ∧
      Fin15AnchoredAtom3624 chi ∧
      Fin15AnchoredAtom3744 chi ∧
      Fin15AnchoredAtom4074 chi)) ∨
      ((Fin15AnchoredAtom3548 chi ∧
      Fin15AnchoredAtom3549 chi ∧
      Fin15AnchoredAtom3567 chi ∧
      Fin15AnchoredAtom3631 chi ∧
      Fin15AnchoredAtom3751 chi ∧
      Fin15AnchoredAtom4081 chi) ∨
      (Fin15AnchoredAtom3548 chi ∧
      Fin15AnchoredAtom3551 chi ∧
      Fin15AnchoredAtom3569 chi ∧
      Fin15AnchoredAtom3633 chi ∧
      Fin15AnchoredAtom3753 chi ∧
      Fin15AnchoredAtom4083 chi)))))))) ∨
      (((((((Fin15AnchoredAtom3548 chi ∧
      Fin15AnchoredAtom3552 chi ∧
      Fin15AnchoredAtom3570 chi ∧
      Fin15AnchoredAtom3634 chi ∧
      Fin15AnchoredAtom3754 chi ∧
      Fin15AnchoredAtom4084 chi) ∨
      ((Fin15AnchoredAtom3548 chi ∧
      Fin15AnchoredAtom3553 chi ∧
      Fin15AnchoredAtom3571 chi ∧
      Fin15AnchoredAtom3635 chi ∧
      Fin15AnchoredAtom3755 chi ∧
      Fin15AnchoredAtom4085 chi) ∨
      (Fin15AnchoredAtom3549 chi ∧
      Fin15AnchoredAtom3551 chi ∧
      Fin15AnchoredAtom3573 chi ∧
      Fin15AnchoredAtom3637 chi ∧
      Fin15AnchoredAtom3757 chi ∧
      Fin15AnchoredAtom4087 chi))) ∨
      (((Fin15AnchoredAtom3549 chi ∧
      Fin15AnchoredAtom3552 chi ∧
      Fin15AnchoredAtom3574 chi ∧
      Fin15AnchoredAtom3638 chi ∧
      Fin15AnchoredAtom3758 chi ∧
      Fin15AnchoredAtom4088 chi) ∨
      (Fin15AnchoredAtom3549 chi ∧
      Fin15AnchoredAtom3553 chi ∧
      Fin15AnchoredAtom3575 chi ∧
      Fin15AnchoredAtom3639 chi ∧
      Fin15AnchoredAtom3759 chi ∧
      Fin15AnchoredAtom4089 chi)) ∨
      ((Fin15AnchoredAtom3551 chi ∧
      Fin15AnchoredAtom3552 chi ∧
      Fin15AnchoredAtom3579 chi ∧
      Fin15AnchoredAtom3643 chi ∧
      Fin15AnchoredAtom3763 chi ∧
      Fin15AnchoredAtom4093 chi) ∨
      (Fin15AnchoredAtom3551 chi ∧
      Fin15AnchoredAtom3553 chi ∧
      Fin15AnchoredAtom3580 chi ∧
      Fin15AnchoredAtom3644 chi ∧
      Fin15AnchoredAtom3764 chi ∧
      Fin15AnchoredAtom4094 chi)))) ∨
      ((((Fin15AnchoredAtom3552 chi ∧
      Fin15AnchoredAtom3553 chi ∧
      Fin15AnchoredAtom3581 chi ∧
      Fin15AnchoredAtom3645 chi ∧
      Fin15AnchoredAtom3765 chi ∧
      Fin15AnchoredAtom4095 chi) ∨
      (Fin15AnchoredAtom3555 chi ∧
      Fin15AnchoredAtom3556 chi ∧
      Fin15AnchoredAtom3567 chi ∧
      Fin15AnchoredAtom3652 chi ∧
      Fin15AnchoredAtom3772 chi ∧
      Fin15AnchoredAtom4102 chi)) ∨
      ((Fin15AnchoredAtom3555 chi ∧
      Fin15AnchoredAtom3558 chi ∧
      Fin15AnchoredAtom3569 chi ∧
      Fin15AnchoredAtom3654 chi ∧
      Fin15AnchoredAtom3774 chi ∧
      Fin15AnchoredAtom4104 chi) ∨
      (Fin15AnchoredAtom3555 chi ∧
      Fin15AnchoredAtom3559 chi ∧
      Fin15AnchoredAtom3570 chi ∧
      Fin15AnchoredAtom3655 chi ∧
      Fin15AnchoredAtom3775 chi ∧
      Fin15AnchoredAtom4105 chi))) ∨
      (((Fin15AnchoredAtom3555 chi ∧
      Fin15AnchoredAtom3560 chi ∧
      Fin15AnchoredAtom3571 chi ∧
      Fin15AnchoredAtom3656 chi ∧
      Fin15AnchoredAtom3776 chi ∧
      Fin15AnchoredAtom4106 chi) ∨
      (Fin15AnchoredAtom3556 chi ∧
      Fin15AnchoredAtom3558 chi ∧
      Fin15AnchoredAtom3573 chi ∧
      Fin15AnchoredAtom3658 chi ∧
      Fin15AnchoredAtom3778 chi ∧
      Fin15AnchoredAtom4108 chi)) ∨
      ((Fin15AnchoredAtom3556 chi ∧
      Fin15AnchoredAtom3559 chi ∧
      Fin15AnchoredAtom3574 chi ∧
      Fin15AnchoredAtom3659 chi ∧
      Fin15AnchoredAtom3779 chi ∧
      Fin15AnchoredAtom4109 chi) ∨
      (Fin15AnchoredAtom3556 chi ∧
      Fin15AnchoredAtom3560 chi ∧
      Fin15AnchoredAtom3575 chi ∧
      Fin15AnchoredAtom3660 chi ∧
      Fin15AnchoredAtom3780 chi ∧
      Fin15AnchoredAtom4110 chi))))) ∨
      (((((Fin15AnchoredAtom3558 chi ∧
      Fin15AnchoredAtom3559 chi ∧
      Fin15AnchoredAtom3579 chi ∧
      Fin15AnchoredAtom3664 chi ∧
      Fin15AnchoredAtom3784 chi ∧
      Fin15AnchoredAtom4114 chi) ∨
      (Fin15AnchoredAtom3558 chi ∧
      Fin15AnchoredAtom3560 chi ∧
      Fin15AnchoredAtom3580 chi ∧
      Fin15AnchoredAtom3665 chi ∧
      Fin15AnchoredAtom3785 chi ∧
      Fin15AnchoredAtom4115 chi)) ∨
      ((Fin15AnchoredAtom3559 chi ∧
      Fin15AnchoredAtom3560 chi ∧
      Fin15AnchoredAtom3581 chi ∧
      Fin15AnchoredAtom3666 chi ∧
      Fin15AnchoredAtom3786 chi ∧
      Fin15AnchoredAtom4116 chi) ∨
      (Fin15AnchoredAtom3567 chi ∧
      Fin15AnchoredAtom3569 chi ∧
      Fin15AnchoredAtom3573 chi ∧
      Fin15AnchoredAtom3683 chi ∧
      Fin15AnchoredAtom3803 chi ∧
      Fin15AnchoredAtom4133 chi))) ∨
      (((Fin15AnchoredAtom3567 chi ∧
      Fin15AnchoredAtom3570 chi ∧
      Fin15AnchoredAtom3574 chi ∧
      Fin15AnchoredAtom3684 chi ∧
      Fin15AnchoredAtom3804 chi ∧
      Fin15AnchoredAtom4134 chi) ∨
      (Fin15AnchoredAtom3567 chi ∧
      Fin15AnchoredAtom3571 chi ∧
      Fin15AnchoredAtom3575 chi ∧
      Fin15AnchoredAtom3685 chi ∧
      Fin15AnchoredAtom3805 chi ∧
      Fin15AnchoredAtom4135 chi)) ∨
      ((Fin15AnchoredAtom3569 chi ∧
      Fin15AnchoredAtom3570 chi ∧
      Fin15AnchoredAtom3579 chi ∧
      Fin15AnchoredAtom3689 chi ∧
      Fin15AnchoredAtom3809 chi ∧
      Fin15AnchoredAtom4139 chi) ∨
      (Fin15AnchoredAtom3569 chi ∧
      Fin15AnchoredAtom3571 chi ∧
      Fin15AnchoredAtom3580 chi ∧
      Fin15AnchoredAtom3690 chi ∧
      Fin15AnchoredAtom3810 chi ∧
      Fin15AnchoredAtom4140 chi)))) ∨
      ((((Fin15AnchoredAtom3570 chi ∧
      Fin15AnchoredAtom3571 chi ∧
      Fin15AnchoredAtom3581 chi ∧
      Fin15AnchoredAtom3691 chi ∧
      Fin15AnchoredAtom3811 chi ∧
      Fin15AnchoredAtom4141 chi) ∨
      (Fin15AnchoredAtom3573 chi ∧
      Fin15AnchoredAtom3574 chi ∧
      Fin15AnchoredAtom3579 chi ∧
      Fin15AnchoredAtom3695 chi ∧
      Fin15AnchoredAtom3815 chi ∧
      Fin15AnchoredAtom4145 chi)) ∨
      ((Fin15AnchoredAtom3573 chi ∧
      Fin15AnchoredAtom3575 chi ∧
      Fin15AnchoredAtom3580 chi ∧
      Fin15AnchoredAtom3696 chi ∧
      Fin15AnchoredAtom3816 chi ∧
      Fin15AnchoredAtom4146 chi) ∨
      (Fin15AnchoredAtom3574 chi ∧
      Fin15AnchoredAtom3575 chi ∧
      Fin15AnchoredAtom3581 chi ∧
      Fin15AnchoredAtom3697 chi ∧
      Fin15AnchoredAtom3817 chi ∧
      Fin15AnchoredAtom4147 chi))) ∨
      (((Fin15AnchoredAtom3579 chi ∧
      Fin15AnchoredAtom3580 chi ∧
      Fin15AnchoredAtom3581 chi ∧
      Fin15AnchoredAtom3701 chi ∧
      Fin15AnchoredAtom3821 chi ∧
      Fin15AnchoredAtom4151 chi) ∨
      (Fin15AnchoredAtom3582 chi ∧
      Fin15AnchoredAtom3584 chi ∧
      Fin15AnchoredAtom3591 chi ∧
      Fin15AnchoredAtom3619 chi ∧
      Fin15AnchoredAtom3823 chi ∧
      Fin15AnchoredAtom4153 chi)) ∨
      ((Fin15AnchoredAtom3582 chi ∧
      Fin15AnchoredAtom3585 chi ∧
      Fin15AnchoredAtom3592 chi ∧
      Fin15AnchoredAtom3620 chi ∧
      Fin15AnchoredAtom3824 chi ∧
      Fin15AnchoredAtom4154 chi) ∨
      (Fin15AnchoredAtom3582 chi ∧
      Fin15AnchoredAtom3587 chi ∧
      Fin15AnchoredAtom3594 chi ∧
      Fin15AnchoredAtom3622 chi ∧
      Fin15AnchoredAtom3826 chi ∧
      Fin15AnchoredAtom4156 chi)))))) ∨
      ((((((Fin15AnchoredAtom3582 chi ∧
      Fin15AnchoredAtom3588 chi ∧
      Fin15AnchoredAtom3595 chi ∧
      Fin15AnchoredAtom3623 chi ∧
      Fin15AnchoredAtom3827 chi ∧
      Fin15AnchoredAtom4157 chi) ∨
      (Fin15AnchoredAtom3582 chi ∧
      Fin15AnchoredAtom3589 chi ∧
      Fin15AnchoredAtom3596 chi ∧
      Fin15AnchoredAtom3624 chi ∧
      Fin15AnchoredAtom3828 chi ∧
      Fin15AnchoredAtom4158 chi)) ∨
      ((Fin15AnchoredAtom3584 chi ∧
      Fin15AnchoredAtom3585 chi ∧
      Fin15AnchoredAtom3603 chi ∧
      Fin15AnchoredAtom3631 chi ∧
      Fin15AnchoredAtom3835 chi ∧
      Fin15AnchoredAtom4165 chi) ∨
      (Fin15AnchoredAtom3584 chi ∧
      Fin15AnchoredAtom3587 chi ∧
      Fin15AnchoredAtom3605 chi ∧
      Fin15AnchoredAtom3633 chi ∧
      Fin15AnchoredAtom3837 chi ∧
      Fin15AnchoredAtom4167 chi))) ∨
      (((Fin15AnchoredAtom3584 chi ∧
      Fin15AnchoredAtom3588 chi ∧
      Fin15AnchoredAtom3606 chi ∧
      Fin15AnchoredAtom3634 chi ∧
      Fin15AnchoredAtom3838 chi ∧
      Fin15AnchoredAtom4168 chi) ∨
      (Fin15AnchoredAtom3584 chi ∧
      Fin15AnchoredAtom3589 chi ∧
      Fin15AnchoredAtom3607 chi ∧
      Fin15AnchoredAtom3635 chi ∧
      Fin15AnchoredAtom3839 chi ∧
      Fin15AnchoredAtom4169 chi)) ∨
      ((Fin15AnchoredAtom3585 chi ∧
      Fin15AnchoredAtom3587 chi ∧
      Fin15AnchoredAtom3609 chi ∧
      Fin15AnchoredAtom3637 chi ∧
      Fin15AnchoredAtom3841 chi ∧
      Fin15AnchoredAtom4171 chi) ∨
      (Fin15AnchoredAtom3585 chi ∧
      Fin15AnchoredAtom3588 chi ∧
      Fin15AnchoredAtom3610 chi ∧
      Fin15AnchoredAtom3638 chi ∧
      Fin15AnchoredAtom3842 chi ∧
      Fin15AnchoredAtom4172 chi)))) ∨
      ((((Fin15AnchoredAtom3585 chi ∧
      Fin15AnchoredAtom3589 chi ∧
      Fin15AnchoredAtom3611 chi ∧
      Fin15AnchoredAtom3639 chi ∧
      Fin15AnchoredAtom3843 chi ∧
      Fin15AnchoredAtom4173 chi) ∨
      (Fin15AnchoredAtom3587 chi ∧
      Fin15AnchoredAtom3588 chi ∧
      Fin15AnchoredAtom3615 chi ∧
      Fin15AnchoredAtom3643 chi ∧
      Fin15AnchoredAtom3847 chi ∧
      Fin15AnchoredAtom4177 chi)) ∨
      ((Fin15AnchoredAtom3587 chi ∧
      Fin15AnchoredAtom3589 chi ∧
      Fin15AnchoredAtom3616 chi ∧
      Fin15AnchoredAtom3644 chi ∧
      Fin15AnchoredAtom3848 chi ∧
      Fin15AnchoredAtom4178 chi) ∨
      (Fin15AnchoredAtom3588 chi ∧
      Fin15AnchoredAtom3589 chi ∧
      Fin15AnchoredAtom3617 chi ∧
      Fin15AnchoredAtom3645 chi ∧
      Fin15AnchoredAtom3849 chi ∧
      Fin15AnchoredAtom4179 chi))) ∨
      (((Fin15AnchoredAtom3591 chi ∧
      Fin15AnchoredAtom3592 chi ∧
      Fin15AnchoredAtom3603 chi ∧
      Fin15AnchoredAtom3652 chi ∧
      Fin15AnchoredAtom3856 chi ∧
      Fin15AnchoredAtom4186 chi) ∨
      (Fin15AnchoredAtom3591 chi ∧
      Fin15AnchoredAtom3594 chi ∧
      Fin15AnchoredAtom3605 chi ∧
      Fin15AnchoredAtom3654 chi ∧
      Fin15AnchoredAtom3858 chi ∧
      Fin15AnchoredAtom4188 chi)) ∨
      ((Fin15AnchoredAtom3591 chi ∧
      Fin15AnchoredAtom3595 chi ∧
      Fin15AnchoredAtom3606 chi ∧
      Fin15AnchoredAtom3655 chi ∧
      Fin15AnchoredAtom3859 chi ∧
      Fin15AnchoredAtom4189 chi) ∨
      (Fin15AnchoredAtom3591 chi ∧
      Fin15AnchoredAtom3596 chi ∧
      Fin15AnchoredAtom3607 chi ∧
      Fin15AnchoredAtom3656 chi ∧
      Fin15AnchoredAtom3860 chi ∧
      Fin15AnchoredAtom4190 chi))))) ∨
      (((((Fin15AnchoredAtom3592 chi ∧
      Fin15AnchoredAtom3594 chi ∧
      Fin15AnchoredAtom3609 chi ∧
      Fin15AnchoredAtom3658 chi ∧
      Fin15AnchoredAtom3862 chi ∧
      Fin15AnchoredAtom4192 chi) ∨
      (Fin15AnchoredAtom3592 chi ∧
      Fin15AnchoredAtom3595 chi ∧
      Fin15AnchoredAtom3610 chi ∧
      Fin15AnchoredAtom3659 chi ∧
      Fin15AnchoredAtom3863 chi ∧
      Fin15AnchoredAtom4193 chi)) ∨
      ((Fin15AnchoredAtom3592 chi ∧
      Fin15AnchoredAtom3596 chi ∧
      Fin15AnchoredAtom3611 chi ∧
      Fin15AnchoredAtom3660 chi ∧
      Fin15AnchoredAtom3864 chi ∧
      Fin15AnchoredAtom4194 chi) ∨
      (Fin15AnchoredAtom3594 chi ∧
      Fin15AnchoredAtom3595 chi ∧
      Fin15AnchoredAtom3615 chi ∧
      Fin15AnchoredAtom3664 chi ∧
      Fin15AnchoredAtom3868 chi ∧
      Fin15AnchoredAtom4198 chi))) ∨
      (((Fin15AnchoredAtom3594 chi ∧
      Fin15AnchoredAtom3596 chi ∧
      Fin15AnchoredAtom3616 chi ∧
      Fin15AnchoredAtom3665 chi ∧
      Fin15AnchoredAtom3869 chi ∧
      Fin15AnchoredAtom4199 chi) ∨
      (Fin15AnchoredAtom3595 chi ∧
      Fin15AnchoredAtom3596 chi ∧
      Fin15AnchoredAtom3617 chi ∧
      Fin15AnchoredAtom3666 chi ∧
      Fin15AnchoredAtom3870 chi ∧
      Fin15AnchoredAtom4200 chi)) ∨
      ((Fin15AnchoredAtom3603 chi ∧
      Fin15AnchoredAtom3605 chi ∧
      Fin15AnchoredAtom3609 chi ∧
      Fin15AnchoredAtom3683 chi ∧
      Fin15AnchoredAtom3887 chi ∧
      Fin15AnchoredAtom4217 chi) ∨
      (Fin15AnchoredAtom3603 chi ∧
      Fin15AnchoredAtom3606 chi ∧
      Fin15AnchoredAtom3610 chi ∧
      Fin15AnchoredAtom3684 chi ∧
      Fin15AnchoredAtom3888 chi ∧
      Fin15AnchoredAtom4218 chi)))) ∨
      ((((Fin15AnchoredAtom3603 chi ∧
      Fin15AnchoredAtom3607 chi ∧
      Fin15AnchoredAtom3611 chi ∧
      Fin15AnchoredAtom3685 chi ∧
      Fin15AnchoredAtom3889 chi ∧
      Fin15AnchoredAtom4219 chi) ∨
      (Fin15AnchoredAtom3605 chi ∧
      Fin15AnchoredAtom3606 chi ∧
      Fin15AnchoredAtom3615 chi ∧
      Fin15AnchoredAtom3689 chi ∧
      Fin15AnchoredAtom3893 chi ∧
      Fin15AnchoredAtom4223 chi)) ∨
      ((Fin15AnchoredAtom3605 chi ∧
      Fin15AnchoredAtom3607 chi ∧
      Fin15AnchoredAtom3616 chi ∧
      Fin15AnchoredAtom3690 chi ∧
      Fin15AnchoredAtom3894 chi ∧
      Fin15AnchoredAtom4224 chi) ∨
      (Fin15AnchoredAtom3606 chi ∧
      Fin15AnchoredAtom3607 chi ∧
      Fin15AnchoredAtom3617 chi ∧
      Fin15AnchoredAtom3691 chi ∧
      Fin15AnchoredAtom3895 chi ∧
      Fin15AnchoredAtom4225 chi))) ∨
      (((Fin15AnchoredAtom3608 chi ∧
      Fin15AnchoredAtom3610 chi ∧
      Fin15AnchoredAtom3613 chi ∧
      Fin15AnchoredAtom3693 chi ∧
      Fin15AnchoredAtom3897 chi ∧
      Fin15AnchoredAtom4227 chi) ∨
      (Fin15AnchoredAtom3609 chi ∧
      Fin15AnchoredAtom3610 chi ∧
      Fin15AnchoredAtom3615 chi ∧
      Fin15AnchoredAtom3695 chi ∧
      Fin15AnchoredAtom3899 chi ∧
      Fin15AnchoredAtom4229 chi)) ∨
      ((Fin15AnchoredAtom3609 chi ∧
      Fin15AnchoredAtom3611 chi ∧
      Fin15AnchoredAtom3616 chi ∧
      Fin15AnchoredAtom3696 chi ∧
      Fin15AnchoredAtom3900 chi ∧
      Fin15AnchoredAtom4230 chi) ∨
      (Fin15AnchoredAtom3610 chi ∧
      Fin15AnchoredAtom3611 chi ∧
      Fin15AnchoredAtom3617 chi ∧
      Fin15AnchoredAtom3697 chi ∧
      Fin15AnchoredAtom3901 chi ∧
      Fin15AnchoredAtom4231 chi))))))) ∨
      ((((((Fin15AnchoredAtom3615 chi ∧
      Fin15AnchoredAtom3616 chi ∧
      Fin15AnchoredAtom3617 chi ∧
      Fin15AnchoredAtom3701 chi ∧
      Fin15AnchoredAtom3905 chi ∧
      Fin15AnchoredAtom4235 chi) ∨
      ((Fin15AnchoredAtom3619 chi ∧
      Fin15AnchoredAtom3620 chi ∧
      Fin15AnchoredAtom3631 chi ∧
      Fin15AnchoredAtom3652 chi ∧
      Fin15AnchoredAtom3912 chi ∧
      Fin15AnchoredAtom4242 chi) ∨
      (Fin15AnchoredAtom3619 chi ∧
      Fin15AnchoredAtom3622 chi ∧
      Fin15AnchoredAtom3633 chi ∧
      Fin15AnchoredAtom3654 chi ∧
      Fin15AnchoredAtom3914 chi ∧
      Fin15AnchoredAtom4244 chi))) ∨
      (((Fin15AnchoredAtom3619 chi ∧
      Fin15AnchoredAtom3623 chi ∧
      Fin15AnchoredAtom3634 chi ∧
      Fin15AnchoredAtom3655 chi ∧
      Fin15AnchoredAtom3915 chi ∧
      Fin15AnchoredAtom4245 chi) ∨
      (Fin15AnchoredAtom3619 chi ∧
      Fin15AnchoredAtom3624 chi ∧
      Fin15AnchoredAtom3635 chi ∧
      Fin15AnchoredAtom3656 chi ∧
      Fin15AnchoredAtom3916 chi ∧
      Fin15AnchoredAtom4246 chi)) ∨
      ((Fin15AnchoredAtom3620 chi ∧
      Fin15AnchoredAtom3621 chi ∧
      Fin15AnchoredAtom3636 chi ∧
      Fin15AnchoredAtom3657 chi ∧
      Fin15AnchoredAtom3917 chi ∧
      Fin15AnchoredAtom4247 chi) ∨
      (Fin15AnchoredAtom3620 chi ∧
      Fin15AnchoredAtom3622 chi ∧
      Fin15AnchoredAtom3637 chi ∧
      Fin15AnchoredAtom3658 chi ∧
      Fin15AnchoredAtom3918 chi ∧
      Fin15AnchoredAtom4248 chi)))) ∨
      ((((Fin15AnchoredAtom3620 chi ∧
      Fin15AnchoredAtom3623 chi ∧
      Fin15AnchoredAtom3638 chi ∧
      Fin15AnchoredAtom3659 chi ∧
      Fin15AnchoredAtom3919 chi ∧
      Fin15AnchoredAtom4249 chi) ∨
      (Fin15AnchoredAtom3620 chi ∧
      Fin15AnchoredAtom3624 chi ∧
      Fin15AnchoredAtom3639 chi ∧
      Fin15AnchoredAtom3660 chi ∧
      Fin15AnchoredAtom3920 chi ∧
      Fin15AnchoredAtom4250 chi)) ∨
      ((Fin15AnchoredAtom3622 chi ∧
      Fin15AnchoredAtom3623 chi ∧
      Fin15AnchoredAtom3643 chi ∧
      Fin15AnchoredAtom3664 chi ∧
      Fin15AnchoredAtom3924 chi ∧
      Fin15AnchoredAtom4254 chi) ∨
      (Fin15AnchoredAtom3622 chi ∧
      Fin15AnchoredAtom3624 chi ∧
      Fin15AnchoredAtom3644 chi ∧
      Fin15AnchoredAtom3665 chi ∧
      Fin15AnchoredAtom3925 chi ∧
      Fin15AnchoredAtom4255 chi))) ∨
      (((Fin15AnchoredAtom3623 chi ∧
      Fin15AnchoredAtom3624 chi ∧
      Fin15AnchoredAtom3645 chi ∧
      Fin15AnchoredAtom3666 chi ∧
      Fin15AnchoredAtom3926 chi ∧
      Fin15AnchoredAtom4256 chi) ∨
      (Fin15AnchoredAtom3631 chi ∧
      Fin15AnchoredAtom3633 chi ∧
      Fin15AnchoredAtom3637 chi ∧
      Fin15AnchoredAtom3683 chi ∧
      Fin15AnchoredAtom3943 chi ∧
      Fin15AnchoredAtom4273 chi)) ∨
      ((Fin15AnchoredAtom3631 chi ∧
      Fin15AnchoredAtom3634 chi ∧
      Fin15AnchoredAtom3638 chi ∧
      Fin15AnchoredAtom3684 chi ∧
      Fin15AnchoredAtom3944 chi ∧
      Fin15AnchoredAtom4274 chi) ∨
      (Fin15AnchoredAtom3631 chi ∧
      Fin15AnchoredAtom3635 chi ∧
      Fin15AnchoredAtom3639 chi ∧
      Fin15AnchoredAtom3685 chi ∧
      Fin15AnchoredAtom3945 chi ∧
      Fin15AnchoredAtom4275 chi))))) ∨
      (((((Fin15AnchoredAtom3633 chi ∧
      Fin15AnchoredAtom3634 chi ∧
      Fin15AnchoredAtom3643 chi ∧
      Fin15AnchoredAtom3689 chi ∧
      Fin15AnchoredAtom3949 chi ∧
      Fin15AnchoredAtom4279 chi) ∨
      (Fin15AnchoredAtom3633 chi ∧
      Fin15AnchoredAtom3635 chi ∧
      Fin15AnchoredAtom3644 chi ∧
      Fin15AnchoredAtom3690 chi ∧
      Fin15AnchoredAtom3950 chi ∧
      Fin15AnchoredAtom4280 chi)) ∨
      ((Fin15AnchoredAtom3634 chi ∧
      Fin15AnchoredAtom3635 chi ∧
      Fin15AnchoredAtom3645 chi ∧
      Fin15AnchoredAtom3691 chi ∧
      Fin15AnchoredAtom3951 chi ∧
      Fin15AnchoredAtom4281 chi) ∨
      (Fin15AnchoredAtom3636 chi ∧
      Fin15AnchoredAtom3637 chi ∧
      Fin15AnchoredAtom3640 chi ∧
      Fin15AnchoredAtom3692 chi ∧
      Fin15AnchoredAtom3952 chi ∧
      Fin15AnchoredAtom4282 chi))) ∨
      (((Fin15AnchoredAtom3637 chi ∧
      Fin15AnchoredAtom3638 chi ∧
      Fin15AnchoredAtom3643 chi ∧
      Fin15AnchoredAtom3695 chi ∧
      Fin15AnchoredAtom3955 chi ∧
      Fin15AnchoredAtom4285 chi) ∨
      (Fin15AnchoredAtom3637 chi ∧
      Fin15AnchoredAtom3639 chi ∧
      Fin15AnchoredAtom3644 chi ∧
      Fin15AnchoredAtom3696 chi ∧
      Fin15AnchoredAtom3956 chi ∧
      Fin15AnchoredAtom4286 chi)) ∨
      ((Fin15AnchoredAtom3638 chi ∧
      Fin15AnchoredAtom3639 chi ∧
      Fin15AnchoredAtom3645 chi ∧
      Fin15AnchoredAtom3697 chi ∧
      Fin15AnchoredAtom3957 chi ∧
      Fin15AnchoredAtom4287 chi) ∨
      (Fin15AnchoredAtom3640 chi ∧
      Fin15AnchoredAtom3641 chi ∧
      Fin15AnchoredAtom3643 chi ∧
      Fin15AnchoredAtom3698 chi ∧
      Fin15AnchoredAtom3958 chi ∧
      Fin15AnchoredAtom4288 chi)))) ∨
      ((((Fin15AnchoredAtom3643 chi ∧
      Fin15AnchoredAtom3644 chi ∧
      Fin15AnchoredAtom3645 chi ∧
      Fin15AnchoredAtom3701 chi ∧
      Fin15AnchoredAtom3961 chi ∧
      Fin15AnchoredAtom4291 chi) ∨
      (Fin15AnchoredAtom3652 chi ∧
      Fin15AnchoredAtom3654 chi ∧
      Fin15AnchoredAtom3658 chi ∧
      Fin15AnchoredAtom3683 chi ∧
      Fin15AnchoredAtom3978 chi ∧
      Fin15AnchoredAtom4308 chi)) ∨
      ((Fin15AnchoredAtom3652 chi ∧
      Fin15AnchoredAtom3655 chi ∧
      Fin15AnchoredAtom3659 chi ∧
      Fin15AnchoredAtom3684 chi ∧
      Fin15AnchoredAtom3979 chi ∧
      Fin15AnchoredAtom4309 chi) ∨
      (Fin15AnchoredAtom3652 chi ∧
      Fin15AnchoredAtom3656 chi ∧
      Fin15AnchoredAtom3660 chi ∧
      Fin15AnchoredAtom3685 chi ∧
      Fin15AnchoredAtom3980 chi ∧
      Fin15AnchoredAtom4310 chi))) ∨
      (((Fin15AnchoredAtom3654 chi ∧
      Fin15AnchoredAtom3655 chi ∧
      Fin15AnchoredAtom3664 chi ∧
      Fin15AnchoredAtom3689 chi ∧
      Fin15AnchoredAtom3984 chi ∧
      Fin15AnchoredAtom4314 chi) ∨
      (Fin15AnchoredAtom3654 chi ∧
      Fin15AnchoredAtom3656 chi ∧
      Fin15AnchoredAtom3665 chi ∧
      Fin15AnchoredAtom3690 chi ∧
      Fin15AnchoredAtom3985 chi ∧
      Fin15AnchoredAtom4315 chi)) ∨
      ((Fin15AnchoredAtom3655 chi ∧
      Fin15AnchoredAtom3656 chi ∧
      Fin15AnchoredAtom3666 chi ∧
      Fin15AnchoredAtom3691 chi ∧
      Fin15AnchoredAtom3986 chi ∧
      Fin15AnchoredAtom4316 chi) ∨
      (Fin15AnchoredAtom3658 chi ∧
      Fin15AnchoredAtom3659 chi ∧
      Fin15AnchoredAtom3664 chi ∧
      Fin15AnchoredAtom3695 chi ∧
      Fin15AnchoredAtom3990 chi ∧
      Fin15AnchoredAtom4320 chi)))))) ∨
      ((((((Fin15AnchoredAtom3658 chi ∧
      Fin15AnchoredAtom3660 chi ∧
      Fin15AnchoredAtom3665 chi ∧
      Fin15AnchoredAtom3696 chi ∧
      Fin15AnchoredAtom3991 chi ∧
      Fin15AnchoredAtom4321 chi) ∨
      (Fin15AnchoredAtom3659 chi ∧
      Fin15AnchoredAtom3660 chi ∧
      Fin15AnchoredAtom3666 chi ∧
      Fin15AnchoredAtom3697 chi ∧
      Fin15AnchoredAtom3992 chi ∧
      Fin15AnchoredAtom4322 chi)) ∨
      ((Fin15AnchoredAtom3664 chi ∧
      Fin15AnchoredAtom3665 chi ∧
      Fin15AnchoredAtom3666 chi ∧
      Fin15AnchoredAtom3701 chi ∧
      Fin15AnchoredAtom3996 chi ∧
      Fin15AnchoredAtom4326 chi) ∨
      (Fin15AnchoredAtom3682 chi ∧
      Fin15AnchoredAtom3683 chi ∧
      Fin15AnchoredAtom3686 chi ∧
      Fin15AnchoredAtom3692 chi ∧
      Fin15AnchoredAtom4017 chi ∧
      Fin15AnchoredAtom4347 chi))) ∨
      (((Fin15AnchoredAtom3683 chi ∧
      Fin15AnchoredAtom3684 chi ∧
      Fin15AnchoredAtom3689 chi ∧
      Fin15AnchoredAtom3695 chi ∧
      Fin15AnchoredAtom4020 chi ∧
      Fin15AnchoredAtom4350 chi) ∨
      (Fin15AnchoredAtom3683 chi ∧
      Fin15AnchoredAtom3685 chi ∧
      Fin15AnchoredAtom3690 chi ∧
      Fin15AnchoredAtom3696 chi ∧
      Fin15AnchoredAtom4021 chi ∧
      Fin15AnchoredAtom4351 chi)) ∨
      ((Fin15AnchoredAtom3684 chi ∧
      Fin15AnchoredAtom3685 chi ∧
      Fin15AnchoredAtom3691 chi ∧
      Fin15AnchoredAtom3697 chi ∧
      Fin15AnchoredAtom4022 chi ∧
      Fin15AnchoredAtom4352 chi) ∨
      (Fin15AnchoredAtom3689 chi ∧
      Fin15AnchoredAtom3690 chi ∧
      Fin15AnchoredAtom3691 chi ∧
      Fin15AnchoredAtom3701 chi ∧
      Fin15AnchoredAtom4026 chi ∧
      Fin15AnchoredAtom4356 chi)))) ∨
      ((((Fin15AnchoredAtom3695 chi ∧
      Fin15AnchoredAtom3696 chi ∧
      Fin15AnchoredAtom3697 chi ∧
      Fin15AnchoredAtom3701 chi ∧
      Fin15AnchoredAtom4030 chi ∧
      Fin15AnchoredAtom4360 chi) ∨
      (Fin15AnchoredAtom3702 chi ∧
      Fin15AnchoredAtom3704 chi ∧
      Fin15AnchoredAtom3711 chi ∧
      Fin15AnchoredAtom3739 chi ∧
      Fin15AnchoredAtom3823 chi ∧
      Fin15AnchoredAtom4363 chi)) ∨
      ((Fin15AnchoredAtom3702 chi ∧
      Fin15AnchoredAtom3705 chi ∧
      Fin15AnchoredAtom3712 chi ∧
      Fin15AnchoredAtom3740 chi ∧
      Fin15AnchoredAtom3824 chi ∧
      Fin15AnchoredAtom4364 chi) ∨
      (Fin15AnchoredAtom3702 chi ∧
      Fin15AnchoredAtom3707 chi ∧
      Fin15AnchoredAtom3714 chi ∧
      Fin15AnchoredAtom3742 chi ∧
      Fin15AnchoredAtom3826 chi ∧
      Fin15AnchoredAtom4366 chi))) ∨
      (((Fin15AnchoredAtom3702 chi ∧
      Fin15AnchoredAtom3708 chi ∧
      Fin15AnchoredAtom3715 chi ∧
      Fin15AnchoredAtom3743 chi ∧
      Fin15AnchoredAtom3827 chi ∧
      Fin15AnchoredAtom4367 chi) ∨
      (Fin15AnchoredAtom3702 chi ∧
      Fin15AnchoredAtom3709 chi ∧
      Fin15AnchoredAtom3716 chi ∧
      Fin15AnchoredAtom3744 chi ∧
      Fin15AnchoredAtom3828 chi ∧
      Fin15AnchoredAtom4368 chi)) ∨
      ((Fin15AnchoredAtom3704 chi ∧
      Fin15AnchoredAtom3705 chi ∧
      Fin15AnchoredAtom3723 chi ∧
      Fin15AnchoredAtom3751 chi ∧
      Fin15AnchoredAtom3835 chi ∧
      Fin15AnchoredAtom4375 chi) ∨
      (Fin15AnchoredAtom3704 chi ∧
      Fin15AnchoredAtom3707 chi ∧
      Fin15AnchoredAtom3725 chi ∧
      Fin15AnchoredAtom3753 chi ∧
      Fin15AnchoredAtom3837 chi ∧
      Fin15AnchoredAtom4377 chi))))) ∨
      (((((Fin15AnchoredAtom3704 chi ∧
      Fin15AnchoredAtom3708 chi ∧
      Fin15AnchoredAtom3726 chi ∧
      Fin15AnchoredAtom3754 chi ∧
      Fin15AnchoredAtom3838 chi ∧
      Fin15AnchoredAtom4378 chi) ∨
      (Fin15AnchoredAtom3704 chi ∧
      Fin15AnchoredAtom3709 chi ∧
      Fin15AnchoredAtom3727 chi ∧
      Fin15AnchoredAtom3755 chi ∧
      Fin15AnchoredAtom3839 chi ∧
      Fin15AnchoredAtom4379 chi)) ∨
      ((Fin15AnchoredAtom3705 chi ∧
      Fin15AnchoredAtom3707 chi ∧
      Fin15AnchoredAtom3729 chi ∧
      Fin15AnchoredAtom3757 chi ∧
      Fin15AnchoredAtom3841 chi ∧
      Fin15AnchoredAtom4381 chi) ∨
      (Fin15AnchoredAtom3705 chi ∧
      Fin15AnchoredAtom3708 chi ∧
      Fin15AnchoredAtom3730 chi ∧
      Fin15AnchoredAtom3758 chi ∧
      Fin15AnchoredAtom3842 chi ∧
      Fin15AnchoredAtom4382 chi))) ∨
      (((Fin15AnchoredAtom3705 chi ∧
      Fin15AnchoredAtom3709 chi ∧
      Fin15AnchoredAtom3731 chi ∧
      Fin15AnchoredAtom3759 chi ∧
      Fin15AnchoredAtom3843 chi ∧
      Fin15AnchoredAtom4383 chi) ∨
      (Fin15AnchoredAtom3707 chi ∧
      Fin15AnchoredAtom3708 chi ∧
      Fin15AnchoredAtom3735 chi ∧
      Fin15AnchoredAtom3763 chi ∧
      Fin15AnchoredAtom3847 chi ∧
      Fin15AnchoredAtom4387 chi)) ∨
      ((Fin15AnchoredAtom3707 chi ∧
      Fin15AnchoredAtom3709 chi ∧
      Fin15AnchoredAtom3736 chi ∧
      Fin15AnchoredAtom3764 chi ∧
      Fin15AnchoredAtom3848 chi ∧
      Fin15AnchoredAtom4388 chi) ∨
      (Fin15AnchoredAtom3708 chi ∧
      Fin15AnchoredAtom3709 chi ∧
      Fin15AnchoredAtom3737 chi ∧
      Fin15AnchoredAtom3765 chi ∧
      Fin15AnchoredAtom3849 chi ∧
      Fin15AnchoredAtom4389 chi)))) ∨
      ((((Fin15AnchoredAtom3711 chi ∧
      Fin15AnchoredAtom3712 chi ∧
      Fin15AnchoredAtom3723 chi ∧
      Fin15AnchoredAtom3772 chi ∧
      Fin15AnchoredAtom3856 chi ∧
      Fin15AnchoredAtom4396 chi) ∨
      (Fin15AnchoredAtom3711 chi ∧
      Fin15AnchoredAtom3714 chi ∧
      Fin15AnchoredAtom3725 chi ∧
      Fin15AnchoredAtom3774 chi ∧
      Fin15AnchoredAtom3858 chi ∧
      Fin15AnchoredAtom4398 chi)) ∨
      ((Fin15AnchoredAtom3711 chi ∧
      Fin15AnchoredAtom3715 chi ∧
      Fin15AnchoredAtom3726 chi ∧
      Fin15AnchoredAtom3775 chi ∧
      Fin15AnchoredAtom3859 chi ∧
      Fin15AnchoredAtom4399 chi) ∨
      (Fin15AnchoredAtom3711 chi ∧
      Fin15AnchoredAtom3716 chi ∧
      Fin15AnchoredAtom3727 chi ∧
      Fin15AnchoredAtom3776 chi ∧
      Fin15AnchoredAtom3860 chi ∧
      Fin15AnchoredAtom4400 chi))) ∨
      (((Fin15AnchoredAtom3712 chi ∧
      Fin15AnchoredAtom3714 chi ∧
      Fin15AnchoredAtom3729 chi ∧
      Fin15AnchoredAtom3778 chi ∧
      Fin15AnchoredAtom3862 chi ∧
      Fin15AnchoredAtom4402 chi) ∨
      (Fin15AnchoredAtom3712 chi ∧
      Fin15AnchoredAtom3715 chi ∧
      Fin15AnchoredAtom3730 chi ∧
      Fin15AnchoredAtom3779 chi ∧
      Fin15AnchoredAtom3863 chi ∧
      Fin15AnchoredAtom4403 chi)) ∨
      ((Fin15AnchoredAtom3712 chi ∧
      Fin15AnchoredAtom3716 chi ∧
      Fin15AnchoredAtom3731 chi ∧
      Fin15AnchoredAtom3780 chi ∧
      Fin15AnchoredAtom3864 chi ∧
      Fin15AnchoredAtom4404 chi) ∨
      (Fin15AnchoredAtom3714 chi ∧
      Fin15AnchoredAtom3715 chi ∧
      Fin15AnchoredAtom3735 chi ∧
      Fin15AnchoredAtom3784 chi ∧
      Fin15AnchoredAtom3868 chi ∧
      Fin15AnchoredAtom4408 chi)))))))))) := by
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
                exact fin15Anchored_clause29784 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29785 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29786 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29787 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29788 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29789 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29790 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29791 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29792 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29793 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29794 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29795 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29796 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29797 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29798 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29799 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29800 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29801 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29802 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29803 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29804 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29805 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29806 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29807 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29808 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29809 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29810 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29811 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29812 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29813 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29814 chi hnoStrong hbad
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
                  exact fin15Anchored_clause29815 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29816 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29817 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29818 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29819 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29820 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29821 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29822 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29823 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29824 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29825 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29826 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29827 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29828 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29829 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29830 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29831 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29832 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29833 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29834 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29835 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29836 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29837 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29838 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29839 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29840 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29841 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29842 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29843 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29844 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29845 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29846 chi hnoStrong hbad
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
                exact fin15Anchored_clause29847 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29848 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29849 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29850 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29851 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29852 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29853 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29854 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29855 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29856 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29857 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29858 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29859 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29860 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29861 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29862 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29863 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29864 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29865 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29866 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29867 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29868 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29869 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29870 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29871 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29872 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29873 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29874 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29875 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29876 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29877 chi hnoStrong hbad
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
                  exact fin15Anchored_clause29878 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29879 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29880 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29881 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29882 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29883 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29884 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29885 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29886 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29887 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29888 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29889 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29890 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29891 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29892 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29893 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29894 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29895 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29896 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29897 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29898 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29899 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29900 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29901 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29902 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29903 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29904 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29905 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29906 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29907 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29908 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29909 chi hnoStrong hbad
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
                exact fin15Anchored_clause29910 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29911 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29912 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29913 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29914 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29915 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29916 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29917 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29918 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29919 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29920 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29921 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29922 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29923 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29924 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29925 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29926 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29927 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29928 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29929 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29930 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29931 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29932 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29933 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29934 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29935 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29936 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29937 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29938 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29939 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29940 chi hnoStrong hbad
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
                  exact fin15Anchored_clause29941 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29942 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29943 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29944 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29945 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29946 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29947 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29948 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29949 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29950 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29951 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29952 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29953 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29954 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29955 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29956 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29957 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29958 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29959 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29960 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29961 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29962 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29963 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29964 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29965 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29966 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29967 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29968 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29969 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29970 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29971 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29972 chi hnoStrong hbad
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
                exact fin15Anchored_clause29973 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29974 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29975 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29976 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29977 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29978 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29979 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29980 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29981 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29982 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29983 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29984 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29985 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29986 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29987 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29988 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29989 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29990 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29991 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29992 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29993 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29994 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29995 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29996 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29997 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29998 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29999 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30000 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30001 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30002 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30003 chi hnoStrong hbad
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
                  exact fin15Anchored_clause30004 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30005 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30006 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30007 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30008 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30009 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30010 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30011 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30012 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30013 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30014 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30015 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30016 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30017 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30018 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30019 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30020 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30021 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30022 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30023 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30024 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30025 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30026 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30027 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30028 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30029 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30030 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30031 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30032 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30033 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30034 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30035 chi hnoStrong hbad

end ErdosSzekeres

end
