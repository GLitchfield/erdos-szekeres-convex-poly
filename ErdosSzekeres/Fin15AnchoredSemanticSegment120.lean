module

public import ErdosSzekeres.Fin15AnchoredClauseChunk236
public import ErdosSzekeres.Fin15AnchoredClauseChunk237
public import ErdosSzekeres.Fin15AnchoredClauseChunk238

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 120. -/

theorem fin15Anchored_rejectSemanticSegment120
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom4201 chi ∧
      Fin15AnchoredAtom4204 chi ∧
      Fin15AnchoredAtom4208 chi ∧
      Fin15AnchoredAtom4218 chi ∧
      Fin15AnchoredAtom4329 chi ∧
      Fin15AnchoredAtom4665 chi) ∨
      ((Fin15AnchoredAtom4217 chi ∧
      Fin15AnchoredAtom4218 chi ∧
      Fin15AnchoredAtom4223 chi ∧
      Fin15AnchoredAtom4229 chi ∧
      Fin15AnchoredAtom4350 chi ∧
      Fin15AnchoredAtom4686 chi) ∨
      (Fin15AnchoredAtom4217 chi ∧
      Fin15AnchoredAtom4219 chi ∧
      Fin15AnchoredAtom4224 chi ∧
      Fin15AnchoredAtom4230 chi ∧
      Fin15AnchoredAtom4351 chi ∧
      Fin15AnchoredAtom4687 chi))) ∨
      (((Fin15AnchoredAtom4218 chi ∧
      Fin15AnchoredAtom4219 chi ∧
      Fin15AnchoredAtom4225 chi ∧
      Fin15AnchoredAtom4231 chi ∧
      Fin15AnchoredAtom4352 chi ∧
      Fin15AnchoredAtom4688 chi) ∨
      (Fin15AnchoredAtom4223 chi ∧
      Fin15AnchoredAtom4224 chi ∧
      Fin15AnchoredAtom4225 chi ∧
      Fin15AnchoredAtom4235 chi ∧
      Fin15AnchoredAtom4356 chi ∧
      Fin15AnchoredAtom4692 chi)) ∨
      ((Fin15AnchoredAtom4229 chi ∧
      Fin15AnchoredAtom4230 chi ∧
      Fin15AnchoredAtom4231 chi ∧
      Fin15AnchoredAtom4235 chi ∧
      Fin15AnchoredAtom4360 chi ∧
      Fin15AnchoredAtom4696 chi) ∨
      (Fin15AnchoredAtom4237 chi ∧
      Fin15AnchoredAtom4239 chi ∧
      Fin15AnchoredAtom4248 chi ∧
      Fin15AnchoredAtom4263 chi ∧
      Fin15AnchoredAtom4298 chi ∧
      Fin15AnchoredAtom4704 chi)))) ∨
      ((((Fin15AnchoredAtom4237 chi ∧
      Fin15AnchoredAtom4240 chi ∧
      Fin15AnchoredAtom4249 chi ∧
      Fin15AnchoredAtom4264 chi ∧
      Fin15AnchoredAtom4299 chi ∧
      Fin15AnchoredAtom4705 chi) ∨
      (Fin15AnchoredAtom4242 chi ∧
      Fin15AnchoredAtom4244 chi ∧
      Fin15AnchoredAtom4248 chi ∧
      Fin15AnchoredAtom4273 chi ∧
      Fin15AnchoredAtom4308 chi ∧
      Fin15AnchoredAtom4714 chi)) ∨
      ((Fin15AnchoredAtom4242 chi ∧
      Fin15AnchoredAtom4245 chi ∧
      Fin15AnchoredAtom4249 chi ∧
      Fin15AnchoredAtom4274 chi ∧
      Fin15AnchoredAtom4309 chi ∧
      Fin15AnchoredAtom4715 chi) ∨
      (Fin15AnchoredAtom4242 chi ∧
      Fin15AnchoredAtom4246 chi ∧
      Fin15AnchoredAtom4250 chi ∧
      Fin15AnchoredAtom4275 chi ∧
      Fin15AnchoredAtom4310 chi ∧
      Fin15AnchoredAtom4716 chi))) ∨
      (((Fin15AnchoredAtom4244 chi ∧
      Fin15AnchoredAtom4245 chi ∧
      Fin15AnchoredAtom4254 chi ∧
      Fin15AnchoredAtom4279 chi ∧
      Fin15AnchoredAtom4314 chi ∧
      Fin15AnchoredAtom4720 chi) ∨
      (Fin15AnchoredAtom4244 chi ∧
      Fin15AnchoredAtom4246 chi ∧
      Fin15AnchoredAtom4255 chi ∧
      Fin15AnchoredAtom4280 chi ∧
      Fin15AnchoredAtom4315 chi ∧
      Fin15AnchoredAtom4721 chi)) ∨
      ((Fin15AnchoredAtom4245 chi ∧
      Fin15AnchoredAtom4246 chi ∧
      Fin15AnchoredAtom4256 chi ∧
      Fin15AnchoredAtom4281 chi ∧
      Fin15AnchoredAtom4316 chi ∧
      Fin15AnchoredAtom4722 chi) ∨
      (Fin15AnchoredAtom4248 chi ∧
      Fin15AnchoredAtom4249 chi ∧
      Fin15AnchoredAtom4254 chi ∧
      Fin15AnchoredAtom4285 chi ∧
      Fin15AnchoredAtom4320 chi ∧
      Fin15AnchoredAtom4726 chi))))) ∨
      (((((Fin15AnchoredAtom4248 chi ∧
      Fin15AnchoredAtom4250 chi ∧
      Fin15AnchoredAtom4255 chi ∧
      Fin15AnchoredAtom4286 chi ∧
      Fin15AnchoredAtom4321 chi ∧
      Fin15AnchoredAtom4727 chi) ∨
      (Fin15AnchoredAtom4249 chi ∧
      Fin15AnchoredAtom4250 chi ∧
      Fin15AnchoredAtom4256 chi ∧
      Fin15AnchoredAtom4287 chi ∧
      Fin15AnchoredAtom4322 chi ∧
      Fin15AnchoredAtom4728 chi)) ∨
      ((Fin15AnchoredAtom4254 chi ∧
      Fin15AnchoredAtom4255 chi ∧
      Fin15AnchoredAtom4256 chi ∧
      Fin15AnchoredAtom4291 chi ∧
      Fin15AnchoredAtom4326 chi ∧
      Fin15AnchoredAtom4732 chi) ∨
      (Fin15AnchoredAtom4263 chi ∧
      Fin15AnchoredAtom4264 chi ∧
      Fin15AnchoredAtom4269 chi ∧
      Fin15AnchoredAtom4285 chi ∧
      Fin15AnchoredAtom4340 chi ∧
      Fin15AnchoredAtom4746 chi))) ∨
      (((Fin15AnchoredAtom4263 chi ∧
      Fin15AnchoredAtom4265 chi ∧
      Fin15AnchoredAtom4270 chi ∧
      Fin15AnchoredAtom4286 chi ∧
      Fin15AnchoredAtom4341 chi ∧
      Fin15AnchoredAtom4747 chi) ∨
      (Fin15AnchoredAtom4264 chi ∧
      Fin15AnchoredAtom4265 chi ∧
      Fin15AnchoredAtom4271 chi ∧
      Fin15AnchoredAtom4287 chi ∧
      Fin15AnchoredAtom4342 chi ∧
      Fin15AnchoredAtom4748 chi)) ∨
      ((Fin15AnchoredAtom4272 chi ∧
      Fin15AnchoredAtom4273 chi ∧
      Fin15AnchoredAtom4276 chi ∧
      Fin15AnchoredAtom4282 chi ∧
      Fin15AnchoredAtom4347 chi ∧
      Fin15AnchoredAtom4753 chi) ∨
      (Fin15AnchoredAtom4273 chi ∧
      Fin15AnchoredAtom4274 chi ∧
      Fin15AnchoredAtom4279 chi ∧
      Fin15AnchoredAtom4285 chi ∧
      Fin15AnchoredAtom4350 chi ∧
      Fin15AnchoredAtom4756 chi)))) ∨
      ((((Fin15AnchoredAtom4273 chi ∧
      Fin15AnchoredAtom4275 chi ∧
      Fin15AnchoredAtom4280 chi ∧
      Fin15AnchoredAtom4286 chi ∧
      Fin15AnchoredAtom4351 chi ∧
      Fin15AnchoredAtom4757 chi) ∨
      (Fin15AnchoredAtom4274 chi ∧
      Fin15AnchoredAtom4275 chi ∧
      Fin15AnchoredAtom4281 chi ∧
      Fin15AnchoredAtom4287 chi ∧
      Fin15AnchoredAtom4352 chi ∧
      Fin15AnchoredAtom4758 chi)) ∨
      ((Fin15AnchoredAtom4279 chi ∧
      Fin15AnchoredAtom4280 chi ∧
      Fin15AnchoredAtom4281 chi ∧
      Fin15AnchoredAtom4291 chi ∧
      Fin15AnchoredAtom4356 chi ∧
      Fin15AnchoredAtom4762 chi) ∨
      (Fin15AnchoredAtom4285 chi ∧
      Fin15AnchoredAtom4286 chi ∧
      Fin15AnchoredAtom4287 chi ∧
      Fin15AnchoredAtom4291 chi ∧
      Fin15AnchoredAtom4360 chi ∧
      Fin15AnchoredAtom4766 chi))) ∨
      (((Fin15AnchoredAtom4295 chi ∧
      Fin15AnchoredAtom4296 chi ∧
      Fin15AnchoredAtom4306 chi ∧
      Fin15AnchoredAtom4316 chi ∧
      Fin15AnchoredAtom4336 chi ∧
      Fin15AnchoredAtom4777 chi) ∨
      (Fin15AnchoredAtom4308 chi ∧
      Fin15AnchoredAtom4309 chi ∧
      Fin15AnchoredAtom4314 chi ∧
      Fin15AnchoredAtom4320 chi ∧
      Fin15AnchoredAtom4350 chi ∧
      Fin15AnchoredAtom4791 chi)) ∨
      ((Fin15AnchoredAtom4308 chi ∧
      Fin15AnchoredAtom4310 chi ∧
      Fin15AnchoredAtom4315 chi ∧
      Fin15AnchoredAtom4321 chi ∧
      Fin15AnchoredAtom4351 chi ∧
      Fin15AnchoredAtom4792 chi) ∨
      (Fin15AnchoredAtom4309 chi ∧
      Fin15AnchoredAtom4310 chi ∧
      Fin15AnchoredAtom4316 chi ∧
      Fin15AnchoredAtom4322 chi ∧
      Fin15AnchoredAtom4352 chi ∧
      Fin15AnchoredAtom4793 chi)))))) ∨
      ((((((Fin15AnchoredAtom4314 chi ∧
      Fin15AnchoredAtom4315 chi ∧
      Fin15AnchoredAtom4316 chi ∧
      Fin15AnchoredAtom4326 chi ∧
      Fin15AnchoredAtom4356 chi ∧
      Fin15AnchoredAtom4797 chi) ∨
      (Fin15AnchoredAtom4320 chi ∧
      Fin15AnchoredAtom4321 chi ∧
      Fin15AnchoredAtom4322 chi ∧
      Fin15AnchoredAtom4326 chi ∧
      Fin15AnchoredAtom4360 chi ∧
      Fin15AnchoredAtom4801 chi)) ∨
      ((Fin15AnchoredAtom4350 chi ∧
      Fin15AnchoredAtom4351 chi ∧
      Fin15AnchoredAtom4352 chi ∧
      Fin15AnchoredAtom4356 chi ∧
      Fin15AnchoredAtom4360 chi ∧
      Fin15AnchoredAtom4821 chi) ∨
      (Fin15AnchoredAtom4362 chi ∧
      Fin15AnchoredAtom4363 chi ∧
      Fin15AnchoredAtom4369 chi ∧
      Fin15AnchoredAtom4390 chi ∧
      Fin15AnchoredAtom4446 chi ∧
      Fin15AnchoredAtom4572 chi))) ∨
      (((Fin15AnchoredAtom4362 chi ∧
      Fin15AnchoredAtom4364 chi ∧
      Fin15AnchoredAtom4370 chi ∧
      Fin15AnchoredAtom4391 chi ∧
      Fin15AnchoredAtom4447 chi ∧
      Fin15AnchoredAtom4573 chi) ∨
      (Fin15AnchoredAtom4363 chi ∧
      Fin15AnchoredAtom4364 chi ∧
      Fin15AnchoredAtom4375 chi ∧
      Fin15AnchoredAtom4396 chi ∧
      Fin15AnchoredAtom4452 chi ∧
      Fin15AnchoredAtom4578 chi)) ∨
      ((Fin15AnchoredAtom4363 chi ∧
      Fin15AnchoredAtom4366 chi ∧
      Fin15AnchoredAtom4377 chi ∧
      Fin15AnchoredAtom4398 chi ∧
      Fin15AnchoredAtom4454 chi ∧
      Fin15AnchoredAtom4580 chi) ∨
      (Fin15AnchoredAtom4363 chi ∧
      Fin15AnchoredAtom4367 chi ∧
      Fin15AnchoredAtom4378 chi ∧
      Fin15AnchoredAtom4399 chi ∧
      Fin15AnchoredAtom4455 chi ∧
      Fin15AnchoredAtom4581 chi)))) ∨
      ((((Fin15AnchoredAtom4363 chi ∧
      Fin15AnchoredAtom4368 chi ∧
      Fin15AnchoredAtom4379 chi ∧
      Fin15AnchoredAtom4400 chi ∧
      Fin15AnchoredAtom4456 chi ∧
      Fin15AnchoredAtom4582 chi) ∨
      (Fin15AnchoredAtom4364 chi ∧
      Fin15AnchoredAtom4366 chi ∧
      Fin15AnchoredAtom4381 chi ∧
      Fin15AnchoredAtom4402 chi ∧
      Fin15AnchoredAtom4458 chi ∧
      Fin15AnchoredAtom4584 chi)) ∨
      ((Fin15AnchoredAtom4364 chi ∧
      Fin15AnchoredAtom4367 chi ∧
      Fin15AnchoredAtom4382 chi ∧
      Fin15AnchoredAtom4403 chi ∧
      Fin15AnchoredAtom4459 chi ∧
      Fin15AnchoredAtom4585 chi) ∨
      (Fin15AnchoredAtom4364 chi ∧
      Fin15AnchoredAtom4368 chi ∧
      Fin15AnchoredAtom4383 chi ∧
      Fin15AnchoredAtom4404 chi ∧
      Fin15AnchoredAtom4460 chi ∧
      Fin15AnchoredAtom4586 chi))) ∨
      (((Fin15AnchoredAtom4365 chi ∧
      Fin15AnchoredAtom4366 chi ∧
      Fin15AnchoredAtom4384 chi ∧
      Fin15AnchoredAtom4405 chi ∧
      Fin15AnchoredAtom4461 chi ∧
      Fin15AnchoredAtom4587 chi) ∨
      (Fin15AnchoredAtom4366 chi ∧
      Fin15AnchoredAtom4367 chi ∧
      Fin15AnchoredAtom4387 chi ∧
      Fin15AnchoredAtom4408 chi ∧
      Fin15AnchoredAtom4464 chi ∧
      Fin15AnchoredAtom4590 chi)) ∨
      ((Fin15AnchoredAtom4366 chi ∧
      Fin15AnchoredAtom4368 chi ∧
      Fin15AnchoredAtom4388 chi ∧
      Fin15AnchoredAtom4409 chi ∧
      Fin15AnchoredAtom4465 chi ∧
      Fin15AnchoredAtom4591 chi) ∨
      (Fin15AnchoredAtom4367 chi ∧
      Fin15AnchoredAtom4368 chi ∧
      Fin15AnchoredAtom4389 chi ∧
      Fin15AnchoredAtom4410 chi ∧
      Fin15AnchoredAtom4466 chi ∧
      Fin15AnchoredAtom4592 chi))))) ∨
      (((((Fin15AnchoredAtom4369 chi ∧
      Fin15AnchoredAtom4370 chi ∧
      Fin15AnchoredAtom4375 chi ∧
      Fin15AnchoredAtom4411 chi ∧
      Fin15AnchoredAtom4467 chi ∧
      Fin15AnchoredAtom4593 chi) ∨
      (Fin15AnchoredAtom4369 chi ∧
      Fin15AnchoredAtom4373 chi ∧
      Fin15AnchoredAtom4378 chi ∧
      Fin15AnchoredAtom4414 chi ∧
      Fin15AnchoredAtom4470 chi ∧
      Fin15AnchoredAtom4596 chi)) ∨
      ((Fin15AnchoredAtom4370 chi ∧
      Fin15AnchoredAtom4372 chi ∧
      Fin15AnchoredAtom4381 chi ∧
      Fin15AnchoredAtom4417 chi ∧
      Fin15AnchoredAtom4473 chi ∧
      Fin15AnchoredAtom4599 chi) ∨
      (Fin15AnchoredAtom4370 chi ∧
      Fin15AnchoredAtom4373 chi ∧
      Fin15AnchoredAtom4382 chi ∧
      Fin15AnchoredAtom4418 chi ∧
      Fin15AnchoredAtom4474 chi ∧
      Fin15AnchoredAtom4600 chi))) ∨
      (((Fin15AnchoredAtom4370 chi ∧
      Fin15AnchoredAtom4374 chi ∧
      Fin15AnchoredAtom4383 chi ∧
      Fin15AnchoredAtom4419 chi ∧
      Fin15AnchoredAtom4475 chi ∧
      Fin15AnchoredAtom4601 chi) ∨
      (Fin15AnchoredAtom4372 chi ∧
      Fin15AnchoredAtom4373 chi ∧
      Fin15AnchoredAtom4387 chi ∧
      Fin15AnchoredAtom4423 chi ∧
      Fin15AnchoredAtom4479 chi ∧
      Fin15AnchoredAtom4605 chi)) ∨
      ((Fin15AnchoredAtom4373 chi ∧
      Fin15AnchoredAtom4374 chi ∧
      Fin15AnchoredAtom4389 chi ∧
      Fin15AnchoredAtom4425 chi ∧
      Fin15AnchoredAtom4481 chi ∧
      Fin15AnchoredAtom4607 chi) ∨
      (Fin15AnchoredAtom4375 chi ∧
      Fin15AnchoredAtom4377 chi ∧
      Fin15AnchoredAtom4381 chi ∧
      Fin15AnchoredAtom4427 chi ∧
      Fin15AnchoredAtom4483 chi ∧
      Fin15AnchoredAtom4609 chi)))) ∨
      ((((Fin15AnchoredAtom4375 chi ∧
      Fin15AnchoredAtom4378 chi ∧
      Fin15AnchoredAtom4382 chi ∧
      Fin15AnchoredAtom4428 chi ∧
      Fin15AnchoredAtom4484 chi ∧
      Fin15AnchoredAtom4610 chi) ∨
      (Fin15AnchoredAtom4375 chi ∧
      Fin15AnchoredAtom4379 chi ∧
      Fin15AnchoredAtom4383 chi ∧
      Fin15AnchoredAtom4429 chi ∧
      Fin15AnchoredAtom4485 chi ∧
      Fin15AnchoredAtom4611 chi)) ∨
      ((Fin15AnchoredAtom4377 chi ∧
      Fin15AnchoredAtom4378 chi ∧
      Fin15AnchoredAtom4387 chi ∧
      Fin15AnchoredAtom4433 chi ∧
      Fin15AnchoredAtom4489 chi ∧
      Fin15AnchoredAtom4615 chi) ∨
      (Fin15AnchoredAtom4377 chi ∧
      Fin15AnchoredAtom4379 chi ∧
      Fin15AnchoredAtom4388 chi ∧
      Fin15AnchoredAtom4434 chi ∧
      Fin15AnchoredAtom4490 chi ∧
      Fin15AnchoredAtom4616 chi))) ∨
      (((Fin15AnchoredAtom4378 chi ∧
      Fin15AnchoredAtom4379 chi ∧
      Fin15AnchoredAtom4389 chi ∧
      Fin15AnchoredAtom4435 chi ∧
      Fin15AnchoredAtom4491 chi ∧
      Fin15AnchoredAtom4617 chi) ∨
      (Fin15AnchoredAtom4381 chi ∧
      Fin15AnchoredAtom4382 chi ∧
      Fin15AnchoredAtom4387 chi ∧
      Fin15AnchoredAtom4439 chi ∧
      Fin15AnchoredAtom4495 chi ∧
      Fin15AnchoredAtom4621 chi)) ∨
      ((Fin15AnchoredAtom4381 chi ∧
      Fin15AnchoredAtom4383 chi ∧
      Fin15AnchoredAtom4388 chi ∧
      Fin15AnchoredAtom4440 chi ∧
      Fin15AnchoredAtom4496 chi ∧
      Fin15AnchoredAtom4622 chi) ∨
      (Fin15AnchoredAtom4382 chi ∧
      Fin15AnchoredAtom4383 chi ∧
      Fin15AnchoredAtom4389 chi ∧
      Fin15AnchoredAtom4441 chi ∧
      Fin15AnchoredAtom4497 chi ∧
      Fin15AnchoredAtom4623 chi))))))) ∨
      ((((((Fin15AnchoredAtom4387 chi ∧
      Fin15AnchoredAtom4388 chi ∧
      Fin15AnchoredAtom4389 chi ∧
      Fin15AnchoredAtom4445 chi ∧
      Fin15AnchoredAtom4501 chi ∧
      Fin15AnchoredAtom4627 chi) ∨
      ((Fin15AnchoredAtom4390 chi ∧
      Fin15AnchoredAtom4391 chi ∧
      Fin15AnchoredAtom4396 chi ∧
      Fin15AnchoredAtom4411 chi ∧
      Fin15AnchoredAtom4502 chi ∧
      Fin15AnchoredAtom4628 chi) ∨
      (Fin15AnchoredAtom4390 chi ∧
      Fin15AnchoredAtom4393 chi ∧
      Fin15AnchoredAtom4398 chi ∧
      Fin15AnchoredAtom4413 chi ∧
      Fin15AnchoredAtom4504 chi ∧
      Fin15AnchoredAtom4630 chi))) ∨
      (((Fin15AnchoredAtom4390 chi ∧
      Fin15AnchoredAtom4394 chi ∧
      Fin15AnchoredAtom4399 chi ∧
      Fin15AnchoredAtom4414 chi ∧
      Fin15AnchoredAtom4505 chi ∧
      Fin15AnchoredAtom4631 chi) ∨
      (Fin15AnchoredAtom4391 chi ∧
      Fin15AnchoredAtom4393 chi ∧
      Fin15AnchoredAtom4402 chi ∧
      Fin15AnchoredAtom4417 chi ∧
      Fin15AnchoredAtom4508 chi ∧
      Fin15AnchoredAtom4634 chi)) ∨
      ((Fin15AnchoredAtom4391 chi ∧
      Fin15AnchoredAtom4394 chi ∧
      Fin15AnchoredAtom4403 chi ∧
      Fin15AnchoredAtom4418 chi ∧
      Fin15AnchoredAtom4509 chi ∧
      Fin15AnchoredAtom4635 chi) ∨
      (Fin15AnchoredAtom4393 chi ∧
      Fin15AnchoredAtom4394 chi ∧
      Fin15AnchoredAtom4408 chi ∧
      Fin15AnchoredAtom4423 chi ∧
      Fin15AnchoredAtom4514 chi ∧
      Fin15AnchoredAtom4640 chi)))) ∨
      ((((Fin15AnchoredAtom4393 chi ∧
      Fin15AnchoredAtom4395 chi ∧
      Fin15AnchoredAtom4409 chi ∧
      Fin15AnchoredAtom4424 chi ∧
      Fin15AnchoredAtom4515 chi ∧
      Fin15AnchoredAtom4641 chi) ∨
      (Fin15AnchoredAtom4394 chi ∧
      Fin15AnchoredAtom4395 chi ∧
      Fin15AnchoredAtom4410 chi ∧
      Fin15AnchoredAtom4425 chi ∧
      Fin15AnchoredAtom4516 chi ∧
      Fin15AnchoredAtom4642 chi)) ∨
      ((Fin15AnchoredAtom4396 chi ∧
      Fin15AnchoredAtom4397 chi ∧
      Fin15AnchoredAtom4401 chi ∧
      Fin15AnchoredAtom4426 chi ∧
      Fin15AnchoredAtom4517 chi ∧
      Fin15AnchoredAtom4643 chi) ∨
      (Fin15AnchoredAtom4396 chi ∧
      Fin15AnchoredAtom4398 chi ∧
      Fin15AnchoredAtom4402 chi ∧
      Fin15AnchoredAtom4427 chi ∧
      Fin15AnchoredAtom4518 chi ∧
      Fin15AnchoredAtom4644 chi))) ∨
      (((Fin15AnchoredAtom4396 chi ∧
      Fin15AnchoredAtom4399 chi ∧
      Fin15AnchoredAtom4403 chi ∧
      Fin15AnchoredAtom4428 chi ∧
      Fin15AnchoredAtom4519 chi ∧
      Fin15AnchoredAtom4645 chi) ∨
      (Fin15AnchoredAtom4396 chi ∧
      Fin15AnchoredAtom4400 chi ∧
      Fin15AnchoredAtom4404 chi ∧
      Fin15AnchoredAtom4429 chi ∧
      Fin15AnchoredAtom4520 chi ∧
      Fin15AnchoredAtom4646 chi)) ∨
      ((Fin15AnchoredAtom4398 chi ∧
      Fin15AnchoredAtom4399 chi ∧
      Fin15AnchoredAtom4408 chi ∧
      Fin15AnchoredAtom4433 chi ∧
      Fin15AnchoredAtom4524 chi ∧
      Fin15AnchoredAtom4650 chi) ∨
      (Fin15AnchoredAtom4398 chi ∧
      Fin15AnchoredAtom4400 chi ∧
      Fin15AnchoredAtom4409 chi ∧
      Fin15AnchoredAtom4434 chi ∧
      Fin15AnchoredAtom4525 chi ∧
      Fin15AnchoredAtom4651 chi))))) ∨
      (((((Fin15AnchoredAtom4399 chi ∧
      Fin15AnchoredAtom4400 chi ∧
      Fin15AnchoredAtom4410 chi ∧
      Fin15AnchoredAtom4435 chi ∧
      Fin15AnchoredAtom4526 chi ∧
      Fin15AnchoredAtom4652 chi) ∨
      (Fin15AnchoredAtom4402 chi ∧
      Fin15AnchoredAtom4403 chi ∧
      Fin15AnchoredAtom4408 chi ∧
      Fin15AnchoredAtom4439 chi ∧
      Fin15AnchoredAtom4530 chi ∧
      Fin15AnchoredAtom4656 chi)) ∨
      ((Fin15AnchoredAtom4402 chi ∧
      Fin15AnchoredAtom4404 chi ∧
      Fin15AnchoredAtom4409 chi ∧
      Fin15AnchoredAtom4440 chi ∧
      Fin15AnchoredAtom4531 chi ∧
      Fin15AnchoredAtom4657 chi) ∨
      (Fin15AnchoredAtom4403 chi ∧
      Fin15AnchoredAtom4404 chi ∧
      Fin15AnchoredAtom4410 chi ∧
      Fin15AnchoredAtom4441 chi ∧
      Fin15AnchoredAtom4532 chi ∧
      Fin15AnchoredAtom4658 chi))) ∨
      (((Fin15AnchoredAtom4408 chi ∧
      Fin15AnchoredAtom4409 chi ∧
      Fin15AnchoredAtom4410 chi ∧
      Fin15AnchoredAtom4445 chi ∧
      Fin15AnchoredAtom4536 chi ∧
      Fin15AnchoredAtom4662 chi) ∨
      (Fin15AnchoredAtom4411 chi ∧
      Fin15AnchoredAtom4413 chi ∧
      Fin15AnchoredAtom4417 chi ∧
      Fin15AnchoredAtom4427 chi ∧
      Fin15AnchoredAtom4538 chi ∧
      Fin15AnchoredAtom4664 chi)) ∨
      ((Fin15AnchoredAtom4411 chi ∧
      Fin15AnchoredAtom4414 chi ∧
      Fin15AnchoredAtom4418 chi ∧
      Fin15AnchoredAtom4428 chi ∧
      Fin15AnchoredAtom4539 chi ∧
      Fin15AnchoredAtom4665 chi) ∨
      (Fin15AnchoredAtom4413 chi ∧
      Fin15AnchoredAtom4414 chi ∧
      Fin15AnchoredAtom4423 chi ∧
      Fin15AnchoredAtom4433 chi ∧
      Fin15AnchoredAtom4544 chi ∧
      Fin15AnchoredAtom4670 chi)))) ∨
      ((((Fin15AnchoredAtom4414 chi ∧
      Fin15AnchoredAtom4415 chi ∧
      Fin15AnchoredAtom4425 chi ∧
      Fin15AnchoredAtom4435 chi ∧
      Fin15AnchoredAtom4546 chi ∧
      Fin15AnchoredAtom4672 chi) ∨
      (Fin15AnchoredAtom4417 chi ∧
      Fin15AnchoredAtom4418 chi ∧
      Fin15AnchoredAtom4423 chi ∧
      Fin15AnchoredAtom4439 chi ∧
      Fin15AnchoredAtom4550 chi ∧
      Fin15AnchoredAtom4676 chi)) ∨
      ((Fin15AnchoredAtom4418 chi ∧
      Fin15AnchoredAtom4419 chi ∧
      Fin15AnchoredAtom4425 chi ∧
      Fin15AnchoredAtom4441 chi ∧
      Fin15AnchoredAtom4552 chi ∧
      Fin15AnchoredAtom4678 chi) ∨
      (Fin15AnchoredAtom4423 chi ∧
      Fin15AnchoredAtom4424 chi ∧
      Fin15AnchoredAtom4425 chi ∧
      Fin15AnchoredAtom4445 chi ∧
      Fin15AnchoredAtom4556 chi ∧
      Fin15AnchoredAtom4682 chi))) ∨
      (((Fin15AnchoredAtom4427 chi ∧
      Fin15AnchoredAtom4428 chi ∧
      Fin15AnchoredAtom4433 chi ∧
      Fin15AnchoredAtom4439 chi ∧
      Fin15AnchoredAtom4560 chi ∧
      Fin15AnchoredAtom4686 chi) ∨
      (Fin15AnchoredAtom4427 chi ∧
      Fin15AnchoredAtom4429 chi ∧
      Fin15AnchoredAtom4434 chi ∧
      Fin15AnchoredAtom4440 chi ∧
      Fin15AnchoredAtom4561 chi ∧
      Fin15AnchoredAtom4687 chi)) ∨
      ((Fin15AnchoredAtom4428 chi ∧
      Fin15AnchoredAtom4429 chi ∧
      Fin15AnchoredAtom4435 chi ∧
      Fin15AnchoredAtom4441 chi ∧
      Fin15AnchoredAtom4562 chi ∧
      Fin15AnchoredAtom4688 chi) ∨
      (Fin15AnchoredAtom4433 chi ∧
      Fin15AnchoredAtom4434 chi ∧
      Fin15AnchoredAtom4435 chi ∧
      Fin15AnchoredAtom4445 chi ∧
      Fin15AnchoredAtom4566 chi ∧
      Fin15AnchoredAtom4692 chi)))))) ∨
      ((((((Fin15AnchoredAtom4436 chi ∧
      Fin15AnchoredAtom4437 chi ∧
      Fin15AnchoredAtom4439 chi ∧
      Fin15AnchoredAtom4442 chi ∧
      Fin15AnchoredAtom4567 chi ∧
      Fin15AnchoredAtom4693 chi) ∨
      (Fin15AnchoredAtom4439 chi ∧
      Fin15AnchoredAtom4440 chi ∧
      Fin15AnchoredAtom4441 chi ∧
      Fin15AnchoredAtom4445 chi ∧
      Fin15AnchoredAtom4570 chi ∧
      Fin15AnchoredAtom4696 chi)) ∨
      ((Fin15AnchoredAtom4446 chi ∧
      Fin15AnchoredAtom4447 chi ∧
      Fin15AnchoredAtom4452 chi ∧
      Fin15AnchoredAtom4467 chi ∧
      Fin15AnchoredAtom4502 chi ∧
      Fin15AnchoredAtom4698 chi) ∨
      (Fin15AnchoredAtom4449 chi ∧
      Fin15AnchoredAtom4451 chi ∧
      Fin15AnchoredAtom4465 chi ∧
      Fin15AnchoredAtom4480 chi ∧
      Fin15AnchoredAtom4515 chi ∧
      Fin15AnchoredAtom4711 chi))) ∨
      (((Fin15AnchoredAtom4452 chi ∧
      Fin15AnchoredAtom4454 chi ∧
      Fin15AnchoredAtom4458 chi ∧
      Fin15AnchoredAtom4483 chi ∧
      Fin15AnchoredAtom4518 chi ∧
      Fin15AnchoredAtom4714 chi) ∨
      (Fin15AnchoredAtom4452 chi ∧
      Fin15AnchoredAtom4455 chi ∧
      Fin15AnchoredAtom4459 chi ∧
      Fin15AnchoredAtom4484 chi ∧
      Fin15AnchoredAtom4519 chi ∧
      Fin15AnchoredAtom4715 chi)) ∨
      ((Fin15AnchoredAtom4452 chi ∧
      Fin15AnchoredAtom4456 chi ∧
      Fin15AnchoredAtom4460 chi ∧
      Fin15AnchoredAtom4485 chi ∧
      Fin15AnchoredAtom4520 chi ∧
      Fin15AnchoredAtom4716 chi) ∨
      (Fin15AnchoredAtom4453 chi ∧
      Fin15AnchoredAtom4454 chi ∧
      Fin15AnchoredAtom4461 chi ∧
      Fin15AnchoredAtom4486 chi ∧
      Fin15AnchoredAtom4521 chi ∧
      Fin15AnchoredAtom4717 chi)))) ∨
      ((((Fin15AnchoredAtom4454 chi ∧
      Fin15AnchoredAtom4455 chi ∧
      Fin15AnchoredAtom4464 chi ∧
      Fin15AnchoredAtom4489 chi ∧
      Fin15AnchoredAtom4524 chi ∧
      Fin15AnchoredAtom4720 chi) ∨
      (Fin15AnchoredAtom4454 chi ∧
      Fin15AnchoredAtom4456 chi ∧
      Fin15AnchoredAtom4465 chi ∧
      Fin15AnchoredAtom4490 chi ∧
      Fin15AnchoredAtom4525 chi ∧
      Fin15AnchoredAtom4721 chi)) ∨
      ((Fin15AnchoredAtom4455 chi ∧
      Fin15AnchoredAtom4456 chi ∧
      Fin15AnchoredAtom4466 chi ∧
      Fin15AnchoredAtom4491 chi ∧
      Fin15AnchoredAtom4526 chi ∧
      Fin15AnchoredAtom4722 chi) ∨
      (Fin15AnchoredAtom4458 chi ∧
      Fin15AnchoredAtom4459 chi ∧
      Fin15AnchoredAtom4464 chi ∧
      Fin15AnchoredAtom4495 chi ∧
      Fin15AnchoredAtom4530 chi ∧
      Fin15AnchoredAtom4726 chi))) ∨
      (((Fin15AnchoredAtom4458 chi ∧
      Fin15AnchoredAtom4460 chi ∧
      Fin15AnchoredAtom4465 chi ∧
      Fin15AnchoredAtom4496 chi ∧
      Fin15AnchoredAtom4531 chi ∧
      Fin15AnchoredAtom4727 chi) ∨
      (Fin15AnchoredAtom4459 chi ∧
      Fin15AnchoredAtom4460 chi ∧
      Fin15AnchoredAtom4466 chi ∧
      Fin15AnchoredAtom4497 chi ∧
      Fin15AnchoredAtom4532 chi ∧
      Fin15AnchoredAtom4728 chi)) ∨
      ((Fin15AnchoredAtom4464 chi ∧
      Fin15AnchoredAtom4465 chi ∧
      Fin15AnchoredAtom4466 chi ∧
      Fin15AnchoredAtom4501 chi ∧
      Fin15AnchoredAtom4536 chi ∧
      Fin15AnchoredAtom4732 chi) ∨
      (Fin15AnchoredAtom4467 chi ∧
      Fin15AnchoredAtom4469 chi ∧
      Fin15AnchoredAtom4473 chi ∧
      Fin15AnchoredAtom4483 chi ∧
      Fin15AnchoredAtom4538 chi ∧
      Fin15AnchoredAtom4734 chi))))) ∨
      (((((Fin15AnchoredAtom4469 chi ∧
      Fin15AnchoredAtom4470 chi ∧
      Fin15AnchoredAtom4479 chi ∧
      Fin15AnchoredAtom4489 chi ∧
      Fin15AnchoredAtom4544 chi ∧
      Fin15AnchoredAtom4740 chi) ∨
      (Fin15AnchoredAtom4473 chi ∧
      Fin15AnchoredAtom4474 chi ∧
      Fin15AnchoredAtom4479 chi ∧
      Fin15AnchoredAtom4495 chi ∧
      Fin15AnchoredAtom4550 chi ∧
      Fin15AnchoredAtom4746 chi)) ∨
      ((Fin15AnchoredAtom4473 chi ∧
      Fin15AnchoredAtom4475 chi ∧
      Fin15AnchoredAtom4480 chi ∧
      Fin15AnchoredAtom4496 chi ∧
      Fin15AnchoredAtom4551 chi ∧
      Fin15AnchoredAtom4747 chi) ∨
      (Fin15AnchoredAtom4474 chi ∧
      Fin15AnchoredAtom4475 chi ∧
      Fin15AnchoredAtom4481 chi ∧
      Fin15AnchoredAtom4497 chi ∧
      Fin15AnchoredAtom4552 chi ∧
      Fin15AnchoredAtom4748 chi))) ∨
      (((Fin15AnchoredAtom4479 chi ∧
      Fin15AnchoredAtom4480 chi ∧
      Fin15AnchoredAtom4481 chi ∧
      Fin15AnchoredAtom4501 chi ∧
      Fin15AnchoredAtom4556 chi ∧
      Fin15AnchoredAtom4752 chi) ∨
      (Fin15AnchoredAtom4483 chi ∧
      Fin15AnchoredAtom4484 chi ∧
      Fin15AnchoredAtom4489 chi ∧
      Fin15AnchoredAtom4495 chi ∧
      Fin15AnchoredAtom4560 chi ∧
      Fin15AnchoredAtom4756 chi)) ∨
      ((Fin15AnchoredAtom4483 chi ∧
      Fin15AnchoredAtom4485 chi ∧
      Fin15AnchoredAtom4490 chi ∧
      Fin15AnchoredAtom4496 chi ∧
      Fin15AnchoredAtom4561 chi ∧
      Fin15AnchoredAtom4757 chi) ∨
      (Fin15AnchoredAtom4484 chi ∧
      Fin15AnchoredAtom4485 chi ∧
      Fin15AnchoredAtom4491 chi ∧
      Fin15AnchoredAtom4497 chi ∧
      Fin15AnchoredAtom4562 chi ∧
      Fin15AnchoredAtom4758 chi)))) ∨
      ((((Fin15AnchoredAtom4489 chi ∧
      Fin15AnchoredAtom4490 chi ∧
      Fin15AnchoredAtom4491 chi ∧
      Fin15AnchoredAtom4501 chi ∧
      Fin15AnchoredAtom4566 chi ∧
      Fin15AnchoredAtom4762 chi) ∨
      (Fin15AnchoredAtom4495 chi ∧
      Fin15AnchoredAtom4496 chi ∧
      Fin15AnchoredAtom4497 chi ∧
      Fin15AnchoredAtom4501 chi ∧
      Fin15AnchoredAtom4570 chi ∧
      Fin15AnchoredAtom4766 chi)) ∨
      ((Fin15AnchoredAtom4505 chi ∧
      Fin15AnchoredAtom4506 chi ∧
      Fin15AnchoredAtom4516 chi ∧
      Fin15AnchoredAtom4526 chi ∧
      Fin15AnchoredAtom4546 chi ∧
      Fin15AnchoredAtom4777 chi) ∨
      (Fin15AnchoredAtom4508 chi ∧
      Fin15AnchoredAtom4509 chi ∧
      Fin15AnchoredAtom4514 chi ∧
      Fin15AnchoredAtom4530 chi ∧
      Fin15AnchoredAtom4550 chi ∧
      Fin15AnchoredAtom4781 chi))) ∨
      (((Fin15AnchoredAtom4509 chi ∧
      Fin15AnchoredAtom4510 chi ∧
      Fin15AnchoredAtom4516 chi ∧
      Fin15AnchoredAtom4532 chi ∧
      Fin15AnchoredAtom4552 chi ∧
      Fin15AnchoredAtom4783 chi) ∨
      (Fin15AnchoredAtom4518 chi ∧
      Fin15AnchoredAtom4519 chi ∧
      Fin15AnchoredAtom4524 chi ∧
      Fin15AnchoredAtom4530 chi ∧
      Fin15AnchoredAtom4560 chi ∧
      Fin15AnchoredAtom4791 chi)) ∨
      ((Fin15AnchoredAtom4518 chi ∧
      Fin15AnchoredAtom4520 chi ∧
      Fin15AnchoredAtom4525 chi ∧
      Fin15AnchoredAtom4531 chi ∧
      Fin15AnchoredAtom4561 chi ∧
      Fin15AnchoredAtom4792 chi) ∨
      (Fin15AnchoredAtom4519 chi ∧
      Fin15AnchoredAtom4520 chi ∧
      Fin15AnchoredAtom4526 chi ∧
      Fin15AnchoredAtom4532 chi ∧
      Fin15AnchoredAtom4562 chi ∧
      Fin15AnchoredAtom4793 chi)))))))) ∨
      (((((((Fin15AnchoredAtom4524 chi ∧
      Fin15AnchoredAtom4525 chi ∧
      Fin15AnchoredAtom4526 chi ∧
      Fin15AnchoredAtom4536 chi ∧
      Fin15AnchoredAtom4566 chi ∧
      Fin15AnchoredAtom4797 chi) ∨
      ((Fin15AnchoredAtom4527 chi ∧
      Fin15AnchoredAtom4528 chi ∧
      Fin15AnchoredAtom4530 chi ∧
      Fin15AnchoredAtom4533 chi ∧
      Fin15AnchoredAtom4567 chi ∧
      Fin15AnchoredAtom4798 chi) ∨
      (Fin15AnchoredAtom4527 chi ∧
      Fin15AnchoredAtom4529 chi ∧
      Fin15AnchoredAtom4531 chi ∧
      Fin15AnchoredAtom4534 chi ∧
      Fin15AnchoredAtom4568 chi ∧
      Fin15AnchoredAtom4799 chi))) ∨
      (((Fin15AnchoredAtom4530 chi ∧
      Fin15AnchoredAtom4531 chi ∧
      Fin15AnchoredAtom4532 chi ∧
      Fin15AnchoredAtom4536 chi ∧
      Fin15AnchoredAtom4570 chi ∧
      Fin15AnchoredAtom4801 chi) ∨
      (Fin15AnchoredAtom4538 chi ∧
      Fin15AnchoredAtom4539 chi ∧
      Fin15AnchoredAtom4544 chi ∧
      Fin15AnchoredAtom4550 chi ∧
      Fin15AnchoredAtom4560 chi ∧
      Fin15AnchoredAtom4806 chi)) ∨
      ((Fin15AnchoredAtom4538 chi ∧
      Fin15AnchoredAtom4540 chi ∧
      Fin15AnchoredAtom4545 chi ∧
      Fin15AnchoredAtom4551 chi ∧
      Fin15AnchoredAtom4561 chi ∧
      Fin15AnchoredAtom4807 chi) ∨
      (Fin15AnchoredAtom4550 chi ∧
      Fin15AnchoredAtom4551 chi ∧
      Fin15AnchoredAtom4552 chi ∧
      Fin15AnchoredAtom4556 chi ∧
      Fin15AnchoredAtom4570 chi ∧
      Fin15AnchoredAtom4816 chi)))) ∨
      ((((Fin15AnchoredAtom4560 chi ∧
      Fin15AnchoredAtom4561 chi ∧
      Fin15AnchoredAtom4562 chi ∧
      Fin15AnchoredAtom4566 chi ∧
      Fin15AnchoredAtom4570 chi ∧
      Fin15AnchoredAtom4821 chi) ∨
      (Fin15AnchoredAtom4572 chi ∧
      Fin15AnchoredAtom4573 chi ∧
      Fin15AnchoredAtom4578 chi ∧
      Fin15AnchoredAtom4593 chi ∧
      Fin15AnchoredAtom4628 chi ∧
      Fin15AnchoredAtom4698 chi)) ∨
      ((Fin15AnchoredAtom4572 chi ∧
      Fin15AnchoredAtom4575 chi ∧
      Fin15AnchoredAtom4580 chi ∧
      Fin15AnchoredAtom4595 chi ∧
      Fin15AnchoredAtom4630 chi ∧
      Fin15AnchoredAtom4700 chi) ∨
      (Fin15AnchoredAtom4572 chi ∧
      Fin15AnchoredAtom4576 chi ∧
      Fin15AnchoredAtom4581 chi ∧
      Fin15AnchoredAtom4596 chi ∧
      Fin15AnchoredAtom4631 chi ∧
      Fin15AnchoredAtom4701 chi))) ∨
      (((Fin15AnchoredAtom4573 chi ∧
      Fin15AnchoredAtom4575 chi ∧
      Fin15AnchoredAtom4584 chi ∧
      Fin15AnchoredAtom4599 chi ∧
      Fin15AnchoredAtom4634 chi ∧
      Fin15AnchoredAtom4704 chi) ∨
      (Fin15AnchoredAtom4573 chi ∧
      Fin15AnchoredAtom4576 chi ∧
      Fin15AnchoredAtom4585 chi ∧
      Fin15AnchoredAtom4600 chi ∧
      Fin15AnchoredAtom4635 chi ∧
      Fin15AnchoredAtom4705 chi)) ∨
      ((Fin15AnchoredAtom4573 chi ∧
      Fin15AnchoredAtom4577 chi ∧
      Fin15AnchoredAtom4586 chi ∧
      Fin15AnchoredAtom4601 chi ∧
      Fin15AnchoredAtom4636 chi ∧
      Fin15AnchoredAtom4706 chi) ∨
      (Fin15AnchoredAtom4575 chi ∧
      Fin15AnchoredAtom4576 chi ∧
      Fin15AnchoredAtom4590 chi ∧
      Fin15AnchoredAtom4605 chi ∧
      Fin15AnchoredAtom4640 chi ∧
      Fin15AnchoredAtom4710 chi))))) ∨
      (((((Fin15AnchoredAtom4575 chi ∧
      Fin15AnchoredAtom4577 chi ∧
      Fin15AnchoredAtom4591 chi ∧
      Fin15AnchoredAtom4606 chi ∧
      Fin15AnchoredAtom4641 chi ∧
      Fin15AnchoredAtom4711 chi) ∨
      (Fin15AnchoredAtom4576 chi ∧
      Fin15AnchoredAtom4577 chi ∧
      Fin15AnchoredAtom4592 chi ∧
      Fin15AnchoredAtom4607 chi ∧
      Fin15AnchoredAtom4642 chi ∧
      Fin15AnchoredAtom4712 chi)) ∨
      ((Fin15AnchoredAtom4578 chi ∧
      Fin15AnchoredAtom4579 chi ∧
      Fin15AnchoredAtom4583 chi ∧
      Fin15AnchoredAtom4608 chi ∧
      Fin15AnchoredAtom4643 chi ∧
      Fin15AnchoredAtom4713 chi) ∨
      (Fin15AnchoredAtom4578 chi ∧
      Fin15AnchoredAtom4580 chi ∧
      Fin15AnchoredAtom4584 chi ∧
      Fin15AnchoredAtom4609 chi ∧
      Fin15AnchoredAtom4644 chi ∧
      Fin15AnchoredAtom4714 chi))) ∨
      (((Fin15AnchoredAtom4578 chi ∧
      Fin15AnchoredAtom4581 chi ∧
      Fin15AnchoredAtom4585 chi ∧
      Fin15AnchoredAtom4610 chi ∧
      Fin15AnchoredAtom4645 chi ∧
      Fin15AnchoredAtom4715 chi) ∨
      (Fin15AnchoredAtom4578 chi ∧
      Fin15AnchoredAtom4582 chi ∧
      Fin15AnchoredAtom4586 chi ∧
      Fin15AnchoredAtom4611 chi ∧
      Fin15AnchoredAtom4646 chi ∧
      Fin15AnchoredAtom4716 chi)) ∨
      ((Fin15AnchoredAtom4579 chi ∧
      Fin15AnchoredAtom4580 chi ∧
      Fin15AnchoredAtom4587 chi ∧
      Fin15AnchoredAtom4612 chi ∧
      Fin15AnchoredAtom4647 chi ∧
      Fin15AnchoredAtom4717 chi) ∨
      (Fin15AnchoredAtom4580 chi ∧
      Fin15AnchoredAtom4581 chi ∧
      Fin15AnchoredAtom4590 chi ∧
      Fin15AnchoredAtom4615 chi ∧
      Fin15AnchoredAtom4650 chi ∧
      Fin15AnchoredAtom4720 chi)))) ∨
      ((((Fin15AnchoredAtom4580 chi ∧
      Fin15AnchoredAtom4582 chi ∧
      Fin15AnchoredAtom4591 chi ∧
      Fin15AnchoredAtom4616 chi ∧
      Fin15AnchoredAtom4651 chi ∧
      Fin15AnchoredAtom4721 chi) ∨
      (Fin15AnchoredAtom4581 chi ∧
      Fin15AnchoredAtom4582 chi ∧
      Fin15AnchoredAtom4592 chi ∧
      Fin15AnchoredAtom4617 chi ∧
      Fin15AnchoredAtom4652 chi ∧
      Fin15AnchoredAtom4722 chi)) ∨
      ((Fin15AnchoredAtom4584 chi ∧
      Fin15AnchoredAtom4585 chi ∧
      Fin15AnchoredAtom4590 chi ∧
      Fin15AnchoredAtom4621 chi ∧
      Fin15AnchoredAtom4656 chi ∧
      Fin15AnchoredAtom4726 chi) ∨
      (Fin15AnchoredAtom4584 chi ∧
      Fin15AnchoredAtom4586 chi ∧
      Fin15AnchoredAtom4591 chi ∧
      Fin15AnchoredAtom4622 chi ∧
      Fin15AnchoredAtom4657 chi ∧
      Fin15AnchoredAtom4727 chi))) ∨
      (((Fin15AnchoredAtom4585 chi ∧
      Fin15AnchoredAtom4586 chi ∧
      Fin15AnchoredAtom4592 chi ∧
      Fin15AnchoredAtom4623 chi ∧
      Fin15AnchoredAtom4658 chi ∧
      Fin15AnchoredAtom4728 chi) ∨
      (Fin15AnchoredAtom4590 chi ∧
      Fin15AnchoredAtom4591 chi ∧
      Fin15AnchoredAtom4592 chi ∧
      Fin15AnchoredAtom4627 chi ∧
      Fin15AnchoredAtom4662 chi ∧
      Fin15AnchoredAtom4732 chi)) ∨
      ((Fin15AnchoredAtom4593 chi ∧
      Fin15AnchoredAtom4595 chi ∧
      Fin15AnchoredAtom4599 chi ∧
      Fin15AnchoredAtom4609 chi ∧
      Fin15AnchoredAtom4664 chi ∧
      Fin15AnchoredAtom4734 chi) ∨
      (Fin15AnchoredAtom4593 chi ∧
      Fin15AnchoredAtom4596 chi ∧
      Fin15AnchoredAtom4600 chi ∧
      Fin15AnchoredAtom4610 chi ∧
      Fin15AnchoredAtom4665 chi ∧
      Fin15AnchoredAtom4735 chi)))))) ∨
      ((((((Fin15AnchoredAtom4593 chi ∧
      Fin15AnchoredAtom4597 chi ∧
      Fin15AnchoredAtom4601 chi ∧
      Fin15AnchoredAtom4611 chi ∧
      Fin15AnchoredAtom4666 chi ∧
      Fin15AnchoredAtom4736 chi) ∨
      (Fin15AnchoredAtom4595 chi ∧
      Fin15AnchoredAtom4596 chi ∧
      Fin15AnchoredAtom4605 chi ∧
      Fin15AnchoredAtom4615 chi ∧
      Fin15AnchoredAtom4670 chi ∧
      Fin15AnchoredAtom4740 chi)) ∨
      ((Fin15AnchoredAtom4596 chi ∧
      Fin15AnchoredAtom4597 chi ∧
      Fin15AnchoredAtom4607 chi ∧
      Fin15AnchoredAtom4617 chi ∧
      Fin15AnchoredAtom4672 chi ∧
      Fin15AnchoredAtom4742 chi) ∨
      (Fin15AnchoredAtom4599 chi ∧
      Fin15AnchoredAtom4600 chi ∧
      Fin15AnchoredAtom4605 chi ∧
      Fin15AnchoredAtom4621 chi ∧
      Fin15AnchoredAtom4676 chi ∧
      Fin15AnchoredAtom4746 chi))) ∨
      (((Fin15AnchoredAtom4599 chi ∧
      Fin15AnchoredAtom4601 chi ∧
      Fin15AnchoredAtom4606 chi ∧
      Fin15AnchoredAtom4622 chi ∧
      Fin15AnchoredAtom4677 chi ∧
      Fin15AnchoredAtom4747 chi) ∨
      (Fin15AnchoredAtom4600 chi ∧
      Fin15AnchoredAtom4601 chi ∧
      Fin15AnchoredAtom4607 chi ∧
      Fin15AnchoredAtom4623 chi ∧
      Fin15AnchoredAtom4678 chi ∧
      Fin15AnchoredAtom4748 chi)) ∨
      ((Fin15AnchoredAtom4605 chi ∧
      Fin15AnchoredAtom4606 chi ∧
      Fin15AnchoredAtom4607 chi ∧
      Fin15AnchoredAtom4627 chi ∧
      Fin15AnchoredAtom4682 chi ∧
      Fin15AnchoredAtom4752 chi) ∨
      (Fin15AnchoredAtom4609 chi ∧
      Fin15AnchoredAtom4610 chi ∧
      Fin15AnchoredAtom4615 chi ∧
      Fin15AnchoredAtom4621 chi ∧
      Fin15AnchoredAtom4686 chi ∧
      Fin15AnchoredAtom4756 chi)))) ∨
      ((((Fin15AnchoredAtom4609 chi ∧
      Fin15AnchoredAtom4611 chi ∧
      Fin15AnchoredAtom4616 chi ∧
      Fin15AnchoredAtom4622 chi ∧
      Fin15AnchoredAtom4687 chi ∧
      Fin15AnchoredAtom4757 chi) ∨
      (Fin15AnchoredAtom4610 chi ∧
      Fin15AnchoredAtom4611 chi ∧
      Fin15AnchoredAtom4617 chi ∧
      Fin15AnchoredAtom4623 chi ∧
      Fin15AnchoredAtom4688 chi ∧
      Fin15AnchoredAtom4758 chi)) ∨
      ((Fin15AnchoredAtom4615 chi ∧
      Fin15AnchoredAtom4616 chi ∧
      Fin15AnchoredAtom4617 chi ∧
      Fin15AnchoredAtom4627 chi ∧
      Fin15AnchoredAtom4692 chi ∧
      Fin15AnchoredAtom4762 chi) ∨
      (Fin15AnchoredAtom4618 chi ∧
      Fin15AnchoredAtom4619 chi ∧
      Fin15AnchoredAtom4621 chi ∧
      Fin15AnchoredAtom4624 chi ∧
      Fin15AnchoredAtom4693 chi ∧
      Fin15AnchoredAtom4763 chi))) ∨
      (((Fin15AnchoredAtom4621 chi ∧
      Fin15AnchoredAtom4622 chi ∧
      Fin15AnchoredAtom4623 chi ∧
      Fin15AnchoredAtom4627 chi ∧
      Fin15AnchoredAtom4696 chi ∧
      Fin15AnchoredAtom4766 chi) ∨
      (Fin15AnchoredAtom4628 chi ∧
      Fin15AnchoredAtom4630 chi ∧
      Fin15AnchoredAtom4634 chi ∧
      Fin15AnchoredAtom4644 chi ∧
      Fin15AnchoredAtom4664 chi ∧
      Fin15AnchoredAtom4769 chi)) ∨
      ((Fin15AnchoredAtom4640 chi ∧
      Fin15AnchoredAtom4641 chi ∧
      Fin15AnchoredAtom4642 chi ∧
      Fin15AnchoredAtom4662 chi ∧
      Fin15AnchoredAtom4682 chi ∧
      Fin15AnchoredAtom4787 chi) ∨
      (Fin15AnchoredAtom4643 chi ∧
      Fin15AnchoredAtom4644 chi ∧
      Fin15AnchoredAtom4647 chi ∧
      Fin15AnchoredAtom4653 chi ∧
      Fin15AnchoredAtom4683 chi ∧
      Fin15AnchoredAtom4788 chi))))) ∨
      (((((Fin15AnchoredAtom4644 chi ∧
      Fin15AnchoredAtom4645 chi ∧
      Fin15AnchoredAtom4650 chi ∧
      Fin15AnchoredAtom4656 chi ∧
      Fin15AnchoredAtom4686 chi ∧
      Fin15AnchoredAtom4791 chi) ∨
      (Fin15AnchoredAtom4644 chi ∧
      Fin15AnchoredAtom4646 chi ∧
      Fin15AnchoredAtom4651 chi ∧
      Fin15AnchoredAtom4657 chi ∧
      Fin15AnchoredAtom4687 chi ∧
      Fin15AnchoredAtom4792 chi)) ∨
      ((Fin15AnchoredAtom4645 chi ∧
      Fin15AnchoredAtom4646 chi ∧
      Fin15AnchoredAtom4652 chi ∧
      Fin15AnchoredAtom4658 chi ∧
      Fin15AnchoredAtom4688 chi ∧
      Fin15AnchoredAtom4793 chi) ∨
      (Fin15AnchoredAtom4650 chi ∧
      Fin15AnchoredAtom4651 chi ∧
      Fin15AnchoredAtom4652 chi ∧
      Fin15AnchoredAtom4662 chi ∧
      Fin15AnchoredAtom4692 chi ∧
      Fin15AnchoredAtom4797 chi))) ∨
      (((Fin15AnchoredAtom4656 chi ∧
      Fin15AnchoredAtom4657 chi ∧
      Fin15AnchoredAtom4658 chi ∧
      Fin15AnchoredAtom4662 chi ∧
      Fin15AnchoredAtom4696 chi ∧
      Fin15AnchoredAtom4801 chi) ∨
      (Fin15AnchoredAtom4664 chi ∧
      Fin15AnchoredAtom4665 chi ∧
      Fin15AnchoredAtom4670 chi ∧
      Fin15AnchoredAtom4676 chi ∧
      Fin15AnchoredAtom4686 chi ∧
      Fin15AnchoredAtom4806 chi)) ∨
      ((Fin15AnchoredAtom4664 chi ∧
      Fin15AnchoredAtom4666 chi ∧
      Fin15AnchoredAtom4671 chi ∧
      Fin15AnchoredAtom4677 chi ∧
      Fin15AnchoredAtom4687 chi ∧
      Fin15AnchoredAtom4807 chi) ∨
      (Fin15AnchoredAtom4665 chi ∧
      Fin15AnchoredAtom4666 chi ∧
      Fin15AnchoredAtom4672 chi ∧
      Fin15AnchoredAtom4678 chi ∧
      Fin15AnchoredAtom4688 chi ∧
      Fin15AnchoredAtom4808 chi)))) ∨
      ((((Fin15AnchoredAtom4670 chi ∧
      Fin15AnchoredAtom4671 chi ∧
      Fin15AnchoredAtom4672 chi ∧
      Fin15AnchoredAtom4682 chi ∧
      Fin15AnchoredAtom4692 chi ∧
      Fin15AnchoredAtom4812 chi) ∨
      (Fin15AnchoredAtom4676 chi ∧
      Fin15AnchoredAtom4677 chi ∧
      Fin15AnchoredAtom4678 chi ∧
      Fin15AnchoredAtom4682 chi ∧
      Fin15AnchoredAtom4696 chi ∧
      Fin15AnchoredAtom4816 chi)) ∨
      ((Fin15AnchoredAtom4686 chi ∧
      Fin15AnchoredAtom4687 chi ∧
      Fin15AnchoredAtom4688 chi ∧
      Fin15AnchoredAtom4692 chi ∧
      Fin15AnchoredAtom4696 chi ∧
      Fin15AnchoredAtom4821 chi) ∨
      (Fin15AnchoredAtom4698 chi ∧
      Fin15AnchoredAtom4700 chi ∧
      Fin15AnchoredAtom4704 chi ∧
      Fin15AnchoredAtom4714 chi ∧
      Fin15AnchoredAtom4734 chi ∧
      Fin15AnchoredAtom4769 chi))) ∨
      (((Fin15AnchoredAtom4698 chi ∧
      Fin15AnchoredAtom4701 chi ∧
      Fin15AnchoredAtom4705 chi ∧
      Fin15AnchoredAtom4715 chi ∧
      Fin15AnchoredAtom4735 chi ∧
      Fin15AnchoredAtom4770 chi) ∨
      (Fin15AnchoredAtom4698 chi ∧
      Fin15AnchoredAtom4702 chi ∧
      Fin15AnchoredAtom4706 chi ∧
      Fin15AnchoredAtom4716 chi ∧
      Fin15AnchoredAtom4736 chi ∧
      Fin15AnchoredAtom4771 chi)) ∨
      ((Fin15AnchoredAtom4700 chi ∧
      Fin15AnchoredAtom4701 chi ∧
      Fin15AnchoredAtom4710 chi ∧
      Fin15AnchoredAtom4720 chi ∧
      Fin15AnchoredAtom4740 chi ∧
      Fin15AnchoredAtom4775 chi) ∨
      (Fin15AnchoredAtom4700 chi ∧
      Fin15AnchoredAtom4702 chi ∧
      Fin15AnchoredAtom4711 chi ∧
      Fin15AnchoredAtom4721 chi ∧
      Fin15AnchoredAtom4741 chi ∧
      Fin15AnchoredAtom4776 chi))))))) ∨
      ((((((Fin15AnchoredAtom4701 chi ∧
      Fin15AnchoredAtom4702 chi ∧
      Fin15AnchoredAtom4712 chi ∧
      Fin15AnchoredAtom4722 chi ∧
      Fin15AnchoredAtom4742 chi ∧
      Fin15AnchoredAtom4777 chi) ∨
      ((Fin15AnchoredAtom4704 chi ∧
      Fin15AnchoredAtom4705 chi ∧
      Fin15AnchoredAtom4710 chi ∧
      Fin15AnchoredAtom4726 chi ∧
      Fin15AnchoredAtom4746 chi ∧
      Fin15AnchoredAtom4781 chi) ∨
      (Fin15AnchoredAtom4704 chi ∧
      Fin15AnchoredAtom4706 chi ∧
      Fin15AnchoredAtom4711 chi ∧
      Fin15AnchoredAtom4727 chi ∧
      Fin15AnchoredAtom4747 chi ∧
      Fin15AnchoredAtom4782 chi))) ∨
      (((Fin15AnchoredAtom4705 chi ∧
      Fin15AnchoredAtom4706 chi ∧
      Fin15AnchoredAtom4712 chi ∧
      Fin15AnchoredAtom4728 chi ∧
      Fin15AnchoredAtom4748 chi ∧
      Fin15AnchoredAtom4783 chi) ∨
      (Fin15AnchoredAtom4710 chi ∧
      Fin15AnchoredAtom4711 chi ∧
      Fin15AnchoredAtom4712 chi ∧
      Fin15AnchoredAtom4732 chi ∧
      Fin15AnchoredAtom4752 chi ∧
      Fin15AnchoredAtom4787 chi)) ∨
      ((Fin15AnchoredAtom4713 chi ∧
      Fin15AnchoredAtom4714 chi ∧
      Fin15AnchoredAtom4717 chi ∧
      Fin15AnchoredAtom4723 chi ∧
      Fin15AnchoredAtom4753 chi ∧
      Fin15AnchoredAtom4788 chi) ∨
      (Fin15AnchoredAtom4714 chi ∧
      Fin15AnchoredAtom4715 chi ∧
      Fin15AnchoredAtom4720 chi ∧
      Fin15AnchoredAtom4726 chi ∧
      Fin15AnchoredAtom4756 chi ∧
      Fin15AnchoredAtom4791 chi)))) ∨
      ((((Fin15AnchoredAtom4714 chi ∧
      Fin15AnchoredAtom4716 chi ∧
      Fin15AnchoredAtom4721 chi ∧
      Fin15AnchoredAtom4727 chi ∧
      Fin15AnchoredAtom4757 chi ∧
      Fin15AnchoredAtom4792 chi) ∨
      (Fin15AnchoredAtom4715 chi ∧
      Fin15AnchoredAtom4716 chi ∧
      Fin15AnchoredAtom4722 chi ∧
      Fin15AnchoredAtom4728 chi ∧
      Fin15AnchoredAtom4758 chi ∧
      Fin15AnchoredAtom4793 chi)) ∨
      ((Fin15AnchoredAtom4720 chi ∧
      Fin15AnchoredAtom4721 chi ∧
      Fin15AnchoredAtom4722 chi ∧
      Fin15AnchoredAtom4732 chi ∧
      Fin15AnchoredAtom4762 chi ∧
      Fin15AnchoredAtom4797 chi) ∨
      (Fin15AnchoredAtom4726 chi ∧
      Fin15AnchoredAtom4727 chi ∧
      Fin15AnchoredAtom4728 chi ∧
      Fin15AnchoredAtom4732 chi ∧
      Fin15AnchoredAtom4766 chi ∧
      Fin15AnchoredAtom4801 chi))) ∨
      (((Fin15AnchoredAtom4734 chi ∧
      Fin15AnchoredAtom4735 chi ∧
      Fin15AnchoredAtom4740 chi ∧
      Fin15AnchoredAtom4746 chi ∧
      Fin15AnchoredAtom4756 chi ∧
      Fin15AnchoredAtom4806 chi) ∨
      (Fin15AnchoredAtom4734 chi ∧
      Fin15AnchoredAtom4736 chi ∧
      Fin15AnchoredAtom4741 chi ∧
      Fin15AnchoredAtom4747 chi ∧
      Fin15AnchoredAtom4757 chi ∧
      Fin15AnchoredAtom4807 chi)) ∨
      ((Fin15AnchoredAtom4735 chi ∧
      Fin15AnchoredAtom4736 chi ∧
      Fin15AnchoredAtom4742 chi ∧
      Fin15AnchoredAtom4748 chi ∧
      Fin15AnchoredAtom4758 chi ∧
      Fin15AnchoredAtom4808 chi) ∨
      (Fin15AnchoredAtom4740 chi ∧
      Fin15AnchoredAtom4741 chi ∧
      Fin15AnchoredAtom4742 chi ∧
      Fin15AnchoredAtom4752 chi ∧
      Fin15AnchoredAtom4762 chi ∧
      Fin15AnchoredAtom4812 chi))))) ∨
      (((((Fin15AnchoredAtom4746 chi ∧
      Fin15AnchoredAtom4747 chi ∧
      Fin15AnchoredAtom4748 chi ∧
      Fin15AnchoredAtom4752 chi ∧
      Fin15AnchoredAtom4766 chi ∧
      Fin15AnchoredAtom4816 chi) ∨
      (Fin15AnchoredAtom4756 chi ∧
      Fin15AnchoredAtom4757 chi ∧
      Fin15AnchoredAtom4758 chi ∧
      Fin15AnchoredAtom4762 chi ∧
      Fin15AnchoredAtom4766 chi ∧
      Fin15AnchoredAtom4821 chi)) ∨
      ((Fin15AnchoredAtom4769 chi ∧
      Fin15AnchoredAtom4770 chi ∧
      Fin15AnchoredAtom4775 chi ∧
      Fin15AnchoredAtom4781 chi ∧
      Fin15AnchoredAtom4791 chi ∧
      Fin15AnchoredAtom4806 chi) ∨
      (Fin15AnchoredAtom4769 chi ∧
      Fin15AnchoredAtom4771 chi ∧
      Fin15AnchoredAtom4776 chi ∧
      Fin15AnchoredAtom4782 chi ∧
      Fin15AnchoredAtom4792 chi ∧
      Fin15AnchoredAtom4807 chi))) ∨
      (((Fin15AnchoredAtom4770 chi ∧
      Fin15AnchoredAtom4771 chi ∧
      Fin15AnchoredAtom4777 chi ∧
      Fin15AnchoredAtom4783 chi ∧
      Fin15AnchoredAtom4793 chi ∧
      Fin15AnchoredAtom4808 chi) ∨
      (Fin15AnchoredAtom4775 chi ∧
      Fin15AnchoredAtom4776 chi ∧
      Fin15AnchoredAtom4777 chi ∧
      Fin15AnchoredAtom4787 chi ∧
      Fin15AnchoredAtom4797 chi ∧
      Fin15AnchoredAtom4812 chi)) ∨
      ((Fin15AnchoredAtom4781 chi ∧
      Fin15AnchoredAtom4782 chi ∧
      Fin15AnchoredAtom4783 chi ∧
      Fin15AnchoredAtom4787 chi ∧
      Fin15AnchoredAtom4801 chi ∧
      Fin15AnchoredAtom4816 chi) ∨
      (Fin15AnchoredAtom4789 chi ∧
      Fin15AnchoredAtom4790 chi ∧
      Fin15AnchoredAtom4793 chi ∧
      Fin15AnchoredAtom4796 chi ∧
      Fin15AnchoredAtom4800 chi ∧
      Fin15AnchoredAtom4820 chi)))) ∨
      ((((Fin15AnchoredAtom4791 chi ∧
      Fin15AnchoredAtom4792 chi ∧
      Fin15AnchoredAtom4793 chi ∧
      Fin15AnchoredAtom4797 chi ∧
      Fin15AnchoredAtom4801 chi ∧
      Fin15AnchoredAtom4821 chi) ∨
      (Fin15AnchoredAtom4794 chi ∧
      Fin15AnchoredAtom4795 chi ∧
      Fin15AnchoredAtom4796 chi ∧
      Fin15AnchoredAtom4797 chi ∧
      Fin15AnchoredAtom4802 chi ∧
      Fin15AnchoredAtom4822 chi)) ∨
      ((Fin15AnchoredAtom4806 chi ∧
      Fin15AnchoredAtom4807 chi ∧
      Fin15AnchoredAtom4808 chi ∧
      Fin15AnchoredAtom4812 chi ∧
      Fin15AnchoredAtom4816 chi ∧
      Fin15AnchoredAtom4821 chi) ∨
      (¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1942 chi ∧
      ¬Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom1987 chi ∧
      ¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom2126 chi ∧
      ¬Fin15AnchoredAtom2162 chi ∧
      ¬Fin15AnchoredAtom2163 chi ∧
      ¬Fin15AnchoredAtom2171 chi ∧
      ¬Fin15AnchoredAtom2207 chi ∧
      ¬Fin15AnchoredAtom2327 chi ∧
      ¬Fin15AnchoredAtom2328 chi ∧
      ¬Fin15AnchoredAtom2336 chi ∧
      ¬Fin15AnchoredAtom2372 chi ∧
      ¬Fin15AnchoredAtom2492 chi ∧
      ¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom2877 chi ∧
      ¬Fin15AnchoredAtom2878 chi ∧
      ¬Fin15AnchoredAtom2886 chi ∧
      ¬Fin15AnchoredAtom2922 chi ∧
      ¬Fin15AnchoredAtom3042 chi ∧
      ¬Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom3051 chi ∧
      ¬Fin15AnchoredAtom3087 chi ∧
      ¬Fin15AnchoredAtom3207 chi ∧
      ¬Fin15AnchoredAtom3537 chi ∧
      ¬Fin15AnchoredAtom3538 chi ∧
      ¬Fin15AnchoredAtom3546 chi ∧
      ¬Fin15AnchoredAtom3582 chi ∧
      ¬Fin15AnchoredAtom3702 chi ∧
      ¬Fin15AnchoredAtom4032 chi))) ∨
      (((¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1942 chi ∧
      ¬Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom1989 chi ∧
      ¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom2128 chi ∧
      ¬Fin15AnchoredAtom2162 chi ∧
      ¬Fin15AnchoredAtom2165 chi ∧
      ¬Fin15AnchoredAtom2173 chi ∧
      ¬Fin15AnchoredAtom2209 chi ∧
      ¬Fin15AnchoredAtom2327 chi ∧
      ¬Fin15AnchoredAtom2330 chi ∧
      ¬Fin15AnchoredAtom2338 chi ∧
      ¬Fin15AnchoredAtom2374 chi ∧
      ¬Fin15AnchoredAtom2494 chi ∧
      ¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom2877 chi ∧
      ¬Fin15AnchoredAtom2880 chi ∧
      ¬Fin15AnchoredAtom2888 chi ∧
      ¬Fin15AnchoredAtom2924 chi ∧
      ¬Fin15AnchoredAtom3042 chi ∧
      ¬Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom3053 chi ∧
      ¬Fin15AnchoredAtom3089 chi ∧
      ¬Fin15AnchoredAtom3209 chi ∧
      ¬Fin15AnchoredAtom3537 chi ∧
      ¬Fin15AnchoredAtom3540 chi ∧
      ¬Fin15AnchoredAtom3548 chi ∧
      ¬Fin15AnchoredAtom3584 chi ∧
      ¬Fin15AnchoredAtom3704 chi ∧
      ¬Fin15AnchoredAtom4034 chi) ∨
      (¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1942 chi ∧
      ¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom1990 chi ∧
      ¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2129 chi ∧
      ¬Fin15AnchoredAtom2162 chi ∧
      ¬Fin15AnchoredAtom2166 chi ∧
      ¬Fin15AnchoredAtom2174 chi ∧
      ¬Fin15AnchoredAtom2210 chi ∧
      ¬Fin15AnchoredAtom2327 chi ∧
      ¬Fin15AnchoredAtom2331 chi ∧
      ¬Fin15AnchoredAtom2339 chi ∧
      ¬Fin15AnchoredAtom2375 chi ∧
      ¬Fin15AnchoredAtom2495 chi ∧
      ¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom2877 chi ∧
      ¬Fin15AnchoredAtom2881 chi ∧
      ¬Fin15AnchoredAtom2889 chi ∧
      ¬Fin15AnchoredAtom2925 chi ∧
      ¬Fin15AnchoredAtom3042 chi ∧
      ¬Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom3054 chi ∧
      ¬Fin15AnchoredAtom3090 chi ∧
      ¬Fin15AnchoredAtom3210 chi ∧
      ¬Fin15AnchoredAtom3537 chi ∧
      ¬Fin15AnchoredAtom3541 chi ∧
      ¬Fin15AnchoredAtom3549 chi ∧
      ¬Fin15AnchoredAtom3585 chi ∧
      ¬Fin15AnchoredAtom3705 chi ∧
      ¬Fin15AnchoredAtom4035 chi)) ∨
      ((¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1942 chi ∧
      ¬Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom1992 chi ∧
      ¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom2131 chi ∧
      ¬Fin15AnchoredAtom2162 chi ∧
      ¬Fin15AnchoredAtom2168 chi ∧
      ¬Fin15AnchoredAtom2176 chi ∧
      ¬Fin15AnchoredAtom2212 chi ∧
      ¬Fin15AnchoredAtom2327 chi ∧
      ¬Fin15AnchoredAtom2333 chi ∧
      ¬Fin15AnchoredAtom2341 chi ∧
      ¬Fin15AnchoredAtom2377 chi ∧
      ¬Fin15AnchoredAtom2497 chi ∧
      ¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom2877 chi ∧
      ¬Fin15AnchoredAtom2883 chi ∧
      ¬Fin15AnchoredAtom2891 chi ∧
      ¬Fin15AnchoredAtom2927 chi ∧
      ¬Fin15AnchoredAtom3042 chi ∧
      ¬Fin15AnchoredAtom3048 chi ∧
      ¬Fin15AnchoredAtom3056 chi ∧
      ¬Fin15AnchoredAtom3092 chi ∧
      ¬Fin15AnchoredAtom3212 chi ∧
      ¬Fin15AnchoredAtom3537 chi ∧
      ¬Fin15AnchoredAtom3543 chi ∧
      ¬Fin15AnchoredAtom3551 chi ∧
      ¬Fin15AnchoredAtom3587 chi ∧
      ¬Fin15AnchoredAtom3707 chi ∧
      ¬Fin15AnchoredAtom4037 chi) ∨
      (¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1942 chi ∧
      ¬Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom1993 chi ∧
      ¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom2132 chi ∧
      ¬Fin15AnchoredAtom2162 chi ∧
      ¬Fin15AnchoredAtom2169 chi ∧
      ¬Fin15AnchoredAtom2177 chi ∧
      ¬Fin15AnchoredAtom2213 chi ∧
      ¬Fin15AnchoredAtom2327 chi ∧
      ¬Fin15AnchoredAtom2334 chi ∧
      ¬Fin15AnchoredAtom2342 chi ∧
      ¬Fin15AnchoredAtom2378 chi ∧
      ¬Fin15AnchoredAtom2498 chi ∧
      ¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom2877 chi ∧
      ¬Fin15AnchoredAtom2884 chi ∧
      ¬Fin15AnchoredAtom2892 chi ∧
      ¬Fin15AnchoredAtom2928 chi ∧
      ¬Fin15AnchoredAtom3042 chi ∧
      ¬Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom3057 chi ∧
      ¬Fin15AnchoredAtom3093 chi ∧
      ¬Fin15AnchoredAtom3213 chi ∧
      ¬Fin15AnchoredAtom3537 chi ∧
      ¬Fin15AnchoredAtom3544 chi ∧
      ¬Fin15AnchoredAtom3552 chi ∧
      ¬Fin15AnchoredAtom3588 chi ∧
      ¬Fin15AnchoredAtom3708 chi ∧
      ¬Fin15AnchoredAtom4038 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1942 chi ∧
      ¬Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom1994 chi ∧
      ¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom2133 chi ∧
      ¬Fin15AnchoredAtom2162 chi ∧
      ¬Fin15AnchoredAtom2170 chi ∧
      ¬Fin15AnchoredAtom2178 chi ∧
      ¬Fin15AnchoredAtom2214 chi ∧
      ¬Fin15AnchoredAtom2327 chi ∧
      ¬Fin15AnchoredAtom2335 chi ∧
      ¬Fin15AnchoredAtom2343 chi ∧
      ¬Fin15AnchoredAtom2379 chi ∧
      ¬Fin15AnchoredAtom2499 chi ∧
      ¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom2877 chi ∧
      ¬Fin15AnchoredAtom2885 chi ∧
      ¬Fin15AnchoredAtom2893 chi ∧
      ¬Fin15AnchoredAtom2929 chi ∧
      ¬Fin15AnchoredAtom3042 chi ∧
      ¬Fin15AnchoredAtom3050 chi ∧
      ¬Fin15AnchoredAtom3058 chi ∧
      ¬Fin15AnchoredAtom3094 chi ∧
      ¬Fin15AnchoredAtom3214 chi ∧
      ¬Fin15AnchoredAtom3537 chi ∧
      ¬Fin15AnchoredAtom3545 chi ∧
      ¬Fin15AnchoredAtom3553 chi ∧
      ¬Fin15AnchoredAtom3589 chi ∧
      ¬Fin15AnchoredAtom3709 chi ∧
      ¬Fin15AnchoredAtom4039 chi) ∨
      (¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom1996 chi ∧
      ¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom2135 chi ∧
      ¬Fin15AnchoredAtom2163 chi ∧
      ¬Fin15AnchoredAtom2165 chi ∧
      ¬Fin15AnchoredAtom2180 chi ∧
      ¬Fin15AnchoredAtom2216 chi ∧
      ¬Fin15AnchoredAtom2328 chi ∧
      ¬Fin15AnchoredAtom2330 chi ∧
      ¬Fin15AnchoredAtom2345 chi ∧
      ¬Fin15AnchoredAtom2381 chi ∧
      ¬Fin15AnchoredAtom2501 chi ∧
      ¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom2878 chi ∧
      ¬Fin15AnchoredAtom2880 chi ∧
      ¬Fin15AnchoredAtom2895 chi ∧
      ¬Fin15AnchoredAtom2931 chi ∧
      ¬Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom3060 chi ∧
      ¬Fin15AnchoredAtom3096 chi ∧
      ¬Fin15AnchoredAtom3216 chi ∧
      ¬Fin15AnchoredAtom3538 chi ∧
      ¬Fin15AnchoredAtom3540 chi ∧
      ¬Fin15AnchoredAtom3555 chi ∧
      ¬Fin15AnchoredAtom3591 chi ∧
      ¬Fin15AnchoredAtom3711 chi ∧
      ¬Fin15AnchoredAtom4041 chi)) ∨
      ((¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom1997 chi ∧
      ¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2136 chi ∧
      ¬Fin15AnchoredAtom2163 chi ∧
      ¬Fin15AnchoredAtom2166 chi ∧
      ¬Fin15AnchoredAtom2181 chi ∧
      ¬Fin15AnchoredAtom2217 chi ∧
      ¬Fin15AnchoredAtom2328 chi ∧
      ¬Fin15AnchoredAtom2331 chi ∧
      ¬Fin15AnchoredAtom2346 chi ∧
      ¬Fin15AnchoredAtom2382 chi ∧
      ¬Fin15AnchoredAtom2502 chi ∧
      ¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom2878 chi ∧
      ¬Fin15AnchoredAtom2881 chi ∧
      ¬Fin15AnchoredAtom2896 chi ∧
      ¬Fin15AnchoredAtom2932 chi ∧
      ¬Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom3061 chi ∧
      ¬Fin15AnchoredAtom3097 chi ∧
      ¬Fin15AnchoredAtom3217 chi ∧
      ¬Fin15AnchoredAtom3538 chi ∧
      ¬Fin15AnchoredAtom3541 chi ∧
      ¬Fin15AnchoredAtom3556 chi ∧
      ¬Fin15AnchoredAtom3592 chi ∧
      ¬Fin15AnchoredAtom3712 chi ∧
      ¬Fin15AnchoredAtom4042 chi) ∨
      (¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom1999 chi ∧
      ¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom2138 chi ∧
      ¬Fin15AnchoredAtom2163 chi ∧
      ¬Fin15AnchoredAtom2168 chi ∧
      ¬Fin15AnchoredAtom2183 chi ∧
      ¬Fin15AnchoredAtom2219 chi ∧
      ¬Fin15AnchoredAtom2328 chi ∧
      ¬Fin15AnchoredAtom2333 chi ∧
      ¬Fin15AnchoredAtom2348 chi ∧
      ¬Fin15AnchoredAtom2384 chi ∧
      ¬Fin15AnchoredAtom2504 chi ∧
      ¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom2878 chi ∧
      ¬Fin15AnchoredAtom2883 chi ∧
      ¬Fin15AnchoredAtom2898 chi ∧
      ¬Fin15AnchoredAtom2934 chi ∧
      ¬Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom3048 chi ∧
      ¬Fin15AnchoredAtom3063 chi ∧
      ¬Fin15AnchoredAtom3099 chi ∧
      ¬Fin15AnchoredAtom3219 chi ∧
      ¬Fin15AnchoredAtom3538 chi ∧
      ¬Fin15AnchoredAtom3543 chi ∧
      ¬Fin15AnchoredAtom3558 chi ∧
      ¬Fin15AnchoredAtom3594 chi ∧
      ¬Fin15AnchoredAtom3714 chi ∧
      ¬Fin15AnchoredAtom4044 chi))) ∨
      (((¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom2000 chi ∧
      ¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom2139 chi ∧
      ¬Fin15AnchoredAtom2163 chi ∧
      ¬Fin15AnchoredAtom2169 chi ∧
      ¬Fin15AnchoredAtom2184 chi ∧
      ¬Fin15AnchoredAtom2220 chi ∧
      ¬Fin15AnchoredAtom2328 chi ∧
      ¬Fin15AnchoredAtom2334 chi ∧
      ¬Fin15AnchoredAtom2349 chi ∧
      ¬Fin15AnchoredAtom2385 chi ∧
      ¬Fin15AnchoredAtom2505 chi ∧
      ¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom2878 chi ∧
      ¬Fin15AnchoredAtom2884 chi ∧
      ¬Fin15AnchoredAtom2899 chi ∧
      ¬Fin15AnchoredAtom2935 chi ∧
      ¬Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom3064 chi ∧
      ¬Fin15AnchoredAtom3100 chi ∧
      ¬Fin15AnchoredAtom3220 chi ∧
      ¬Fin15AnchoredAtom3538 chi ∧
      ¬Fin15AnchoredAtom3544 chi ∧
      ¬Fin15AnchoredAtom3559 chi ∧
      ¬Fin15AnchoredAtom3595 chi ∧
      ¬Fin15AnchoredAtom3715 chi ∧
      ¬Fin15AnchoredAtom4045 chi) ∨
      (¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom2001 chi ∧
      ¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom2140 chi ∧
      ¬Fin15AnchoredAtom2163 chi ∧
      ¬Fin15AnchoredAtom2170 chi ∧
      ¬Fin15AnchoredAtom2185 chi ∧
      ¬Fin15AnchoredAtom2221 chi ∧
      ¬Fin15AnchoredAtom2328 chi ∧
      ¬Fin15AnchoredAtom2335 chi ∧
      ¬Fin15AnchoredAtom2350 chi ∧
      ¬Fin15AnchoredAtom2386 chi ∧
      ¬Fin15AnchoredAtom2506 chi ∧
      ¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom2878 chi ∧
      ¬Fin15AnchoredAtom2885 chi ∧
      ¬Fin15AnchoredAtom2900 chi ∧
      ¬Fin15AnchoredAtom2936 chi ∧
      ¬Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom3050 chi ∧
      ¬Fin15AnchoredAtom3065 chi ∧
      ¬Fin15AnchoredAtom3101 chi ∧
      ¬Fin15AnchoredAtom3221 chi ∧
      ¬Fin15AnchoredAtom3538 chi ∧
      ¬Fin15AnchoredAtom3545 chi ∧
      ¬Fin15AnchoredAtom3560 chi ∧
      ¬Fin15AnchoredAtom3596 chi ∧
      ¬Fin15AnchoredAtom3716 chi ∧
      ¬Fin15AnchoredAtom4046 chi)) ∨
      ((¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom2008 chi ∧
      ¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2147 chi ∧
      ¬Fin15AnchoredAtom2165 chi ∧
      ¬Fin15AnchoredAtom2166 chi ∧
      ¬Fin15AnchoredAtom2192 chi ∧
      ¬Fin15AnchoredAtom2228 chi ∧
      ¬Fin15AnchoredAtom2330 chi ∧
      ¬Fin15AnchoredAtom2331 chi ∧
      ¬Fin15AnchoredAtom2357 chi ∧
      ¬Fin15AnchoredAtom2393 chi ∧
      ¬Fin15AnchoredAtom2513 chi ∧
      ¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom2880 chi ∧
      ¬Fin15AnchoredAtom2881 chi ∧
      ¬Fin15AnchoredAtom2907 chi ∧
      ¬Fin15AnchoredAtom2943 chi ∧
      ¬Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom3072 chi ∧
      ¬Fin15AnchoredAtom3108 chi ∧
      ¬Fin15AnchoredAtom3228 chi ∧
      ¬Fin15AnchoredAtom3540 chi ∧
      ¬Fin15AnchoredAtom3541 chi ∧
      ¬Fin15AnchoredAtom3567 chi ∧
      ¬Fin15AnchoredAtom3603 chi ∧
      ¬Fin15AnchoredAtom3723 chi ∧
      ¬Fin15AnchoredAtom4053 chi) ∨
      (¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom2010 chi ∧
      ¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom2149 chi ∧
      ¬Fin15AnchoredAtom2165 chi ∧
      ¬Fin15AnchoredAtom2168 chi ∧
      ¬Fin15AnchoredAtom2194 chi ∧
      ¬Fin15AnchoredAtom2230 chi ∧
      ¬Fin15AnchoredAtom2330 chi ∧
      ¬Fin15AnchoredAtom2333 chi ∧
      ¬Fin15AnchoredAtom2359 chi ∧
      ¬Fin15AnchoredAtom2395 chi ∧
      ¬Fin15AnchoredAtom2515 chi ∧
      ¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom2864 chi ∧
      ¬Fin15AnchoredAtom2880 chi ∧
      ¬Fin15AnchoredAtom2883 chi ∧
      ¬Fin15AnchoredAtom2909 chi ∧
      ¬Fin15AnchoredAtom2945 chi ∧
      ¬Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom3048 chi ∧
      ¬Fin15AnchoredAtom3074 chi ∧
      ¬Fin15AnchoredAtom3110 chi ∧
      ¬Fin15AnchoredAtom3230 chi ∧
      ¬Fin15AnchoredAtom3540 chi ∧
      ¬Fin15AnchoredAtom3543 chi ∧
      ¬Fin15AnchoredAtom3569 chi ∧
      ¬Fin15AnchoredAtom3605 chi ∧
      ¬Fin15AnchoredAtom3725 chi ∧
      ¬Fin15AnchoredAtom4055 chi)))) ∨
      ((((¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom2011 chi ∧
      ¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom2150 chi ∧
      ¬Fin15AnchoredAtom2165 chi ∧
      ¬Fin15AnchoredAtom2169 chi ∧
      ¬Fin15AnchoredAtom2195 chi ∧
      ¬Fin15AnchoredAtom2231 chi ∧
      ¬Fin15AnchoredAtom2330 chi ∧
      ¬Fin15AnchoredAtom2334 chi ∧
      ¬Fin15AnchoredAtom2360 chi ∧
      ¬Fin15AnchoredAtom2396 chi ∧
      ¬Fin15AnchoredAtom2516 chi ∧
      ¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom2865 chi ∧
      ¬Fin15AnchoredAtom2880 chi ∧
      ¬Fin15AnchoredAtom2884 chi ∧
      ¬Fin15AnchoredAtom2910 chi ∧
      ¬Fin15AnchoredAtom2946 chi ∧
      ¬Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom3075 chi ∧
      ¬Fin15AnchoredAtom3111 chi ∧
      ¬Fin15AnchoredAtom3231 chi ∧
      ¬Fin15AnchoredAtom3540 chi ∧
      ¬Fin15AnchoredAtom3544 chi ∧
      ¬Fin15AnchoredAtom3570 chi ∧
      ¬Fin15AnchoredAtom3606 chi ∧
      ¬Fin15AnchoredAtom3726 chi ∧
      ¬Fin15AnchoredAtom4056 chi) ∨
      (¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom1976 chi ∧
      ¬Fin15AnchoredAtom2012 chi ∧
      ¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom2151 chi ∧
      ¬Fin15AnchoredAtom2165 chi ∧
      ¬Fin15AnchoredAtom2170 chi ∧
      ¬Fin15AnchoredAtom2196 chi ∧
      ¬Fin15AnchoredAtom2232 chi ∧
      ¬Fin15AnchoredAtom2330 chi ∧
      ¬Fin15AnchoredAtom2335 chi ∧
      ¬Fin15AnchoredAtom2361 chi ∧
      ¬Fin15AnchoredAtom2397 chi ∧
      ¬Fin15AnchoredAtom2517 chi ∧
      ¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom2866 chi ∧
      ¬Fin15AnchoredAtom2880 chi ∧
      ¬Fin15AnchoredAtom2885 chi ∧
      ¬Fin15AnchoredAtom2911 chi ∧
      ¬Fin15AnchoredAtom2947 chi ∧
      ¬Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom3050 chi ∧
      ¬Fin15AnchoredAtom3076 chi ∧
      ¬Fin15AnchoredAtom3112 chi ∧
      ¬Fin15AnchoredAtom3232 chi ∧
      ¬Fin15AnchoredAtom3540 chi ∧
      ¬Fin15AnchoredAtom3545 chi ∧
      ¬Fin15AnchoredAtom3571 chi ∧
      ¬Fin15AnchoredAtom3607 chi ∧
      ¬Fin15AnchoredAtom3727 chi ∧
      ¬Fin15AnchoredAtom4057 chi)) ∨
      ((¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom1978 chi ∧
      ¬Fin15AnchoredAtom2014 chi ∧
      ¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom2153 chi ∧
      ¬Fin15AnchoredAtom2166 chi ∧
      ¬Fin15AnchoredAtom2168 chi ∧
      ¬Fin15AnchoredAtom2198 chi ∧
      ¬Fin15AnchoredAtom2234 chi ∧
      ¬Fin15AnchoredAtom2331 chi ∧
      ¬Fin15AnchoredAtom2333 chi ∧
      ¬Fin15AnchoredAtom2363 chi ∧
      ¬Fin15AnchoredAtom2399 chi ∧
      ¬Fin15AnchoredAtom2519 chi ∧
      ¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom2868 chi ∧
      ¬Fin15AnchoredAtom2881 chi ∧
      ¬Fin15AnchoredAtom2883 chi ∧
      ¬Fin15AnchoredAtom2913 chi ∧
      ¬Fin15AnchoredAtom2949 chi ∧
      ¬Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom3048 chi ∧
      ¬Fin15AnchoredAtom3078 chi ∧
      ¬Fin15AnchoredAtom3114 chi ∧
      ¬Fin15AnchoredAtom3234 chi ∧
      ¬Fin15AnchoredAtom3541 chi ∧
      ¬Fin15AnchoredAtom3543 chi ∧
      ¬Fin15AnchoredAtom3573 chi ∧
      ¬Fin15AnchoredAtom3609 chi ∧
      ¬Fin15AnchoredAtom3729 chi ∧
      ¬Fin15AnchoredAtom4059 chi) ∨
      (¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom1979 chi ∧
      ¬Fin15AnchoredAtom2015 chi ∧
      ¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom2154 chi ∧
      ¬Fin15AnchoredAtom2166 chi ∧
      ¬Fin15AnchoredAtom2169 chi ∧
      ¬Fin15AnchoredAtom2199 chi ∧
      ¬Fin15AnchoredAtom2235 chi ∧
      ¬Fin15AnchoredAtom2331 chi ∧
      ¬Fin15AnchoredAtom2334 chi ∧
      ¬Fin15AnchoredAtom2364 chi ∧
      ¬Fin15AnchoredAtom2400 chi ∧
      ¬Fin15AnchoredAtom2520 chi ∧
      ¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom2869 chi ∧
      ¬Fin15AnchoredAtom2881 chi ∧
      ¬Fin15AnchoredAtom2884 chi ∧
      ¬Fin15AnchoredAtom2914 chi ∧
      ¬Fin15AnchoredAtom2950 chi ∧
      ¬Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom3079 chi ∧
      ¬Fin15AnchoredAtom3115 chi ∧
      ¬Fin15AnchoredAtom3235 chi ∧
      ¬Fin15AnchoredAtom3541 chi ∧
      ¬Fin15AnchoredAtom3544 chi ∧
      ¬Fin15AnchoredAtom3574 chi ∧
      ¬Fin15AnchoredAtom3610 chi ∧
      ¬Fin15AnchoredAtom3730 chi ∧
      ¬Fin15AnchoredAtom4060 chi))) ∨
      (((¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1935 chi ∧
      ¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom1980 chi ∧
      ¬Fin15AnchoredAtom2016 chi ∧
      ¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom2155 chi ∧
      ¬Fin15AnchoredAtom2166 chi ∧
      ¬Fin15AnchoredAtom2170 chi ∧
      ¬Fin15AnchoredAtom2200 chi ∧
      ¬Fin15AnchoredAtom2236 chi ∧
      ¬Fin15AnchoredAtom2331 chi ∧
      ¬Fin15AnchoredAtom2335 chi ∧
      ¬Fin15AnchoredAtom2365 chi ∧
      ¬Fin15AnchoredAtom2401 chi ∧
      ¬Fin15AnchoredAtom2521 chi ∧
      ¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom2870 chi ∧
      ¬Fin15AnchoredAtom2881 chi ∧
      ¬Fin15AnchoredAtom2885 chi ∧
      ¬Fin15AnchoredAtom2915 chi ∧
      ¬Fin15AnchoredAtom2951 chi ∧
      ¬Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom3050 chi ∧
      ¬Fin15AnchoredAtom3080 chi ∧
      ¬Fin15AnchoredAtom3116 chi ∧
      ¬Fin15AnchoredAtom3236 chi ∧
      ¬Fin15AnchoredAtom3541 chi ∧
      ¬Fin15AnchoredAtom3545 chi ∧
      ¬Fin15AnchoredAtom3575 chi ∧
      ¬Fin15AnchoredAtom3611 chi ∧
      ¬Fin15AnchoredAtom3731 chi ∧
      ¬Fin15AnchoredAtom4061 chi) ∨
      (¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1939 chi ∧
      ¬Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom1984 chi ∧
      ¬Fin15AnchoredAtom2020 chi ∧
      ¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom2159 chi ∧
      ¬Fin15AnchoredAtom2168 chi ∧
      ¬Fin15AnchoredAtom2169 chi ∧
      ¬Fin15AnchoredAtom2204 chi ∧
      ¬Fin15AnchoredAtom2240 chi ∧
      ¬Fin15AnchoredAtom2333 chi ∧
      ¬Fin15AnchoredAtom2334 chi ∧
      ¬Fin15AnchoredAtom2369 chi ∧
      ¬Fin15AnchoredAtom2405 chi ∧
      ¬Fin15AnchoredAtom2525 chi ∧
      ¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom2874 chi ∧
      ¬Fin15AnchoredAtom2883 chi ∧
      ¬Fin15AnchoredAtom2884 chi ∧
      ¬Fin15AnchoredAtom2919 chi ∧
      ¬Fin15AnchoredAtom2955 chi ∧
      ¬Fin15AnchoredAtom3048 chi ∧
      ¬Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom3084 chi ∧
      ¬Fin15AnchoredAtom3120 chi ∧
      ¬Fin15AnchoredAtom3240 chi ∧
      ¬Fin15AnchoredAtom3543 chi ∧
      ¬Fin15AnchoredAtom3544 chi ∧
      ¬Fin15AnchoredAtom3579 chi ∧
      ¬Fin15AnchoredAtom3615 chi ∧
      ¬Fin15AnchoredAtom3735 chi ∧
      ¬Fin15AnchoredAtom4065 chi)) ∨
      ((¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1940 chi ∧
      ¬Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom1985 chi ∧
      ¬Fin15AnchoredAtom2021 chi ∧
      ¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom2160 chi ∧
      ¬Fin15AnchoredAtom2168 chi ∧
      ¬Fin15AnchoredAtom2170 chi ∧
      ¬Fin15AnchoredAtom2205 chi ∧
      ¬Fin15AnchoredAtom2241 chi ∧
      ¬Fin15AnchoredAtom2333 chi ∧
      ¬Fin15AnchoredAtom2335 chi ∧
      ¬Fin15AnchoredAtom2370 chi ∧
      ¬Fin15AnchoredAtom2406 chi ∧
      ¬Fin15AnchoredAtom2526 chi ∧
      ¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom2875 chi ∧
      ¬Fin15AnchoredAtom2883 chi ∧
      ¬Fin15AnchoredAtom2885 chi ∧
      ¬Fin15AnchoredAtom2920 chi ∧
      ¬Fin15AnchoredAtom2956 chi ∧
      ¬Fin15AnchoredAtom3048 chi ∧
      ¬Fin15AnchoredAtom3050 chi ∧
      ¬Fin15AnchoredAtom3085 chi ∧
      ¬Fin15AnchoredAtom3121 chi ∧
      ¬Fin15AnchoredAtom3241 chi ∧
      ¬Fin15AnchoredAtom3543 chi ∧
      ¬Fin15AnchoredAtom3545 chi ∧
      ¬Fin15AnchoredAtom3580 chi ∧
      ¬Fin15AnchoredAtom3616 chi ∧
      ¬Fin15AnchoredAtom3736 chi ∧
      ¬Fin15AnchoredAtom4066 chi) ∨
      (¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom1886 chi ∧
      ¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
      ¬Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom1986 chi ∧
      ¬Fin15AnchoredAtom2022 chi ∧
      ¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom2161 chi ∧
      ¬Fin15AnchoredAtom2169 chi ∧
      ¬Fin15AnchoredAtom2170 chi ∧
      ¬Fin15AnchoredAtom2206 chi ∧
      ¬Fin15AnchoredAtom2242 chi ∧
      ¬Fin15AnchoredAtom2334 chi ∧
      ¬Fin15AnchoredAtom2335 chi ∧
      ¬Fin15AnchoredAtom2371 chi ∧
      ¬Fin15AnchoredAtom2407 chi ∧
      ¬Fin15AnchoredAtom2527 chi ∧
      ¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom2876 chi ∧
      ¬Fin15AnchoredAtom2884 chi ∧
      ¬Fin15AnchoredAtom2885 chi ∧
      ¬Fin15AnchoredAtom2921 chi ∧
      ¬Fin15AnchoredAtom2957 chi ∧
      ¬Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom3050 chi ∧
      ¬Fin15AnchoredAtom3086 chi ∧
      ¬Fin15AnchoredAtom3122 chi ∧
      ¬Fin15AnchoredAtom3242 chi ∧
      ¬Fin15AnchoredAtom3544 chi ∧
      ¬Fin15AnchoredAtom3545 chi ∧
      ¬Fin15AnchoredAtom3581 chi ∧
      ¬Fin15AnchoredAtom3617 chi ∧
      ¬Fin15AnchoredAtom3737 chi ∧
      ¬Fin15AnchoredAtom4067 chi))))) ∨
      (((((¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom2024 chi ∧
      ¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2126 chi ∧
      ¬Fin15AnchoredAtom2128 chi ∧
      ¬Fin15AnchoredAtom2135 chi ∧
      ¬Fin15AnchoredAtom2171 chi ∧
      ¬Fin15AnchoredAtom2173 chi ∧
      ¬Fin15AnchoredAtom2180 chi ∧
      ¬Fin15AnchoredAtom2244 chi ∧
      ¬Fin15AnchoredAtom2336 chi ∧
      ¬Fin15AnchoredAtom2338 chi ∧
      ¬Fin15AnchoredAtom2345 chi ∧
      ¬Fin15AnchoredAtom2409 chi ∧
      ¬Fin15AnchoredAtom2529 chi ∧
      ¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom2886 chi ∧
      ¬Fin15AnchoredAtom2888 chi ∧
      ¬Fin15AnchoredAtom2895 chi ∧
      ¬Fin15AnchoredAtom2959 chi ∧
      ¬Fin15AnchoredAtom3051 chi ∧
      ¬Fin15AnchoredAtom3053 chi ∧
      ¬Fin15AnchoredAtom3060 chi ∧
      ¬Fin15AnchoredAtom3124 chi ∧
      ¬Fin15AnchoredAtom3244 chi ∧
      ¬Fin15AnchoredAtom3546 chi ∧
      ¬Fin15AnchoredAtom3548 chi ∧
      ¬Fin15AnchoredAtom3555 chi ∧
      ¬Fin15AnchoredAtom3619 chi ∧
      ¬Fin15AnchoredAtom3739 chi ∧
      ¬Fin15AnchoredAtom4069 chi) ∨
      (¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom2025 chi ∧
      ¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2126 chi ∧
      ¬Fin15AnchoredAtom2129 chi ∧
      ¬Fin15AnchoredAtom2136 chi ∧
      ¬Fin15AnchoredAtom2171 chi ∧
      ¬Fin15AnchoredAtom2174 chi ∧
      ¬Fin15AnchoredAtom2181 chi ∧
      ¬Fin15AnchoredAtom2245 chi ∧
      ¬Fin15AnchoredAtom2336 chi ∧
      ¬Fin15AnchoredAtom2339 chi ∧
      ¬Fin15AnchoredAtom2346 chi ∧
      ¬Fin15AnchoredAtom2410 chi ∧
      ¬Fin15AnchoredAtom2530 chi ∧
      ¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom2886 chi ∧
      ¬Fin15AnchoredAtom2889 chi ∧
      ¬Fin15AnchoredAtom2896 chi ∧
      ¬Fin15AnchoredAtom2960 chi ∧
      ¬Fin15AnchoredAtom3051 chi ∧
      ¬Fin15AnchoredAtom3054 chi ∧
      ¬Fin15AnchoredAtom3061 chi ∧
      ¬Fin15AnchoredAtom3125 chi ∧
      ¬Fin15AnchoredAtom3245 chi ∧
      ¬Fin15AnchoredAtom3546 chi ∧
      ¬Fin15AnchoredAtom3549 chi ∧
      ¬Fin15AnchoredAtom3556 chi ∧
      ¬Fin15AnchoredAtom3620 chi ∧
      ¬Fin15AnchoredAtom3740 chi ∧
      ¬Fin15AnchoredAtom4070 chi)) ∨
      ((¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom2027 chi ∧
      ¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2126 chi ∧
      ¬Fin15AnchoredAtom2131 chi ∧
      ¬Fin15AnchoredAtom2138 chi ∧
      ¬Fin15AnchoredAtom2171 chi ∧
      ¬Fin15AnchoredAtom2176 chi ∧
      ¬Fin15AnchoredAtom2183 chi ∧
      ¬Fin15AnchoredAtom2247 chi ∧
      ¬Fin15AnchoredAtom2336 chi ∧
      ¬Fin15AnchoredAtom2341 chi ∧
      ¬Fin15AnchoredAtom2348 chi ∧
      ¬Fin15AnchoredAtom2412 chi ∧
      ¬Fin15AnchoredAtom2532 chi ∧
      ¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom2886 chi ∧
      ¬Fin15AnchoredAtom2891 chi ∧
      ¬Fin15AnchoredAtom2898 chi ∧
      ¬Fin15AnchoredAtom2962 chi ∧
      ¬Fin15AnchoredAtom3051 chi ∧
      ¬Fin15AnchoredAtom3056 chi ∧
      ¬Fin15AnchoredAtom3063 chi ∧
      ¬Fin15AnchoredAtom3127 chi ∧
      ¬Fin15AnchoredAtom3247 chi ∧
      ¬Fin15AnchoredAtom3546 chi ∧
      ¬Fin15AnchoredAtom3551 chi ∧
      ¬Fin15AnchoredAtom3558 chi ∧
      ¬Fin15AnchoredAtom3622 chi ∧
      ¬Fin15AnchoredAtom3742 chi ∧
      ¬Fin15AnchoredAtom4072 chi) ∨
      (¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom2028 chi ∧
      ¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2126 chi ∧
      ¬Fin15AnchoredAtom2132 chi ∧
      ¬Fin15AnchoredAtom2139 chi ∧
      ¬Fin15AnchoredAtom2171 chi ∧
      ¬Fin15AnchoredAtom2177 chi ∧
      ¬Fin15AnchoredAtom2184 chi ∧
      ¬Fin15AnchoredAtom2248 chi ∧
      ¬Fin15AnchoredAtom2336 chi ∧
      ¬Fin15AnchoredAtom2342 chi ∧
      ¬Fin15AnchoredAtom2349 chi ∧
      ¬Fin15AnchoredAtom2413 chi ∧
      ¬Fin15AnchoredAtom2533 chi ∧
      ¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom2886 chi ∧
      ¬Fin15AnchoredAtom2892 chi ∧
      ¬Fin15AnchoredAtom2899 chi ∧
      ¬Fin15AnchoredAtom2963 chi ∧
      ¬Fin15AnchoredAtom3051 chi ∧
      ¬Fin15AnchoredAtom3057 chi ∧
      ¬Fin15AnchoredAtom3064 chi ∧
      ¬Fin15AnchoredAtom3128 chi ∧
      ¬Fin15AnchoredAtom3248 chi ∧
      ¬Fin15AnchoredAtom3546 chi ∧
      ¬Fin15AnchoredAtom3552 chi ∧
      ¬Fin15AnchoredAtom3559 chi ∧
      ¬Fin15AnchoredAtom3623 chi ∧
      ¬Fin15AnchoredAtom3743 chi ∧
      ¬Fin15AnchoredAtom4073 chi))) ∨
      (((¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom2029 chi ∧
      ¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2126 chi ∧
      ¬Fin15AnchoredAtom2133 chi ∧
      ¬Fin15AnchoredAtom2140 chi ∧
      ¬Fin15AnchoredAtom2171 chi ∧
      ¬Fin15AnchoredAtom2178 chi ∧
      ¬Fin15AnchoredAtom2185 chi ∧
      ¬Fin15AnchoredAtom2249 chi ∧
      ¬Fin15AnchoredAtom2336 chi ∧
      ¬Fin15AnchoredAtom2343 chi ∧
      ¬Fin15AnchoredAtom2350 chi ∧
      ¬Fin15AnchoredAtom2414 chi ∧
      ¬Fin15AnchoredAtom2534 chi ∧
      ¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom2886 chi ∧
      ¬Fin15AnchoredAtom2893 chi ∧
      ¬Fin15AnchoredAtom2900 chi ∧
      ¬Fin15AnchoredAtom2964 chi ∧
      ¬Fin15AnchoredAtom3051 chi ∧
      ¬Fin15AnchoredAtom3058 chi ∧
      ¬Fin15AnchoredAtom3065 chi ∧
      ¬Fin15AnchoredAtom3129 chi ∧
      ¬Fin15AnchoredAtom3249 chi ∧
      ¬Fin15AnchoredAtom3546 chi ∧
      ¬Fin15AnchoredAtom3553 chi ∧
      ¬Fin15AnchoredAtom3560 chi ∧
      ¬Fin15AnchoredAtom3624 chi ∧
      ¬Fin15AnchoredAtom3744 chi ∧
      ¬Fin15AnchoredAtom4074 chi) ∨
      (¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom2036 chi ∧
      ¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2128 chi ∧
      ¬Fin15AnchoredAtom2129 chi ∧
      ¬Fin15AnchoredAtom2147 chi ∧
      ¬Fin15AnchoredAtom2173 chi ∧
      ¬Fin15AnchoredAtom2174 chi ∧
      ¬Fin15AnchoredAtom2192 chi ∧
      ¬Fin15AnchoredAtom2256 chi ∧
      ¬Fin15AnchoredAtom2338 chi ∧
      ¬Fin15AnchoredAtom2339 chi ∧
      ¬Fin15AnchoredAtom2357 chi ∧
      ¬Fin15AnchoredAtom2421 chi ∧
      ¬Fin15AnchoredAtom2541 chi ∧
      ¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom2888 chi ∧
      ¬Fin15AnchoredAtom2889 chi ∧
      ¬Fin15AnchoredAtom2907 chi ∧
      ¬Fin15AnchoredAtom2971 chi ∧
      ¬Fin15AnchoredAtom3053 chi ∧
      ¬Fin15AnchoredAtom3054 chi ∧
      ¬Fin15AnchoredAtom3072 chi ∧
      ¬Fin15AnchoredAtom3136 chi ∧
      ¬Fin15AnchoredAtom3256 chi ∧
      ¬Fin15AnchoredAtom3548 chi ∧
      ¬Fin15AnchoredAtom3549 chi ∧
      ¬Fin15AnchoredAtom3567 chi ∧
      ¬Fin15AnchoredAtom3631 chi ∧
      ¬Fin15AnchoredAtom3751 chi ∧
      ¬Fin15AnchoredAtom4081 chi)) ∨
      ((¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom2038 chi ∧
      ¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2128 chi ∧
      ¬Fin15AnchoredAtom2131 chi ∧
      ¬Fin15AnchoredAtom2149 chi ∧
      ¬Fin15AnchoredAtom2173 chi ∧
      ¬Fin15AnchoredAtom2176 chi ∧
      ¬Fin15AnchoredAtom2194 chi ∧
      ¬Fin15AnchoredAtom2258 chi ∧
      ¬Fin15AnchoredAtom2338 chi ∧
      ¬Fin15AnchoredAtom2341 chi ∧
      ¬Fin15AnchoredAtom2359 chi ∧
      ¬Fin15AnchoredAtom2423 chi ∧
      ¬Fin15AnchoredAtom2543 chi ∧
      ¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom2864 chi ∧
      ¬Fin15AnchoredAtom2888 chi ∧
      ¬Fin15AnchoredAtom2891 chi ∧
      ¬Fin15AnchoredAtom2909 chi ∧
      ¬Fin15AnchoredAtom2973 chi ∧
      ¬Fin15AnchoredAtom3053 chi ∧
      ¬Fin15AnchoredAtom3056 chi ∧
      ¬Fin15AnchoredAtom3074 chi ∧
      ¬Fin15AnchoredAtom3138 chi ∧
      ¬Fin15AnchoredAtom3258 chi ∧
      ¬Fin15AnchoredAtom3548 chi ∧
      ¬Fin15AnchoredAtom3551 chi ∧
      ¬Fin15AnchoredAtom3569 chi ∧
      ¬Fin15AnchoredAtom3633 chi ∧
      ¬Fin15AnchoredAtom3753 chi ∧
      ¬Fin15AnchoredAtom4083 chi) ∨
      (¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom2039 chi ∧
      ¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2128 chi ∧
      ¬Fin15AnchoredAtom2132 chi ∧
      ¬Fin15AnchoredAtom2150 chi ∧
      ¬Fin15AnchoredAtom2173 chi ∧
      ¬Fin15AnchoredAtom2177 chi ∧
      ¬Fin15AnchoredAtom2195 chi ∧
      ¬Fin15AnchoredAtom2259 chi ∧
      ¬Fin15AnchoredAtom2338 chi ∧
      ¬Fin15AnchoredAtom2342 chi ∧
      ¬Fin15AnchoredAtom2360 chi ∧
      ¬Fin15AnchoredAtom2424 chi ∧
      ¬Fin15AnchoredAtom2544 chi ∧
      ¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom2865 chi ∧
      ¬Fin15AnchoredAtom2888 chi ∧
      ¬Fin15AnchoredAtom2892 chi ∧
      ¬Fin15AnchoredAtom2910 chi ∧
      ¬Fin15AnchoredAtom2974 chi ∧
      ¬Fin15AnchoredAtom3053 chi ∧
      ¬Fin15AnchoredAtom3057 chi ∧
      ¬Fin15AnchoredAtom3075 chi ∧
      ¬Fin15AnchoredAtom3139 chi ∧
      ¬Fin15AnchoredAtom3259 chi ∧
      ¬Fin15AnchoredAtom3548 chi ∧
      ¬Fin15AnchoredAtom3552 chi ∧
      ¬Fin15AnchoredAtom3570 chi ∧
      ¬Fin15AnchoredAtom3634 chi ∧
      ¬Fin15AnchoredAtom3754 chi ∧
      ¬Fin15AnchoredAtom4084 chi)))) ∨
      ((((¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom1976 chi ∧
      ¬Fin15AnchoredAtom2040 chi ∧
      ¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2128 chi ∧
      ¬Fin15AnchoredAtom2133 chi ∧
      ¬Fin15AnchoredAtom2151 chi ∧
      ¬Fin15AnchoredAtom2173 chi ∧
      ¬Fin15AnchoredAtom2178 chi ∧
      ¬Fin15AnchoredAtom2196 chi ∧
      ¬Fin15AnchoredAtom2260 chi ∧
      ¬Fin15AnchoredAtom2338 chi ∧
      ¬Fin15AnchoredAtom2343 chi ∧
      ¬Fin15AnchoredAtom2361 chi ∧
      ¬Fin15AnchoredAtom2425 chi ∧
      ¬Fin15AnchoredAtom2545 chi ∧
      ¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom2866 chi ∧
      ¬Fin15AnchoredAtom2888 chi ∧
      ¬Fin15AnchoredAtom2893 chi ∧
      ¬Fin15AnchoredAtom2911 chi ∧
      ¬Fin15AnchoredAtom2975 chi ∧
      ¬Fin15AnchoredAtom3053 chi ∧
      ¬Fin15AnchoredAtom3058 chi ∧
      ¬Fin15AnchoredAtom3076 chi ∧
      ¬Fin15AnchoredAtom3140 chi ∧
      ¬Fin15AnchoredAtom3260 chi ∧
      ¬Fin15AnchoredAtom3548 chi ∧
      ¬Fin15AnchoredAtom3553 chi ∧
      ¬Fin15AnchoredAtom3571 chi ∧
      ¬Fin15AnchoredAtom3635 chi ∧
      ¬Fin15AnchoredAtom3755 chi ∧
      ¬Fin15AnchoredAtom4085 chi) ∨
      (¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom1978 chi ∧
      ¬Fin15AnchoredAtom2042 chi ∧
      ¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2129 chi ∧
      ¬Fin15AnchoredAtom2131 chi ∧
      ¬Fin15AnchoredAtom2153 chi ∧
      ¬Fin15AnchoredAtom2174 chi ∧
      ¬Fin15AnchoredAtom2176 chi ∧
      ¬Fin15AnchoredAtom2198 chi ∧
      ¬Fin15AnchoredAtom2262 chi ∧
      ¬Fin15AnchoredAtom2339 chi ∧
      ¬Fin15AnchoredAtom2341 chi ∧
      ¬Fin15AnchoredAtom2363 chi ∧
      ¬Fin15AnchoredAtom2427 chi ∧
      ¬Fin15AnchoredAtom2547 chi ∧
      ¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom2868 chi ∧
      ¬Fin15AnchoredAtom2889 chi ∧
      ¬Fin15AnchoredAtom2891 chi ∧
      ¬Fin15AnchoredAtom2913 chi ∧
      ¬Fin15AnchoredAtom2977 chi ∧
      ¬Fin15AnchoredAtom3054 chi ∧
      ¬Fin15AnchoredAtom3056 chi ∧
      ¬Fin15AnchoredAtom3078 chi ∧
      ¬Fin15AnchoredAtom3142 chi ∧
      ¬Fin15AnchoredAtom3262 chi ∧
      ¬Fin15AnchoredAtom3549 chi ∧
      ¬Fin15AnchoredAtom3551 chi ∧
      ¬Fin15AnchoredAtom3573 chi ∧
      ¬Fin15AnchoredAtom3637 chi ∧
      ¬Fin15AnchoredAtom3757 chi ∧
      ¬Fin15AnchoredAtom4087 chi)) ∨
      ((¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom1979 chi ∧
      ¬Fin15AnchoredAtom2043 chi ∧
      ¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2129 chi ∧
      ¬Fin15AnchoredAtom2132 chi ∧
      ¬Fin15AnchoredAtom2154 chi ∧
      ¬Fin15AnchoredAtom2174 chi ∧
      ¬Fin15AnchoredAtom2177 chi ∧
      ¬Fin15AnchoredAtom2199 chi ∧
      ¬Fin15AnchoredAtom2263 chi ∧
      ¬Fin15AnchoredAtom2339 chi ∧
      ¬Fin15AnchoredAtom2342 chi ∧
      ¬Fin15AnchoredAtom2364 chi ∧
      ¬Fin15AnchoredAtom2428 chi ∧
      ¬Fin15AnchoredAtom2548 chi ∧
      ¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom2869 chi ∧
      ¬Fin15AnchoredAtom2889 chi ∧
      ¬Fin15AnchoredAtom2892 chi ∧
      ¬Fin15AnchoredAtom2914 chi ∧
      ¬Fin15AnchoredAtom2978 chi ∧
      ¬Fin15AnchoredAtom3054 chi ∧
      ¬Fin15AnchoredAtom3057 chi ∧
      ¬Fin15AnchoredAtom3079 chi ∧
      ¬Fin15AnchoredAtom3143 chi ∧
      ¬Fin15AnchoredAtom3263 chi ∧
      ¬Fin15AnchoredAtom3549 chi ∧
      ¬Fin15AnchoredAtom3552 chi ∧
      ¬Fin15AnchoredAtom3574 chi ∧
      ¬Fin15AnchoredAtom3638 chi ∧
      ¬Fin15AnchoredAtom3758 chi ∧
      ¬Fin15AnchoredAtom4088 chi) ∨
      (¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1935 chi ∧
      ¬Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom1980 chi ∧
      ¬Fin15AnchoredAtom2044 chi ∧
      ¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2129 chi ∧
      ¬Fin15AnchoredAtom2133 chi ∧
      ¬Fin15AnchoredAtom2155 chi ∧
      ¬Fin15AnchoredAtom2174 chi ∧
      ¬Fin15AnchoredAtom2178 chi ∧
      ¬Fin15AnchoredAtom2200 chi ∧
      ¬Fin15AnchoredAtom2264 chi ∧
      ¬Fin15AnchoredAtom2339 chi ∧
      ¬Fin15AnchoredAtom2343 chi ∧
      ¬Fin15AnchoredAtom2365 chi ∧
      ¬Fin15AnchoredAtom2429 chi ∧
      ¬Fin15AnchoredAtom2549 chi ∧
      ¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom2870 chi ∧
      ¬Fin15AnchoredAtom2889 chi ∧
      ¬Fin15AnchoredAtom2893 chi ∧
      ¬Fin15AnchoredAtom2915 chi ∧
      ¬Fin15AnchoredAtom2979 chi ∧
      ¬Fin15AnchoredAtom3054 chi ∧
      ¬Fin15AnchoredAtom3058 chi ∧
      ¬Fin15AnchoredAtom3080 chi ∧
      ¬Fin15AnchoredAtom3144 chi ∧
      ¬Fin15AnchoredAtom3264 chi ∧
      ¬Fin15AnchoredAtom3549 chi ∧
      ¬Fin15AnchoredAtom3553 chi ∧
      ¬Fin15AnchoredAtom3575 chi ∧
      ¬Fin15AnchoredAtom3639 chi ∧
      ¬Fin15AnchoredAtom3759 chi ∧
      ¬Fin15AnchoredAtom4089 chi))) ∨
      (((¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1939 chi ∧
      ¬Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom1984 chi ∧
      ¬Fin15AnchoredAtom2048 chi ∧
      ¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2131 chi ∧
      ¬Fin15AnchoredAtom2132 chi ∧
      ¬Fin15AnchoredAtom2159 chi ∧
      ¬Fin15AnchoredAtom2176 chi ∧
      ¬Fin15AnchoredAtom2177 chi ∧
      ¬Fin15AnchoredAtom2204 chi ∧
      ¬Fin15AnchoredAtom2268 chi ∧
      ¬Fin15AnchoredAtom2341 chi ∧
      ¬Fin15AnchoredAtom2342 chi ∧
      ¬Fin15AnchoredAtom2369 chi ∧
      ¬Fin15AnchoredAtom2433 chi ∧
      ¬Fin15AnchoredAtom2553 chi ∧
      ¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom2874 chi ∧
      ¬Fin15AnchoredAtom2891 chi ∧
      ¬Fin15AnchoredAtom2892 chi ∧
      ¬Fin15AnchoredAtom2919 chi ∧
      ¬Fin15AnchoredAtom2983 chi ∧
      ¬Fin15AnchoredAtom3056 chi ∧
      ¬Fin15AnchoredAtom3057 chi ∧
      ¬Fin15AnchoredAtom3084 chi ∧
      ¬Fin15AnchoredAtom3148 chi ∧
      ¬Fin15AnchoredAtom3268 chi ∧
      ¬Fin15AnchoredAtom3551 chi ∧
      ¬Fin15AnchoredAtom3552 chi ∧
      ¬Fin15AnchoredAtom3579 chi ∧
      ¬Fin15AnchoredAtom3643 chi ∧
      ¬Fin15AnchoredAtom3763 chi ∧
      ¬Fin15AnchoredAtom4093 chi) ∨
      (¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1940 chi ∧
      ¬Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom1985 chi ∧
      ¬Fin15AnchoredAtom2049 chi ∧
      ¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2131 chi ∧
      ¬Fin15AnchoredAtom2133 chi ∧
      ¬Fin15AnchoredAtom2160 chi ∧
      ¬Fin15AnchoredAtom2176 chi ∧
      ¬Fin15AnchoredAtom2178 chi ∧
      ¬Fin15AnchoredAtom2205 chi ∧
      ¬Fin15AnchoredAtom2269 chi ∧
      ¬Fin15AnchoredAtom2341 chi ∧
      ¬Fin15AnchoredAtom2343 chi ∧
      ¬Fin15AnchoredAtom2370 chi ∧
      ¬Fin15AnchoredAtom2434 chi ∧
      ¬Fin15AnchoredAtom2554 chi ∧
      ¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom2875 chi ∧
      ¬Fin15AnchoredAtom2891 chi ∧
      ¬Fin15AnchoredAtom2893 chi ∧
      ¬Fin15AnchoredAtom2920 chi ∧
      ¬Fin15AnchoredAtom2984 chi ∧
      ¬Fin15AnchoredAtom3056 chi ∧
      ¬Fin15AnchoredAtom3058 chi ∧
      ¬Fin15AnchoredAtom3085 chi ∧
      ¬Fin15AnchoredAtom3149 chi ∧
      ¬Fin15AnchoredAtom3269 chi ∧
      ¬Fin15AnchoredAtom3551 chi ∧
      ¬Fin15AnchoredAtom3553 chi ∧
      ¬Fin15AnchoredAtom3580 chi ∧
      ¬Fin15AnchoredAtom3644 chi ∧
      ¬Fin15AnchoredAtom3764 chi ∧
      ¬Fin15AnchoredAtom4094 chi)) ∨
      ((¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom1886 chi ∧
      ¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
      ¬Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom1986 chi ∧
      ¬Fin15AnchoredAtom2050 chi ∧
      ¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2132 chi ∧
      ¬Fin15AnchoredAtom2133 chi ∧
      ¬Fin15AnchoredAtom2161 chi ∧
      ¬Fin15AnchoredAtom2177 chi ∧
      ¬Fin15AnchoredAtom2178 chi ∧
      ¬Fin15AnchoredAtom2206 chi ∧
      ¬Fin15AnchoredAtom2270 chi ∧
      ¬Fin15AnchoredAtom2342 chi ∧
      ¬Fin15AnchoredAtom2343 chi ∧
      ¬Fin15AnchoredAtom2371 chi ∧
      ¬Fin15AnchoredAtom2435 chi ∧
      ¬Fin15AnchoredAtom2555 chi ∧
      ¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom2876 chi ∧
      ¬Fin15AnchoredAtom2892 chi ∧
      ¬Fin15AnchoredAtom2893 chi ∧
      ¬Fin15AnchoredAtom2921 chi ∧
      ¬Fin15AnchoredAtom2985 chi ∧
      ¬Fin15AnchoredAtom3057 chi ∧
      ¬Fin15AnchoredAtom3058 chi ∧
      ¬Fin15AnchoredAtom3086 chi ∧
      ¬Fin15AnchoredAtom3150 chi ∧
      ¬Fin15AnchoredAtom3270 chi ∧
      ¬Fin15AnchoredAtom3552 chi ∧
      ¬Fin15AnchoredAtom3553 chi ∧
      ¬Fin15AnchoredAtom3581 chi ∧
      ¬Fin15AnchoredAtom3645 chi ∧
      ¬Fin15AnchoredAtom3765 chi ∧
      ¬Fin15AnchoredAtom4095 chi) ∨
      (¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom2057 chi ∧
      ¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2135 chi ∧
      ¬Fin15AnchoredAtom2136 chi ∧
      ¬Fin15AnchoredAtom2147 chi ∧
      ¬Fin15AnchoredAtom2180 chi ∧
      ¬Fin15AnchoredAtom2181 chi ∧
      ¬Fin15AnchoredAtom2192 chi ∧
      ¬Fin15AnchoredAtom2277 chi ∧
      ¬Fin15AnchoredAtom2345 chi ∧
      ¬Fin15AnchoredAtom2346 chi ∧
      ¬Fin15AnchoredAtom2357 chi ∧
      ¬Fin15AnchoredAtom2442 chi ∧
      ¬Fin15AnchoredAtom2562 chi ∧
      ¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom2895 chi ∧
      ¬Fin15AnchoredAtom2896 chi ∧
      ¬Fin15AnchoredAtom2907 chi ∧
      ¬Fin15AnchoredAtom2992 chi ∧
      ¬Fin15AnchoredAtom3060 chi ∧
      ¬Fin15AnchoredAtom3061 chi ∧
      ¬Fin15AnchoredAtom3072 chi ∧
      ¬Fin15AnchoredAtom3157 chi ∧
      ¬Fin15AnchoredAtom3277 chi ∧
      ¬Fin15AnchoredAtom3555 chi ∧
      ¬Fin15AnchoredAtom3556 chi ∧
      ¬Fin15AnchoredAtom3567 chi ∧
      ¬Fin15AnchoredAtom3652 chi ∧
      ¬Fin15AnchoredAtom3772 chi ∧
      ¬Fin15AnchoredAtom4102 chi)))))))))) := by
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
                exact fin15Anchored_clause30289 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30290 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30291 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30292 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30293 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30294 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30295 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30296 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30297 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30298 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30299 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30300 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30301 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30302 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30303 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30304 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30305 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30306 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30307 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30308 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30309 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30310 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30311 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30312 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30313 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30314 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30315 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30316 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30317 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30318 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30319 chi hnoStrong hbad
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
                  exact fin15Anchored_clause30320 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30321 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30322 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30323 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30324 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30325 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30326 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30327 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30328 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30329 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30330 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30331 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30332 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30333 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30334 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30335 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30336 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30337 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30338 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30339 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30340 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30341 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30342 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30343 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30344 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30345 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30346 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30347 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30348 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30349 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30350 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30351 chi hnoStrong hbad
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
                exact fin15Anchored_clause30352 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30353 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30354 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30355 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30356 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30357 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30358 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30359 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30360 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30361 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30362 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30363 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30364 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30365 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30366 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30367 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30368 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30369 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30370 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30371 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30372 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30373 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30374 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30375 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30376 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30377 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30378 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30379 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30380 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30381 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30382 chi hnoStrong hbad
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
                  exact fin15Anchored_clause30383 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30384 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30385 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30386 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30387 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30388 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30389 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30390 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30391 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30392 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30393 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30394 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30395 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30396 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30397 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30398 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30399 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30400 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30401 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30402 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30403 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30404 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30405 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30406 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30407 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30408 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30409 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30410 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30411 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30412 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30413 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30414 chi hnoStrong hbad
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
                exact fin15Anchored_clause30415 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30416 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30417 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30418 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30419 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30420 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30421 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30422 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30423 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30424 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30425 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30426 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30427 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30428 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30429 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30430 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30431 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30432 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30433 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30434 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30435 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30436 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30437 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30438 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30439 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30440 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30441 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30442 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30443 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30444 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30445 chi hnoStrong hbad
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
                  exact fin15Anchored_clause30446 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30447 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30448 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30449 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30450 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30451 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30452 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30453 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30454 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30455 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30456 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30457 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30458 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30459 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30460 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30461 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30462 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30463 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30464 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30465 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30466 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30467 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30468 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30469 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30470 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30471 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30472 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30473 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30474 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30475 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30476 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30477 chi hnoStrong hbad
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
                exact fin15Anchored_clause30478 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30479 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30480 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30481 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30482 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30483 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30484 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30485 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30486 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30487 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30488 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30489 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30490 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30491 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30492 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30493 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30494 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30495 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30496 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30497 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30498 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30499 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30500 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30501 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30502 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30503 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30504 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30505 chi hno hbad
                ·
                  exact fin15Anchored_clause30506 chi hno hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30507 chi hno hbad
                ·
                  exact fin15Anchored_clause30508 chi hno hbad
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
                  exact fin15Anchored_clause30509 chi hno hbad
                ·
                  exact fin15Anchored_clause30510 chi hno hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30511 chi hno hbad
                ·
                  exact fin15Anchored_clause30512 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30513 chi hno hbad
                ·
                  exact fin15Anchored_clause30514 chi hno hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30515 chi hno hbad
                ·
                  exact fin15Anchored_clause30516 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30517 chi hno hbad
                ·
                  exact fin15Anchored_clause30518 chi hno hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30519 chi hno hbad
                ·
                  exact fin15Anchored_clause30520 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30521 chi hno hbad
                ·
                  exact fin15Anchored_clause30522 chi hno hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30523 chi hno hbad
                ·
                  exact fin15Anchored_clause30524 chi hno hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30525 chi hno hbad
                ·
                  exact fin15Anchored_clause30526 chi hno hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30527 chi hno hbad
                ·
                  exact fin15Anchored_clause30528 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30529 chi hno hbad
                ·
                  exact fin15Anchored_clause30530 chi hno hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30531 chi hno hbad
                ·
                  exact fin15Anchored_clause30532 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30533 chi hno hbad
                ·
                  exact fin15Anchored_clause30534 chi hno hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30535 chi hno hbad
                ·
                  exact fin15Anchored_clause30536 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30537 chi hno hbad
                ·
                  exact fin15Anchored_clause30538 chi hno hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30539 chi hno hbad
                ·
                  exact fin15Anchored_clause30540 chi hno hbad

end ErdosSzekeres

end
