module

public import ErdosSzekeres.Fin15AnchoredClauseChunk226
public import ErdosSzekeres.Fin15AnchoredClauseChunk227
public import ErdosSzekeres.Fin15AnchoredClauseChunk228

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 115. -/

theorem fin15Anchored_rejectSemanticSegment115
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom2410 chi ∧
      Fin15AnchoredAtom2413 chi ∧
      Fin15AnchoredAtom2428 chi ∧
      Fin15AnchoredAtom2449 chi ∧
      Fin15AnchoredAtom2709 chi ∧
      Fin15AnchoredAtom4249 chi) ∨
      ((Fin15AnchoredAtom2410 chi ∧
      Fin15AnchoredAtom2414 chi ∧
      Fin15AnchoredAtom2429 chi ∧
      Fin15AnchoredAtom2450 chi ∧
      Fin15AnchoredAtom2710 chi ∧
      Fin15AnchoredAtom4250 chi) ∨
      (Fin15AnchoredAtom2412 chi ∧
      Fin15AnchoredAtom2413 chi ∧
      Fin15AnchoredAtom2433 chi ∧
      Fin15AnchoredAtom2454 chi ∧
      Fin15AnchoredAtom2714 chi ∧
      Fin15AnchoredAtom4254 chi))) ∨
      (((Fin15AnchoredAtom2412 chi ∧
      Fin15AnchoredAtom2414 chi ∧
      Fin15AnchoredAtom2434 chi ∧
      Fin15AnchoredAtom2455 chi ∧
      Fin15AnchoredAtom2715 chi ∧
      Fin15AnchoredAtom4255 chi) ∨
      (Fin15AnchoredAtom2413 chi ∧
      Fin15AnchoredAtom2414 chi ∧
      Fin15AnchoredAtom2435 chi ∧
      Fin15AnchoredAtom2456 chi ∧
      Fin15AnchoredAtom2716 chi ∧
      Fin15AnchoredAtom4256 chi)) ∨
      ((Fin15AnchoredAtom2415 chi ∧
      Fin15AnchoredAtom2416 chi ∧
      Fin15AnchoredAtom2421 chi ∧
      Fin15AnchoredAtom2457 chi ∧
      Fin15AnchoredAtom2717 chi ∧
      Fin15AnchoredAtom4257 chi) ∨
      (Fin15AnchoredAtom2415 chi ∧
      Fin15AnchoredAtom2418 chi ∧
      Fin15AnchoredAtom2423 chi ∧
      Fin15AnchoredAtom2459 chi ∧
      Fin15AnchoredAtom2719 chi ∧
      Fin15AnchoredAtom4259 chi)))) ∨
      ((((Fin15AnchoredAtom2415 chi ∧
      Fin15AnchoredAtom2419 chi ∧
      Fin15AnchoredAtom2424 chi ∧
      Fin15AnchoredAtom2460 chi ∧
      Fin15AnchoredAtom2720 chi ∧
      Fin15AnchoredAtom4260 chi) ∨
      (Fin15AnchoredAtom2415 chi ∧
      Fin15AnchoredAtom2420 chi ∧
      Fin15AnchoredAtom2425 chi ∧
      Fin15AnchoredAtom2461 chi ∧
      Fin15AnchoredAtom2721 chi ∧
      Fin15AnchoredAtom4261 chi)) ∨
      ((Fin15AnchoredAtom2416 chi ∧
      Fin15AnchoredAtom2418 chi ∧
      Fin15AnchoredAtom2427 chi ∧
      Fin15AnchoredAtom2463 chi ∧
      Fin15AnchoredAtom2723 chi ∧
      Fin15AnchoredAtom4263 chi) ∨
      (Fin15AnchoredAtom2416 chi ∧
      Fin15AnchoredAtom2420 chi ∧
      Fin15AnchoredAtom2429 chi ∧
      Fin15AnchoredAtom2465 chi ∧
      Fin15AnchoredAtom2725 chi ∧
      Fin15AnchoredAtom4265 chi))) ∨
      (((Fin15AnchoredAtom2418 chi ∧
      Fin15AnchoredAtom2419 chi ∧
      Fin15AnchoredAtom2433 chi ∧
      Fin15AnchoredAtom2469 chi ∧
      Fin15AnchoredAtom2729 chi ∧
      Fin15AnchoredAtom4269 chi) ∨
      (Fin15AnchoredAtom2418 chi ∧
      Fin15AnchoredAtom2420 chi ∧
      Fin15AnchoredAtom2434 chi ∧
      Fin15AnchoredAtom2470 chi ∧
      Fin15AnchoredAtom2730 chi ∧
      Fin15AnchoredAtom4270 chi)) ∨
      ((Fin15AnchoredAtom2419 chi ∧
      Fin15AnchoredAtom2420 chi ∧
      Fin15AnchoredAtom2435 chi ∧
      Fin15AnchoredAtom2471 chi ∧
      Fin15AnchoredAtom2731 chi ∧
      Fin15AnchoredAtom4271 chi) ∨
      (Fin15AnchoredAtom2421 chi ∧
      Fin15AnchoredAtom2423 chi ∧
      Fin15AnchoredAtom2427 chi ∧
      Fin15AnchoredAtom2473 chi ∧
      Fin15AnchoredAtom2733 chi ∧
      Fin15AnchoredAtom4273 chi))))) ∨
      (((((Fin15AnchoredAtom2421 chi ∧
      Fin15AnchoredAtom2424 chi ∧
      Fin15AnchoredAtom2428 chi ∧
      Fin15AnchoredAtom2474 chi ∧
      Fin15AnchoredAtom2734 chi ∧
      Fin15AnchoredAtom4274 chi) ∨
      (Fin15AnchoredAtom2421 chi ∧
      Fin15AnchoredAtom2425 chi ∧
      Fin15AnchoredAtom2429 chi ∧
      Fin15AnchoredAtom2475 chi ∧
      Fin15AnchoredAtom2735 chi ∧
      Fin15AnchoredAtom4275 chi)) ∨
      ((Fin15AnchoredAtom2423 chi ∧
      Fin15AnchoredAtom2424 chi ∧
      Fin15AnchoredAtom2433 chi ∧
      Fin15AnchoredAtom2479 chi ∧
      Fin15AnchoredAtom2739 chi ∧
      Fin15AnchoredAtom4279 chi) ∨
      (Fin15AnchoredAtom2423 chi ∧
      Fin15AnchoredAtom2425 chi ∧
      Fin15AnchoredAtom2434 chi ∧
      Fin15AnchoredAtom2480 chi ∧
      Fin15AnchoredAtom2740 chi ∧
      Fin15AnchoredAtom4280 chi))) ∨
      (((Fin15AnchoredAtom2424 chi ∧
      Fin15AnchoredAtom2425 chi ∧
      Fin15AnchoredAtom2435 chi ∧
      Fin15AnchoredAtom2481 chi ∧
      Fin15AnchoredAtom2741 chi ∧
      Fin15AnchoredAtom4281 chi) ∨
      (Fin15AnchoredAtom2427 chi ∧
      Fin15AnchoredAtom2428 chi ∧
      Fin15AnchoredAtom2433 chi ∧
      Fin15AnchoredAtom2485 chi ∧
      Fin15AnchoredAtom2745 chi ∧
      Fin15AnchoredAtom4285 chi)) ∨
      ((Fin15AnchoredAtom2427 chi ∧
      Fin15AnchoredAtom2429 chi ∧
      Fin15AnchoredAtom2434 chi ∧
      Fin15AnchoredAtom2486 chi ∧
      Fin15AnchoredAtom2746 chi ∧
      Fin15AnchoredAtom4286 chi) ∨
      (Fin15AnchoredAtom2428 chi ∧
      Fin15AnchoredAtom2429 chi ∧
      Fin15AnchoredAtom2435 chi ∧
      Fin15AnchoredAtom2487 chi ∧
      Fin15AnchoredAtom2747 chi ∧
      Fin15AnchoredAtom4287 chi)))) ∨
      ((((Fin15AnchoredAtom2433 chi ∧
      Fin15AnchoredAtom2434 chi ∧
      Fin15AnchoredAtom2435 chi ∧
      Fin15AnchoredAtom2491 chi ∧
      Fin15AnchoredAtom2751 chi ∧
      Fin15AnchoredAtom4291 chi) ∨
      (Fin15AnchoredAtom2436 chi ∧
      Fin15AnchoredAtom2437 chi ∧
      Fin15AnchoredAtom2442 chi ∧
      Fin15AnchoredAtom2457 chi ∧
      Fin15AnchoredAtom2752 chi ∧
      Fin15AnchoredAtom4292 chi)) ∨
      ((Fin15AnchoredAtom2436 chi ∧
      Fin15AnchoredAtom2439 chi ∧
      Fin15AnchoredAtom2444 chi ∧
      Fin15AnchoredAtom2459 chi ∧
      Fin15AnchoredAtom2754 chi ∧
      Fin15AnchoredAtom4294 chi) ∨
      (Fin15AnchoredAtom2436 chi ∧
      Fin15AnchoredAtom2441 chi ∧
      Fin15AnchoredAtom2446 chi ∧
      Fin15AnchoredAtom2461 chi ∧
      Fin15AnchoredAtom2756 chi ∧
      Fin15AnchoredAtom4296 chi))) ∨
      (((Fin15AnchoredAtom2437 chi ∧
      Fin15AnchoredAtom2439 chi ∧
      Fin15AnchoredAtom2448 chi ∧
      Fin15AnchoredAtom2463 chi ∧
      Fin15AnchoredAtom2758 chi ∧
      Fin15AnchoredAtom4298 chi) ∨
      (Fin15AnchoredAtom2437 chi ∧
      Fin15AnchoredAtom2440 chi ∧
      Fin15AnchoredAtom2449 chi ∧
      Fin15AnchoredAtom2464 chi ∧
      Fin15AnchoredAtom2759 chi ∧
      Fin15AnchoredAtom4299 chi)) ∨
      ((Fin15AnchoredAtom2437 chi ∧
      Fin15AnchoredAtom2441 chi ∧
      Fin15AnchoredAtom2450 chi ∧
      Fin15AnchoredAtom2465 chi ∧
      Fin15AnchoredAtom2760 chi ∧
      Fin15AnchoredAtom4300 chi) ∨
      (Fin15AnchoredAtom2439 chi ∧
      Fin15AnchoredAtom2440 chi ∧
      Fin15AnchoredAtom2454 chi ∧
      Fin15AnchoredAtom2469 chi ∧
      Fin15AnchoredAtom2764 chi ∧
      Fin15AnchoredAtom4304 chi)))))) ∨
      ((((((Fin15AnchoredAtom2439 chi ∧
      Fin15AnchoredAtom2441 chi ∧
      Fin15AnchoredAtom2455 chi ∧
      Fin15AnchoredAtom2470 chi ∧
      Fin15AnchoredAtom2765 chi ∧
      Fin15AnchoredAtom4305 chi) ∨
      (Fin15AnchoredAtom2440 chi ∧
      Fin15AnchoredAtom2441 chi ∧
      Fin15AnchoredAtom2456 chi ∧
      Fin15AnchoredAtom2471 chi ∧
      Fin15AnchoredAtom2766 chi ∧
      Fin15AnchoredAtom4306 chi)) ∨
      ((Fin15AnchoredAtom2442 chi ∧
      Fin15AnchoredAtom2444 chi ∧
      Fin15AnchoredAtom2448 chi ∧
      Fin15AnchoredAtom2473 chi ∧
      Fin15AnchoredAtom2768 chi ∧
      Fin15AnchoredAtom4308 chi) ∨
      (Fin15AnchoredAtom2442 chi ∧
      Fin15AnchoredAtom2445 chi ∧
      Fin15AnchoredAtom2449 chi ∧
      Fin15AnchoredAtom2474 chi ∧
      Fin15AnchoredAtom2769 chi ∧
      Fin15AnchoredAtom4309 chi))) ∨
      (((Fin15AnchoredAtom2442 chi ∧
      Fin15AnchoredAtom2446 chi ∧
      Fin15AnchoredAtom2450 chi ∧
      Fin15AnchoredAtom2475 chi ∧
      Fin15AnchoredAtom2770 chi ∧
      Fin15AnchoredAtom4310 chi) ∨
      (Fin15AnchoredAtom2444 chi ∧
      Fin15AnchoredAtom2445 chi ∧
      Fin15AnchoredAtom2454 chi ∧
      Fin15AnchoredAtom2479 chi ∧
      Fin15AnchoredAtom2774 chi ∧
      Fin15AnchoredAtom4314 chi)) ∨
      ((Fin15AnchoredAtom2444 chi ∧
      Fin15AnchoredAtom2446 chi ∧
      Fin15AnchoredAtom2455 chi ∧
      Fin15AnchoredAtom2480 chi ∧
      Fin15AnchoredAtom2775 chi ∧
      Fin15AnchoredAtom4315 chi) ∨
      (Fin15AnchoredAtom2445 chi ∧
      Fin15AnchoredAtom2446 chi ∧
      Fin15AnchoredAtom2456 chi ∧
      Fin15AnchoredAtom2481 chi ∧
      Fin15AnchoredAtom2776 chi ∧
      Fin15AnchoredAtom4316 chi)))) ∨
      ((((Fin15AnchoredAtom2448 chi ∧
      Fin15AnchoredAtom2449 chi ∧
      Fin15AnchoredAtom2454 chi ∧
      Fin15AnchoredAtom2485 chi ∧
      Fin15AnchoredAtom2780 chi ∧
      Fin15AnchoredAtom4320 chi) ∨
      (Fin15AnchoredAtom2448 chi ∧
      Fin15AnchoredAtom2450 chi ∧
      Fin15AnchoredAtom2455 chi ∧
      Fin15AnchoredAtom2486 chi ∧
      Fin15AnchoredAtom2781 chi ∧
      Fin15AnchoredAtom4321 chi)) ∨
      ((Fin15AnchoredAtom2449 chi ∧
      Fin15AnchoredAtom2450 chi ∧
      Fin15AnchoredAtom2456 chi ∧
      Fin15AnchoredAtom2487 chi ∧
      Fin15AnchoredAtom2782 chi ∧
      Fin15AnchoredAtom4322 chi) ∨
      (Fin15AnchoredAtom2454 chi ∧
      Fin15AnchoredAtom2455 chi ∧
      Fin15AnchoredAtom2456 chi ∧
      Fin15AnchoredAtom2491 chi ∧
      Fin15AnchoredAtom2786 chi ∧
      Fin15AnchoredAtom4326 chi))) ∨
      (((Fin15AnchoredAtom2457 chi ∧
      Fin15AnchoredAtom2459 chi ∧
      Fin15AnchoredAtom2463 chi ∧
      Fin15AnchoredAtom2473 chi ∧
      Fin15AnchoredAtom2788 chi ∧
      Fin15AnchoredAtom4328 chi) ∨
      (Fin15AnchoredAtom2457 chi ∧
      Fin15AnchoredAtom2460 chi ∧
      Fin15AnchoredAtom2464 chi ∧
      Fin15AnchoredAtom2474 chi ∧
      Fin15AnchoredAtom2789 chi ∧
      Fin15AnchoredAtom4329 chi)) ∨
      ((Fin15AnchoredAtom2459 chi ∧
      Fin15AnchoredAtom2460 chi ∧
      Fin15AnchoredAtom2469 chi ∧
      Fin15AnchoredAtom2479 chi ∧
      Fin15AnchoredAtom2794 chi ∧
      Fin15AnchoredAtom4334 chi) ∨
      (Fin15AnchoredAtom2459 chi ∧
      Fin15AnchoredAtom2461 chi ∧
      Fin15AnchoredAtom2470 chi ∧
      Fin15AnchoredAtom2480 chi ∧
      Fin15AnchoredAtom2795 chi ∧
      Fin15AnchoredAtom4335 chi))))) ∨
      (((((Fin15AnchoredAtom2460 chi ∧
      Fin15AnchoredAtom2461 chi ∧
      Fin15AnchoredAtom2471 chi ∧
      Fin15AnchoredAtom2481 chi ∧
      Fin15AnchoredAtom2796 chi ∧
      Fin15AnchoredAtom4336 chi) ∨
      (Fin15AnchoredAtom2463 chi ∧
      Fin15AnchoredAtom2464 chi ∧
      Fin15AnchoredAtom2469 chi ∧
      Fin15AnchoredAtom2485 chi ∧
      Fin15AnchoredAtom2800 chi ∧
      Fin15AnchoredAtom4340 chi)) ∨
      ((Fin15AnchoredAtom2463 chi ∧
      Fin15AnchoredAtom2465 chi ∧
      Fin15AnchoredAtom2470 chi ∧
      Fin15AnchoredAtom2486 chi ∧
      Fin15AnchoredAtom2801 chi ∧
      Fin15AnchoredAtom4341 chi) ∨
      (Fin15AnchoredAtom2464 chi ∧
      Fin15AnchoredAtom2465 chi ∧
      Fin15AnchoredAtom2471 chi ∧
      Fin15AnchoredAtom2487 chi ∧
      Fin15AnchoredAtom2802 chi ∧
      Fin15AnchoredAtom4342 chi))) ∨
      (((Fin15AnchoredAtom2469 chi ∧
      Fin15AnchoredAtom2470 chi ∧
      Fin15AnchoredAtom2471 chi ∧
      Fin15AnchoredAtom2491 chi ∧
      Fin15AnchoredAtom2806 chi ∧
      Fin15AnchoredAtom4346 chi) ∨
      (Fin15AnchoredAtom2473 chi ∧
      Fin15AnchoredAtom2474 chi ∧
      Fin15AnchoredAtom2479 chi ∧
      Fin15AnchoredAtom2485 chi ∧
      Fin15AnchoredAtom2810 chi ∧
      Fin15AnchoredAtom4350 chi)) ∨
      ((Fin15AnchoredAtom2473 chi ∧
      Fin15AnchoredAtom2475 chi ∧
      Fin15AnchoredAtom2480 chi ∧
      Fin15AnchoredAtom2486 chi ∧
      Fin15AnchoredAtom2811 chi ∧
      Fin15AnchoredAtom4351 chi) ∨
      (Fin15AnchoredAtom2474 chi ∧
      Fin15AnchoredAtom2475 chi ∧
      Fin15AnchoredAtom2481 chi ∧
      Fin15AnchoredAtom2487 chi ∧
      Fin15AnchoredAtom2812 chi ∧
      Fin15AnchoredAtom4352 chi)))) ∨
      ((((Fin15AnchoredAtom2479 chi ∧
      Fin15AnchoredAtom2480 chi ∧
      Fin15AnchoredAtom2481 chi ∧
      Fin15AnchoredAtom2491 chi ∧
      Fin15AnchoredAtom2816 chi ∧
      Fin15AnchoredAtom4356 chi) ∨
      (Fin15AnchoredAtom2482 chi ∧
      Fin15AnchoredAtom2483 chi ∧
      Fin15AnchoredAtom2485 chi ∧
      Fin15AnchoredAtom2488 chi ∧
      Fin15AnchoredAtom2817 chi ∧
      Fin15AnchoredAtom4357 chi)) ∨
      ((Fin15AnchoredAtom2485 chi ∧
      Fin15AnchoredAtom2486 chi ∧
      Fin15AnchoredAtom2487 chi ∧
      Fin15AnchoredAtom2491 chi ∧
      Fin15AnchoredAtom2820 chi ∧
      Fin15AnchoredAtom4360 chi) ∨
      (Fin15AnchoredAtom2492 chi ∧
      Fin15AnchoredAtom2493 chi ∧
      Fin15AnchoredAtom2500 chi ∧
      Fin15AnchoredAtom2528 chi ∧
      Fin15AnchoredAtom2612 chi ∧
      Fin15AnchoredAtom4362 chi))) ∨
      (((Fin15AnchoredAtom2492 chi ∧
      Fin15AnchoredAtom2494 chi ∧
      Fin15AnchoredAtom2501 chi ∧
      Fin15AnchoredAtom2529 chi ∧
      Fin15AnchoredAtom2613 chi ∧
      Fin15AnchoredAtom4363 chi) ∨
      (Fin15AnchoredAtom2492 chi ∧
      Fin15AnchoredAtom2495 chi ∧
      Fin15AnchoredAtom2502 chi ∧
      Fin15AnchoredAtom2530 chi ∧
      Fin15AnchoredAtom2614 chi ∧
      Fin15AnchoredAtom4364 chi)) ∨
      ((Fin15AnchoredAtom2492 chi ∧
      Fin15AnchoredAtom2496 chi ∧
      Fin15AnchoredAtom2503 chi ∧
      Fin15AnchoredAtom2531 chi ∧
      Fin15AnchoredAtom2615 chi ∧
      Fin15AnchoredAtom4365 chi) ∨
      (Fin15AnchoredAtom2492 chi ∧
      Fin15AnchoredAtom2497 chi ∧
      Fin15AnchoredAtom2504 chi ∧
      Fin15AnchoredAtom2532 chi ∧
      Fin15AnchoredAtom2616 chi ∧
      Fin15AnchoredAtom4366 chi))))))) ∨
      ((((((Fin15AnchoredAtom2492 chi ∧
      Fin15AnchoredAtom2498 chi ∧
      Fin15AnchoredAtom2505 chi ∧
      Fin15AnchoredAtom2533 chi ∧
      Fin15AnchoredAtom2617 chi ∧
      Fin15AnchoredAtom4367 chi) ∨
      ((Fin15AnchoredAtom2492 chi ∧
      Fin15AnchoredAtom2499 chi ∧
      Fin15AnchoredAtom2506 chi ∧
      Fin15AnchoredAtom2534 chi ∧
      Fin15AnchoredAtom2618 chi ∧
      Fin15AnchoredAtom4368 chi) ∨
      (Fin15AnchoredAtom2493 chi ∧
      Fin15AnchoredAtom2494 chi ∧
      Fin15AnchoredAtom2507 chi ∧
      Fin15AnchoredAtom2535 chi ∧
      Fin15AnchoredAtom2619 chi ∧
      Fin15AnchoredAtom4369 chi))) ∨
      (((Fin15AnchoredAtom2493 chi ∧
      Fin15AnchoredAtom2495 chi ∧
      Fin15AnchoredAtom2508 chi ∧
      Fin15AnchoredAtom2536 chi ∧
      Fin15AnchoredAtom2620 chi ∧
      Fin15AnchoredAtom4370 chi) ∨
      (Fin15AnchoredAtom2493 chi ∧
      Fin15AnchoredAtom2497 chi ∧
      Fin15AnchoredAtom2510 chi ∧
      Fin15AnchoredAtom2538 chi ∧
      Fin15AnchoredAtom2622 chi ∧
      Fin15AnchoredAtom4372 chi)) ∨
      ((Fin15AnchoredAtom2493 chi ∧
      Fin15AnchoredAtom2498 chi ∧
      Fin15AnchoredAtom2511 chi ∧
      Fin15AnchoredAtom2539 chi ∧
      Fin15AnchoredAtom2623 chi ∧
      Fin15AnchoredAtom4373 chi) ∨
      (Fin15AnchoredAtom2493 chi ∧
      Fin15AnchoredAtom2499 chi ∧
      Fin15AnchoredAtom2512 chi ∧
      Fin15AnchoredAtom2540 chi ∧
      Fin15AnchoredAtom2624 chi ∧
      Fin15AnchoredAtom4374 chi)))) ∨
      ((((Fin15AnchoredAtom2494 chi ∧
      Fin15AnchoredAtom2495 chi ∧
      Fin15AnchoredAtom2513 chi ∧
      Fin15AnchoredAtom2541 chi ∧
      Fin15AnchoredAtom2625 chi ∧
      Fin15AnchoredAtom4375 chi) ∨
      (Fin15AnchoredAtom2494 chi ∧
      Fin15AnchoredAtom2496 chi ∧
      Fin15AnchoredAtom2514 chi ∧
      Fin15AnchoredAtom2542 chi ∧
      Fin15AnchoredAtom2626 chi ∧
      Fin15AnchoredAtom4376 chi)) ∨
      ((Fin15AnchoredAtom2494 chi ∧
      Fin15AnchoredAtom2497 chi ∧
      Fin15AnchoredAtom2515 chi ∧
      Fin15AnchoredAtom2543 chi ∧
      Fin15AnchoredAtom2627 chi ∧
      Fin15AnchoredAtom4377 chi) ∨
      (Fin15AnchoredAtom2494 chi ∧
      Fin15AnchoredAtom2498 chi ∧
      Fin15AnchoredAtom2516 chi ∧
      Fin15AnchoredAtom2544 chi ∧
      Fin15AnchoredAtom2628 chi ∧
      Fin15AnchoredAtom4378 chi))) ∨
      (((Fin15AnchoredAtom2494 chi ∧
      Fin15AnchoredAtom2499 chi ∧
      Fin15AnchoredAtom2517 chi ∧
      Fin15AnchoredAtom2545 chi ∧
      Fin15AnchoredAtom2629 chi ∧
      Fin15AnchoredAtom4379 chi) ∨
      (Fin15AnchoredAtom2495 chi ∧
      Fin15AnchoredAtom2496 chi ∧
      Fin15AnchoredAtom2518 chi ∧
      Fin15AnchoredAtom2546 chi ∧
      Fin15AnchoredAtom2630 chi ∧
      Fin15AnchoredAtom4380 chi)) ∨
      ((Fin15AnchoredAtom2495 chi ∧
      Fin15AnchoredAtom2497 chi ∧
      Fin15AnchoredAtom2519 chi ∧
      Fin15AnchoredAtom2547 chi ∧
      Fin15AnchoredAtom2631 chi ∧
      Fin15AnchoredAtom4381 chi) ∨
      (Fin15AnchoredAtom2495 chi ∧
      Fin15AnchoredAtom2498 chi ∧
      Fin15AnchoredAtom2520 chi ∧
      Fin15AnchoredAtom2548 chi ∧
      Fin15AnchoredAtom2632 chi ∧
      Fin15AnchoredAtom4382 chi))))) ∨
      (((((Fin15AnchoredAtom2495 chi ∧
      Fin15AnchoredAtom2499 chi ∧
      Fin15AnchoredAtom2521 chi ∧
      Fin15AnchoredAtom2549 chi ∧
      Fin15AnchoredAtom2633 chi ∧
      Fin15AnchoredAtom4383 chi) ∨
      (Fin15AnchoredAtom2497 chi ∧
      Fin15AnchoredAtom2498 chi ∧
      Fin15AnchoredAtom2525 chi ∧
      Fin15AnchoredAtom2553 chi ∧
      Fin15AnchoredAtom2637 chi ∧
      Fin15AnchoredAtom4387 chi)) ∨
      ((Fin15AnchoredAtom2497 chi ∧
      Fin15AnchoredAtom2499 chi ∧
      Fin15AnchoredAtom2526 chi ∧
      Fin15AnchoredAtom2554 chi ∧
      Fin15AnchoredAtom2638 chi ∧
      Fin15AnchoredAtom4388 chi) ∨
      (Fin15AnchoredAtom2498 chi ∧
      Fin15AnchoredAtom2499 chi ∧
      Fin15AnchoredAtom2527 chi ∧
      Fin15AnchoredAtom2555 chi ∧
      Fin15AnchoredAtom2639 chi ∧
      Fin15AnchoredAtom4389 chi))) ∨
      (((Fin15AnchoredAtom2500 chi ∧
      Fin15AnchoredAtom2501 chi ∧
      Fin15AnchoredAtom2507 chi ∧
      Fin15AnchoredAtom2556 chi ∧
      Fin15AnchoredAtom2640 chi ∧
      Fin15AnchoredAtom4390 chi) ∨
      (Fin15AnchoredAtom2500 chi ∧
      Fin15AnchoredAtom2502 chi ∧
      Fin15AnchoredAtom2508 chi ∧
      Fin15AnchoredAtom2557 chi ∧
      Fin15AnchoredAtom2641 chi ∧
      Fin15AnchoredAtom4391 chi)) ∨
      ((Fin15AnchoredAtom2500 chi ∧
      Fin15AnchoredAtom2506 chi ∧
      Fin15AnchoredAtom2512 chi ∧
      Fin15AnchoredAtom2561 chi ∧
      Fin15AnchoredAtom2645 chi ∧
      Fin15AnchoredAtom4395 chi) ∨
      (Fin15AnchoredAtom2501 chi ∧
      Fin15AnchoredAtom2502 chi ∧
      Fin15AnchoredAtom2513 chi ∧
      Fin15AnchoredAtom2562 chi ∧
      Fin15AnchoredAtom2646 chi ∧
      Fin15AnchoredAtom4396 chi)))) ∨
      ((((Fin15AnchoredAtom2501 chi ∧
      Fin15AnchoredAtom2504 chi ∧
      Fin15AnchoredAtom2515 chi ∧
      Fin15AnchoredAtom2564 chi ∧
      Fin15AnchoredAtom2648 chi ∧
      Fin15AnchoredAtom4398 chi) ∨
      (Fin15AnchoredAtom2501 chi ∧
      Fin15AnchoredAtom2505 chi ∧
      Fin15AnchoredAtom2516 chi ∧
      Fin15AnchoredAtom2565 chi ∧
      Fin15AnchoredAtom2649 chi ∧
      Fin15AnchoredAtom4399 chi)) ∨
      ((Fin15AnchoredAtom2501 chi ∧
      Fin15AnchoredAtom2506 chi ∧
      Fin15AnchoredAtom2517 chi ∧
      Fin15AnchoredAtom2566 chi ∧
      Fin15AnchoredAtom2650 chi ∧
      Fin15AnchoredAtom4400 chi) ∨
      (Fin15AnchoredAtom2502 chi ∧
      Fin15AnchoredAtom2503 chi ∧
      Fin15AnchoredAtom2518 chi ∧
      Fin15AnchoredAtom2567 chi ∧
      Fin15AnchoredAtom2651 chi ∧
      Fin15AnchoredAtom4401 chi))) ∨
      (((Fin15AnchoredAtom2502 chi ∧
      Fin15AnchoredAtom2504 chi ∧
      Fin15AnchoredAtom2519 chi ∧
      Fin15AnchoredAtom2568 chi ∧
      Fin15AnchoredAtom2652 chi ∧
      Fin15AnchoredAtom4402 chi) ∨
      (Fin15AnchoredAtom2502 chi ∧
      Fin15AnchoredAtom2505 chi ∧
      Fin15AnchoredAtom2520 chi ∧
      Fin15AnchoredAtom2569 chi ∧
      Fin15AnchoredAtom2653 chi ∧
      Fin15AnchoredAtom4403 chi)) ∨
      ((Fin15AnchoredAtom2502 chi ∧
      Fin15AnchoredAtom2506 chi ∧
      Fin15AnchoredAtom2521 chi ∧
      Fin15AnchoredAtom2570 chi ∧
      Fin15AnchoredAtom2654 chi ∧
      Fin15AnchoredAtom4404 chi) ∨
      (Fin15AnchoredAtom2504 chi ∧
      Fin15AnchoredAtom2505 chi ∧
      Fin15AnchoredAtom2525 chi ∧
      Fin15AnchoredAtom2574 chi ∧
      Fin15AnchoredAtom2658 chi ∧
      Fin15AnchoredAtom4408 chi)))))) ∨
      ((((((Fin15AnchoredAtom2504 chi ∧
      Fin15AnchoredAtom2506 chi ∧
      Fin15AnchoredAtom2526 chi ∧
      Fin15AnchoredAtom2575 chi ∧
      Fin15AnchoredAtom2659 chi ∧
      Fin15AnchoredAtom4409 chi) ∨
      (Fin15AnchoredAtom2505 chi ∧
      Fin15AnchoredAtom2506 chi ∧
      Fin15AnchoredAtom2527 chi ∧
      Fin15AnchoredAtom2576 chi ∧
      Fin15AnchoredAtom2660 chi ∧
      Fin15AnchoredAtom4410 chi)) ∨
      ((Fin15AnchoredAtom2507 chi ∧
      Fin15AnchoredAtom2508 chi ∧
      Fin15AnchoredAtom2513 chi ∧
      Fin15AnchoredAtom2577 chi ∧
      Fin15AnchoredAtom2661 chi ∧
      Fin15AnchoredAtom4411 chi) ∨
      (Fin15AnchoredAtom2507 chi ∧
      Fin15AnchoredAtom2510 chi ∧
      Fin15AnchoredAtom2515 chi ∧
      Fin15AnchoredAtom2579 chi ∧
      Fin15AnchoredAtom2663 chi ∧
      Fin15AnchoredAtom4413 chi))) ∨
      (((Fin15AnchoredAtom2507 chi ∧
      Fin15AnchoredAtom2512 chi ∧
      Fin15AnchoredAtom2517 chi ∧
      Fin15AnchoredAtom2581 chi ∧
      Fin15AnchoredAtom2665 chi ∧
      Fin15AnchoredAtom4415 chi) ∨
      (Fin15AnchoredAtom2508 chi ∧
      Fin15AnchoredAtom2510 chi ∧
      Fin15AnchoredAtom2519 chi ∧
      Fin15AnchoredAtom2583 chi ∧
      Fin15AnchoredAtom2667 chi ∧
      Fin15AnchoredAtom4417 chi)) ∨
      ((Fin15AnchoredAtom2508 chi ∧
      Fin15AnchoredAtom2512 chi ∧
      Fin15AnchoredAtom2521 chi ∧
      Fin15AnchoredAtom2585 chi ∧
      Fin15AnchoredAtom2669 chi ∧
      Fin15AnchoredAtom4419 chi) ∨
      (Fin15AnchoredAtom2510 chi ∧
      Fin15AnchoredAtom2511 chi ∧
      Fin15AnchoredAtom2525 chi ∧
      Fin15AnchoredAtom2589 chi ∧
      Fin15AnchoredAtom2673 chi ∧
      Fin15AnchoredAtom4423 chi)))) ∨
      ((((Fin15AnchoredAtom2510 chi ∧
      Fin15AnchoredAtom2512 chi ∧
      Fin15AnchoredAtom2526 chi ∧
      Fin15AnchoredAtom2590 chi ∧
      Fin15AnchoredAtom2674 chi ∧
      Fin15AnchoredAtom4424 chi) ∨
      (Fin15AnchoredAtom2513 chi ∧
      Fin15AnchoredAtom2514 chi ∧
      Fin15AnchoredAtom2518 chi ∧
      Fin15AnchoredAtom2592 chi ∧
      Fin15AnchoredAtom2676 chi ∧
      Fin15AnchoredAtom4426 chi)) ∨
      ((Fin15AnchoredAtom2513 chi ∧
      Fin15AnchoredAtom2515 chi ∧
      Fin15AnchoredAtom2519 chi ∧
      Fin15AnchoredAtom2593 chi ∧
      Fin15AnchoredAtom2677 chi ∧
      Fin15AnchoredAtom4427 chi) ∨
      (Fin15AnchoredAtom2513 chi ∧
      Fin15AnchoredAtom2516 chi ∧
      Fin15AnchoredAtom2520 chi ∧
      Fin15AnchoredAtom2594 chi ∧
      Fin15AnchoredAtom2678 chi ∧
      Fin15AnchoredAtom4428 chi))) ∨
      (((Fin15AnchoredAtom2513 chi ∧
      Fin15AnchoredAtom2517 chi ∧
      Fin15AnchoredAtom2521 chi ∧
      Fin15AnchoredAtom2595 chi ∧
      Fin15AnchoredAtom2679 chi ∧
      Fin15AnchoredAtom4429 chi) ∨
      (Fin15AnchoredAtom2514 chi ∧
      Fin15AnchoredAtom2515 chi ∧
      Fin15AnchoredAtom2522 chi ∧
      Fin15AnchoredAtom2596 chi ∧
      Fin15AnchoredAtom2680 chi ∧
      Fin15AnchoredAtom4430 chi)) ∨
      ((Fin15AnchoredAtom2514 chi ∧
      Fin15AnchoredAtom2516 chi ∧
      Fin15AnchoredAtom2523 chi ∧
      Fin15AnchoredAtom2597 chi ∧
      Fin15AnchoredAtom2681 chi ∧
      Fin15AnchoredAtom4431 chi) ∨
      (Fin15AnchoredAtom2514 chi ∧
      Fin15AnchoredAtom2517 chi ∧
      Fin15AnchoredAtom2524 chi ∧
      Fin15AnchoredAtom2598 chi ∧
      Fin15AnchoredAtom2682 chi ∧
      Fin15AnchoredAtom4432 chi))))) ∨
      (((((Fin15AnchoredAtom2515 chi ∧
      Fin15AnchoredAtom2516 chi ∧
      Fin15AnchoredAtom2525 chi ∧
      Fin15AnchoredAtom2599 chi ∧
      Fin15AnchoredAtom2683 chi ∧
      Fin15AnchoredAtom4433 chi) ∨
      (Fin15AnchoredAtom2515 chi ∧
      Fin15AnchoredAtom2517 chi ∧
      Fin15AnchoredAtom2526 chi ∧
      Fin15AnchoredAtom2600 chi ∧
      Fin15AnchoredAtom2684 chi ∧
      Fin15AnchoredAtom4434 chi)) ∨
      ((Fin15AnchoredAtom2516 chi ∧
      Fin15AnchoredAtom2517 chi ∧
      Fin15AnchoredAtom2527 chi ∧
      Fin15AnchoredAtom2601 chi ∧
      Fin15AnchoredAtom2685 chi ∧
      Fin15AnchoredAtom4435 chi) ∨
      (Fin15AnchoredAtom2518 chi ∧
      Fin15AnchoredAtom2519 chi ∧
      Fin15AnchoredAtom2522 chi ∧
      Fin15AnchoredAtom2602 chi ∧
      Fin15AnchoredAtom2686 chi ∧
      Fin15AnchoredAtom4436 chi))) ∨
      (((Fin15AnchoredAtom2518 chi ∧
      Fin15AnchoredAtom2520 chi ∧
      Fin15AnchoredAtom2523 chi ∧
      Fin15AnchoredAtom2603 chi ∧
      Fin15AnchoredAtom2687 chi ∧
      Fin15AnchoredAtom4437 chi) ∨
      (Fin15AnchoredAtom2519 chi ∧
      Fin15AnchoredAtom2520 chi ∧
      Fin15AnchoredAtom2525 chi ∧
      Fin15AnchoredAtom2605 chi ∧
      Fin15AnchoredAtom2689 chi ∧
      Fin15AnchoredAtom4439 chi)) ∨
      ((Fin15AnchoredAtom2519 chi ∧
      Fin15AnchoredAtom2521 chi ∧
      Fin15AnchoredAtom2526 chi ∧
      Fin15AnchoredAtom2606 chi ∧
      Fin15AnchoredAtom2690 chi ∧
      Fin15AnchoredAtom4440 chi) ∨
      (Fin15AnchoredAtom2520 chi ∧
      Fin15AnchoredAtom2521 chi ∧
      Fin15AnchoredAtom2527 chi ∧
      Fin15AnchoredAtom2607 chi ∧
      Fin15AnchoredAtom2691 chi ∧
      Fin15AnchoredAtom4441 chi)))) ∨
      ((((Fin15AnchoredAtom2522 chi ∧
      Fin15AnchoredAtom2523 chi ∧
      Fin15AnchoredAtom2525 chi ∧
      Fin15AnchoredAtom2608 chi ∧
      Fin15AnchoredAtom2692 chi ∧
      Fin15AnchoredAtom4442 chi) ∨
      (Fin15AnchoredAtom2525 chi ∧
      Fin15AnchoredAtom2526 chi ∧
      Fin15AnchoredAtom2527 chi ∧
      Fin15AnchoredAtom2611 chi ∧
      Fin15AnchoredAtom2695 chi ∧
      Fin15AnchoredAtom4445 chi)) ∨
      ((Fin15AnchoredAtom2528 chi ∧
      Fin15AnchoredAtom2529 chi ∧
      Fin15AnchoredAtom2535 chi ∧
      Fin15AnchoredAtom2556 chi ∧
      Fin15AnchoredAtom2696 chi ∧
      Fin15AnchoredAtom4446 chi) ∨
      (Fin15AnchoredAtom2528 chi ∧
      Fin15AnchoredAtom2530 chi ∧
      Fin15AnchoredAtom2536 chi ∧
      Fin15AnchoredAtom2557 chi ∧
      Fin15AnchoredAtom2697 chi ∧
      Fin15AnchoredAtom4447 chi))) ∨
      (((Fin15AnchoredAtom2528 chi ∧
      Fin15AnchoredAtom2532 chi ∧
      Fin15AnchoredAtom2538 chi ∧
      Fin15AnchoredAtom2559 chi ∧
      Fin15AnchoredAtom2699 chi ∧
      Fin15AnchoredAtom4449 chi) ∨
      (Fin15AnchoredAtom2528 chi ∧
      Fin15AnchoredAtom2533 chi ∧
      Fin15AnchoredAtom2539 chi ∧
      Fin15AnchoredAtom2560 chi ∧
      Fin15AnchoredAtom2700 chi ∧
      Fin15AnchoredAtom4450 chi)) ∨
      ((Fin15AnchoredAtom2529 chi ∧
      Fin15AnchoredAtom2530 chi ∧
      Fin15AnchoredAtom2541 chi ∧
      Fin15AnchoredAtom2562 chi ∧
      Fin15AnchoredAtom2702 chi ∧
      Fin15AnchoredAtom4452 chi) ∨
      (Fin15AnchoredAtom2529 chi ∧
      Fin15AnchoredAtom2531 chi ∧
      Fin15AnchoredAtom2542 chi ∧
      Fin15AnchoredAtom2563 chi ∧
      Fin15AnchoredAtom2703 chi ∧
      Fin15AnchoredAtom4453 chi)))))))) ∨
      (((((((Fin15AnchoredAtom2529 chi ∧
      Fin15AnchoredAtom2532 chi ∧
      Fin15AnchoredAtom2543 chi ∧
      Fin15AnchoredAtom2564 chi ∧
      Fin15AnchoredAtom2704 chi ∧
      Fin15AnchoredAtom4454 chi) ∨
      ((Fin15AnchoredAtom2529 chi ∧
      Fin15AnchoredAtom2533 chi ∧
      Fin15AnchoredAtom2544 chi ∧
      Fin15AnchoredAtom2565 chi ∧
      Fin15AnchoredAtom2705 chi ∧
      Fin15AnchoredAtom4455 chi) ∨
      (Fin15AnchoredAtom2529 chi ∧
      Fin15AnchoredAtom2534 chi ∧
      Fin15AnchoredAtom2545 chi ∧
      Fin15AnchoredAtom2566 chi ∧
      Fin15AnchoredAtom2706 chi ∧
      Fin15AnchoredAtom4456 chi))) ∨
      (((Fin15AnchoredAtom2530 chi ∧
      Fin15AnchoredAtom2532 chi ∧
      Fin15AnchoredAtom2547 chi ∧
      Fin15AnchoredAtom2568 chi ∧
      Fin15AnchoredAtom2708 chi ∧
      Fin15AnchoredAtom4458 chi) ∨
      (Fin15AnchoredAtom2530 chi ∧
      Fin15AnchoredAtom2533 chi ∧
      Fin15AnchoredAtom2548 chi ∧
      Fin15AnchoredAtom2569 chi ∧
      Fin15AnchoredAtom2709 chi ∧
      Fin15AnchoredAtom4459 chi)) ∨
      ((Fin15AnchoredAtom2530 chi ∧
      Fin15AnchoredAtom2534 chi ∧
      Fin15AnchoredAtom2549 chi ∧
      Fin15AnchoredAtom2570 chi ∧
      Fin15AnchoredAtom2710 chi ∧
      Fin15AnchoredAtom4460 chi) ∨
      (Fin15AnchoredAtom2532 chi ∧
      Fin15AnchoredAtom2533 chi ∧
      Fin15AnchoredAtom2553 chi ∧
      Fin15AnchoredAtom2574 chi ∧
      Fin15AnchoredAtom2714 chi ∧
      Fin15AnchoredAtom4464 chi)))) ∨
      ((((Fin15AnchoredAtom2532 chi ∧
      Fin15AnchoredAtom2534 chi ∧
      Fin15AnchoredAtom2554 chi ∧
      Fin15AnchoredAtom2575 chi ∧
      Fin15AnchoredAtom2715 chi ∧
      Fin15AnchoredAtom4465 chi) ∨
      (Fin15AnchoredAtom2533 chi ∧
      Fin15AnchoredAtom2534 chi ∧
      Fin15AnchoredAtom2555 chi ∧
      Fin15AnchoredAtom2576 chi ∧
      Fin15AnchoredAtom2716 chi ∧
      Fin15AnchoredAtom4466 chi)) ∨
      ((Fin15AnchoredAtom2535 chi ∧
      Fin15AnchoredAtom2536 chi ∧
      Fin15AnchoredAtom2541 chi ∧
      Fin15AnchoredAtom2577 chi ∧
      Fin15AnchoredAtom2717 chi ∧
      Fin15AnchoredAtom4467 chi) ∨
      (Fin15AnchoredAtom2535 chi ∧
      Fin15AnchoredAtom2538 chi ∧
      Fin15AnchoredAtom2543 chi ∧
      Fin15AnchoredAtom2579 chi ∧
      Fin15AnchoredAtom2719 chi ∧
      Fin15AnchoredAtom4469 chi))) ∨
      (((Fin15AnchoredAtom2535 chi ∧
      Fin15AnchoredAtom2539 chi ∧
      Fin15AnchoredAtom2544 chi ∧
      Fin15AnchoredAtom2580 chi ∧
      Fin15AnchoredAtom2720 chi ∧
      Fin15AnchoredAtom4470 chi) ∨
      (Fin15AnchoredAtom2535 chi ∧
      Fin15AnchoredAtom2540 chi ∧
      Fin15AnchoredAtom2545 chi ∧
      Fin15AnchoredAtom2581 chi ∧
      Fin15AnchoredAtom2721 chi ∧
      Fin15AnchoredAtom4471 chi)) ∨
      ((Fin15AnchoredAtom2536 chi ∧
      Fin15AnchoredAtom2538 chi ∧
      Fin15AnchoredAtom2547 chi ∧
      Fin15AnchoredAtom2583 chi ∧
      Fin15AnchoredAtom2723 chi ∧
      Fin15AnchoredAtom4473 chi) ∨
      (Fin15AnchoredAtom2536 chi ∧
      Fin15AnchoredAtom2540 chi ∧
      Fin15AnchoredAtom2549 chi ∧
      Fin15AnchoredAtom2585 chi ∧
      Fin15AnchoredAtom2725 chi ∧
      Fin15AnchoredAtom4475 chi))))) ∨
      (((((Fin15AnchoredAtom2538 chi ∧
      Fin15AnchoredAtom2539 chi ∧
      Fin15AnchoredAtom2553 chi ∧
      Fin15AnchoredAtom2589 chi ∧
      Fin15AnchoredAtom2729 chi ∧
      Fin15AnchoredAtom4479 chi) ∨
      (Fin15AnchoredAtom2538 chi ∧
      Fin15AnchoredAtom2540 chi ∧
      Fin15AnchoredAtom2554 chi ∧
      Fin15AnchoredAtom2590 chi ∧
      Fin15AnchoredAtom2730 chi ∧
      Fin15AnchoredAtom4480 chi)) ∨
      ((Fin15AnchoredAtom2539 chi ∧
      Fin15AnchoredAtom2540 chi ∧
      Fin15AnchoredAtom2555 chi ∧
      Fin15AnchoredAtom2591 chi ∧
      Fin15AnchoredAtom2731 chi ∧
      Fin15AnchoredAtom4481 chi) ∨
      (Fin15AnchoredAtom2541 chi ∧
      Fin15AnchoredAtom2542 chi ∧
      Fin15AnchoredAtom2546 chi ∧
      Fin15AnchoredAtom2592 chi ∧
      Fin15AnchoredAtom2732 chi ∧
      Fin15AnchoredAtom4482 chi))) ∨
      (((Fin15AnchoredAtom2541 chi ∧
      Fin15AnchoredAtom2543 chi ∧
      Fin15AnchoredAtom2547 chi ∧
      Fin15AnchoredAtom2593 chi ∧
      Fin15AnchoredAtom2733 chi ∧
      Fin15AnchoredAtom4483 chi) ∨
      (Fin15AnchoredAtom2541 chi ∧
      Fin15AnchoredAtom2544 chi ∧
      Fin15AnchoredAtom2548 chi ∧
      Fin15AnchoredAtom2594 chi ∧
      Fin15AnchoredAtom2734 chi ∧
      Fin15AnchoredAtom4484 chi)) ∨
      ((Fin15AnchoredAtom2541 chi ∧
      Fin15AnchoredAtom2545 chi ∧
      Fin15AnchoredAtom2549 chi ∧
      Fin15AnchoredAtom2595 chi ∧
      Fin15AnchoredAtom2735 chi ∧
      Fin15AnchoredAtom4485 chi) ∨
      (Fin15AnchoredAtom2543 chi ∧
      Fin15AnchoredAtom2544 chi ∧
      Fin15AnchoredAtom2553 chi ∧
      Fin15AnchoredAtom2599 chi ∧
      Fin15AnchoredAtom2739 chi ∧
      Fin15AnchoredAtom4489 chi)))) ∨
      ((((Fin15AnchoredAtom2543 chi ∧
      Fin15AnchoredAtom2545 chi ∧
      Fin15AnchoredAtom2554 chi ∧
      Fin15AnchoredAtom2600 chi ∧
      Fin15AnchoredAtom2740 chi ∧
      Fin15AnchoredAtom4490 chi) ∨
      (Fin15AnchoredAtom2544 chi ∧
      Fin15AnchoredAtom2545 chi ∧
      Fin15AnchoredAtom2555 chi ∧
      Fin15AnchoredAtom2601 chi ∧
      Fin15AnchoredAtom2741 chi ∧
      Fin15AnchoredAtom4491 chi)) ∨
      ((Fin15AnchoredAtom2546 chi ∧
      Fin15AnchoredAtom2548 chi ∧
      Fin15AnchoredAtom2551 chi ∧
      Fin15AnchoredAtom2603 chi ∧
      Fin15AnchoredAtom2743 chi ∧
      Fin15AnchoredAtom4493 chi) ∨
      (Fin15AnchoredAtom2547 chi ∧
      Fin15AnchoredAtom2548 chi ∧
      Fin15AnchoredAtom2553 chi ∧
      Fin15AnchoredAtom2605 chi ∧
      Fin15AnchoredAtom2745 chi ∧
      Fin15AnchoredAtom4495 chi))) ∨
      (((Fin15AnchoredAtom2547 chi ∧
      Fin15AnchoredAtom2549 chi ∧
      Fin15AnchoredAtom2554 chi ∧
      Fin15AnchoredAtom2606 chi ∧
      Fin15AnchoredAtom2746 chi ∧
      Fin15AnchoredAtom4496 chi) ∨
      (Fin15AnchoredAtom2548 chi ∧
      Fin15AnchoredAtom2549 chi ∧
      Fin15AnchoredAtom2555 chi ∧
      Fin15AnchoredAtom2607 chi ∧
      Fin15AnchoredAtom2747 chi ∧
      Fin15AnchoredAtom4497 chi)) ∨
      ((Fin15AnchoredAtom2550 chi ∧
      Fin15AnchoredAtom2551 chi ∧
      Fin15AnchoredAtom2553 chi ∧
      Fin15AnchoredAtom2608 chi ∧
      Fin15AnchoredAtom2748 chi ∧
      Fin15AnchoredAtom4498 chi) ∨
      (Fin15AnchoredAtom2553 chi ∧
      Fin15AnchoredAtom2554 chi ∧
      Fin15AnchoredAtom2555 chi ∧
      Fin15AnchoredAtom2611 chi ∧
      Fin15AnchoredAtom2751 chi ∧
      Fin15AnchoredAtom4501 chi)))))) ∨
      ((((((Fin15AnchoredAtom2556 chi ∧
      Fin15AnchoredAtom2559 chi ∧
      Fin15AnchoredAtom2564 chi ∧
      Fin15AnchoredAtom2579 chi ∧
      Fin15AnchoredAtom2754 chi ∧
      Fin15AnchoredAtom4504 chi) ∨
      (Fin15AnchoredAtom2556 chi ∧
      Fin15AnchoredAtom2561 chi ∧
      Fin15AnchoredAtom2566 chi ∧
      Fin15AnchoredAtom2581 chi ∧
      Fin15AnchoredAtom2756 chi ∧
      Fin15AnchoredAtom4506 chi)) ∨
      ((Fin15AnchoredAtom2557 chi ∧
      Fin15AnchoredAtom2559 chi ∧
      Fin15AnchoredAtom2568 chi ∧
      Fin15AnchoredAtom2583 chi ∧
      Fin15AnchoredAtom2758 chi ∧
      Fin15AnchoredAtom4508 chi) ∨
      (Fin15AnchoredAtom2557 chi ∧
      Fin15AnchoredAtom2560 chi ∧
      Fin15AnchoredAtom2569 chi ∧
      Fin15AnchoredAtom2584 chi ∧
      Fin15AnchoredAtom2759 chi ∧
      Fin15AnchoredAtom4509 chi))) ∨
      (((Fin15AnchoredAtom2559 chi ∧
      Fin15AnchoredAtom2561 chi ∧
      Fin15AnchoredAtom2575 chi ∧
      Fin15AnchoredAtom2590 chi ∧
      Fin15AnchoredAtom2765 chi ∧
      Fin15AnchoredAtom4515 chi) ∨
      (Fin15AnchoredAtom2562 chi ∧
      Fin15AnchoredAtom2564 chi ∧
      Fin15AnchoredAtom2568 chi ∧
      Fin15AnchoredAtom2593 chi ∧
      Fin15AnchoredAtom2768 chi ∧
      Fin15AnchoredAtom4518 chi)) ∨
      ((Fin15AnchoredAtom2562 chi ∧
      Fin15AnchoredAtom2565 chi ∧
      Fin15AnchoredAtom2569 chi ∧
      Fin15AnchoredAtom2594 chi ∧
      Fin15AnchoredAtom2769 chi ∧
      Fin15AnchoredAtom4519 chi) ∨
      (Fin15AnchoredAtom2562 chi ∧
      Fin15AnchoredAtom2566 chi ∧
      Fin15AnchoredAtom2570 chi ∧
      Fin15AnchoredAtom2595 chi ∧
      Fin15AnchoredAtom2770 chi ∧
      Fin15AnchoredAtom4520 chi)))) ∨
      ((((Fin15AnchoredAtom2564 chi ∧
      Fin15AnchoredAtom2565 chi ∧
      Fin15AnchoredAtom2574 chi ∧
      Fin15AnchoredAtom2599 chi ∧
      Fin15AnchoredAtom2774 chi ∧
      Fin15AnchoredAtom4524 chi) ∨
      (Fin15AnchoredAtom2564 chi ∧
      Fin15AnchoredAtom2566 chi ∧
      Fin15AnchoredAtom2575 chi ∧
      Fin15AnchoredAtom2600 chi ∧
      Fin15AnchoredAtom2775 chi ∧
      Fin15AnchoredAtom4525 chi)) ∨
      ((Fin15AnchoredAtom2565 chi ∧
      Fin15AnchoredAtom2566 chi ∧
      Fin15AnchoredAtom2576 chi ∧
      Fin15AnchoredAtom2601 chi ∧
      Fin15AnchoredAtom2776 chi ∧
      Fin15AnchoredAtom4526 chi) ∨
      (Fin15AnchoredAtom2567 chi ∧
      Fin15AnchoredAtom2568 chi ∧
      Fin15AnchoredAtom2571 chi ∧
      Fin15AnchoredAtom2602 chi ∧
      Fin15AnchoredAtom2777 chi ∧
      Fin15AnchoredAtom4527 chi))) ∨
      (((Fin15AnchoredAtom2568 chi ∧
      Fin15AnchoredAtom2569 chi ∧
      Fin15AnchoredAtom2574 chi ∧
      Fin15AnchoredAtom2605 chi ∧
      Fin15AnchoredAtom2780 chi ∧
      Fin15AnchoredAtom4530 chi) ∨
      (Fin15AnchoredAtom2568 chi ∧
      Fin15AnchoredAtom2570 chi ∧
      Fin15AnchoredAtom2575 chi ∧
      Fin15AnchoredAtom2606 chi ∧
      Fin15AnchoredAtom2781 chi ∧
      Fin15AnchoredAtom4531 chi)) ∨
      ((Fin15AnchoredAtom2569 chi ∧
      Fin15AnchoredAtom2570 chi ∧
      Fin15AnchoredAtom2576 chi ∧
      Fin15AnchoredAtom2607 chi ∧
      Fin15AnchoredAtom2782 chi ∧
      Fin15AnchoredAtom4532 chi) ∨
      (Fin15AnchoredAtom2574 chi ∧
      Fin15AnchoredAtom2575 chi ∧
      Fin15AnchoredAtom2576 chi ∧
      Fin15AnchoredAtom2611 chi ∧
      Fin15AnchoredAtom2786 chi ∧
      Fin15AnchoredAtom4536 chi))))) ∨
      (((((Fin15AnchoredAtom2577 chi ∧
      Fin15AnchoredAtom2579 chi ∧
      Fin15AnchoredAtom2583 chi ∧
      Fin15AnchoredAtom2593 chi ∧
      Fin15AnchoredAtom2788 chi ∧
      Fin15AnchoredAtom4538 chi) ∨
      (Fin15AnchoredAtom2579 chi ∧
      Fin15AnchoredAtom2580 chi ∧
      Fin15AnchoredAtom2589 chi ∧
      Fin15AnchoredAtom2599 chi ∧
      Fin15AnchoredAtom2794 chi ∧
      Fin15AnchoredAtom4544 chi)) ∨
      ((Fin15AnchoredAtom2579 chi ∧
      Fin15AnchoredAtom2581 chi ∧
      Fin15AnchoredAtom2590 chi ∧
      Fin15AnchoredAtom2600 chi ∧
      Fin15AnchoredAtom2795 chi ∧
      Fin15AnchoredAtom4545 chi) ∨
      (Fin15AnchoredAtom2580 chi ∧
      Fin15AnchoredAtom2581 chi ∧
      Fin15AnchoredAtom2591 chi ∧
      Fin15AnchoredAtom2601 chi ∧
      Fin15AnchoredAtom2796 chi ∧
      Fin15AnchoredAtom4546 chi))) ∨
      (((Fin15AnchoredAtom2583 chi ∧
      Fin15AnchoredAtom2584 chi ∧
      Fin15AnchoredAtom2589 chi ∧
      Fin15AnchoredAtom2605 chi ∧
      Fin15AnchoredAtom2800 chi ∧
      Fin15AnchoredAtom4550 chi) ∨
      (Fin15AnchoredAtom2583 chi ∧
      Fin15AnchoredAtom2585 chi ∧
      Fin15AnchoredAtom2590 chi ∧
      Fin15AnchoredAtom2606 chi ∧
      Fin15AnchoredAtom2801 chi ∧
      Fin15AnchoredAtom4551 chi)) ∨
      ((Fin15AnchoredAtom2589 chi ∧
      Fin15AnchoredAtom2590 chi ∧
      Fin15AnchoredAtom2591 chi ∧
      Fin15AnchoredAtom2611 chi ∧
      Fin15AnchoredAtom2806 chi ∧
      Fin15AnchoredAtom4556 chi) ∨
      (Fin15AnchoredAtom2593 chi ∧
      Fin15AnchoredAtom2594 chi ∧
      Fin15AnchoredAtom2599 chi ∧
      Fin15AnchoredAtom2605 chi ∧
      Fin15AnchoredAtom2810 chi ∧
      Fin15AnchoredAtom4560 chi)))) ∨
      ((((Fin15AnchoredAtom2593 chi ∧
      Fin15AnchoredAtom2595 chi ∧
      Fin15AnchoredAtom2600 chi ∧
      Fin15AnchoredAtom2606 chi ∧
      Fin15AnchoredAtom2811 chi ∧
      Fin15AnchoredAtom4561 chi) ∨
      (Fin15AnchoredAtom2594 chi ∧
      Fin15AnchoredAtom2595 chi ∧
      Fin15AnchoredAtom2601 chi ∧
      Fin15AnchoredAtom2607 chi ∧
      Fin15AnchoredAtom2812 chi ∧
      Fin15AnchoredAtom4562 chi)) ∨
      ((Fin15AnchoredAtom2599 chi ∧
      Fin15AnchoredAtom2600 chi ∧
      Fin15AnchoredAtom2601 chi ∧
      Fin15AnchoredAtom2611 chi ∧
      Fin15AnchoredAtom2816 chi ∧
      Fin15AnchoredAtom4566 chi) ∨
      (Fin15AnchoredAtom2602 chi ∧
      Fin15AnchoredAtom2603 chi ∧
      Fin15AnchoredAtom2605 chi ∧
      Fin15AnchoredAtom2608 chi ∧
      Fin15AnchoredAtom2817 chi ∧
      Fin15AnchoredAtom4567 chi))) ∨
      (((Fin15AnchoredAtom2605 chi ∧
      Fin15AnchoredAtom2606 chi ∧
      Fin15AnchoredAtom2607 chi ∧
      Fin15AnchoredAtom2611 chi ∧
      Fin15AnchoredAtom2820 chi ∧
      Fin15AnchoredAtom4570 chi) ∨
      (Fin15AnchoredAtom2613 chi ∧
      Fin15AnchoredAtom2614 chi ∧
      Fin15AnchoredAtom2625 chi ∧
      Fin15AnchoredAtom2646 chi ∧
      Fin15AnchoredAtom2702 chi ∧
      Fin15AnchoredAtom4578 chi)) ∨
      ((Fin15AnchoredAtom2613 chi ∧
      Fin15AnchoredAtom2616 chi ∧
      Fin15AnchoredAtom2627 chi ∧
      Fin15AnchoredAtom2648 chi ∧
      Fin15AnchoredAtom2704 chi ∧
      Fin15AnchoredAtom4580 chi) ∨
      (Fin15AnchoredAtom2613 chi ∧
      Fin15AnchoredAtom2617 chi ∧
      Fin15AnchoredAtom2628 chi ∧
      Fin15AnchoredAtom2649 chi ∧
      Fin15AnchoredAtom2705 chi ∧
      Fin15AnchoredAtom4581 chi))))))) ∨
      (((((((Fin15AnchoredAtom2613 chi ∧
      Fin15AnchoredAtom2618 chi ∧
      Fin15AnchoredAtom2629 chi ∧
      Fin15AnchoredAtom2650 chi ∧
      Fin15AnchoredAtom2706 chi ∧
      Fin15AnchoredAtom4582 chi) ∨
      (Fin15AnchoredAtom2614 chi ∧
      Fin15AnchoredAtom2615 chi ∧
      Fin15AnchoredAtom2630 chi ∧
      Fin15AnchoredAtom2651 chi ∧
      Fin15AnchoredAtom2707 chi ∧
      Fin15AnchoredAtom4583 chi)) ∨
      ((Fin15AnchoredAtom2614 chi ∧
      Fin15AnchoredAtom2616 chi ∧
      Fin15AnchoredAtom2631 chi ∧
      Fin15AnchoredAtom2652 chi ∧
      Fin15AnchoredAtom2708 chi ∧
      Fin15AnchoredAtom4584 chi) ∨
      (Fin15AnchoredAtom2614 chi ∧
      Fin15AnchoredAtom2617 chi ∧
      Fin15AnchoredAtom2632 chi ∧
      Fin15AnchoredAtom2653 chi ∧
      Fin15AnchoredAtom2709 chi ∧
      Fin15AnchoredAtom4585 chi))) ∨
      (((Fin15AnchoredAtom2614 chi ∧
      Fin15AnchoredAtom2618 chi ∧
      Fin15AnchoredAtom2633 chi ∧
      Fin15AnchoredAtom2654 chi ∧
      Fin15AnchoredAtom2710 chi ∧
      Fin15AnchoredAtom4586 chi) ∨
      (Fin15AnchoredAtom2615 chi ∧
      Fin15AnchoredAtom2617 chi ∧
      Fin15AnchoredAtom2635 chi ∧
      Fin15AnchoredAtom2656 chi ∧
      Fin15AnchoredAtom2712 chi ∧
      Fin15AnchoredAtom4588 chi)) ∨
      ((Fin15AnchoredAtom2616 chi ∧
      Fin15AnchoredAtom2617 chi ∧
      Fin15AnchoredAtom2637 chi ∧
      Fin15AnchoredAtom2658 chi ∧
      Fin15AnchoredAtom2714 chi ∧
      Fin15AnchoredAtom4590 chi) ∨
      (Fin15AnchoredAtom2616 chi ∧
      Fin15AnchoredAtom2618 chi ∧
      Fin15AnchoredAtom2638 chi ∧
      Fin15AnchoredAtom2659 chi ∧
      Fin15AnchoredAtom2715 chi ∧
      Fin15AnchoredAtom4591 chi)))) ∨
      ((((Fin15AnchoredAtom2617 chi ∧
      Fin15AnchoredAtom2618 chi ∧
      Fin15AnchoredAtom2639 chi ∧
      Fin15AnchoredAtom2660 chi ∧
      Fin15AnchoredAtom2716 chi ∧
      Fin15AnchoredAtom4592 chi) ∨
      (Fin15AnchoredAtom2619 chi ∧
      Fin15AnchoredAtom2624 chi ∧
      Fin15AnchoredAtom2629 chi ∧
      Fin15AnchoredAtom2665 chi ∧
      Fin15AnchoredAtom2721 chi ∧
      Fin15AnchoredAtom4597 chi)) ∨
      ((Fin15AnchoredAtom2620 chi ∧
      Fin15AnchoredAtom2623 chi ∧
      Fin15AnchoredAtom2632 chi ∧
      Fin15AnchoredAtom2668 chi ∧
      Fin15AnchoredAtom2724 chi ∧
      Fin15AnchoredAtom4600 chi) ∨
      (Fin15AnchoredAtom2622 chi ∧
      Fin15AnchoredAtom2624 chi ∧
      Fin15AnchoredAtom2638 chi ∧
      Fin15AnchoredAtom2674 chi ∧
      Fin15AnchoredAtom2730 chi ∧
      Fin15AnchoredAtom4606 chi))) ∨
      (((Fin15AnchoredAtom2623 chi ∧
      Fin15AnchoredAtom2624 chi ∧
      Fin15AnchoredAtom2639 chi ∧
      Fin15AnchoredAtom2675 chi ∧
      Fin15AnchoredAtom2731 chi ∧
      Fin15AnchoredAtom4607 chi) ∨
      (Fin15AnchoredAtom2625 chi ∧
      Fin15AnchoredAtom2627 chi ∧
      Fin15AnchoredAtom2631 chi ∧
      Fin15AnchoredAtom2677 chi ∧
      Fin15AnchoredAtom2733 chi ∧
      Fin15AnchoredAtom4609 chi)) ∨
      ((Fin15AnchoredAtom2625 chi ∧
      Fin15AnchoredAtom2628 chi ∧
      Fin15AnchoredAtom2632 chi ∧
      Fin15AnchoredAtom2678 chi ∧
      Fin15AnchoredAtom2734 chi ∧
      Fin15AnchoredAtom4610 chi) ∨
      (Fin15AnchoredAtom2625 chi ∧
      Fin15AnchoredAtom2629 chi ∧
      Fin15AnchoredAtom2633 chi ∧
      Fin15AnchoredAtom2679 chi ∧
      Fin15AnchoredAtom2735 chi ∧
      Fin15AnchoredAtom4611 chi))))) ∨
      (((((Fin15AnchoredAtom2626 chi ∧
      Fin15AnchoredAtom2627 chi ∧
      Fin15AnchoredAtom2634 chi ∧
      Fin15AnchoredAtom2680 chi ∧
      Fin15AnchoredAtom2736 chi ∧
      Fin15AnchoredAtom4612 chi) ∨
      (Fin15AnchoredAtom2627 chi ∧
      Fin15AnchoredAtom2628 chi ∧
      Fin15AnchoredAtom2637 chi ∧
      Fin15AnchoredAtom2683 chi ∧
      Fin15AnchoredAtom2739 chi ∧
      Fin15AnchoredAtom4615 chi)) ∨
      ((Fin15AnchoredAtom2627 chi ∧
      Fin15AnchoredAtom2629 chi ∧
      Fin15AnchoredAtom2638 chi ∧
      Fin15AnchoredAtom2684 chi ∧
      Fin15AnchoredAtom2740 chi ∧
      Fin15AnchoredAtom4616 chi) ∨
      (Fin15AnchoredAtom2628 chi ∧
      Fin15AnchoredAtom2629 chi ∧
      Fin15AnchoredAtom2639 chi ∧
      Fin15AnchoredAtom2685 chi ∧
      Fin15AnchoredAtom2741 chi ∧
      Fin15AnchoredAtom4617 chi))) ∨
      (((Fin15AnchoredAtom2630 chi ∧
      Fin15AnchoredAtom2631 chi ∧
      Fin15AnchoredAtom2634 chi ∧
      Fin15AnchoredAtom2686 chi ∧
      Fin15AnchoredAtom2742 chi ∧
      Fin15AnchoredAtom4618 chi) ∨
      (Fin15AnchoredAtom2630 chi ∧
      Fin15AnchoredAtom2633 chi ∧
      Fin15AnchoredAtom2636 chi ∧
      Fin15AnchoredAtom2688 chi ∧
      Fin15AnchoredAtom2744 chi ∧
      Fin15AnchoredAtom4620 chi)) ∨
      ((Fin15AnchoredAtom2631 chi ∧
      Fin15AnchoredAtom2632 chi ∧
      Fin15AnchoredAtom2637 chi ∧
      Fin15AnchoredAtom2689 chi ∧
      Fin15AnchoredAtom2745 chi ∧
      Fin15AnchoredAtom4621 chi) ∨
      (Fin15AnchoredAtom2631 chi ∧
      Fin15AnchoredAtom2633 chi ∧
      Fin15AnchoredAtom2638 chi ∧
      Fin15AnchoredAtom2690 chi ∧
      Fin15AnchoredAtom2746 chi ∧
      Fin15AnchoredAtom4622 chi)))) ∨
      ((((Fin15AnchoredAtom2632 chi ∧
      Fin15AnchoredAtom2633 chi ∧
      Fin15AnchoredAtom2639 chi ∧
      Fin15AnchoredAtom2691 chi ∧
      Fin15AnchoredAtom2747 chi ∧
      Fin15AnchoredAtom4623 chi) ∨
      (Fin15AnchoredAtom2637 chi ∧
      Fin15AnchoredAtom2638 chi ∧
      Fin15AnchoredAtom2639 chi ∧
      Fin15AnchoredAtom2695 chi ∧
      Fin15AnchoredAtom2751 chi ∧
      Fin15AnchoredAtom4627 chi)) ∨
      ((Fin15AnchoredAtom2640 chi ∧
      Fin15AnchoredAtom2641 chi ∧
      Fin15AnchoredAtom2646 chi ∧
      Fin15AnchoredAtom2661 chi ∧
      Fin15AnchoredAtom2752 chi ∧
      Fin15AnchoredAtom4628 chi) ∨
      (Fin15AnchoredAtom2640 chi ∧
      Fin15AnchoredAtom2643 chi ∧
      Fin15AnchoredAtom2648 chi ∧
      Fin15AnchoredAtom2663 chi ∧
      Fin15AnchoredAtom2754 chi ∧
      Fin15AnchoredAtom4630 chi))) ∨
      (((Fin15AnchoredAtom2640 chi ∧
      Fin15AnchoredAtom2644 chi ∧
      Fin15AnchoredAtom2649 chi ∧
      Fin15AnchoredAtom2664 chi ∧
      Fin15AnchoredAtom2755 chi ∧
      Fin15AnchoredAtom4631 chi) ∨
      (Fin15AnchoredAtom2640 chi ∧
      Fin15AnchoredAtom2645 chi ∧
      Fin15AnchoredAtom2650 chi ∧
      Fin15AnchoredAtom2665 chi ∧
      Fin15AnchoredAtom2756 chi ∧
      Fin15AnchoredAtom4632 chi)) ∨
      ((Fin15AnchoredAtom2643 chi ∧
      Fin15AnchoredAtom2644 chi ∧
      Fin15AnchoredAtom2658 chi ∧
      Fin15AnchoredAtom2673 chi ∧
      Fin15AnchoredAtom2764 chi ∧
      Fin15AnchoredAtom4640 chi) ∨
      (Fin15AnchoredAtom2643 chi ∧
      Fin15AnchoredAtom2645 chi ∧
      Fin15AnchoredAtom2659 chi ∧
      Fin15AnchoredAtom2674 chi ∧
      Fin15AnchoredAtom2765 chi ∧
      Fin15AnchoredAtom4641 chi)))))) ∨
      ((((((Fin15AnchoredAtom2644 chi ∧
      Fin15AnchoredAtom2645 chi ∧
      Fin15AnchoredAtom2660 chi ∧
      Fin15AnchoredAtom2675 chi ∧
      Fin15AnchoredAtom2766 chi ∧
      Fin15AnchoredAtom4642 chi) ∨
      (Fin15AnchoredAtom2646 chi ∧
      Fin15AnchoredAtom2648 chi ∧
      Fin15AnchoredAtom2652 chi ∧
      Fin15AnchoredAtom2677 chi ∧
      Fin15AnchoredAtom2768 chi ∧
      Fin15AnchoredAtom4644 chi)) ∨
      ((Fin15AnchoredAtom2646 chi ∧
      Fin15AnchoredAtom2649 chi ∧
      Fin15AnchoredAtom2653 chi ∧
      Fin15AnchoredAtom2678 chi ∧
      Fin15AnchoredAtom2769 chi ∧
      Fin15AnchoredAtom4645 chi) ∨
      (Fin15AnchoredAtom2646 chi ∧
      Fin15AnchoredAtom2650 chi ∧
      Fin15AnchoredAtom2654 chi ∧
      Fin15AnchoredAtom2679 chi ∧
      Fin15AnchoredAtom2770 chi ∧
      Fin15AnchoredAtom4646 chi))) ∨
      (((Fin15AnchoredAtom2648 chi ∧
      Fin15AnchoredAtom2649 chi ∧
      Fin15AnchoredAtom2658 chi ∧
      Fin15AnchoredAtom2683 chi ∧
      Fin15AnchoredAtom2774 chi ∧
      Fin15AnchoredAtom4650 chi) ∨
      (Fin15AnchoredAtom2648 chi ∧
      Fin15AnchoredAtom2650 chi ∧
      Fin15AnchoredAtom2659 chi ∧
      Fin15AnchoredAtom2684 chi ∧
      Fin15AnchoredAtom2775 chi ∧
      Fin15AnchoredAtom4651 chi)) ∨
      ((Fin15AnchoredAtom2649 chi ∧
      Fin15AnchoredAtom2650 chi ∧
      Fin15AnchoredAtom2660 chi ∧
      Fin15AnchoredAtom2685 chi ∧
      Fin15AnchoredAtom2776 chi ∧
      Fin15AnchoredAtom4652 chi) ∨
      (Fin15AnchoredAtom2651 chi ∧
      Fin15AnchoredAtom2652 chi ∧
      Fin15AnchoredAtom2655 chi ∧
      Fin15AnchoredAtom2686 chi ∧
      Fin15AnchoredAtom2777 chi ∧
      Fin15AnchoredAtom4653 chi)))) ∨
      ((((Fin15AnchoredAtom2651 chi ∧
      Fin15AnchoredAtom2653 chi ∧
      Fin15AnchoredAtom2656 chi ∧
      Fin15AnchoredAtom2687 chi ∧
      Fin15AnchoredAtom2778 chi ∧
      Fin15AnchoredAtom4654 chi) ∨
      (Fin15AnchoredAtom2652 chi ∧
      Fin15AnchoredAtom2653 chi ∧
      Fin15AnchoredAtom2658 chi ∧
      Fin15AnchoredAtom2689 chi ∧
      Fin15AnchoredAtom2780 chi ∧
      Fin15AnchoredAtom4656 chi)) ∨
      ((Fin15AnchoredAtom2652 chi ∧
      Fin15AnchoredAtom2654 chi ∧
      Fin15AnchoredAtom2659 chi ∧
      Fin15AnchoredAtom2690 chi ∧
      Fin15AnchoredAtom2781 chi ∧
      Fin15AnchoredAtom4657 chi) ∨
      (Fin15AnchoredAtom2653 chi ∧
      Fin15AnchoredAtom2654 chi ∧
      Fin15AnchoredAtom2660 chi ∧
      Fin15AnchoredAtom2691 chi ∧
      Fin15AnchoredAtom2782 chi ∧
      Fin15AnchoredAtom4658 chi))) ∨
      (((Fin15AnchoredAtom2658 chi ∧
      Fin15AnchoredAtom2659 chi ∧
      Fin15AnchoredAtom2660 chi ∧
      Fin15AnchoredAtom2695 chi ∧
      Fin15AnchoredAtom2786 chi ∧
      Fin15AnchoredAtom4662 chi) ∨
      (Fin15AnchoredAtom2661 chi ∧
      Fin15AnchoredAtom2663 chi ∧
      Fin15AnchoredAtom2667 chi ∧
      Fin15AnchoredAtom2677 chi ∧
      Fin15AnchoredAtom2788 chi ∧
      Fin15AnchoredAtom4664 chi)) ∨
      ((Fin15AnchoredAtom2663 chi ∧
      Fin15AnchoredAtom2664 chi ∧
      Fin15AnchoredAtom2673 chi ∧
      Fin15AnchoredAtom2683 chi ∧
      Fin15AnchoredAtom2794 chi ∧
      Fin15AnchoredAtom4670 chi) ∨
      (Fin15AnchoredAtom2663 chi ∧
      Fin15AnchoredAtom2665 chi ∧
      Fin15AnchoredAtom2674 chi ∧
      Fin15AnchoredAtom2684 chi ∧
      Fin15AnchoredAtom2795 chi ∧
      Fin15AnchoredAtom4671 chi))))) ∨
      (((((Fin15AnchoredAtom2664 chi ∧
      Fin15AnchoredAtom2665 chi ∧
      Fin15AnchoredAtom2675 chi ∧
      Fin15AnchoredAtom2685 chi ∧
      Fin15AnchoredAtom2796 chi ∧
      Fin15AnchoredAtom4672 chi) ∨
      (Fin15AnchoredAtom2667 chi ∧
      Fin15AnchoredAtom2669 chi ∧
      Fin15AnchoredAtom2674 chi ∧
      Fin15AnchoredAtom2690 chi ∧
      Fin15AnchoredAtom2801 chi ∧
      Fin15AnchoredAtom4677 chi)) ∨
      ((Fin15AnchoredAtom2668 chi ∧
      Fin15AnchoredAtom2669 chi ∧
      Fin15AnchoredAtom2675 chi ∧
      Fin15AnchoredAtom2691 chi ∧
      Fin15AnchoredAtom2802 chi ∧
      Fin15AnchoredAtom4678 chi) ∨
      (Fin15AnchoredAtom2673 chi ∧
      Fin15AnchoredAtom2674 chi ∧
      Fin15AnchoredAtom2675 chi ∧
      Fin15AnchoredAtom2695 chi ∧
      Fin15AnchoredAtom2806 chi ∧
      Fin15AnchoredAtom4682 chi))) ∨
      (((Fin15AnchoredAtom2677 chi ∧
      Fin15AnchoredAtom2678 chi ∧
      Fin15AnchoredAtom2683 chi ∧
      Fin15AnchoredAtom2689 chi ∧
      Fin15AnchoredAtom2810 chi ∧
      Fin15AnchoredAtom4686 chi) ∨
      (Fin15AnchoredAtom2677 chi ∧
      Fin15AnchoredAtom2679 chi ∧
      Fin15AnchoredAtom2684 chi ∧
      Fin15AnchoredAtom2690 chi ∧
      Fin15AnchoredAtom2811 chi ∧
      Fin15AnchoredAtom4687 chi)) ∨
      ((Fin15AnchoredAtom2678 chi ∧
      Fin15AnchoredAtom2679 chi ∧
      Fin15AnchoredAtom2685 chi ∧
      Fin15AnchoredAtom2691 chi ∧
      Fin15AnchoredAtom2812 chi ∧
      Fin15AnchoredAtom4688 chi) ∨
      (Fin15AnchoredAtom2683 chi ∧
      Fin15AnchoredAtom2684 chi ∧
      Fin15AnchoredAtom2685 chi ∧
      Fin15AnchoredAtom2695 chi ∧
      Fin15AnchoredAtom2816 chi ∧
      Fin15AnchoredAtom4692 chi)))) ∨
      ((((Fin15AnchoredAtom2689 chi ∧
      Fin15AnchoredAtom2690 chi ∧
      Fin15AnchoredAtom2691 chi ∧
      Fin15AnchoredAtom2695 chi ∧
      Fin15AnchoredAtom2820 chi ∧
      Fin15AnchoredAtom4696 chi) ∨
      (Fin15AnchoredAtom2696 chi ∧
      Fin15AnchoredAtom2697 chi ∧
      Fin15AnchoredAtom2702 chi ∧
      Fin15AnchoredAtom2717 chi ∧
      Fin15AnchoredAtom2752 chi ∧
      Fin15AnchoredAtom4698 chi)) ∨
      ((Fin15AnchoredAtom2696 chi ∧
      Fin15AnchoredAtom2700 chi ∧
      Fin15AnchoredAtom2705 chi ∧
      Fin15AnchoredAtom2720 chi ∧
      Fin15AnchoredAtom2755 chi ∧
      Fin15AnchoredAtom4701 chi) ∨
      (Fin15AnchoredAtom2696 chi ∧
      Fin15AnchoredAtom2701 chi ∧
      Fin15AnchoredAtom2706 chi ∧
      Fin15AnchoredAtom2721 chi ∧
      Fin15AnchoredAtom2756 chi ∧
      Fin15AnchoredAtom4702 chi))) ∨
      (((Fin15AnchoredAtom2697 chi ∧
      Fin15AnchoredAtom2699 chi ∧
      Fin15AnchoredAtom2708 chi ∧
      Fin15AnchoredAtom2723 chi ∧
      Fin15AnchoredAtom2758 chi ∧
      Fin15AnchoredAtom4704 chi) ∨
      (Fin15AnchoredAtom2697 chi ∧
      Fin15AnchoredAtom2701 chi ∧
      Fin15AnchoredAtom2710 chi ∧
      Fin15AnchoredAtom2725 chi ∧
      Fin15AnchoredAtom2760 chi ∧
      Fin15AnchoredAtom4706 chi)) ∨
      ((Fin15AnchoredAtom2700 chi ∧
      Fin15AnchoredAtom2701 chi ∧
      Fin15AnchoredAtom2716 chi ∧
      Fin15AnchoredAtom2731 chi ∧
      Fin15AnchoredAtom2766 chi ∧
      Fin15AnchoredAtom4712 chi) ∨
      (Fin15AnchoredAtom2702 chi ∧
      Fin15AnchoredAtom2704 chi ∧
      Fin15AnchoredAtom2708 chi ∧
      Fin15AnchoredAtom2733 chi ∧
      Fin15AnchoredAtom2768 chi ∧
      Fin15AnchoredAtom4714 chi)))))))))) := by
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
                exact fin15Anchored_clause29026 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29027 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29028 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29029 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29030 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29031 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29032 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29033 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29034 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29035 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29036 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29037 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29038 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29039 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29040 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29041 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29042 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29043 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29044 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29045 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29046 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29047 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29048 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29049 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29050 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29051 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29052 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29053 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29054 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29055 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29056 chi hnoStrong hbad
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
                  exact fin15Anchored_clause29057 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29058 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29059 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29060 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29061 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29062 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29063 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29064 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29065 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29066 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29067 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29068 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29069 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29070 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29071 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29072 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29073 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29074 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29075 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29076 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29077 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29078 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29079 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29080 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29081 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29082 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29083 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29084 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29085 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29086 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29087 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29088 chi hnoStrong hbad
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
                exact fin15Anchored_clause29089 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29090 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29091 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29092 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29093 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29094 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29095 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29096 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29097 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29098 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29099 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29100 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29101 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29102 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29103 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29104 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29105 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29106 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29107 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29108 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29109 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29110 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29111 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29112 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29113 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29114 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29115 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29116 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29117 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29118 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29119 chi hnoStrong hbad
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
                  exact fin15Anchored_clause29120 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29121 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29122 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29123 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29124 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29125 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29126 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29127 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29128 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29129 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29130 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29131 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29132 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29133 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29134 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29135 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29136 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29137 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29138 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29139 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29140 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29141 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29142 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29143 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29144 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29145 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29146 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29147 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29148 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29149 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29150 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29151 chi hnoStrong hbad
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
                exact fin15Anchored_clause29152 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29153 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29154 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29155 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29156 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29157 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29158 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29159 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29160 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29161 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29162 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29163 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29164 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29165 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29166 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29167 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29168 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29169 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29170 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29171 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29172 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29173 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29174 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29175 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29176 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29177 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29178 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29179 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29180 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29181 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29182 chi hnoStrong hbad
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
                  exact fin15Anchored_clause29183 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29184 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29185 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29186 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29187 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29188 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29189 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29190 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29191 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29192 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29193 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29194 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29195 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29196 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29197 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29198 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29199 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29200 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29201 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29202 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29203 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29204 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29205 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29206 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29207 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29208 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29209 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29210 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29211 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29212 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29213 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29214 chi hnoStrong hbad
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
                  exact fin15Anchored_clause29215 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29216 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29217 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29218 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29219 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29220 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29221 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29222 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29223 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29224 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29225 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29226 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29227 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29228 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29229 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29230 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29231 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29232 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29233 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29234 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29235 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29236 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29237 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29238 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29239 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29240 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29241 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29242 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29243 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29244 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29245 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29246 chi hnoStrong hbad
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
                  exact fin15Anchored_clause29247 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29248 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29249 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29250 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29251 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29252 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29253 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29254 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29255 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29256 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29257 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29258 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29259 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29260 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29261 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29262 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29263 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29264 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29265 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29266 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29267 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29268 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29269 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29270 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29271 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29272 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29273 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29274 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29275 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29276 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29277 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29278 chi hnoStrong hbad

end ErdosSzekeres

end
