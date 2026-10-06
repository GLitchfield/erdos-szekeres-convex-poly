Timed proof pilot checkpoint 2

Time: 2026-09-08T22:23:19.760622+00:00

Checked and remotely verified pilot theorem commits: 16

Compiled index counts: {'closed': 59, 'open': 11, 'claimed': 1, 'refuted': 1}

Stale index reasons: ['index is stale: 1 node(s) in statements.lock are not indexed (ctx_bound_additive_near_saturated_interval_complement); run `es extract`']

Current work: {'node': 'ctx_bound_additive_near_saturated_interval_complement', 'consumer': 'ctx_bound_additive_sandwich_one_singleton_end', 'state': 'Proof16 pushed; full index refresh running. Exploring capacity-three outer bounds under parent claim.', 'registration_script': 'register_near_saturated.py', 'registration_job': '20260908-181805-f7a856', 'type_hash': '81e27fa5ac515155', 'current_job': '20260908-182300-9e18fa', 'last_successful_build': '20260908-182020-f064d4', 'last_successful_build_artifact': 'near-saturated-build-2.json', 'check': 'near-saturated-check.json', 'check_job': '20260908-182113-11835e', 'commit': '8a19b1447e89352a3c0545412c4cf124a6bee5b1', 'pushed': True, 'downstream_plan': 'capacity-three-gap-next-research.md'}

The unrestricted singleton-end sandwich theorem remains open. Verified estimates include ancestor and indexed-sibling normalization, unit/rank-region potentials, and both orientations of arbitrary-disjoint single-run additivity when either ancestor capacity is at most two. The unrestricted comparison with both capacities at least three still requires proof.

Resource policy:30GiB shared budget,28GiB full extractor cap,3GiB proof checks,1GiB finite-probe shards.

Proof commits:

- ctx_reverse_extension_transport: a91a23691b9f15bcf831e472a02ae678e88c2c69

- ctx_single_run_part_limits_exact: 601f5c1f2400065f73786843ad9f411a8b3d3e9f

- ctx_single_run_descendant_limits_normalize: 9523c014bb3617d747e8a5e7292387b655cf7773

- ctx_single_run_descendant_bound_normalize: 748ad6e4f02c52227f0af3e527b7ba91b546b7e1

- ctx_part_capacity_drop_in_clear_interval: 1e9321d8de83d3208b12677c1db3ac22025e48d2

- ctx_bound_le_numRuns_of_unit_axis_limit: ba0b6b82a2da47943f6122d4d62d866738decda6

- ctx_unit_axis_active_region_potential: abf32d88edcc026b0dcca117fd3d39edfc4e67b4

- ctx_bound_le_one_of_large_sibling_maximum: 7a84da04da07113fc0a52b4d40ab578470f93cf9

- ctx_bound_additive_saturated_interval_complement: ca0ba576fe1001cc73fe02ad77d4d7ab568704bb

- ctx_bound_le_one_of_clear_unit_axis: fd297977d57572e15358b73ecc57c27f905c02a2

- ctx_bound_additive_interval_complement_small_outer_axis: 7f360a55fe9ea497bffafaacc52a1ea063d9cee4

- ctx_unit_axis_region_potential_additive: 8ff0c30841724b413ca0d5a1725c24106f5a8266

- ctx_small_global_axis_rank_region_potential: 072151cf6ce3f0254aceed3bc35634709ce4a4a3

- ctx_bound_additive_disjoint_single_run_small_axis: c8d3344942f8994526b1f2612ad2714bce76f48f

- ctx_sibling_maximum_upper_normalize: ce19bac7267a6ae56b2f7d0adc6e67942b674769

- ctx_bound_additive_near_saturated_interval_complement: 8a19b1447e89352a3c0545412c4cf124a6bee5b1
