Timed proof pilot checkpoint 3

Time: 2026-09-09T00:23:31.357564+00:00

Checked and remotely verified pilot theorem commits: 24

Compiled index counts: {'closed': 67, 'open': 11, 'claimed': 1, 'refuted': 1}

Stale index reasons: ['index is stale: 1 node(s) in statements.lock are not indexed (ctx_boundary_marker_full_rank_budget); run `es extract`']

Current work: {'node': 'ctx_boundary_marker_full_rank_budget', 'stage': 'proof checked and pushed, refreshing index', 'commit': '89ab270642323c32d57ebc22c573a39d3bf4ebdc', 'proof_plan': 'boundary-full-rank-plan.md', 'job': '20260908-202241-30d335'}

The unrestricted singleton-end sandwich theorem remains open. Verified ingredients include descendant and history normalization, unit/rank-region potentials, arbitrary-disjoint single-run additivity when either ancestor capacity is at most two, the near-saturated outer-maximum band, and boundary estimates preserving older opposite-axis history. The remaining outer-block comparison with both capacities at least three outside the proved band still requires proof.

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

- ctx_erase_level_bound_mono: 8736821ca1879e97382c769ae22b56166d0d3e37

- ctx_boundary_marker_upper_normalize: 14f27a01d63ade8ec4f6714dc3e5634d1d50c415

- ctx_boundary_marker_rank_budget: d00f37d020932ecb816bf80ad3b6f6feb8bc5394

- ctx_one_sided_part_boundary_budget: d6ef86afdb569a2fadc37890a0d62bb0544c2efe

- ctx_bound_mono_of_marker_inclusion: d21ef6f6c6ddfd8754fb21874c1119c3abe9a34a

- ctx_straddling_removed_marker_unit: a92b960dae4a7c0955ea85e22db2b7eea1956c2b

- ctx_boundary_marker_erase_normalize: 95cf5c3a7923c6d0e4532ab2a82a111327264613

- ctx_boundary_marker_full_rank_budget: 89ab270642323c32d57ebc22c573a39d3bf4ebdc
