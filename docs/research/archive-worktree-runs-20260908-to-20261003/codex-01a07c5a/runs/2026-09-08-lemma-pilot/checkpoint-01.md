Timed proof pilot checkpoint 1

Time: 2026-09-08T20:23:43.688474+00:00

Checked and remotely verified pilot theorem commits: 7

Compiled index counts: {'closed': 50, 'open': 11, 'claimed': 1, 'refuted': 1}

Stale index reasons: ['index is stale: 1 node(s) in statements.lock are not indexed (ctx_unit_axis_active_region_potential); run `es extract`']

Current work: {'node': 'ctx_unit_axis_active_region_potential', 'consumer': 'ctx_bound_le_numRuns_of_unit_axis_limit', 'state': 'Stronger theorem and corollary checked, committed and pushed; claim released closed. Full index refresh running before next selection.', 'registration_script': 'register_unit_axis_potential.py', 'proof_plan': 'unit-axis-next-plan.md', 'registration_job': '20260908-161549-934a5d', 'type_hash': 'c88df2f35ee32c75', 'branch': 'node/ctx_unit_axis_active_region_potential', 'file': 'ESBlueprint/B/CtxUnitAxisActiveRegionPotential.lean', 'claim_verified': True, 'check_job': '20260908-161719-18efc2', 'check_artifact': 'unit-axis-potential-check.json', 'corollary_check_artifact': 'unit-axis-corollary-check.json', 'latest_published_commit': 'abf32d88edcc026b0dcca117fd3d39edfc4e67b4', 'refresh_job': '20260908-162003-7e875c', 'exploratory_probe_job': '20260908-162137-540d78'}

The unrestricted singleton-end sandwich theorem remains open. Current reusable estimates cover unit capacities and normalized histories; higher-capacity outer-run comparisons still require proof.

Resource policy:30GiB shared budget,28GiB full extractor cap,3GiB proof checks,1GiB finite-probe shards.

Proof commits:

- ctx_reverse_extension_transport: a91a23691b9f15bcf831e472a02ae678e88c2c69

- ctx_single_run_part_limits_exact: 601f5c1f2400065f73786843ad9f411a8b3d3e9f

- ctx_single_run_descendant_limits_normalize: 9523c014bb3617d747e8a5e7292387b655cf7773

- ctx_single_run_descendant_bound_normalize: 748ad6e4f02c52227f0af3e527b7ba91b546b7e1

- ctx_part_capacity_drop_in_clear_interval: 1e9321d8de83d3208b12677c1db3ac22025e48d2

- ctx_bound_le_numRuns_of_unit_axis_limit: ba0b6b82a2da47943f6122d4d62d866738decda6

- ctx_unit_axis_active_region_potential: abf32d88edcc026b0dcca117fd3d39edfc4e67b4
