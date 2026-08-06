PROJECT_TOOL_BIN := $(CURDIR)/scripts/toolchain
export PATH := $(PROJECT_TOOL_BIN):$(PATH)

.PHONY: check update lean test test-exhaustive wayfinder review-doctor

check:
	@python3 --version
	@git --version
	@lake --version

update: check
	@lake update

lean:
	@! rg -n --glob '*.lean' '\b(sorry|admit)\b' ErdosSzekeres ErdosSzekeres.lean
	@lake build

test: check lean
	@python3 -m unittest discover -s scripts -p 'test_*.py'
	@python3 scripts/check_e3_state455_aggregation.py
	@python3 scripts/check_e3_state566_aggregation.py
	@python3 scripts/check_decomposable_context_collision.py \
		data/derived/e3-context-k6-n9-singleton-collision.json >/dev/null
	@python3 scripts/check_decomposable_rank_profiles.py \
		data/derived/e3-rank-k6-n9-singleton.json >/dev/null
	@python3 scripts/check_incoming_star_prefixes.py \
		data/derived/e3-incoming-star-prefix-k6-n8.json >/dev/null
	@python3 scripts/check_singleton_residuals.py \
		data/derived/e3-singleton-residual-k6-n9.json --workers 8 >/dev/null
	@python3 scripts/check_span_rank_footprints.py \
		data/derived/e3-span-rank-footprint-k6-n9.json --workers 8 >/dev/null
	@python3 scripts/check_two_root_span_footprints.py \
		data/derived/e3-two-root-span-k6-n9.json --workers 8 >/dev/null
	@python3 scripts/check_span_dominance_quotients.py \
		data/derived/e3-span-dominance-quotient-k6-n9.json --source-only >/dev/null
	@python3 scripts/check_large_span_dominance_quotient.py \
		data/derived/e3-span-dominance-quotient-k6-n10.json --source-only >/dev/null
	@python3 scripts/check_rooted_span_interfaces.py \
		data/derived/e3-rooted-span-interface-k6-n10.json --source-only >/dev/null
	@python3 scripts/check_allocated_span_pascal_demand.py \
		data/derived/e3-allocated-span-pascal-demand-k6-n8.json --source-only >/dev/null
	@python3 scripts/check_reflected_transition_hall.py \
		data/derived/e3-reflected-transition-hall-k6-n8.json --source-only >/dev/null
	@python3 scripts/replay_active_reflected_representative.py \
		data/derived/e3-active-reflected-representative-counterexample-k6-n8.json >/dev/null
	@python3 scripts/check_active_reflected_transition_hall.py \
		data/derived/e3-active-reflected-transition-hall-k6-n8.json >/dev/null
	@python3 scripts/replay_actual_ray_event_pairs.py \
		data/derived/e3-actual-ray-event-pair-frozen-n12-k7.json >/dev/null
	@python3 scripts/replay_coarse_ray_event_matrix.py \
		data/derived/e3-coarse-ray-event-matrix-frozen-n12-k7.json >/dev/null
	@python3 scripts/replay_reflected_endpoint_incidence_matrix.py \
		data/derived/e3-reflected-endpoint-incidence-matrix-frozen-n12-k7.json >/dev/null
	@python3 scripts/replay_two_lane_adjacent_uncrossing.py \
		data/derived/e3-two-lane-adjacent-uncrossing-frozen-n12-k7.json >/dev/null
	@python3 scripts/check_structural_charging_countercontrols.py >/dev/null
	@python3 scripts/check_crossing_separated_caps.py >/dev/null
	@python3 scripts/check_published_offwindow.py >/dev/null
	@python3 scripts/check_rank_profile_realization.py >/dev/null
	@python3 scripts/check_agent_orchestration.py >/dev/null
	@python3 scripts/wayfinder_status.py >/dev/null
	@python3 -m py_compile scripts/adversarial_review.py \
		scripts/analyze_cap_failure_charge_matching.py \
		scripts/analyze_packed_escape_sharp_models.py \
		scripts/search_middle_bridge_realization.py \
		scripts/analyze_decomposable_rank_profiles.py \
		scripts/analyze_lrat_checkpoints.py \
		scripts/analyze_packed_escape_lrat_core.py \
		scripts/analyze_middle_split_failure_classes.py \
		scripts/analyze_two_probe_bridge_compatibility.py \
		scripts/check_agent_orchestration.py \
		scripts/check_e3_state455_aggregation.py \
		scripts/check_e3_state566_aggregation.py \
		scripts/check_decomposable_contexts.py \
		scripts/check_decomposable_context_collision.py \
		scripts/check_decomposable_rank_profiles.py \
		scripts/check_incoming_star_prefixes.py \
		scripts/check_singleton_residuals.py \
		scripts/check_span_rank_footprints.py \
		scripts/check_span_dominance_quotients.py \
		scripts/check_large_span_dominance_quotient.py \
		scripts/check_rooted_span_interfaces.py \
		scripts/check_allocated_span_pascal_demand.py \
		scripts/check_reflected_transition_hall.py \
		scripts/check_active_reflected_representative.py \
		scripts/replay_active_reflected_representative.py \
		scripts/enumerate_active_reflected_transition_hall.py \
		scripts/check_active_reflected_transition_hall.py \
		scripts/check_actual_ray_event_pairs.py \
		scripts/replay_actual_ray_event_pairs.py \
		scripts/check_coarse_ray_event_matrix.py \
		scripts/replay_coarse_ray_event_matrix.py \
		scripts/check_reflected_endpoint_incidence_matrix.py \
		scripts/replay_reflected_endpoint_incidence_matrix.py \
		scripts/check_two_lane_adjacent_uncrossing.py \
		scripts/replay_two_lane_adjacent_uncrossing.py \
		scripts/check_two_root_span_footprints.py \
		scripts/check_crossing_separated_caps.py \
		scripts/check_middle_split_bridge_routes.py \
		scripts/check_middle_split_pair.py \
		scripts/check_packed_middle_escape.py \
		scripts/check_strong_cup_blocks.py \
		scripts/check_two_cap_free_sides.py \
		scripts/check_two_cap_free_sides_middle.py \
		scripts/check_two_cap_free_sides_witness.py \
		scripts/check_witness_profile_collision.py \
		scripts/check_published_offwindow.py \
		scripts/check_structural_charging_countercontrols.py \
		scripts/check_rank_profile_realization.py \
		scripts/check_repeated_residue_fibers.py \
		scripts/check_decomposable_enumeration.py \
		scripts/check_signotope_state_witness.py \
		scripts/enumerate_decomposable_colorings.py \
		scripts/enumerate_decomposable_contexts.py \
		scripts/enumerate_published_offwindow.py \
		scripts/enumerate_incoming_star_prefixes.py \
		scripts/enumerate_singleton_residuals.py \
		scripts/enumerate_span_rank_footprints.py \
		scripts/enumerate_span_dominance_quotients.py \
		scripts/enumerate_large_span_dominance_quotient.py \
		scripts/enumerate_rooted_span_interfaces.py \
		scripts/enumerate_allocated_span_pascal_demand.py \
		scripts/enumerate_reflected_transition_hall.py \
		scripts/enumerate_two_root_span_footprints.py \
		scripts/span_dominance_quotient.py \
		scripts/extract_dimacs_clause_core.py \
		scripts/find_decomposable_context_collision.py \
		scripts/verify_cap_failure_charge_matching.py \
		scripts/generate_e3_state455_lean.py \
		scripts/generate_e3_state466_lean.py \
		scripts/generate_e3_state566_lean.py \
		scripts/generate_cup_blocks_state_sat.py \
		scripts/generate_es5_sat.py scripts/generate_signotope_state_sat.py \
		scripts/split_dimacs_units.py scripts/split_lrat_checkpoints.py \
		scripts/toolchain/unzip scripts/verify_middle_split_bridge_route_model.py \
		scripts/verify_middle_split_pair_model.py \
		scripts/verify_packed_escape_sharp_census.py \
		scripts/verify_packed_middle_escape_model.py \
		scripts/verify_middle_bridge_realization.py \
		scripts/verify_repeated_residue_model.py \
		scripts/wayfinder_status.py

test-exhaustive: test
	@python3 scripts/check_span_dominance_quotients.py \
		data/derived/e3-span-dominance-quotient-k6-n9.json --workers 8 >/dev/null
	@python3 scripts/check_large_span_dominance_quotient.py \
		data/derived/e3-span-dominance-quotient-k6-n10.json >/dev/null
	@python3 scripts/check_rooted_span_interfaces.py \
		data/derived/e3-rooted-span-interface-k6-n10.json >/dev/null
	@python3 scripts/check_two_root_span_footprints.py \
		data/derived/e3-two-root-span-k6-n10.json --workers 8 >/dev/null
	@python3 scripts/check_allocated_span_pascal_demand.py \
		data/derived/e3-allocated-span-pascal-demand-k6-n8.json >/dev/null
	@python3 scripts/check_reflected_transition_hall.py \
		data/derived/e3-reflected-transition-hall-k6-n8.json >/dev/null

wayfinder:
	@python3 scripts/wayfinder_status.py

review-doctor:
	@python3 scripts/adversarial_review.py doctor
