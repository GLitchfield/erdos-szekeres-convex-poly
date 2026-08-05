PROJECT_TOOL_BIN := $(CURDIR)/scripts/toolchain
export PATH := $(PROJECT_TOOL_BIN):$(PATH)

.PHONY: check update lean test wayfinder review-doctor

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
	@python3 scripts/check_structural_charging_countercontrols.py >/dev/null
	@python3 scripts/check_crossing_separated_caps.py >/dev/null
	@python3 scripts/check_published_offwindow.py >/dev/null
	@python3 scripts/check_rank_profile_realization.py >/dev/null
	@python3 scripts/check_agent_orchestration.py >/dev/null
	@python3 scripts/wayfinder_status.py >/dev/null
	@python3 -m py_compile scripts/adversarial_review.py \
		scripts/analyze_cap_failure_charge_matching.py \
		scripts/analyze_decomposable_rank_profiles.py \
		scripts/analyze_lrat_checkpoints.py \
		scripts/check_agent_orchestration.py \
		scripts/check_e3_state455_aggregation.py \
		scripts/check_e3_state566_aggregation.py \
		scripts/check_decomposable_contexts.py \
		scripts/check_decomposable_context_collision.py \
		scripts/check_decomposable_rank_profiles.py \
		scripts/check_incoming_star_prefixes.py \
		scripts/check_crossing_separated_caps.py \
		scripts/check_middle_split_pair.py \
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
		scripts/find_decomposable_context_collision.py \
		scripts/verify_cap_failure_charge_matching.py \
		scripts/generate_e3_state455_lean.py \
		scripts/generate_e3_state466_lean.py \
		scripts/generate_e3_state566_lean.py \
		scripts/generate_cup_blocks_state_sat.py \
		scripts/generate_es5_sat.py scripts/generate_signotope_state_sat.py \
		scripts/split_dimacs_units.py scripts/split_lrat_checkpoints.py \
		scripts/toolchain/unzip scripts/verify_middle_split_pair_model.py \
		scripts/verify_repeated_residue_model.py \
		scripts/wayfinder_status.py

wayfinder:
	@python3 scripts/wayfinder_status.py

review-doctor:
	@python3 scripts/adversarial_review.py doctor
