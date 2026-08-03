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
	@python3 scripts/wayfinder_status.py >/dev/null
	@python3 -m py_compile scripts/adversarial_review.py \
		scripts/analyze_lrat_checkpoints.py \
		scripts/check_e3_state455_aggregation.py \
		scripts/check_e3_state566_aggregation.py \
		scripts/check_decomposable_enumeration.py \
		scripts/check_signotope_state_witness.py \
		scripts/enumerate_decomposable_colorings.py \
		scripts/generate_e3_state455_lean.py \
		scripts/generate_e3_state466_lean.py \
		scripts/generate_e3_state566_lean.py \
		scripts/generate_es5_sat.py scripts/generate_signotope_state_sat.py \
		scripts/split_dimacs_units.py scripts/split_lrat_checkpoints.py \
		scripts/toolchain/unzip scripts/wayfinder_status.py

wayfinder:
	@python3 scripts/wayfinder_status.py

review-doctor:
	@python3 scripts/adversarial_review.py doctor
