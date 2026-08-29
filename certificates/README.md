# Checked proof certificates

This directory contains proof inputs that are part of the reproducible Lean
build.  Lean sources must not use `include_str` to read from ignored `runs/`
state.  The following project-generated artifacts were promoted from their
frozen local runs on 2026-08-29 and checked byte-for-byte with `cmp` before
commit.

| Canonical directory | Frozen source | Files | Aggregate SHA-256 |
| --- | --- | ---: | --- |
| `half-pure-singleton-fin10` | `runs/agents/20260811-four-slot-deep-wave/half-pure-fin10` | 2 | `383a838cd17295c6f3c7138ae34c36640f251f73fb704f9249897841b0f437ca` |
| `mixed567-all-order-checkpoints` | `runs/agents/20260812-promotion-wave/mixed567-lean/{core,checkpoints}` | 97 | `0f6f3b59195145dba673642672cf2aa5c5d4f033fe7a2bac1cd0500ac2efdf38` |
| `synchronized-five-fan-fin11-checkpoints` | `runs/agents/20260812-promotion-wave/fin11-cubes/depth-6/v015-1_v111-1_v155-1_v068-0_v142-0_v002-0/core` and `runs/agents/20260820-four-thread-grounding-slate/fin11/generated` | 97 | `6f5396dc921657d3d0b4b4229821602e265b1245d14a36028b70f8ea6a78f194` |
| `pascal556-witness-reuse-fin14` | `runs/agents/20260812-promotion-wave/pascal556-lean` | 1 | `cdfe268a6c6009054163d0131cc6dd6579dc3d980b04d3125903d025b15a580a` |
| `predecessor-half-fin13-checkpoints` | `runs/experiments/20260826-predecessor-half-fin13/{compact-core,checkpointed}` | 769 | `e8c6e080a4ed1ee8ae2e1fb316b8c3e7d8ec9114b2357f69102c25616fbe8995` |

Each aggregate is the SHA-256 of the sorted `sha256sum` output for every file
under the named canonical directory.  These are project-generated DIMACS,
LRAT, and checkpoint-state inputs; they are not third-party source snapshots.
