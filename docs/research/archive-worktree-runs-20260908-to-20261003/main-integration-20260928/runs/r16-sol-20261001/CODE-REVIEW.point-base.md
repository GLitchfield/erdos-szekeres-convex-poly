# R16 point-base candidate review — 2026-10-01 07:15Z

Extension reviewed07:42Z: optional --unit-axis-bound-rule uses existing closed
Lean ctx_bound_zero_of_unit_global_axis only when a<=1 OR u<=1. Initial limit
matrices and point thresholds still computed; every such root separately counted,
bound provenance explicit in comparison/JSON. Nonunit roots use unchanged C.
Optional --timing-a selects one legal a for the existing one-fixture timing path.
Original candidate/runner preserved in *-before-unit-rule.py. The first five-child
family033628-3c3c4a was cancelled at a progress checkpoint after700/9792 audited
roots(0violations),not a result; same full coverage must be rerun. Shared C and
execution library unchanged. Useful generic unit-global shortcut deferred pending
evidence/maintenance; no new workflow algorithm or promotion required now.

Configured Sol only. Reviewed point_base_candidate.py and probe_one_marked_point_base.py before the family run. The candidate uses initial per-run diagonal limits, legacy threshold, and the shared compiled bound, with exactly one marked word end checked explicitly. The frozen generator has uniform level-one letters and no marker inside a child run, so these diagonals represent every point in that run. This is diagnostic arithmetic, not a Lean equivalence certificate.

The runner reuses the frozen generator and bounded persistent C evaluator, closes each evaluator, records source hashes and full coverage, and reports progress every 100 roots. Timing job20261001-031415-ce41e8 passed one longest four-child k5 fixture in0.021995562s. No evaluator, recurrence, job/guard or result-storage infrastructure changed. No generic algorithm to promote; the one-off mathematical candidate remains under the run directory.
