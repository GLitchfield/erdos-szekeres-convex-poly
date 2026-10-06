# R16 adjacent-marker normalization review — 2026-10-01 08:15Z

Review window: window-72353247b15a4945. Reviewer: configured Sol/xhigh only.
The repository asks for a separate Astra mathematical/library review; the host
instruction permits only the configured Sol model and forbids delegation.
This is an explicitly recorded Sol self-review, not an independent Astra review.

Accepted theorem: ctx_boundary_adjacent_same_side_marker_merge_normalize_exact.
Final check 20261001-041119-280ff1; receipt
58c9ef0ef8e21c116e7e98592a6d190ad4c520d9d2256ca2e7f7604c230aea26.
Locked type 98bb67be7dd8f195; no sorry or nonstandard axioms.
Closed proof fixture 5a470668cc9300f9eb0bca040b8b1344b9cf5d823f2bebdc3f2ef4739873c3ee.
Frozen source SHA256 766e592a2fe05a4c80c8e9958cc594385f8c86396c060f567f809c5edb5e983f.
Receipt file SHA256 04f1d53cd662ba7dca88f8e1af3eac5a636be418eeefbd3c72a1f4813ebfe21f.

Reviewed statement and all proof layers: relabel/side/maximum transport;
opposite-axis level and sublist bijections; terminal selected level lists;
young extension folds; source-left=young-left+2 versus normalized-left=young-left+1;
right-extension equality; middle-level source-left=young-left+1;
selected chain and join identities; capacity arithmetic; part commutation;
inheritance of positivity, pair invariant, sole marker, older witness, boundary
order, oldest selected history and global bound; base and fuel/full equality.
The selected global<=k hypothesis pays the source's extra pure-chain join cap.
No positivity of either merged maximum is assumed or smuggled in.
Opposite history and global are retained. The conclusion covers every source
child endpoint and every fuel; it does not assert a root upper bound or attainment.
No other node's statement/body was edited. The new statement lock is unchanged.

Search/reuse: boundary adjacent same side marker merge normalize; merge same
side levels. The existing ctx_bound_le_merge_same_side_levels provides basic
transport but proves monotonicity with max(younger,older) and fixed globals.
Its local transports and the earlier certified boundary erasure proof were reused
inside this new node; the exact older+1 merge and global decrement are new.
No open theorem dependency appears in the accepted theorem's axiom receipt.

Ad hoc code review covered the current point_base_candidate.py and
probe_one_marked_point_base.py, their before-unit-rule snapshots, the marked-first
normal-form extension, existing review records, and the recorded job argv/failures.
The optional unit-axis shortcut is exactly the existing closed theorem
ctx_bound_zero_of_unit_global_axis for a<=1 OR u<=1. It computes all point
thresholds before the shortcut, reports per-root bound provenance, retains the
same 9,792-root family, and leaves every nonunit C evaluation unchanged.
The current candidate/runner hashes match the frozen launch hashes. No source
is changed while job034251-3577ad runs. C's global-zero rejection in the earlier
marked-first family is recorded; those normalized bounds are explicit theorem
rule applications and not C measurements.

No tracked workflow/C/Python implementation changed on this node branch.
The cache experiment and original generator/runner artifacts remain preserved.
The earlier usage-boundary repair and Part1 falsifier have their prior review
records; their algorithms were not modified in this research continuation.
No new recurring algorithm needs promotion from the exact Lean proof.
A possible shared unit-global evaluator shortcut is deferred because the
in-flight family pins shared evaluator sources; any later promotion requires
its own semantic regression fixtures and catalog/example review.
The one-off point-potential and marked-first mathematical candidates remain
separate from existing shared execution and result storage.

The successful targeted Lean receipt supplies theorem credit. Finite probe
passes and partial proof receipts supply diagnostic evidence only. N_ends and
N_root remain open.
