# R16 marked-first normal form candidate review — 2026-10-01 07:35Z

Configured Sol self-review before timing/family. Shared part API searched and
read via es lib search/show; existing runner extended, no new workflow.

Pure candidate assumes uniform ext1 old side, one maximum, both word ends
marked, and chooses the least actual child position. Actual complement uses
shared part. Proposed word replaces only that child by ext1 old side, merges
maximum to max(newMaximum,oldMaximum+1), decreases selected global by one.
Includes original legal global1, yielding raw normalized global0.
Correction: shared C API rejects global0; full family job033602-36ec69 failed
before any audited root/output. Timing withglobals5 remains valid.
Runner now handles normalized global0 by the existing closed Lean theorem
ctx_bound_zero_of_unit_global_axis (a<=1 OR u<=1 gives every bound0), explicitly
counts these rule applications and records provenance in JSON. Source positive
globals still evaluated by C; all initial matrices computed with lean=True.
No root/comparison coverage dropped. Rule-applied normalized values are not
C measurements. No new theorem credit asserted.

Runner optional --marked-first-child preserves default unmarked-p0 behavior.
Marked mode checks only the same-axis complement, every legal new maximum,
both old sides/all original globals/maxima. Reuses frozen root generation,
shared C evaluator/part and Lean-style matrices,progress/coverage/source hashes,
pool closing and existing guarded job reporting. Existing sources preserved in
*-before-marked-first.py snapshots. No shared recurrence or library edits.

No useful new generic algorithm to promote: mathematical candidate remains
small and separate from runner; existing shared execution/storage reused.
