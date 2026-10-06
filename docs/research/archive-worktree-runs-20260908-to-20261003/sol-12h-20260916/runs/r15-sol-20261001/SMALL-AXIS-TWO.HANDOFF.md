# Accepted small-axis indexed-marker bound two — 2026-10-01 07:39Z

Exact theorem: ctx_bound_le_two_of_small_global_axis_with_indexed_marker.
For a raw context with positive actual external labels, a chosen global
parameter at most three, N in levelsOn s 0 and x in extPositions N,
every boundFuel approximation and the full bound are at most two.
No well-formedness, run-count, sibling-maximum or length premise.

Commit 1a6c30a2590c51bdbddfe17b372039539e687989 on its own node branch
from main; node-commit job 20261001-033834-4e8833 terminal rc0. Only its
registered module/root import and harness-generated metadata were committed.
Type a485f50bd2c84ea5; first targeted check 20261001-033711-8a0538 passed
41.2s outer / 2341MiB / OOM0 / 3.344053s build. Complete receipt
040463f1f2cff1838389e97a3bffe687e07eb2f17e742370c56553f9ad8a0f83
is saved as CHECK.small-axis-two-v1.full.json: closed, no sorry,
standard axioms only, lock true, no blocked dependencies/tag errors,
incremental=true. Fixture dcf7cd7aaa4a183526da403b4f1ada7f6a89ebe7993532bfafa4445937cd2f8b.

Source SMALL-AXIS-TWO.candidate-v1.txt is byte-identical to the proof,
SHA256 52da6659bae8338dd36cb65b33cd998ced0b1fbe962cae9debbb0e7528316b1e.
The local one-extension and exterior-region proof is copied from the closed
rank-region potential, then composed with that theorem. Marker nonemptiness
caps the potential by the two exterior regions. No failed compiler attempt.
Search fde7dff9c1895f701c41aab673c34ef89a4639bc56a5ed8b97d796b5a7512fc8
found only different small-maxima linear/triple potentials, no duplicate.

Remaining obligation is positive k>=4 maximal-segment exchange, locked
type dbd0e335b115583d; partial commit e03d9bc70c29527dec456d5d3621ad5af95f37d1.
This result is an upper bound, not a flip witness. Next candidate: a proper
part on the side of an indexed maximum >=k-3 has all fuel/full bound <=2.
Normalize its shifted old level, preserving the fresh actual indexed
level-one marker, and apply this theorem. A two-axis near-saturation bound
and k4 paired upper bound may follow; none are yet proved. Exact normalization
is not assumed and no inequality is reversed. No own jobs are pending.

