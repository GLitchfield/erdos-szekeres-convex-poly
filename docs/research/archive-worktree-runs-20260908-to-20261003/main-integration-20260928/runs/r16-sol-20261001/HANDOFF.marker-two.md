# R16 indexed-marker global-two zero handoff

Accepted independent commit 56dfcefde8e66cf872a469889c0a34d7c5bae794.
Branch node/CtxBoundZeroOfIndexedMarkerAndGlobalAxisAtMostTwo; parent
5847e155fa613d4d2311eaee86b4b094f630e9a4. Exactly five node files, clean,
left_uncommitted=[]. No integration, push or primary source edit.

Accepted theorem ctx_bound_zero_of_indexed_marker_and_global_axis_at_most_two,
locked type f7acd09c609a4ab1.
For arbitrary raw sigma and side s, require N in sigma.levels, sideAt N=s,
x in extPositions N, chosen global <=2. Conclusion: every boundFuel and
full bound equal zero. No positivity, WellFormed, legal k/globals or maximum
hypotheses. Physical but unindexed inert markers are outside this statement.

Successful targeted check 20261001-074023-fb5509:
3.08964204788208s /573MiB /4G; closed, lock_ok=true, sorry=false,
only propext/Classical.choice/Quot.sound, no blocked/uncovered/nonstandard axioms.
Exact INLINE receipt is CHECK.marker-two-v2.closed.detail.json, SHA256
091db6902946d2a09bf939d8064de78c29174cf269f93c7cdca3f66ae673743a.
Whole-parent fixture cc89037c14c7d32978398259df98b9f530fd09cdf235b8c1ee1efda0c34b9f6e.
Commit job 20261001-074230-37c5cc completed; approved parent independently verified.
Frozen exact source Marker-two.closed.lean (4229 characters /88 lines), SHA256
7b1daffdbae434a386dcd3bbc50b983b2e0d56df7d4379c2b652e44bf490e294.
Reviewed source matches accepted v2 byte for byte.

Every child differs from the marker. The indexed singleton-level left/right
witness gives chosen chainExt>=1, so chosen point limit is zero at global<=2.
All point baseOf values vanish. Unconditional sum-point upper gives full bound
zero. Fuel monotonicity and checked stabilization give every-fuel zero.
No dependence on the unrelated open EndCut statement.

Failures retained:
- Registration 20261001-073533-70ee09: wrong positional name/module CLI;
  stopped before Lean or node creation. REGISTER.marker-two-v1.failed.log.
  Corrected --name and explicit --targeted registration073616-b3bf2d succeeded.
- Check 20261001-073854-2923ff: two unreduced side-match arithmetic hypotheses
  and missing stabilization import, 3.083804s /607MiB. Marker-two-v1.failed.lean,
  CHECK.marker-two-v1.failed.json, BUILD.marker-two-v1.failed.log.
- Small successful inline receipt was initially mistaken for an artifact reference;
  local assertion stopped before freezing but retained the complete result.
  Saved exact job.result_json directly. No result lost or theorem affected.

Research window window-ae537e713d314658 ended accepted=1; separate configured
Sol self-review window window-3aef6249c749480e ended accepted=0.
CODE-REVIEW.marker-two.md and COMMIT.marker-two.txt document review and searches.
Host forbids delegation; no independent Astra review. No new workflow or Python
algorithm introduced; checked automation reused and no promotion needed.

This helper resolves zero-capacity cut parts with an actual indexed marker,
and root old-marker axes <=2 once marker existence is supplied.
It does not itself prove the full degenerate selector, neither-marked exchange,
larger-axis upper or N_ends/N_root.
Other accepted results and precise larger-axis Stuck evidence are in the main
MATHEMATICAL-HANDOFF.md and HANDOFF.larger-axis-upper-stuck.md.
Coordinator journal additionally confirms completed k7 <=5-child diagnostic
selector coverage with 0 failures (24674 nonzero contexts); prior 'k7 partial'
language is superseded. Six-child coverage remains open.
Same trial, active native goal, unchanged research deadline 17:04:46.416915Z.
