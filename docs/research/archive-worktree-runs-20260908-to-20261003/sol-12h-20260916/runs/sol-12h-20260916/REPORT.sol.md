# Sol/xhigh twelve-hour research report

## Outcome

This run accepted 32 new, compiling, sorry-free Lean theorems and moved the compiled frontier
from 251 to 283 closed nodes. The target
`ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end` remains open: this run did not
prove the full unbounded sandwich additivity statement and does not claim the exact
Erdős–Szekeres conjecture.

The accepted chain closes every actual two-marker internal-complement `k=6` cut, including the
opposite-kept orientation, and reduces the remaining chosen-kept extreme cut to one precise
case. Any failure of the twelve bound now forces a canonical low/high rank-pair intersection of
cardinality at least three. A bounded falsifier then showed that the tempting broad theorem
`pair overlap >= 3 -> companion bound <= 11` is false after the actual cut construction is
forgotten. The real companion retains a synthetic opposite-axis level-one marker of maximum one;
the final accepted theorem exports the rank-endpoint loss caused by exactly that marker.

The safest next result is therefore a cut-specific coupled recursion bound retaining that
synthetic marker and `maximumAt 1 = 1`, sharing one charge across the low/high capacity groups.
Separate pair-set cardinality estimates are insufficient: bounded value-eleven examples already
have pair sizes `6+6` with overlap three and `6+9` with overlap six.

## Accepted proof receipts

All declarations below are in namespace `ErdosSzekeres`. Each targeted check passed, each full
extract reported no problems, every declaration has `sorry=false`, and the only axioms are
`propext`, `Classical.choice`, and `Quot.sound`. Full type hashes and artifacts are recorded in
`verified-results.json`.

| # | Declaration (namespace omitted) | Commit | Targeted check | Full extract |
|---:|---|---|---|---|
| 1 | `ctx_two_marker_younger_exterior_internal_complement_cut_component_bounds` | `e75b479d` | `20260916-132433-e4bbf5` | `20260916-135701-379475` |
| 2 | `ctx_two_marker_younger_exterior_internal_complement_cut_six_bound_of_extreme_maximum` | `21d89b6d` | `20260916-140958-8de097` | `20260916-141133-ca1bf7` |
| 3 | `ctx_two_marker_internal_complement_cut_six_top_width_both_middle_residual_classification` | `4162fc7f` | `20260916-142346-d4354d` | `20260916-142554-c7aed8` |
| 4 | `ctx_two_marker_internal_complement_cut_six_bound_of_maximum_three` | `0e7d7135` | `20260916-143839-50652f` | `20260916-144106-bf5e46` |
| 5 | `ctx_two_marker_internal_complement_cut_six_top_width_maximum_two_residual_classification` | `e320d72b` | `20260916-145250-e0ddba` | `20260916-145522-1e453f` |
| 6 | `ctx_two_marker_older_surrounding_internal_complement_cut_six_bound_of_maximum_two` | `b6f27203` | `20260916-150756-9d2087` | `20260916-150957-6ba730` |
| 7 | `ctx_two_marker_internal_complement_cut_six_top_width_younger_exterior_maximum_two_residual_classification` | `2a50cc86` | `20260916-152210-de216b` | `20260916-152443-b1be37` |
| 8 | `ctx_two_marker_younger_exterior_complement_mixed_capacities_separated_by_older_marker` | `4ccf71da` | `20260916-155348-fff097` | `20260916-155524-f2a4ab` |
| 9 | `ctx_small_global_axis_opposite_binomial_bound` | `602f2541` | `20260916-160642-75bf19` | `20260916-160803-809a48` |
| 10 | `ctx_chosen_sibling_maximum_opposite_binomial_bound` | `1611b971` | `20260916-161820-c15010` | `20260916-161938-bd0c38` |
| 11 | `ctx_two_marker_younger_exterior_internal_complement_cut_six_bound_of_maximum_two` | `c3d2e235` | `20260916-163135-a5e97f` | `20260916-163317-dd4907` |
| 12 | `ctx_two_marker_internal_complement_cut_six_bound` | `0ab8709d` | `20260916-164528-5443c6` | `20260916-164816-b9fbbb` |
| 13 | `ctx_two_marker_opposite_kept_block_cut_six_bound` | `fe1a819f` | `20260916-170402-b35869` | `20260916-170648-5450b5` |
| 14 | `ctx_extreme_cut_six_twelve_of_large_chosen_history_maximum` | `9a9c5df2` | `20260916-172204-669034` | `20260916-172443-57c484` |
| 15 | `ctx_extreme_cut_six_eleven_of_small_chosen_maxima_capacity_two` | `1e18fa9b` | `20260916-173720-aba3a1` | `20260916-174004-00216e` |
| 16 | `ctx_extreme_cut_six_small_history_mixed_capacity_residual_classification` | `85392b3c` | `20260916-175347-87cff4` | `20260916-175630-57e5b1` |
| 17 | `ctx_two_marker_low_capacity_pruning_seven_bound_of_high_witness` | `b35292cd` | `20260916-181715-590953` | `20260916-181854-927555` |
| 18 | `ctx_two_marker_low_capacity_pruning_rank_pair_bound_of_high_witness` | `b445cf15` | `20260916-183819-b4c7a3` | `20260916-183954-5c88e7` |
| 19 | `ctx_two_marker_mixed_capacity_disjoint_pair_support_ten_bound` | `b55e1455` | `20260916-190138-b1c17b` | `20260916-190313-12956a` |
| 20 | `ctx_two_marker_mixed_capacity_pair_overlap_excess_bound` | `ac94fa0b` | `20260916-192331-b83058` | `20260916-192506-24fc3a` |
| 21 | `ctx_two_marker_mixed_capacity_pair_intersection_one_eleven_bound` | `2d1497d6` | `20260916-193629-f77421` | `20260916-193807-7ef8cd` |
| 22 | `ctx_extreme_cut_six_twelve_of_pair_intersection_one` | `627c262c` | `20260916-195757-8c8c11` | `20260916-195938-3eee7a` |
| 23 | `ctx_extreme_cut_six_two_pair_collision_residual_classification` | `c6ca74b3` | `20260916-201221-2cff30` | `20260916-201400-920aaa` |
| 24 | `ctx_binary_capacity_pair_intersection_source_witnesses` | `92a77dc6` | `20260916-202532-139225` | `20260916-202619-c4f9b2` |
| 25 | `ctx_two_marker_pair_collision_source_separated` | `c3a6b225` | `20260916-204318-4582ca` | `20260916-204450-a2debe` |
| 26 | `ctx_extreme_cut_six_two_pair_geometric_residual_classification` | `8c0ed5bb` | `20260916-215002-439e4f` | `20260916-215140-9ad749` |
| 27 | `ctx_pure_extensions_position_monotone` | `135fac25` | `20260916-220409-ccc189` | `20260916-220508-3b2f2f` |
| 28 | `CtxTwoStraddlingPairCollisionsCommonWitnessIntervals` | `71b7db83` | `20260916-222053-0bc83c` | `20260916-222148-f9354b` |
| 29 | `rank_pair_triangle_intersection_card_ge_three_of_two_common_ranks` | `9e00e6e3` | `20260916-223441-59ed83` | `20260916-223522-fd980e` |
| 30 | `ctx_two_marker_two_pair_collision_intersection_three` | `c201c0c1` | `20260916-225757-dc63fb` | `20260916-225934-da5cf1` |
| 31 | `ctx_extreme_cut_six_pair_intersection_three_residual_classification` | `12fdc631` | `20260916-231128-4cd541` | `20260916-231308-5f6b3b` |
| 32 | `ctx_actual_marker_opposite_rank_interval_endpoint_exclusion` | `13bf3cd8` | `20260916-235158-9a1fd5` | `20260916-235247-bb4e2b` |

The final full extract (`20260916-235247-bb4e2b`) covered 296 nodes and 12,910 declarations,
reported 17 destinations and no problems, took 478.9 seconds at 5,862 MiB peak, and produced
tree hash `acd8e08828fb7257`. The final declaration type hash is `a5cecb39bcbadb6d`.

## Mathematical progress and remaining case

Results 1–13 close the actual two-marker internal-complement `k=6` cases. They establish the
younger-exterior component bounds, dispose of maximum-three and maximum-two residuals, transport
the separator geometry, and close the entire opposite-kept block.

Results 14–22 reduce the chosen-kept extreme cut. Large chosen-history maximum closes at twelve;
small maxima and capacity at most two close at eleven; disjoint canonical low/high pair support
closes the companion at ten; intersection at most one closes it at eleven and therefore the full
actual cut at twelve.

Results 23–31 turn the remaining pair overlap into source geometry. Two distinct collisions have
marker-separated source witnesses. Pure-extension monotonicity cross-combines their intervals;
two distinct common ranks generate three common nondecreasing pairs. Thus overlap cardinality two
is impossible, and the actual cut has the dichotomy “all cut sums are at most twelve, or canonical
pair-intersection cardinality is at least three.”

Result 32 captures the structure missing from the broad companion abstraction. An actual marker
on the rank axis puts every child strictly to one side: to its right every available rank is at
least two; to its left every rank `r` satisfies `r+2 <= global`. The unfinished step is to use
this endpoint partition inside both pruning recursions simultaneously. Neither the existing
`bound <= 10 + intersectionCard` estimate nor separate low/high pair cardinalities recover the
two required units of slack.

## Diagnostics, falsification, and failed attempts

- Guarded job `20260916-233503-c02de0` exhaustively tested the Lean-aligned retained recurrence at
  `(a,u,k)=(5,5,6)` with at most four children, two external positions, and two levels: 7,127
  well-formed contexts and 64,062 nontrivial partitions, zero additivity violations. This is
  falsification evidence only, not Lean proof credit.
- Guarded job `20260916-234719-bc184a` ran the final audited overlap probe. Among 1,984 bare exact
  two-marker signatures, 128 were mixed residuals and 40 had value twelve despite overlap at
  least three. With the mandatory synthetic opposite marker, all 824 mixed residuals among
  12,480 signatures had value at most eleven; overlap was three or six. This refutes the broad
  theorem and supports the actual-cut-specific target, but is not an equivalence certificate.
- The first full extract, `20260916-132614-f88e9e`, exceeded its 20 GiB budget after scanning
  (1,824.9 seconds, 20,480 MiB peak). Subsequent extracts used the declared 28 GiB guard and
  completed successfully.
- The generic five-child sweep `20260916-232614-4001ee` was cancelled after its retained benchmark
  implied roughly four hours. The filtered five-child extension `20260917-000224-ed58a0` was
  cancelled at the predeclared 00:25 EDT stop after about 1,364 seconds; its empty output has no
  evidentiary value.
- Initial cache-copy job `20260916-125101-e0cb90` failed with exit 127 because `rg` was absent in
  that job environment. The working environment subsequently recovered; all 32 accepted results
  passed targeted checks and full extraction.
- Proof-repair failures, including the three dependent-match/simplifier failures immediately
  before result 32 (`20260916-235052-8f9ecb`, `20260916-235109-3d3741`, and
  `20260916-235136-52c963`), are preserved in `checkpoint.md` rather than presented as results.

## Code and repository state

The run reused the catalogued `decomposable.context-enumeration`, `research.recursive-bounds`,
context-limit, and Lean-aligned zero-child implementations. The only introduced executable is
run-local `probe_two_marker_overlap.py`, which adds exact-residual filtering and pure-extension
reconstruction around those APIs. It was reviewed as one-off residual-specific mathematics and
was deliberately not promoted: it has no Lean equivalence certificate and no justified generic
workflow contract. `code-inventory.md` records this decision.

The prepared head was `52e48fa2`; accepted theorem commits run from `e75b479d` through final head
`13bf3cd8` on `node/CtxActualMarkerOppositeRankIntervalEndpointExclusion`. The tracked worktree is
clean. The final harness count is 283 closed, 12 open, one refuted, and no claims.
`es status` continues to flag the unrelated cross-worktree node
`CtxTwoMarkerYoungerExteriorInternalComplementChosenComponentFourBound` as stale because its source
is absent from this branch; repeated full extraction of this branch cannot index that source. No
push or publication was performed. The parent was released with outcome `partial`; its claim is
now absent and its attempt history records the partial result.

## Final review, jobs, and usage

The prescribed review command completed at the consolidation boundary and produced immutable
artifact `9e0334a07915ba705b6496701822b4aa9984b91b641444881f8011c919806779`. It inventoried
249 research jobs, the complete changed-tracked boundary from `52e48fa2` to `13bf3cd8`, and the
run-local probe at SHA-256 `ffb9a687d4c433fa5a4d7e2c8c9bbed454ed1283f5a326703d1d38b01649fd97`.
Its `explicit_proof_receipts` list is empty because these nodes were accepted through `es check`
plus guarded full extraction rather than the `es proof` receipt workflow; the bundle therefore
marks theorem credit `not_assessed`. The corresponding successful check/extract lifecycle entries
are present in that same bundle, and all 32 are independently reconciled in the table above and
`verified-results.json` (32 names, 32 commits, 32 successful targeted checks, 32 full extracts,
and 32 `sorry=false` entries). A baseline-to-head diff contains no added `sorry`, `native_decide`,
or axiom declaration.

The run's explicit single-model/no-delegation constraint precluded invoking an external Astra
agent. This is therefore a Sol-side code, receipt, and mathematical review, not the brief's
post-terminal authoritative Astra review.

The same review was rerun after the research deadline with the native goal paused and the host in
its bounded `final_turn_active` state. It produced artifact
`4be31e0952d1f142f426d4ea97db972af5d550428f0b2b213cd505527b7f01db`, again inventorying
249 jobs, the same prepared-head-to-final-head boundary and probe hash, and the final successful
check/extract lifecycle entries. The durable host observer remains the sole live job because it
exits only when this native goal is completed; it has no pending research child.

At the pre-consolidation inventory, the only running job was durable host observer
`20260916-130525-4020c1`; all proof, extraction, and diagnostic jobs were terminal. After release,
the refreshed frontier is 283 closed, 12 open, one refuted, and no claims. The queued and starting
job lists are empty; the same observer remains the sole running job while this goal finalizes.

Usage window: `window-e959d6afb2e44ef6`, thread
`01a0ab2e-b3cd-7e22-86e7-9ea28ebc6efb`. The reconciled consolidation snapshot at
`2026-09-17T04:36:11.407Z` came from the native rollout JSONL and covered 2,308 records:
335,319,469 input tokens (332,160,256 cached), 703,890 output tokens, and 172,120 reasoning-output
tokens, with zero reconciliation delta. The source warns that the active request and later
reporting may lag. The reconciled finalization snapshot at `2026-09-17T05:08:31.839Z` covered
2,414 records: 345,701,715 input tokens (342,451,584 cached), 731,517 output tokens, and 181,146
reasoning-output tokens, again with zero reconciliation delta. Relative to consolidation, the
single finalization phase added 106 recorded requests, 10,382,246 input tokens (10,291,328 cached),
27,627 output tokens, and 9,026 reasoning-output tokens. The final answer itself necessarily falls
after this snapshot.

## Safest next action

Start from `ctx_extreme_cut_six_pair_intersection_three_residual_classification` and keep the
actual companion construction visible. Prove a coupled recursive potential under the explicit
synthetic opposite-axis level-one marker with maximum one, using
`ctx_actual_marker_opposite_rank_interval_endpoint_exclusion` to partition endpoint loss and
share a charge across the low/high capacity groups. Do not attempt the falsified detached theorem
`overlap >= 3 -> companion bound <= 11`. Reuse the actual-marker transport and normalization in
`ctx_two_actual_marker_companion_maximum_bound`: at the result-31 interface one already has
`p ∈ B.extPositions 1`, `B.sideAt 1 = t`, and
`B.maximumAt 1 = n` by `Ctx.Context.part_maximumAt_one`. Specialize the target branch to `n = 1`
before erasing or abstracting that level. The existing companion-maximum theorem gives 13 at
`k=6,n=1`; the new coupled overlap/endpoint charge must save exactly two.
