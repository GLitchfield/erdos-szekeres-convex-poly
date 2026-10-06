# Twelve-hour lemma research report

Research window: 2026-09-09T19:32:21Z to 2026-09-10T07:32:21Z.
The final deadline checkpoint was missed during an agent activity gap and was recorded
late on resumption; the original parent claim expired. The late handoff does not
extend the fixed research window. Timing and resource deviations are detailed below.

Final compiled-state verification: 2026-09-10T12:16:01.587017+00:00.
Agent: `codex:01a087a7-d0cf-7e23-8514-e295400a06ee`.

The run produced 38 explicitly stated, compiling theorems with locked types,
standard axioms, checked node branches and verified full indexes. Completion of this
timed research run does not mean the Erdős–Szekeres conjecture is proved.
The shared harness began with 114 closed nodes;
the final checked counts are `{"closed": 152, "open": 12, "refuted": 1}`.

## Mathematical progress and remaining work

The run added 38 registered, compiling theorems. The previous run's 70 additions are inherited and are not counted again. Local helper proofs inside a new theorem are not separate results.

Results 1–24 develop the rank accounting needed by the additive context obstruction: arbitrary-cut one-level bounds; exact rank-pair, row/column and triple-face union counts; pruning comparisons that preserve physical child runs; capacity-three additivity cases; and boundary/marker normalizations. Result 5 removes the actual-marker assumption for the small-global rank-pair potential. Result 22 preserves the exact missing corner in a clipped pair union. These are reusable components, not a proof of the full additive conjecture. Result 21 explicitly assumes an anchored-square bound.

Result 25 proves an unconditional normalization of shared rank unions to a bare chosen-marker context, including positive labels, child preservation, active children, zero indexed maxima and full-bound domination. It does not prove the bare square bound. Results 26, 29 and 30 are conditional reductions with explicitly bounded bare-square premises. Result 27 proves the small-opposite-global square case unconditionally; result 28 proves the internal chosen-interval square budget when the opposite indexed history is empty.

Result 31 is the main reduction: the general chosen-capacity-five youngest-marker exact-rank square estimate follows from a bare two-marker potential P(w) = choose(w+1, 2) + w - 1 at widths w ≥ 4. The premise restricts to positive contexts with two actual chosen markers, zero indexed maxima, all children active, no opposite indexed history and chosen global at most five. The source may have arbitrary histories, maxima, inactive children and physical separators. Those complications are handled by the checked normalization and cut lemmas. The bare two-marker premise itself remains unproved.

Results 32–38 establish concrete cut estimates for that remaining premise. The internal opposite block beyond the younger marker (32) and the block between the markers (33) satisfy P(w) unconditionally under their stated geometry. Internal blocks surrounding the younger marker (34) or older marker (36) reduce the companion to at most w-2 and explicitly assume the smaller-width bare two-marker premise. The outward endpoint cuts beyond the younger marker (35) and older marker (37) satisfy P(w) unconditionally. The endpoint block strictly between the markers (38) satisfies the stronger sum bound 2w-1. The endpoint statements allow arbitrary opposite history where stated. The full compiled signatures are authoritative for each hypothesis; the cut classes have not been assembled into a complete classification theorem.

The primary mathematical gap is the older-exterior internal cut. Independent full bounds give a chosen-side estimate 3w-1, while the triangular companion requires 3w-2: the missing unit must be proved. A corrected finite diagnostic shows this is tight. For w=5, source word S S S E2.lower E1.lower S, a=6, u=5, k=10 and zero old maxima, keeping position 1 gives source value 19=P(5), chosen value 13=3w-2 and opposite value 6=choose(w-1,2). Both legal pairs of new maxima (4,5) and (5,4) give the same values. The Lean recurrence uses m+n=k-1, not m+n=k. The original equal-five interpretation was corrected; the seven-case corrected probe completed without timeout. This is Python evidence, not a Lean theorem.

Two additional drafts are preserved but unregistered and uncompiled: `two-marker-surrounding-endpoint-cut` (1391 lines, conditional on P at widths at most w-1) and `inward-endpoint-cut` (361 lines, proposing an unconditional triangular bound). They were not checked after the deadline and contribute zero to the result count. Next session should inspect fresh harness state, reassess these drafts, register one actual cut theorem at a time, then address the missing unit and the complete cut classification, empty/full parts and recurrence base cases. Existing scripts retain this run's agent, paths, deadline and branch guards and must be adapted rather than run blindly.

Known dead ends remain excluded. Capacity-three adjacent-child contraction has a compiling counterexample: physical separators matter, including unindexed external letters. The proposed generic nonmonotone three-marker bound 2w+1 is false in a finite example with w=5 and value 13>11. The separating-marker normalization cannot impose the proposed k-M cap. Timed-out finite probes provide no positive evidence for their uncompleted cases.

The parent `ctx_bound_additive_sandwich_one_singleton_end` and the full Erdős–Szekeres happy-ending conjecture remain open. The handoff records actual theorem progress and remaining premises; it does not claim the conjecture has been proved.

## Verified theorem branches

Every listed branch was checked against its local ref, remote-tracking ref and the
actual remote head. Proof and index commit scope, ancestry, compiled type hash,
standard axioms, build records and audits are in `final-verification.json`.
Local proof components inside a registered theorem are not counted separately.

| # | Theorem | Result | Proof commit | Index commit |
|---|---|---|---|---|
| 1 | `ctx_one_level_arbitrary_cut_rank_bound` | Bound arbitrary cuts in a one-level context by twice its active rank count minus one | `c826c713d4c0d6e598a5b1394a1a1ecc0c5bceed` | `68b32722a08bcc8a92331b3d78732259634e68e8` |
| 2 | `ctx_one_level_arbitrary_cut_rank_pair_bound` | Bound arbitrary cuts by the active opposite-rank-pair union | `91dc6cfe256a7044d641d909a1f78cd6edbfc494` | `24cf5562a310ab8ae582b3402d17e35f26c55bc0` |
| 3 | `rank_row_column_union_card_eq_group_charges` | Count pivot-merged row and column reservations exactly | `fd72e926e7b5e260b66e190508623e9ec45270f0` | `957fbb0f9be69ab1980b8a104b52bc5f8e5baf48` |
| 4 | `ctx_youngest_marker_row_column_potential_bound` | Bound youngest-marker contexts by endpoint row and column reservations | `91d658f78842af49694920a1d468fca1adf2fbf2` | `5fd1e53524e6381ee81aaec6407cbad12b923bbc` |
| 5 | `ctx_small_global_axis_rank_pair_potential` | Remove the marker premise from the small-global rank-pair potential | `361aecaaa58f1a860d3ae1a756afef78928b07dc` | `25802f5e86af0dbfe05cbdd1cbf1020d580f74dd` |
| 6 | `ctx_small_global_opposite_maximum_binomial_bound` | Bound small-global contexts by an opposite sibling maximum | `c5e2cccc02c156221a1f59f4b4e18357ec46e54a` | `b9220bb4d0bbab2b3b23b2cd6d24afb1fed97d0f` |
| 7 | `ctx_bound_additive_interval_complement_middle_capacity_three` | Prove middle-capacity-three interval complement additivity | `4f73db04d61acb10f87343a91c19933da5a5ead9` | `1f5d18c6a8f2a2390787e53a17ff1215e49576dd` |
| 8 | `ctx_bound_additive_single_run_min_capacity_three` | Prove every single-run interval cut at minimum capacity three | `414fc39a38e1cde35625ec37d8a266f3410e12cd` | `ffebbbad67b14a7d0843e391a054c1c724ec0379` |
| 9 | `ctx_bound_le_sum_run_group_prunings_capacity_three` | Extend run-group pruning decomposition to capacity three | `4a3c72a8197a3bf61a17b9f79f70d281ae81819d` | `d871c09b9d423c938c69fd4f128c41c4c16a23b3` |
| 10 | `ctx_bound_le_inactive_prune_capacity_three` | Preserve the bound under inactive pruning at capacity three | `b143dd3551836ed375c4607a19a4f41dbba7b9dd` | `02357922d61c31c8f7894907b135ab2a692f6f9e` |
| 11 | `ctx_active_boundary_marker_rank_pair_union_bound` | Bound active boundary contexts by their opposite rank-pair union | `a252375883f9d8e9e2cf84014d82c777f6fe320b` | `20482203b3e50bcc3720410299659dab01744513` |
| 12 | `ctx_chain_one_straddling_unique_axis_level` | Isolate chain-one straddling geometry from capacity bounds | `b96cb9fb512a78b862a4247da01cb23eca1003a5` | `287a6f5aa550f9d89149431724a9c9981e3cce17` |
| 13 | `ctx_two_boundary_marker_upper_normalize` | Normalize regions between two markers on one indexed level | `8a0e304d9c9573456ba5dc815ed265448830392f` | `aa1c9eb8ac4d8fdb4d7a1d69f62a3e1ac592d81f` |
| 14 | `ctx_two_boundary_marker_erase_normalize` | Preserve opposite history in two-boundary normalization | `9807dcab54af331158adeee46c979d3351f9712c` | `0334c9f9c8cec28b4d333ba81b30f3cf7752a410` |
| 15 | `ctx_chain_one_children_exterior_of_two_levels` | State two-level exterior geometry by pure chain extension | `df6338b735b2df203ecd9fae4e616380bdfd4a4c` | `fec8181767c56f6f6b93ee54d78750e97e7c6012` |
| 16 | `ctx_active_two_boundary_marker_rank_union_bound` | Bound active bracketed regions by opposite rank unions | `bcc22ba96d77a0c3b5dbedd671b95f605cf5a1ca` | `a0d2af2d609864071bcda380a1df01d50c68cc75` |
| 17 | `ctx_separating_marker_erase_normalize` | Normalize markers separating younger and older chosen history | `b33a439883f0bc98fc7722bd4c8f28adac6b2ae7` | `5729e607dec45a1cbf49be3518737ab387b075f1` |
| 18 | `ctx_separating_marker_retained_boundary_rank_union_bound` | Bound separated exteriors using a retained older boundary marker | `ba706e005fd6450e9d7acd47a0a4807394121035` | `4d07ef5d14ede7badbda0ed9fac4f4d150477a42` |
| 19 | `rank_triple_face_interval_union_card_sq` | Count the union of endpoint triple faces exactly | `1886726572bddc7a907664c498e89d58e851491c` | `f3b001dfb93f9d4d371e4ff87a27b93e79a97627` |
| 20 | `rank_triple_face_union_card_eq_group_charges` | Count grouped ordered-triple endpoint faces | `cef99ecf201239beb825f2f77a2ce84c8ff4f7ea` | `fa02f2cf10c73cea7aba59450d35ed8c12e1e0f8` |
| 21 | `ctx_youngest_marker_triple_face_bound_of_anchored_square` | Reduce triple-face control to an explicit anchored-square bound | `f4df9204bc46a653268e26edf79b3ea52bd8b737` | `ab102a8735761cdd61007e4abc39146a77b0da6a` |
| 22 | `rank_pair_clipped_interval_union_missing_corner` | Count the missing corner in clipped rank-pair unions | `aa55f85505946d2bf6dd4c97290ae5f9052180e0` | `fb659f7d1121648923490f8cd2d13e84084f69e3` |
| 23 | `ctx_single_level_occurrence_prune_bound_mono` | Prune occurrences while preserving indexed level sides | `bd0ccf0fba273028df5fa641965c7ce01aea76f4` | `449fa9ba2288e90f5cd655a318b493a5b8c20b96` |
| 24 | `ctx_separating_marker_retained_level_doubled_rank_bound` | Bound separated contexts using a retained same-axis marker | `02eff613f00022cfa301b6918b3d1f3e3e90e1a8` | `e1dff45be6be68f696b7f6c679aaaf0c8d7bce0c` |
| 25 | `ctx_shared_rank_bare_marker_upper_normalize` | Normalize shared ranks to a bare chosen marker | `233a77645318eb08b110cc7950bbfb3b91f44ee9` | `de5ef041bdc36c8521326192fdaa443db6836525` |
| 26 | `ctx_youngest_marker_rank_square_bound_of_bounded_bare_square` | Reduce marker square bounds to the bounded-width bare case | `89c72aa862c38073cc8bba83decc23c7ecc9eff4` | `dab51d8c274218b83de7452a29831500cb7aefd4` |
| 27 | `ctx_small_opposite_global_marker_square_bound` | Prove the marker square bound for small opposite globals | `b4985eb2917931b6b40f7a4bf401bb026b063d1a` | `fb1d560280cbcc1d34958591286d0f2edd99f8d8` |
| 28 | `ctx_internal_interval_cut_square_of_empty_opposite_history` | Prove the square budget for internal chosen-interval cuts | `a1c0ea0acd6a4e77698bb8dc421b40eb370bea57` | `1a28ea8d1adf58d38f578ca852d61c8f1bfd5876` |
| 29 | `ctx_endpoint_cut_square_of_bounded_bare_square` | Reduce endpoint cut square budgets to smaller bare-marker widths | `93d49f9c332d3e928c14b69d6d34abe666e21779` | `be47702eedde785ed99676d69045c104cec17dc2` |
| 30 | `ctx_bracketed_pivot_complement_cut_square_of_bounded_bare_square` | Bound internal complement cuts with a bracketed pivot | `247c4d3c955e792a54a39a726c3c0a4240d482b3` | `474a094d05297ac07140054801893762bbdb5eff` |
| 31 | `ctx_youngest_marker_rank_square_bound_of_bare_two_marker_potential` | Reduce the youngest-marker square bound to a bare two-marker potential | `590b3e8b4b76e8ccb3946162d23decb1b0ea7725` | `c686c795e5c19b0474574962f3982270566e4569` |
| 32 | `ctx_two_marker_younger_exterior_internal_complement_cut_potential_bound` | Prove the younger-exterior internal cut for the two-marker potential | `375f8b4bf8f922a1608154d2bc2711454c135409` | `f1a54a61806c43881dc1da854dc84a1cbaedd8d3` |
| 33 | `ctx_two_marker_between_internal_complement_cut_potential_bound` | Prove the between-markers internal complement cut potential | `60801e684dbc1c8c4131e3e0074f907b5a8bcba2` | `237ed4754a2fbe8ad0b9264094bf0a024338a2a1` |
| 34 | `ctx_two_marker_surround_younger_internal_complement_cut_potential_bound` | Reduce the younger-surrounding internal cut to two fewer opposite ranks | `fe05c63fe2c73306598a9c9b2515beeaf3854ec1` | `16fe923d7329de676b3b888f7fa7b8c9beb18e8d` |
| 35 | `ctx_two_marker_younger_exterior_endpoint_cut_potential_bound` | Prove the two-marker younger-exterior endpoint cut potential | `6cb0fca6262f7477477027983308d53c096b3869` | `ee7d08085c1b5f35b726255ada3e400c3f7f63b3` |
| 36 | `ctx_two_marker_surround_older_internal_complement_cut_potential_bound` | Reduce the older-surrounding internal cut by two opposite ranks | `f28ca41954235b56e8b0265d58716042b98d7baa` | `2ae887375dff31e4dc1af1bc41545fab006f7b1e` |
| 37 | `ctx_two_marker_older_exterior_endpoint_cut_potential_bound` | Prove the older-exterior endpoint cut potential | `a5c5bedf8504b96d586c4c0dc2594579ba112a5b` | `c4f7b89c8aabb7e011e706f584cce3f6d1283b7d` |
| 38 | `ctx_two_marker_between_endpoint_cut_doubled_rank_bound` | Bound the between-marker endpoint cut by twice the width minus one | `fba21f2c697f11eb3ceb5eb617f0bbd27c0b9b4e` | `b45fd29ec491882e8af10584a51aefd67223e876` |

## Checkpoints

The stale count records the state at the checkpoint, including any active proof or
refresh. The final compiled-state audit requires a current index with no problems.

| Checkpoint | Actual UTC | Checked results | Stale entries |
|---|---|---:|---:|
| 02h | 2026-09-09T21:32:29.067021+00:00 | 7 | 1 |
| 04h | 2026-09-09T23:32:28.132452+00:00 | 15 | 1 |
| 06h | 2026-09-10T01:33:04.899573+00:00 | 21 | 0 |
| 08h | 2026-09-10T03:34:39.991684+00:00 | 27 | 0 |
| 10h | 2026-09-10T05:32:29.607588+00:00 | 33 | 1 |
| 12h | 2026-09-10T12:06:39.306897+00:00 | 38 | 0 |

## Resources and execution

The fixed research window was 2026-09-09T19:32:21Z to 2026-09-10T07:32:21Z. All 38 proof commits and targeted audits were completed before the deadline. The last full compiled refresh also finished before it, at 2026-09-10T07:04:21Z. Final index publication and handoff occurred after the deadline.

There was a gap in agent activity spanning the deadline: the last saved pre-gap continuation state was about 07:00Z, and the first current-clock observation on resumption was 12:06:05Z. The cause is not established by the available evidence. Continuous agent research through the last half hour and an on-time final handoff cannot be claimed. No new theorem was registered or proof development started after resumption. The missed 12h checkpoint was recorded at 2026-09-10T12:06:39.306897+00:00, 16458.307 seconds (4h34m18.307s) late, with its actual timestamp and 38 direct remote ref checks. It is a late recovery checkpoint, not evidence of an on-time checkpoint. Earlier checkpoint lateness was 8.067s, 7.132s, 43.900s, 138.992s and 8.608s respectively. The 06h checkpoint has a separate direct-remote supplement.

The original parent claim expired after its 07:34:35Z deadline. Its expired event remains in the harness. A short, explicitly labeled handoff claim was created and released with outcome partial at 12:08:23Z; this does not erase or retroactively repair the missed release. No claim remains for this agent. The first post-gap publication attempt correctly refused outdated claim metadata. That metadata was regenerated from the current full compiled cache before publication was retried.

The normal-shell worker successfully dispatched the research jobs and the late checkpoint. Quiet foreground behavior is expected. The boot ID on resumption matched the original ca967a75-a19a-45df-bbd0-58a14b1e2600; no reboot was observed. No parallel proof agents were launched. The inherited worktree configuration change is preserved outside all proof/index commits, with normal build cap 3 GiB. The shared budget is 30 GiB; proof jobs normally used 3 GiB, full refreshes 28 GiB, index checks normally 2 GiB, diagnostics smaller caps and awake helpers 128 MiB. The final metadata reconciliation and global audit use 3 GiB. The 38 full-refresh job intervals do not overlap other recorded Lean/build/registration/index-check workflows (final-refresh-serialization-review.json).

Resource measurements are scoped: the outer refresh wrapper's peak is not its nested extractor peak. A live nested-extractor sample recorded 5,724,327,936 bytes at 05:21:40.672254Z, and the final refresh's nested sample recorded 5,391,163,392 bytes at 06:58:22.741827Z, both without recorded OOM. These are samples, not guaranteed final peaks. The largest passing proof-build peak in the saved build records was 1685 MiB (result 25); the slowest passing build record was 28.773 seconds (result 26). Failed proof attempts and deliberate stops remain in the job inventory and are not counted as successful validation.

Two material resource incidents were resolved and must remain visible. The ninth-node audit omitted --targeted and inherited a 36 GiB inner extractor cap (38,654,705,664 bytes), exceeding the requested cap policy. The identified scope was stopped through the worker; observed peak was 5,391,912,960 bytes with no recorded OOM. A run-local guard subsequently rejected non-targeted node checks. Thus the run cannot claim that every cap request honored the 30 GiB policy. The 34th first build was intentionally terminated after about six minutes of a costly simp_all step, with observed inner peak 1,114,927,104 bytes and no OOM. Explicit inequalities repaired the proof, which then compiled successfully under two million heartbeats. Other recorded failed dispatches and proof repairs are retained in the manifest/job records.

The original Windows SetThreadExecutionState helper confirmed an idle-sleep prevention request and retained a heartbeat through 08:32:17.659650Z. It stopped at its explicit deadline-plus-one-hour fallback at 08:32:27.776412Z; its final Windows-child exit code was not captured in the old state file. Linux logind inhibition was denied and is not claimed. There is no evidence of an active idle-sleep inhibitor between that fallback and the separate late-handoff helper's confirmation around 12:06:59Z. A new 128 MiB handoff helper was started with separate state/log artifacts so the original evidence was preserved. The separate handoff helper stopped at 2026-09-10T12:16:49.423055+00:00 with Windows child exit code zero. The final runtime check passed at 2026-09-10T12:17:25.037274+00:00; its own harness job then finished successfully. No live jobs or claims remain for this agent. The existing normal-shell worker (PID 3972, Python -m es worker) remains running. The first runtime check used an incorrect shell-launcher process predicate; it was corrected to the actual Python module command and rerun successfully, without restarting the worker.

Final job inventory: 312 recorded jobs, 273 done and 39 failed, with no live jobs. Failed intermediate proof attempts, deliberate diagnostic interruption, dispatch mistakes and the two corrected handoff checks remain visible. Every counted theorem has a separate passing build and targeted audit; failed attempts are not counted as proof. Final global compiled-state verification used 3 GiB, took 122.0 seconds and recorded a 259 MiB outer peak. The final metadata reconciliation/publication used 3 GiB, took 236.8 seconds and recorded an 808 MiB outer peak. See final-job-inventory.json, final-runtime-check.json and final-cleanup-job.json.

## Handoff evidence

The manifest is `run.json`; the final environment checks are `final-extract.json`,
`final-layers.json`, `final-audit.json`, and `final-status.json`.
`final-verification.json` contains the checked branch refs, proof records, claims
and job state at the compiled-state check. Final awake shutdown, worker state and
job cleanup are recorded in `final-runtime-check.json`, `final-cleanup-job.json`,
and `final-job-inventory.json`. The requirement review is `completion-review.json`;
`next-run.md` is the concrete restart handoff. The worktree is `/home/gavin/git/erdos-szekeres-convex-poly/runs/worktrees/codex-01a07c5a` on
`node/ctx_two_marker_between_endpoint_cut_doubled_rank_bound` at `b45fd29ec491882e8af10584a51aefd67223e876`.
The inherited local `harness/config.toml` change is preserved outside the commits.
Run artifacts and prepared but unpublished drafts remain in this run directory.

Report generated 2026-09-10T12:18:23.474361+00:00. The final review record and artifact hashes
are saved separately in `completion-review.json`.
