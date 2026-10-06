# R17 accepted independent theorem inventory

R17 is active. X remains open; this inventory claims only the closed helpers
below. Every commit has direct approved parent
5847e155fa613d4d2311eaee86b4b094f630e9a4, standard axioms only, matching locked
type, original-source targeted check, and released closed claim. No integration
or push. One registered node per independent branch.

| Theorem | Type hash | Commit | Original targeted check |
| --- | --- | --- | --- |
| ctx_one_level_root_outside_pair_leaf_threshold_agreement | c0ded5f538e4991b | f3c21cb85f0eccc1a21ad2d5b1be4583f44e26d8 | 20261001-101508-cb8b72 |
| ctx_one_level_root_inside_pair_leaf_threshold_mono | e0edc5ff21a26055 | dff190112c32d08f2648a74d2aa6b397cde08b9b | 20261001-103958-ef6757 |
| ctx_outside_pair_single_run_complement_bound_agreement | 3bd69f1808f1dcb | 9905f302ac33e05a31abda1a3cba3445adcc5266 | 20261001-112811-271572 |
| ctx_one_level_root_singleton_base_exchange_unit_axis | cfa5c55a7200eb09 | b55ab7cbe98190f87d2f583c337d7a36180b2c76 | 20261001-114533-4b9cdf |

The first theorem gives exact leaf agreement outside the pair in arbitrary
WF contexts. The second gives leaf monotonicity inside the pair when another
child exists. The third gives raw complement equality outside the pair when
the actual complement has at most one run. The fourth proves the full X
inequality when either global axis is at most one. It includes its registered
actual-domain falsifier and result:102144 cuts/145920 leaf audits/zero failures.

The current compiled environment represents only the current branch, not
this entire inventory. Future parent composition must import exact committed
dependency declarations and preserve their registered locks and open status.
Isolated complete-parent checks and frozen receipts/reviews are in this run.
Sol self-review is performed; independent Astra is forbidden and deferred.

There are twelve closed independent theorem commits as of00:33UTC Oct2.
The current branch is refined X ff30, with two strict residuals still open.
The tenth commit requires the exact independent inputs1/8; direct parent5847
alone does not contain their source modules. Its assembly is explicit below.

5. Full X when old chosen global axis<=2: commit
   fac5fc67d0d3417ee0de71dfca46f9986d4570a0, parent5847e155fa613d4d2311eaee86b4b094f630e9a4,
   type2a67a6c76ffd76d3,7files,clean atcommit,claim released closed.
   Isolated124529-2ad7e9/op-3e27ce880b024c1e; original targeted124644-6cb79a,
   receipt d32f65668cbbec79c08eb2c676f96c77fc5deab2dc14c1c2ebdb250595a1002f,
   closed/lock_ok/no uncovered axioms,5.721s603MiB4G.
   Actual-domain falsifier115632-75eac4 passed114688 selected cuts/256000 audits.
   Accepted bodyc13879e49740965b32f83eb8f5684acf72798e4a09dcab326a9ec4998208400c.

6. Full X for positive-axis outside-pair one-run complement: commit
   b2584679e9ec6723983084fca19d1e5a2c0a161b,parent5847e155fa613d4d2311eaee86b4b094f630e9a4,
   typec9478fa33072e959,7files,clean atcommit,claimreleasedclosed.
   Isolated125339-719c2d/op-8abc2880da5046f6 accepted firstcandidate;
   original targeted130242-35fceb,receipt
   0a2669c9195fc6d392cbfe262bfca7f9325005835e3792100b34ddfcac735442,
   closed/lock_ok/no uncovered,4.905s628MiB4G.
   Actual-domain125302-349e2d passed5888cuts/235520audits.
   Body8948cc151746ce381ea252334020156c83ee700c6713b0327eb38ad052805ba0.

7. Finite same-leaf/global inside-pair forced-orientation obstruction:
   ctx_one_level_root_singleton_leaf_only_selector_counterexample.
   commit3b8a2dce55b334284f9908183eb79df833d6b723,
   approvedparent5847e155fa613d4d2311eaee86b4b094f630e9a4,5files,clean.
   Lockedtype5bf8d6c3f662df4d. First isolated142847-bdac15/
   op-268de19162b04fae accepted8.062s/2100MiB/4G;
   fixture683983dbba5a1c172ce23ebeccca277d6cbd4f2bc1d57ba5f096bee77e15a32d,
   body004439f27b0e2b8eaa995a85f90b7833f481e2f9e26e5cb1373986d98ac897d9.
   Original143341-7b14b1 passed5.305s/825MiB/4G,closed/noholes/standard
   axioms/no uncovered or tag errors, receipt
   22500f3b5287b3fd98d269025d69be6f301f1bdd6659851fcbbc60f79930b243.
   Commit143629-55b3cf done; claimreleasedclosed. It certifies two original
   source6/leafcap3cup1 witnesses and opposite rescuing orientations for
   every legal target coupling, without refuting X. No finite-table axiom.

8. Inside-pair explicit leaf monotonicity under two child runs:
   ctx_inside_pair_leaf_threshold_mono_of_two_runs.
   commit463b7f9d5fa23db7733a0fe8c0fa303f5fdbdeb6,
   parent5847e155fa613d4d2311eaee86b4b094f630e9a4, exactly5files.
   Lockedtypeca8c8fa7a2e9b812. Whole-parent163942-45f6a8 accepted
   6.796s/2105MiB/4G; original164623-f18764 passed70.0s/2372MiB/20G,
   receiptce6b5ddc0fd3a8b248008a1ad060e4c5fb07fdd4cbdd86ed0756de0c29cb3b29.
   Closed/noholes/standardaxioms/no blockers/tagerrors; commit164844-f31df7
   completed and claim releasedclosed. Derives the surviving-child premise
   from two runs. This is an adaptation to X's actual premise, not a broader
   domain than the old explicit-child helper, and not full-sum exchange.
   Exact source archived as inside-two-runs.closed-source.txt.

9. Every proper part vanishes at a large indexed maximum with opposite
   global axis at most two:
   ctx_proper_part_zero_of_large_sibling_maximum_and_opposite_global_two.
   commit1edc5c9ff9ef7856bc45cc9d575c41eb31b62804,
   parent5847e155fa613d4d2311eaee86b4b094f630e9a4, exactly5nodefiles,
   lockedtype5818b07d53e26989. Whole-parent175800-10103e/
   op-e57d4e9d89af4401 accepted7.75s/2104MiB/4G, receipt
   eafcce44cde54b175844f3621b325d3e76de622407d5b8079bae6eac3776b5bc.
   Originaltargeted175912-d53273 passed51.5s/2345MiB/20G,0OOM/missing/
   budgetexceedance, receipt
   51865331b549b5e0bede01c2384876adc360faa0f47e7166928a13346bb321de.
   Full original/node receipts confirm closed/noholes/standard axioms,
   lockmatching/no blockers/tagerrors; commit180546-2ff8be verified and
   claimreleasedclosed. Positive labels/indexedmaximum>=k-2/opposite<=2
   and one omitted sourcechild; arbitrary keep/newside/newmaximum, no
   multi-run/WF/occupied-old-level/legal coupling premise. Exposes the
   internal closed R16 proof without modifying any R16 node/source/job.
   Exact acceptedsource92138c415f2f9329c37431779d9e8347b041986604a33181e6d5eb3754046a78
   archived as proper-part.closed-source.txt. Failed by-span candidate,
   CLI/parser setup and corrected commit-audit wording remain in the log.
   Guardedreturn180656-b73431 passed exact Xarchive/clean-state checks.

10. Full singleton-value same-cut transport at source-opposite global<=2:
    ctx_pair_contraction_singleton_value_mono_of_opposite_global_two.
    commita7e7b6b71bc3dbce0b16e459c4103c91b66ccc3a,
    directparent5847e155fa613d4d2311eaee86b4b094f630e9a4, exactly5nodefiles.
    Lockedtypeef8f2f46dd387851. Whole-parent184449-42278a/
    op-293d16a06a794bd5 accepted7.379s2103MiB4G, receipt
    3ccb3b848d4ffb58fd68d6648e2e3e56c87cfab07487a6276eb664ac0da83a1a.
    Originaltargeted184653-5922f6 passed93.0s2368MiB20G,0OOM/missing/
    budgetexceedance; fullreceipt
    92302e1ab69aeca7b33d4fe7ccf5a0bf97e29208a9cfb96543b3a3695e629c7d
    confirms Std/closed/noholes/type/lock/no blockers/tagerrors.
    Commit184915-ba8c0d verified and claimreleasedclosed. Arbitrary WF,
    >=2runs, adjacentchildpair, legal sourcecut, globaloppositeSOURCEcut<=2.
    Fresh actual indexed marker kills sourcecomplement, then closedleaf
    comparisons transportthreshold at the identicalside/coupling. No old
    maximum/one-levelhistory restriction and no targetCmonotonicity assumed.
    Requires outsideleaf1(f3c21c) and two-runinsideleaf8(463b7f9) modules;
    exact prior approved lock entries were restored without type edits.
    Bodyff91e00c699abd4cb6277e22e18d801ca5bd5187a5acec896764e9ee6f2a1cca;
    acceptedsource07b69bd4980d4c0d8cfba04fb606c70c086e73de85ee003451ce43b9e60d676f
    archived as opposite-source-axis-two.closed-source.txt. Failed first
    elaboration candidate184230-24a5be retained. Guardedreturn185006-4c93f7
    passed exact Xarchive/clean-state checks; it is not yet composed into X68.

11. Raw-context actual-marker consumed-axis zero, every fuel and full bound:
    ctx_actual_marker_chosen_global_two_zero.
    commit bb4647871239844a3438ab7b7c11418991b11443, direct approved parent5847,
    five node files, type dae6380c2e356e7c, clean tracked tree at commit.
    Actual indexed occurrence plus consumed global Lower→u/Upper→a<=2;
    no well-formedness, positivity, one-level-root, maximum or legal-cut premise.
    Isolated complete-parent195721-89a38e accepted7.7377s/2101MiB/4G;
    original targeted incremental200508-c89b5b passed48.9s/2342MiB/20G.
    Exact source edbd8d6a5ed8c38296720c7689fbbe4d00fce2aae7aa5833786e13922411ec58,
    original receipt file SHA bce19150c8647ddfcbed892f2fccefcf0e6bda191ed8337f57e88da41e3566e5.
    Closed/no holes/standard axioms/matching lock/no blockers or tag errors;
    original and actual-Git audit JSONs retained, claim released closed.
    Source archive actual-marker-zero.closed-source.txt; independent base imports.
    Not an additional required input of the already checked refined X.

12. Numeric axis information is necessary beyond a cap-at-three selector:
    ctx_singleton_exchange_capped_axes_selector_counterexample.
    commit a1de7d72dd9f7f0c180a73bfffbbf8d6316bb300, direct approved5847,
    five node paths, type ee2218b99f3247d4, clean tracked tree at commit.
    Same literal S,1Lower,S,S geometry/capped axes, globals(4,5)/(5,4),
    k6/m1/Lower source4, source7 both; each has a legal rescue but no common
    target side/coupling does. Ordinary kernel decide plus all8 legal cases;
    no native_decide/table axiom, not a refutation of X or a universal rule.
    Complete-parent202919-18c130/op-3b3fd6725e054ce3 accepted8.434s/2102MiB/4G.
    Original targeted incremental203012-ff6c0b passed52.1s/2346MiB/20G,
    receipt31b0ff44133c82b1747cb0e3f293e17d42d742d59f11a206087f30ce4d47b05b,
    exact sourceedccc2808005382c3c559f972c5cf4d63824db9110a09b7985f70bffb80ababa.
    Closed/standard axioms/no holes/matching lock/no blockers or tag errors;
    actual Git audit and accepted-source archive retained, claim releasedclosed.
    Independent base imports; not a new required input of refinedXff30.
