# R21 mathematical handoff — all approved results certified

Researcher `codex:agent-run-bef3c92bee6b417b`; native thread
`01a0fe0f-bbf0-7a53-b71b-d7f6bfd74e21`; host `20261002-152034-e81b35`.
Authority: `/home/gavin/git/erdos-szekeres-convex-poly/runs/worktrees/sol-12h-20261002`.
Source and `runs/es-operations/` paths resolve from that worktree; other
evidence paths resolve from its `runs/r21-sol-20261002/` artifact directory.
An older primary-checkout handoff copy is a historical snapshot.

Both required targets and the approved optional dual are original-source
certified, with no sorry and only `propext`, `Classical.choice`, `Quot.sound`.
Claims are released; researcher jobs are terminal; the worktree is clean on
`node/DecomposableStateUpperDiagonalFourOfGates`. No merge, push or R19/R20
worktree/branch/node modification occurred. No approved mathematical obligation
remains. The coordinator/user approved early finish at
`2026-10-02T23:34:06.656638Z`, superseding the original research deadline
`2026-10-03T07:20:39.240366Z`. The native goal was paused for this single
finalization/report turn, with hard stop `2026-10-03T00:04:06.656638Z`.
Existing receipts, terminal job states, clean worktree and committed source
hashes were rechecked after the early finish. No new research or compiler run
was started. Coordinator review reference supplied by the user:
`898cacb2cc898d6f542760b1a2bc7933a322fc`; the compiled receipts below are the
independently inspected evidence supporting final completion.

Native-goal status was updated to complete after these finalization checks,
within the revised hard stop. Recorded goal elapsed time is 15,207 seconds
(about 4 hours 13 minutes). All approved obligations are supported by the
receipts below; the compact final report is ready.

## Accepted theorems and exact receipts

All names below are in namespace ErdosSzekeres. Commits form a chain from
baseline `6e4d0e66`, with exactly one closed node per commit and no statement edit.

| Result | Type hash | Original-source job | Commit |
| --- | --- | --- | --- |
| `card_le_choose_of_oneChange_no_capFour_no_strong` | `17d2458e770c2e45` | `20261002-154314-8d501b` | `adf3b2f1f1e0875dc59057e7abfd46be219d88da` |
| `decomposableStateUpper_four_diagonal_of_gates` | `8a8c8eaac2a011d3` | `20261002-165002-e99108` | `05ba7924a4ba74089e6ce1f396126cddbaeefca8` |
| `decomposableStateUpper_diagonal_four_of_gates` | `9fbc31b5eb51b848` | `20261002-172932-0a1eb5` | `77ec6962881731dcbabe99ad6f33a2e01f72e270` |

The single-set statement is: k at least three, OneChangeOn on s, no four-cap
and no strong k-set imply `s.card <= 1 + Nat.choose (k-1) 2`, for arbitrary Fin n.
The exact requested state takes `forall k, 5 <= k -> SingletonLowerPascalTailGate 4 k k`
and returns `forall k, 5 <= k -> DecomposableStateUpper 4 k k`. The dual retains
that same hypothesis and returns `DecomposableStateUpper k 4 k` for every k at least five.

Sources are `ESBlueprint/C/CardLeChooseOfOneChangeNoCapFourNoStrong.lean`,
`DecomposableStateUpperFourDiagonalOfGates.lean` and
`DecomposableStateUpperDiagonalFourOfGates.lean` in that directory. Their SHA-256s:

- Single set: `94758a5127d9da310118d1d5bf04d0ed2a768edad877b9e23b3f2e43bd5d2a77`.
- Requested state: `383673715f23c362195b19aaeffbfe4acaaa3064c5f965b1e6f756ec41bd0d09`.
- Dual: `1575ca2c4b3b9c0f5c8321eae172606e092fdaf15fa8f365b88c41bc0d69699d`.

All committed bytes match those accepted sources and the locks, verified in
`final-review/certified-results.json`, immutable artifact
`0225c2faff1a654a902c9c7046e4131a38446d97983360b490dc77924a5388bf`.
First source receipt is `runs/es-operations/20261002-154314-8d501b/receipt.json`;
its succeeded node-finish operation is `op-8fd70671be5c456f`, with full extract
`20261002-160005-c336e7`, audits `20261002-161845-f1fb21`, review `20261002-161859-dd9e36`.
The other source/audit/layer/review receipts are in `diagonal-finalization/` and
`dual-finalization/`. Audits `20261002-170811-d4a30d`, `20261002-174759-82d42d`
passed. Manual full-source-route review artifacts are respectively
`3282828854a31abf87f12abdb7ec9e64388a3c0b9b221484a8b8cee8ddee1982` and
`e0a9967bbec97ce9df4d5b3bb65e44c85c7f8a2e71e1b52c9131e95a01d71657`.
Commit jobs: `20261002-162156-adb838`, `20261002-170947-db7d40`, `20261002-175001-204507`.
Receipt inspection, not inventory or process counts, establishes the mathematics.

## Proof idea and what was learned

Baek's complete label/slope/lacing proof is ported. Beta is the longest ending
cup length minus one. Delta removes at most n+2 representatives of short beta
classes in the successor induction; Pascal leaves the previous quadratic
threshold in the complement. Label/slope laws extend interweaved laced cups
when an asymmetric join is absent; both join orientations otherwise supply
lacing directly. Lacing gives the gon. This is the compiled structural argument,
not a fitted numerical rule.

OneChangeOn promotes consecutive chain colors to all triple colors by induction
on the outer index span. Overlapping smaller triples agree on a quartet's outer
colors, forcing all colors to agree. Invoke Baek.main at n=k-3. No four-cap
forces its cap list to have length two or three, since a four-prefix would be
a forbidden cap. Length two leaves a k-cup. Length three leaves a (k-1)-cup
plus a cap apex q sharing extrema p,r. The union's triple color is right
exactly when its middle vertex is q; anchored one-change propagation proves
this rule and hence both strong equalities. Opposite endpoint triple colors
exclude q from the cup; sorted-list distinctness gives exactly k vertices.

The requested state needs no predecessor or child-tail induction. Decomposability
gives OneChangeOn on the WHOLE set, and the three-entry window satisfies
`T(4,k,k) = choose(k-2,2) + (k-2) + 1 = 1 + choose(k-1,2)`.
Thus the single-set bound directly forces a four-cap or strong k-set above
that threshold. The cup disjunct is unnecessary. The approved hgate binder
is retained but unused; callers still supply it to the exact exported interface.
Existing color duality proves the optional family. `PROOF-MAP.md` has source entry points.

OneChangeOn cannot be dropped merely because Baek permits arbitrary configurations.
Diagnostic `20261002-170418-461953`, in `parity-witness/`, colors Fin5 triples
right iff their index sum is odd. It has no all-triple cap4 or strong4, yet
card5 exceeds bound4. Strong4 would force two equal-parity ordered pairs,
requiring span at least five; Fin5 permits span at most four. Quartet0123 is RLRL.
Cap014/cup024 is a gon whose union0124 is not strong. This is ordinary-code
evidence explaining the bridge hypothesis, not Lean-certified refutation or
extra theorem credit.

The same saved triple table shows a consecutive cap0124 (012 and124 right,
024 left). Thus the no-all-triple-cap to no-consecutive-cap implication also
needs OneChangeOn; Baek.main need not return a gon in this witness. Both
bridge steps are independently explained by the law, without another probe.

## Failures, recovery and reusable limits

Port failures were API/namespace repairs, including List field notation,
Pairwise/Sorted, order-dual simplification, lt_or_le, coercions and simp.
Exact failed jobs and consequences are in `PROGRESS.md`, `MATHEMATICAL-HANDOFF-HISTORY.md`
and the shared journal. Failed compiler recovery's sorryAx output was excluded.
The cap-length reduction made a general two-chain union theorem unnecessary.

Full extract `20261002-154414-813658` initially lacked ErdosSzekeres.olean.
Serial whole-core restoration `20261002-154541-37c842` was stopped at a measured
checkpoint because cached-chain startup implied about 130 more minutes. Outputs
were retained; the SAME full target was restored by existing no-serial job
`20261002-155725-92b804` in 12 seconds. Supported reconciliation
`20261002-155833-bc8423` repaired stale stopped-scope leases, unknown_execution empty,
no effects retried. Explicit operation retry preserved accepted stages and succeeded.
Evidence: `reservation-recovery/`, `core-restoration-parallel/`.

Targeted registration `20261002-162428-b8907e` refused the required gate interface's
28.4 GiB object closure above the configured 4 GiB ceiling. Full registration
`20261002-162620-50ff52` recovered. Both large-interface nodes used shared
capture/check, exact-span assembly/preflight, full es check, audits and node commit;
node finish's forced targeted source stage would refuse. No configuration, lock
or limit override was used. Generic full-source node-finish support is deferred;
existing commands completed this run without another execution framework.

One missing-venv provenance invocation did not run; its premature log was
explicitly corrected before shared sha256_file verified all 18 used original
bodies. Receipt `baek-port/source-manifest-verified.json`. Do not rerun the
one-off preparation script over repaired source. Archived failed candidates
are documentary; the committed node module is authoritative.

## Provenance, review and accounting

J. Baek, jcpaik/erdos-tuza-valtr, commit
`a5ad53efefb36f8654b9227ce4dba2bf04a7ec3f`, Apache-2.0. The unchanged copy is
`baek-erdos-tuza-valtr-a5ad53e/`. Ported sections identify original files and
modification to Lean4.29.1. `CODE-LIBRARY-REVIEW.md` reviews the preparation
script, fixed parity evaluator, archived insertion recipes, Lean sources and
recorded commands. Shared APIs/evaluators were reused; no tracked workflow script
or new recurring algorithm was added. Configured gpt-6.1-sol/xhigh only, no delegation;
independent Astra review is not claimed under that explicit model contract.

Research windows: `window-77355285698d4a64`, `window-1f56fe4fe55046ba`,
`window-fec772473d794228`. Separate code reviews: `window-7373e4889c364aa7`,
`window-dc0da6abc7784922`, `window-aaf19fdf62ef405c`. Final mathematical review:
`window-17527a1de5524727`, complete with accepted=0. Scheduled monitoring
`window-57469c43b8994b9c` is also complete, accepted=0. Early-finish finalization
review is `window-9b7d5d80cdae43c1`; it verifies existing evidence and awards no
additional theorem credit. Available session usage is synchronized, including
failed/setup/monitoring work; reporting requests can lag the latest snapshot.

As-of review `20261002-175213-dcbe10`, artifact
`6fb9ad1cf39a0310ef97a3b91b14d09a7980375920e304acf0cab61edd11f9e5`, inventories
the artifact parent and commands. Its pending job was itself, now terminal.
Its usage ingestion refuses reassigning explicit phase-window requests into
the active umbrella window; unavailable/zero totals are not cost evidence.
Successful direct full-session sync is `final-review/usage-sync.json`; preserve
all assignments. No savings comparison is claimed. At dual release, an older
primary handoff conflicted; the newer snapshot was preserved as immutable
`a2431f60792107d9623c54ceb2b5afb68085e09c904c394c374b2be808cb511b`.
Use this live worktree handoff and accepted receipts for current status.

## Safest next action and remaining scope

Review/integrate the three commits in order, then provide the separately reviewed
singleton lower gate family to the exported interfaces. All approved R21
obligations are closed. The general happy-ending conjecture is not established:
a four-cap for large k is not itself a strong k-set, and this proof gives no
new uniform route for arbitrary cap parameters. No unresolved compiler failure,
active claim or queued research job remains. Finalization checked status,
source/commit hashes, exact receipts and available usage. Further compilation
is unnecessary absent changes or new concerns. This handoff and the compact
final report complete the approved R21 run under the revised deadline.
