# R14 Sol report

Part 1 narrowing is **Done**. Part 2 is **Stuck** after two consecutive failed
lifting attempts at the same obligation, under the brief's stop rule. N_root and
X remain open. No full Done claim or native-goal completion is made.

Agent codex:01a0f4c8-720d-7fe2-afe2-0052a6bdd4b4; Sol xhigh, no delegation.
One trial. Coordinator-ended research deadline2026-10-01T00:57:33.947017Z;
finalization hard stop01:27:33.947017Z. The original12:06:12.335613Z deadline
was superseded by the coordinator's early finish, not extended by this session.

## Changed and committed

Each branch starts independently at main4d0be1b72911. Nothing merged or pushed.

| Change | Commit | Targeted check | Outcome |
|---|---|---|---|
| Register N_root | 763b4b67730ef5e3c8215ec5c441bb7b84979a41 | 20260930-201226-c5e3cf | Type81be57bce6e33074; compiling conjecture |
| Explicit N_root+X conditional | f575ec7269a34e65846110120a6d3e68a3fdce6f | 20260930-201714-9a8260 | Typefdf891b82544f272; closed, standard axioms only |
| Compose existing C1r | 9262f92e48bad197df1c1462064ff2f067bdfb40 | 20260930-202121-ffa3b9 | Type94e83f4b24e9975d unchanged; no local sorry, transitive sorry through N_root/X |

The closed conditional is the sole new accepted theorem. N_root registration
and C1r composition give no closed-theorem credit. Integration must bring the
first two separate commits before the C1r module; its targeted check used
byte-identical committed dependency source overlays, subsequently removed.
C1r's check was closure-only (incremental=false), not a full frontier refresh.
Existing statements were not edited. All compiler work was memory-guarded.

## Diagnostic research

N_root falsifier20260930-201130-95f7bd passed5976 declared roots,127472
singleton cuts and127472 explicit-threshold audits. Scope and complete output:
FALSIFIER.n-root.json. This finite arithmetic is not Lean certification.

First lifting attempt, job20260930-203426-6088a8: internal-block shrink fails
for (3,4,5,1), S L SS L SS, middle B=[2,3], optimal outer value1+2=3,
where all strict internal subblocks after reoptimization give at most2.
Attaining singletons exist outside B. The same job also exposes the unit/unit
single-run split boundary: (3,3,4,1), SS L SS, prefix upper1 has bound1 but
every proper further cut gives0. Both roots still satisfy N_root.

Second attempt permits rotating to any of three whole pieces of every
attaining inner cut. Cold timing203852-88f833:0.704s,249MiB for a five-child,
five-run k6 root. Sweep203944-6341ad completed728 exact five-child roots,
11228 eligible optimal cuts,50 failures across25 root rows;307.194s,257MiB.
At its five-minute checkpoint715/728 roots were done; the review recorded an
estimate6-20s remaining and the job finished unchanged.

Positive-component witness: (3,4,5,1), S L S L S L SS, B=[2,4] lower c2,
outer1+2=3. All12 attaining inner cuts isolate2 or4; every root cut isolating
either, after full orientation/coupling reoptimization, is at most2. R=[0,6,7]
is not an original interval. An outside singleton7 upper c3 attains3.
All25 retained failed-rotation roots still have an attaining singleton.
This refutes the restricted lifting law, not N_root or every possible
minimal-optimal-cut proof. No third mathematical attempt or trial was started.

Independent Python recurrence replay jobs204700-42ee55,204828-4db107 and
204828-2be80b reproduced the unit boundary, internal shrink and whole-piece
rotation witnesses respectively:0.109s/22MiB,7.934s/34MiB,9.257s/33MiB,
complete=true,zero mismatches. AUDIT.*-python.json and FAILED-ROTATION-WITNESS.json
retain exact values; these are diagnostic arithmetic, not Lean certification.

## Limits and next action

The exact remaining replacement law is: for a legal one-level root and an
attaining proper interval B with both outer parts of size>=2, there is another
proper original interval K with |K|<|B| and a legal reoptimized side/coupling
whose cut value is at least the root bound. It is unproved. Restricting K inside
B or to the three whole nested pieces is false in the retained families.
An eventual proof must also handle the single-run unit/unit split loss.
Read MATHEMATICAL-HANDOFF.md before resumption; the brief's two-attempt stop
remains in force. Coordinator review is received. Safest next action is a separately
scoped proof route permitting complement refinement and an outside block. Do not repeat
R13's minimum-active-capacity or fixed-position selectors.

The worktree Git metadata is read-only to this sandbox; guarded worker jobs
made branches and commits. The harness unexpectedly copied one cited release
handoff into the primary runs directory; this is logged. No primary source
was edited. Future releases cite receipts and this report carries handoff paths.
Full extraction, merge, push, model change and delegation were not performed.

All owned compiler, research and verification jobs are terminal; N_root and C1r
claims were released partial. The conditional claim was released closed earlier.
Current branch: node/CtxOneLevelRootBoundAttainedBySingletonCut; tracked tree clean.
Main advanced independently during the run; all three commits' direct parent is
the required immutable base4d0be1b729110f969f78ee88e77fd970f82173e8.

REVIEW.receipt-source.json verifies committed bytes, frozen source/type hashes,
whitespace, direct parents, and unchanged C1r statement/docstring. Self-review
caught and corrected an unexecuted misplaced audit branch and a mutable-main
comparison; both intermediate artifacts are retained. No Lean compiler failure
occurred. Code review reused shared mathematics and es execution/proof/commit
APIs; refuted one-off rotations and fixture-specific adapters were not promoted.
No library/catalog change is warranted. An Astra review cannot run under the
explicit single-Sol/no-delegation rule. Coordinator outcome review is now recorded
in COORDINATOR-REVIEW.json and the host state: Part1 Done, Part2 Stuck, ending early.

Research window7e3932fdc6b84ad4 ended with1 accepted theorem. Mathematical/code
self-review used window9d7251efd05a4851; library maintenance/reporting is separate
windowf1ec6b3decf14505. Usage was imported, but active/late reporting can lag.
The factual research-window snapshot reports100 responses,95387 output tokens
(48985 reasoning tokens included),317737 uncached input tokens; it reports no
linked job resource totals because these jobs lack explicit window links.
Use the individual job receipts for elapsed time and peaks. Setup, failed routes,
recovery and review are included in session imports; no matched baseline or
savings claim is made. Final usage receipts are saved alongside this report.

Self-review snapshot:13 responses/15822 output tokens, exceeding its observational
10000-output target. Maintenance/reporting snapshot:6/9302; later reporting may
raise it. The three USAGE.window-*.json files retain the full factual snapshots.
Compact host review artifact438958e77c0e5735a66fe206979e632a8d10e16621c169b83188a1aa6bbf4f99
inventories files but has0 linked jobs/explicit proof receipts: its researcher id
is codex:agent-run-d72f94dce1234fc9, while this session consistently used
codex:01a0f4c8-720d-7fe2-afe2-0052a6bdd4b4. Its baselinec589080a also includes
older changes. Use the explicit check receipts and REVIEW.receipt-source.json
for theorem acceptance and R14 scope; identity history was not rewritten.

The diagnostic/verification job IDs abbreviated above are:

| Job | Evidence |
|---|---|
| 20260930-201130-95f7bd | N_root targeted falsifier, pass |
| 20260930-203426-6088a8 | Internal-shrink and unit-boundary fixtures |
| 20260930-203852-88f833 | Cold five-child rotation timing |
| 20260930-203944-6341ad | Complete728-root rotation sweep |
| 20260930-204700-42ee55 | Python unit-boundary replay |
| 20260930-204828-4db107 | Python internal-shrink replay |
| 20260930-204828-2be80b | Python whole-piece rotation replay |

The native goal is paused after the coordinator's early deadline. It is left paused:
N_root is still unproved, so the full proof objective is incomplete. This finalization
turn performs no new research and starts no checks; all owned checks were already
terminal and their receipts were inspected again. Final host inventory artifact
448b242a169f0e728dba21459874f27399cf93c514fffc764087f028466b2c7b retains the
coordinator early-finish state; its identity linkage limitation remains as above.
No callback is verified or promised. The recorded outcome is independently supported
by the explicit targeted receipts, source fixtures, commits and witness replays.
COMPLETION-AUDIT.md records the continuation's requirement-by-requirement current
state audit. It confirms Part1 narrowing is complete and Part2's proof is incomplete.
