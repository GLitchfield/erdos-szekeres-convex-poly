# R21 progress

Researcher: `codex:agent-run-bef3c92bee6b417b`; thread
`01a0fe0f-bbf0-7a53-b71b-d7f6bfd74e21`. Baseline `6e4d0e66`.
Effective research deadline: 2026-10-02T23:34:06.656638Z, approved early finish.
Finalization hard stop: 2026-10-03T00:04:06.656638Z. The original deadline
2026-10-03T07:20:39.240366Z and consolidation time were superseded by the
coordinator/user instruction after all results were reviewed.

## Final verification — 2026-10-02 23:36Z

No new research or compiler run occurred after the early finish. Existing
original-source receipts and job states were rechecked: all three targets
closed, exact locks intact, no sorry, only propext/Classical.choice/Quot.sound.
All three current source hashes match their accepted and committed bytes.
The frontier is fresh with zero problems; the worktree is clean and no
researcher jobs or claims remain active. Coordinator review reference supplied
by the user: `898cacb2cc898d6f542760b1a2bc7933a322fc`.

Monitoring window `window-57469c43b8994b9c` ended accepted=0; direct session
usage was synchronized. Finalization review window is
`window-9b7d5d80cdae43c1`, with no additional theorem credit. The mathematical
handoff names all proofs, source receipts, commits, failures and limits.
The native goal is now complete after verified finalization; the supported
compact final report follows. Integration is left to the coordinator;
no merge or push occurred.

## Verified results checkpoint — 2026-10-02 22:19Z

All approved mathematics is certified and committed: single-set bound
`adf3b2f1`, exact conditional four-diagonal state `05ba7924`, and optional
color dual `77ec6962`. The proof uses one-change chain promotion and the
cup-plus-apex invariant, then applies the quadratic bound to the whole
decomposable set. No mathematical obstruction remains for R21; the general
cap-parameter family is outside this proof's scope.

Original-source checks `20261002-154314-8d501b`, `20261002-165002-e99108`,
`20261002-172932-0a1eb5` certify the exact locked types without sorry and
with only the three standard axioms. The compiled frontier is fresh with zero
problems; the worktree is clean, claims released and all researcher jobs terminal.
`MATHEMATICAL-HANDOFF.md` is the consolidated current account;
`MATHEMATICAL-HANDOFF-HISTORY.md` preserves the earlier chronology.

The saved parity diagnostic also exhibits consecutive cap0124, with right
012/124 but left024. Thus OneChangeOn is needed for the no-all-triple-cap to
no-consecutive-cap step as well as the gon-to-strong step. This is ordinary-code
diagnostic evidence, logged without claiming another Lean result. The port
README now points to all three final source checks and commits.

The native goal remains active under its fixed deadline. No more compiler run
is needed without a changed source or new concern. Remaining work is the
scheduled consistency/accounting consolidation and compact report. Run-review
usage ingestion conflicts with explicit phase assignments; direct full-session
usage synchronization works. Preserve assignments and do not treat unavailable
inventory totals as zero cost.

Final mathematical review window `window-17527a1de5524727` is complete
(accepted=0; results are credited only in their three research windows).
Monitoring window `window-57469c43b8994b9c` records scheduled standby with
an observational 10,000 output-token target. At 23:00Z the host still reports
the unchanged 07:20:39Z deadline and no active researcher jobs. Current
consolidated handoff snapshot: immutable log attachment
`f7771711b9bd9cf20546bb68e3051156a756720f5c86126c99f0995cf6897b8a`.

## 2026-10-02 19:23Z — startup

Read AGENTS.md and RESEARCH-BRIEF.md in full. No prior R21 research jobs or
proof receipts exist. The live host job is `20261002-152034-e81b35`.
The context index reports stale fingerprints; an initial guarded incremental
extract will determine whether a full refresh is needed before registering work.

Current proof idea: port Baek's alpha/beta-label induction and interweaved
laced-cup theorem, then bridge its ordered-list cap/cup gon to the project's
strong finite-set polygon under `OneChangeOn`. This should give
`card <= 1 + choose (k-1) 2` in a 4-cap-free, strong-k-free set, for `k >= 3`.
The substantive bridge obligation is chain promotion and the strongness/cardinality
of the union of two chains sharing endpoints. No new theorem is certified yet.

Next: register and claim the single-set bound on its own node branch; port the
source in scoped Mathlib-only helpers with per-file Apache-2.0 attribution.
Then use the conditional Pascal-tail shell to assemble `(4,k,k)` for `k >= 5`.
The upper tail has width zero. R20's lower gate remains an explicit hypothesis.
No R19/R20 branch, worktree, or node is being modified.

## 2026-10-02 19:28Z — registered node and first port evidence

Branch: `node/CardLeChooseOfOneChangeNoCapFourNoStrong`.
Node: `ErdosSzekeres.card_le_choose_of_oneChange_no_capFour_no_strong`.
Statement hash: `17d2458e770c2e45`; claim held by this researcher.
Registration `20261002-152323-76d3f2` passed with a targeted extraction.
Initial frontier refresh `20261002-152224-5de722` passed (203 MiB).
Branch creation `20261002-152234-660d20` passed.

Baek source is preserved and hashed in `baek-port/source-manifest.json`.
The port will live inside the registered node module; separate untagged
ESBlueprint helper modules are rejected by the harness. The current standalone
Mathlib-only files under `baek-port/` are diagnostics for that source body.

Leaf check `20261002-152546-170eb1` failed on modern constructor parsing and
field notation for nested List helpers. Inspection corrected the namespace
plan: prefixed List/Finset extensions in their actual type namespaces, Config
and its proofs in `ErdosSzekeres.Baek`. Recheck `20261002-152757-545631`
passed; the full Mathlib-only main check is now submitted.

The bridge has a simpler proof idea: no four-cap forces Baek's gon cap chain
to have length two or three. This leaves a k-cup or a (k-1)-cup with one cap
apex sharing endpoints. One-change propagation determines union triple colors
by the middle vertex; the apex is excluded from the cup by the opposite
endpoint triple. This avoids needing a general two-chain union theorem.
The project node still has its registered sorry; no theorem credit yet.

## 2026-10-02 19:39Z — source theorem and structural bridge compile

The full Baek `main` port passed Mathlib-only check `20261002-153221-05028a`:
its exact axiom list is `[propext, Classical.choice, Quot.sound]`. The preceding
failed checks (`20261002-152847-73ba26`, `20261002-153105-7091d8`,
`20261002-153149-aae592`) were specific API/simp repairs and are logged.
The first full attempt is preserved as `baek-port/BaekMathlib.initial.lean.txt`;
the accepted diagnostic source is `baek-port/BaekMathlib.lean`.

The port is now embedded in the registered node module, alongside private
project bridges. The generic one-change chain promotion compiled in build
`20261002-153332-ace1ef` (the outer wrapper subsequently refused its final 30G
stage above the 20G enclosing cap, so the wrapper itself is not a success
receipt). Chain adapters and IsCupSet/IsCapSet conversion passed diagnostic
`20261002-153535-1c15b4` on the original source.

Cup-plus-apex strongness passed `20261002-153850-6aa1ed` after two strict-index
if-condition goals from `20261002-153731-942943` were repaired. The mathematical
invariant is now compiled: every triple in the union turns right exactly when
its middle vertex is the cap apex. This yields both strong equalities directly.
No new axiom, certificate, or native_decide has been added.

The registered cardinal theorem remains open. Its complete candidate proof is
`baek-port/SingleSetBody.txt`; proof capture/check is next. The assembly goal has
not yet been registered; its lower gate will remain a hypothesis.

## 2026-10-02 19:45Z — single-set theorem certified; full-index recovery

The complete candidate passed isolated original-source proof check
`op-c4d15e58009f4b2e`, job `20261002-154155-82ff5c`. Finalization operation
`op-8fd70671be5c456f` then passed candidate job `20261002-154254-ad8b35`
and actual-source targeted check `20261002-154314-8d501b`: the registered
statement is closed, hash `17d2458e770c2e45`, no sorry, and only the three
standard axioms. The complete target proof now lives in the registered module.

The remaining full-index stage `20261002-154414-813658` failed because its
default imports require the missing `ErdosSzekeres.olean` root, while the
extractor builds only the ESBlueprint target. This is a fresh-worktree build
prerequisite, not a mathematical failure. Guarded job `20261002-154541-37c842`
is restoring the configured ESCore target; resume the same finalization
operation afterwards. The claim remains held; no commit yet.

The phase-2 proof is simpler than the proposed predecessor assembly: the
single-set bound applies to the entire decomposable set, because
`IsDecomposableOn.turnSequenceAllowed` supplies OneChangeOn. At `(4,k,k)`
the threshold is `1 + choose (k-1) 2`, so a larger cap-four-free set directly
contains a strong k-set. The requested lower-gate hypothesis can remain in
the exact signature without being used. Only the binomial-window identity
and this direct implication remain to formalize; no R20 integration is needed.

## 2026-10-02 19:57Z — measured core-restoration optimization

The restoration checkpoint showed a startup bottleneck: at ten minutes, 244
serial guarded invocations had succeeded, but long cached dependency chains
were only near segment 018 of 255. At about 1.8 dependency levels/minute,
roughly 130 minutes remained. Their logs show native-cache fetches; the entire
ESCore source is unchanged from baseline.

The checkpoint decision and stopped coverage are recorded in `es job review`
and `es log`. Serial job `20261002-154541-37c842` is terminal (`killed`,
requested cancellation); its fetched outputs are retained. Replacement
`20261002-155725-92b804` builds the SAME full configured ESCore target using
the existing `es build core --no-serial` path under the same 30G guard. Its
budget is derived at launch from the user's fixed research deadline. This
changes execution, not the mathematical obligation or imported sources.
After it succeeds, resume `op-8fd70671be5c456f`; full-index closure stays open.

## 2026-10-02 20:00Z — full-core recovery complete; extraction retried

The first parallel attempt refused before Lean because cancellation left two
storage leases. Supported reconciliation job `20261002-155833-bc8423` checked
the exact stopped scope and released both: `unknown_execution=[]`, no external
effects retried. Its receipt and the refusal log are in `reservation-recovery/`.
Requeued `20261002-155725-92b804` then restored the full core in 12 seconds
using native cached outputs, peak 680 MiB, rc0. `ErdosSzekeres.olean` is present;
the completion log is in `core-restoration-parallel/`.

The failed workflow needs explicit `operation retry`, rather than `resume`.
Operation `op-8fd70671be5c456f` is retrying only full extraction in job
`20261002-160005-c336e7` (attempt 2); accepted candidate and source stages
were preserved. Audits/review and the first commit are next after extraction.

## 2026-10-02 20:20Z — single-set finalized and reviewed

`op-8fd70671be5c456f` succeeded all stages. Original-source check
`20261002-154314-8d501b` closes unchanged hash `17d2458e770c2e45` with only
standard axioms. Full extraction `20261002-160005-c336e7` returned
`frontier_fresh=true`, `problems=[]`; allowlist and layer audits
`20261002-161845-f1fb21` have no failures/violations. Review artifact
`20261002-161859-dd9e36` is accepted and unpublished, with source SHA-256
`94758a5127d9da310118d1d5bf04d0ed2a768edad877b9e23b3f2e43bd5d2a77`.
The claim was released closed automatically. The first commit is next.

Separate code/library review `window-7373e4889c364aa7` is documented in
`CODE-LIBRARY-REVIEW.md`. No recurring algorithm or new execution framework
needs promotion: the source preparation is explicitly one-off, and execution
reused shared APIs. No tracked workflow script changed. Original source
provenance recheck passed all 18 bodies; the earlier missing-venv attempt and
premature log were corrected explicitly before the successful check.

## 2026-10-02 20:24Z — single-set committed; diagonal registration started

Commit `adf3b2f1f1e0875dc59057e7abfd46be219d88da` closes exactly the
single-set node on `node/CardLeChooseOfOneChangeNoCapFourNoStrong`.
Commit job `20261002-162156-adb838` passed and left no uncommitted tracked
changes. The source, root import, lock, nodes, and status are the only files
in that commit. No merge or push occurred.

Phase-2 research window is `window-1f56fe4fe55046ba`. Branch-creation job
`20261002-162302-b578fa` passed; current branch is
`node/DecomposableStateUpperFourDiagonalOfGates`, based on the single-set
commit. Registration `20261002-162428-b8907e` is pending for the exact
requested gate-conditional forall-k state. It imports the minimal
`StructuralChargingPascalTails` interface and declares the closed single-set
dependency. The candidate `baek-port/DiagonalStateBody.txt` is still unchecked.

## 2026-10-02 20:31Z — required gate interface exceeds targeted closure limit

Registration `20261002-162428-b8907e` elaborated the exact signature, then
refused targeted extraction: the minimal `StructuralChargingPascalTails`
interface has a 28.4 GiB object closure, above the configured 4 GiB limit.
The source stub/root import were retained; no lock or claim was established.
Replacement `20261002-162620-50ff52` is registering the unchanged statement
through the ordinary full-extraction route in a 28G guarded job.

Source inspection also shows `node finish` always chooses targeted source
checking, so it would encounter the same ceiling. After successful registration,
claim the node, import the committed single-set module, capture/check the exact
candidate, insert only its accepted proof body, and use full `es check` plus
audits and `es node commit`. These are existing supported commands; no limit
override, statement change, or new workflow implementation is planned.

## 2026-10-02 20:50Z — exact diagonal candidate accepted

Full registration `20261002-162620-50ff52` succeeded. The exact approved
signature has hash `8a8c8eaac2a011d3`; its claim is held by this researcher.
Capture `20261002-164647-f0e109` pinned the source and dependencies in fixture
`cde2cefc033c776ec43cd182b35dadc594bc1dd4cf8527e6725c2a5ffa157ea1`.
Isolated proof check `20261002-164739-f7c8e6`, operation
`op-001b20713f8646f6`, accepted the complete candidate with only standard
axioms and the unchanged type hash. No mathematical repair was needed.

The accepted body uses whole-set OneChangeOn, the already certified bound,
and the exact three-term threshold identity. The gate hypothesis is retained
but unused. Shared `proofs.assembled` and `finalize.preflight` inserted only
the captured proof span; `diagonal-finalization/insertion.json` records the
identity, source hash, and accepted receipt. Original-source full check
`20261002-165002-e99108` is pending under a 28G guard. Final project closure,
audits, review, release and commit remain outstanding; isolated acceptance
alone is not the final receipt.

## 2026-10-02 21:05Z — original-source build and hypothesis diagnostic

The exact diagonal source built successfully inside
`20261002-165002-e99108`; full extraction remains in index formatting. Its
ten-minute checkpoint is on track against earlier approximately nineteen-minute
full runs, with a diagnostic estimate of nine to ten minutes remaining.
No check is being narrowed or stopped.

Fixed parity-witness job `20261002-170418-461953` passed in 0.1 seconds.
On Fin5, right iff the triple index sum is odd yields no all-triple cap4
and no strong4, yet card5 exceeds the proposed bound4. Quartet0123 is RLRL.
This explains why OneChangeOn is required for the bridge from Baek's gon to
project strongness; a cap014/cup024 gon has non-strong union0124. Evidence is
ordinary-code diagnostic only, not Lean theorem credit. Semantics, shared
evaluators, structural parity explanation and exact output are in
`parity-witness/`. The registered target is unchanged.

## 2026-10-02 21:08Z — requested uniform state closed in original source

Full check `20261002-165002-e99108` succeeded: 1052.6 seconds, peak 5704 MiB.
`diagonal-finalization/source-check.json` reports closed, no sorry, standard
axioms only, unchanged type hash `8a8c8eaac2a011d3`, matching statement lock,
and `targeted=false`. The complete index is fresh with zero problems.
Source SHA-256 `383673715f23c362195b19aaeffbfe4acaaa3064c5f965b1e6f756ec41bd0d09`
matches the isolated accepted candidate; the committed single-set source hash
is unchanged. The required mathematical result is now original-source certified.
Audits, separate code/source review, claim release and commit are next.

## 2026-10-02 21:10Z — both required targets committed; optional dual next

Audit `20261002-170811-d4a30d` passed with no failures/violations. Separate
review `window-dc0da6abc7784922` pins the exact accepted assembly in artifact
`3282828854a31abf87f12abdb7ec9e64388a3c0b9b221484a8b8cee8ddee1982`.
Claim released closed with this mathematical handoff. Commit
`05ba7924a4ba74089e6ce1f396126cddbaeefca8`, job `20261002-170947-db7d40`,
contains exactly the diagonal node and its root/lock/index/status records;
no uncommitted tracked changes remain. No merge or push occurred.

Both required R21 targets now have original-source receipts and commits.
Native goal remains active until the user's fixed deadline; it will not be
marked complete early. Optional color dual research window is
`window-fec772473d794228`. Its proof uses existing `decomposableStateUpper_comm`;
search found no proposed-name duplicate. A separate node branch is being
created from the certified diagonal commit; no R19/R20 state is touched.

## 2026-10-02 21:11Z — dual registration running

Branch `node/DecomposableStateUpperDiagonalFourOfGates` was created by
`20261002-171028-5412d4` from commit `05ba7924a4ba74089e6ce1f396126cddbaeefca8`.
Full registration `20261002-171102-7dd5ce` is running at 28G, review ten minutes.
It imports the committed requested state and registers the same gate binder
with conclusion `forall k, 5 <= k -> DecomposableStateUpper k 4 k`.
Prepared `baek-port/DiagonalFourDualBody.txt` uses only existing color duality.
Claim, capture, isolated/full checks and review follow successful registration.

## 2026-10-02 21:28Z — dual registered and candidate checking

Full registration `20261002-171102-7dd5ce` succeeded. Exact dual type hash is
`9fbc31b5eb51b848`; status open/ready, lock approved, index fresh with no problems.
Claim is held by this researcher. Capture `20261002-172722-0386f3` produced
fixture `b81e683b25929484caf2d465743cfc23199f97ac13dbbb930bd5fd20c193c8b1`.
Candidate check `op-a70d22fb0d42419f`, job `20261002-172749-6b4c46`, is pending.
The proof applies existing color duality to the committed uniform state;
the exact original source still has its allowed sorry. Original-source full
check, audits and separate review/commit follow candidate acceptance.

## 2026-10-02 21:29Z — dual candidate accepted and inserted

`20261002-172749-6b4c46` accepted the exact dual body, unchanged hash
`9fbc31b5eb51b848`, standard axioms only. Candidate source SHA-256 is
`1575ca2c4b3b9c0f5c8321eae172606e092fdaf15fa8f365b88c41bc0d69699d`.
Shared `proofs.assembled` and `finalize.preflight` inserted only its accepted
proof span; `dual-finalization/insertion.json` records the pinned identity.
Original-source full check `20261002-172932-0a1eb5` is running at 28G,
review ten minutes. The exact insertion command is archived in
`dual-finalization/INSERTION-RECIPE.py.txt` for separate code review.
Audits, separate review, claim release and commit remain before final credit.

## 2026-10-02 21:48Z — optional dual closed in original source

`20261002-172932-0a1eb5` succeeded: 1023.2s, peak5662MiB. The exact dual
is closed, no sorry, standard axioms only, unchanged hash `9fbc31b5eb51b848`,
matching lock, full route. Index is fresh with zero problems. Source hash
`1575ca2c4b3b9c0f5c8321eae172606e092fdaf15fa8f365b88c41bc0d69699d`
matches isolated acceptance; the first two committed source hashes are unchanged.
All approved mathematical results are original-source certified. Final audits,
separate review, claim release and dual commit remain.

## 2026-10-02 21:57Z — all approved results committed and reviewed

Dual audit `20261002-174759-82d42d` passed. Review window
`window-aaf19fdf62ef405c` pins its source/assembly in artifact
`e0a9967bbec97ce9df4d5b3bb65e44c85c7f8a2e71e1b52c9131e95a01d71657`.
Claim released closed. Commit `77ec6962881731dcbabe99ad6f33a2e01f72e270`,
job `20261002-175001-204507`, contains exactly the dual node and its harness
records; worktree is clean, with no active researcher jobs or claims. Both
required results and the optional dual have complete original-source receipts.
All three source hashes still match isolated acceptance and their commits.

As-of inventory `20261002-175213-dcbe10`, artifact
`6fb9ad1cf39a0310ef97a3b91b14d09a7980375920e304acf0cab61edd11f9e5`, covers
the parent artifact directory and recorded commands. Its only pending job was
itself, now terminal. Its usage ingestion refuses reassigning requests already
in explicit phase windows into the umbrella window; unavailable/zero totals
are not cost evidence. Direct session sync succeeded, recorded in
`final-review/usage-sync.json`; no assignments or usage limits were reset.
The inventory includes unchanged upstream files and Lean sources as scripts;
all new/changed code and archived insertion recipes are reviewed in
`CODE-LIBRARY-REVIEW.md`. No tracked workflow script changed.

The newer release handoff was preserved as immutable artifact
`a2431f60792107d9623c54ceb2b5afb68085e09c904c394c374b2be808cb511b` when an
older primary-checkout copy already existed. The live worktree handoff is
authoritative. Final mathematical review window is `window-17527a1de5524727`.
The native goal remains active solely under the fixed deadline contract;
consolidation is scheduled for 06:50:39Z and completion cannot be marked before
07:20:39.240366Z. No approved mathematical obligation remains.
