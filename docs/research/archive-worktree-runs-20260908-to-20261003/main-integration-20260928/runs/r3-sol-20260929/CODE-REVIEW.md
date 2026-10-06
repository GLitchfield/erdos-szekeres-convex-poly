# R3 code and mathematical evidence review

Sol self-review begun 2026-09-30T00:46Z, window `window-de1a257b85a04dac`.
This is not an independent Astra review: the authorized run fixes Sol/xhigh and
forbids delegation. Independent coordinator review remains pending. No primary
checkout or shared library code was changed.

## Inventory and reuse

`review.pre-registration.json` references immutable inventory artifact
`6c9a50b1346eca8b0351ea12bb56ece2c28e8dd7be3846e17b490afc534f34bc`:
26 artifact scripts, no changed tracked scripts, three inline commands, and no
registered proof receipts at that snapshot. `code-manifest.final-gate.sha256`
also includes the subsequently archived Lean witness source. Inventory/process
success is not theorem credit. `es run review` must be refreshed after the node
check and commit.

Reused catalog contracts: `research.recursive-bounds`, `research.context-part`,
`research.context-extension`, `decomposable.context-enumeration`, and the retained
point-limit routine `limits_from_signature(..., lean=True)`. The generic
two-marker `workflow.recursive-cut-probe` domain did not match the four-marker
feature search; that mismatch was logged. Execution, reservations, outputs and
job follow-up use the existing es harness. Candidate definitions are separate
small drivers using the charge engine's explicit feature hooks.

The two benchmark inline programs call the reused compiled evaluator at fixed
words and varied memo limits, recording equal values and elapsed seconds. The
third is the placeholder dispatch smoke command, which receives no numerical
or theorem credit. Their exact commands are in jobs `20260929-194735-6432b4`,
`20260929-195053-b6947f`, and `20260929-193303-30e943`.

## Evaluator semantics

The local C change is restricted to allowing levels beyond the maxima length in
base evaluation, retaining them in word order while excluding them from indexed
extension and sibling-maximum folds. Indexed levels still enforce one side per
level. Recursion shifts all external levels and prepends the new maximum, so a
barrier remains unindexed after a cut. All physical child positions remain
explicit; proper intervals and their complements both reduce the child count.
Coupled maxima enumerate exactly `m+n=k-1`, with both positive orientations.
The evaluator includes zero-valued summands, matching the current Lean function
body; the old prose comment on `Context.bound` is not its arithmetic semantics.

The C memo is fresh for each call, the Python layer adds bounded top-level
caching, and no history is compressed. Indexed unused levels retain the existing
default-side behavior. Arithmetic overflow or allocation failures report errors;
no output is treated as a proof certificate. The scalar validation and saturated
extension arithmetic are intended here only for the small tested parameters,
not a proved arbitrary-integer implementation. Python rejects empty-child words;
the probe wrapper explicitly returns zero for them.

The adapted semantic label is
`context-bound-zero-children-c-unindexed-r3-v1`. The wrapper's inherited API
docstrings still mention the earlier label; use the explicit `SEMANTICS` constant
and result field. Preserve the executed files rather than silently rewriting
their recorded hashes. Cross-check job `20260929-193603-fca912` tested 158
indexed/pruned samples, not a general equivalence theorem. Independent Lean
runtime witness checks are jobs `20260929-203242-f56b7c` and
`20260929-204540-701aaf`.

## Feature and charge audit

`gate_probe.py` enumerates all four-marker permutations and child gap
compositions subject to its stated filters. Its clean family does not enforce
the original internality of q0, so its relation to the two actual source
admissions is an overapproximation. Larger requested child counts are only
credited when `max_children_completed` reaches them. Guarded timeouts preserve
complete smaller checkpoints and do not refute a predicate.

`inheritance_audit.py` uses exact strict saving as a relaxation. It is useful
for rejecting a potential but does not discover a geometric invariant. The
feature-check variants explicitly check source saving and recursive predicate
inheritance. `feature_check_random.py` stops checking a candidate after its first
failure; its counts are truncated by that rule. The later charge engine checks
all sampled matching sources and never evaluates full source B in its predicate.

The charge certificate excludes a single-run source through active mixed
capacity witnesses. Each group-pruned bound is an independent upper charge;
the capacity-three decomposition's Lean hypotheses are not inferred solely
from a successful Python audit. k7/global-rank-6 exploratory outputs require a
separate applicability audit. Source coverage and valid pruning support are
therefore explicit limits, even for a numerically successful audit.

`charge_ancestry_candidate.py` constructs legal interval/complement descendants
from internal-q0 ancestors and saves lineage. Its predicate reconstructs the
older cut in the projected color word and requires a valid younger interval or
complement at each level. Random generation samples sources; the recursive
audit then visits every cut of a matching source. This does not enumerate all
histories or prove that every needed admission context satisfies the predicate.

Driver imports intentionally replace the engine's candidate/feature globals
before `main`; their source hashes alone do not identify all transitive imports.
Use the complete manifest/inventory along with each job's exact command. The
engine's inherited `certificate_contract` paragraph describes the original
dense predicate; actual `features` and `candidates` fields and the driver code
are authoritative for later candidates. Older long sweeps used archived
`charge_certificate.v2.py`, not the subsequently edited engine.

Review caught a handoff error: adding the large-marker terminal branch repaired
the earlier failure cuts, while the final sources failed at the next maximum
splits. The corrected cuts are k6 lower2/upper3 and k7 upper4/lower2. Exact
Lean replay `20260929-204540-701aaf` confirms their numerical source saving;
`K6-GATE.md` distinguishes these from the earlier cuts. The final Fail verdict
is limited to the tested feature route; no universal noninheritance claim is
supported.

## Reflection proof review

`ReflectionAudit.reused.lean` proves precisely the requested statement. It
transports word positions by the bounded involution `length-1-p`; boundedness
is present wherever subtraction is inverted. Reversed child positions are the
reversed list mapped through that involution. A cut's keep list is a nonempty
proper infix, and its reversed image is reconstructed as such; complement
transport and `part` transport preserve side and maximum.

The proof only compares `base` in the single-run case. Convexity of physical
child positions follows from at most one run, including an explicit empty case.
The checked child-interval lemma gives constant point capacities across that
run, and checked reversal transport compares the old last child with the new
first. It never assumes unrestricted head-based base invariance.

Fuel induction compares every candidate cut with its reversed legal cut. Every
part uses `WellFormed.part` with the positive maximum and `<=k-2` side
conditions. Reversing again supplies the opposite inequality; equal child
counts give equality at the fuel used by full `bound`. The compiling named
audit `20260929-201544-f6a775` reports only `propext`, `Classical.choice`, and
`Quot.sound`. There is no admission, `native_decide`, or added axiom in this
proof. Registration, isolated proof receipt and targeted node check subsequently
succeeded; the final delivery review below identifies the accepted receipts.

## Final delivery review

Separate observational window `window-228a3bffc83d40b3`, begun06:10Z, records
the final Sol self-review. No independent Astra review was performed because
the authorized run fixes Sol/xhigh and forbids delegation. No further trial or
shared library change is authorized.

Immutable post-check inventory artifact
`bda11ab1fc70dc6575e8d348e3863b807ef4cafcc11646720736c8ffb3fbd66f` records
27 artifact scripts, one changed tracked script, three journaled inline
commands,57 non-host jobs, no pending/unknown jobs and no active own claims.
The new theorem is untracked because staging failed; it is outside both the
run-artifact root and tracked-script inventory. The whole module was therefore
reviewed explicitly. SHA256
`b7cedc2e2bd969ee0b96f5af992fbb59b43e8c29927c65f62dfbac7f171f59b9` equals
the accepted isolated candidate. The new root import and single lock entry were
also inspected; no other statement changed. Generated nodes/status files
contain another agent's live claim and are excluded from the delivery patch.

The only new inline workflow glue loads the existing Config/fixture APIs,
checks the accepted receipt against body and locked type hashes, invokes
`es.finalize.preflight`, assembles with `es.proofs.assembled`, verifies the
accepted full-source hash, and atomically replaces the registered source.
It does not compile Lean or run a mathematical search. This reuses the existing
finalization contract while omitting the forbidden full-extract stage; no new
general workflow implementation or library promotion is needed. Insertion
identity/source evidence is retained in `reflection.insertion-receipt.json`.

Inspected isolated receipt
`2a5679692abe8beb64bdd4555af34ac754ed7940d762716fda8902507a6bc36c` explicitly
accepts the exact body. Inspected original-module check receipt
`492f82808b20c3216db2349a8bbf5fca32262d1b5788e4579dc8cf0855ec0dab` reports
closed/sorry-free status, matching locked type `4125616738b08f1d`, only
`propext`, `Classical.choice`, `Quot.sound`, and no uncovered/nonstandard axioms.
Actual dependencies include the checked point-interval node and generated
auxiliaries in addition to the declared transport tag. This is a diagnostic
tag mismatch, not an additional hypothesis or axiom. No compiler failure or
unresolved proof concern remains; repeated compiler checks are not justified.

Authorized Git staging failed on read-only `.git-data/index.lock`; nothing was
staged or committed. The three-file `ctx-bound-reverse.patch` has SHA256
`1a51d350487e567157b49dcff2786067cf001a6f9c1476dd1b1bf5ae4ac947d0` and
passes `git apply --reverse --check` against current files. This verifies the
delivery artifact without changing Git metadata. Do not treat it as a commit.
The sole remaining implementation step requires a coordinator's writable host.
All-in usage stays in the canonical window; no duplicate phase import or
unsupported cost saving is claimed.

## Maintenance decision

Defer shared promotion: the user permits only run artifacts and the reflection
registration/proof in this checkout. The barrier-aware C evaluator may deserve
a shared extension with regression fixtures and a changed semantic contract,
but it is unmerged diagnostic code and no library promotion is authorized here.
Do not generalize the failed one-off ancestry predicates into the catalog.
The reusable charge-audit pattern can be reviewed by the coordinator with its
full manifest, original witnesses and fixed semantics. No next trial is begun.

Phase usage is recorded as a separate observational review window, with no
duplicate usage import; the host's canonical window and final immutable review
capture all-in setup, failed work, verification and waiting. A numerical
research/review split is not available from that aggregate accounting alone.
