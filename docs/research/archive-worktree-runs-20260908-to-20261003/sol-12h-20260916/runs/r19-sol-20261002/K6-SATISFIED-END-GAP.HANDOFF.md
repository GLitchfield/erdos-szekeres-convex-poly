# A satisfied k6 context requires more than a global-end cut

2026-10-02, agent codex:01a0fc94-0467-7b90-823c-bce1e6fe6128.
Node ctx_k6_satisfied_end_cut_counterexample, independent branch
node/CtxK6SatisfiedEndCutCounterexample, base
e3c87197b66a65092e1ffe5e9d0d8c7aa1981cf8, unchanged typee482c53a7d35a688.
Registration20261002-115600-64a5bd, fixture
d1ddd4ad8c6d47a7315eef5ca62c9869880679dcf44f934e41864a855e788b3c.
Pinned commit8e2f72ce9b0ae129609f051661313b7bee767dcf,
commit job20261002-123327-1634d8 DONE, with exactly this node's five files.
Final source check20261002-122611-18dca1 is DONE/CLOSED; claim released CLOSED.
Receipt37353e1f739a6742ee72aa641913fdcf267f1bdadc569e67d87be88a4f097f51,
compiler223.023s, outer259.2s/8613MiB under20G. The saved original-check and
final-verification JSONs assert exact source/body assembly, type and lock,
standard axioms, no sorry and no blocked/uncovered dependencies. A first
verification parser used unsupported lock_status and failed; the actual
lock_ok and explicit statements.lock entry were checked in its logged repair.

## Exact mathematics

The literal context is(a,u,k)=(5,5,6), SSS1L3L2LS, maxima111, children[0,1,2,6].
The theorem certifies WellFormed, Satisfies for the constant-right coloring on
Fin4/univ, bound>=8, and that every first/last child cut (p0 or p6), both
orientations and all four admissible couplings, is strictly below that bound.
The finite proof checks all16 end sums<=7. It does not export exact parent
bound8, uniqueness of the middle attainer or exclusion of the extra run-end p2;
those remain diagnostics from PEEL.cost-profiles.json. It also does not assert
realization of the entire external history by planar points or a decomposable
coloring. Satisfies constrains the four children. Capacity8 is not their count.

Constant-right means every cup has at most two points: any three ordered
vertices would require right=left. Every cap has at most four points. Every
strong subset has at most four, below k-1=5. Kernel calculations show cup
limits>=2 and cap limits=4 at all ordered child endpoints, so these cardinality
facts imply Satisfies. Reverse endpoint pairs are deliberately excluded.

The lower bound uses an explicit cut tree, avoiding evaluation of the entire
four-child maximum. First isolate p1 on upper with maximum3; its value is2.
Let tau be the lower remainder with maximum2, child positions[0,2,6]. Isolate
p6 in tau on lower with maximum3; its value is4. Its upper remainder rho,
maximum2 and children[0,2], has bound>=2: cut p0 on lower with maximum1, and
the complementary upper singleton has maximum4; their sum is2. Three uses
of existing ctx_bound_cut_le and Nat addition monotonicity certify
rho.bound>=2, tau.bound>=6 and sigma.bound>=8. They do not prove those
inequalities are equalities. The two last singleton leaf values sum to2.

This supports the k6 explanation in PEEL.MECHANISM.md: removing the middle
child separates the early surviving children into two unit runs, while the
old last run retains threshold capacity4. The remainder has three runs in
total. An end deletion leaves the early survivors contiguous and loses one
unit. Raw endpoint-limit loss alone does not select the optimal child: the
last-child lower remainder can lose no limits and still have smaller capacity.

The inherited ctx_bound_attained_by_end_cut_of_four_le uses global first/last
positions (four refers to its global parameter lower bounds, not four run
ends). This exact satisfied witness contradicts that route mathematically,
even if a Satisfies premise were added. No separate compiled universal
negation or modification of that inherited node is claimed here. Arbitrary
singleton selection under actual history constraints remains open; the raw
universal PEEL was already refuted separately.

## Evidence and failures

Instrumented original check20261002-122050-540a3f is DONE/CLOSED, receipt
88fac84f6f23b82f0930b921826c0d7fed308e99a868b88577cb93832cae05fd, parsed in
K6-SATISFIED-END-GAP.instrumented-original-check.json. Standard axioms only,
no sorry, matching type, no blocked/uncovered dependencies. Compiler225.670s;
outer guarded job263.9s, measured peak8643MiB under20G. Nested build peak0
means unavailable nested measurement. run_guarded uses the enclosing scope;
this was not an observed4G-then20G retry. Final source removes diagnostic
filesystem writes and is checked separately before its commit.

Initial check20261002-120611-283b1e and structural/abstract-arithmetic checks
20261002-121353-e4bfee /20261002-121540-b7b7ef each hit the4GiB guard at
17.965/18.544/18.860s. Durable localization identified the end calculations
as the expensive stage. Splitting finite limit checks and avoiding omega on
closed bound expressions did not themselves repair the memory problem; the
lower cut tree remains a useful proof simplification. No configuration or
statement changed to grant a result.

Stage1 diagnostics20261002-120925-2ababe /20261002-121102-b9a652 failed
3.373s/576MiB and3.474s/551MiB because omega/norm_num left forbidden reverse
endpoint cases. Retaining the ordering premise in each closed finite
implication solved them. These temporary blueprint bodies contain explicit
diagnostic sorries and grant no theorem credit.

Diagnostic tree job20261002-121131-e63a53 failed after its scans because the
shared evaluator has no .semantics attribute; its output was missing. Repair
20261002-121203-d4fb1c completed, using the documented semantics literal, and
K6-SATISFIED-END-GAP.cut-tree.json preserves all24+16 choices. All these
numbers were diagnostic until the cut inequalities and leaf sums compiled.
Memory-localization job20261002-121930-23bbc3 failed at unknown liftIO before
producing progress; standard liftM repaired the temporary instrumentation.
Available failure logs and successful artifacts are preserved. The first full
numerical body was edited during repair rather than separately frozen; its
exact failure is supported by the compiler/job logs, not a recoverable original
body artifact. Current final assembly is byte-verified. Temporary stage1 and
memory-localization body artifacts are preserved separately.

## Reuse and remaining review

Semantic search "satisfied context end cut counterexample" identifies this
node and no prior satisfied witness. The existing raw end-cut refutation and
ctx_bound_cut_le provide the relevant approach; single-run searches are saved
in K6-SATISFIED-END-GAP.single-run-search.json. Reused Finset.orderEmbOfFin,
Fin.card_Iio and the existing cardinality/rank definitions. No new statement
is added outside the registered ESBlueprint node.

The diagnostic script k6_cut_tree.py is a fixed one-context composition of
shared compiled_evaluator, part and singleton_cut_values. It does not implement
a new recurrence or execution framework. Its metadata failure and repair are
documented in the job journal; the failed complete script was not independently
frozen before its one-field repair. Proof assembly uses es.proofs. Separate Sol
code/library self-review is recorded in K6-SATISFIED-END-GAP.CODE-REVIEW.md;
independent coordinator
review remains pending under the no-delegation contract. Do not promote this
one-off mathematical composition solely to grow the catalog.

Audit/layers pass and all378 inherited lock objects remain unchanged, exactly
one new entry. Preserve the ignored runs/r19-sol-20261002 artifact root with
the pinned branch. No merge or push. The native goal stays active until its
fixed deadline; any later scope question must preserve these receipts.
