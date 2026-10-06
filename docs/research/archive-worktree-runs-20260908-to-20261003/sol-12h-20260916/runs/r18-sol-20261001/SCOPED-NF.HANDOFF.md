# R18 scoped root normal form

At 2026-10-01 23:25Z: ORIGINAL-SOURCE CLOSED AND COMMITTED.
Commit38cda637947e39072344ec0e81d5214bfd3e8940, job192456-a15599 DONE,
exactly module/rootimport/lock, left_uncommitted=[], clean git status.
Final normalized original audit191354-1ea077 DONE518.7s2403MiB, compiler
57.6311s/nestedpeak0unmeasured; exacttype1933d0914d56fe0c/lock/noholes/std-only,
nonstandard/uncovered/blocked empty. SCOPED-NF.FINAL.DONE.RECEIPT.json SHA256
c59f01da1a95a9783041cf5a400980b5ececc02d05bda6fcc192b6118150d5cd;
finalsource SHA25620f144b2bad092ebe56942a95509c9623e0620ec5686b79150c585d1c4686a52.
Source body-v6 differs from standalone acceptedv5 only by2spaces removed on
blank line3504/module3539. Full final source was rebuilt/re-audited. Localcap
restored byte-exact20G and diff--checkPASS before commit. No candidatebundle
installed. Claim release CLOSED after recording this final handoff.
Node `ctx_one_level_root_bound_normal_form_of_axis_two_or_saturated`, exact
type hash `1933d0914d56fe0c`, own main-based branch
`node/CtxOneLevelRootBoundNormalFormOfAxisTwoOrSaturated`.

The statement retains all original ROOT-NF hypotheses and adds only
`a = 2 ∨ u = 2 ∨ m = k - 2`. For legal positive globals bounded by k,
k>=3, legal old maximum 1<=m<=k-2 and a word containing only children
and ext 1 side, the full recursive bound equals the endpoint-preserving
normal word's full bound. It retains one child per run, clamps at three
if either global is two, and at two otherwise. Physical run lengths and
separator multiplicities are unrestricted. Empty/unit/single-run behavior,
including the unused lower-side default, is preserved. No extra WF premise.

The direct proof first handles unit globals, empty words and one run.
For multiple runs and opposite global two it establishes the exact Boolean
criterion: old maximum <=k-3 and chosen global >=3+endpoint-count, with
one extra required unit when both ends are unmarked and there are >=3 runs.
A chosen global <=2 instead forces zero. For saturated maximum k-2,
the exact value is one iff the opposite global >=3 and the chosen global
>=3+[both ends marked]. It then proves the normal word preserves run
thresholds, physical head/last marker presence, and inherited context fields.
All auxiliary functions are local proof terms; no restricted NF premise.

Local complete carrier proof accepted in job20261001-184447-76e39a,
op-94b398a69124455d:76.76796s,2118MiB,standard axioms only.
Stage9684c249b3bc39a0b384f1f0605f4d02bd4e269997d9dec640065a74530ea1a8;
bodyd64308067f6e0a98cb1c95f7725ef32dc9f49842f9a6e28ffa5448cf741c7719.
This carrier acceptance grants no independent public-node credit.
SCOPED-NF.v3.ACCEPTED.STATUS.json/RECEIPT.json/compile.log preserve evidence.

Earlier scope glue checks failed on folded marker endpoint tests and folded
inherited fields, then one negative endpoint test under simp only. The final
repair explicitly transports a/u/k and includes ne_eq. Full failures are
preserved as SCOPED-NF.v1.FAILED and v2.FAILED; no mathematical counterexample.
Latest standalone body is ROOT-NF-AXIS-TWO-OR-SATURATED.body-v5.txt (3676 lines).

Registration20261001-184852-7d3aa3 DONE415.8s2299MiB/noOOM. All3327 build steps
completed; placeholder was expected OPEN/sorryAx. Temporary local8G cap was
restored byte-exact to20G before capture. Inherited repair preserved all378
statement type hashes/types and fixed19 metadata records; durable
LOCK-REPAIR.scoped-root-NF.json and registration lock/config backups.
Closed proof imports were added before fresh fixture
c6b5640b79e2f48061907a61f9b5a765bc6856f336a0526ce0c0808084161f10.
Standalone original-parent check20261001-185645-ad5b02/op-6f391cc96a144303
ACCEPTED61.6804s2114MiB, exacttype1933d0914d56fe0c/std-only.
Stagea618799c7c22a4a1010d86a253f46f55266a48c03853c7fb88aef1475f89a1f1,
body0b802d58a429d0e738ed0250312e43c0f02cb5a78f7c4f3d57638def212f81b1;
SCOPED-NF.standalone.ACCEPTED.STATUS/RECEIPT/compile.log preserve evidence.
The identical body is installed, byte/hash checked, source has no holes.
Guarded20G targeted original audit20261001-185919-3fd4fd DONE515.4s2397MiB,
compiler59.1665s. Nested peak0 is unmeasured, not zero memory. The exact audit
is CLOSED/type1933d0914d56fe0c/lock_oktrue/sorryfalse/std-only, with empty
nonstandard/uncovered/blocked sets. SCOPED-NF.DONE.RECEIPT.json and
SCOPED-NF.ORIGINAL-AUDIT.JOB.DONE.json preserve evidence.
Reservation matched configured nested20G cap. Initial admission wait cause
was unverified; it subsequently started without worker intervention.
Fresh installed fixture3ec39cb0bcbbbfcd06017d5a8da5c9cf9a544ce7ced0560b7549462aeef1f9f6.
Extra local marked-global-three exact candidate is being checked; it does not
change the registered scope or installed public body. Commit/release next.

23:15Z update: marked-global-three extra local check191046-3c1a82 ACCEPTED
63.0641s2118MiB/std-only, stagef4cea43bdbb9a21675ffe197fd95f59b6d15ae6b342d0458917cb0fa575e76d7.
No carrier installation. Commit191227-eaa757 failed0.3s59MiB only at trailing
spaces on one blank proof line3539; no commit. Removed exactly2spaces
(bodyline3504), git diff --checkPASS. Prior original receipt/source preserved
as SCOPED-NF.pre-whitespace-original.*, normalized candidatebody-v6.txt.
Final exact-source audit191354-1ea077 is running8G; temporaryLOCAL build cap8G
matches enclosingguard and measured2397MiB prior peak. Restore byte-exact20G
against SCOPED-NF.final-whitespace-audit.config-original.toml.txt afterterminal,
before commit/capture. Same full targeted audit; no semantic/coverage change.

es search "root normal form axis two or saturated sibling maximum" returned
no indexed hit; the shared index is stale, so the original targeted type and
receipts are authoritative. No full extract, merge, push or delegation.

General ROOT-NF and C1r remain OPEN. Actual general NF v8 has full smaller-root
equality IH and three holes. Prepared v12 integrates this scoped equality
without restricting that IH, but is uninstalled/unchecked. The remaining
legal domain has k>=4, both globals>=3 and m<=k-3: both paired-cut upper
orientations and normal-form lower remain open. Two-level parts are outside
the one-level IH domain; independent contraction of all reachable complements
is invalid (locally kernel-certified12-to9 example). Joint cut transport or
reoptimization still needs proof.
