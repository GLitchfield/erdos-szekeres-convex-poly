# R18 active boundary chosen-global-three unit upper

At 2026-10-02 00:24Z: public original-source audit CLOSED and committed.
Node ctx_bound_le_one_of_active_boundary_marker_and_chosen_global_three.
Exact signature ACTIVE-BOUNDARY-GLOBAL-THREE-UNIT.signature-v1.txt,
67-line body-v1.txt.

Contract: arbitrary raw context with positive physical extension labels; an
actual indexed marker x of level N whose side is s; chosen global<=3; and
all active children (both point capacities positive) on one side of x.
The direction is a Boolean: true means p<x, false means x<p. Conclusion:
every fuel approximation and the full recursive bound are <=1.
No WF, legal maxima, opposite global bound, uniform word, run count, or
younger-marker geometry is required. Inactive children may lie anywhere.

Proof: a singleton indexed-marker sublist witnesses chosen left or right
extension>=1. At an active child, chosen global<=3 forces global exactly3
and total chosen chain exactly1. All active children therefore share rank2
when x is left, or rank1 when x is right. Apply CLOSED
ctx_bound_le_one_of_common_singleton_rank for every fuel and full bound.

Local carrier20261001-183852-f77ad9/op-e9643e6573a54bab ACCEPTED10.29095s,
2103MiB,standard axioms only. Stage
821f070632736d907f1ec02506dd03e5774e138b44986c07f7f4237e96ab5289;
body3c9942a8fe729720b82fa7776a303728bc16de0b39612fc6ba8212b3cf221921.
ACTIVE-BOUNDARY-G3.v1.ACCEPTED.STATUS.json/RECEIPT.json preserve evidence.

Search before writing found existing active boundary rank-pair/rank-union
contracts with extra younger-marker geometry. Latest search CAS
aed962941305884b981e34b1ca167c18276b749f9bc3caa1e52445154a5c359d inspected;
R16 CLOSED inventory/direct contracts contain no identical simple export.
Shared index stale; no full extract. Reuses core left/right sublist witness
construction and CLOSED common-rank theorem; no new workflow algorithm.

Use: upper bound for chosen-global-three one-level roots with a marked word
end. Its local version already participates in locally accepted exact marked
classifier191046-3c1a82 (bound0 ifbothendsmarked, otherwise1), and joins the
new locally accepted unmarked exact2 classifier194757-d9f82a. The complete
public chosenG3 normal-form driver and actual induction update are unchecked.

Own main-based branch created by200357-f744a6 frommain4a990c3f159168994ae08f4cbff511e952371df0,
afterCEXcommit/release and allownjobs terminal. Reused inherited metadata
repair0.24s/378records/19restored with every typehash/typepp invariant;
LOCK-REPAIR.active-boundary.json and inherited pernode backup preserved.
Registration200435-bdc31f DONE415.6s/2300MiB/narrowCommonRankimport;
exacttype7994790d52c34481. Config8->20 restored byte-exact before claim,
headeroptions/open and freshfixture
bba243ec47d08b0e82b8fcf153565183c7596f86a7e12ffe8cf40e4822042b15.
First standalone body-v1 check201237-770242 failed3.7618s/449MiB at one
dependent-match conversion in its final CommonRank call. Logged/preserved
PUBLIC.v1.FAILED.STATUS and diagnostic8989d09038f48b4131108fad142aef6e163315a175f47a4fcba47052b50d7867.
No mathematical counterexample or changed hypotheses. Body-v2 makes the
final side cases explicit:71 physical lines. Public check201437-f1b7ae/
op-6fb27d3a993f4a62 ACCEPTED7.7923s/2102MiB/exacttype/std-only;
stage6dcc0e589fce9d31b1480d2f4e7656a809bc5d4ec17ef77d40664cba645c40d7,
bodyf1f3bf435a848071326a2ff23086ec17a6ba05ff8f2c0d3caa6475ee7e151805.
Identical body installed/diff--checkPASS; PUBLIC.v2.ACCEPTED.STATUS preserved.

Final original audit201540-74c207 DONE398.0s/2366MiB/noOOM,
compiler4.1965s/nestedpeak0 unmeasured. CLOSED/exacttype7994790d52c34481/
lock_oktrue/sorryfalse/standard axioms only; nonstandard/uncovered/blockedempty.
ACTIVE-BOUNDARY.FINAL.ORIGINAL-AUDIT.RECEIPT.json SHA256
8ae909ef916134eb34bbc7f3764b36435cca2bdfecdd912f79da28984fd893d9;
source ACTIVE-BOUNDARY.final-source.lean.txt SHA256
23ab40fb9437ba10069358cd4ca308b7c7495ffb3f7a49c80175613295e4d405.
Local build8->20 restored byte-exact/cmp and diff--checkPASS beforecommit.
Commit202347-f72d79 DONE, SHAa1696a16ed13e116cfb8f263505b7892113d848a,
exact3nodefiles/left_uncommitted[]/clean. Claim releasedCLOSED with thishandoff.
Eleventh original-source CLOSED AND COMMITTED; generalNF/C1r stillOPEN.

The proof-only explicit-side fix propagated to future artifacts:
chosen3NFbody-v3 (6181physical lines/noholes), actualNFv16 (6349/threeholes),
Opp3publicNFbody-v2 (10877/noholes), privateOpp3carrier-v2 (10977/noholes).
All whole drafts still UNINSTALLED/UNCHECKED; actualgeneralNFv8 authoritative.
Registered generalNFstatement and FULLP(n) byte-exact invariants checked again.
