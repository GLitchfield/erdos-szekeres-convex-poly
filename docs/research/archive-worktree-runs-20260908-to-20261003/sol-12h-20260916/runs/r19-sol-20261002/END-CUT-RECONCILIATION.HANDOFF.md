# Inherited end-cut state reconciliation

2026-10-02, codex:01a0fc94-0467-7b90-823c-bce1e6fe6128. Exact target is inherited
ctx_bound_attained_by_end_cut_of_four_le, locked type90cbc8f14c117817. It asserts
an end-child cut sum at least the full bound for every WellFormed multi-run
context with both global parameters >=4. No bound>=2 hypothesis is needed.
The stronger full-PEEL raw witness already contradicts this inequality; the
actual-history k6 witness also contradicts it. No new mathematical proof idea
is needed for a false statement, and no new Lean theorem credit is claimed.

Research window-d43f0ec140164ad7 ended accepted0; this grants no new theorem.
Claim released REFUTED after completed separate review. New branch
node/CtxBoundAttainedByEndCutOfFourLeR19 starts exactly at
e3c87197b66a65092e1ffe5e9d0d8c7aa1981cf8, branch job20261002-162850-d18e2a DONE.
The existing same-name-without-R19 branch, R18 branches and all accepted R19
pins are untouched. Only its existing falsifier source changes. No Lean source,
root import or locked statement was edited; no merge/push.

The old falsifier samples only two external levels. This misses both known
witnesses. The new first stage replays two fixed, independently Lean-certified
WellFormed contexts using research.compiled-context-bound and
research.singleton-cuts. Both orientations/all legal couplings at the global
first/last positions are retained, including zero parts. Complementary end
intervals have the same sums after orientation/summand exchange. The existing
generated scan remains available if regressions do not refute the statement.
The fixed-only flag supports bounded replay, with scope explicit in its output.

Pilot20261002-163007-29e069 is terminal FAILED/rc2, the expected counterexample
convention: outer0.2s/13MiB, fixed computation0.011142s. Both output rows present.
Raw(4,4,5),3U4LSS1L2USS/maxima1111: diagnostic B2, all12 end sums1.
K6(5,5,6),SSS1L3L2LS/maxima111: diagnostic B8, end maximum7 over16 cuts.
No infrastructure error, missing output or dropped generated coverage is claimed.
END-CUT-RECONCILIATION.regressions.json records exact rows and cut values.

Official es falsify --async --mem4G --targeted job20261002-163119-f885b2 is
terminal FAILED/outerrc1, the harness convention for COUNTEREXAMPLE/innerrc2.
Immutable result6e699acc6d48b6b07ce9da642b26390c277fb7ad88f44e7ee65a72406d789c99
is copied fully in END-CUT-RECONCILIATION.falsify-result.full.json. It records
both witnesses, unchanged locked type, scriptSHA
eba1b4e8fd7a6bc666e0d1497a099451dfbe3edbf37677064190a8ae5ed66535.
Falsifier0.1s, fixed arithmetic0.008534s. Outer seconds/peak are absent in
kind-falsify metadata and are not invented. No infrastructure failure.
On this correction branch, live es status marks refuted/notready/lock_ok,
stale=[]/problems=[];
END-CUT-RECONCILIATION.live-verification.json records it. Targeted node-show
retains the prior indexed pass by design; live status is authoritative.
The falsifier result is tracked per checkout. An independent e3baseline branch
retains the old pass until this pin is integrated, even though the shared journal
records the refutation. Do not claim global integration or edit other branches
to simulate it. ABSENT-FLANK.final-verification.json records the baseline status.
Pinned4bd6580007983864837acf6bf65930f709d04c21, commitjob20261002-163348-346775
DONE. Parent exactly e3c87197; clean tree; exactly two changed files, falsifier
and its recorded result. Every inherited Lean/root/lock/index file is byte
unchanged. No further test/replay is justified. All owned jobs are terminal.

Lean evidence is separate: raw full-PEEL negation receipt
9159d9e9c8b436a7edd362410be34693c221562de3d85dcfca000cbb2c7ee3f5
certifies WF, bound>=2 and every singleton sum1, not exactB2. K6 receipt
37353e1f739a6742ee72aa641913fdcf267f1bdadc569e67d87be88a4f097f51
certifies WF/Satisfies, bound>=8 and all16 global-end sums<=7. ExactB8 has
receiptf2d86d2b78a2888f86ed602b7adc5c32e04d850e5616102b720b5348c4a89c38;
actual history has receiptd882dc65055b3a1af3920b833c3e518df688494e481c51e80b25075ff88f965d.
No separately compiled conjunction or exact inherited-universal negation was
added. These existing receipts already imply failure of the inherited formula.

Search before changes found exactly the inherited statement, no new lemma
was written. Catalog/API/source for shared compiled evaluator and singleton
enumeration were read; no new evaluator, validator or workflow driver was made.
Only two small fixed candidates and their result adapter were added. Separate
review window-c79b87deedbf4382 inspected final source, result, journal commands
and exact pin; END-CUT-RECONCILIATION.CODE-REVIEW.md records reuse/no-promotion.
General feasible
singleton attainment is still open without an invariant or proof idea.
