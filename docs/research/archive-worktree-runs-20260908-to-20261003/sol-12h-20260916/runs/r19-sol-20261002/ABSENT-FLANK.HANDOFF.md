# Absent-flank hypothesis certificate

2026-10-02, codex:01a0fc94-0467-7b90-823c-bce1e6fe6128. Research window
window-f0aedbd4e9c24918 ended accepted1. Separate self-review
window-6b2828b4e84146fb ended accepted0. Branch node/CtxAbsentFlankSwapCounterexample
starts independently at e3c87197b66a65092e1ffe5e9d0d8c7aa1981cf8;
branch job20261002-163917-07f5a4 DONE. Previous pins and R18 branches preserved.

Exact obligation is the literal ctx_absent_flank_swap_counterexample in
ABSENT-FLANK.signature.lean.txt. At(5,5,6), wordSS, maxima1,2, both external
levels are absent. The exact label/maxima transformation from the accepted
FLANK-SWAP formula leaves the word unchanged and gives maxima3,2. Both states
are WellFormed; depth2, vacuous left/right positional flank predicates, equal
default sides and legal M3 all hold. Yet their bounds are10 and4.
This certifies insufficiency of positional predicates alone. It does not contradict
the accepted theorem, whose two nonempty-flank assumptions exclude the witness.

Proof idea: both contexts have one child run and no external walks. Chain
extension counts are zero. Absent levels still contribute declared maxima to
joinExt under the context API's default lower side. Cup limits are3 and2,
cap limit4 in both; thresholds T(5,4,6)=10 andT(5,3,6)=4. Finite kernel reduction
can certify the values. A general local WellFormed proof for two child letters
uses existing List.getElem?_replicate and legal maxima. Vacuous flank predicates
follow from empty extPositions. No new mathematical engine or selector narrowing.

Prior diagnostic20261002-083642-6bb0ca found the same values; the original-source
certificate now establishes them in Lean. Search ABSENT-FLANK.search.json found no exact existing theorem;
the earlier WellFormed/no-external/replicate search also found no duplicate.
No new lemma body has been written before claim/registration.

Guarded registration20261002-164024-dc6909 DONE111.6s/2303MiB4G,
typee95f3c86045ea3ce. Original fixture
e62c434d182d4c0de1012a68411b53e4bceea5d6b3f4a4f86d37a8c5e2dd331d captured
after successful claim, before any proof assembly. Full original-source check
20261002-164625-6c030a CLOSED: compiler3.984048s, outer52.1s/2345MiB under4G,
receiptb6b07830e79402c133ded8f19180ce85d5a8135d5b24280d4866dbc435346e84.
Only standard axioms, no sorry/blocked/uncovered/nonstandard; matching registered
type/PP/lock; byte-exact fixture assembly; all378 inherited locks unchanged/one
new; changed audit and layers pass. Source
f81f3d07f77f4a17a3307baea96b344422c1f9cd51fc055da1dd1487dadce476,
body666aeb411f07de41e9abe0eda2a1a70b994472f14fc6c41ec3e221566dfb3884.
ABSENT-FLANK.final-verification.json is authoritative. Nested peak0 is unavailable;
outer measured peak is reported. Pinnedc6cbb39d5f845059595734204ca0d1c9a561a497,
guarded commit20261002-165108-236285 DONE. Parent exactly e3c87197, clean tree,
exactly five node/import/lock/index/status files. All owned jobs terminal.
Claim released CLOSED after separate self-review; ABSENT-FLANK.release.json
confirms four evidence files copied to the primary checkout. No further compiler
test is justified. No approval, delegation, merge or push.

First check20261002-164446-7efeaf failed compiler4.155433s, outer16.9s/631MiB4G.
Four scalar WellFormed projections retained arbitrary ms in their syntactic
expected types, so decide rejected free variables; flank simp could not match
local context spelling. Explicit scalar change and local-context change repair
representation only. body-v1/check-v1 and full compiler log preserve the failure.
No theorem credit from that attempt. A routine layers --check invocation was
unsupported before any checks/effects; CLIhelp confirmed plain es layers checks
directly, and the corrected call passes. No missing output is invented.

The theorem proves positional predicates alone insufficient; this one witness
does not prove each nonempty hypothesis independently necessary or classify all
valid swaps with absent levels. The accepted presence-restricted FLANK-SWAP is
unchanged and not contradicted.

Inherited-end-only reconciliation is complete, pin
4bd6580007983864837acf6bf65930f709d04c21, claim released refuted. Separate
scope/end research and review windows are complete; late usage job
20261002-164135-6f15f6 DONE and LATE-USAGE.scope-end.verified.json verifies848660
outputs across26 completed nonoverlapping windows, zero reconciliation deltas.
Active/unassigned work and unlinked resources remain excluded; no matched savings.
Late absent-flank usage job20261002-165755-7cfaa0 DONE: research29888 and
self-review15859 recorded outputs. The latter exceeds its observational10000
target. LATE-USAGE.absent-flank.verified.json verifies894407 outputs across28
completed nonoverlapping windows, zero deltas; active consolidation excluded.
The end-cut refutation status is on its correction branch; a new e3baseline
retains the tracked old pass until integration. Shared journal still records
the refutation. Do not claim global integration or change baseline statements.
General feasible singleton
attainment still has no proof invariant. The native deadline remains
2026-10-03T00:25:54.693298Z; consolidation starts23:55:54.693298Z.
