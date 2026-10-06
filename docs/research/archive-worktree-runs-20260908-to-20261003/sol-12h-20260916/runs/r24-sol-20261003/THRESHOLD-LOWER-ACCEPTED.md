# Universal decomposable threshold lower construction

2026-10-04 00:27 UTC. Full source validation and independent audits passed.
One-node local commit `aebb65051bc97c57ca9c3da83f42c7533f66e3a1`, job
`20261003-202615-98e8f1`, contains exactly the module, root import, nodes,
lock and status files; left_uncommitted=[] and tracked status is clean.
Explicit CLOSED claim release succeeded; `threshold-lower-claim-release.json`
records the copied handoff and no missing evidence. No merge, push or publication.

`ErdosSzekeres.decomposable_threshold_lower_exists`, module
`ESBlueprint.B.DecomposableThresholdLowerExists`, locked type
`a3f0da371108b910`, is CLOSED, lock_ok=true, no sorry, and uses only
`propext`, `Classical.choice`, `Quot.sound`.

For every `k≥3`, `2≤a,u≤k`, it constructs a decomposable, sweep-realizable
coloring on `T(a,u,k)` whose cups have cardinality at most `u−1`, caps at
most `a−1`, and which contains no strong `k`-set. This is the universal
legal lower leaf. It does not assert the upper N<=T or B attainment.

The proof preserves decomposition under geometric ordered append by exact
restrictions, generic coloring pushforward and agreement transfer. A local
Pascal family covers all nonnegative parameters. Consecutive binomial
windows retain the entire window's cap bound; prefix cup plus the next
band's cap is exactly `k−1`. The public inactive and active threshold
identities give the exact cardinality. Increasing enumeration of arbitrary
finite sets supplies the final cup/cap bounds and strong contradiction.

## Exact evidence

Searches: general-threshold-lower-construction-search.json and
general-threshold-lower-final-search.json. Registration
`20261003-195136-0bd13d` passed. Full ready, rather than closure-only
provisional dependency fields, confirmed ready=true and the locked type.
Capture `20261003-195435-02d257` passed.

Fixture:
`9aa024252b7e9cbf4e42bad43a2707f31a9678b4e18b03b22b91cc0a9dd8e005`.
Body v3:
`2379568bb1bc5cedead56284eb6627466eea4131da114f437b1cda9361b004c1`.
Original source:
`718e4e96eceec639ec16c1566c3f739f8cdedf31384d2a5736039faa1c1d3dfb`.

Isolated `op-71d0f250633a4b19`, job `20261003-195510-6327b3`, accepted
the exact body/type in 12.409779 seconds / 2235 MiB, standard axioms.
Immutable receipt:
`572f73a21bf7121096abb345cefb40f68d0608a2504ff15a057894a58821a1b7`.
The first actual compiler check passed. V1/v2 are preserved static drafts,
not failed compiler attempts.

Exact insertion `20261003-195545-a45a2d` passed via the unchanged reviewed
adapter and shared preflight/fixture assembly. It validates the actual
successful stored operation, agent/root, fixture/body/type/axioms/source
and branch/base/claim; it does not create or reclassify an operation.

Supported non-targeted full original-source check
`20261003-195602-12b3d3` passed, rc0, 1650.0 seconds / 6309 MiB.
`threshold-lower-full-source-check.json` has targeted=false,
incremental=false, unchanged locked type, no sorry and standard axioms.
`threshold-lower-full-final-status.json` has stale=[] and problems=[].
Scan15835/15835 was an intermediate checkpoint; the terminal full result
grants validation. The review at 20 minutes left the on-track job alone.

Independent audit/layers `20261003-202515-9033b5` passed in 12.1 seconds /
96 MiB: failures=[], violations=[]. Actual source/body hashes were checked
again, the complete source was read, and whitespace validation passes.

The known pushforward import closure exceeds targeted eligibility. No
knowingly failing node-finish stage or cap/policy change was attempted.
The full supported check and audits are distinct actual receipts; no
fictional full-stage operation or policy-success claim is made.

## Remaining mathematical obligation

Updated 2026-10-04 01:21 UTC: fixed-root assigned limits are fully accepted,
unchanged type `a89e497ebd1cfbea`, commit `e0e31525`; all five normal stages
passed. `ASSIGNED-LIMIT-TRANSFER-ACCEPTED.md` gives exact evidence.
`B-ATTAINMENT-REMAINING-INTERFACES.md` gives the uniform-label base and the
stable ordered merge/fuel induction still to formalize.
Even their completion would leave the upper capacity invariant and closed
profile sibling loss open. Separate fixed-Sol second reviews are complete
and recorded in `CODE-REVIEW.md`; no further trial is admitted here.
