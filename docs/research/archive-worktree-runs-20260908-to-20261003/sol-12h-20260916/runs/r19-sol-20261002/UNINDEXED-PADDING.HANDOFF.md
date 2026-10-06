# Exterior unindexed padding is invisible to the context bound

2026-10-02, agent codex:01a0fc94-0467-7b90-823c-bce1e6fe6128.
Node ctx_bound_eq_unindexed_padding, independent branch
node/CtxBoundEqUnindexedPadding, basee3c87197b66a65092e1ffe5e9d0d8c7aa1981cf8,
unchanged locked type5cbca3e4a0d72461. Registration20261002-124743-7422db.
Pinned commit940641e30236f2dbf0b0f229cacbfe05872f8f5a, commit job
20261002-130959-3edb64 DONE. Claim released CLOSED after separate review
window-061a596dfee14451; see UNINDEXED-PADDING.CODE-REVIEW.md.

The theorem applies to any raw sigma, with no WellFormed, global legality,
maximum positivity or positive-inner-label hypothesis. Every letter in exterior
left/right padding must be external, with its label greater than sigma's
indexed depth maxima.length. For tau.word=left++sigma.word++right and identical
other fields, child positions translate by left.length, all cup/cap limits
at translated endpoints agree, every same-fuel bound agrees, and full bound
agrees. Both exterior sides, arbitrary padding multiplicity/sides, empty words
and virtual endpoints are included. It does not erase internal separators.

The proof uses a constant order embedding i->left.length+i. Filtered ranges
show children and indexed external positions translate, run count is unchanged,
and each indexed sideAt remains the same. The nearest indexed marker in either
walk direction translates, so all extension folds keep their counts and their
endpoints translate. Chain and strong-join counts therefore agree. This is
exact transport of the walks, not just agreement of parent limit matrices.

Part commutation translates keep indices and bumps the exterior labels. Every
cut increases indexed depth and each padding label by1, preserving the strict
unindexed inequality. Contiguous blocks and complement filters correspond by
the same injection. Fuel induction compares every retained cut, including
zero-valued parts, and single-run bases agree. Child-position lengths are equal,
so the chosen full-bound fuel is identical.

This removes a documented obstruction in the R19 normalization explanation.
After exact oldest-flank normalization removes lower4L then upper3U from
3U4LSS1L2USS at(4,4,5), maxima1111, their retained prefix3U4L is above depth2
and globals are(3,3,5). This theorem erases that prefix to the actual two-level
core SS1L2USS without changing bounds or transported limits. That conclusion
is a logical composition of independent accepted branches, not a separately
compiled combined corollary. The exact raw witness remains infeasible under
Satisfies; this does not prove feasible PEEL or actual-history realization.
The previous Satisfies transport theorem requires identical child positions;
literal erasure renumbers positions, so a rank-based constraint transport is
the next precise remaining normalization obligation.

Original-source check20261002-130548-84659e CLOSED,3.724435s/601MiB, no sorry,
standard axioms only, matching type/lock and no blocked/uncovered dependencies.
Receipt357fd8bbee50ebc29aae9752951405f645a99922023acd2759510879e0e1ff17,
saved/parsed in UNINDEXED-PADDING.original-check.json. Fixture
0e55ff0e3d8d3d7df5a735563a5eb946153834617678466acb3606450db06ed4.
Final-verification JSON asserts byte-exact assembly, source SHA
32d53cb0176bffdf2941d44e27ec1a9cfc81d3cfb223847bdebfa0f34e4e2b04,
all378 inherited lock objects unchanged and exactly one new. Audit/layers pass.
The final body432 lines is composed of frozen geometry, limits, parts and fuel
chunks; earlier failed/partial bodies are retained separately.

Searches unindexed external erase / unindexed padding bound found no duplicate.
Existing ctx_bound_external_letter_contraction already handles identical
adjacent letters; it was read for geometry techniques and left unchanged.
Existing normalization nodes retag/truncate maxima while retaining word letters;
this theorem supplies literal exterior erasure, with no WellFormed premise.
Reused List range/filter/map/fold APIs and named Context extension/part steps.

Failures: registration20261002-124636-68618f omitted the full-type colon and
failed before locking a node; only the delimiter was repaired. Initial geometry
check20261002-125407-c67c8a failed3.543s/586MiB at addition associativity.
Limits check20261002-125811-0c8adf failed3.324s/597MiB at tuple-match reduction,
expected-type inference for projected fold equality and opaque pad fields.
Full logs corrected an initially incomplete error summary before the repair.
Repaired limits20261002-130015-768905 and parts20261002-130255-f153f1 passed
as staged diagnostics but retained explicit blueprint sorries for remaining
bound goals. They are not accepted theorem receipts. The final fuel induction
passed its first complete check, and the final module contains no sorry.

No Python mathematical algorithm or tracked workflow script was added. Short
artifact assembly/verification snippets reuse es.proofs and JSON/standard git
reads. Separate Sol code/library self-review precedes the next trial; independent
coordinator review remains pending. Preserve ignored artifacts with the pinned
branch; no merge/push, and the native goal stays active until its fixed deadline.
