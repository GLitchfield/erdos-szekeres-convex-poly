# Ordinal coloring-constraint transport

2026-10-02 17:40 UTC, codex:01a0fc94-0467-7b90-823c-bce1e6fe6128.
Node ctx_satisfies_of_ordinal_limits_le, independent
node/CtxSatisfiesOfOrdinalLimitsLe, basee3c87197b66a65092e1ffe5e9d0d8c7aa1981cf8.
Registered20261002-131728-185858, unchanged locked typeaf6326496e9c975b.
Pinned commit3ef1651152fa03db37ef45215344ea5c986f256d, commit job
20261002-134046-fdfd1d DONE. Claim released CLOSED after separate self-review
window-afe2dfc298944d7d; see RANK-TRANSPORT.CODE-REVIEW.md.

For raw contexts sigma/tau with equal child counts, sigma.k<=tau.k and
cup/cap budget inequalities at matching ordinal child positions, Satisfies
sigma transfers to tau for the same coloring and ambient set. Word positions
need not agree, and no WF/global hypotheses are imposed. Every ordinal below
the child count is used in the premise, so no missing-list default is relied on.
The proof covers empty ambient sets and small k by the same statement.

The proof uses existing rank_lt_card on the min/max of each nonempty subset C
of S. Their ranks are below S.card=sigma.childPositions.length. The pointwise
ordinal budget hypothesis and transitivity transfer cup/cap constraints; natural
k-1 monotonicity transfers strong constraints. Equal counts transfer cardinality.
No new helper is needed. The16-line proof passed its first actual compiler check.

This removes the remaining constraint-transport obstruction after literal
exterior-padding erasure. Accepted padding translates positions by prefix
length, and the valid ordinal getters translate to the same children. Two
applications give constraint equivalence when corresponding limits/k agree.
Combined with oldest-flank normalization, the raw PEEL lift normalizes and
physically erases to its(3,3,5) core. This is logical composition of independent
accepted branches, not a separately compiled combined corollary. It does not
prove feasible singleton selection or actual external-history realization.

Original-source check20261002-133225-571382 CLOSED; compiler2.820798s, guarded
outer38.4s/2349MiB under4G. Inner peak0 is unavailable nested measurement.
Receipt098887d523a6ecee23d7a9e6b91161b641405999a7582d3d24550edeb2e264cb,
RANK-TRANSPORT.original-check.json. Fixture
4f3f9b1ef30e3c4032eddddd13c74e83ec7596870624e055a3ce1bb59d3bdecd.
No sorry, standard axioms only, matching type/lock, no blocked/uncovered
dependencies. Audit/layers pass. Final-verification JSON asserts byte-exact
assembly, source SHA83fc5fa5cfafc18f91b16b6ee47ce5b812d99a56003aa777da7ec5eff173aecc,
all378 inherited lock objects unchanged and exactly one new.

Searches Satisfies ordinal child limits rank transport /Satisfies transport
childPositions length returned no duplicate. Core rank_lt_card and shared
es.proofs, artifacts, jobs and Store APIs were reused. No Python mathematical
algorithm or tracked workflow script was added.

Infrastructure failures are distinct from mathematics. Initial assembly used
unavailable python (exit127), leaving the original placeholder. The following
direct async check20261002-132023-a5d16b lost its sandbox runner before publishing
any compiler receipt; it never certified the intended proof. Observers
20261002-132817-a06fbc /20261002-133006-5f8bc4 and a fresh reconciliation scan
found no exact runner/start identity, job-tagged child, check command or lease.
Two unreadable user processes were systemd daemons born before this job.
Reconciliation20261002-133154-42ffbf verified byte-exact placeholder source and
unchanged job identity before recording only this job FAILED through shared
Store API/journal. No process was killed or foreign job modified. Evidence in
runner-reconciliation.json; compiler receipt missing, no theorem credit.

Corrected assembly used python3. The final check ran synchronously within a
worker-backed es job run. It briefly waited behind an older foreign operation's
shared40G admission reservation; foreign jobs were left untouched. Future checks
here should use this worker-backed path. A later verification-report snippet
passed all mathematical/lock/assembly assertions but guessed a missing fixture
id key; it was repaired using the known captured ID, without source or Lean
change. The final report now parses completely.

New ad hoc workflow artifacts are inspect_ordinal_check_runner.py, its frozen
readonly-first version, and reconcile_ordinal_check_runner.py. They are exact
one-job recovery tools, not a general stale-job cleanup API. Separate review
must inspect the narrow identity/source/process guards and journal mutations.
Generic bus-aware submit/null-scope recovery fixes remain deferred; no tracked
harness code was patched. Independent coordinator review is pending. Preserve
ignored artifacts alongside the pin; native goal stays active until its deadline.
