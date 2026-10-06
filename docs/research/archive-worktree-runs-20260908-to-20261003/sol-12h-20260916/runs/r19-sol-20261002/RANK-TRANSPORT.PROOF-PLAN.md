# Ordinal transport of coloring constraints

Node ctx_satisfies_of_ordinal_limits_le, branch node/CtxSatisfiesOfOrdinalLimitsLe,
basee3c87197b66a65092e1ffe5e9d0d8c7aa1981cf8. Registered typeaf6326496e9c975b,
job20261002-131728-185858 DONE. Active claim codex:01a0fc94-0467-7b90-823c-bce1e6fe6128.

For the same ambient coloring and set S, compare raw contexts sigma/tau with
equal child counts, nondecreasing k and cup/cap limits at corresponding ordinal
child endpoints. The list positions need not agree. No WF or global premise.
If sigma is Satisfies, every nonempty subset C has its min/max in S. Their ranks
in S are below S.card=sigma.childPositions.length, by existing rank_lt_card.
Apply the ordinal limit hypothesis at these two ranks, then transitivity to
sigma's cup/cap constraints. Strong bounds transfer by monotonicity of k-1.
Equal child counts transfer the remaining Satisfies cardinality condition.

This supplies the missing constraint invariant for physical exterior-padding
erasure: accepted padding translates the actual word positions, while Satisfies
selects positions by the same ranks in S. It does not prove feasible PEEL or
external-history realization. The intended proof is16 lines and uses no new
helper. Searches in RANK-TRANSPORT.search.json /length-search.json found no
duplicate. Reuses the core rank lemma and shared es.proofs fixture/assembly API.

Fixture4f3f9b1ef30e3c4032eddddd13c74e83ec7596870624e055a3ce1bb59d3bdecd.
Initial assembly used unavailable python (exit127); source remained the original
blueprint sorry. Accidentally submitted check20261002-132023-a5d16b therefore
checks only that placeholder and is diagnostic, with no intended proof credit.
Exact host observations20261002-132817-a06fbc /20261002-133006-5f8bc4 found no
matching runner, job-tagged child or lease. Two unreadable daemons predate launch.
Guarded one-job reconciliation20261002-133154-42ffbf verified byte-exact placeholder
source and unchanged job identity, then recorded FAILED/no compiler receipt;
no process was killed or foreign job modified. Evidence in runner-reconciliation.json.
The intended body is now assembled through python3 and the shared fixture API.
Full original-source check20261002-133225-571382 is queued under4G via es job run
wrapping synchronous es check. This avoids direct sandbox asynchronous launch.
An older foreign operation holds shared worker admission; leave it untouched.
No compiler failure in the16-line body has yet been observed. Research
window-001510fde88a48ee remains active. Generic bus-aware launch/reconciliation
repair is deferred to separate review, not silently patched here.
