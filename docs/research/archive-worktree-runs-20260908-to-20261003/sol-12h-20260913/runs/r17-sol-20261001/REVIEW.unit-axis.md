# Sol review of unit-axis localized exchange

Sol/xhigh only. The trial forbids other models and delegation; independent
Astra review is deferred, not claimed as performed.

The proof applies raw unit-global-axis vanishing to the singleton part and
its complement. Parts retain the global fields, so the original a<=1 or
u<=1 hypothesis applies to both. The exact singleton threshold identity
turns the explicit leaf threshold into the singleton bound. The entire
source cut is zero, and the original legal side/coupling supplies a target
whose nonnegative value suffices. No geometric assumption is smuggled in.

Two earlier candidates failed only on the local record syntax and a redundant
rfl after a closing rewrite. Accepted job20261001-114214-16099f audited the
whole unchanged declaration, typecfa5c55a7200eb09, standard axioms only,
8.866s/2107MiB under4G. Body SHA256
d7c097d63e1ec347d64a4d885301bd20afdd9b298d456ef0258f6f19601961fd.
Original targeted check20261001-114533-4b9cdf passed rc=0, closed,
lock_ok=true, no uncovered axioms: incremental2.236s/196MiB under4G.
Receipt193ac981794a1c1cdf1757d357b0dc4cb54c590c474b9fd4ae19ab34f716506c.

Shared falsifier code review: selected() implements the five exact proposed
restrictions, uses the old marker side for the chosen global axis, and counts
runs in the actual complement part. Global fields are restricted to the
registered legal range. Every selected source singleton cut is compared with
all legal target sides/couplings at q=p before the pair and q=p-1 after it.
The unit domain includes all source cuts in its bounded family. An unknown
--node is rejected. Existing singleton_values independently audits every
explicit T leaf. The compiled evaluator is closed in finally. No new workflow,
storage, guard, or evaluator implementation was introduced.

Falsifier job20261001-114525-ad60e8 passed:102144 selected cuts,
145920 leaf audits,3312 roots/4784 pairs, zero violations,237.3s;
record under harness/falsify is committed with the exact script hash.
This finite family does not claim exhaustive quantification.

Commitb55ab7cbe98190f87d2f583c337d7a36180b2c76, parent approved5847e155,
exactly seven node/falsifier/result files, clean at commit. Commit job
20261001-115200-0a9793 succeeded and the claim was released closed.
