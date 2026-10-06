# R14 conditional proof account

Closed theorem: `ctx_bound_child_run_contraction_one_level_root_of_singleton_exchange`.
Its full registered statement is retained in `Conditional.registered.lean`.
It assumes local singleton attainment for the doubled one-level root and the
local mapped singleton-base exchange to its contracted root, as explicit hypotheses.
No conjecture theorem is imported into the module.

Targeted check 20260930-201714-9a8260, receipt
d8eb137d025c8948d4153f304fdcf6de19ec731ecb3a7f4384e5735c67431833
(`CHECK.conditional.json`): sorry=false, standard axioms only, lock matches
fdf891b82544f272; build 5.067s, 615MiB. Source fixture
0bd141084b4f4cdebab336c2ffe74c53f200767d31374db2ebd3824a450bbb89
is preserved in `FIXTURE.conditional.json`. Registration job 201439-59e3cd and
commit job 201903-b6756f on 20260930; receipts are alongside this account.
The commit receipt supplies the exact SHA and one-node file set.

Proof reuses R13's RootConditionalInterface.lean (including its RootReverse
argument). The reverse inequality handles unit global axes with the closed
zero theorem and other axes by child expansion. Run count and base contraction
handle single-run roots. For multi-run roots, N supplies a singleton, X transports
its value, the explicit position map remains a child, and a closed singleton cut
inequality bounds the transported value by the smaller root.

No mathematical or compiler failure occurred. A receipt-read attempt fetched
only the default 4096-byte page and failed JSON parsing; the complete 11448-byte
receipt was then fetched explicitly, without recompiling.

Open obligation: N_root is registered but unproved (type81be57bce6e33074,
commit763b4b67730ef5e3c8215ec5c441bb7b84979a41); X remains the open main
conjecture. This conditional alone closes neither. Next compose C1r from
the conditional applied to those two registered conjecture theorems, then
attempt N_root under the R14 optimal-block induction brief.
