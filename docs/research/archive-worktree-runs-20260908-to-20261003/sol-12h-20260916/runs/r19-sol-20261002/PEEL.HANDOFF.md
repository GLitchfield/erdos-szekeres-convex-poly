# Full PEEL registration and falsification

Agent `codex:01a0fc94-0467-7b90-823c-bce1e6fe6128`, R19, 2026-10-02.
Independent branch `node/CtxBoundAttainedBySingletonCut`, base `e3c87197`.

The exact registered obligation is singleton attainment for every WellFormed
context with a,u>=4, at least two runs and bound>=2, allowing any child, either
side and every legal coupling 1<=c<=k-2, including zero-valued parts. Node
`ErdosSzekeres.ctx_bound_attained_by_singleton_cut`, unchanged type hash
`460265cf1251df69`, registration job `20261002-093211-c20b7b`. The module's
registered sorry is an open blueprint placeholder, not an accepted theorem.
The claim gate refused a claim before the falsifier passed; it was not bypassed.

The full conjecture is diagnostically false. The explicit witness is
(a,u,k)=(4,4,5), word `3U4LSS1L2USS`, maxima (1,1,1,1), children [2,3,6,7].
The compiled interval-cut bound is2, whereas all24 singleton cuts have sum1.
Official exact-dataset falsification `20261002-100340-9841d8` records inner
counterexample exit2 (outer job status FAILED by convention), after validating
the WellFormed/global/two-run premises. Dataset `PEEL.counterexample.json`, full
record `PEEL.exact-falsifier.json`, artifact
`287e751d9d72d75032bc2f746007e7b26258e6f8291b6601de61b13626c61735`.
Falsifier SHA256 `a141f6763c80236099ce2ce78d1b5f078d83c845070622b76d9a6690a22fc681`.
This is diagnostic evidence, pending a separate Lean refutation node.

The structural explanation is that prepending oldest upper unit flank3U raises
a from3 to4 while preserving the earlier `SS1L2USS` gap; prepending oldest lower
unit flank4L then raises u from3 to4. Probe `20261002-094943-6dc167` and
`PEEL.oldest-flank-lift.json` record all three contexts, bound2 and singleton sums1.
The global bounds do not prohibit small effective chain limits in descendants.
A proof of full PEEL under these raw hypotheses is therefore unavailable.
This does not refute the happy-ending conjecture or the one-level root target.
Whether a geometric feasibility/history premise removes this example is open.

The earlier proposed raw chain-limit cost rule also fails independently:
`PEEL.MECHANISM.md` and probe `20261002-093908-bcbe7b` explain why the middle
child of `SSS1L3L2LS` is optimal and why retaining run capacities matters. An
end child with zero change to all remaining limits can still give a smaller
bound. A separate (4,5,6) example attains only with a zero-valued leaf. Those
diagnostics correct the initial cost interpretation; they do not prove a
replacement selection theorem.

The generated full falsifier scan `20261002-093527-a2bca0` was scientifically
superseded, not stopped at a chosen deadline: its depth<=3 family cannot contain
the depth4 witness. Cancellation was requested; a source-confirmed non-run job
polling gap required one-off recorded recovery `20261002-100139-bd1337`.
`PEEL.cancellation-recovery.json` verifies the exact live runner/start identity,
its sole Python descendant in the precise systemd scope, and acknowledged scope
termination. The original falsifier finished ERROR/-15 after1569.8s, not PASS.
Its original script hash and terminal receipt are in the journal. Last durable
checkpoint covers all k5 axes, k6 a=u4 depths1/2, and14000 depth3 rows out of
114816 (5346 eligible,171072 singleton cuts). No violation was seen there;
remaining finite coverage is unvisited and remains open. No completeness claim.

Reuse: `compiled_evaluator` and `singleton_cut_values`; catalog APIs were read.
The new falsifier adds small candidate enumeration and exact-row validation,
with common orchestration delegated to es. Its generated mode preserves absent
declared levels, all actual subsets, legal maxima and zero parts. No standalone
duplicate evaluator was written. The cancellation workaround reuses shared
process identity and scope acknowledgement; it is one-off infrastructure glue,
not promoted. The generic cancellation gap needs separate harness maintenance.

Next: register the exact universal negation on a fresh node branch from the
pinned base. Use the certified `ctx_bound_cut_le` on [2,3] for bound>=2; decide
the small cut value and all24 singleton sums in the Lean kernel. Avoid computing
the full four-child bound if it is unnecessarily costly. Search
`singleton attainment counterexample cut bound` returned no duplicate; search
`ctx_bound_cut_le` found the cut inequality and existing end-cut refutation.
No proof receipt exists for this refutation yet. The three already accepted R19
proofs and their receipts are in the separate SPLIT/FLANK-SWAP handoffs.
