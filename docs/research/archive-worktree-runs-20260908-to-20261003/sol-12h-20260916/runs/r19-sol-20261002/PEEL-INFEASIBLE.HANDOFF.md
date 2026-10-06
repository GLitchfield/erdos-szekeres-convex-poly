# Exact PEEL witness is not a satisfied coloring context

2026-10-02, agent `codex:01a0fc94-0467-7b90-823c-bce1e6fe6128`.
Node `ctx_singleton_attainment_counterexample_not_satisfiable`, independent
branch node/CtxSingletonAttainmentCounterexampleNotSatisfiable, base
e3c87197b66a65092e1ffe5e9d0d8c7aa1981cf8. Locked type2979318b28265786 unchanged.
Pinned commit1e8e5c90b897d653c1e875ee39bee22f172ce64e, commit job
20261002-110806-69a5a6. Claim released CLOSED.

The theorem asserts, for every ambient size n, coloring χ and finite set S,
that `Ctx.Satisfies χ S σ` is false for the exact literal full-PEEL witness:
(a,u,k)=(4,4,5), word3U4LSS1L2USS, maxima1111. This is an additional certified
scope fact about the accepted raw-context refutation. It does not invalidate
that refutation or establish a replacement PEEL theorem for feasible contexts.

Proof: kernel-check children[2,3,6,7] and cupLimit2 3=1. Satisfies would give
S.card=4. Its increasing finite-set enumeration has ranks0 and1 at those first
two children: elements below index i are exactly the image of Fin.Iio i. Their
two-point subset is a cup vacuously, since its cardinality is two and an ordered
triple has three distinct points. Satisfies then gives2<=cupLimit2 3=1.
The rank/cardinality argument is reused from the accepted PAIR-LIMITS proof,
specialized locally so this node branch starts independently at the fixed base.

Original-source check20261002-110525-546700 CLOSED, build2.922275s/546MiB,
no sorry, standard axioms only, matching type/lock and no blocked/uncovered
dependencies. Immutable receipt
67023967022a9fc6d5a0e81d1747f55825db39858ae6efc200ea84f48cc5c62f,
copied and parsed in PEEL-INFEASIBLE.original-check.json. Changed-node audit and
layers pass; all378 inherited locks are unchanged, with exactly one new entry.
Registration20261002-110036-538445 and frozen fixture
89c0cc933c5b2dbc30e694b50609687c0ae870d085a4f931495a02981d0a4517.

Search `singleton attainment counterexample not satisfies` found no duplicate;
ready/status consulted, inherited end-cut-of-four-le node remains untouched.
First check20261002-110400-fcdd78 failed2.723891s/543MiB because decide rejected
a Fin comparison whose type contained free S.card. Explicitly changing it to
the definitionally equal natural inequality0<1 and using omega repaired it.
No theorem type, computational semantics or mathematical route changed.

Reusable lesson: global a,u and WellFormed alone permit infeasible raw recursion
states. Pair limits>=2 are necessary for coloring histories with distinct
children. Whether they or stronger history invariants yield a valid singleton
selection theorem remains open. No new sibling-penalty narrowing is proposed.
Exact oldest-flank normalization is the separate structural proof idea for
why oldest unit flanks lift the raw gap while changing effective parameters.

No new research Python algorithm or tracked workflow script was introduced.
Proof-span assembly and immutable result preservation use shared es APIs;
receipt and parsed-lock comparison are checked directly against the exact base.
Keep original artifacts and failure log. Review in a separate usage window
before the next trial; independent coordinator review remains pending under
the fixed Sol-only contract. Preserve this ignored handoff with the pinned
branch; no merge or push.
