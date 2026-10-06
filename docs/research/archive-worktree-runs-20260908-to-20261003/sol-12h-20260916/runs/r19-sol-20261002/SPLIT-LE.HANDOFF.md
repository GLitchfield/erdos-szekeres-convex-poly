# Exact splitting upper bound

Target `ErdosSzekeres.decomposableThreshold_split_le`, type hash
`7c6bc98c44ce5e25`, on `node/DecomposableThresholdSplitLe` from `e3c87197`.
For all `3 ≤ a,u ≤ k` and all `1 ≤ d ≤ k-2`, the two adjacent-singleton
thresholds sum to at most `T(a,u,k)`.

In the classical regime, each child is bounded by the corresponding unconstrained
Pascal predecessor, and their sum is the parent coefficient. In the active
regime, set `a'=min(a-1,d+1)-1`, `u'=min(u-1,k-d)-1`. Both are positive,
their child parameters leave a parent unit, and `a'+u'≤k-1`. Thus the existing
certified `published_nonsaturated_next_threshold_pair_le` allocates them to
disjoint prefix and suffix windows. This explains the entire coupling domain;
it is not a fit to finite data.

Accepted original-source check: `20261002-084819-794720`, DONE rc0,
3.1230239868164062 seconds / 590 MiB build. Receipt
`1866ab58618b533de5d93e823b22854e8155325c7c1a746878f8899f5eccc4f6`,
copied to `SPLIT-LE.original-check.json`: CLOSED, no sorry, locked type unchanged,
only `propext`, `Classical.choice`, `Quot.sound`, no uncovered axioms.
Incremental original-source extraction, layers, and changed-node axiom audit pass.
All 378 inherited lock records were compared structurally and remain unchanged.
The changed-node audit also displayed an inherited open node relative to the
coordinator's newly integrated main; that proof was neither edited nor credited.

Registration `20261002-083448-0fc69d` completed after the coordinator's 30G
integration extract released admission. Frozen fixture
`904d75081a29c3ef2990bd3ce8a66e2d2dfd51153c236c0b6f54dcd4118be8bc`;
proof body inserted through the shared `es.proofs.assembled` API. A narrow
`DecomposableContextLemmas` import supplies monotonicity; no statement changed.

Together with the explicit witness in commit
`991b783989fd7515b23409ec3202bd9b860210e3`, these are the two registered,
compiling halves of the requested finite maximum identity. No separate
`Finset.sup` wrapper has been exported, and neither half proves context PEEL.

Review description: every legal split coupling is bounded by the parent threshold;
the companion witness attains it at `d=a-2`. Search before proving: splitting
query returned no existing identity; `es search decomposableThreshold` found
monotonicity and choose/window forms; `es search published_nonsaturated_next_threshold_pair_le`
found the reusable active-window allocation. `CtxBasePascalCombine` was inspected
and motivated direct reuse of that core inequality. No PR, merge, or push.
