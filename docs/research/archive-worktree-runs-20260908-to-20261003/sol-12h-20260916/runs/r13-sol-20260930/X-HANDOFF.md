# Localized singleton exchange X — partial narrowing

Node: `ctx_one_level_root_singleton_base_exchange`, statement hash
`a68960f119792789`, branch `node/CtxOneLevelRootSingletonBaseExchange` from
main `41cc0e4b58206008bde4af9b510b56b35dd3aa69`.

The source is a one-level root with parameters 1<=a,u<=k, k>=3,
1<=m<=k-2, word `left ++ [child,child] ++ right`, maxima `[m]`, and every
left/right letter either child or `ext 1 side`. Assume at least two runs.
For any source singleton p, orientation s and coupling c in1..k-2,
the explicit leaf threshold T(cap+1,cup+1,k) plus the opposite complement
part is at most the corresponding sum in the shortened root at the mapped
singleton q, some new orientation t, and some coupling d in1..k-2.
Here q=p when p<=length(left), otherwise q=p-1; the deleted copy maps to
the retained copy. All singleton positions are covered, not just the pair.

This is strictly a singleton-base/part conjecture. It does not assume
whole-bound contraction, quantify arbitrary interval cuts, or assert a
normal form. The existential orientation and coupling are necessary:
same-coupling transport fails in the P11 data.

Registered falsifier job `20260930-171455-ff2d9f`: pass,29.5s,3984 roots,
4648 duplicate-pair cases,106912 cuts,168592 explicit-T leaf audits.
Finite domain: k5 all25 global pairs; k6(5,5),(6,6); all maxima; both sides;
two/three runs, lengths1..2, at most4 children; one gap marker and optional
single end markers. Script hash
`63e77b47c4c31d3412a8841915ab30417d4dc2f4d6fb72cfe3d19f79569dfeaf`.
Evidence `FALSIFIER.X.pass.json`, `RECEIPT.X-falsify.json`.

Larger ad hoc exchange evidence: k5<=5 children,7800 pair cases,zero
failures (`exchange-k5-all5.json`,job20260930-163512-92d63d). The k6 full
counterpart is still running as job20260930-164738-c3329d.

Exact remaining obligation: derive C1r from X alone. A sufficient route
would prove singleton-cut attainment for one-level roots and use X on the
attaining cut. Such a normal-form theorem is not yet proved, and will not
be silently added as an extra unproved premise in a claimed Done result.
Diagnostic singleton attainment passes k5/k6/k7 roots with<=4 children;
general four-child two-level contexts also pass. General five-child test
job20260930-170246-ccbdbe is pending. Endpoint-only attainment is refuted.

Review: the node falsifier reuses the shared compiled evaluator, child-part
constructor, endpoint-limit matrices and threshold formula. Its root
generator is small mathematics specific to this node. No separate job,
budget, timeout, storage, or reporting framework was added. All probes are
diagnostic; the registered proof is still `sorry` in ESBlueprint.
