# Pointwise remaining-budget loss does not select a first child

Node ctx_k6_remaining_budget_cost_counterexample, independent
node/CtxK6RemainingBudgetCostCounterexample, basee3c87197b66a65092e1ffe5e9d0d8c7aa1981cf8.
Registration20261002-135149-8bc692, locked type7be8179010ca9dad; active claim
codex:01a0fc94-0467-7b90-823c-bce1e6fe6128. Research window-33dfcce0c9504e9d.

Literal SSS1L3L2LS at(5,5,6), maxima111. Compare upper3 peels at p6 and p1,
both with lower2 companions. Both leaves have bound2. The end remainder keeps
children[0,1,2], preserves every ordered remaining cup/cap endpoint limit and
has bound4. The middle remainder keeps[0,2,6], strictly decreases cup(0,0)
but has bound>=6. Every legal end-child side/coupling has sum<=7. Thus zero
pointwise budget loss can select a child inferior to one with positive loss,
even with equal leaf gain. This refutes that precise cost surrogate, not every
undefined cost notion or full singleton selection on realizable histories.

Kernel checks handle endpoint limits, leaves and the contiguous end remainder.
For the middle companion gamma, cut its last child6 lower3: leaf4 plus rho.
Rho keeps[0,2] upper2 and has bound>=2, from its child0 lower1 split worth1+1.
Two applications of ctx_bound_cut_le give gamma>=6. No full parent or gamma
maximum is evaluated. The37-line body reuses the accepted k6 cut-tree technique
but adds the exact cost comparison; its statement has not been edited by hand.

The same literal context is separately accepted WellFormed/Satisfies under
constant-right coloring in K6-SATISFIED-END-GAP.HANDOFF.md. This is logical
composition of independent receipts, not a compiled conjunction here. Full
parent bound8, exact middle bound6, uniqueness of the middle attainer and actual
external-history realization remain separate diagnostic/open facts.

Existing diagnostic20261002-093908-bcbe7b explains why: the end's new level1
marker sits beyond older markers, so a walk using it cannot subsequently thread
the older right markers. Longest chain and join counts stay unchanged. Middle
peeling changes the residual run geometry; a spanning cup limit2 permits two
unit early components plus last capacity4. Parent budget losses miss that
capacity change. The longest-chain/join equalities are diagnostic, outside the
locked statement. There is no general feasible-selection proof idea yet.

Searches BUDGET-LOSS.search.json /cut-tree-search.json found no duplicate.
Selected data BUDGET-LOSS.selected-diagnostic.json avoids rereading the30MB
profile artifact in reports. No new mathematical Python algorithm or workflow
script is needed. Shared proof fixture/assembly and guarded check APIs are reused.
Initial fixture5818a63cbfd14ef2866e4caf6c724922022a6c809480d45b05540ed1374cc305
was superseded after adding only maxHeartbeats4m/maxRecDepth10000 metadata.
Current fixtureb20fee4385c4593b4d42cbb168337b8d72b5548b4ae916e325ea41316e2b44be.
Complete original-source check20261002-135814-128f53 is queued under4G; no new
theorem credit until it closes. No compiler failure in this body yet.
