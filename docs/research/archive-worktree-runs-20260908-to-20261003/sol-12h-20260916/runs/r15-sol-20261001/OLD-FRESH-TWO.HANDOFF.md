# R15 old/fresh near-saturation proper-part estimate

Proof status: ACCEPTED and committed afb36431268c2e326f2f443846205346b3c0f85e
by terminal commit job20261001-075043-9a772d. Exact type a7a22e44827d4efb.
Check 20261001-074813-96b1dc DONE0,109.8s2407MiB, noOOM/budget exceeded;
CHECK.old-fresh-two-v1.json full receipt SHA256
830f5f8aa06a80cda98c049807a46ea137eb023626ccd1e766d867f6a70added.
Closed, standard axioms only, no sorry, locked type, no blocks/errors,
targeted and incremental checks true. Build3.2322583198547363s. Source
OLD-FRESH-TWO.candidate-v1.txt SHA256
f7c650e1f026f65051aba0c951e0f86e777446c762a3df0202cbf84088ee8f88.
Normal ready claim preceded proof; capture ce97629aeddd0f43bd964789e923461d961f6088397bd26caa42531c323ca206.
Node ctx_part_bound_le_two_of_near_saturated_old_and_fresh_maxima on
node/CtxPartBoundLeTwoOfNearSaturatedOldAndFreshMaxima, from main.
Registration job 20261001-074249-bf9a06. Fresh running/starting 100-job scans
showed no compiler before submission. The earlier 074218-64c649 branch-helper
attempt failed at CLI parsing with no mutation or output; guarded manual git
branch creation 074230-069b27 succeeded.

Exact obligation: positive actual external labels, N in source levels,
k-3 <= maximumAt N, arbitrary keep/axis/new m with k-3 <= m, and actual
removed source child r. Prove every fuel bound and full bound of the part <=2.
No well-formedness, legal-coupling, run-count or global-width premise.

Proof route reuses the local hTwo in K4-UPPER-THREE.candidate-v2.txt. On the
old level's axis use the accepted same-side near-saturated proper-part bound.
On its opposite axis, the removed child creates an actual fresh level-one
marker. The shifted old level and fresh level then give opposite-axis
near-saturation; apply the accepted both-axis <=2 theorem. Retain both fuel
and full conclusions. Part globals are copied unchanged; no global-width
reduction is assumed.

Dependencies: exact closed SMALL-AXIS-TWO.candidate-v1.txt,
SAME-SIDE-TWO.candidate-v2.txt, BOTH-SIDES-TWO.candidate-v2.txt and
K4-UPPER-THREE.candidate-v2.txt restored only as untracked overlays. The new
proof directly requires the same-side and both-axis near-saturation nodes;
their separate accepted commits are 67cb2a0cc13e71e6cd083ad4fac42a35830b2b8e
and 5d2e6e79fa60cb2f3647235efd8810c3c2557af7; the former additionally needs
small-axis commit 1a6c30a2590c51bdbddfe17b372039539e687989. Exclude overlays
from the node commit and remove them after terminal check and commit.

Searches for proper-part near-saturated old/fresh maxima returned no matches.
The actual-removed-child hypothesis is essential to this proof route: the
saved κ4 raw source counterexample has bound three despite a near-saturated
old maximum. This estimate supplies no lower bound after a segment flip.
Full FLIP positive κ>=4 remains open.
