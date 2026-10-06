# Independent-color profile gluing

2026-10-03 19:48 UTC. Registered general target, typee3f7f68984afcdfc,
after endpoint full acceptance/commit469c5d2f. Branch
node/DeepSplitProfileGluingExists, base469c5d2f; claimed. Guarded registration
20261003-154540-714d3c passed96.5s/2310MiB. Only accepted strong/endpoint
module imports were added to the generated header. Captured fixture
c6a04909ea5c4351ddcf0b646f7063024aac5f8104e4592551ae5ed1b7f888c5,
job20261003-154747-4688c4. Isolated first candidate check is next/in flight.
No theorem acceptance is yet claimed.
Search profile-gluing-exists-search.json/deep-gluing-coloring-search.json
and source search found no matching construction. Existing color agreement
APIs were found in DecompositionPrimeMutationLocality and CreationShield.

Fix disjoint finite supports L/U in the same ambient ordered Fin n and two
independent colorings psiL/psiU. Each child is decomposable and avoids
strong(s+1). Impose the exact pure-chain and endpoint-extension predicates
from deepSplit_endpoint_constraints_iff on its own coloring, and the cardinal
coupling for every psiL lower cup plus psiU upper cap.

Prove existence of a parent coloring chi agreeing with psiL on all triples
in L and psiU on all triples in U, deep below at L/U, decomposable on their
union, satisfying all cup/cap predicates and avoiding strong(s+1). The
union cardinal is exactly |L|+|U|. All natural s are allowed; child
decomposability itself implies nonempty supports. No parent one-change or
sweep-realizability assumption, fixed normal form or leaf N oracle is used.

Define chi(t) to use psiL when the whole triple lies in L, psiU when the
whole triple lies in U, and otherwise the deep crossing color determined
by the middle point. Disjointness makes the two inherited cases compatible.
The constructor immediately gives the deep split and triple agreement.
Reuse IsDecomposableOn.of_agreeOnTriples for child transport and split them
to obtain parent decomposability. Reuse the existing strong-set agreement
iff on each subset to transport child avoidance. Cups/caps transport by
their defining triple predicates, requiring only small local facts.

Transport each parent-color child chain back to its original coloring;
apply the exact endpoint-constraint iff for parent predicates and the
accepted strong-coupling iff for parent avoidance. No vertex is removed.

This certifies that compatible refinements incur no further union loss,
even when child maxima are attained by different colorings. It does not
construct the joint supports from abstract sub-zone patterns or define
their maxima in Lean, and does not compute the endpoint loss invariant.
The fixed-support construction is a reusable component of the exact Q3
max-plus law, not a closed universal N formula. Done means acceptance of
the unchanged general existence theorem with original/full/audit receipts.
