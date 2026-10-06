# General assigned-slot transfer at a fixed deep root

Current 2026-10-04 01:16 UTC: unchanged general type
`a89e497ebd1cfbea` is fully accepted, commit `e0e31525`. All five normal
stages of `op-e4fb2f1518694e80` passed; full extraction, audits and complete
source review are verified. Automatic CLOSED release leaves no live claim.
`ASSIGNED-LIMIT-TRANSFER-ACCEPTED.md` records exact evidence.
Universal threshold lower is fully committed `aebb6505`. Earlier draft-only
snapshots below are historical; no B attainment is claimed.

2026-10-04 00:04 UTC: complete type and proof-v3 drafts now exist as
`assigned-limit-transfer-node-type.txt` and `assigned-limit-transfer-proof-v3.txt`.
They are unregistered, unclaimed and unchecked. The inline predicate uses
actual first/last points, with empty chains vacuous, and permits slot
multiplicities. The type requires `σ.k≥3`, weak monotonicity, distinct labels
across actual children, explicit side/marker premises and reserved shares.
The proof abstracts cup transfer, handles caps by duality, and derives
coupling from the zero-gain consumer. Static version repairs concern equality
directions and dependent-match application; none is a compiler receipt.
Threshold full `195602-12b3d3` and its separate review remain priorities.
The old plan-only snapshot below is historical; no second trial admitted.

2026-10-03 23:42 UTC. Plan only: no registered node, Lean body, claim or
trial. Endpoint full-extract191701-14ca1a and the universal T lower draft
have priority. Search assigned-slot-gluing-plan-search.json returned no
indexed hit; this does not prove no reusable API exists.

For a context tau, coloring chi, actual support S and assignment z into
original word positions, define the semantic chain constraints by

    every nonempty C contained in S:
      cup(C) => |C| <= tau.cupLimit(z(min C), z(max C));
      cap(C) => |C| <= tau.capLimit(z(min C), z(max C)).

The assignment is weakly increasing in actual sweep order, permitting
multiple points in a slot and leaving some slots empty. This predicate
does not fix cardinality and is therefore suitable for virtual B leaves.
Its eventual definition/statement must be registered through es node add;
do not introduce a global definition by hand outside ESBlueprint.

At a fixed actual deep root L below U, use child contexts
tauL=sigma.part keepL lower beta and tauU=sigma.part keepU upper alpha,
with alpha+beta=sigma.k-1. Explicitly require each new-level side, opposite
point labels in that child's extPositions1, disjoint child slot labels,
monotonicity of z, child semantic chain constraints and child strong
avoidance. For B's later application these follow from a proper partition
of original child slots in a WellFormed context. The transfer itself can
be raw with explicit hypotheses. Decomposition/realization are independent
and may be provided by the accepted fixed-support gluing theorem.

Pure lower caps and upper cups inherit parent constraints through the
existing unconditional ctx_part_limits_le. Pure lower cups and upper caps
also inherit that way, as required by the finite endpoint criterion.

For a nonempty lower cup C and an upper endpoint q before C, monotonicity
gives z(q)<=z(min C). Disjoint labels rule out equality, so it is strict.
Use the endpoint lemma with left selection true and right selection false;
the cardinal gain is1. The mirror handles an upper endpoint after C.
For two strict endpoints x<C<y, both selections give gain2. Their labels
cannot coincide around a nonempty core. Cardinalities of the inserted
sets increase exactly by1/2 because the actual supports are disjoint.
Identify their first/last points by min'/max' comparison, retaining the
original word positions. The upper-cap proof is the dual.

If C is empty, the one/two inserted endpoints form a pure set in the
opposite actual child. Its inherited cup/cap limits already apply. Thus
the positive-size premise is never dropped or used on an empty chain.
The general deepSplit_finite_endpoint_constraints_iff then supplies every
parent chain constraint, with no assumption that arbitrary predicates
are monotone under taking subsets.

For strong coupling, take a lower cup C and upper cap D. If nonempty,
the zero-gain consumer gives |C|+beta<=k-1 and |D|+alpha<=k-1, hence
|C|<=alpha and |D|<=beta. The sum is<=k-1. Empty cases use nonnegative
cardinality and the other positive child's bound; both empty is trivial.
Accepted deepSplit_strong_avoidance_iff combines this with child avoidance.

This transfer would remove the semantic endpoint/coupling step from the
virtual construction. It would still leave ordered merging of independently
constructed point domains, slot membership, empty-child conventions and
induction over B's exact interval/complement recurrence. It would not prove
N<=T, a closed sibling loss or the complete profile-maximization theorem.

Admission requires a complete unchanged general statement and proof idea,
source/isolated/full checks, audits, exact receipt/source review and a
one-node commit. If the research window does not allow that, preserve this
plan as the next exact obligation; do not claim a narrowing as a result.
