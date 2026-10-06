# The constructive interface needed for the finite context recurrence

Current 2026-10-04 01:16 UTC: the universal T lower leaf is fully accepted
`aebb6505`, and endpoint paths are fully accepted `fa6dacd1`. Fixed-root
assigned-limit v4 is fully accepted, unchanged type
`a89e497ebd1cfbea`, commit `e0e31525`; full validation and audits passed. Stable merging
and fuel induction remain open. B-ATTAINMENT-REMAINING-INTERFACES.md gives
the explicit lexicographic-tag placement argument and source share mapping.
Older pending snapshots below are historical.

2026-10-03 23:24 UTC. General proof design, not a registered slot-assignment
construction theorem. Universal literal history is fully accepted0930d3c7.
Endpoint-count lifting is fully accepted fa6dacd1, unchanged
type5f51f6e3b493f420, after full extraction191701-14ca1a and all five stages
of op-58b7ff64fee64da9. The general threshold lower type/body-v3 draft is
being registered via195136-0bd13d on node/DecomposableThresholdLowerExists;
no candidate acceptance yet. Assigned-slot transfer remains a separate plan.

The desired construction is not reverse literal Ctx.Satisfies. That predicate
fixes the number of points to the number of child letters. A one-run threshold
leaf of B may have more points than its available child letters; another leaf
may be empty. Both occur in the hand attaining construction.

Instead use an order-preserving assignment z from the constructed points into
the ORIGINAL child positions. Order-preserving here means weakly increasing:
multiple points may share a slot. A chain C is constrained by cupLimit or
capLimit at z(min C),z(max C); the strong bound remains k-1. The assignment
must land in the chosen child's original slots, but need not occupy every
slot. Decomposability and exact cardinality are independent requirements.
For a literal occupancy theorem one would impose additional surjectivity or
per-slot lower counts. They must not be silently inferred from B attainment.

At a recurrence root, original slots are partitioned into keep and its
complement. Child assignments have disjoint slot supports even though each
child may have multiplicities. Merge their point orders within original slots
and between slots. This produces two disjoint actual supports in a common
ambient Fin order. The accepted order-embedding extension theorem preserves
each child's coloring exactly; the accepted fixed-support profile-gluing
theorem then supplies the mixed colors and strong coupling. These theorems
do not themselves construct the slot assignment or verify its constraints.

Why one/two endpoint lifting suffices for mixed chains: an upper point
before a nonempty lower chain has an original slot x strictly before the
chain's first slot p. Weak monotonicity gives x<=p, and equality is excluded
because upper and lower slots belong to disjoint parts of the partition.
The mirror gives q<y for an upper point after the chain. If two upper
endpoints had the same slot around a lower point, weak monotonicity would
force the lower point into that same slot, again impossible. Thus distinct
opposite endpoints satisfy precisely the strict hypotheses in the general
endpoint-path-lifting candidate, even with multiplicities inside a part.

For lower cups and upper caps, the child's part already reserves the selected
zero/one/two new endpoints. Count lifting adds these gains to every old pure
extension and sibling-join candidate. The natural subtraction limit follows
using positivity of the actual nonempty chain; truncated subtraction alone
does not permit cancelling an arbitrary gain. For inherited lower caps and
upper cups, reuse CLOSED ctx_part_limits_le rather than exporting a duplicate
weak monotonicity lemma. The opposite-axis identities are also already public.

The new join maximum m controls coupling: every nonempty lower cup has size
at most k-1-m, while the other child's cap maximum is at most m. Their sum is
at most k-1. The same argument with the two sides exchanged handles the other
orientation. Empty children are discarded; they do not justify assuming a
positive sibling or saturating a maximum absent from the construction.

The remaining induction base is a GENERAL one-zone threshold lower
construction, with exact cardinality T and cap/cup/strong limits. Assign its
points to any one original slot in that run, whose endpoint limits are
constant within the run. The classical inactive construction and active
Pascal bands are described in BOUND-INTERPRETATION.md. No new general Lean
receipt for that leaf construction exists in R24. Existing small bases of the
two-cap family are internal universal-induction ingredients and do not replace
this threshold theorem.

After count lifting, the open constructive obligations are therefore:

- formulate and register the weakly increasing slot-assignment profile;
- prove merging/placement and the mixed endpoint limits for assigned supports;
- provide the general threshold lower leaf and empty/singleton conventions;
- induct over the actual finite bound recursion, retaining original slots and
  unused declared levels, then derive B<=N with optional occupancies.

Even that lower theorem would not prove N<=T or a closed formula for the
endpoint penalty. For the persistent two-cap obstruction it would justify
turning a hypothetical B=2p attaining tree into an excluded interval-root
maximizer. The general capacity upper and joint-pattern optimization remain
separate questions.
