# A persistent interval-root obstruction in reachable profiles

2026-10-03 17:28 UTC. General hand proof under the audited DS identities.
Explicit constructions and finite root checks are diagnostic. The general
root-incidence theorem now has an accepted Lean receipt; full extraction and
repository audit are pending. The literal p5 finite B9 receipt and unchanged-C
arbitrary child4/6 receipts are now complete;parent B uses the hand-equivalent
matrix-state backend,not a kernel-certified reduction.

## Exact capacity

For p>=4 put s=p and take two ordered zones with

    Cp = [[p,p],[0,p]], Cu = [[2,4],[0,2]].

Their optional maximum, and the maximum with p required points in each zone,
is exactly2p. The upper is elementary: cup<=2 makes each zone a cap, and
global cap<=p allows at mostp points in either zone.

The following general construction attains2p with strong maximum p. Let X_p
have p points in each zone, each zone a p-cap, global cap<=p and cup<=4.

- Base X_2 is a4-cup divided into two pairs; it has cap2 and strong4.
- Base X_3 starts with the classical6-point cap3/cup3 tree. Keep its first
  three cap points and two of its last three cup points. Add an upper
  singleton between the last pair. The first zone remains a3-cap; the second
  becomes a3-cap. Opposite-color singleton caps have rank<=3, cups grow by at
  most one, and the root coupling is at most3+1. Thus cap3,cup4,strong4.
- For p>=4, put a lower4-cap A and an upper copy B=X_(p-2) at a new root.
  Place one point of A before and one after B in each zone, preserving A's
  and B's internal orders. Then every zone is a p-cap. Globally, caps have
  size at most max(4,(p-2)+2)=p; cups at most max(4,2+2)=4. DS gives strong
  maximum max(strong(A),strong(B),2+(p-2))=p. The p=2/3 bases have strong4,
  which is admissible when used inside the p=4/5 constructions.

The bases are construction ingredients, not claims that strong2/3 admits
4/6 points. The conclusion N_p=2p starts atp4.

## Every maximal root is forced and noninterval

Take any decomposable2p-point candidate with this profile and strong<=p, not
just the displayed construction. Both zones must be full p-caps. Let A<<B
be any nontrivial DS root, with A lower and B upper.

No zone can lie entirely in B: that gives cap(B)>=p and cup(A)>=1, hence a
strong(p+1)-set by DS.

B cannot meet only one zone. If it occupied that whole zone the previous
argument applies. Otherwise the other p-cap is contained in A and A has at
least one further point, so |A|>p. Since A has no(p+1)-cap, A is not a cap,
and therefore contains a3-cup. The mixed full p-cap in B's zone has at most
two lower points, so cap(B)=|B|>=p-2. The root coupling is then at least
3+(p-2)=p+1, again impossible.

Consequently A and B both meet both zones. In each mixed p-cap, the DS cap
intersection bound gives |A intersect Z_i|<=2. Since A has at least two
points, cup(A)>=2, so the strong coupling gives cap(B)<=p-2. But B intersect
Z_i is itself a cap of size p-|A intersect Z_i|>=p-2. Hence equality holds:

    |A intersect Z_0|=|A intersect Z_1|=2,
    cap(B)=p-2, cup(A)=2, |A|=4, |B|=2p-4.

The two lower points of a mixed cap must surround all its upper points.
Otherwise two lower points and an upper point give a left-turn triple whose
middle point is lower, contradicting that the full zone is a cap. Thus A is
exactly the first and last point of each zone, and B is exactly the two zone
interiors. Since p>=4, both interiors are nonempty. A has gaps inside both
zones; B has a gap across the zone boundary. Neither is an interval in the
whole parent sweep order.

This proves that **no maximizer for this family has an interval-child root**.
It is an optimization obstruction, stronger than the six-point example in
`interval-root-obstruction-strong4.json`, where changing the coloring restores
an interval-root optimum. It follows directly from endpoint geometry and
strong coupling, without enumerating all extremal colorings.

## These profiles occur in actual singleton histories

For p>=5 set a=k=p+1,u=5, maxima=(1,1,1), and take

    sigma = S^l 1L 3L 2L S^r, l,r>=1.

The cap limits are constantlyp. In either child run the cup extension count
is2 and strong extension is3; spanning both runs these are0 and1. Therefore
the cup matrix is exactly[[2,4],[0,2]] for every l,r. At l=r=p the word has
2p child positions and X_p satisfies its exact minimum-slot profile.

The three external letters are one actual singleton at each declared level,
all on the upper sibling side (L is the kept-child side). Attaching those
singletons gives2p+3 total points with cap/cup/strong maxima p/4/p. This
supplies an actual ancestor history, rather than a raw declaration with an
impossible sibling maximum. The p4 case is excluded from this context claim:
its spanning cup strong limit would be3 rather than4.

`Ctx.Satisfies` in `DecomposableContext.lean:203` fixes the child-position count
and requires all endpoint cup/cap bounds and the strong bound on the child.
It imposes no additional occupancy condition beyond that correspondence.
For l=r=p, the checked X_p has exactly2p points and fills those two runs.
These are the exact hypotheses needed for the literal cardinality question.

## Consequence for the retained finite recurrence

The hand construction theorem in `VIRTUAL-CUT-LOWER-PROOF.md` gives an attaining
B tree in original slot order. At every positive-positive recurrence node,
one part is an interval of the current child slots, hence an interval of the
constructed points. Zero children can be discarded without changing that
fact. A one-run T leaf cannot contain points in both original zones, because
the original external letters are retained at every virtual cut.

If B(sigma)=2p, its attaining tree must occupy both full zones. Its first
positive-positive node after discarding zero ancestors would be an actual
interval-child root. The preceding forced-root theorem excludes that.
Together with B<=N=2p, this hand argument gives

    B(S^l 1L3L2L S^r) <= 2p-1 for every finite l,r>=1.

Thus the interval/complement restriction, not merely inadequate slot
resolution, causes a persistent gap. At l=r=p it also refutes the literal
cardinality upper S.card<=B under these hand arguments. A finite-matrix
recurrence calculation gives B9 atp5,l=r5. The general nested interior lower
construction in `PREFIX-DOMINATION-OBSTRUCTION.md` attains2p-1 with only1+3
slots. The hand exact value is therefore2p-1 once a run has at least3 slots.
Kernel certification remains open;the numeric parent result uses the
hand-equivalent matrix-state backend.

Allowing the forced arbitrary subset (the four zone endpoints) removes this
root obstruction. The unchanged-C p5 arbitrary children have B4 andB6,
sum10>B9,as stored in `literal-cap-receipt-p5.json`. The upper child's relaxed
strong bound permits an interval construction of both3-cap zones. This is
also a diagnostic refutation of full finite-bound additivity,with the parent
backend qualification retained.

## Receipts and next formal obligation

Job `20261003-124348-ebade8` constructs X_5 in0.005s:10-point cap5/cup4/strong5,
two5-cap zones,90 interval/complement root failures with explicit violating
triples, and a13-point actual singleton history with5/4/5 maxima. Artifact
`two-cap-blocks-p5.json`. The broader p4..8 verification is separate.

The general root-incidence obligation is compiled as
`ErdosSzekeres.two_full_cap_blocks_root_structure`, locked type
`84e6237f7f3a6146`, with only `propext`, `Classical.choice`, and `Quot.sound`.
Isolated accepted job `20261003-134701-7e1d3c` has receipt
`d1b02ae6c07291c7d0997408ea5a2093f03716be0701b59c24ff7c7a0b1135e6`;
original-source check `20261003-134841-d86a75` also passes. The registered
statement requires no order separation: it proves lower intersections2+2,
lower cardinal4/cap, upper cardinal2p-4 and cap rankp-2. Full extraction
`20261003-134932-d2c521`, axiom/layer audits and review passed in
`op-130d007913064c93`; one-node commit
`13b050e1a9259605e864a30c7f1516699c5be18e` preserves the unchanged statement.

The endpoint/four-cup/noninterval consequence has isolated/source acceptance
as `two_full_cap_blocks_root_noninterval`, type50cecd70f72957e5; full extraction
`20261003-142251-748654`, audits and review all passed. Commit
`0422f8c765737dd921bf04f54781dee3acab819a` pins the unchanged statement.
Its proof is recorded
in `ROOT-ENDPOINT-PROOF-PLAN.md`. The
construction can reuse the already certified upper-singleton rank-three and
strong-transition facts. The finite-B implication also needs the general
extension/gluing interface, unless a concrete numerical bound is certified
directly. Neither the construction nor the B interface has a new kernel receipt.
