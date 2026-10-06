# Ordered cup blocks do not directly truncate Baek's alpha rows

2026-10-03 20:20UTC. Hand observation; no new Lean instance or numerical run.
The authoritative label APIs are Baek.Config.Cap4FreeSlope/cap4FreeLabel and
Baek.Config.Label.alpha inside accepted
ESBlueprint/C/CardLeChooseOfOneChangeNoCapFourNoStrong.lean.
The name binaryCap4FreeSlope in earlier discussion was an informal alias,
not a declaration. No CapFourFreeLabeling module exists here.

Take the decomposable coloring with lower{0}, upper{1,2,3}, upper a cup.
Colors012,013,023 are right;123 is left. This is a deep split because the
middle of every crossing triple is upper. There is no4cap or strong4-set;
cup rankR=3 and the least consecutive cup-block cover is d=2. The whole set
is not a cup, while singleton{0} and cup{1,2,3} form such a cover.

Cap4FreeSlope(a,b) means every earlier c forms a cup(c,a,b). Vertex0
witnesses false slopes1->2 and2->3. Hence alpha(3)>=2, while d-1=1.
Even a long pure cup block can contain a chain of false slope edges caused
by an earlier point outside that block. The proposed bound alpha<=d-1 is
false and cannot justify truncating the triangular label diagram.

This does not refute the beta-row deletion conjecture: ending-cup beta is
0,1,1,2; delta2 deletes0,1 and leaves the two-point cup{2,3}. It explains
why the desired cover reduction is a new structural statement rather than
a restatement of an existing label-range bound.

For the strong reduction, no4cap makes every strong support a cup or a cup
plus one interior right-turn apex. Existing Baek deletion can extend a long
surviving cup, but it does not automatically preserve the apex's right-turn
relations with the new point. On a quadruple o<p<a<r, one-change permits
left,left,left,right as well as left,left,right,right. Knowing that o
extends the cup containing p,r therefore does not force color(o,a,r)=right.
An endpoint/apex trace, or a different charging invariant, is required to
justify promotion to an oversized strong set. This is an obstacle to the
proposed proof route, not a refutation of the G formula or row-deletion claim.

Source reuse20:23UTC sharpens this gap. Existing public
strongPolygon_endpointSupport_isColor/strongPolygonMiddleProfile_partition
and StrongPolygonMiddleProfileInPascalWindow in
StructuralChargingPascalProfileHoles already bound the right interior count
by1 under no4cap. The accepted C proof's private
baek_cup_insert_apex_isStrong says an interior apex with a right triple at
the cup's minimum/apex/maximum suffices for strongness. Therefore promotion
needs a cupR extension preserving the apex's interior position and that
single right endpoint trace. Interior extensions keep that trace; exterior
extensions may change it. These are existing proofs, not new R24 credit.
