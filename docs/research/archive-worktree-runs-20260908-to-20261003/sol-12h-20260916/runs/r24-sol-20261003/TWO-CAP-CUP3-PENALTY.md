# The cup-three gate and an exact two-point endpoint loss

2026-10-03 17:24 UTC. General hand mathematics from DS. Neither upper lemma nor exact capacity has a compiling Lean receipt. `es search "two cap blocks equal maximum force four cup"` returned no indexed theorem.

## Two equal cap blocks force a four-cup

For r>=1, a decomposable coloring on two consecutive r-point zones,each an r-cap,cannot have both global cap<=r and cup<=3. No strong bound is needed.

Induct on r. The r1 case has two points,which themselves form a2-cap. At a nontrivial root A lower,B upper,neither zone can lie entirely in B: any A point outside that zone attaches to its r-cap,creating an(r+1)-cap. Thus A meets both zones.

If B meets only one zone,the other whole r-cap lies in A. The mixed cap zone has one or two A points,and they lie outside B's zone points (one may be at either end,two must be at both ends). Suppose the mixed zone is on the right. If its first point lies in A before B,then that point together with the preceding full r-cap gives r+1 points; they cannot all be a cap,so they contain a3-cup ending at that first A point. Attaching a B point to its right gives a4-cup. Otherwise the mixed zone has only one A point,at its last position. The B(r-1)-cap,one A point from the preceding zone,and that last A point form an(r+1)-cap. Reflect for a mixed zone on the left. Hence B meets both zones.

Each mixed r-cap has one or two A points at its ends. If both zones have two A points,choose the last A of zone0 and first A of zone1,and one B point before/after them; these four points form a cup by DS. If one zone has two A points and the other one A point,there are two possibilities: the singleton A lies towards the middle,giving the same4-cup,or it lies towards the global outside. In the latter case A supplies a point before all B and a point after all B,so cap(B)<=r-2,but the zone with one A contains an(r-1)-cap inside B. Contradiction.

It remains that each zone has one A point. If both A points face the middle,a B-A-A-B4-cup appears. If both face the outside,they extend an(r-1)-cap of B to r+1. If both are first points or both last points,one A point lies globally before/after all B,so cap(B)<=r-1. B has two complete(r-1)-cap zones,cup<=3,and is decomposable. The induction hypothesis applies. This exhausts the root geometry.

The proof uses only cap-intersection geometry,extension by lower endpoints,and detection of mixed4-cups. It explains a classical endpoint obstruction rather than a SAT pattern.

## Exact critical-strong capacity

For p>=3,let strong limit s=p,and take

    Cp=[[p,p],[0,p]],Cu=[[2,3],[0,2]],r=(0,0).

Then the proposed hand result is N_p=2p-2. Both zones are caps,so each has at mostp points. The previous lemma excludes total2p. It remains to exclude p+(p-1) (and its reflection).

At any root A lower,B upper,neither zone can lie entirely in B. A whole p-zone gives cap(B)>=p and cup(A)>=1; a whole(p-1)-zone gives cap(B)>=p-1 and A contains at least the other p-zone,so cup(A)>=2. Both exceed the strong bound.

If B only meets the p-zone,that zone has one or two A points. With one,cap(B)>=p-1 and cup(A)>=2; with two,|A|>p so cup(A)>=3,and cap(B)>=p-2. Both root couplings exceedp.

If B only meets the(p-1)-zone,one A point there gives |A|>p and cap(B)=p-2,again too strong. Two A points give cap(B)=p-3,but they surround its B points. The nearer A endpoint together with the full p-cap cannot be a(p+1)-cap,so it creates a3-cup that the interior B point extends to a4-cup. For p3 this two-endpoint case leaves no B point and is not a root.

Thus B meets both zones,and A also meets both. In the full p-zone,A has at most2 points; cup(A)>=2 forces cap(B)<=p-2,so A has exactly2 points there,cap(B)=p-2,and cup(A)=2. If A has two points in the other zone,the two inner A endpoints and B points on either side give a4-cup. If it has one,then B has two full(p-2)-cap zones,cap<=p-2,cup<=3; the first lemma excludes them. Thus total2p-1 is impossible.

## General lower construction

For p>=4,form A from a lower p-cap in zone0 and an upper singleton at the last position of zone1. It has p+1 points,cap p,cup3,strong max3. At a new root,put an upper(p-3)-cap B after zone0 and before that singleton. The whole zone1 is a(p-2)-cap. Its endpoint cap,cup and root coupling bounds are

    cap<=max(p,(p-3)+2)=p,
    cup<=3,
    strong<=max(3,3+(p-3))=p.

Every3-cup of A ends at its last singleton,and no B point is to the right of it or to the left of its zone0 start,so it cannot extend to a4-cup. Mixed cups from a2-cup of A can add only one B endpoint,because all B points lie in the same gap after zone0. This establishes the cup bound. The total is(p+1)+(p-3)=2p-2. For p3,omit empty B and use A alone (four points,cap3,cup3,strong3).

Consequently reducing the cross-zone cup bound from4 to3 in the critical-strong two-cap profile changes its exact true capacity from2p to2p-2,an endpoint loss of2. Without the strong bound,the same construction with B sizep-2 gives2p-1 points and strongp+1; the first lemma supplies the matching upper2p-1. The strong coupling contributes one of the two lost points.

This is a proposed exact parameterized penalty,not a scalar formula for arbitrary profiles. It must be independently checked before use in further exact covers. A small p3/p4 probe can refute the hand proof; passing cases cannot certify it. The lower construction and the root proof should be audited separately,and any implementation should reuse existing DS construction/verification code.
