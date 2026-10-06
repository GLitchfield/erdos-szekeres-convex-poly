# Diagonal proof plan

Updated2026-10-03T05:06Z. The structural plan below is now formalized in
accepted exact Lean helpers. Z-prime:20261002-234842-f12d34;
endpoint extensions:20261002-235448-9f5cae; R1:20261003-000353-78b053;
adjacent-pair deficit:20261003-000935-deaead; R2:20261003-001609-4350b7;
full diagonal root:20261003-002306-951371. Each has no sorry, standard
axioms only and an original-source receipt in this directory. Exact
locked statements and commits are in MATHEMATICAL-HANDOFF.md.

The exact diagonal gate source compiles first try,20261003-002559-692f37.
Full original-source acceptance20261003-002634-6a5ff2 is ACCEPTED with
exact hash87bbef437ea7141f, no sorry and standard axioms only. Gate commit
5d4fa26d8a20192c90624b23ed8a9cef90af8dd1. Exact R20/R21 inputs remain those
in RESEARCH-BRIEF.md and AUDITED-PROOF-5kk.md. The predecessor gate is
accepted at0281d8bbf6ec782323840a4c2643153a648124fb.

Implementation refinements: R1 uses occupancy of only the first/last lower
cup blocks. Both occupied force upper<=3; missing outer block permits the
classic lower pair bound; neither occupied leaves the middle cup. R2 uses
chosen lower witnesses, avoiding all lower-extremum selectors. Its mixed
upper<=2k-3 argument covers both3cap and4cap upper children uniformly.
The adjacent-pair deficit needs no whole5cap hypothesis. The final root
retains global extremes for normalization, and at k6 its final both4cap
case contradicts lower square<=1. Arithmetic nlinarith uses only the exact
cardinal bounds to avoid irrelevant-context heartbeat growth.

## Keep helper imports thin

Existing `diagonal_cup_block_card_add_le` in
StructuralChargingPascalCupBlocks.lean converts the exact R20 contract into
the fixed-k count for two ordered cups with one-change, no4cap, no k-cup and
no strong k-set: total<=2k-4. A strong-free set is k-cup-free by
IsCupSet.isStrongPolygonSet. Thin R1/R2 helpers may take this count as an
explicit hypothesis, with the final gate supplying it from hblocks.
The final gate must still state the exact uniform hblocks/hbaek signatures.

## Z prime (audited Lemma7)

For P cup before Q4cf, no5cap/no uCup, prove
P.card+Q.card<=choose(u,2)+u-2. Short P<=u-2 uses triangular Q directly.
At P=u-1 move p=maxP into Q and erase it from P. A4cap in insert p Q must
start at p; the turn with z=max(P.erase p) either extends P to a uCup or
prepends z to a5cap. Thus the new Q is4cf, its triangle bound loses one
point, and the total improves to the target. This already compiled as a
subargument of the predecessor R2 wrapper and avoids a new first-cap rank.

## R1: three decomposable cups (audited Lemma8)

Expose a genuine root A<<B, then use concrete cap witnesses.
B singleton: coupling excludes (k-1)CupA, three-cup bound gives3k-9,+1.
B cup of size>=2: coupling excludes(k-2)CupA. If A misses a block, two-cup
bound gives2k-7 plus B<=k-1. If A meets all three, B<=3 and three-cup
bound gives3k-12. Bhas3cap: coupling excludes(k-3)CupA; BbeforemaxA and
BafterminA are cups because an outside3cap gains an A endpoint to4cap.
Aone block gives<=k-4, Btwo cups uses supplied2k-4. Atwo blocks uses
2k-9, and an outer B piece has at most one point while its complement is a
cup of at most k-1. Aallthree blocks has<=3(k-4) and B<=3.

Baseline `HasDeepBelowSplit.upper_mem_cup_isSweepEndpoint` (Decomposable.lean:799)
already supplies the outside one-point fact: every upper point in a cup
crossing the split is a sweep endpoint. Two upper points on one side of a
lower member would make one of them interior. Reuse this API rather than
constructing another cap-triple witness. Its companion
cup_inter_upper_card_le_two supplies the coarser intersection bound.

The geometric small-B facts are: middle Bpoints have cardinal<=1 since
two such points plus minA/maxA make a4cap; if A meets the first/last block,
the corresponding outside Bpiece has cardinal<=1 because two Bpoints plus
that A extreme would be a cap triple inside the original cup block.

## R2: regroup audited Lemma9 by A's position in P|Q

Implementation simplification at03:30Z: the R1/R2 auxiliary partitions
need chosen lower points, not global extrema. In R1 use any lower point
in the first/last original cup block for the outside one-point facts; when
both are present, partition B around those two points to get B<=3. Any
lower point gives the two upper cups from whole4cf. In R2 all-Q/all-P cases
use any lower point a in that block. In the mixed case use any a in A∩P
and b in A∩Q; P<Q gives a<b. The same outside/middle/last geometry applies
and covers B since chosen lower points are excluded from B by disjointness.
This avoids all minA/maxA selector and membership proofs in R1/R2. The
global-extrema normalization in the final diagonal root remains necessary.

For V=Pcup|Q4cf, decomp, no5cap/no kCup/noStrongk, target
T*=1+choose(k-1,2)+k-4.
Expose root A<<B, retain decompB. Singleton B uses predecessor R2 at u=k-1
on A; Bcup size>=2 uses Z prime at u=k-2 plus B<=k-1.

When Bcontains3cap but is4cf, coupling gives no(k-3)CupA:

- A entirely in P: A<=k-4; supplied Baek bounds B by1+choose(k-1,2).
- A entirely in Q: triangle A<=choose(k-3,2). B splits into Ppart, Qbefore
  minA, QafterminA. Both Qparts are cups: any3cap plus the A endpoint would
  make a4cap inside Q. R1 on decompB gives B<=3k-8. This works irrespective
  of which root part contains the outer sweep points.
- A meets both: a=minA lies in P, b=maxA lies in Q. Bbeforea has<=1 point
  (a cap triple would lie in Pcup); Bbetween a,b is a cup (3cap gains both
  endpoints to5cap), and Bafterb is a cup (3cap gains b to4cap in Q).
  Supplied two-cup count gives the latter two pieces<=2k-4, so B<=2k-3.
  Z prime at u=k-3 on A then yields exactly T*.

This removes the audited AB/BA/BB subcase distinction for the beta3 branch.
Each stronger estimate has a stated geometric reason; no coverage is dropped.

When Bcontains4cap, coupling gives no(k-4)CupA:

- A entirely in P: every4capB has its first point before minA (else gains
  minA to5cap). That prefix has<=1 point; deleting it leaves B4cf. Baek gives
  B<=2+choose(k-1,2), and A<=k-5 gives T*.
- A mixed: same prefix<=1; BafterminA is4cf by endpoint gain, and its two
  pieces (middle/aftermaxA) are cups. Supplied count gives B<=2k-3. Z prime
  u=k-4 suffices with slack uniformly even at k6, provided Z prime is proved
  for u>=2. Its u2 case is immediate: no2Cup means the whole set has<=1 point.
- A entirely in Q: triangle A<=choose(k-4,2). The three Bcups above have
  both adjacent pairs4cf: beforeminA a4cap would gain that endpoint to5cap;
  afterminA lies in Q. Adjacent pair counts give B<=3k-5. This suffices for
  k>=7; at k6 use the audited extremal deficit (double dagger). If that
  deficit is proved uniformly as B<=3k-6, it closes this case uniformly for
  all k>=6 with no separate small-parameter branch.

## Extremal three-cup deficit (double dagger)

For P|Y|X cups, adjacent pairs4cf with counts<=2k-4, whole no5cap/no kCup/
noStrongk, equality at3k-5 forces P=X=k-1,Y=k-3. Let p=maxP, xi=minX.
The certified two-cup forced extensions imply p+Y and Y+xi are cups;
one-change glues them to M=p+Y+xi, a(k-1)Cup. Reuse the accepted
threeCupBlocks theorem's local hglue proof: choose the last two Y points,
then apply maximum insertion to p+Y using the turn from Y+xi. This is
simpler than a fresh consecutive-triple case analysis and has the same
semantics.

Let pPrev be the predecessor of p. Turn(pPrev,p,xi) must be cap, else P+xi
is a kCup. Turn(pPrev,y1,y2) must also be cap, else pPrev+Y+xi is a(k-1)Cup
with the same endpoints as that3cap, forming a strong k-set by the accepted
common-endpoint bridge. Four-cap-freeness of P+Y forces the preceding turn
(pPrevPrev,pPrev,y1) to be cup, so P-minus-p+y1 is a(k-1)Cup.
Finally turn(p1,p,y1) cup extends M to a kCup; cap gives a3cap sharing the
endpoints of P-minus-p+y1 and therefore a strong k-set. Both contradict.
All chosen predecessor points exist since k>=6 and |P|=k-1; Y has>=3 points.

Lean selector plan: use p=maxP, Z=P.erase p, pPrev=maxZ, and
pPrevPrev=max(Z.erase pPrev), rather than variable-sized Fin indices. Existing
max-insertion lemmas accept exactly these last-two/predecessor contracts.
Take p1=minP, y1=minY, y2=min(Y.erase y1), xi=minX. k>=6 guarantees all
required nonempty erased sets. The current predecessor R2 wrapper already
compiles these min/max/erase contracts.

For gluing p+Y and Y+xi, the accepted consecutive-chain theorem suffices:
a consecutive triple containing both outer endpoints is impossible when
Y has at least two points; every other consecutive triple belongs to one
of the two cups. This can keep the glue proof thin without importing the
large cupblock module's existing two-endpoint glue theorem.

The double-dagger argument itself does not use whole-set five-cap-freeness;
adjacent-pair four-cap-freeness, pair counts, one-change, and strong-freeness
are enough. Record this exact semantic scope if exposed as a helper.

## Diagonal genuine-root bound (reviewed plan at03:26Z)

Retain decomposability of both children A,B. Put
G=choose(k-1,2)+choose(k-3,2)+1=(k-3)^2+k-1.
Use one global order reversal and the same thin geometry as the predecessor
root. Reflection transports decomposability without swapping child labels.
The local predecessor application to a child S needs no(k-1)-cup; for
card(S)>=2 expose its genuine root, inherit the gap exclusions and apply
the accepted predecessor root. For card(S)<=1 the bound is immediate.

NN (minimum lower, maximum upper): B is4cf by lower endpoint extension.
The upper maximum implies A has no(k-1)-cup. If B is a cup with at least
two points, coupling2 gives no(k-2)-cupA, so square(k-3)^2 plus B<=k-1
equals G. If B is singleton, use the predecessor bound H on A and add1.
If B has a3-cap, coupling3 gives no(k-3)-cupA. If A lies left of q,
triangle choose(k-3,2) plus Baek(B)<=1+choose(k-1,2) equals G. Otherwise
the same two-cup upper partition as the predecessor proof gives B<=2k-3,
while square(k-4)^2 on A has sufficient slack (k-5).

N1 (both outer endpoints lower): B is a cup. Size>=2 uses coupling2 and
the square as above. For a singleton B, coupling1 gives no(k-1)-cupA;
use decomposable predecessor bound H. Do not assume the singleton upper
point is outside every cup: it may lie inside the lower sweep span.

N2 (both endpoints upper): gaining both upper endpoints gives A no
(k-2)-cup. If B is a cup, square(k-3)^2+B<=k-1 gives G. If B is4cf but
has a3-cap, coupling3 gives no(k-3)-cupA. Four-cap-free A uses the triangle
plus Baek on B. If A has a4-cap, it crosses q and gives three ordered upper
cup pieces; R1 bounds B by3k-8, and square(k-4)^2 on A makes exactly G.

If B has a4-cap, coupling4 gives no(k-4)-cupA. Four-cap-free A uses
triangle choose(k-4,2), while B is an ordered cup prefix/4cf suffix and
R2 yields T*=1+choose(k-1,2)+k-4. Their sum is G by Pascal. If A also has
a4-cap, square(k-5)^2 applies. Its three upper cup pieces have first two
4cf by outside endpoint extension, so classic two-cup plus last-cup bounds
give B<=3k-4. This is <=G after adding the square for k>=7, with slack
2k-13. At k=6, A<=1 from the square contradicts card(A)>=4 from its4-cap.

If the full root set is entirely on one side of q, it is4cf and Baek gives
1+choose(k-1,2)<=G directly. This handles the one-sided branches before
normalizing the endpoint configuration.

The exact diagonal gate needs upper reservoir G+1=H+2. Its threshold
differs from the predecessor threshold by1: the Pascal-row window adds
the top term choose(k-2,k-2)=1. Prove this locally in the final gate, then
reuse the accepted predecessor threshold identity and child-root wrapper.
