# BDL: the exact remaining root obligation

Live paper account, 2026-10-04 02:34 UTC. **BDL is unproved and unrefuted.** This file
states the exact unresolved root case and proves its conditional equivalence
to BDL. Full-core BRL+ is stronger and diagnostically refuted by paper82;
its conditional implication below does not supply a proof premise.
Detailed arguments, rejected routes
and evidence are in BDL-OBSTRUCTION.md; current state is in
MATHEMATICAL-HANDOFF.md. There is no new Lean theorem or receipt.

## Definitions and accepted input

For a finite ordered triple coloring write c,d,sigma for maximum cup, cap
and strong-set cardinalities, with zero on the empty set. A strong set has
the defining equalities on every increasing quadruple; a cup or cap has a
single color on every triple. All decomposable colorings satisfy one-change.

Fix s>=1. A valid band partition on integer indices[l,h] assigns each
point exactly one j, with c(X_j)<=j+1 and d(X_j)<=s-j. Empty cells are
allowed. BDL asks for this partition on[s-beta,alpha-1] when

  sigma(X)<=s, alpha=c(X), beta=d(X), alpha+beta>=s+1.

The audited DS law at a decomposable root X=A<<B is the input. Put
p=c(A),q=d(A),r=c(B),t=d(B). Then

  sigma(X)=max(sigma(A),sigma(B),p+t),
  c(X)<=max(r,p+2), d(X)<=max(q,t+2).

A cup meeting A uses a cup of A and at most one B point at each end.
Caps have the dual description. Decomposability and exclusions are
hereditary. Accepted source: primary checkout
runs/claude-audit-667-20261003/AUDITED-PROOF-667.md section6.1; the
crossing cup/cap strong-set construction is already compiled in
ErdosSzekeres.Decomposable.

Another accepted fact is the endpoint split for |X|>=2, hence alpha,beta>=2.
If F is the set of first
points of maximum beta-caps, then c(F)<=alpha-1 and d(X minus F)<=beta-1.
For the first bound, a maximum alpha-cup in F would end where a maximum
beta-cap starts. The common-endpoint extension theorem gives a larger cup
or cap, contradiction. The last-point version follows by x-reversal.
The R23 compiled common-endpoint input is preserved on
node/ContainsCupSetSuccOrContainsCapSetSuccOfOneChangeCommonEndpoint,
commit7806d5c4; it has not been imported or changed here. Its exact
statement assumes both chains have at least2 points and cup maximum
equal to cap minimum, with OneChangeOn the union. The node is absent
from the current branch index; its retained branch receipt is separate.
Searches for
`tight nested absorption band` and `core band decomposition` found no
existing general band theorem.

## Exact unresolved root case

Let beta>=4,l=s-beta>=1,alpha+beta>=s+3. Let A,B be nonempty
decomposable parts with the deep-below root X=A<<B, satisfying

  c(A)=l, c(B)=alpha, d(B)=d(X)=beta, sigma(X)<=s.

Suppose a valid partition of B on[l,alpha-1] is supplied, and a maximum
beta-cap of X meets BOTH A and B. **The missing
obligation is to construct a valid partition of X on the same indices.**
It can rearrange all child points; it is not required to extend the
supplied assignment. Since l+2<alpha, DS implies c(X)=alpha.

Paper68 closes one further general case. If X and B have the SAME
maximum-beta-cap core, every parent maximum beta-cap stays entirely in B:
a new one would have an A endpoint strictly inside the old core and
strictly shrink it. Put ALL A into the SECOND supplied band l+1.
Its cups have at most max(c(B_(l+1)),l+2)<=l+2 points; a beta-cap
there cannot stay entirely in B_(l+1) or meet A. Its cap is therefore
<=beta-1. Every other band stays valid. This works at every m>=3.

The conservation construction is an explicit closed paper case,
not a Lean theorem. Semantic
audit192948-6ebf40 passed0.337776305s/10MiB, including every eligible
second-band subset on the retained tight conserved-core n12 spine.
Details and the dual penultimate insertion are paper68.

Paper81 closes the broader case in which NO maximum beta-cap meets BOTH
children, even when pure beta-caps in A strictly contract the core. If
d(A)<beta let F be empty; otherwise take the first points of all maximum
beta-caps of A. The endpoint split gives c(F)<=l-1 and
d(A minus F)<=beta-1. In the latter case l>=2, because l=1 would make
A a singleton, so both endpoint chains meet the compiled theorem's
cardinality>=2 hypotheses. Replace the first two supplied cells by

  new_l     = B_l union F,
  new_(l+1) = B_(l+1) union(A minus F).

Bottom cups have size at most max(l+1,l-1+2)=l+1, and its cap bound
beta holds by containment in X. Second cups have size at most l+2.
Both pure second-band parts have cap number<=beta-1; a mixed beta-cap
would contradict the global assumption. All other cells stay unchanged.
This works for EVERY supplied valid B map, without ancestor constraints.
It contains conservation as the F-empty subcase.

Thus the exact missing obligation for this reduction requires a genuinely
MIXED maximum beta-cap. Such a cap has an A endpoint inside the old B
core and strictly contracts it. Pure-only contraction is closed. BDL
implies this restricted obligation; paper81 and the other closing cases
below give the converse conditional reduction. The diagnostic replay
20261003-215341-49dcb5 passed0.207469503s/7MiB at p2/beta5/m3,n15:
strictly contracting pure-only caps and endpoint peeling validate in
pure-maximum-closure-certificate.json. Neither the paper construction nor
the replay is a new Lean theorem or a proof of the remaining mixed case.

Paper73 bounds core-changing insertions on a constant-profile demand>=3
chain by charged endpoint caps/cups. This does not allow deleting its
conserved stretches: paper74's uniform construction preserves c,d,sigma
and exact maximum-chain families at an inner step but creates a regional
(beta-1)-cap used by an outer maximum cap. The missing construction still
needs compatible regional nearmaximum-chain information. Neither the
event count nor this state obstruction changes the exact ROOT below.

This root has explicit structure. A is classic: c(A)+d(A)<=l+beta=s.
Its strong number is at most s-2 (or it is a singleton). Every maximum
beta-cap of B strictly surrounds EVERY A point: an exterior lower point
would extend that cap to beta+1. Therefore, with

  L*=max first(D), R*=min last(D) over maximum beta-caps D in B,

we have L*<min(A)<=max(A)<R*. The bottom cup bound l+1 misses the raw
mixed bound l+2 by precisely one. This geometry is why this case is the
specific remaining problem; identifying it is not a new proof result.

The root also supplies a visible TWO-endpoint constraint:

  d(B intersect(min A,max A))<=beta-2.

Otherwise the two A extrema and a(beta-1)-cap strictly between them form
a mixed(beta+1)-cap. Together with d(A)<=beta and strict enclosure by
every maximum B cap, this condition is EXACTLY equivalent to retained
cap d(X)=beta: every oversized mixed cap has one exterior A endpoint
and a beta-cap, or two A endpoints and an internal(beta-1)-cap. An empty
singleton span contributes zero. Section58 gives the full DS proof and
the independent complete n<=6 semantic audit173627-983795.

The full BDL immediately implies this root obligation. Conversely the
root obligation, for all stated parameters and its cup/cap dual, suffices
for BDL by the following size induction. Thus this is the exact residual
obligation for the audited reduction, rather than an unproved auxiliary
invariant silently assumed to be preserved.

## Conditional size induction

Before the induction, the hard-root hypotheses can be unfolded completely.
Write p=s-beta and m=alpha-p. Its parameter range is

  p>=1, beta>=4, 3<=m<=beta, s=p+beta, alpha=p+m.

Equivalently take nonempty decomposable A,B with A<<B, c(A)=p,
d(A)<=beta, c(B)=p+m,d(B)=beta,sigma(B)<=p+beta, and a supplied
valid B partition. Require every A point strictly inside every maximum
beta-cap of B and d(B intersect span(A))<=beta-2. These are all the
retention hypotheses. For the unresolved case also require

  d(B_<maxA)=beta-1 OR d(B_>minA)=beta-1 OR
  (|A|>=2 AND d(B intersect span(A))=beta-2).

This is exactly mixed maximum-cap existence: a mixed cap uses one or two
A endpoints; each displayed threshold constructs the corresponding cap.
Retention gives the upper bounds beta-1,beta-1,beta-2, so an attained
threshold is an equality. A is classic. If |A|>=2, middle determinacy gives
sigma(A)<=c(A)+d(A)-2<=s-2; if |A|=1 its strong number1 is also<=s-2
since s>=5. DS then gives sigma(X)=s EXACTLY, cup(X)=p+m,cap(X)=beta.
Conversely the original hard root supplies every one of these inputs.

After subtracting p from the band labels, the missing construction is a
partition of A union B into h=0,...,m-1 with

  cup(X_h)<=p+h+1, cap(X_h)<=beta-h.

This is an equivalent statement of the same open obligation, not a new
narrowing or solved invariant. It exposes the saturated strong join and
the precise sibling window that a preserved context theorem must use.
One cannot replace arbitrary A by a single chosen p-cup without a proof.
The parent may distribute A among bands; all-A-bottom normalization and
full-core BRL are separately stronger. Full-core BRL+ is diagnostically
refuted below; sibling-specific all-A-bottom normalization remains unproved.

The statements below close all other roots, without requiring the supplied
child partition to be canonical.

Use induction on |X| for fixed s, assuming the root obligation.

The empty set is inactive for s>=1. If s=1, the quadruple definition of
strong sets makes every pair strong, so |X|<=1; any active instance is
the singleton in band0. If s=2, every triple is strong, so |X|<=2; an
active two-point instance splits into singleton bands0,1. For every
two-band instance with s>=1, |X|>=2, hence alpha,beta>=2 and the
endpoint theorem's nondegenerate chain hypotheses hold. These facts use
the definitions in Decomposable.lean, not a new compiled theorem here.

If alpha+beta=s+1, all X fits the single band j=alpha-1=s-beta.
If alpha+beta=s+2, put the first maximum-cap points F in j=alpha-2
and X minus F in j+1. The endpoint bounds are exactly the two required
limits; no decomposition or positional induction is needed. In particular
this covers all roots whose classic, one-band or two-band upper child
could occur in tight absorption. For the explicit classic/one-band child
split independent of this shortcut, see BDL-OBSTRUCTION.md section5.

It remains to consider alpha+beta>=s+3. Write l=s-beta,h=alpha-1
at X=A<<B. DS gives p+t<=s. A child is classic if its cup and cap
numbers sum to at most s; otherwise the size IH supplies its own bands.

**Both maxima strict: beta>t and alpha>p.** A nonclassic A retains
[s-q,p-1], a nonclassic B retains[s-t,r-1]. The ranges lie inside[l,h]
and are separated because p-1<s-t. A classic A fits whole in
j_A=max(p-1,l), with j_A<=s-q and j_A<s-t. A classic B fits whole
in j_B=min(s-t,h), with j_B>=r-1 and j_B>=p. These indices lie in
the parent range. If both are classic, j_A<j_B: use j_B>=p when
j_A=p-1, and s-t>l,h>=l+1 when j_A=l. Thus every band uses only
one child, preserving all chain limits.

**Retained cap: beta=t.** Then p<=l and A is classic. If p<=l-1,
mixed cups have length<=p+2<=l+1. The parent's three-or-more-band
assumption forces r=alpha, since its cup number cannot come from those
mixed cups. Hence B has the same natural band range, supplied by the IH.
Add all A to B's bottom. Its cup bound holds by DS, and its cap bound
beta holds by containment in X. Other cells are unchanged.

If p=l, all maximum caps of B surround A as above, and again r=alpha
because alpha>=l+3>p+2. For beta>=4, paper81 closes the root if no
maximum beta-cap meets BOTH children; otherwise it is exactly the
unresolved mixed root obligation. The beta<=3 boundary is closed below.

**Retained cup: alpha=p.** Dualize the coloring and interchange the
root parts, then apply the retained-cap argument. Band j becomes s-1-j,
turning the old cap bound into the new cup bound and conversely. The
dual root's positive bottom is the cup number of its nonempty lower part.

Both maxima cannot be retained: alpha=p,beta=t would give
alpha+beta=p+t<=s. The three cases above are exhaustive. This completes
the CONDITIONAL induction. It supplies no construction in the unresolved
root case. ∎

## Why maximum cap size three is a closed boundary

In a genuinely three-or-more-band retained-cap root with beta=3,
alpha>=s and alpha<=sigma(X)<=s, so alpha=s. Positive bottom gives s>=4.
B has an open maximum-three-cap core. Cutting at an empty gap in that
core divides B into two spatial cups: neither side can contain a three-cap.

The existing ordered-two-cup theorem, at k=s+1>=5, gives |B|<=2s-2.
Its hypotheses hold because there is no four-cap, cup(s+1), or strong(s+1).
Compiled inputs are diagonalCupBlocksForce4kk_of_five_le and
diagonal_cup_block_card_add_le; this application is reuse of the earlier
R20 result, not a new theorem. Source: ESBlueprint/B/
DiagonalCupBlocksForce4kkOfFiveLe.lean and
ErdosSzekeres/StructuralChargingPascalCupBlocks.lean.

Let F be first points of maximum three-caps and G its complement.
Both are cups: F lies at or left of the core, and G contains no maximum
cap. We have |F|<=s-1,|G|<=s and |F|+|G|<=2s-2. Construct bands
s-3,s-2,s-1 as follows. If |F|=s-1, move one F point to the top,
put remaining F at bottom and G in the middle. Otherwise put F at bottom;
if |G|=s move one G point to the top, and put its remainder in the middle.
The bottom/middle cup bounds are s-2,s-1, their cap bounds3,2, and the
top is at most a singleton. The bottom lies wholly at or left of L*.
The last-point mirror gives the right choice. Either choice absorbs A.
All beta=3 hard roots therefore close. For beta<=2, a genuinely
multiband open-core child cannot occur. Detailed proof and operation
audits are in BDL-OBSTRUCTION.md sections41-43. ∎

## The stronger sufficient realignment lemma BRL+

There is a more precise sibling-aware sufficient condition before asking
for full-core positioning. Let C be the bottom of a valid B partition.
Since c(C)<=l+1, DS gives the exact equivalence

  c(A union C)<=l+1
    iff c(A intersect(min C,max C))<=l-1,

with empty span when |C|<2. A mixed forbidden(l+2)-cup consists exactly
of a maximum l-cup of A bracketed by two C endpoints. Parent cap retention
already bounds the new bottom's cap. Thus finding a child partition with
this span avoidance is EQUIVALENT to a parent partition putting ALL A
in bottom. For l1, C must lie on one side of the singleton; for l2, C's
span may contain at most one A point. General l uses A's actual interval
cup rank. The ordinary root obligation can put A in several bands and
is weaker. This normalization/selection lemma is unproved.

The implications are: full-core BRL => sibling-aware span avoidance
<=> parent with all A in bottom => ordinary root obligation. No reverse
implication to full-core BRL or normalization is claimed. The actual root's
beta-2 interior cap window is retained in the sibling-aware formulation.

BRL+ asks, for a decomposable Y with sigma<=s, exact cup alpha and
cap beta>=4,l=s-beta>=1,alpha+beta>=s+3, a supplied valid partition
on[l,alpha-1], and open maximum-cap core(L*,R*), for another valid
partition whose bottom lies wholly<=L* OR wholly>=R*. Only one side
is needed, with no simultaneous top restriction.

It implies the exact root obligation. In the hard root, use BRL+ on B.
The resulting bottom is entirely before A or entirely after A. Mixed
cups in A union bottom(B) then use at most one B endpoint, giving cup
<=l+1; cap<=beta follows by containment in X. Other cells remain valid.

The BRL+ profiles really occur as hard children. Insert an l-cup in ONE
EMPTY gap of Y's cap core as a new lower part. Its strong join is l+beta=s,
mixed cups have length<=l+2<alpha, and maximum beta-caps all surround
the insertion. No old point lies between two inserted points, so a mixed
cap can gain at most one new lower endpoint; the cap number stays beta.
Thus c(X)=alpha,d(X)=beta,sigma(X)<=s. This verifies relevance of the
profile, but does not prove that full-core positioning is necessary:
an actual root only needs choices relative to the sibling's extrema, and
it may admit a partition placing sibling points in several bands.

Full-core BRL+ is diagnostically REFUTED. The independently replayed
24-point child has alpha4,beta5,sigma6,s6,l1,m3 and core(6,15), but
neither bottom<=6 nor bottom>=15 is possible on bands1..3. It is the
prefix-free label instance g657n25d1-32 with originalpoint7 removed.
Guarded job20261003-223307-714ff0 passed10.6s/1613MiB; complete
backtracking finds neither constrained assignment. A lower singleton at
localgap7 nevertheless has a verified ordinary partition with z inband2;
restricting it supplies a valid child partition. Thus the BRL+ premise
is nonvacuous. This result refutes neither BDL nor ordinary MIXED ROOT.
It also does not establish that ALL-A-bottom fails at that particular
gap: a returned band2 solution does not exclude another band1 solution.
The exact witness, hypotheses and source hashes are paper82 and
brl24-backtracking-recheck.txt. No Lean certificate is claimed.
No general global recoloring constructor or regional-context invariant
with a proved closure rule is known for the exact mixed root obligation.

## Direct obstruction to extending an arbitrary supplied child partition

A decisive example is the retained thirteen-point child from
BDL-OBSTRUCTION.md section45, cup4,cap4,strong5,
core(5,7), with valid supplied cells

  {0,6,12} / {2,3,4,5,10,11} / {1,7,8,9}.

Insert a lower singleton at gap6, giving parent index a=6 and shifting
old indices>=6 by one. This is the literal hard root at s5,l1, with
parent cup4,cap4,strong5. No band accepts a with the child assignment
fixed: band1 would contain cup(0,6,13), band2 cap(2,3,5,6), and band3
cap(6,8,9). The point was not precommitted to the bottom; every choice fails.

Nevertheless the parent has the explicit valid partition

  {0,4,5,6} / {8,9,10,11,12,13} / {1,2,3,7}.

It uses the existing left realignment of the child. The parent has fourteen
points and closed cap core(6,6). This is NOT a BDL counterexample. It
shows directly that arbitrary child IH witnesses do not lift, even in the
exact positive-bottom three-band domain.

Independent pure-definition audit163902-f49cdf completed0.016231s/13MiB:
all three blockers, exact chains/core, an explicit strong5, all3003
six-subset nonstrong quads and the displayed repair. Artifact:
exact-frozen-child-root.json. It uses the retained child certificate,
does no new coloring search or SAT solve, and yields no Lean receipt.

The same child partition is isolated under every valid single-point move.
An upward-only simultaneous repair would admit a valid first move (process
changes by descending original band), so it is also excluded. Every distinct
valid repair must contain a directed band-transfer cycle. Neither this
observation nor numerical cardinality slack proves a compatible cycle exists.
That simultaneous choice is the outstanding mathematical step.

Even unrestricted jumps up from the bottom and down into it do not suffice
if higher-band moves are allowed only upward. On the SAME n13 coloring,
valid supplied cells {3,8,9,12}/{0,1,2,4,5}/{6,7,10,11} have the property
that EVERY valid core-sided repair moves old top into the new middle.
This holds even without retaining allowed-side old-bottom points. Short
forced-chain proofs for both sides are in BDL-OBSTRUCTION.md section55;
independent pure certificates171455-14b1ba and171640-4579d2 verify all
input hypotheses, chain facts and explicit both-side ordinary repairs.
Artifact top-middle-required-certificate.json. The proposed BS+MT repair
rule is thereby diagnostically refuted. The exact root obligation remains
open; full-core BRL+ is separately refuted by paper82, while the n13
example itself has both ordinary sided repairs. No compiling theorem
credit is claimed.

The same compatibility issue affects a strong-budget Pascal route. Section62
gives a literal cap4 tight root at s7 with a valid PSL split whose natural
child intervals are3..4 and2..2. NO pair of natural child partitions glues
by the Pascal shift, by a two-case forced5-cup proof. Broader parent-derived
child ranges admit compatible maps and an explicit parent BDL partition.
Diagnostic182312-e38782 checks all256 red-child maps and both repairs;
natural-pascal-trap.json,0.077168s/12MiB. This does not refute PSL/BDL or
close ROOT. A strong-budget BDL induction would need a compatible ambient
statement beyond ordinary natural-child BDL, even with witness selection.

## What the root budget and quotient now explain

Strict strong slack sigma(X)<s closes BDL uniformly on paper. At every
root p+t<=s-1, so a retained cap has p<=s-beta-1 and ordinary absorption
works; the dual is identical, and strict maxima use separate child ranges.
Fixed-s size induction gives the construction without endpoint realignment.
This is section63, not a new compiling theorem or a proof at sigma=s.
Guarded pilot183828-3a6df1 passed; construction audit190244-6260d2
checks all clauses through n6,0.206465975s/8MiB,strict-slack-n6.json.

The root implication graph gives a different structural explanation.
Any transversal of its SCCs is strong: a failed first quadruple equality
forces the first two vertices into one component, and the second forces
the last two. A strong transversal has at most one interior cup and one
interior cap component, so ANY complete coloring has<=4 SCCs/<=4 roots.
All pairs except the global endpoints have an implication arrow one way;
only singleton endpoint components can be incomparable. These are paper
facts from sections64/66. Library regression184930-602e54 passed40
tests2.20s/36MiB,root-quotient-tests-v2.xml; no Lean credit follows.

In a hard retained-cap root, surrounding B extrema join all A internally,
and every B directly reaches A. A is the unique sink SCC; dually the
hard retained-cup sibling is the unique source. A hypothetical smallest
BDL counterexample can therefore have only a2/3-component total chain
and at most one hard root of each orientation. At3 components D/M/E,
the middle retains exact cup alpha/cap beta and the outer contexts are
classic. The known n8 two-hard-root coloring already has this shape AND
valid bands; no counterexample or partition theorem follows.

Sibling extrema add explicit arrows WITHIN each child graph, so restricting
to a global SCC changes its internal decomposition. The constant quotient
therefore loses context; bottom insertion still depends on actual interval
cup ranks of A. This explains why neither a new root nor scalar component
data supplies the missing simultaneous band assignment. There is still
no full ROOT/BRL/BDL proof idea with a proved preserved invariant.
