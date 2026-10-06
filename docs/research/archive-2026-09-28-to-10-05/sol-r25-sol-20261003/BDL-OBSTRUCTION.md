# BDL: exact root reduction and the open positional obligation

Status (2026-10-04 02:34 UTC): exact conditional root reduction written;
**BDL remains unproved and unrefuted, with no new Lean theorem.**

Paper82 diagnostically refutes full-core BRL+ at a pinned24-point child.
The ordinary mixed-root obligation remains open; the checked singleton
parent has a valid globally recolored partition. No all-A-bottom
impossibility is inferred from that returned band2 solution.

The minimal residual for this reduction is ROOT with a genuinely MIXED
maximum cap, or its dual, stated completely in BDL-CORE-REDUCTION.md.
Paper81 closes all no-mixed-maximum roots by lower-child endpoint peeling,
including pure-only strict contraction; conservation is a subcase.
Generic monotone exchange,
frozen extension and capacity-only diagonal normalization have retained
counterexamples; none refutes ordinary BDL. DIAGONAL-PADDING.md transfers
cardinality bounds conditionally, while CORED-PASCAL-DEFICIT.md leaves a
sharp demand>=3 slab deficit open. CORED-PASCAL-SHARPNESS.md explains its
extremal family and classical two-band boundary. These are paper accounts
with diagnostic replays, not compiler receipts. Current handoff is
MATHEMATICAL-HANDOFF.md; sections below retain the full research record.

Research17 identifies a general consequence of the same DS reduction:
with strict strong slack sigma(X)<s, BDL has an explicit recursive proof
without endpoint realignment. The new section63 is a paper consequence,
not a compiling theorem or a solution at the exact budget sigma(X)=s.
No new Lean statement has been registered. Computational checks, when linked below,
are diagnostic and cannot supply the missing induction step.

Current concise account: BDL-CORE-REDUCTION.md states the exact necessary-
and-sufficient unresolved root obligation and distinguishes it from the
stronger sufficient BRL+ realignment route. The chronological sections here
retain every proof route, failure mode and diagnostic evidence. No full BDL
proof or new Lean theorem is claimed.

## 1. Definitions and accepted input

Work with a finite ordered decomposable triple coloring. A cup/cap has all its
consecutive triples cup/cap; the one-change property makes every subchain a chain.
The empty set has chain number zero, a singleton one, and any two points two.
Let `s=k-1`, and assume there is no strong `k`-set. For a nonempty set `Y`, write
`c(Y)` and `d(Y)` for its cup and cap numbers.

For integers `l<=h`, an `s`-band partition on `[l,h]` assigns every point exactly
one index `j` in that interval, with `c(Y_j)<=j+1` and `d(Y_j)<=s-j`.
Empty bands are allowed. BDL asks for such a partition on
`[s-d(X), c(X)-1]` when `c(X)+d(X)>=s+1`.
The equality case has one band, namely all of `X`, and needs no induction.

The input is audited Lemma DS (main checkout:
`runs/claude-audit-667-20261003/AUDITED-PROOF-667.md`, section 6.1).
At a root `X=A<<B`, all mixed triples are cups exactly when their middle
point is in `A`. Every cup meeting `A` consists of a cup of `A`, optionally
extended by one `B` point at each end; caps are dual. In particular, put

`p=c(A), q=d(A), r=c(B), t=d(B), alpha=c(X), beta=d(X)`.

Then `p+t<=s`, `p,r<=alpha`, `q,t<=beta`,
`alpha<=max(r,p+2)`, and `beta<=max(q,t+2)`.
All nonempty children have their chain numbers at most `s`.
We call a child **classic** when its cup and cap numbers sum to at most `s`;
otherwise the BDL induction hypothesis supplies its intrinsic bands.

## 2. Ordinary separated composition

Assume the parent is genuinely multiband: `alpha+beta>=s+2`. Write
`l=s-beta` and `h=alpha-1`.
If `beta>t` and `alpha>p`, the two child partitions can be placed in disjoint
parent bands as follows.

- If `A` is nonclassic, retain its intrinsic bands `[s-q,p-1]`.
  They lie in `[l,h]` and end strictly below `s-t`.
  If `A` is classic, put all of `A` in `j_A=max(p-1,l)`.
  This index satisfies `p-1<=j_A<=s-q`, `j_A<=h`, and `j_A<s-t`.
- If `B` is nonclassic, retain its intrinsic bands `[s-t,r-1]`.
  They lie in `[l,h]` and begin strictly above `p-1`.
  If `B` is classic, put all of `B` in `j_B=min(s-t,h)`.
  This index satisfies `r-1<=j_B<=s-t`, `j_B>=l`, and `j_B>=p`.

If both children are classic, `j_A<j_B`: when `j_A=p-1` use `j_B>=p`;
when `j_A=l`, use both `s-t>l` and `h>=l+1`.
Thus no band contains points of both children. The cup/cap bounds are inherited
without any positional assumption. This covers all classic/nonclassic pairs
under the two strict inequalities.

## 3. Retained cap maximum: non-tight absorption

Suppose `beta=t`. Then `q<=t` and `p+t<=s`, so `A` is classic.
Moreover `alpha>p`, since `alpha=p` would give `alpha+beta<=s`.
Write `j_0=s-t`.

If `p<=j_0-1`, place all of `A` in B's bottom band `j_0`.
If `B` is classic, put all of `B` there as well: `r+t<=s` gives `r<=j_0`.
If `B` is nonclassic, retain its intrinsic BDL partition.
The resulting bottom band has cap number at most `beta=t`, because it is a
subset of `X`. By DS its cup number is at most
`max(c(B_{j_0}),p+2)<=j_0+1`.
All other bands are unchanged. Thus this case closes.

## 4. Tight retained cap maximum: what is forced

The remaining case is

`beta=t` and `p=j_0=s-t` (**R**).

For every `t`-cap `D` in `B`, every point of `A` is strictly between its first
and last points. Indeed, a lower point before or after `D` extends it to a
`(t+1)`-cap by DS, contradicting `d(X)=t`.
Since a root has two nonempty parts, `beta>=2` and `p>=1`.

The simple absorption from section 3 misses its cup limit by one:
`p+2=j_0+2`, whereas band `j_0` permits only `j_0+1`.
This is a genuine positional issue; `p+t<=s` alone does not repair it.

## 5. Endpoint split and R with classic or one-band B

**Endpoint fact.** If `Y` has cap number `b>=2` and cup number `a`, let `F`
be the first points of its `b`-caps. Then
`c(F)<=a-1` and `d(Y\F)<=b-1`.

Proof: every `b`-cap meets `F` at its first point, proving the second bound.
For any `x<y` in `Y` and any `b`-cap starting `y,z,...`, the triple `(x,y,z)`
must be a cup: otherwise adjoining `x` makes a `(b+1)`-cap.
Thus a cup in `F` can be extended at its right end by the second point of a
`b`-cap starting at its last point. A singleton cup extends to two points
as well. Hence every cup of `F` has at most `a-1` points. ∎

In R, let `F` be the first points of the `t`-caps of `A`; if there are no such
caps, set `F=empty`. The endpoint fact gives `c(F)<=p-1`; when `F=empty`
the same inequality holds since `p>=1`. Also `d(A\F)<=t-1`.
If `r+t<=s+1` (B classic or exactly one-band), use

`X_p = F union B`, and `X_{p+1}=A\F`.

Their cup limits are respectively
`max(r,c(F)+2)<=p+1` and `p<=p+2`; their cap limits are respectively
`t` (by containment in X) and `t-1`.
Both indices are in the parent's range: its bottom is `p`, and the
multiband assumption gives `alpha>=p+2`.
All higher parent bands may be empty. Thus this subcase closes rigorously.

## 6. R with a positioned bottom band

**Two-band improvement.** The endpoint fact proves BDL for *every* one-change
coloring with `c(Y)+d(Y)=s+2`, without decomposability: put its first maximum-cap
points F in `j=s-d(Y)=c(Y)-2` and the complement in `j+1`.
The limits are exactly `c(F)<=c(Y)-1` and `d(Y\F)<=d(Y)-1`.
If its maximum caps share a core, F lies on the left of that core; the
last-point mirror gives the right choice. Thus P holds automatically with
two bands. In R, this closes the additional case `r+t=s+2`.
The genuinely unresolved upper child has `r+t>=s+3` (at least three bands).

If B is multiband (`r+t>=s+2`) and has an intrinsic band partition whose
bottom band `B_p` lies entirely before `min(A)` or after `max(A)`, add all
of A to that band. A cup meeting A then has at most one B endpoint, so the
new band has cup number at most `max(c(B_p),p+1)<=p+1`.
Its cap number is at most `t` by containment in X. The other bands stay
unchanged. Thus this positional hypothesis also closes R.

Let `L*=max_D min(D)` and `R*=min_D max(D)`, over all maximum caps of B.
Section 4 gives `L*<min(A)<=max(A)<R*`.
Therefore the coordinator's invariant P, even in its weaker either-side
form, suffices: whenever `L*<R*`, B has a BDL partition with its bottom
band contained in `(-infinity,L*]` or `[R*,infinity)`.

## 7. Dual cases and exhaustiveness

If `alpha=p`, then `r<=p` and B is classic. Apply sections 3–6 after
swapping cups and caps and the root parts: under duality the lower part
is B and the upper part A. Band `j` becomes `s-1-j`; its new cup limit is
the old cap limit `s-j`, and its new cap limit is the old cup limit `j+1`.
Thus the mirrored tight case is `alpha=p` and `t=s-p`, with a positioned
top band of A. No new numerical argument is needed.

For a multiband parent, `beta=t` and `alpha=p` cannot both hold, since
`p+t<=s`. Consequently the strict/retained-cap/retained-cup trichotomy
above is exhaustive.

## 8. Current exact open obligation

Ordinary BDL plus a theorem supplying the either-side core partition in
section 6 for every smaller multiband B closes the root induction.
**That positional theorem is not proved.** Simultaneously asserting P is
not an induction proof: P must also be constructed at every root split,
including those which absorb a classic child into the bottom band.

The next question is whether a context invariant weaker than unrestricted
endpoint choices, but strong enough to supply section 6, is preserved.
No BDL credit is claimed by this reduction alone.

An unrestricted simultaneous cap-core/cup-core invariant is already false:
take the root with lower four-cup on indices `0,1,3,4` and upper singleton `2`.
The whole coloring has cup number 4, cap number 3 and strong number 5.
At `k=6` it has two bands. Every maximum cup spans `(0,4)` and the maximum
caps have common core `(1,3)`. Point 2 lies in both open cores. Requiring the
bottom band to lie on one side of the cap core and the top band on one side
of the cup core leaves that point in neither band, regardless of side choices.
This does not refute P separately; it rules out a tempting simultaneous IH.

Diagnostic construction audit: `mechanism-n6.json`, guarded job
`20261003-105504-05c55d`, passed all 3,428 admitted roots through six points,
including 276 invocations of the child positional hypothesis. The endpoint
fact and four separate endpoint choices also passed. The checker explicitly
does not attempt to infer preservation of P from these SAT witnesses.

## 9. Two false attempts to make the induction local

These refute strengthened induction statements, **not BDL**.

### 9.1 Simultaneous bottom-pair / top-pair control is false (paper)

Let the x-order be `0<1<...<6`, and take the explicit decomposition

`X = ({3} << ({4} << ({2} << ({5} << ({0} << {6}))))) << {1}`.

Its caps among triples are exactly
`(0,1,z)` for `2<=z<=6`, `(0,2,3)`, `(0,2,4)`, `(2,5,6)`,
and the four triples inside `{3,4,5,6}`; every other triple is a cup.
This is mask `1073741696` in lexicographic triple order.
Reading the tree from its innermost pair upward, the cup/cap/strong maxima are
`(2,2,2), (3,2,3), (3,3,3), (3,3,4), (3,4,4), (4,4,4)`.
These follow directly from DS; in the five-point node the unique maximum
cap of its upper four-point child spans the lower singleton and cannot extend.
Its maximum-cap core is `(3,6)` and maximum-cup core `(1,4)`.

At `k=5`, the bands are `0,1,2,3`. Requiring the union of the lowest two to
have cup number at most 2 makes that union a cap. Requiring the union of the
highest two to have cap number at most 2 makes that union a cup.
But **X cannot be partitioned into one cap C and one cup D**:

1. `S={3,4,5,6}` is a cap, so `|D intersect S|<=2` and `|C intersect S|>=2`.
2. For either `x=0` or `x=1`, every triple consisting of x and two points of S
   is a cup. Hence neither 0 nor 1 can be in C; both are in D.
3. Every `(0,1,z)`, `z>=2`, is a cap, so every z>=2 must be in C.
4. Then C contains the cup `(2,3,4)`, a contradiction. ∎

The two pair controls exist separately. Thus separate existential partitions
cannot be combined into this simultaneous IH. Diagnostic independent replay:
`pair-obstruction-independent.json`, job `20261003-111711-59390b`, verifies the
tree and every one of 128 bipartitions. The wider candidate audit
`pair-compatibility-n7.json`, job `20261003-111141-fd7360`, found 76 failures;
its exhaustive n<=6 pass found none in the stated both-core, >=3-band domain.

### 9.2 Even the single cap-core low-pair cup condition is false (diagnostic)

Candidate CH2: for a decomposable Y with nonempty maximum-cap core, BDL can
be arranged so the union of its first two bands has cup number <=j0+2,
where `j0=s-cap(Y)`.

Why it looked useful: in tight R, adjoining A to those two bands produces
a set with cup <=j0+2 and cap <=beta, so the universal two-band endpoint
split constructs the new bottom band. Moreover CH2 would imply P: repartition
the first two bands by their first/last beta-cap points (or leave the bottom
empty if their cap number is smaller than beta). Thus no extra bottom-first
assumption is needed.

But `core-prefix-gate-k7-n27-pilot.json` retains a counterexample at k7 with
cup5,cap5,strong6,capcore `(13,17)`. Its root lower part is the pair at
indices17,18, with cup2, while its upper cap number is4. Thus `beta=t+1`
and `p=j0+1`, exactly the transition where an extra pair of cup endpoints
defeats the proposed bound.

Independent all-triple clauses, exact-one band assignment and Glucose4
reconfirmed the failure and reduced it to a 23-point example at fixed k7:
cup5,cap5,strong6,capcore `(2,14)`. This example has an independently checked
ordinary BDL partition. It is deletion-minimal under the *actual* CH2
hypotheses and fixed k, not a claimed global minimum. Exact labels, surviving
indices and deletion trace: `prefix-obstruction-independent.json`, guarded
job `20261003-111711-a726d5`.

The failed assertion from the first k7 sampling adapter and the failed first
corpus replay are separately retained; neither was a mathematical refutation.
Profiles constrain caps of their declared bound, while candidate hypotheses
must be checked against the actual maximum. Absorbing an external point can
also make a formerly open maximum-cap core collapse to that point.

## 10. Interpretation after these failures

Do not require simultaneous independent endpoint choices or replace adjacent
band counts by chain bounds on their union. The bands may have long mixed
chains across them, and different endpoint choices can require different
partitions. The next abstraction must represent that freedom (for example an
exchange argument or context-dependent band assignments), rather than another
rigid strengthening of P. There is currently no proof of such an exchange
lemma. The exact open BDL root obligation remains section8 / case R with
at least three bands in the upper child, and its dual.

## 11. Exact minimal sufficient lemma after the reduction

The following **Band Realignment Lemma (BRL)** is the remaining sufficient
obligation for this proof route. It is deliberately weaker than asserting P
without a supplied partition, and does not request both endpoint orientations.
It has not been proved or registered in Lean.

Let Y be decomposable with no strong k-set. Set `alpha=c(Y)`, `beta=d(Y)`,
`s=k-1`. Assume:

1. `alpha+beta>=s+3` (at least three intrinsic bands);
2. a valid BDL partition of Y on `[s-beta,alpha-1]` **already exists**;
3. its maximum beta-caps have common open core `(L*,R*)`, `L*<R*`.

Then there exists another valid partition on the same band range whose bottom
band is contained in `(-infinity,L*]` or in `[R*,infinity)`.

**Conditional theorem (paper): BRL for every decomposable Y and k implies BDL.**
Induct on the number of points. The one-band parent closes directly. For a
multiband parent, sections2-7 are exhaustive. In tight R, a classic/one-band
upper child closes by section5, a two-band upper child by section6's endpoint
improvement, and an upper child with at least three bands has its supplied
BDL partition by the size IH. Section4 puts all of A inside its maximum-cap
core, so BRL realigns that supplied partition. Section6 absorbs A into its
bottom band. The dual tight case is identical after duality, which preserves
decomposability and the strong-set condition. Every invoked child is strictly
smaller. Hence the induction is well founded. ∎

The exact obstacle is proving BRL from the supplied partition. A candidate
exchange would remove an interior-core bottom point and replace it with a
first/last point of a newly created overlong cap in the next band. What is
missing is a proof that the resulting cup conflicts can be resolved without
requiring the false joint choices or false low-pair bound above. No such
exchange termination or obstruction theorem has been established.

BRL is a minimal *sufficient* positional obligation for this documented
induction route, not a claim that every proof of BDL must establish it.
The supplied-partition hypothesis and the >=3-band restriction are essential
to keeping the obligation narrower than the original conjecture.

## 12. A fixed child partition cannot simply be extended (paper)

The weaker-looking shortcut E is false: in R, distributing A among all parent
bands need not extend an arbitrary fixed child partition of B.

Take `0<1<...<5`, `A={3}` and

`B = {5} << (({1} << {2}) << ({0} << {4}))`.

The four-point child `C={0,1,2,4}` is a cup. Every B-triple involving 5 is
a cap, so B has cup4,cap3,strong4 and cap core `(2,5)`. Put `X=A<<B`.
Since 3 lies inside every B three-cap, cap(X)=3. Cups meeting A have at most
three points; C remains a four-cup. DS gives strong(X)=max(1,4,1+3)=4.
Thus k5 is admissible, s4, p1, and B has the three bands 1,2,3.

The child partition `B_1={0,4}`, `B_2={1,2}`, `B_3={5}` is valid.
But 3 cannot be put in any band without recoloring B:

- At band1 it makes the cup `(0,3,4)`, exceeding cup2.
- At band2 it makes the cap `(1,2,3)`, exceeding cap2.
- At band3 it makes a two-point chain with 5, exceeding cap1.

A single exchange repairs it: move 4 to band2, whose new cell `{1,2,4}`
is a cup. B's bottom is now `{0}`, before its cap core, and adding 3 to
that bottom makes only a two-point chain. Hence this obstruction supports
the need for a choice or realignment operation, rather than refuting BDL.

Independent evidence: `fixed-extension-independent.json`, job
`20261003-113338-7a1bdb`, recovered the tree and checked all 729 parent
assignments with independent chain DP and the all-quad strong definition;
64 were valid and the minimum number of changed B assignments was one.
The first replay (`20261003-113241-ff67a0`) failed on a syntax error before
execution and produced no evidence; its source remains as v1.

## 13. Even with an open core, the bottom cannot be a cap peel (paper)

This sharpens the coordinator's older unrestricted SB-peel refutation by checking
its missing core hypothesis. Define, in the order `0<...<10`,

`D={2}<<({9}<<{10})`,
`E=((({1}<<{8})<<{4}) << ({0}<<{3}))`,
`A={7}<<(D<<E)`, and `X=A<<({5}<<{6})`.

Direct DS calculations give `(cup,cap,strong)` respectively
`D=(2,3,3)`, `E=(3,3,4)`, `D<<E=(3,4,5)`,
`A=(3,4,5)` and `X=(4,4,5)`. The maximum-cap core of X is `(4,7)`.
Thus k6 is admissible and the three bands are 1,2,3.

For the core calculation, both `I={0,1,2,3,4}` and `J={7,8,9,10}` have
cap number3 by their induced DS splits. Every four-cap in A therefore
meets both I and J. Every mixed four-cap of X uses the upper pair5,6 and
one lower endpoint on each side, so it also starts at or before4 and ends
at or after7. Cap `(4,5,6,7)` attains both boundaries. Hence the core is
exactly `(4,7)`.

**There is no set H of cup number at most 2 that hits all four-caps of X.**
Such H is a cap. Let `I={0,1,2,3,4}` and `J={7,8,9,10}`.
Every `{i,5,6,j}` with `i in I,j in J` is a cap by the root rule.
If H omits both 5 and 6, hitting these caps requires all of I or all of J
to lie in H. This is impossible: I contains the cup `(0,1,3)` and J the
cup `(8,9,10)`.

So H contains 5 or 6. Any two points of I together with that point form a
cup, and the same holds for any two points of J. Consequently H has at
most one point of I and at most one point of J. It must still hit these
six four-caps, which lie entirely in A:

`(0,1,2,7), (0,3,4,7), (1,3,4,9), (1,3,4,10),
(1,4,8,9), (0,3,8,10)`.

The first two require either the I point 0 or the J point 7. If it uses
I point 0, caps `(1,3,4,9)` and `(1,3,4,10)` require both J points 9 and 10, a
contradiction. If it uses J point 7, caps `(1,3,4,9)`, `(1,4,8,9)` and `(0,3,8,10)` have
no common point of I, again a contradiction. ∎

Yet both one-sided BDL partitions exist. A left choice is

`X_1={2,3,4}`, `X_2={0,1,7,8,9,10}`, `X_3={5,6}`,

with respective `(cup,cap)` numbers `(2,3),(3,3),(2,2)`.
A right choice is

`X_1={7,9,10}`, `X_2={2,4,6,8}`, `X_3={0,1,3,5}`,

with numbers `(2,3),(3,3),(4,2)`. The bottom cannot be empty: bands2 and3
have classical capacities `C(4,2)=6` and `C(4,3)=4`, totaling only10.
For example cap `{0,5,6,7}` avoids the left bottom entirely. The bottom's
role is therefore not to hit every maximum cap; such caps can cross higher
bands. This is the precise reason the restricted peeling shortcut fails.

Independent evidence: `old-peel-actual-cores.json`, job
`20261003-114042-ee7521`, and `core-peel-failure-certificate.json`, job
`20261003-114201-0e4ed9`. The latter checks all 205 possible cap candidates
against all 40 maximum caps, both partitions, and the strong5 maximum by
the all-quad definition. The original n14 unrestricted failure has degenerate
core `(5,5)`; the n11 failure above has the actual open core `(4,7)`.

## 14. What the core does and does not mean (paper)

The maximum-cap core controls endpoint visibility. It does not say its interior
has a small cup number. Here is a uniform family, rather than a fitted bound.

Fix beta>=5. Start with Y0 a beta-cap, with outer endpoints fixed. At each step
let Yi=Yi-1<<Bi, where Bi is an upper pair placed inside the original outer
endpoints and around every previous interior point. Such positions exist by
inserting the new pair between the outer endpoints and their nearest interior
neighbors. All parts remain decomposable.

For i>=1, `cap(Yi)=beta`, `cup(Yi)=2i+2`, and
`strong(Yi)=max(beta,2i+2)`. Indeed mixed caps at every new root have at most
four points, so beta-caps are exactly the original beta-cap. A longest cup
of the previous interior extends by both new upper endpoints, and DS bounds
every new cup by that length. For i=1 start from an interior two-point cup;
thereafter every maximum cup is internal, since a cup using an original outer
endpoint cannot gain both new endpoints. DS gives the displayed strong number.

Set s=max(beta,2i+2), k=s+1. The cap core remains the whole open interval between
the original endpoints and contains a `(2i+2)`-cup. Its cup number exceeds the
next-band limit `s-beta+2` by `min(beta,2i+2)-2`, which is unbounded. Nevertheless
an original cap endpoint is an easy peel and P holds for this family. Thus
interior complexity alone neither supplies nor refutes realignment.

## 15. Exchange must permit simultaneous and nonlocal changes

Even a valid one-point-at-a-time exchange is too restrictive (paper). Let
`Y={3}<<(cup{0,1,2})`, in the order0<1<2<3. Then cup3,cap3,strong3,
and the maximum-cap core is `(1,3)`. At k4 the three bands0,1,2 have
cardinal capacities1,2,1. The supplied valid partition

`Y_0={2}`, `Y_1={0,1}`, `Y_2={3}`

puts the bottom point inside the core. No single-point recoloring preserves
validity, because every recipient band is full. Swapping0 and2 repairs it.
Therefore a proof must permit simultaneous exchanges or build a different
partition directly; monotone sequences of single-point valid moves cannot
prove BRL from arbitrary supplied partitions.

Nor can one keep all higher-band points fixed (diagnostic). On the retained
k7,n27 input, both full core-side partitions exist, but an interior-bottom
supplied partition has no left or right realignment while its original
band3/4 points keep their bands. Low-pair points were allowed to escape into
higher bands, so the failure is stronger than a lowest-two-bands-only failure.
Independent deletion reduction retained n18, cup5,cap5,strong6, core `(6,10)`,
with the same failure and full realignment witnesses. Exact supplied assignment,
labels, fixed points and witnesses are in `frozen-realignment-reduced.json`,
job `20261003-115000-04e158` (45 trials,2.903s). This is deletion-minimal at
fixed k with the actual hypotheses and valid supplied bands, not globally minimal.
The full hard-input replay is `brl-hard-input-replay.json`,
job `20261003-114847-38c372` (1.681s).

These results leave BRL itself open. They explain why it needs global choice:
maximum chains can cross bands, cup/cap capacity can block individual moves,
and a repair can require changing points above the lowest pair. No general
coupled exchange invariant or terminating construction is known yet.

## 16. A constructive positional root step: cap gain exactly two (paper)

Suppose `X=A<<B`, no strong k-set, parent has at least three bands,
`alpha+beta>=s+3`, and its maximum-cap core is open. Suppose
`beta=t+2`. Write `l=s-beta`. The node inequality gives `p<=l+2`,
and three parent bands give `alpha>=l+3`, hence `alpha>p`.
Assume only ordinary BDL for the upper child B when it is nonclassic.

Place B in bands at least l+2: retain its intrinsic range
`[s-t,r-1]=[l+2,r-1]` when `r+t>=s+1`; otherwise put all B in l+2.
In the latter case `r<=s-t=l+2`, so cup<=l+3 and cap<=t suffice.
All these bands lie in the parent's range, since `r<=alpha` and
the parent's top is at least l+2.

If `q<beta`, put all A in l+1. It has cup<=p<=l+2 and cap<=beta-1,
exactly the required limits there. The bottom l is empty, so either core
orientation holds automatically.

If `q=beta`, let F be A's first maximum beta-cap points. The endpoint fact
gives cup(F)<=p-1<=l+1, and cap(A\F)<=beta-1. Put F in l and A\F
in l+1. Their other limits follow from cup(A)<=l+2 and cap(X)=beta.
Because A's beta-caps are also parent beta-caps, their first endpoints
are at or before the parent's L*. Thus the bottom F lies left of the
parent core. The last-endpoint mirror gives the right choice.
No band mixes A and B, and no positional child hypothesis is used. ∎

The same endpoint construction works for `beta>=t+2` whenever `p<=l+2`:
B's minimum index is then at least l+2, using its classic free index
`min(s-t,alpha-1)` when necessary. For larger p and strict cup gain
`alpha>p`, DS forces q=beta; a positioned child A then propagates P
through ordinary separated composition. But retainedcup `alpha=p` can
collide with B at A's top band and needs a compatible top choice as well.
Do not treat this as closure of every cap-gain>=2 root.

Diagnostic execution: `positional-steps-n6.json`, guarded job
`20261003-115741-ea8db7`,203 first and203 last constructions through n6,
with independent all-triple cell validation. The finite execution supports
the displayed uniform proof; it does not prove Q or full BDL.

## 17. A remaining compatibility question (unproved)

In a tight retainedcup root used to propagate cap positioning, its lower child
A has `cup(A)=alpha`, `cap(A)=beta` and at least three intrinsic bands.
Tight upper absorption needs A's top one-sided in its maximum-cup core;
cap positioning needs its bottom one-sided in its maximum-cap core.
Thus the actual induction requests simultaneous choices on A.

Candidate Q: for a decomposable set with no strong k-set, at least three
intrinsic bands, and both maximum-chain cores open, there is a valid
BDL partition whose bottom is wholly on one side of the cap core and
whose top is wholly on one side of the cup core. Only one of the four
pairs is required. This is weaker than the false joint adjacent-pair
chain bounds and excludes the known two-band simultaneous-core obstruction
for a structural reason: the retainedcup child in question has >=3 bands.

Q is **not proved**; no simultaneous induction has been supplied. It is
a compatibility question motivated by the remaining root, not a substitute
for BRL or a claim that further narrowing alone is a result. Its first
diagnostic audit passed all552 applicable instances through n6 (allfour
pairs in fact); this tiny positive evidence needs hostile checks before
any proof route relies on it.

## 18. Revised cap-positioning induction map (conditional, paper)

This is an audit of which constructions preserve the cap-positioned bottom;
it is not a complete induction. Assume parent>=3 bands and open cap core.

- Cap gain2 closes by section16 with ordinary BDL for B only.
- Larger gain forces q=beta. If p<=l+2, section16's endpoint construction
  still closes. Otherwise A has at least three bands. For strict cup gain
  alpha>p, a positioned BDL partition of A concatenates with B; their
  intrinsic ranges are disjoint and both classic/free indices stay separated.
  Parent beta-caps are exactly A beta-caps, since mixed caps have at most
  t+2<beta. So its bottom position is preserved unchanged.
- In retainedcup alpha=p, the node inequality and >=3 bands force
  beta>=t+3, q=beta, and B classic. Thus A again has >=3 bands and the
  parent's cap core is exactly A's. Put B into A's top band p-1. If
  t<=s-p-1, its new cap number is at most
  max(cap(A_top),t+2)<=s-p+1, while its cup number is <=p by containment.
  The bottom is unchanged, so ordinary child P suffices here.
- If instead t=s-p, all B points lie in A's maximum-cup core by the dual
  retained-maximum argument. A partition simultaneously positioning its
  bottom relative to its cap core and its top relative to its cup core
  (hypothetical Q) permits the top absorption: mixed caps gain at most one
  A endpoint, so cap<=t+1=s-p+1. The bottom remains unchanged.

The genuinely unresolved cap-positioning transitions are cap gain0,
cap gain1, and this tight retainedcup compatibility request. Q itself has
no preservation proof. This structural map is why Q with >=3 child bands
is a relevant question rather than an arbitrary restriction of a failed
two-band invariant. BRL remains the sufficient open lemma for BDL.

## 19. Cap gain one with an interior lower anchor (conditional, paper)

Suppose beta=t+1, parent>=3 bands, open parent cap core `(L,R)`, and
`M=A intersect (L,R)` is nonempty. Then p<=l+1, l=s-beta.
Every t-cap of B strictly surrounds every x in M: otherwise adding x
produces a maximum beta-cap whose first or last point lies inside `(L,R)`,
contradicting the definition of that core. Thus B's t-cap core `(LB,RB)`
is open and `LB<min(M)<=max(M)<RB`.

Take a B partition whose bottom at l+1 lies on one side of its cap core.
If B is genuinely multiband this is the smaller positional IH (two bands
are already automatic). If B is classic or one-band, r<=l+2: its first
t-cap endpoints in l+1 and the complement in l+2 give such a padded
partition by the endpoint fact. Both indices lie in the parent's range.

For a left choice, let `Al=A intersect (-infinity,L]` and `C=A\Al`.
Put Al in parent bottom l and C together with B's bottom at l+1.
All C lies after B's bottom, since min(C)=min(M)>LB.
Also cap(C)<=t, as C contains no first point of a parent beta-cap;
cap(B_bottom)<=t-1, since it lies before B's open maximum-t-cap core.
Their mixed caps gain only one C endpoint, hence cap<=t. Their mixed
cups gain only one B endpoint, hence cup<=p+1<=l+2. The other cells
are unchanged, and Al has cup<=p<=l+1 and cap<=beta in band l.
Its position is on the required left side. The right choice is mirrored. ∎

Either child orientation yields a parent orientation, so this case uses
only the weak either-side child statement. It does not need both sides.
Diagnostic execution through n6: `positional-anchor-n6.json`,
job `20261003-120557-8c1d03`,17 constructions each side.

If M is empty but A already lies entirely on one side of the parent core,
ordinary separated composition puts all A in l and closes P directly.
The remaining gain-one geometry is therefore **split exterior anchors**:
A meets both sides of the parent core and has no interior point. B's
maximum-t-cap core need not be open in that geometry, so section19's
induction request is genuinely unavailable.

## 20. Retained cap with at most one lower exterior (conditional, paper)

Suppose beta=t, parent>=3 bands and open parent cap core `(L,R)`.
Then p<=l and every A point lies inside B's maximum-beta-cap core.
Furthermore alpha=r: any cup meeting A has at most p+2<=l+2 points,
whereas parent>=3 bands means alpha>=l+3. Thus B has the same intrinsic
range as the parent, including l and l+1.

Assume B has a left-positioned bottom, and A has no points at or after R.
Put `Al=A intersect (-infinity,L]` into B's bottom at l, and put the
remaining `M=A intersect (L,R)` into B's next band l+1.
The bottom gains at most one B cup endpoint, because B's positioned
bottom lies before all A; cup<=p+1<=l+1, and cap<=beta by containment.
Its position stays at or before L, because B's core contains the parent
core and Al is on that side.

In the next band cups are bounded by max(cup(B_next),p+2)<=l+2.
A mixed beta-cap there would have a first or last point in M, impossible
for a parent maximum cap. A beta-cap wholly in M is likewise impossible,
and B_next has cap<=beta-1. Hence its cap limit beta-1 holds. Other
bands are unchanged. The right version mirrors this construction. ∎

If all A lies inside the parent core, either child orientation suffices.
With one nonempty exterior, the construction requires the **matching**
child orientation; the weak either-side BRL does not guarantee that choice.
With two nonempty exteriors it leaves an exterior on the wrong band and
does not close. Preserve these compatibility obligations explicitly.

Search record: `es search 'decomposable uniform upper theorem Band Decomposition Lemma'`
and `es search 'cap first points endpoint split'` returned no matches;
`es search 'cup cap endpoint extension'` found the separately retained
common-endpoint node (`node/ContainsCupSetSuccOrContainsCapSetSuccOfOneChangeCommonEndpoint`,
commit `7806d5c4`). This R25 branch has not imported or changed it.

## 21. Joint positional capacity boundary (paper test)

Classical cup-cap capacity for limits cup<=a,cap<=b is choose(a+b-2,a-1).
Thus ordinary band j has capacity choose(s-1,j). If its bottom is on one
side of an open maximum-beta-cap core, it contains no beta-cap; its capacity
falls to choose(s-2,l). If the top is on one side of the open maximum-alpha-cup
core, it contains no alpha-cup and its capacity falls to choose(s-2,alpha-2).
These are separate cells when there are at least three intrinsic bands.

Consequently Q implies the bound

    |Y| <= sum[j=l..alpha-1] choose(s-1,j)
           - choose(s-2,l-1) - choose(s-2,alpha-1).

The usual conventions handle boundary indices. For alpha=beta=s-1, l=1,
this is2^(s-1)-4 rather than ordinary capacity2^(s-1)-2. So an actual
cup4,cap4,strong<=5, both-open-core n13 coloring refutes Q at k6; at k7
the analogous target is actual cup5,cap5,strong<=6,n29.

The experiment is deliberately at this structural boundary, rather than
collecting another small-case confirmation. Profiles force all declared
maximum caps and cups across either a common cut, or two ordered cuts;
reflection covers the reverse ordering. Decode and check actual maxima before
using this hypothesis. Both n12 pilot profiles yield actual eligible models
and Q witnesses in0.122s, job `20261003-123046-7241ae`. The n13 boundary is
job `20261003-123127-49274c`, pending when this section was written.

Search: `es search 'cup cap cardinality binomial classical bound'` returned
no match. The separately retained R23 classical per-band node remains the
source for eventual Lean reduction; it has not been imported here. This section
is paper reasoning and diagnostic computation, not a new compiled theorem.

At k6,n13 both profiles are UNSAT in0.096s, job `20261003-123127-49274c`.
This gives diagnostic support for the first deficit, not a uniform reason.
The k7,n20 upper-bound-only pilot gave actual cap4 models and was correctly
excluded from Q. Exact existence must use selected-set all-triple witnesses;
the encoder's endpoint chain variables only imply truth from an existing chain
and cannot assert existence. Exact pilot `20261003-123435-c1d817` has actual
cup=cap5,strong6,both open cores and allfour choices. The next test is n28,
the predicted jointcapacity at k7. The cut profiles cover the geometries;
an ordered pair of cuts can also occur when the actual cores overlap.

## 22. Scalar DS-context admissibility is false (paper counterexample)

This refutes the precise Adm_DS conditions of the current shared
`runs/claude-bdl-induct-20261003/t_adm2.py`; it does not refute BDL, BRL,
or the >=3-band Lemma M. Let k=6 and s=5. Let C={1,2,6,7} be a four-cap,
and V=C<<{0}, with upper singleton0 left of C. Then cup(V)=3,cap(V)=4,
strong(V)=4 and its intrinsic range is[1,2]. Set

    Y = {3} << ({5} << ({4} << V)).

The three singleton lower ancestor pieces L={3,4,5} are all tagged band1.
Their union is a three-cap, so its cup2/cap3 fits band1(cup2,cap4).
The parent Y has cup3,cap4,strong5; thus global no-strong6 holds,
D2 cap(V union lower tags)<=s-lo is4<=4, and D3 cup(V union upper tags)
<=hi+1 is3<=3 (there are no upper tags). V is nonclassic with two bands,
so alpha(V)+beta(V)=7=k+1 passes the exact generator's domain filter.

Every x in V on the left (x=0,1,2) forms the cup{x,3,4}; every x on the
right (x=6,7) forms cup{4,5,x}. Thus no Vpoint can enter fixed bottom1.
All V would be in band2, whose cap limit3 excludes C's four-cap. No
completion exists. Yet ordinary BDL is witnessed by bottom{3,5,6,7},
top{0,1,2,4}: their cup/cap numbers are respectively2/4 and3/3. ∎

The explicit prefix-free tree addresses are

    1111,11100,111010,0,110,10,1110110,1110111.

Independent integer-bit input is padded to a common width7. Certificate
`adm-ds-failure-certificate.json` checks all32 free-point assignments and
strong5 directly from all quadruples, plus a separate SAT comparison with
ordinary BDL. Job `20261003-125213-31de43` finishes0.00113s. Earlier jobs
`20261003-124925-ace3fa`, `20261003-125034-520ae0`,
`20261003-125119-8081e4` failed only checker input representations; v1-v3
sources and invalid-string diagnostic are preserved. They supplied no verdict.

The failure explains why scalar admissibility does not survive ancestor
nesting: individually tiny lower pieces, already valid together, block every
free point on both sides. Global cup/cap and strong bounds do not describe
which tagged chain is extended by which free point. Even pointwise, pairwise,
and three-point feasibility hold here, since such a subset can go wholly
into band2. The obstruction is the entire four-cap. A higher-arity chain
extension condition or a genuine positional context must remain available.

`es search 'DS shaped tagged context band completion'` returned no match.
This is a paper refutation with an independent finite certificate, not a
registered or compiled Lean theorem.

## 23. Uniform nested-tag obstruction and unbounded local arity (paper)

For every b>=4 take a b-cap C, two of its points on the left of a gap and
b-2 on the right, and an upper singleton z to the left of all C. Put
V=C<<{z}. Thus cup(V)=3,cap(V)=b,strong(V)=b. In the gap insert lower
singletons a<c<d in sweep order, with ancestor tree

    Y = {a} << ({d} << ({c} << V)).

Set k=b+2,s=b+1 and use span[1,2]. All three tags are fixed at band1.
Their union is a three-cap with cup2; it fits band's cup2/capb budgets.
V's intrinsic range is exactly[1,2], and all three pieces are actual lower
siblings along its root path.

No capb+1 occurs. After adjoining c, maximal b-caps are pure C: a cap
using c has at most b-1 points on the right or3 on the left. After adjoining
d, a cap using d has at most b-1 points on the right or4 on the left.
For b>4, maximal b-caps are still pure C; for b=4, the additional four-caps
start to the left of a and end at d. Hence every maximal b-cap before
adjoining a surrounds a, and adjoining a cannot create a (b+1)-cap.
Caps C attain b, while cups have length at most3 by DS at each singleton
split. DS also gives strong(Y)=b+1 since each cap maximum stays b. Thus
all scalar Adm_DS conditions hold for every b>=4.

Any Vpoint x left of the gap makes cup{x,a,c}; any x right of the gap
makes cup{c,d,x}. No Vpoint can share bottom1 with the tags. All V would
be in band2, which has cap limitb-1, excluding C. No completion exists. ∎

Yet **every subset of at most b-1 free Vpoints** can go wholly into band2:
its cup number is at most3 and cap number at most its cardinalityb-1.
Thus no fixed arity of local feasibility tests suffices to replace chain
compatibility in these physical contexts. This explains the failure rather
than merely raising the size of a negative example.

Representative b5/b6 check: `adm-ds-family-certificate.json`, job
`20261003-125625-bdbf25`,0.00684s, all64/128 assignments, allquadstrong and
ordinary BDL witnesses. The constructor reuses Q9's es_labels(2,b), metrics
and certificates are independent. `es search 'nested lower ancestor tags
bounded local feasibility'` returned no match. No Lean theorem is claimed.
## 24. Global endpoint frontiers do not control their merged ranks

Two deterministic whole-set endpoint constructions were tested to avoid fixed
ancestor commitments. Both fail for a structural reason: valid separate pieces
at the same rank can recreate a longer monochromatic chain when merged.

The first rule splits a nonclassic set into first endpoints F of maximum caps
and its complement, recurses to classical leaves, and assigns each leaf its
lowest feasible band using its actual cup number. It fails on a three-point cup
at k=4: F={0,1} and complement={2} both enter band1, whose cup limit is2.

The corrected rule retains inherited limits (a,b), passes (a-1,b) to F and
(a,b-1) to the complement, and at a+b=s+1 assigns band a-1. Each leaf bound is
valid by the endpoint fact. Nevertheless at X={3}<<cup{0,1,2}, k=4, the only
cup triple is012, all other triples are caps, and cup=cap=strong=3. The maximum
3-caps are013,023,123, hence F={0,1}, complement={2,3}. Both pairs have cup=cap2
and reach inherited limits(2,2), band1. Their union violates both band limits3>2.
Ordinary BDL holds with bands {3}:0, {1,2}:1, {0}:2.

This is a direct paper counterexample to the merge rule, not a BDL refutation.
The guarded diagnostics are jobs20261003-130912-3089c7 and20261003-131008-fb6edf,
artifacts global-peeling-n6.json and global-frontier-n6.json; both stopped on
their mathematically decisive first conflict, not at a time limit. No further
endpoint-frontier variants are commissioned. Counts and closed rank pairs omit
the compatibility of crossing chains; the remaining BRL obligation is unchanged.

## 25. Exact three-tag kernel for a possible three-band repair

This section identifies a question, not a theorem of band deletion. Let V be
decomposable, with cup alpha>=4, cap b>=4, and strong number<=b+1. Suppose a gap
splits its points into V_l,V_r, each with cap number<=b-2. Insert three points
a<c<d in that gap, and form Y={a}<<({d}<<({c}<<V)). Set k=b+2, s=b+1.

The following input analysis is a paper calculation. The inner shell has no
mixed cap longer than b-1: it adds one endpoint c to a cap wholly on one side.
The middle shell has cap number b. Its maximum b-caps are either pure V caps,
or a (b-2)-cap in V_l followed by c,d. Both kinds strictly surround a. Hence
the outer shell retains cap number b. DS bounds every cup meeting a tag by3,
so cup(Y)=alpha. At every shell the joining strong number is1+b=b+1;
therefore strong(Y)=b+1. The three tags themselves form a3-cap, and hence fit
bottom band1 (cup<=2,cap<=b). Scalar D1,D2,D3 are all satisfied.

Every free x in V_l makes a bottom cup (x,a,c); every x in V_r makes a bottom
cup (c,d,x). Thus no free point can enter bottom1 while all tags stay there.
Since each higher cell is wholly in V, completion of these fixed tags is
**equivalent** to V admitting valid bands j=2,...,alpha-1 at the same k.
Call this precise question RF2. It is refuted below. The original two-band
family has alpha3 and no such partition; the extra band does not suffice.

The cap gate cannot be weakened for this tag geometry. A (b-1)-cap in V_l
extends by c and then d to a(b+1)-cap. One in V_r extends by d and then a to
a(b+1)-cap. This explains the two-unit side deficit from the actual chain
extensions. It is not merely an extra numerical filter.

Diagnostics: jobs20261003-131448-b5d2d9 and20261003-131540-aff8aa check all1649
eligible inputs throughn7 (3.191s), all with bottomempty partitions. A larger
exactprofile pilot20261003-131820-5a14fe has actualcup6/cap5,strong6 atn20,k7,
sidecaps<=3, and a raised-floor partition (1.371s total,1.055s solve). The
raised-floor capacity here is sum(j=2..5)choose(5,j)=26. A gate-profile n27
would refute RF2 by count; no such coloring has been established. The n26
saturation probe also found a failure atn26 (18.716s,285MiB); its cup core is
empty, so it does not refute Q. No n27 query is needed or commissioned. Finite
passes do not prove RF2, BRL, or admissibility of general tagged contexts.

### 25.1 Three-band failure with a short paper contradiction

Take the eight-point coloring

V = (({0}<<{1}) << ((({2}<<{7})<<{6})<<{5})) << ({3}<<{4}).

Set P={0,1,2}, M={3,4}, Q={5,6,7}. Both P union{m} and Q union{m} are4-cups
for each m in M. Every triple (p,m,q), p in P,m in M,q in Q, is a cap;
so are (p,3,4) and (3,4,q). The four-set {0,2,5,6} is a cap. Moreover
(0,2,q) is a cap for every q in Q, and (p,5,6) is a cap for every p in P.
These are direct readings of the displayed decomposition.

The node C=(({2}<<{7})<<{6})<<{5} has cup=cap=strong=3. Its lower predecessor
is a3-cap; adjoining5 gives the3-cup {5,6,7}. Joining lowerpair{0,1} to C gives
cup3,cap4,strong5. Finally the upperpair{3,4} has no V points strictly between
its two points, so a mixed cup extends a lower cup by at most one endpoint.
The whole V therefore has cup4,cap4,strong5. Both sides of gap (3,4) are4-cups,
hence have cap number2. At k6 the intrinsic bands are1,2,3.

Suppose bottom1 could be empty. Write H for band3 and D for band2. H is a cup
because its cap limit is2. D contains neither a4-cup nor a4-cap.

1. If H contains both middle points, the triples (p,3,4),(3,4,q) force every
   outer point into D. Then D contains the4-cap {0,2,5,6}.
2. If H contains exactly one middle point m, the other lies in D. To hit the
   two4-cups through that other point, H must contain p in P and q in Q.
   But (p,m,q) is a cap in H.
3. If H contains no middle point, it must still meet P and Q to hit those
   four-cups. It cannot contain all P, since (0,2,q) is a cap for its q;
   nor all Q, since (p,5,6) is a cap for its p. Thus D contains some p,q
   and both middle points. All triples of {p,3,4,q} are caps.

Every case contradicts a band bound. Hence RF2 is false. This is a paper
refutation, independent of the SAT verdict.

Insert a<c<d into gap (3,4) and form the three shells of section25. The resulting
eleven-point Y has cup4,cap4,strong5, the same3-band range[1,3], and all scalar
Adm_DS hypotheses. Its fixed tags exclude every free point from bottom1.
The just-proved contradiction excludes completion in bands2,3. Nevertheless
ordinary BDL holds: in the new order0,...,10, use bottom{4,6,9,10},
middle{3,5,7,8}, top{0,1,2}. Their (cup,cap) numbers are(2,4),(3,3),(3,2).

The independent certificate job20261003-132110-e6062c (0.009505s) reconstructs
the tree, checks all256 free assignments and both strong numbers by the complete
quad definition. It retains both ordinary partitions and every blocking cup in
raised-floor-failure-certificate.json. V and Y have empty cup cores, so Q is
unaffected. The n8 finder stopped on its decisive counterexample; it did not
complete the n8 pass. No further RF2 instances are needed. The minimal supplied-
partition realignment obligation BRL remains unproved and unrefuted.

## 26. Closed form for singleton lower ancestors in one gap (paper)

This interpretation explains depth exhaustion without assuming a band rule.
Let V_l<V_r be the two nonempty sides of an empty gap of a decomposable V.
Insert m singleton lower ancestors in the gap: the outermost has depth1,
the innermost depthm. Let r be their depths listed in x order. Write a=c(V),
b=d(V), d_l=d(V_l), d_r=d(V_r), and let I(r),D(r) be the longest increasing
and decreasing subsequence lengths. Let B(r) be the longest subsequence whose
depths increase and then decrease (a bitonic peak, with either side empty).

The resulting Y has the exact cap number

d(Y) = max(b, d_l+D(r), d_r+I(r), B(r)).

Proof: a cap containing a tag cannot meet both V sides, since (left,tag,right)
is a cup at its lowest ancestor. For two tags x<y, the triple(left,x,y) is a
cap exactly when depth(y)<depth(x); (x,y,right) is a cap exactly when
depth(x)<depth(y). Thus a mixed cap on the left uses a decreasing tag-depth
subsequence, and one on the right uses an increasing subsequence. Each such
subsequence can be joined to an entire maximum cap of its free side, since
triples with one tag and two free points have that tag at an endpoint. Hence
both mixed terms are attained. Among pure tags, a triple is a cap exactly
when its minimum depth is at an endpoint. A sequence has this property for
every triple precisely when it increases and then decreases: a descent followed
by an ascent supplies a valley, and a bitonic peak has no valley. Thus B(r)
is exactly the pure-tag cap number. Pure free caps give b. These exhaust caps. ∎

Every cup meeting a tag has at most3 points by DS. Consequently c(Y)=a whenever
a>=3. If d(Y)=b and m>=1, all intermediate suffixes also have cap number b
(they contain V and are subsets of Y). DS then gives
strong(Y)=max(strong(V),b+1).

Retaining b forces D(r)<=b-d_l and I(r)<=b-d_r. Map each tag position to the
pair of longest increasing/decreasing subsequence lengths ending there. These
pairs are distinct: between positions i<j, either r_i<r_j raises the first
coordinate, or r_i>r_j raises the second. Therefore

m <= (b-d_l)(b-d_r).

This is necessary; the additional pure-tag bound B(r)<=b must still hold.
For two-unit deficits on both sides it limits the context to four singleton
ancestors. In the section25 pattern with three tags a<c<d at depths(1,3,2),
the maximum-cap core is exactly(a,d). A fourth lower singleton e inside it
retains b, but left cap V_l+{a} and right cap {d}+V_r both have length b-1.
Adjoining e creates b-caps ending and starting at e, so the core collapses to e.
Any additional lower root point would extend a maximum cap and increase b.

This is a depth/extension explanation, not a solution of BRL. The scalar cap
budget remains insufficient to color the free points, as section25 proves.
The exact formula was checked on all34 depth permutations through four tags
on V8, job20261003-133004-951e7c (0.038995s), including both fourth-insertion
collapse locations. The checker reuses research.context-extension for the
ordered subsequence arithmetic and independent colors for actual maxima.

The broader audit20261003-133101-9b8202 completed6.157s/81MiB: all154permutations
through five tags on each of V8 and the retained V26 matched the formula. Both
have two-unit side deficits. Four patterns at depth4 retain the cap bound;
none of the120 depth5 patterns do. The fourth-insertion collapse holds in both
specific positions on both bases. These checks validate the stated semantics;
the proof above, rather than their number, supplies the general explanation.

## 27. A repair that closes ordinary bands but loses parent positioning (paper)

Retain the three-tag setup of section25, with r=(1,3,2), two-unit free side
cap deficits, alpha=c(V)>=3, and k=b+2. Suppose V has a BDL partition whose bottom1
lies wholly on the left of the free gap. Keep all its bands, put c,d in bottom1,
and put the outer tag a in band2.

The bottom's new tag depths decrease in position order. A triple involving one
left free point and these two tags is therefore a cap; triples involving two
free points and one tag are caps as well. There is no new bottom3-cup. The
cap bound b follows from the whole-set cap number. Band2 receives only a.
A mixed cap there uses one free side and has length<=b-2+1=b-1, and a mixed
cup has length<=3. Those are exactly band2's limits. All higher bands stay valid.
If the child's bottom is on the right, use a,c in bottom1 and d in band2;
the increasing depth pair has the mirrored property. Thus either child side
constructs ordinary BDL for this whole three-tag context. ∎

This does not establish the parent positional lemma. When both free side caps
have length b-2, the parent core is(a,d); c is in its interior. The displayed
bottom includes c and points outside that core, so it cannot lie wholly on
one side. In the certified V8/V26 the free bottom is essential, and both
constructed orientations indeed fail parent positioning. Ordinary BDL and
preservation of BRL are different obligations.

The chronological root steps explain the lost choice. Inserting inner c keeps
the original free cap core, and c is interior, so section20's next-band operation
preserves either orientation. Inserting d creates the new right core boundaryd;
the simple one-exterior propagation uses the right child choice. Inserting a
then creates the left boundarya and requests the left choice on that preceding
child. The previously chosen right construction does not supply it. One cannot
preserve a single orientation by this schedule without further realignment.

Guarded actual-operation audit20261003-133553-c4f23a completed0.632s on V8/V26,
both child orientations. It keeps their free bands, checks each merged cell by
independent chain DP, and records the failed parent-position flags in
three-tag-repair.json. Child positional partitions were supplied by SAT;
this verifies the operation, not the universal positional hypothesis.

## 28. Core inflation explains the joint capacity deficit (conditional, paper)

The count test in section21 cannot isolate Q's extra compatibility requirement.
Assume X has no strong(s+1)-set, cup alpha, cap beta, at least three intrinsic
bands, and both extreme-chain cores open. Set l=s-beta and t=s-alpha.
For l>=1, take the classical decomposable ES block A with cup<=l,cap<=beta,
and size choose(s-2,l-1). Place it in one empty x-gap inside X's cap core,
lower than all X points. The canonical ES recursion has strong<=s-2 (the
singleton boundary also satisfies strong<=s), and the joining number is
cup(A)+cap(X)<=l+beta=s.

A cap meeting X gains at most one A endpoint: two would require an X point
inside A's empty-gap span. Nor can one A point extend a beta-cap, since all A
points lie strictly inside every such cap. Pure A caps have length<=beta.
Thus cap stays beta. A cup meeting A has length<=l+2<=alpha-1, so every
maximum alpha-cup is still an old X cup; its core is unchanged up to the
order embedding. The whole set still has strong<=s by DS.

For t>=1, insert the classical upper block B with cup<=alpha,cap<=t,
size choose(s-2,alpha-1), in an empty gap inside this unchanged cup core.
The dual one-endpoint argument retains cup alpha, and every cap meeting B
has length<=t+2<=beta-1. Pure B caps have length<=t. The joining number is
alpha+t=s, so strong<=s remains. If l or t is zero, use the empty block and
interpret the corresponding out-of-range binomial term as zero.

This constructs a larger decomposable Y with the same alpha,beta and strong
bound, and

|Y| = |X| + choose(s-2,l-1) + choose(s-2,alpha-1).

Consequently **ordinary BDL for Y**, or Theorem8 at this one parameter state,
implies exactly the joint capacity bound of section21 for X. This is a
conditional argument: no ordinary BDL proof or numerical UNSAT certificate
is supplied by it. In particular a k7,n29,cup=cap5,both-open-core model would
inflate to n31 with the same maxima and strong<=6, exceeding ordinary BDL's
capacity30. It would refute ordinary BDL itself, not merely expose incompatible
Q choices. Counting alone cannot distinguish those two conjectures.

If a Q partition of X is supplied, the construction also extends it: put all
A in bottom l and all B in top alpha-1. Each positioned old extreme cell is
on one side of its new block, so its mixed chain gains at most one endpoint;
the whole block fits the required limits. Other bands stay unchanged. This
operation is not a converse extracting Q from a BDL partition of Y.

Pilot20261003-134408-d2cdca (0.014799s) checks both k6,n12 profile models:
they inflate to n14,cup=cap4,strong5, and supplied Q partitions extend to
cell sizes4,6,4, saturating ordinary capacity. Both cores collapse to their
insertions. The first pilot134338-c7f298 failed on string JSON point keys
before recording a partition; v1 is retained and no theorem credit is given
to that failure. Larger operation audits are recorded separately.

The six-case audit20261003-134514-056c1b completed0.933s. Both k7,n28
models inflate to n30 with cup=cap5,strong6 and band sizes5,10,10,5.
At k8 the same bases inflate to n38 using five-point lower/upper blocks;
cup=cap5,strong7 is retained, and a supplied Q partition extends. These are
checks of the operation and hypotheses, not proofs of Q or the capacity bound.

## 29. What a cardinality-maximal BDL counterexample would look like (paper)

Fix s,alpha,beta with alpha+beta>=s+3, and suppose a BDL counterexample with
these exact chain numbers and strong<=s exists. Choose one with maximum
cardinality. Such a choice is possible: the ordinary cup/cap theorem bounds
the size by choose(alpha+beta-2,alpha-1), without using BDL or Theorem8.

If beta<s, its maximum-cap core cannot be open. Indeed insert a single lower
point in an empty gap inside that core. Section28's first argument retains
cap beta, and its joining strong number is 1+beta<=s. Here
alpha>=s-beta+3>=4, so every new cup has length<=3<alpha: cup alpha is
retained as well. The larger set would still be a BDL counterexample, since
any band partition of it restricts to a band partition of the original set.
This contradicts cardinality maximality. Dually, if alpha<s, its maximum-cup
core cannot be open. ∎

Thus when both inequalities are strict, an extremal counterexample has both
cores closed. This reduction is unconditional under counterexample existence.
It gives neither a saturation embedding theorem nor a proof of BDL: a parent
can have a closed core while its upper child has an open one, precisely the
geometry a retained-maximum absorption can create. The endpoint-set shortcut
EP+ was reconsidered but immediately rejected by section13: all first endpoints
hit every maximum four-cap, so their cup number is at least3 at strong5,cap4,
exceeding the proposed bound strong-cap+1=2. No new enumeration was needed.

## 30. Weighted closed form for ordered lower ancestor blocks (paper)

Generalize section26's singleton tags to nonempty decomposable blocks Ai.
All blocks are noninterleaved x-intervals within the same empty gap of V,
and all are LOWER siblings on the path to V. Their distinct depths ri,
listed in x order, are a permutation of1,...,m. Let

pi=c(Ai), qi=d(Ai), alpha=c(V), beta=d(V),
d_l=d(V_l), d_r=d(V_r),

where both free sides V_l,V_r are nonempty. For a bitonic-peak subsequence
S of the depth permutation, let i* be its unique deepest selected block and
give it weight qi*. Define

W(r,q) = max_S (|S|-1+qi*), with W(empty)=0.

Then the complete set Y satisfies the exact formulas

d(Y)=max(beta, d_l+D(r), d_r+I(r), W(r,q)),
c(Y)=max(alpha, max_i(pi+2)).

For the cap formula, a cap meeting V and any block cannot meet both free
sides: a free-left/block/free-right triple is a cup. Nor can that cap use
two points of any block: with one free point, those two lower block points
make a cup at their root. The mixed cap terms are therefore exactly those
in section26, with only one point per selected block, independent of qi.

A pure context cap uses a bitonic-peak depth subsequence, by the same
three-block test. Every block except its deepest selected one contributes
at most one point: two points of that shallower block and a deeper point
make a cup. Its deepest block can contribute any internal qi*-cap. Conversely
such an internal cap, one point from each other selected block, and a bitonic
peak order form a cap: triples from three blocks have their shallowest depth
at an endpoint; triples with two deepest-block points have their lower
ancestor at an endpoint. Thus W is both necessary and attained.

For cups, repeatedly apply DS down the ancestor path for the upper bound:
c(Y)<=max(alpha,max_i(pi+2)). Each pi-cup is extended by one V point on
each side of the empty gap, so every pi+2 term is attained. ∎

Let beta_i be the first displayed cap formula restricted to blocks with
depth>ri; it is the exact cap number of Ai's upper descendant. DS also gives

strong(Y)=max(strong(V), max_i strong(Ai), max_i(pi+beta_i)).

If the whole cap number remains beta, every beta_i is beta, since each
descendant contains V and is a subset of Y. Thus in that retained-cap case
the joining penalty is exactly beta+max_i pi. The old depth bound
m<=(beta-d_l)(beta-d_r) still follows, but the additional weighted-peak
condition W(r,q)<=beta matters for nonsingleton blocks.

These are exact profiles for this one-gap, ordered-block context; they do
not assert that any scalar-admissible fixed band assignment can be completed.
The independent six-permutation operation audit20261003-140344-57b55a
completed0.095829s/12MiB. Actual n15 colorings use blocks with profiles
(1,1),(2,3),(3,2); the cap number varies4/5 with depth order, and every
cup/cap/strong formula agrees. The source reuses the retained ordered-extension
primitive for LIS/LDS and computes weighted peaks explicitly. The durable
block-depth-formula.json also contains the following family certificate.

## 31. Fixed-bottom failure for every bottom index (paper)

The obstruction is not tied to singleton siblings or bottom index1.
Choose p>=1,b>=6,s=p+b. Let C be a b-cap and D a p-cup. Put V=D<<C,
in x order C's first three points, all of D, then C's remaining b-3 points.
It has cup p+2,cap b,strong s, hence exactly two intrinsic bands p,p+1.

Choose the free empty gap after D's first point if p>=2, and immediately
before D if p=1. Its left/right free cap numbers are at most b-2: a cap
meeting D has at most one D endpoint, so the left bound is at most4 and
the right bound at most b-2. For p=1 the left bound is3. Now insert three
p-cup blocks Pa<Pc<Pd in this gap, with depths(1,3,2), so the nested path is

Y=Pa << (Pd << (Pc << V)).

Section30 gives cap(Y)=b, cup(Y)=p+2 and strong(Y)=s. The pure context cap
has length at most4 and both mixed depth extensions have length2. The
context cup number is p+1: Pa and Pd can gain only one context endpoint,
while Pc has no context endpoint higher than itself. Thus assigning every
context point bottom band p meets that band's cup p+1 and cap b limits.
The free V also respects the global cup/cap/strong limits. These are exactly
the scalar hypotheses at issue in the physical context proposal.

Nevertheless no completion respecting these fixed tags exists. Every free
point left of the gap joins the entire p-cup Pa and one Pc point in a
(p+2)-cup; every free point right of it joins the p-cup Pd and one Pc point
in a (p+2)-cup. Hence no free point can be in bottom p. They would all have
to lie in band p+1, which permits cap b-1, whereas V contains C, a b-cap.
Every subset of at most b-1 free points does fit wholly in that next band:
its cup number is at most p+2 and its cap number at most its cardinality.
Therefore bounded-arity completion tests cannot detect the obstruction
uniformly as b grows. ∎

This refutes a fixed-bottom scalar-context invariant at arbitrary p. It
does not refute ordinary BDL, BRL or Q. These sets have exactly two bands,
so ordinary BDL and separate positioning follow from section6. The n8
example in section25 is still needed for the >=3-band restriction.
The independent p2,b6 certificate in job140344-57b55a has n14,cup4,cap6,
strong8; the complete quadruple check agrees with DS. The tag union has
cup3,cap4, valid in bottom2. All256 free assignments in bands2,3 have an
explicit forbidden chain. Ordinary BDL is checked separately: bottom
{0,4,5} has profile(3,2), its complement(4,5). The artifact retains all
blocking cups, every assignment witness, labels and the ordinary partition.

## 32. A common window of classical staircase labels fails (paper)

This tests a global label abstraction rather than another tree-side commitment.
For each point v, take the downset generated by incoming pairs' (cap,cup) ranks,
where each rank is one less than its maximum monochromatic chain length.
In the (beta-1)x(alpha-1) rectangle, encode its staircase boundary by U steps
down the cup coordinate and D steps along the cap coordinate. Every word has
alpha-1 U letters and beta-1 D letters. Any length s-1 window therefore has
its U count in [s-beta,alpha-1], precisely the intrinsic band range.

It is false that some common window offset gives a valid BDL band assignment.
Take x order0<...<5 and decomposition

X={5} << (((({1}<<{2})<<{4})<<{3})<<{0}).

The exact cup,cap,strong numbers are4,4,4. At k5,s4 the boundary words are

v0 UUUDDD; v1 UUDUDD; v2 UDUUDD;
v3 DUUUDD; v4 DUDUUD; v5 UUDDDU.

There are four length3 offsets. Each fails:

- Offset0 places cap(1,2,5) in band2, whose cap limit is2.
- Offset1 places cup(0,1,2,4) in band2, whose cup limit is3.
- Offset2 places cap(2,3,4) in band2, whose cap limit is2.
- Offset3 places cup(1,2,3) in band1, whose cup limit is2.

Ordinary BDL is still valid: band1{4,5},band2{1,2,3},band3{0}, with
profiles(2,2),(3,2),(1,1). Thus even whole-set classical rank words do not
admit this single global diagonal/window compression. ∎

Finder20261003-141242-4edb49 completed0.017065s/12MiB: all applicable states
through n5 passed, but the n6 scan stopped at this decisive mask3255 failure.
Independent20261003-141339-9272b3 completed0.000763s. It enumerates all
monochromatic subsets ending in each pair instead of using the rank recurrence,
reconstructs the displayed tree, checks all four chain conflicts, and checks
strong by all quadruples. Its artifact is common-window-failure-certificate.json.

Classical raw downsets remain an injective label, as in Moshkovitz-Shapira's
proof [arXiv:1206.4001](https://arxiv.org/pdf/1206.4001), section2.1.
The earlier checked September singleton-root collision already showed that
these labels are not a complete compositional state. Section32 separately
rules out a particular global compression even when the whole set is known.
It neither refutes BDL/BRL nor rules out a higher-order matching of labels.

## 33. The sufficient realignment obligation needs positive bottom only (paper)

The conditional proof in section11 never invokes BRL with bottom index0.
At its actual retained-cap root, the lower child is nonempty and has
cup p=s-beta>=1. Therefore it suffices to assume the following narrower BRL+:

Given s, a decomposable Y with strong<=s, exact cup alpha,cap beta,
1<=s-beta, alpha+beta>=s+3, an open maximum-cap core(L*,R*), and a supplied
valid BDL partition on[s-beta,alpha-1], there exists a valid partition in
that same range whose bottom is wholly<=L* or wholly>=R*.

BRL+ still implies full BDL. Repeat section11's size induction: equality,
ordinary separated splits and non-tight absorption close directly; tight
retained-cap splits with upper child of at most two bands close by the
endpoint fact. For every remaining retained-cap split, p=s-beta>=1 and the
upper child has at least three bands and the required open cap core.
Its partition is supplied by the size IH, so BRL+ applies. The tight
retained-cup case is the dual, whose lower bound is the cup number of its
nonempty lower child in the dual tree, again positive. ∎

This removes an unused boundary case from the sufficient conjecture, not
an open step from its proof. No BRL+ exchange or positional induction is
established. The exact profile hypothesis is not artificial: for any Y in
BRL+, insert a p-cup in one empty gap of its cap core, where p=s-beta.
Its upper child is Y. Because insertion is in ONE EMPTY gap, no Y point
lies between two inserted points, so a mixed cap gains at most one lower
endpoint. Every beta-cap of Y surrounds the gap; each Y side has cap at
most beta-1, and the mixed caps therefore retain beta. Mixed cups have
length<=p+2<alpha, and the joining strong number is p+beta=s. Thus every
such Y can actually occur as the difficult child of an admissible
retained-cap root. Inserting in several gaps would not justify this
one-endpoint argument.

## 34. Flexible window matching: conditional count route, now refuted

Section35 refutes this candidate. Its proposed implication is retained to
identify exactly which global compression failed.

Let wx be the classical boundary word of point x from section32. Instead of
one common offset, let W_s(x) contain all length(s-1) contiguous substrings
of wx. Every member has U count between s-beta and alpha-1.

The candidate WM asks for distinct representatives vx in W_s(x). It is
equivalent, by finite Hall matching, to the explicit inequality

|union_{x in S} W_s(x)| >= |S| for every subset S of X.

If WM holds for strong-free decomposable X, the injection x->vx gives

|X| <= sum_{j=s-beta}^{alpha-1} choose(s-1,j),

which is the exact Theorem8 window count. Classic and one/two-band states
already have the ordinary cup/cap binomial bound; the nontrivial new class
is alpha+beta>=s+3. Thus a Hall expansion proof on the whole-set classical
word family would give the general count without proving BDL.

WM does **not** automatically give band chain bounds by assigning j=#U(vx).
The section32 six-point example admits the distinct representatives

v0 UUU, v1 UDU, v2 DUU, v3 UDD, v4 DUD, v5 UUD.

All occur in their point's boundary word, but cap(1,2,5) receives band2,
whose cap limit is2. Counting injection and a band partition are distinct
obligations. The Hall inequality is now refuted, rather than merely unproved.

Diagnostic evidence: n6 pilot20261003-141559-bbd7b4 completed0.093288s/14MiB;
all700 applicable states pass. Exact n7 job20261003-142026-034cda completed
2.687998s, all11900 applicable states through n7 pass. Previously certified
near-capacity witnesses also pass: both k6 n12 and both k7 n28 joint-profile
models and RF2 k7 n26, job20261003-141749-cf69f3,0.091243s/15MiB.
Their actual words and matching representatives are retained. The exact n8
mechanism challenge20261003-142217-7cc776 supplied the refutation below.

The classical rank injection supplies distinct full words, not Hall expansion
of their short-window families. Moreover restricting X to a child changes the
incoming ranks and windows, so no compositional Hall invariant follows from
the child rank state (already refuted by the September collision). The current
question is a whole-family expansion theorem using DS and its strong bound;
more unconstrained count confirmations would not supply that theorem.

## 35. Flexible matching fails at an exactly saturated eight-point set

The eight-point coloring with mask35984842346988246 (lexicographic triples)
is decomposable and has cup=cap=strong4. Thus k5,s4 are admissible, and the
ordinary capacity is1+3+3+1=8. Its classical boundary words, in point order, are

UUUDDD, UUDUDD, UUDDUD, UDUUDD,
UDUDUD, UDDUDU, DUDUUD, DDUUDU.

Every length3 window on points1,...,7 belongs to the six-element family

{DDU,DUD,DUU,UDD,UDU,UUD}.

Therefore seven points have only six possible representatives: Hall fails.
Only point0 has either constant window UUU or DDD. The empty incoming ideal
at that first point thus monopolizes both extreme labels, although the whole
set attains the proposed exact size bound. This is why flexibility among
different contiguous offsets does not fix the classical-word compression.

Ordinary BDL still holds, with band0{6},band1{2,4,5},band2{0,1,3},band3{7}.
The issue is the available classical windows, not the size bound or BDL. No
cyclic-window, two-sweep or positive-bottom fitted repair is pursued after
these two classical-compression failures.

Finder20261003-142217-7cc776 completed49.142934s/32MiB, stopping on this
decisive failure: full coverage through n7, a partial n8 prefix only. It
records a size7 maximum matching and the exact Hall subset. Independent
direct-chain/quad/tree replay20261003-142541-d10a75 completed0.006795s/10MiB.
It reconstructs the tree, checks ranks by all monochromatic subsets rather
than the finder's DP, checks every strong quadruple, verifies the seven-point/
six-window Hall witness and certifies the displayed ordinary partition.
Evidence: window-matching-failure-certificate.json. No new Lean theorem or
compiled receipt.

## 36. Strong=cap does not give a common maximum-cap vertex (paper)

A zero-bottom cap-peel shortcut also fails for a uniform structural reason.
For beta>=4 take a beta-cap A with at least two points on each side of a
contiguous upper (beta-2)-cap B, and let X=A<<B. DS gives cap(X)=beta and
strong(X)=beta: the joining number is2+(beta-2)=beta. A cup meets A in at
most two points, and there are no A points inside B's span, so such a cup
can gain only one B endpoint. A pair of A points on one side does attain3.
Thus cup(X)=3, and at s=beta there are exactly three intrinsic bands0,1,2.

Maximum caps include all of A, and also every set {a_left} union B union
{a_right}. Their total vertex intersection is empty: the pure A cap excludes
all B points, and at least two choices on each A side exclude any individual
A point from a mixed maximum cap. Their endpoint core is nevertheless open,
between the last left A point and the first right A point.

Consequently even strong=cap does not guarantee a singleton transversal of
maximum caps. Zero-bottom BDL cannot generally be a cap peel. Ordinary BDL
here follows directly from the endpoint split of A into bands0,1 and putting
the classic B in band2. This needs no new case computation. ∎

## 37. Exact first-point-conditioned pair-rank transition (paper)

This records the correlation the ordinary incoming pair ranks omit. It is
an explanatory state formula, not a new k-only counting conjecture.

For color e, let rho_S^e(z;u,v) be one less than the longest e-chain in S
ending with the ordered pair u<v and starting strictly after z. Set it to0
when no such pair-chain exists. Let E_S^e(z;u) be the maximum length of an
e-chain ending at u and starting after z (again0 if absent).
Use c/d for cup/cap. Put X=A<<B, and first take z before all X points.
Write a0=min(A),b0=min(B). For a valid pair in X:

- Both endpoints in A:
  rho_X^d=rho_A^d(z;u,v),
  rho_X^c=max(rho_A^c(z;u,v),rho_A^c(b0;u,v)+1).
- Both endpoints in B:
  rho_X^c=rho_B^c(z;u,v),
  rho_X^d=max(rho_B^d(z;u,v),rho_B^d(a0;u,v)+1).
- u in A,v in B:
  rho_X^d=1,
  rho_X^c=max(E_A^c(z;u),E_A^c(b0;u)+1).
- u in B,v in A:
  rho_X^c=1,
  rho_X^d=max(E_B^d(z;u),E_B^d(a0;u)+1).

The extra+1 when the restricted profile is0 is harmless, since the own
pair rank or endpoint-chain length is already at least1.

Proof: a cup ending at an A-A pair can have at most one B endpoint, on
the left. It exists exactly when its first A point is after b0. A cap at
an A-A ending pair cannot meet B: DS allows only one A right endpoint,
so its last two points would not both lie in A. This proves the first
line, and the second is dual. For u in A,v in B, a cup consists of an
A-cup ending at u, the right endpoint v, and optionally the left endpoint
b0. Its pair rank is the stated endpoint length, increased by1 exactly
under that first-point condition. A mixed cap ending at this A-B pair
has only two points, since its lower point u would have to be its first
point, so no B-core point can precede it in the chain. The fourth line
is dual. Every displayed term is attained by these endpoint extensions. ∎

For any cut z, apply the same formula to A_z=A intersect(z,infinity) and
B_z=B intersect(z,infinity), using their restricted minima. If one part
is empty, the parent is simply the other restricted child. Consequently
all first-point-conditioned pair ranks compose exactly from the two child
tables for all cuts; endpoint profiles follow by maximizing pair ranks
plus1, with the singleton case included. With the child strong numbers
added, DS also supplies the parent strong number. This is a closed state,
but its table length depends on n, and no k-only state count follows.

In the existing compiled September matrix-collision witnesses, the ordinary
child cap rank at pair(5,8) is the same. The child cap rank requiring its
first point after q=1 distinguishes the two models:3/2, and the extra
left endpoint q gives the different parent ranks4/3. All240 cut/pair/color
entries on each of those two already-certified examples were independently
audited by20261003-143035-b92ab3, completed0.010131s/10MiB.
Evidence: tail-pair-root-audit.json. The formula explains why
unconditioned matrix equality is insufficient without reopening the
refuted classical-window compression route.

## 38. First maximum-cap endpoints need not reduce strong number (paper)

For p>=3, put a lower p-cup P entirely before an upper three-cup C, and
let A=P<<C. Insert an upper singleton z between the second and third points
of C, forming X=A<<{z}. Finally append a lower singleton w to the right of
everything, forming Y={w}<<X. DS gives

                 cup   cap   strong
  A              p+1    3     p+2
  X              p+2    3     p+2
  Y              p+2    4     p+2.

For A, cups can use P and one right C endpoint, while caps can use a C pair
and one left P endpoint. The p+2 cup in X is P followed by the first C point
and z. All X three-caps extend by w, giving Y's four-caps. The remaining
claims follow from the DS upper bounds and the displayed joining numbers.

All maximum Y caps end at w. Their first-point set is exactly
F=P union {the first two C points}: the pure-A three-caps supply every P
point, and caps (C_i,z,C_last,w) supply the first two C points. No other
point can start a three-cap in X. Thus F is a p-cup below an upper pair,
so strong(F)=p+2=strong(Y). Its cup number is p+1 and cap number3.

The cap core of Y is open, from the second C point to w. At s=p+2 its
bottom index is p-2>=1 and it has four intrinsic bands. Therefore even
positive bottom and an open core do not make strong decrease on F.
This rules out a recursive strong-(s-1) first-endpoint peel, uniformly in
the bottom index. The endpoint fact c(F)<=alpha-1 still holds; that single
chain reduction supplies no corresponding strong reduction. ∎

The p3,n8 instance, and section36's beta4,n6 Helly failure, were audited by
20261003-143726-1d9578,0.004460s/10MiB. The checker reconstructs explicit
distinct-leaf trees and checks all chains and strong quadruples. Evidence:
endpoint-paper-facts.json. These are paper mechanism checks, not new Lean
theorems or progress on isolated numerical cases.

## 39. All decomposition roots from a width-two implication order (paper)

For each cup triple a<b<c put arrows a->b,c->b; for a cap triple put
arrows b->a,b->c. A nonempty proper subset A is a valid lower root part
if and only if it is successor-closed in this graph.

For a cup, successor closure says that if either endpoint is lower then
the middle is lower, exactly the DS mixed-triple condition. For a cap it
says that if the middle is lower then both endpoints are lower, again
exactly that condition. Monochromatic child triples impose no additional
root condition. On a hereditary decomposable set every such root has
decomposable children. This establishes the biconditional, not just one
direction.

The SCC condensation has width at most two for **every** complete triple
coloring: if three components were pairwise incomparable, choose one point
from each. Their triple supplies an arrow between two distinct chosen
components, contradicting incomparability. Any successor-closed component
set is generated by its minimal components, at most two. Hence all roots
are unions of one or two principal reachability sets. Bitset closure costs
polynomial time and produces O(n^2) root candidates instead of 2^n cuts. ∎

This interpretation does not eliminate the positional obligation. A tight
retained-cap root with points of B on both sides of all A makes all A
vertices mutually reachable (the surrounding cup triples give both
directions), and every B vertex reaches A. Therefore A is a single terminal
component. A different root may enlarge A, but cannot split it or put it
in the upper part.

An explicit n8 example has just two roots and both are hard. Start with
S={5} << (cup{0,1,3,4} << {2}). Insert a lower singleton L and then an upper
singleton H in the empty common-core gap (1,2) of S. The final x-order is
S0,S1,L,H,S2,S3,S4,S5. Its lexicographic coloring mask is8936839165773790,
cup=cap4,strong5,k6, and its component chain is

  {3}=H  ->  {0,1,4,5,6,7}=S  ->  {2}=L.

The only roots are A=L,B=S union H (tight retained-cap case), and
A=S union L,B=H (tight retained-cup case). Both large children have
cup=cap4 and three bands1,2,3. Thus changing the root alone cannot always
avoid the missing one-sided partition. Ordinary BDL exists with
band1{7},band2{2,4,5,6},band3{0,1,3}.

Diagnostic audit20261003-144249-133f80 completed0.002053s/11MiB, compares all
254 direct DS cuts with closure and verifies every strong quadruple and the
ordinary partition. Evidence: root-choice-audit.json. The pure root algorithm
is separately checked on **all arbitrary** complete colorings through n5
(1,1,2,16,1024 colorings), job20261003-144848-d62ee3,0.044589s/6MiB,
root-graph-primitive-fixtures.json. Neither receipt is a Lean theorem.

## 40. A source component may itself retain the maximum cap (paper)

A proposed further root normal form required every source component to have
cap less than beta (dually every terminal component to have cup less than
alpha). This would have made a switch between tight cap/cup roots easier.
It is false, so no source-deficit enumeration or fitted repair is pursued.

For every beta>=4 take a beta-cap D and an upper pair E strictly surrounding
all D, with S=D<<E. Insert a lower singleton x after the first two D points,
forming X={x}<<S. DS gives c(S)=4,d(S)=strong(S)=beta and

  c(X)=4, d(X)=beta, strong(X)=beta+1.

Pure D attains beta. A cap in S meeting D has its E core and at most one D
endpoint each side; E lies outside all D, so such caps have at most two
points. Caps meeting x are x plus a cap on just one S side, at most
max(3,beta-1)<beta. Hence the maximum caps of X are exactly D, and its
cap core is open. At s=beta+1 it has the three bands1,2,3.

All D vertices belong to one SCC: cup(E_left,D_i,D_j) gives D_j->D_i,
and cup(D_i,D_j,E_right) gives D_i->D_j. Both E vertices reach D. The cap
triples(E_left,D_first,x) and(x,D_last,E_right) give return arrows from D
to the two E vertices. Thus all of S is one source component, of cap beta.
The singleton x is a terminal component, with no outgoing nontrivial arrow.
The unique valid root has lower part {x}. Its upper child S retains beta
and has three intrinsic bands, so it is precisely the difficult R geometry.

This is no BDL counterexample. Explicitly put E_left,D_first,x in band1,
the remaining D points and E_right in band2, and leave band3 empty. The
first band is a three-cap; the second has cup3 and cap beta-1. Their limits
are(2,beta) and(3,beta-1), respectively. ∎

Independent beta4,n7 replay20261003-145623-f3fc50 completed0.000484s/10MiB,
checking all126 root cuts, every strong quadruple and the displayed partition.
Evidence: one-sided-root-obstruction.json. The first replay145555-208afa
failed before producing a result because E's two leaf addresses coincided;
its source is preserved as v1, and the corrected distinct-leaf replay has
the same triple coloring. After NC and SourceDef failures, stop root-choice
normal-form variants. Root enumeration is reusable; no general BDL or BRL+
proof has been obtained.

## 41. Open three-cap cores have a uniform linear bound and positioned bands (paper)

**Linear bound.** If X is decomposable, d(X)=3, strong(X)<=s, and its maximum
three-caps have common open core(L*,R*), then |X|<=2s-2. Necessarily s>=3.

Let F be the first points of maximum three-caps and G=X\F. The endpoint fact
gives c(F)<=c(X)-1 and d(G)<=2. Also d(F)<=2: a three-cap contained in F
would end at or before max(F)=L*, contradicting the common last endpoint
bound R*>L*. Consequently F and G are cups, and

  |F|<=c(X)-1<=s-1,  |G|<=c(X)<=s.

We show the sum improves by one using any root X=A<<B. Put p=c(A),q=d(A),
r=c(B),t=d(B). A pure three-cap of A is a maximum parent cap, so if q=3
the cap core of A is also open. Applying the preceding elementary endpoint
argument to A gives |A|<=2p-1. If q<=2, A itself is a cup and |A|=p.
There are three possibilities for t:

1. **t=1.** B is a singleton, and p+1<=s. If q=3, then
   |X|<=2p-1+1<=2s-2. Otherwise |X|=p+1<=s<=2s-2.

2. **t=2.** B is a cup, |B|=r<=s, and p+2<=s. If q<=2, immediately
   |X|=p+r<=2s-2. Suppose q=3. We claim r<=3. If r>=4, no A point can
   have two B points on both sides: their two three-caps would end and start
   at that A point, making the parent core closed. Thus every A point is
   before the second B point or after the penultimate B point. A cannot meet
   both zones, since the at least two intervening B points with those two A
   endpoints make a four-cap. If all A is in the left zone, every A point
   starts a three-cap, so L*>=max(A); a pure A three-cap ends<=max(A), giving
   R*<=max(A), contradiction. The right zone is the x-order mirror. Hence
   r<=3, and |X|<=2p-1+3<=2s-2.

3. **t=3.** Retention of the cap maximum forces every maximum B cap to
   strictly surround ALL A; also p+3<=s. If A meets G, its cup G has length
   at most p+2<=s-1 by DS, while |F|<=s-1, proving the claim. If A is wholly
   in F, the cup F consists of ALL A and at most one B endpoint on either
   side. It has no B endpoint z to the right of max(A): as z belongs to F,
   a maximum parent cap starts at z. Everything in that cap is after ALL A,
   so it is a pure maximum B cap, contradicting strict surrounding. Thus
   |F|<=p+1<=s-2, while |G|<=s, again giving |X|<=2s-2.

These possibilities exhaust t>=1, since t<=d(X)=3. The proof uses no BDL,
Theorem8, cardinality saturation theorem, or induction hypothesis. ∎

**Positioned three bands.** In the BDL domain with beta=3 and at least three
intrinsic bands, alpha+3>=s+3 and alpha<=s force alpha=s. The natural range
is exactly[s-3,s-1]. The preceding bound constructs both positional choices:

- If |F|=s-1, put one F point in top s-1, F's remainder in bottom s-3,
  and all G in middle s-2. The bound forces |G|<=s-1.
- Otherwise |F|<=s-2. Put F in bottom; if |G|=s, put one G point in top,
  and put the remaining G in middle. If |G|<=s-1, leave top empty.

Bottom and middle are cups of sizes at most s-2 and s-1, respectively,
so their bounds are(s-2,3) and(s-1,2). Top is at most a singleton, with
cap1. Bottom is a subset of F, hence wholly<=L*. Using last maximum-cap
points and their cup complement gives wholly>=R* by the same argument.
No supplied partition is needed. Thus BRL+ holds for beta=3 for every s,
and the same construction also handles the unused zero-bottom s3 boundary. ∎

The top singleton can also be positioned, giving two aligned joint choices.
For the left-bottom construction, if |F|=s-1 choose min(F) for top. The
endpoint fact extends the entire(s-1)-cup F at its right end into a maximum
s-cup, so min(F) is a first maximum-cup point and lies<=L*_cup. If |G|=s,
choose min(G) instead, again a first maximum-cup point. Otherwise top is
empty. Hence bottom-cap-left/top-cup-left is valid. For last maximum-cap
points H, choose max(H) when |H|=s-1 or max(X\H) when its complement has
size s. The left extension makes max(H) a last maximum-cup point, proving
bottom-cap-right/top-cup-right. No open cup core is needed for these endpoint
inequalities. Color duality gives the analogous two joint choices when the
cup number is3. No claim about the other two orientation pairs is required.

The mechanism is dimension collapse: because the maximum cap has length3,
both endpoint classes have cap<=2 and are whole cups. The strong joining
bound prevents their simultaneous full size. For cap4 these classes can
have cap3 and need not be single chains; section38 already shows their
strong number need not decrease. This proof supplies a reason the boundary
is easier and identifies what must be replaced for the general case.

Pilot20261003-152016-e3e78c completed0.049286s/10MiB. It independently checks
all162 open-cap3 states through n6, every valid root's t1/t2/t3 bounds and
both explicit partitions on114 states with cup=strong. Chain metrics enumerate
all monochromatic subsets and strong sizes use the complete quadruple law;
no SAT partition or supplied child hypothesis is imported. Evidence:
open-three-cap-n6.json. The scaled n8 operation audit152147-891f95 completed
53.445623s/28MiB: all2741 open-cap3 states satisfy the bound, every valid
root satisfies the exact t1/t2/t3 clauses, and both partitions are constructed
on1912 states with cup=strong. Evidence: open-three-cap-n8.json. Search
`es search 'decomposable cap three open maximum cap core cardinality linear
bound one-sided band partition'` finds no compiled equivalent. This is a
paper proof with diagnostic construction checks, no Lean theorem.

The top-selector joint audit152607-4e17f4 completed0.062994s/10MiB, checking
both aligned orientations on114 eligible states through n6 with the same
root clauses. Evidence: open-three-cap-joint-n6.json. The small audit checks
the new selector; the previous n8 receipt certifies the base construction.

## 42. Current sufficient missing lemma after the three-cap argument

It now suffices to prove BRL+ from section33 only when **beta>=4**.
Caps of size<=2 cannot have three intrinsic bands because alpha<=s; beta3
is proved in section41. The same conditional size induction therefore gives
full BDL from this beta>=4 realignment lemma and its color dual. Positive
bottom, the supplied-partition hypothesis and either-side choice remain.

This is an explained uniform reduction, not a completed BDL proof. At beta4
the endpoint classes cease to be cups, so the root saturation argument no
longer applies. No replacement compatible-partition invariant is known.

## 43. Root-free explanation of the cap-three boundary (paper)

The DS proof in section41 is valid, but decomposition is not needed for
this boundary. The following dichotomy explains the strong bound directly.
This bound is already supplied by the compiled uniform ordered-two-cup
theorem `ErdosSzekeres.diagonalCupBlocksForce4kk_of_five_le` and its consumer
`diagonal_cup_block_card_add_le` at k=s+1>=5. The natural-language search
below missed it; a subsequent `es search 'two_cup'` found the existing node.
The argument here is explanatory rediscovery, not new theorem credit. Its
application to the positioned cap3 bands is recorded explicitly.

**Two-cups dichotomy.** Let a finite one-change coloring contain two whole
cups A<B separated in x order, |A|=s-1 and |B|=s, s>=3. If its cup number
is at most s and its cap number at most3, then A union B contains a strong
(s+1)-set. Let b0<b1 be the first two B points, and u<v the last two A
points.

Every triple(a,b0,b1), a in A, is a cap: otherwise a prepends B to an
(s+1)-cup. Consequently every triple(a,a',b0), a<a' in A, is a cup;
if it were a cap, the four-set(a,a',b0,b1) would have first and last
triple cap and hence all four triples cap by one-change. Thus A union{b0}
is an s-cup. For every b in B\{b0}, (v,b0,b) is a cap, since otherwise
it appends b to that s-cup.

There are now two cases. If A union{b1} is a cup, the set
A union{b0,b1}, of size s+1, is strong. Its quads contained in A or using
three A points are all cups. A quad(a,a',b0,b1) has colors
(cup,cup,cap,cap), which satisfies the defining strong equalities.

Otherwise (u,v,b1) is a cap: all preceding consecutive triples in
A union{b1} are cups, so a cup final triple would make the whole set a
cup. For each b>b1 in B, (v,b1,b) must be a cup, or (u,v,b1,b) would be
a four-cap. Therefore {v} union(B\{b0}) is an s-cup. The set {v} union B
is strong of size s+1: quads avoiding b0 are all cups, while a quad
(v,b0,b,b') has colors(cap,cap,cup,cup). This exhausts its quads. ∎

Only the elementary one-change fact that a monochromatic consecutive
chain is a whole cup/cap, and that a quad with first and last triple cap
is a four-cap, is used. No DS, decomposition, BDL or induction is used.

**Root-free linear bound.** Let X be any one-change coloring with cap
number3, strong number<=s, and open maximum-three-cap core(L*,R*).
Cut at an empty x gap strictly inside this core. Both spatial sides are
whole cups: a three-cap entirely on the left would end before R*, and
one entirely on the right would start after L*. Their sizes are at most
s. If |X|>=2s-1, one side has at least s points and the other at least
s-1. After reflection if necessary, select separated cups of sizes
s-1,s. The two-cups dichotomy gives a forbidden strong(s+1)-set.
Hence |X|<=2s-2 for every one-change coloring. ∎

The endpoint classes and their cup bounds in section41 also use only
one-change and the open core. Thus the positioned three-band construction
and its aligned joint endpoint choices are valid in this larger class.
The remaining beta>=4 BRL+ obligation is unchanged; its spatial sides may
contain three-caps, so they cannot replace A,B in this dichotomy.

The strong hypothesis cannot be omitted. The guarded solver154032-1638cb
found the seven-point mask32212484335, cup4,cap3,strong5,core(2,4), with
two core-side cups of sizes3,4. This violates |X|<=2*cup(X)-2; it does
not violate the strong bound above. Independent full quadruple replay is
part of the explicit dichotomy audit. Retained evidence:
three-cap-saturation-no-strong-s4.json. Pure root-free saturation queries
with no strong(s+1)-set were UNSAT at s4/n7 and s5/n9, jobs153904-03f555
and153920-2fdf53; those finite verdicts motivated, but do not prove, the
general argument. Search `es search 'two separated cups no four cap force
longer cup or strong set'` has no compiled hit. No Lean receipt is claimed.

The explicit witness audit154340-a4ec14 completed4.081719s, checking all
one-change patterns on5 and7 points. Every admitted separated-cup input
produces the stated strong witness, checked against all defining quads:
88 left-plus-two and88 right-plus-one constructions. Evidence:
two-cups-dichotomy-n7.json. This includes the whole n7 class containing
the no-strong SAT mask above. No repeated numerical BDL claim is made.

## 44. Exact BRL+ coloring-master search and its limits (diagnostic)

The first remaining profile is s5,alpha4,beta4, natural bands1..3. The
new search_exact_brl.py master encodes decomposition at full binary-label
depth n-1, one-change, those exact cup/cap maxima, strong<=5, exact cap
core(L,R), and a valid supplied ordinary partition. For each master
coloring, independent band SAT asks for a left or right realignment.
A returned side partition is excluded from future colorings by an OR of
its forbidden monochromatic cell chains. Exact iff chain atoms permit
this semantic exclusion. Thus every future model still satisfies the
actual BRL+ hypotheses; the search does not freeze any supplied bands.

All four declared queries finished UNSAT after their learned partitions
covered the remaining master colorings:

| n | exact cap core | job | runtime | evidence |
|---|---|---|---|---|
| 7 | (2,4) | 154918-99fe2e | 0.004434s | exact-brl-n7-L2-R4.json |
| 9 | (3,5) | 155025-cee4b3 | 0.033835s | exact-brl-n9-L3-R5.json |
| 11 | (4,7) | 155115-92f0ea | 0.264850s | exact-brl-n11-L4-R7.json |
| 13 | (5,7) | 155247-4273e3 | 0.136848s | exact-brl-n13-L5-R7.json |

Independent complete-class replay155115-380c6a examined all10596
decomposable n7 colorings using complete monochromatic subsets and
defining strong quadruples. All38 admitted core(2,4) inputs validate
the one listed partition directly, in1.406105s; no master atoms or SAT
encoding were reused. Evidence: exact-brl-n7-cover-replay.json.

These are finite diagnostic covers, not a general BRL+ proof and not
Lean-certified refutations. Unqueried sizes/cores and all other profiles
remain open. No uniform explanation has been extracted from the larger
learned partition collections, so they are not fitted into a rule.

One attempted conceptual shortcut is false on paper: disjoint maximum
cup/cap chains do not force a strong set of size alpha+beta-2. For any
a,b>=4, take a lower b-cap entirely left of an upper a-cup. DS gives
cup=a,cap=b,strong=max(a,b,4), with disjoint open maximum-chain cores.
At a=b4,s5 this is already a three-band positive-bottom input, while
there is no strong6. The preserved R23 common-endpoint theorem has an
actual shared-endpoint hypothesis, and cannot bridge such disjoint
chains. The missing compatibility must use the root geometry.

## 45. Positive bottom and cardinal slack still do not permit one-point repair

The four-point example in section15 has bottom0. The following exact
positive-bottom counterexample closes that possible escape from the
failed exchange mechanism. Write each integer for its singleton, and set

  A=2<<(3<<5),
  D=(12<<(11<<10))<<(8<<7),
  E=((4<<9)<<1)<<0,
  C=D<<E, B=C<<6, X=A<<B.

Points are ordered0,...,12. Reading DS at these roots gives:

| set | cup | cap | strong |
|---|---|---|---|
| A | 2 | 3 | 3 |
| D | 3 | 3 | 4 |
| E | 4 | 2 | 4 |
| C | 4 | 3 | 5 |
| B | 4 | 3 | 5 |
| X | 4 | 4 | 5 |

For C, every E pair has its first point before ALL D, so mixed caps
gain at most one D endpoint. A mixed four-cup of C either uses an E
left endpoint with a three-cup of D, or both E endpoints with the D
pair7,8. Every such cup, and E's own four-cup, surrounds6; hence B
retains cup4. B caps have size at most3. For the outer split, at most
one B point(4) lies between A's extreme points2,5. Thus no cap uses
two A endpoints and two B points; maximum four-caps consist of a B
three-cap and one A endpoint. B's prefix through6 is a cup, so these
four-caps all end>=7; a last A endpoint is impossible. They all
start<=5. Caps(5,7,8,10) and(3,4,6,7) attain the two boundaries,
giving the open core(5,7). The strong numbers follow from each joining
cup(lower)+cap(upper) and the child maxima. There is no strong6.

At k6 the valid supplied bands are

  X_1={0,6,12}, X_2={2,3,4,5,10,11}, X_3={1,7,8,9}.

Their chain profiles are(2,3),(3,3),(4,2). Bottom contains interior
point6, so it is neither core-sided. It has NO valid single-point
recoloring. The following table gives one forbidden recipient chain
for each of the two alternate destinations of every point. C means
cup, D means cap; a3-cup blocks band1, a4-cup or4-cap blocks band2,
and a3-cap blocks band3.

| point | first alternate destination and blocker | second alternate destination and blocker |
|---|---|---|
| 0 | 2:C(0,2,3,4) | 3:D(0,1,7) |
| 1 | 1:C(0,1,6) | 2:C(1,2,3,4) |
| 2 | 1:C(0,2,6) | 3:D(2,7,8) |
| 3 | 1:C(0,3,6) | 3:D(3,7,8) |
| 4 | 1:C(0,4,6) | 3:D(1,4,7) |
| 5 | 1:C(0,5,6) | 3:D(5,7,8) |
| 6 | 2:D(2,4,6,10) | 3:D(1,6,7) |
| 7 | 1:C(0,7,12) | 2:C(4,7,10,11) |
| 8 | 1:C(0,8,12) | 2:C(4,8,10,11) |
| 9 | 1:C(6,9,12) | 2:D(2,4,9,10) |
| 10 | 1:C(0,10,12) | 3:D(1,9,10) |
| 11 | 1:C(0,11,12) | 3:D(1,9,11) |
| 12 | 2:D(2,10,11,12) | 3:D(1,9,12) |

Each blocker contains the moved point and otherwise only points already
in its recipient cell. Removing the sender creates no difficulty; every
possible recipient fails. Yet a left repair exists:

  X'_1={0,4,5}, X'_2={7,8,9,10,11,12}, X'_3={1,2,3,6},

again with profiles(2,3),(3,3),(4,2). Its bottom lies<=L*=5. In the
supplied middle, the three-cap A is below the three-cup{4,10,11},
and only one upper point lies between A endpoints, keeping both chain
numbers3. The supplied top and repaired top are lower pairs extended
at both ends. The repaired middle is D with the upper point9; every
D three-cup surrounds9, so its cup number stays3, and caps stay3.
The two bottoms are explicit three-caps. Thus both partitions are
valid directly from the displayed tree. ∎

The ordinary cardinal capacities are4,6,4, totaling14. The isolated
partition uses3,6,4 points: one slot is unused, but no point is compatible
with any recipient. Cardinality slack is not insertion slack. Therefore
positive bottom does not restore a proof by valid one-point moves;
simultaneous global changes or an independent construction are needed.
No additional one-point repair variants are commissioned.

Retained-model audit160142-e3e845 first found this and another isolated
input in0.037185s. Independent pure-definition certificate160248-98a861,
0.013651s, checks all26 move blockers, exact maxima/core, an explicit
strong5, every six-subset's nonstrong quad, and the left repair, without
SAT or chain DP. Evidence: positive-bottom-isolation-certificate.json.
This is a finite paper counterexample to the mechanism, not BRL+ and
not a new Lean theorem.

## 46. An isolated partition also excludes simultaneous monotone repair

This consequence does not use decomposition or one-change. Let F_j be
downward-closed families of subsets, and let P,P' be two valid partitions
indexed by ordered bands. If P'(x)>=P(x) for every point, the whole change
can be executed by valid one-point moves: process moved points in descending
order of their ORIGINAL band. When x moves from i to j>i, all original
points of j which will leave have already moved, and any earlier point
which entered j has j as its final band. Consequently the current recipient
with x is a subset of the final cell P'_j, and is valid. Removing x from
its sender preserves validity. Ties within an original band can be processed
in any order. The descending version is symmetric. ∎

In particular, the isolated partition in section45 has no distinct valid
coordinatewise upward OR downward rearrangement, even if all changes are
performed simultaneously. Positive numerical slack does not rescue a
monotone cascade. This strengthens the failed mechanism without changing
the BRL+ target or commissioning another case.

There is a useful unordered formulation. Draw a directed edge i->j for
each point moving from band i to j. If this transfer graph is acyclic and
nonempty, a sink with an incoming edge has no outgoing points. Its original
cell is contained in its final cell, so any incoming point can move there
validly as a first one-point move. Hence every distinct valid recoloring of
an isolated partition has a directed transfer cycle. The displayed left
repair of section45 in fact exchanges points in both directions across all
three bands. This observation does NOT prove that a compatible cycle exists
or can improve core position; that simultaneous global existence remains
the missing step. No matroid exchange claim is inferred.

Dedup search `es search 'hereditary partition upward acyclic exchange'`
returned no result. This is paper reasoning only, with no Lean receipt.

## 47. Exact higher-cap BRL+ search (declared scope)

The same coloring-master CEGAR of section44 now accepts s,alpha,beta,
keeping the actual missing lemma's hypotheses and an explicitly valid
supplied partition. All monochromatic atoms through the exact maxima are
prebuilt as equivalences; pairs are constant true. No definitions are added
after solver bootstrap. The former rootless implementation is preserved as
search_exact_brl.v2.py, alongside v1.

Question: does BRL+ itself fail at s6,alpha5,beta5, where bands1..4 give
four coordinated choices? A replayed counterexample would refute the
sufficient lemma. Finite UNSAT establishes only the stated n/core query,
not a uniform exchange or context invariant.

Measured pilot161303-9f91a9 is terminal UNSAT for n10/core(4,6), after five
semantic side-partition exclusions,0.046702s/19MiB. Length5 encoding size
grows by about12x at n15, with about7x cubic base DP; SAT search itself has
no reliable polynomial ETA. Larger actual query161401-254cd3 at n15/core(6,8)
finished fixed-query UNSAT in19.914635s/129MiB, after713 semantic
side-partition exclusions. Its streamed records are retained. No general
exchange explanation is obtained from this cover; no further confirmation
query on this route is commissioned after these two attempts.
Other parameters and core positions remain open.

## 48. A spatial core side can retain the entire strong budget

Dropping the cap number at a core cut does not in general drop the strong
number. There is a uniform decomposable example in the exact positive-floor
domain with FOUR bands. Fix beta>=5 and s>=beta+1, put l=s-beta, u=l+2,
v=beta-2 and alpha=l+4. Let C be a whole(beta-1)-cap. After all C points,
place a v-cap V and insert a whole u-cup U in one empty gap between its
first and second points. Set Z=U<<V, Y=C<<Z, and X=a<<Y, where a is a
singleton before all C and Z points.

Z has cup u+2=alpha, witnessed by first(V),U,last(V). Its cap is v:
each added U endpoint in a mixed cap excludes the corresponding V extreme;
indeed U lies in one gap, so two U endpoints cannot surround any V point.
DS gives strong(Z)=u+v=s. In Y, all C points precede all Z points. Mixed
cups have length<=cup(C)+1=3, and mixed caps<=cap(Z)+1=v+1=beta-1.
Thus cup(Y)=alpha,cap(Y)=beta-1,strong(Y)=s, since its root join is
cup(C)+cap(Z)=beta<s. In X, mixed cups have length<=2 and mixed caps
are a followed by a cap of Y. Hence

  cup(X)=alpha, cap(X)=beta, strong(X)=s.

Every maximum beta-cap of X starts at a. A(beta-1)-cap of Y is either
all C or ends in Z, so the earliest last point of a maximum beta-cap is
last(C). Consequently the open cap core is(a,last(C)), and the ENTIRE
s-point strong set Z lies strictly to its right. Reversing x gives the
same counterexample for a prescribed left side. This refutes a universal
claim that both spatial sides have strong<=s-1; it does not show that
neither side can have the smaller strong budget.

The supplied BDL partition is explicit:

  X_l={a}, X_(l+1)=C, X_(l+2)={first(V)} union U,
  X_(l+3)=V minus {first(V)}.

The third cell is a cup of length u+1=l+3 with cap2; the fourth is a
(v-1)-cap. These meet the exact cup/cap limits. The natural range has
four bands because alpha+beta=s+4, with positive bottom l>=1. Its bottom
is already left-sided; BRL+ is not refuted. ∎

The first-parameter audit162005-914809 (s6,beta5,n11,core(0,4)) completed
0.002991s/11MiB; its output verifies the strong witness, all330 successor-
set blockers and the explicit bands. It uses direct chain/strong definitions and the shared whole-cup
construction. The uniform proof above is DS reasoning, not inferred from
a successful case. A three-band boundary analogue would have a different
constraint alpha+beta=s+3 and is not settled by this family.

## 49. Prescribed spatial strong-drop fails even with exactly three bands

The boundary distinction in section48 does not rescue a prescribed-side
strong-drop induction. Fix beta>=4,s>=beta+1,l=s-beta,alpha=l+3,v=beta-3.
Place a whole alpha-cup P before a whole beta-cap D, and set L=D<<P.
Insert a whole v-cap T in the first empty gap of P, and set X=L<<T.
Thus T is above the whole lower L, while inside P's first x-gap.

In L, cups are either pure P or a cup of D (length<=2) with one P
left endpoint; caps are either pure D or a cap of P (length<=2) with
one D right endpoint. Hence cup(L)=alpha,cap(L)=beta,strong(L)
=max(alpha,beta,4)<=s. Every maximum beta-cap of L is all D.

In X, mixed caps have length<=v+2=beta-1. A mixed cup using a lower
cup contained in P cannot gain an endpoint without omitting the
corresponding P extreme: T lies in a single empty P gap. A lower cup
meeting D has length<=3 and ends after ALL T, so gains at most one T
left endpoint, giving length<=4<=alpha. Pure T cups have length<=2.
Therefore cup(X)=alpha,cap(X)=beta, and its only maximum beta-cap is D.
DS gives strong(X)=cup(L)+cap(T)=alpha+v=s. In particular the ENTIRE
strong s-set P union T lies strictly BEFORE the open core(firstD,lastD).
Reversing x gives full strong number strictly after the core. ∎

An explicit right-sided BDL partition uses all three natural bands:

  X_l={lastD}, X_(l+1)={firstP} union(D minus lastD),
  X_(l+2)=T union(P minus firstP).

The middle has cup<=3<=l+2 and cap<=beta-1. The top has cup<=alpha
and cap<=v+1=beta-2, because all remaining P points follow T. The bottom
is a singleton at the right core boundary. Thus all BRL+ hypotheses are
met and BRL+ itself holds in this family. Only a proposed shortcut that
lowers the strong budget on a prescribed spatial side is refuted.

Minimal parameters beta4,s5 give n9,cup4,cap4,strong5,core(5,8), with
an explicit full strong set(0,1,2,3,4). Diagnostic layout/reversal audit
162907-949dc5 completed0.002006s/11MiB and verifies both the layout and
x-reversal, full strong number, cap cores and the displayed partitions.
It reuses complete-subset chain metrics and all-quad strong evaluation,
and performs no SAT solve or sweep. Both owned audits are terminal; outputs
were inspected. The uniform proof is not inferred from these cases and
no new Lean receipt is claimed.

## 50. At three bands, full-strength decomposition nodes form one spine

There is nevertheless a different boundary fact. A strong r-set with
r>=2 has a cup and cap whose cardinalities sum to r+2. Indeed the strong
quadruple law is middle determinacy (already compiled as
FinsetPolygon.isStrongPolygonSet_iff_isMiddleDeterminedOn). Color each
internal point by its triple with the two extrema; the cup-marker points
and both extrema form a cup, and the cap-marker points and both extrema
form a cap. They share precisely the extrema and cover the strong set.
Consequently sigma(Y)<=cup(Y)+cap(Y)-2 whenever sigma(Y)>=2.

Now assume ambient cup<=alpha,cap<=beta,strong<=s and alpha+beta=s+3.
If both children A,B of ANY decomposition node contained a strong s-set,
then

  cup(A)>=s+2-beta=alpha-1,
  cap(B)>=s+2-alpha=beta-1.

Their DS join is at least alpha+beta-2=s+1, contradiction. Thus at most
one child retains the full strong budget. All nodes with strong number s
in a fixed decomposition tree are comparable by ancestry: two incomparable
ones would give two full-strength children at their least common ancestor.
They form one spine. ∎

This concerns nodes, not a common point of every maximum strong witness.
Full witnesses can meet both children as lower cups plus upper caps, and
sections48-49 show that their spatial location does not give the desired
strong drop. At four bands alpha+beta=s+4, the same arithmetic yields only
a root join>=s, so the contradiction disappears. This is a structural
boundary, not a compatible-band construction or a proof of BRL+.

Dedup search `es search 'strong middle cup cap'` located the existing
middle-word and common-extremes statements; no new Lean theorem is claimed.

## 51. The isolated child really blocks a literal tight retained-cap root

Use the exact n13 child Y of section45, with supplied cells
{0,6,12}/{2,3,4,5,10,11}/{1,7,8,9}. Insert a lower singleton in gap6,
after old point5 and before old point6, giving new point a=6 and shifting
all old indices>=6 by one. Then X={a}<<Y is the actual tight R root:
s5,cup(lower)=1=s-cap(Y),cup(X)=cup(Y)=4,cap(X)=cap(Y)=4,strong(X)=5.
Retention follows from inserting in ONE empty gap of the open core(5,7).

Keeping the supplied child assignment fixed, no choice of a's band works.
Band1 contains cup(0,6,13); band2 contains cap(2,3,5,6); band3 contains
cap(6,8,9). Thus failure is not caused by precommitting a to the bottom.
Yet the left realignment from section45 extends to valid parent cells

  {0,4,5,6}/{8,9,10,11,12,13}/{1,2,3,7},

with profiles(2,4),(3,3),(4,2). They saturate the ordinary4+6+4 capacity.
The parent's cap core closes to(6,6); no parent core-side assertion is
needed for this ordinary BDL partition. This is not a BDL refutation.

Independent pure-definition audit163902-f49cdf,0.016231s/13MiB, reuses
only the retained child labels/certificate and records all3 extension
blockers, exact chains/core, an explicit strong5, every one of3003
six-subset nonstrong quads and the repaired parent cells. Artifact
exact-frozen-child-root.json. No new coloring search or SAT solve is used.
This directly shows that an arbitrary supplied child IH witness cannot
lift in the exact remaining positive-bottom three-band domain. No new
one-point repair variant or Lean receipt is claimed.

The logically exact residual obligation, conditional equivalence to BDL,
and the stronger sufficient BRL+ route are written independently in
BDL-CORE-REDUCTION.md. This is a clarified reduction, not a closed theorem.

## 52. The sum of child band demands is bounded by the parent demand

For a fixed ambient strong budget s, write

  b_s(Y)=max(0,cup(Y)+cap(Y)-s).

When positive this is exactly the number of natural BDL band indices of Y.
At X=A<<B, the DS join gives cup(A)+cap(B)<=s. Heredity gives
cap(A)+cup(B)<=cap(X)+cup(X). Adding yields

  (cup(A)+cap(A)-s)+(cup(B)+cap(B)-s)
    <=cup(X)+cap(X)-s.

If both child excesses are positive, this proves b_s(A)+b_s(B)<=b_s(X).
If only one is positive, its cup and cap are individually bounded by X's,
so its b_s is<=b_s(X); the other contributes zero. If neither is positive,
the inequality is trivial. Thus clipping at zero causes no exception.
Induction down the decomposition tree gives

  sum_{Y in any node antichain} b_s(Y)<=b_s(X).

For s>=2 a node with strong number s has cup+cap>=s+2, by the existing
middle-determinacy characterization used in section50. Each such node
therefore charges at least two demand units. At root demand m, every
antichain of full-strength nodes has size<=floor(m/2). The three-band
one-spine fact is the m=3 instance of this resource bound. ∎

This concerns numerical demand and branching, not the ability to place
points in the allocated bands. In the exact residual root cup(A)=s-cap(B),
A is classic and b_s(A)=0, while B retains all root demand. Section51 shows
that this zero charge can still obstruct every frozen assignment. A proof
must explain physical compatibility along the demand-carrying branch.
Dedup searches `es search 'cup cap excess subtree'` and
`es search 'full strong skeleton'` returned no matches. This is paper
structure, not a new compiled statement or proof receipt.

## 53. Fixed three-band demand does not bound full-strength spine depth

Let beta>=5,s=beta+1. Start with D<<C, where D is a beta-cap lying entirely
before C, a four-cup. Choose a D gap with a>=2 D points to its left and
b=beta-a>=3 to its right. Place h lower singleton ancestors in that ONE
empty gap, where 1<=h<=a-1, with ancestry depths 1,2,...,h in x order.
Depth1 is the outermost lower singleton; each deeper tag belongs to its
upper descendant. Every base address is prefixed by 1^h; the tag of depth
d has address 1^(d-1)0. This specifies a decomposable family.

The exact ancestor cap formula from sections26/30 has increasing depth
length h, decreasing length1 and pure peak h. The free left cap is a;
the free right cap is max(b,3)=b (a D endpoint plus two C points can
give a 3-cap). Hence the global cap is

  max(beta,a+1,b+h,h)=beta.

All terms except the pure D cap are strictly below beta: a+1<=beta-1,
b+h<=beta-1 and h<beta. A cap using free C points has length<=2 before
the same ancestor extension, so cannot evade these bounds. Thus the only
maximum beta-cap is D, with unchanged open core(firstD,lastD).
Every mixed cup at a singleton root has length<=3, while C remains a
four-cup; cup=4. The base strong number is beta (beta>=4), and every
singleton-root join is 1+beta=s. Each of the h ancestor nodes consequently
has cup4,capbeta,strongs, with exactly 4+beta-s=3 natural bands.

There is an explicit right-sided BRL partition:

  X_1={lastD}, X_2=(D minus lastD) union(all tags), X_3=C.

The middle has cup<=3 by the singleton-root recursion over a cap, and
cap<=beta-1 because it omits lastD from the unique beta-cap. The top has
cup4,cap2<=beta-2; the bottom is a singleton at the right core boundary.
Thus this family satisfies BRL and does not refute BDL. Taking a=beta-3,
b=3,h=beta-4 makes full-strength spine depth unbounded as beta grows,
while the intrinsic demand is always three. The demand bound controls
branching width, not how many classic zero-demand contexts occur along
the surviving branch. ∎

One beta6,s7,a3,b3,h2 layout was independently audited against all subset
chain and all-quad strong definitions in job165435-aefae8,0.014965s/11MiB.
The n12 artifact fixed-band-long-spine.json records the unique cap
(0,1,2,5,6,7), core(0,7), both full-strength nodes, a strong7 witness and
the displayed band profiles(1,1),(3,5),(4,2). It performs no coloring
enumeration, SAT solve or sweep. Initial job165414-0320be failed before
any mathematical assertion on the Coloring.cup API typo; failed source
version and the harness traceback are preserved. Semantic maintenance review
corrected the initial paper's b>=2 range to b>=3: the free right cap is
max(b,3), so b2 does not justify the unique-cap assertion. The successful
audit already used b3. No new Lean receipt.

## 54. Three-band compatibility is a coupled outer-transversal problem

Write alpha+beta=s+3. The natural bands are l=alpha-3,l+1,l+2,
which we call L,M,T. Their required profiles are

  L: cup<=alpha-2,cap<=beta;
  M: cup<=alpha-1,cap<=beta-1;
  T: cup<=alpha,cap<=beta-2.

Since global cup=alpha,cap=beta, the L cap and T cup limits are automatic.
The two M limits hold exactly when L union T meets EVERY maximum alpha-cup
and maximum beta-cap. Consequently a valid three-band partition is exactly
a disjoint choice of outer transversals L,T such that

  L union T hits all maximum cups and caps,
  cup(L)<=alpha-2 and cap(T)<=beta-2.

Core-side BRL adds L subset(-infinity,L*] or L subset[R*,infinity).
This exact reformulation is shared input from coordinator Q9h,
primary runs/claude-bandrule-20261003/NOTES.md sectionQ9h. Search
`es search 'three bands transversal maximum cup cap'` found no compiled
result. The equivalence is immediate from the displayed limits; it is
not a construction or a newly accepted theorem.

The proposed stronger BS+MT operation from that input starts with valid
old L,M,T. For one chosen side it keeps allowed-side old L fixed, sends
wrong-side old L to M or T, permits allowed-side old M/T to drop into L,
and permits old M to rise to T. No other move is allowed. It is genuinely
simultaneous, unlike the one-point or monotone routes refuted in sections45-46.
Coordinator h5.py combines LEFT and RIGHT outcomes with OR, so its tested
claim is either-side existence, not a theorem for each prescribed orientation.

On the exact isolated n13 child from section45, this rule has a RIGHT repair

  {7,8,12}/{2,3,5,6,10,11}/{0,1,4,9}.

The transfers are0:L->T,4:M->T,6:L->M,7/8:T->L. They contain both
an L/T cycle and an L/M/T cycle; no valid one-point order exists because
the supplied partition is isolated. The same rule has NO LEFT repair.
Here is a finite forced proof, with indices of section45:

1. Old L point0 remains L; old T points7,8,9 lie beyond L*=5 and remain T.
2. Points10,11,12 cannot enter left L, and each cap(7,8,x) forbids T.
   All three must belong to M.
3. For y=2,3, cap(y,7,8) forbids T and cap(y,10,11,12) forbids M.
   Both y must enter L.
4. Cup(0,2,3) violates L's cup<=2 bound. Contradiction.

Thus the PRESCRIBED-SIDE BS+MT claim is false. This supplied partition
does not refute either-side BS+MT; section55 refutes it with a different
supply on the same coloring. Full LEFT BRL also survives:
the known left repair moves old top points7,8,9 down to M, outside this
operation's allowed moves. No BDL/BRL refutation follows.

Constrained SAT query165924-294138 passed0.036585s/13MiB and separately
reported LEFT UNSAT/RIGHT SAT, three-band-swap-rule.json. Independent
pure-definition certificate170040-4bb30b,0.009638s/8MiB, checks all seven
cap facts and the cup contradiction, the right partition/move permissions,
exact input maxima/core and every1716 successor-strong obstruction.
Artifact three-band-swap-side-certificate.json. It uses no SAT or DP and
does not enumerate candidate repairs. Both jobs are terminal and inspected.

The proof gap is now visible as two coupled demands: dropping first points
of re-exposed maximum caps can repair their transversal condition, but those
drops may create a forbidden cup in L; avoiding that may require top moves
that create forbidden caps in T. No argument from the strong bound is known
that guarantees a compatible choice on at least one side. Fixed endpoint
selection and prescribed orientation are not justified substitutes.

## 55. Even at three bands, every sided repair can require top-to-middle moves

The BS+MT permissions have a simple exact interpretation. If a new valid
partition has bottom Lnew on chosen core side G, then it is a BS+MT repair
of old L,M,T exactly when

  Lold intersect G subset Lnew, and Told intersect Mnew is empty.

The first condition fixes permitted old-bottom points. The second forbids
top-to-middle moves. All other permissions follow from Lnew subset G:
wrong old-bottom can rise to either band, old-middle can rise or stay or
drop on G, and old-top can stay or drop on G. Thus BS+MT is an ANCHORED
outer-transversal problem, stronger than BRL's unanchored existence.

On the SAME decomposable coloring X of section45, change only the supplied
partition to

  L={3,8,9,12}, M={0,1,2,4,5}, T={6,7,10,11}.

It is valid, with profiles(2,4),(3,3),(4,2) and one unused ordinary slot
in M. Globalcup4,cap4,strong5,core(5,7) are unchanged. The stronger fact is:
EVERY valid left-sided OR right-sided repair has Mnew intersect Told nonempty.
In particular either-side BS+MT is false even if its bottom anchors are dropped.

**Left proof.** Suppose Mnew avoids Told. Every old top point6,7,10,11
lies beyond L*=5, so cannot enter left Lnew and must stay Tnew. These
four points form a cup. Tnew has cap<=2, hence is a whole cup, and global
cup=4 forces Tnew exactly Told. Points8,9,12 are wrong-side and cannot
enter Lnew; they must enter Mnew. For y=2,3,5, cap(y,8,9,12) then excludes
Mnew, while top is full, so all three y lie in Lnew. Cups(0,2,3),
(1,2,3),(2,3,4) exclude0,1,4 from Lnew. Top is full, so these three enter
Mnew, together with9. But cup(0,1,4,9) violates Mnew's cup<=3. ∎

**Right proof.** Old top point6 lies before R*=7, so it cannot enter right
Lnew and must stay Tnew. The three old top points7,10,11 form a cup,
so cannot all belong to Lnew, whose cup bound is2. Since none may enter
Mnew, some z in{7,10,11} also lies in Tnew. For each x in{0,2,3,4},
triple(x,6,z) is a cap. It excludes x from Tnew, whose cap bound is2.
All these x lie before7, so cannot enter Lnew either. All four enter
Mnew, contradicting cup(0,2,3,4). ∎

Ordinary BRL survives on both sides, for example

  left:  {0,4,5}/{7,8,9,10,11,12}/{1,2,3,6};
  right: {7,8,12}/{2,3,5,6,10,11}/{0,1,4,9}.

Each moves old top into the middle. This is a refutation of a restrictive
repair mechanism, not of BRL or BDL. No Lean theorem or refuted node is
registered. Shared Q9h's empirical statement that three-band higher repair
needs only M->T does not generalize; three bands already need downward
repair among the higher cells. Further fitted BS+MT variants are stopped.

Job170638-267fba used complete all-subset monochromatic cells to enumerate
all905 valid partitions of this fixed coloring. Bottom has cup<=2, hence
is a whole cap; top has cap<=2, hence is a whole cup. This makes the
inventory exhaustive without a SAT/model limit. There are28 left and80
right partitions, and every one has middle intersecting the supplied top.
The supply scan stopped on this refutation, after52 supplies; remaining
supplies were not classified and no coverage is claimed for them. Artifact
all-supplies-swap-rule.json,0.071694s/13MiB, no new coloring search.

Independent pure-definition job171455-14b1ba,0.026155s/8MiB, certifies
all30 left and77 right sided-cap/top-cup pairs that could keep old top
outside middle, each with an explicit forbidden middle4 chain. It also
checks exact maxima/core/strong and both displayed repairs, with no SAT/DP.
Original pair-cover source/output are preserved as v1. The short proof's
finite chain facts are included in the updated certificate source;
job171640-4579d2 checked them0.023239s/8MiB, including all twelve right
blocking triples and the left cap/cup facts. Artifact
top-middle-required-certificate.json. This is diagnostic evidence, not a
new compiling result. The obstruction is coupled placement, not slot count.

## 56. Positive demand has a finite skeleton, with the hard contexts on edges

Fix a decomposition tree with root demand m=b_s(X)>0. Keep precisely its
positive-demand nodes. They form a connected rooted subtree because cup
and cap maxima are hereditary. For each retained node v define

  e(v)=b_s(v)-sum_{positive children w} b_s(w)>=0.

The inequality is section52. Telescoping over the retained finite tree
gives sum_v e(v)=m. Since demand is integral, at most m nodes have e(v)>0.
Every leaf of the retained tree has positive defect, namely its demand.
Contract all zero-defect vertices with one positive child. The remaining
zero-defect vertices have two children, since a zero-defect leaf is
impossible. In a finite tree of outdegree<=2, branching vertices are at
most leaves minus1. Thus, if D is the number of positive-defect vertices,
the reduced skeleton has at most D+(D-1)<=2m-1 vertices. ∎

Every contracted edge retains the EXACT cup and cap numbers, not just
their sum: positive equal demand gives equal c+d, and both c,d individually
cannot decrease toward the parent. The omitted sibling is classic. If
the positive carrier is upper B, its lower sibling has cup<=s-beta, so
mixed cups are<=s-beta+2=alpha-m+2. For m>=3 this is<alpha; every maximum
alpha-cup therefore remains entirely in the carrier. The lower-carrier
dual preserves every maximum beta-cap. Each edge is the slack or tight
retained-maximum context from the exact root reduction.

This explains where the complexity resides. Branching/creation topology
depends only on the band demand, but the contracted edges contain classic
contexts at unchanged alpha,beta. Section53 shows their depth need not be
bounded by m. For a single orientation, one maximum-chain family is
preserved; the other can acquire new chains and shrink its endpoint core.
Alternating orientations can change both families. Numerical maxima alone
do not record this compatibility. The finite skeleton is not a partition
construction or a proof of the exact residual root obligation.

Dedup search `es search 'positive demand decomposition skeleton'` found no
matches. This is a written structural interpretation, with no new Lean
statement or receipt. It suggests treating entire context chains together
rather than repeatedly asking an arbitrary child assignment to extend.

## 57. The two off-spine context collections separately fit two edge bands

Consider one constant-profile chain from section56, with cup alpha,cap beta,
strong<=s and m=alpha+beta-s>=3. Put p=s-beta,q=s-alpha. Collect all
off-spine LOWER siblings into D and all off-spine UPPER siblings into U,
excluding the terminal carrier. Every lower sibling has cup<=p by the DS
join with its carrier of cap beta. After deleting all upper siblings and
the terminal carrier, induction along the remaining lower-context chain
gives cup(D)<=p+2: each mixed cup uses at most two points above one lower
sibling. Heredity gives cap(D)<=beta. Dually cap(U)<=q+2,cup(U)<=alpha.

D has a valid partition using only the first two parent bands p,p+1:

- If cup(D)<=p+1, put all D in band p.
- Otherwise cup(D)=p+2. If cap(D)<=beta-1, put all D in band p+1.
- In the remaining exact profile(p+2,beta), use the first endpoints of
  maximum caps in band p and their complement in band p+1. The endpoint
  split gives the required limits(p+1,beta),(p+2,beta-1).

Empty collections are harmless. The endpoint theorem requires both chain
numbers>=2; these hold in this remaining nontrivial case. Independently
verified R23 source at preserved commit7806d5c4 gives exactly those
hypotheses. Global chain number1 means at most one point and belongs to
the trivial one-band boundary, so no small-parameter exception is hidden.

The dual argument places U in the last two bands alpha-2,alpha-1. If
m>=4, first and last pairs are disjoint, so the union of all contexts
ALONE has a valid partition without mixing these two collections. At
m=3 they share the middle band. In every case the terminal carrier still
needs its own bands and compatible merging with the contexts. Nothing
here closes that interaction or supplies an induction invariant. ∎

This states what the demand-zero siblings can accumulate: at most two
edge bands on either side, rather than permanent placement in one band.
The numerical demand inequality cannot encode which carrier points must
change when those contexts are merged. Dedup search
`es search 'constant profile contexts two bands'` found no matches;
paper structural interpretation only, no new Lean receipt.

## 58. Exact sibling-span conditions, rather than a full-core requirement

For a nonempty ordered set S write span(S)=(min S,max S), and take its
open span empty if it has fewer than two points. At a deep-below root
X=A<<B, let beta=cap(B)>=2. DS gives the following exact characterization:

  cap(X)=beta iff
    cap(A)<=beta,
    EVERY A point is strictly inside EVERY maximum beta-cap of B,
    cap(B intersect span(A))<=beta-2.

Necessity: a pure A cap cannot exceed beta; an exterior A point extends a
maximum B cap to beta+1; two A extreme points extend an internal
(beta-1)-cap of B to beta+1. Sufficiency: any mixed cap of beta+1 uses
either one A endpoint plus a beta-cap of B, or two A endpoints plus a
(beta-1)-cap of B. Both forms are excluded. Pure B/A caps are bounded.
These are every possible form by DS. The middle condition alone controls
single-endpoint extension; the final condition controls TWO endpoints.

There is also an exact absorption test. Suppose cup(A)=p>=1, C subset B
is the bottom of a valid child partition, so cup(C)<=p+1. Then

  cup(A union C)<=p+1
    iff cup(A intersect span(C))<=p-1.

A forbidden(p+2)-cup cannot be pure A or pure C. By DS it must consist
of a maximum p-cup of A strictly between two C endpoints. Such a cup
exists exactly when A inside the extreme C span has cup number p. If
C has fewer than two points, the mixed two-endpoint form is unavailable
and both sides hold. Cap(A union C)<=beta follows from retained parent
cap, so this is the EXACT remaining test for adding all A to bottom. ∎

For p=1 (a singleton A), bottom C must lie on one side of that point.
For p=2, A is a cap and C's span may contain at most one A point. For
general p it is the actual INTERVAL cup rank of A, rather than a scalar
size or a rule about every A point, that decides the obstruction.

A sibling-aware sufficient lemma would therefore ask for a valid child
partition whose bottom C satisfies cup(A intersect span(C))<=p-1,
with the above exact retained-cap window hypotheses. It is equivalent
to a parent partition placing ALL A in bottom. This is weaker than
full-core BRL, since a bottom span can cross some A points without
containing a maximum A cup. It is still stronger than the exact ordinary
root obligation, which may assign A to several bands. No such sibling-
aware existence lemma or normalization theorem has been proved.

The advantage is semantic: the actual root supplies the beta-2 interior
cap window, and the required avoidance is only the p-cup bracket that
would overflow. Full-core positioning discards that sibling geometry.
This is a more precise description of the obstruction, not a solved
narrowing or a claimed preserved invariant.

Dedup search `es search 'bottom span sibling cup'` found no matches.
Diagnostic pilot173056-52fabf checks both general equivalences on ALL
n<=4 decomposable colorings/root cuts/eligible upper subsets,0.001394s/10MiB.
Full n<=6 semantic audit173627-983795 completed0.099957s/10MiB on all
792 class members and1214 root cuts:789 cap-retention and12788 eligible
upper-subset absorption checks, including2870 forbidden absorptions, all
agree. Artifact root-span-semantics-n6.json. Reuses promoted root_masks
and complete all-triple subset metrics, with no SAT solver or partition-
existence assumption. The literal n14 root of section51 separately checks
the relevant positive-bottom geometry: its frozen bottom spans the singleton,
while the repaired bottom lies before it. These are semantic audits of
general written identities, not BDL existence proofs or Lean receipts.

## 59. Constant-profile contexts cannot be merged into one lower sibling

The bound cup(D)<=p+2 of section57 is sharp even when EVERY lower sibling
is a p-cup or singleton, all carrier profiles stay constant, and D has
zero intrinsic demand. This also shows why contracting the numerical
tree skeleton does not contract the actual deep-below relation.

Fix beta>=6,p>=1,s=p+beta,alpha=p+3. Start with a beta-cap K followed
spatially by an alpha-cup C, with K<<C. In the K gap after its third
point place, in x-order, a singleton a1, a whole p-cup A0, a singleton a2.
Their ancestry depths are respectively2,1,3: X3=a2<<(K<<C),
X2=a1<<X3, X=A0<<X2. Thus A0 is outermost despite lying between the
two other lower contexts. Let b=beta-3>=3 be the number of K points
after the gap. All three inserted blocks lie in one initially empty gap.

At X3, every mixed cap uses one singleton and one K side, hence has
size at most max(4,b+1)<beta. At X2 its left upper cap bound is3,
its right upper cap bound is b+1, so mixed caps are at most
max(4,b+2)<beta. At X, A0 is contiguous, so no mixed cap with two A0
endpoints has an upper interior point. A one-endpoint mixed cap has
size at most max(5,b+2)<beta. Pure A0 caps have size<=2. Consequently
K is the ONLY maximum beta-cap throughout and all carrier cap numbers
are beta. Cup numbers stay alpha: mixed cups above singleton children
are <=3, while A0 can create at most p+2<alpha. The free C realizes
alpha. The strong recurrence gives strong(X)=p+beta=s; the earlier
joins are beta+1<=s and the base strong number is max(beta,alpha,4)<=s.
Every carrier therefore retains demand alpha+beta-s=3.

The union D={a1} union A0 union {a2} is a whole(p+2)-cup: the outer
A0 supplies every mixed middle point. Its cap number is2 and
b_s(D)=max(0,p+4-s)=0. Nevertheless D cannot all enter bottom p, whose
cup limit is p+1. Nor is D deep below the original carrier as one
merged sibling. For a K point d before the gap, the triple(d,a1,a0)
with a0 the first A0 point is a CAP, since at the outer split its middle
point a1 is upper. A supposed split D<<(K union C) would make the
same triple a CUP, since its middle point belongs to D. ∎

There are explicit valid bands p,p+1,p+2: last K point in bottom,
all other K points and all D in middle, and C in top. Middle has cup
<=p+2 and cap<=beta-1 because K was the only maximum beta-cap. Top
has cup alpha and cap2<=beta-2. This is a right-sided BRL partition.
There is also an ALL-A0-bottom ordinary parent partition: put A0 and
the last K point in bottom, all other K points and a1,a2 in middle,
C in top. Bottom has cup<=p+1; middle has cup<=3<=p+2 and cap<=beta-1.
Thus normalizing one actual root sibling can work while permanently
keeping every earlier lower sibling in bottom fails. No failure of
all-A-bottom normalization for an individual root is claimed.

Dedup search `es search 'constant profile lower siblings cannot merge'`
found no matches. First-layout n13,beta6,p1 diagnostic175147-3d72a3
checks complete all-triple chains, independent all-quad strong maximum7,
context cup(3,4,5), nonmerge cap(0,3,4), and both explicit partitions.
Source check_context_shortcuts.py, output context-shortcuts-certificate.json;
combined two-layout time0.122778s/12MiB. The uniform argument is DS paper
reasoning, not a new compiling theorem. The carrier/context word remains
necessary input for a constructive induction.

## 60. The whole cap core need not satisfy the sibling-window cap drop

The exact retained-root condition of section58 bounds the cap number
inside the ACTUAL span of A by beta-2. It cannot be replaced by a bound
on the whole maximum-cap core, even in the exact positive-bottom
three-band BRL domain.

Fix beta>=5,s=beta+2. Let K be a whole beta-cap and I a whole
(beta-1)-cap. Place I in one K gap after two K points, with I<<K,
and at least three K points to its right. In Z=I<<K, mixed caps with
one I endpoint have size<=beta-1; two I endpoints cannot surround K
points because I is contiguous. Thus cap(Z)=beta and K is its only
maximum cap. Both K sides are nonempty, so two I endpoints and one
K point at each side give cup(Z)=4. The strong join is2+beta=beta+2.

Now put an upper whole5-cup P in one EMPTY INTERNAL gap of I, with
W=Z<<P. Mixed cups are at most cup(Z)+one upper endpoint=5 because
P occupies a single empty gap, so cup(W)=5. Mixed caps are at most
two lower endpoints plus cap(P)=4<beta, so cap(W)=beta and K remains
the only maximum cap. The strong recurrence is
max(beta+2,5,4+2)=beta+2=s. Hence natural bands are2,3,4 and the
open cap core is(first K,last K), containing the ENTIRE(beta-1)-cap I.
Its cap number is therefore at least beta-1, not beta-2. ∎

Both BRL orientations are explicit: put the first OR last K point in
bottom2, all remaining Z points in middle3, and P in top4. Middle
has cup<=4 and cap<=beta-1; top has cup5 and cap2<=beta-2. BDL and
BRL are thus satisfied by this family. If one were to spread two new
lower A endpoints around all I, the resulting cap beta+1 would violate
retention; such a parent is not an admissible remaining root.

Dedup search `es search 'maximal cap core interior cap beta minus one'`
found no matches. The same175147-3d72a3 diagnostic independently checks
the first n14,beta5,s7 layout: cup5,cap5,strong7,unique maximum cap
{0,1,11,12,13}, core(0,13), internal cap{2,3,9,10}, and both supplied
sided partitions. No SAT query or new existence theorem is involved.
The actual sibling span cannot be discarded from the weaker absorption
route; full-core BRL remains a stronger sufficient alternative, unproved.

Maintenance13 sharpened the certificate to check the COMPLETE maximum-cap
list, not only its endpoint extrema: in each layout that list is exactly
{K}. Preserved source check_context_shortcuts.v1.py and original output;
updated source and context-shortcuts-certificate-v2.json passed guarded
175424-e14abb,0.145429s/11MiB. Both explicit partitions remain valid.
This removes a validation gap in the independent uniqueness check; no
mathematical statement or parameter coverage was changed.

Paper simplification: the same whole-core cap-drop obstruction exists for
EVERY beta>=4. Keep Z=I<<K, with two K points before I and beta-2>=2
after. Put P spatially AFTER all Z, with W=Z<<P. Cup(W)=5 because
cup(Z)=4, mixed cups gain at most one upper endpoint, and P is a5-cup.
Mixed caps now gain at most one LOWER endpoint and at most two P points,
so their size is<=3<beta, preserving K as the only maximum cap and all
I inside its core. The strong join is4+2=6<=beta+2 and Z already has
strong beta+2. The same first/last-K singleton bottom2, Z remainder
middle3, P top4 maps satisfy their limits. This is a uniform DS paper
argument; no additional beta4 layout or compiling theorem is claimed.
No case is commissioned: the global shortcut is already refuted, and
its earliest parameter would not advance the missing compatibility proof.

## 61. Pascal strong-budget reduction still needs compatible child bands

Write a Pascal split as X=R disjoint-union Bl, with

  cap(R)<=beta-1, cup(Bl)<=alpha-1,
  strong(R),strong(Bl)<=s-1.

Even when this split exists and each child has valid bands at budget s-1,
the proposed parent cells R_j union Bl_(j-1) need not be valid. This is
a compatibility failure of arbitrary witnesses, not a PSL counterexample.

A uniform literal hard-root family explains it. Fix p>=2,beta=4,
s=p+4,alpha=p+3. Let Q be a whole4-cap followed spatially by an
alpha-cup S, with B=Q<<S. Insert a contiguous LOWER p-cup A in the Q
gap after its second point, with X=A<<B. B has cup alpha,cap4 and
strong alpha<=s-1. Its only maximum4-cap is Q and every A point is
strictly inside Q. Both Q sides have two points. B's right side of A
has cap3 (one Q point and two S points), so a mixed parent cap can
reach4 but cannot exceed4. No B point lies inside A's span. Thus
cup(X)=alpha,cap(X)=4,strong(X)=p+4=s: this is exactly case R.

Let z be the last S point, R=A union(S minus z), Bl=Q union{z}.
Their exact profiles and strong numbers are

  R: cup=p+2,cap3,strong=p+2;
  Bl: cup3,cap4,strong4.

They meet every Pascal condition. For R, put A in child band p and
S minus z in p+1. These are its TWO natural bands at child budget p+3.
For p=2, put all Q in Bl child band p-1 and z in p; both cells meet
Bl's natural bands1,2. For p>=3, put all Bl in p-1, a valid whole
cell with cup3<=p and cap4. At p=3 this is its one natural band;
at p>=4 it is the classic-child assignment on the anticipated ambient
range. Distinguish these cases: its actual natural range may be empty
for a classic child, so no BDL conclusion on that empty range is claimed.

After shifting Bl by+1, parent bottom p contains A and ALL Q. Two Q
endpoints bracket the whole p-cup A, giving a(p+2)-cup, beyond its
p+1 limit. At p=2, parent middle also contains the full(p+3)-cup S
and exceeds its p+2 limit. The child inequalities do not bound those
new mixed chains. Nevertheless X has the explicit ordinary partition

  bottom: A plus last Q; middle: Q minus last Q; top: S.

Its profiles are(p+1,2),(2,3),(p+3,2), exactly within the parent
limits. Consequently neither PSL nor BDL is refuted. ∎

There are also compatible child choices on the anticipated AMBIENT ranges.
Put A plus first S in R band p, the remaining R points in p+1;
put last Q in Bl band p-1, all other Bl points in p. Every child cell
meets its budget p+3 bounds. The shifted parent bottom is A plus last
Q plus first S, with cup<=p+1,cap<=3. Its middle is Q minus last Q
plus S minus first S, with cup p+2,cap3. Top is empty. At p=2 these
are genuine NATURAL child partitions. At p>=3 Bl band p can exceed
its actual natural upper endpoint2; this ambient/natural distinction
cannot be silently discarded in a proposed strong-budget induction.
No general compatible-child selection theorem is proved here.

Diagnostic180539-d981d2 checks p2/n11 completely by all-triple subset
metrics and independent all-quad strong maxima,0.005814s/12MiB. Replay
180727-cff0e9 additionally checks the compatible natural child maps and
their parent,0.006715s/12MiB, pascal-band-gluing-v3.json. Source v1/v2
and outputs are preserved. The initial180423-816a21 failed before its
output on an EXTRA parent-core assertion: cap-number retention does not
preserve the maximum-cap family. The relevant B core is(0,5), while
parent core is(3,5) due to new maxcap(3,4,6,7). The exact ROOT inputs
and both obstructions were retained in the corrected replay. No SAT,
new coloring search, PSL refutation or Lean receipt is claimed.

Dedup search `es search 'Pascal split bands union shifted compatibility'`
found no matches. This explains why a numerical Pascal argument, even
if proved generally, needs an additional compatibility theorem to supply
the particular BDL bands. It does not assume that the coordinator's FULL
word-label notion follows by this automatic union operation.

## 62. Some fixed Pascal splits cannot glue ANY natural child witnesses

The scope distinction in section61 is substantive. In that SAME uniform
family at p=3,beta4,s7,alpha6, the red and blue profiles are

  R: cup5,cap3,strong5; Bl: cup3,cap4,strong4.

Both satisfy the Pascal strong bound6, with cap(R)<=3,cup(Bl)<=5.
At child budget6, R's natural bands are3,4 and Bl has exactly band2.
Thus EVERY natural Bl partition places all Q and its single S point z
into parentbottom3 after shifting. There is NO natural R partition whose
shifted union with it is valid, even when R's witness can be chosen freely.

Proof: if an A point enters R band4, that cell's cap bound is2. Two S
points in it would form a cap3 together with that earlier lower A point.
Thus at most one of the FIVE red S points is upper. At least four of
them plus blue z enter parentbottom3: a5-cup violates its cup limit4.
If no A point is upper, all three A points are bottom. The first/last
Q points bracket them and form another5-cup in parentbottom3. These
are exhaustive alternatives, independent of the other child constraints. ∎

This is a counterexample ONLY to the statement that an arbitrary fixed
valid PSL split admits gluing of NATURAL child BDL partitions. It does
not refute PSL, BDL, or existence of another split. It occurs at a literal
DS hard root, while the PSL cut itself is not asserted deep below. In
particular it does not invalidate the closed one-band CHILD cases for a
DS root; those use the DS mixed-chain law, absent for this Pascal cut.

The repair from section61 still works on AMBIENT child ranges: use R
band3 for A plus first S, R band4 for its other S points; use Bl band2
for last Q, Bl band3 for its other points. The blue band3 exceeds its
actual natural upper endpoint2, but fits the parent-derived target
range2..4 with child bounds cup<=j+1,cap<=6-j. Their shifted parent
has bottom/middle/top profiles(4,3),(5,3),(0,0), valid on3..5. Hence
the failure is the strength of the chosen child conclusion, not lack
of a parent partition or numerical impossibility.

More generally at every p>=3, keeping ALL Bl=Q union{z} in its single
classic fitting child band p-1 forces parentbottom p. The same two-case
argument makes the union fail: either an upper A permits at most one
upper red S, putting at least p+2 S points bottom, or the whole A is
bottom and Q brackets its p-cup. At p=3 that one cell is FORCED by the
actual BDL natural range. For p>=4 Bl is classic and its natural range
can be empty; no natural BDL invocation is claimed there. This uniform
one-cell mechanism is the explanation; no further parameters are tested.

Diagnostic182312-e38782 completed0.077168s/12MiB, natural-pascal-trap.json.
It independently checks all input chain/strong maxima, B/parent cores,
the DS tree recurrence, and ALL256 red binary maps. All66 valid natural
maps have an explicit forbidden parent5-cup;190 are invalid child maps.
Every ambient repair cell and its derived shifted parent is revalidated
against complete all-triple metrics. Source certify_natural_pascal_trap.py
reuses the now-promoted research.triple-metrics kernel, no SAT or coloring
search. This finite certificate supports the direct argument, not a
compiling theorem or BDL existence proof. Dedup search
`es search 'natural Pascal child bands existential gluing'` found no match.

A strong-budget proof of BDL would therefore need compatible AMBIENT
partitions, or a richer label invariant retaining the parent's target
bounds. Ordinary natural-child BDL alone is insufficient even with
optimal witness selection for a fixed PSL cut. No such preserved
compatibility invariant is known. Stop variants of natural-band gluing;
this does not replace or close the exact ROOT obligation in the concise
account.

## 63. Strict strong slack closes BDL uniformly by ordinary composition

Fix s>=1. If X is decomposable, sigma(X)<=s-1, and
c(X)+d(X)>=s+1, then X has the BDL partition at budget s. This
is a general paper consequence of DS; it is not a proof at sigma=s.
The search `band decomposition strict strong slack` returned no harness
hits. No Lean statement is registered or formalized before the complete
BDL paper proof, as required by the trial brief.

Use size induction at this fixed s. Write alpha=c(X),beta=d(X),
l=s-beta,h=alpha-1. If alpha+beta=s+1, the whole set fits band
alpha-1. Otherwise alpha+beta>=s+2 and choose any root X=A<<B.
Its profiles p,q,r,t satisfy

  p+t<=sigma(X)<=s-1.

Every child has the same strict strong slack. A classic child, whose
cup and cap sum is<=s, fits a single indicated band. A nonclassic
child has an intrinsic partition by the size IH.

If alpha>p and beta>t, separate the child bands exactly as follows.
Nonclassic A keeps[s-q,p-1]; classic A uses
j_A=max(p-1,l). Nonclassic B keeps[s-t,r-1]; classic B uses
j_B=min(s-t,h). The intrinsic ranges are inside[l,h]. For classic
A, both p-1 and l are<=s-q and strictly<s-t, so its cup/cap
bounds hold and its label lies below B's intrinsic range. For classic
B, both s-t and h are>=r-1 and>=p, so its bounds hold and its
label lies above A's intrinsic range. If both are classic, j_A<j_B:
when j_A=p-1 use j_B>=p; otherwise j_A=l, and both s-t,h are
at least l+1. Thus each resulting band contains only one child.

If beta=t, strict slack gives p<=l-1. A is classic since q<=t.
Every mixed cup meeting A has at most p+2<=l+1 points, whereas
alpha>=l+2. Consequently r=alpha. B's cup+cap sum is therefore
alpha+beta>=s+2, and its IH partition has exactly the parent range.
Assign all A to B's bottom l. Its cup number is at most
max(c(B_l),p+2)<=l+1. Its cap number is at most beta because it
is a subset of X. Other bands stay valid. The case alpha=p is dual:
q=beta, t<=s-p-1, and assign all B to A's top h=alpha-1;
mixed caps have at most t+2<=s-h points. Both maxima cannot be
retained, because alpha+beta=p+t<=s-1. These cases exhaust every
root and complete the induction. No endpoint fact or core selection is
needed. ∎

This explains the obstruction rather than removing the exact-budget gap.
Any BDL counterexample must have sigma(X)=s. At a tight root the
join p+beta=s is attained, so there is precisely no spare unit for the
two-sided endpoint cup. The strict-slack theorem does not supply the
stronger compatible AMBIENT maps needed by section62's PSL split; that
split is not a DS root, and its natural maps already fail despite slack.

The explicit recursion is being audited by check_strict_strong_slack.py.
It reuses decomposable.coloring-enumeration, decomposable.root-cuts and
research.triple-metrics, with complete triples/quadruples and no SAT.
Each applicable budget and each full-set root is covered at the declared
size. Pilot183828-3a6df1 is queued/running; no result is claimed yet.
Pilot183828-3a6df1 subsequently passed0.001778542s/7MiB, covering
12 class members15 budgets8 forced roots, with separation only. A
conservative n6 extrapolation from state/subset/quadruple growth was~7s.
Follow-up190244-6260d2 actually passed0.206465975s/8MiB: all792 class
members1491 budgets904 forced full roots, including72 retained-cap and
60 retained-cup slack calls. Every recursive cell is checked by all triples
and every strength by all quadruples. All constructor clauses now have
diagnostic coverage, so further confirmation sweeps are stopped. These
checks support the uniform induction; they do not give Lean theorem credit.

## 64. The root implication graph has at most four components and four roots

This is a new paper explanation of the root graph, valid for ANY complete
ordered triple coloring, without one-change or decomposition. Searches
`implication SCC transversal strong middle determined` and
`strong set implication graph four components root cuts` returned no
harness hits. It sharpens section39's width-two bound, but it does not
resolve the partition compatibility inside a hard root.

Recall that a cup triple directs each outer point to its middle, and a
cap directs its middle to each outer point. For i<j<k<l, if
chi(i,j,k) differs from chi(i,j,l), the two triples give both i->j
and j->i. Hence i,j lie in the same SCC. If chi(i,k,l) differs
from chi(j,k,l), they give both k->l and l->k, so k,l share
an SCC. Therefore ANY set containing at most one vertex from each SCC
satisfies both strong equalities on every quadruple. It is a strong set.
In particular, the number r of SCCs is at most the strong number.

Choose one representative of each component and order them
v0<...<v_(r-1). In this strong transversal every triple's color depends
only on its middle representative. Indeed, the first strong equality
moves a triple's right endpoint to v_(r-1), and the second moves its
left endpoint to v0. For each interior representative vj write
f(j)=chi(v0,vj,v_(r-1)). If two interior representatives vj<vk
both have cup color, use an earlier representative a and a later b.
Triple(a,vj,vk) gives vk->vj and triple(vj,vk,b) gives vj->vk.
They would be in the same SCC, contrary to their selection. Two interior
cap representatives likewise give both arrows in the reverse directions.
There is thus at most one cup and one cap interior representative. Hence
r<=4; r<=2 is immediate when there are no interior representatives.

At r=4 the two interior colors must differ. The cap interior component
points to both outer components, and both outer components point to the
cup interior component. Thus the full condensation contains a four-point
diamond. Its proper nonempty successor-closed sets are exactly: the cup
sink alone, that sink with either outer component, and the sink with both
outer components. Further arrows can only remove choices, so there are
at most four roots. At r=3 the representative triple gives a fork,
with at most three proper nonempty successor-closed sets; at r=2 there
are at most two, and r<=1 has none. Section39's root biconditional then
gives at most FOUR valid deep-below root cuts for every complete coloring.
The bound is sharp: on four points take cup triples012,013 and cap
triples023,123 (lexicographic mask3). The four lower parts are
{1},{0,1},{1,3},{0,1,3}. ∎

Also, any non-singleton SCC is comparable with every other SCC. Choose
two of its vertices and one from the other component; their triple gives
an arrow between the two components, whatever its color or spatial order.
Thus incomparable components must both be singletons.

The mathematical gain is a constant-size outer quotient, not a BDL
construction: one SCC can contain arbitrarily many points, and restricting
to it removes external paths and exposes a different internal root graph.
The retained n8 example in section39 already has only two roots, one hard
retained-cap and one hard retained-cup, with a six-point middle component.
Its ordinary BDL exists, but neither alternative root removes the positional
step. No root-choice retry, k-only partition state or compiling theorem is
inferred from the four-component bound. Library regression review is due
before changing the promoted root-cut documentation/tests.
That regression184930-602e54 subsequently passed40 root/metric/catalog
tests2.20s/36MiB, including EVERY SCC transversal and direct root of every
arbitrary complete coloring through n5, plus the sharp diamond fixture.
Documentation/fixture/test refinement leaves algorithm and API unchanged;
its exact-path local commit is in progress, not a theorem receipt.

## 65. Every smallest BDL counterexample has only one or two hard roots

Assume a counterexample to BDL at fixed s exists and choose one of least
cardinality. All proper induced subsets then have their BDL partitions
when nonclassic, or fit a classical band when needed. Sections1-7 and
the cap3 boundary consequently close any root except a tight retained-cap
root or its tight retained-cup dual. Section63 also gives sigma(X)=s.
Its cup and cap are both>=4, alpha+beta>=s+3, and s>=5.
The search `tight retained root unique sink source SCC minimal counterexample`
returned no harness hits. This is a conditional structural account of a
hypothetical counterexample, not a BDL existence proof.

In a hard retained-cap root X=A<<B, every maximum beta-cap of B
surrounds ALL A. Choose B endpoints to the left and right of A. For
any a<a' in A, the surrounding mixed cups give a'->a and a->a'.
Thus A lies in one SCC. Root successor closure forbids any path from A
to B, so A is exactly that component. If A has at least two points,
any b in B and two A points give an arrow b->A: b is either an
outer endpoint of a mixed cup or the middle of a mixed cap. If A is a
singleton, choose a B point on the other side of it; their mixed cup
again sends b to A. Every B vertex therefore reaches A. It is the
UNIQUE sink SCC. The dual hard retained-cup root has B equal to the
UNIQUE source SCC. There is at most one hard root of each orientation.

All roots of the minimal counterexample must be hard, so there are at
most two. A condensation with r components has at least r-1 proper
nonempty successor-closed sets, by terminal segments of any topological
ordering. Hence r<=3. A three-element nonchain has at least three such
sets, excluding it. Two incomparable components would both be singletons
by section64, giving only two points, which is not a counterexample.
There must be at least two components because X is decomposable and
nontrivial. Thus its condensation is a TOTAL CHAIN of length two or three.

At length two there is one root and it is one exact ROOT obligation or
its dual. At length three write the components, from sink to source,
D,M,E. The only roots are D<<(M union E) and (D union M)<<E.
The first must be hard retained-cap, since a retained-cup root's upper
part is one SCC; the second must be hard retained-cup, since a retained-
cap root's lower part is one SCC. Put

  p=s-beta=c(D)>=1, t=s-alpha=d(E)>=1,
  m=alpha+beta-s>=3.

Both D and E are classic at budget s. The middle M has EXACT profiles
c(M)=alpha,d(M)=beta. To see the cup equality, the retained-cup root
has c(D union M)=alpha, while its induced split D<<M has mixed cup
bound p+2<alpha and c(D)=p; so the maximum comes from M. Dually
d(M union E)=beta, the split M<<E has mixed cap bound t+2<beta,
and d(E)=t, so d(M)=beta. The actual two root cuts retain their
sibling-span hypotheses: maximum M beta-caps enclose D, and maximum
M alpha-cups enclose E. No simultaneous band normalization is inferred.

This is the exact reason alternative-root strategies can stall: a minimal
failure has one hard root, or one hard root of each orientation, with
no third choice. The retained section39 n8 example already has this
three-component chain and exact middle profiles, but HAS an ordinary BDL
partition. Thus the shape alone does not refute BDL. It identifies an
outer context around a still complicated middle component; restricting
to that component changes its implication graph. Its simultaneous band
compatibility remains the unresolved mathematics, not an easier statement
proved by this classification. No further root-choice sweeps are justified.

## 66. Exact graph composition: sibling extrema add pair arrows

For a root X=A<<B let G_S be the implication graph of the induced
coloring on S, with reflexive loops included. Write a-=min(A),a+=max(A),
b-=min(B),b+=max(B). Then the adjacency of G_X is EXACTLY G_A and
G_B plus these edges, for every ordered pair within the indicated part:

- a1<a2 in A: add a2->a1 if b-<a1; add a1->a2 if a2<b+.
- b1<b2 in B: add b1->b2 if a-<b1; add b2->b1 if b2<a+.
- For each b in B,a in A, add b->a unless {a,b} is the pair of
  global first and global last points. No cross arrow goes A->B.

The search `deep below implication graph context radial arrows extrema`
returned no match. This formula is an exact context interpretation, not
a statement about BDL partitions or a new execution helper.

For the first line, a B point outside the A pair makes a mixed cup.
If B is left, its middle a1 receives a2; if B is right, middle a2
receives a1. A B point inside makes a mixed cap and contributes no
internal A edge. For the second line, an A point outside the B pair
makes a mixed cap: the nearer B point sends an arrow to the farther.
An A point inside makes a mixed cup and no internal B arrow. Existence
of the required exterior point is exactly the displayed extremum test.

Every mixed triple's cross arrows go B->A by the root rule. Conversely,
if a cross pair is not the two global extrema, choose a third point
outside its closed spatial interval. One of a,b is then the triple's
middle. If it is a, the mixed cup sends b->a; if it is b, the mixed
cap does so. A triple containing both global extrema has neither as
its middle and contributes no arrow between them. This proves the third
line and exhausts all possible added edges. The omitted direct arrow
may still be supplied by an internal path; no missing reachability is
claimed. ∎

In a hard retained-cap root, b-<a-<=a+<b+. Both internal A arrows
are present for EVERY pair, making A one SCC. A contains no global
extremum, so every B->A cross arrow is present directly. Its unique-sink
description in section65 follows immediately. The upper graph's new
internal arrows depend ONLY on a-,a+, not on A's internal coloring.
The dual gives the unique source for a hard retained-cup sibling.

This explains how a child can be decomposable while forming one large
SCC in its parent: an outside sibling adds internal arrows between child
points, merging child components. Removing that sibling removes those
arrows, exposing new roots. Merely contracting the global<=4-component
graph consequently loses the recursive context. Also, extrema alone
do NOT determine the band insertion test: section58 requires the actual
cup rank of A inside the proposed bottom span. Thus the graph transform
does not justify replacing arbitrary A by one selected p-cup.

The retained section39 n8 root A={2} illustrates the exact directions:
mixed cap012 contributes1->0 on B's left; mixed cap234 contributes
3->4 on its right; mixed cup023 gives0,3->2 and no internal B arrow.
All B vertices directly reach2 because both global extrema lie in B.
These follow from its already-certified DS root, not a new case search.
No new ad hoc algorithm is promoted for a one-use formula. The unresolved
step remains choosing compatible bands through the context, not enumerating
roots or representing the uncolored implication graph.

A universal simplification is visible even before choosing a root. For
x<y, a direct x->y arrow is supplied by a cup xyz with z>y or a
cap wxy with w<x; the reverse is supplied by a right cap or a left
cup. Every pair other than the two global extrema has at least one such
exterior witness. Thus the graph is semicomplete except for that one
missing pair. Incomparable SCCs, if any, are exactly singleton global-
endpoint components. Its condensation is a chain with at most this one
incomparable endpoint pair, rather than an arbitrary width-two order.
Combined with section64's component bound this explains all root options.
It still omits the chain-placement conditions of a colored band partition.

## 67. One-unit endpoint lowering of the canonical slack map is false

Section63 gives a fresh partition at budget S=s+1 whenever sigma(X)<=s.
Its bands run from s+1-beta to alpha-1. The exact-budget target adds the
new bottom s-beta and lowers every retained band's cap limit by one.
This suggests a global Pascal refinement rather than supplied-child repair:
for each old band j whose cap equals S-j, send first OR last points F_j
of all its maximum caps to j-1 and keep its complement G_j at j.
For noncritical bands send nothing. The endpoint fact gives
c(F_j)<=j,d(F_j)<=s+1-j,c(G_j)<=j+1,d(G_j)<=s-j.
Each piece fits; the remaining assertion is compatibility of
G_j union F_(j+1). There was no proof of that assertion.

The precise hypothesis that the DETERMINISTIC section63 construction always
admits these first/last choices is FALSE on the already retained n11 tight
Pascal root of sections61-62. Here A={2,3} is a two-cup, Q={0,1,4,5}
a four-cap, S={6,7,8,9,10} a five-cup, and X=A<<(Q<<S).
It has c5,d4,sigma6; ordinary BDL is explicitly valid. The canonical
old-budget7 map returned by the existing root-order constructor is

  old3={2,3,5}, profile(3,2);
  old4={0,1,4,6,7,8,9,10}, profile(5,3).

Only old4 is critical. Its first maximum3-cap endpoints are{0,1,4};
its last endpoints are{4,7,8,9,10}. Sending the first set into band3
creates the four-cap(0,1,4,5); sending the last creates(3,5,9,10).
Both violate target band3's cap limit3. This exhausts ALL two choices.
The split bounds still hold individually, so the failure is the join.

A valid ordinary target map moves ALL noncritical old3 into the NEW
bottom2, sends first endpoints to middle3, and leaves S top4. Its
profiles are(3,2),(2,3),(5,2). Thus cap-endpoint transfers alone miss
a necessary release of the receiving band. This refutes only that fresh
canonical mechanism, not BDL, all possible slack witnesses, arbitrary cap
hitting sets, or every global budget-reduction argument. No fitted
endpoint-only variants or new parameter confirmations are commissioned.

Dedup search `es search 'one spare strong budget Pascal cell refinement
band decomposition'` found no match. Probe reuses the section63 constructor
through an optional output callback and the promoted exact metrics/root
algorithms; original source preserved as check_strict_strong_slack.v1.py.
Pilot191410-51e2c9: n8 existing two-hard-root example had one valid choice,
0.002824006s/7MiB. Fixed-corpus191430-632b5c: n11 failure after2/5 retained
cases,0.012479452s/9MiB,unit-budget-corpus.json. Remaining n13 isolation,
n13 natural trap and n14 frozen examples were NOT COVERED for this
mechanism; their verdicts remain unclassified. Diagnostic only, no Lean
credit. Independent direct A<<(Q<<S) replay191726-370f1c PASSED
0.002037982s/7MiB: all165 triples match, all330one-change quads hold,
the exact c5/d4/sigma6 witnesses/exclusions and all maximum3-cap
endpoints/blockers/ordinary repair validate without the metric/root
algorithms. Source certify_unit_budget_failure.py; durable result
unit-budget-failure-certificate.json. This is diagnostic, not Lean credit.

## 68. Core conservation closes a general ROOT case by second-band insertion

At X=A<<B put c(X)=c(B)=alpha,d(X)=d(B)=beta,sigma(X)<=s,
l=s-beta,m=alpha+beta-s>=3. DS gives p=c(A)<=l. Let
(L_B,R_B) be the maximum-beta-cap core of B, and (L_X,R_X) that
of X. Every A point is strictly inside (L_B,R_B).

Every maximum alpha-cup of X is entirely in B: any cup meeting A has
at most p+2<=l+2<alpha points. A NEW maximum beta-cap of X meets A.
If mixed, all its A points are endpoints by DS; if pure A, both extrema
lie in A. Hence its first endpoint a lies in A, giving
L_X>=a>L_B, or its last endpoint a lies in A, giving R_X<=a<R_B.
Old maximum B caps remain maximum in X, so L_X>=L_B,R_X<=R_B.
It follows that these statements are equivalent:

  (L_X,R_X)=(L_B,R_B);
  every maximum beta-cap of X stays entirely in B;
  the entire maximum beta-cap family is unchanged.

This is stronger information than unchanged numerical cap beta. Its proof
uses the actual root, not an arbitrary union or a supplied coloring map.

Under core conservation, ANY valid supplied B partition lifts to X by
putting ALL A into the SECOND band j=l+1. Cups in that band have length
at most max(c(B_j),p+2)<=l+2=j+1. A forbidden beta-cap there would
either be entirely in B_j, contradicting its cap bound beta-1, or meet A,
contradicting maximum-cap-family conservation. Thus its cap is<=beta-1
=s-j. The second band exists because m>=3. All other bands are untouched.
No positioning or cyclic repair is needed in this case. The cup/cap dual
adds an upper context to the PENULTIMATE band when the cup core is unchanged.
This is a uniform closing construction for every band demand, not a small
parameter statement. It is not a new compiling theorem.

Consequently the exact ROOT residual can require STRICT cap-core contraction,
equivalently at least one parent maximum beta-cap meeting A. Together with
the earlier closing cases this restricted residual is still conditionally
equivalent to full BDL. The literal14 frozen example and n11 Pascal example
contract the core, so their failed arbitrary-supply lifts remain relevant.
Contracting ROOT is still unproved; the witness supplies a tight regional
cap/endpoint event but no compatible choice of new bands has been proved.

Along a constant-profile context chain, a conserved-core lower edge preserves
BOTH maximum-chain families (cups automatically, caps by the equivalence),
and the upper edge has the dual property. Any stretch conserving both cores
can therefore be inserted through any supplied base map, placing each lower
context into second band and each upper context into penultimate. At three
bands these are the SAME middle band, so all contexts enter it together.
This closes the arbitrary-depth conservation stretches; only core-changing
events remain on the contracted demand-skeleton edges. Those events can
still occur repeatedly and are not bounded here. The structural explanation
is why conservation is easy and creation of maximum chains is the remaining
compatibility problem, not a claimed proof of general BDL.

Dedup searches `unchanged cap cup core constant profile middle band` and
`cap core unchanged second band` found no matches. The fixed-domain semantic
audit is prepared in audit_core_conservation.py, reusing promoted metrics,
root cuts, complete class enumeration and retained binary-label inputs.
It asks whether core contraction is EXACTLY new maximum-cap creation and
checks EVERY eligible second-band subset union at conserved roots. A failure
would invalidate this paper step; a pass supports the conditional step only.
Pilot/full execution is pending; no diagnostic result claimed yet.

Pilot192734-f8bd3c subsequently passed0.001858112s/8MiB:12complete n<=4
members30roots,4retained-cap equivalences, all contracting. It alone did
not cover conservation/lifting. Same-source full192948-6ebf40 passed
0.337776305s/10MiB: all792n<=6 members plus5retainedfixtures,1221roots,
196retained-core equivalences,21conserved/175contracting. The n12 long
spine has the same old/new core(0,7) at a tight s7 root; all1890eligible
upper second-band subsets lift. Known hard roots contract: n8(1,7)->(2,7),
n11(0,5)->(3,5), n14(5,8)->(6,6). Durable core-conservation-n6-fixed.json.
These checks support the conditional mechanism, not full BDL or a new
Lean receipt. No further conservation confirmation cases are planned.

## 69. The remaining core event is exactly a regional cap threshold

For the retained-cap ROOT with beta>=4, let a0=min(A),a1=max(A),
B_left=B intersect(-infinity,a1),B_right=B intersect(a0,infinity),
and B_inside=B intersect(a0,a1). If A is a singleton the last pair
condition below is omitted. DS lists EVERY beta-cap meeting A:

1. a pure beta-cap of A;
2. one A first endpoint plus a(beta-1)-cap of B to its right;
3. one A last endpoint plus a(beta-1)-cap of B to its left;
4. two A endpoints bracketing a(beta-2)-cap of B.

The singleton endpoint threshold is largest at a0 for the suffix and
at a1 for the prefix; the pair threshold is largest at(a0,a1).
Conversely each displayed threshold constructs a parent beta-cap using
those A extrema. Because cap(X)=beta, these thresholds cannot be larger
than beta,beta-1,beta-1,beta-2 respectively. Therefore conservation is
EXACTLY

  cap(A)<=beta-1;
  cap(B_left)<=beta-2 and cap(B_right)<=beta-2;
  if |A|>=2, cap(B_inside)<=beta-3.

Contracting ROOT means at least one of those bounds is tight one unit
higher. This explains the spare unit used by second-band insertion: its
cap limit is beta-1. A new maximum cap can consume that unit at one of
the actual sibling-window interfaces. This is a direct DS proof, not
a rule fitted to diagnostic data and not a compatible construction for
the tight thresholds. No new computation is commissioned for it.

At p1 the sibling is necessarily one point a. Pure/pair cases disappear.
Strict contraction means the B prefix or suffix at a has cap beta-1.
The exact parent endpoints must include ALL new-cap extrema. Let P be
the family of(beta-1)-caps in B before a, Q the family after a. Then

  L_X=max(L_B, a if Q nonempty, first(D) for D in P);
  R_X=min(R_B, a if P nonempty, last(D) for D in Q).

Empty terms are omitted. Both families nonempty closes the core to(a,a),
as in the literal14 example. If only one family is nonempty, the exact
formula still includes the opposite core edge through that family's B
endpoint; it is not assumed unchanged here. An earlier
one-edge-only formula omitted these extrema and was corrected during
research27; no computed counterexample to the tighter hard-p1 domain is
claimed. No BDL inference follows from this numerical classification alone.

There is a general stopping fact for a constant-profile context chain.
Once the cap core closes, no later LOWER sibling can be inserted while
retaining alpha,beta: every such sibling would have to lie strictly
inside that closed core. UPPER siblings preserve all maximum beta-caps
because their cap<=s-alpha<=beta-3 makes every mixed cap shorter than
beta; hence they cannot reopen it. The dual holds for a closed cup core.
After both close no further constant-profile context can appear. Open
cores may still contract repeatedly; no uniform event-count or full
band construction is asserted.

Dedup search `deep below new maximum cap regional prefix suffix span`
found no match. This records the mathematical meaning of the still-open
case, rather than commissioning more local transfers. Q17's existing
finite tower records the near-maximum regional cap regrowth; its shared
base-context truth remains a separate unproved claim, not assumed here.

## 70. The shared tower rule still needs admission and terminal truth

The primary Q17 source defines a finite side context c=(F,H,bottom,top)
and S(Y,c), its valid band maps. At a classic-sibling/wide-carrier node
the keep/reserve/lift menu proposes child contexts c'. Its exact closure
predicate is

  E(Y,c;C,c') := for EVERY P in S(C,c'),
                SOME placement of sibling Z extends P into S(Y,c).

The greedy "NOORACLE" setting chooses the first E that holds, including
vacuously empty child contexts. It removes the nonemptiness condition on
S(C,c'), not the semantic extension test. Enumeration source realis.py
computes E with all parent maps/restrictions; SAT source bigrule.py uses
CEGAR for the same universal-existential predicate. Therefore this is a
determined semantic procedure, not a syntactic constructor justified by
local DS rules alone. No critique of its diagnostic finite calculations
or a BDL refutation follows from that distinction.

For a paper induction one must prove: soundness of wide-wide inheritance;
at least one closing option at EVERY reached nonterminal menu node;
and nonempty classic/two-band terminal contexts. Terminal truth alone
does not exclude a prior NO OPTION CLOSES deadend. Both sources contain
that branch. If S(Y,c) is empty and every proposed child context is
nonempty, no E holds and no base is reached; a terminal-only condition
would miss it. Shared notes call concatenation keep closure computation-
only, reserve hand-proved. No complete source-pinned paper proof was found.
The source audit uses the actual exact predicates and states no new theorem.

During a constant-profile context stretch, all outer lower siblings lie
strictly inside the current carrier's max-cap core, and upper contexts
preserve that cap family. An inherited cut at an outer kept sibling thus
retains this geometry. Profile loss at an inner/base node can invalidate
that relation; it is a meaningful place to inspect the terminal proof.
This observation does not prove every tower context is feasible.

Before any new case, the declared question is whether the exact greedy
configuration succeeds on the SIX retained R25 labels (root-choice,
Pascal, isolation, natural trap, frozen literal14, long-spine), without
new size/sample generation. A failure refutes that selected procedure,
not BDL. A pass matters only through the actual reached base constraints.
At each intrinsic two-band base the FOUR standard endpoint maps are
compared with its extra context. If all four fail while a SAT witness
exists, endpoint-only base truth is insufficient; no fitted endpoint
variants follow. This diagnoses the base, not a new global peeling rule.

Five Q17 modules are copied unchanged under tower_snapshot/ with
SHA256SUMS; primary files/jobs stay untouched. The small adapter
check_tower_retained_contexts.py fixes all rule options, records traces/
bases and validates root/base metrics, every resulting cell and every
raw side/tower condition with the promoted complete-triple evaluator.
Progress includes cases done/total and SAT-call checkpoints. Its pilot
and full execution are pending; no new diagnostic result is claimed.

Pilot194304-16414a subsequently passed0.005986856s/11MiB,12SATcalls.
Full194527-c9d20f passed all SIX retained labels,0.255000361s/13MiB.
Every root/base model and raw context validated; no deadend/base failure.
The literal14 base has c4/d3/sigma5 and ALL FOUR standard natural
endpoint witnesses fail its inherited context. The procedure succeeds
using an ambient three-band map. Durable tower-retained-corpus.json;
source-pinned diagnostic evidence only, not a paper induction proof.

## 71. An actual reached two-band base needs its ambient third band

In the literal14 input the greedy trace keeps the root lower singleton6,
then uses concatenation keep/either with sibling{2,3,5}. Its remaining
base has global points(0,1,4,7,8,9,10,11,12,13), with intrinsic
c=4,d=3,sigma=5,k=6. Natural bands are2,3; inherited ambient bands
are1,2,3. Write L,M,T for these ambient cells, and number base points
locally0,...,9. The exact context is the disjunction

  OR1: L>=3; every one-,two-,three-cap in M starts at<=1;
  OR2: L>=3,M>=3; every three-cap in M starts at<=1.

There is no top condition. Band bounds are(cup,cap)=(2,4),(3,3),(4,2).
The whole base cap is3, so L's cup<=2 makes it a cap of size<=3.
The whole base cup is4, so T's cap<=2 makes it a cup of size<=4.
These implications hold also for cells of size<=2 by vacuity.

OR1's one-cap condition puts ALL M into positions0,1, hence|M|<=2.
Thus OR1 cannot fit even ambient maps: |Y|<=3+2+4=9<10.
In OR2, every M point is>=3, so the three-cap condition excludes EVERY
three-cap of M. Therefore M is a cup and its own cup bound gives|M|<=3.
All ten points consequently force |L|=3,|M|=3,|T|=4. The explicit map

  local bands (3,3,3,3,2,2,2,1,1,1)

meets OR2 and every band bound. In particular the extra ambient floor1
is ESSENTIAL: with L empty, OR1 fits<=6 points and OR2<=7. This excludes
EVERY natural two-band map, not only four chosen endpoint witnesses.
Ordinary BDL on natural2,3 still holds without the inherited context;
the selected tower procedure and full BDL are not refuted.

Independent direct replay195147-9e13a6 passed0.002994537993799895s/8MiB.
It imports no SAT/tower/metric implementation: first-differing-bit colors,
all120triples,210one-change quads, c4/d3/sigma5 witnesses and next-size
exclusions, exact contexts and every recorded map are checked directly.
Strong5 witness local(0,1,2,3,6). Cardinality bounds above are an explicit
paper argument, not an inferred exhaustive-count theorem. Durable source
certify_tower_ambient_base.py and tower-ambient-base-certificate.json.
No Lean credit and no additional base-case sweep follows. A general
terminal proof must construct compatible AMBIENT maps; natural endpoint
splitting cannot supply it. Option admission and inheritance also remain
unproved, as section70 explains.

## 72. Reachable-range invariants justify mathematical wide-wide inheritance

This closes a mathematical SOUNDNESS step, not option admission or terminal
truth. Treat absence of a cut as a SYMBOLIC value distinct from integers.
The literal pinned source uses integer NONE=-99; its source correspondence
is conditional on noncollision, as explained below. Put s=k-1. Every
reached context at Y has the ambient
range invariant

  F<=s-cap(Y), H>=cup(Y)-1.

It holds at the root. Heredity gives cup(C)<=cup(Y),cap(C)<=cap(Y),
so keeping either endpoint preserves it. child_options changes an endpoint
only to the child's corresponding NATURAL endpoint, which also preserves
it. At wide-wide inheritance the changed endpoints are precisely those
natural endpoints. This is a source induction, independent of context truth.

Every reached OR has a fixed range and varies at most ONE of bottom/top;
the other side is identical in all its disjuncts. A non-OR is included.
At a classic-sibling step all_child_options first selects ONE parent
disjunct. Deferred either then varies only the newly facing side, keeping
the other fixed. At a wide-wide step each projection maps one side and
drops the other; mk_or removes duplicate disjuncts. Thus the invariant is
preserved. Arbitrary correlated OR contexts would not have this property.

Now Y=A<<B has both children wide: p+q>=s+2,r+t>=s+2 with
p=cup(A),q=cap(A),r=cup(B),t=cap(B), and p+t<=s. Consequently
r>=p+2,q>=t+2, so the DS bounds and heredity give cup(Y)=r,cap(Y)=q.
The child ranges used by ww_children are

  A:[F,p-1], B:[s-t,H].

They are disjoint because p-1<s-t. Moreover

  F+1<=p-1, s-t<=H-1,

since F<=s-q and p+q>=s+2, and H>=r-1 and r+t>=s+2.
Thus BOTH parent bottom bands F,F+1 belong entirely to A; BOTH top
bands H-1,H entirely to B. No same-band cup/cap mixes children.

Position and tower constraints transfer exactly under gmap: for any gap g,
gmap(C,g)=|{x in C:x<g}|. A child point is before the mapped gap iff its
parent-coordinate point is before g. Every first/last chain point belongs
to its own cell, so the same equivalence applies to all tower cuts.
Hence child A's inherited bottom condition and B's inherited top condition
are exactly the corresponding parent conditions of their combined map.

If only the parent bottom side varies, choose the disjunct witnessed by
A; B meets the identical fixed top side. If only top varies, choose B's
disjunct instead. With neither varying any disjunct works. This proves
that independently valid child maps produce SOME common parent disjunct,
so conjunction of child proofs is sound on these mathematical contexts.
The rectangular invariant is needed: an arbitrary OR coupling bottom1
with top1 and bottom2 with top2 need not synchronize independent choices.

There is a material encoding limit in the literal diagnostic source:
NONE=-99 also equals a genuine left position threshold1-g at gap100,
or a right tower threshold1-t at gap100. to_thr then treats a genuine
cut as absent. gmap can map a noncolliding parent cut into that value.
Thus exact all-n constraint transfer cannot be claimed for the literal
integer encoding without a noncollision condition. Generated cuts at
n<=99 avoid this collision; all retained six n<=14 audits are unaffected.
No actual reached-coloring failure is asserted, and shared source is
unchanged. General mathematical contexts require symbolic absence.

This is a complete conditional paper proof of this one step, under the
accepted DS law and the symbolic version of the pinned menu. No data extrapolation,
new case, Lean statement or receipt. Dedup search `ambient band ranges
wide child disjunction inherited side` found no match. Option admission
and compatible AMBIENT classic/two-band bases remain the tower's missing
general claims; section71 prevents replacing the latter with ordinary
natural endpoint splitting. Contracting ROOT remains open.

## 73. Maximum-core changing events are bounded by charged endpoint chains

Let X0,...,XN be a BOTTOM-UP nested context chain. Each insertion is
Xi=A_i<<X_(i-1) or Xi=X_(i-1)<<U_i. Throughout put
c(Xi)=alpha,d(Xi)=beta,sigma(Xi)<=s and m=alpha+beta-s>=3.
Chain depth itself can be arbitrary, as section53 shows. Nevertheless
there are at most2(beta-1) cap-core changing insertions and at most
2(alpha-1) cup-core changing insertions.

At an upper insertion DS gives cap(U_i)<=s-alpha<=beta-3.
Every mixed cap then has size<=cap(U_i)+2<=beta-1, and pure U_i
caps are shorter still. Thus the entire maximum-beta-cap family stays
in the previous carrier. At a lower insertion, all A_i points lie
strictly inside its old max-cap core; old maximum caps remain maximum.
The core endpoints therefore move monotonically inwards. If it changes,
choose ANY new maximum beta-cap D. By DS, its first or last point lies
in A_i, including the pure-A_i case. Charge the event LEFT if first(D)
is in A_i, RIGHT otherwise. Each event gets exactly one charge.

A left charge a_i has new core L_i>=a_i>old L. Every later inserted
lower sibling lies beyond that new L, so later left charges are spatially
strictly larger. Right charges are spatially strictly decreasing by the
dual endpoint argument. This uses a charged A endpoint; the exact moving
core edge might instead be a B endpoint of another new cap. That distinction
is necessary and is why the first research27 argument was corrected.

Choose an original maximum beta-cap K of X0, with endpoints b0,b1.
Every inserted lower point is strictly between b0,b1, because K remains
maximum throughout. The set {b0} together with ALL left charges is a
whole cap. To check any triple, its outermost inserted charged point is
its RIGHTMOST point, since left charges increase in bottom-up order.
At that lower split the middle point belongs to the old upper carrier,
so DS makes the triple a cap. Triples including b0 obey the same argument.
The right charges together with b1 similarly form a cap: their outermost
inserted point is LEFTMOST. Since the final cap number is beta,

  number(left charges)<=beta-1;
  number(right charges)<=beta-1.

Upper insertions contribute no cap-core event. This proves the asserted
2(beta-1) bound. Cup/cap duality gives2(alpha-1); lower insertions create
no new maximum alpha-cup because cup(A_i)+2<=s-beta+2<alpha.
Thus at most2(alpha+beta-2)<=4s-4 insertions change either maximum core.
This is a uniform paper explanation, not a bound fitted to finite data.

The one-sided bound beta-1 is SHARP in a simple general family. For
beta>=4 set s=beta+1,alpha=4. Let Q be a beta-cap followed by a4-cup C,
with X0=Q<<C. Insert beta-1 singleton lower siblings a1<...<a_(beta-1)
in Q's gap after its first point, with later a_i OUTERMOST. At step i
the prefix is a whole cap of length i (first Q plus earlier singletons),
and the suffix has cap beta-1 (remaining Q, with possible three-point
mixed caps when beta=4). Singleton DS therefore retains cap beta for
i<=beta-1. Cups stay4 and each strong join is1+beta=s.
The new cap starting at a_i followed by remaining Q moves L to a_i.
R stays last Q until the final insertion, when first Q plus all singletons
is a beta-cap ending at a_(beta-1); the core closes there. Charging each
new suffix cap LEFT gives exactly beta-1 charges. Natural bands1,2,3
are explicit: first Q plus all singletons; remaining Q; the4-cup C.
This is not a BDL counterexample or a proof of arbitrary contracting ROOT.

No compression theorem follows from the event count. Conserved inner
stretches can still create NEAR-maximum chains that interact with later
outer contexts. A second-band lift at an inner node need not preserve its
external tower/position demands. Deleting those stretches would discard
that information. The count bounds maximum-core events only; option
admission, ambient base truth and contracting ROOT remain unproved.
Dedup search `cap core change charges monotone endpoints beta minus one`
found no match. A single beta4/n11 family audit is prepared solely to check
ancestry/orientation/sharpness; no larger parameter confirmation is planned.

There is a structural corollary with the SAME limitation. Paper56's demand
defect identity leaves<=2m-1 vertices after contracting zero-defect unary
paths, where m=b_s(X). A zero-defect unary step with positive demand
preserves cup and cap individually: their sum stays fixed and both are
hereditary. The at most2m-1 resulting path stretches of demand>=3
therefore each have<=4s-4 maximum-core events by the argument above.
Hence there are<= (2m-1)(4s-4) such events across those stretches.
Stretches at demand1/2 are excluded from this event bound; their plain
BDL closing constructions do not prove ambient context truth.

This counts positions in the original tree, not vertices in an equivalent
partition problem. It gives no right to contract conserved stretches:
their beta-1 chains can become beta-caps when an outer context is inserted.
The relevant induction state still needs regional nearmaximum-chain
information, not only maximum cores or the numerical skeleton. Thus no
new polynomial kernel, finite-state proof or BDL theorem is claimed.

Fixedbeta4 replay200416-63a3e6 subsequently PASSEDrc0,
0.009859371988568455s/11MiB after shared memory admission delay.
All three intermediate profiles are c4/d4/sigma5; cores are(1,6),
(2,6),(3,3). Charges1,2,3 with original endpoint0 form the four-cap
attaining beta-1 left charges. All330one-change quads and explicit ordinary
bands validate. Durable core-event-chain-certificate.json. Diagnostic
support for the uniform argument only; no Lean receipt or larger sweep.

## 74. Conserved cores and exact maximum families are not extension state

This gives a uniform reason the event bound does not permit deleting a
conserved stretch. Fix beta>=6,s=beta+1,alpha=4. Let Q be a beta-cap
followed by a4-cup C, with Q<<C. Insert an inner lower singleton z in
Q's gap after its third point, making X0=z<<(Q<<C). The prefix cap is3,
the suffix cap is beta-3 (at least3), so every new mixed cap has size
<=max(4,beta-2)<beta. Mixed cups have size<=3. Q and C remain the ONLY
maximum cap and cup; the strong join1+beta makes sigma(X0)=s.

Now insert a lower singleton b in Q's gap after its second point, with
X1=b<<X0. Before b the cap number is2. After b, the Q suffix has
beta-2 points; the inner z can add one endpoint to the part after its
third-Q gap, giving at most beta-2 again. Other mixed caps with C have
size<=4<=beta-2. Thus the entire suffix cap is EXACTLY beta-2.
Every new cap at b has size<=beta-1; cups stay4, sigma stayss. Consequently
X0 and X1 have the SAME c,d,sigma and EXACT maximum cup/cap families:
the single sets C,Q. This is a genuinely conserved maximum-family step,
not merely equal numerical extrema.

Place an outer lower singleton a immediately before b in the same gap.
In X1's suffix after a, b followed by the Q suffix is a(beta-1)-cap.
Adding a produces a new beta-cap

  (a,b,Q points after the second Q point).

Hence the outer root a<<X1 contracts the cap core. If b is DELETED,
the suffix after a has only cap beta-2, and the prefix cap2; a<<X0
creates no new maximum cap and conserves the core. All four configurations
retain c4/dbeta/sigma(beta+1); their maximum cups are always just C.
Therefore c,d,sigma and even the full maximum-chain families fail to
determine the response to this same outer insertion. The missing state is
the regional NEAR-maximum cap created by the conserved b.

This also appears directly in bands1,2,3. Start with first Q in bottom,
remaining Q plus z in middle, C in top. Its conserved second-band lift
adds b to middle and remains valid. Adding a to that same middle creates
the forbidden beta-cap displayed above. Without b, adding a to middle
would remain valid by conservation. Ordinary full BDL nevertheless holds:
put a with first Q in bottom, keep b/z/remaining Q in middle and C in top.
Bottom is a pair; middle cap<=beta-1 and cup<=3; top cup4/cap2 fits.
Thus this is a failure of maximum-family-only deletion/extension state,
not of BDL, contracting ROOT, or arbitrary compatible recoloring.

Dedup/library searches cover conserved core and regional chain extension;
research.context-extension only computes marker-side extension lengths,
not complete triple families. The fixed beta6/n13 replay reuses the
ancestor constructor/cup-cap generators and promoted exact all-triple/
quad metrics. It checks SAME full profiles/maxfamilies, both outer cores,
the beta-1/beta cap, conserved/deleted lifts, naive overflow and ordinary
repair. Source certify_core_conservation_regrowth.py. No execution or
diagnostic result yet; no larger parameter confirmation is planned.

Fixedbeta6 replay201604-fa2c8b subsequently PASSEDrc0,
0.04214433900779113s/12MiB. All four grounds have c4/d6/sigma7.
Conserved b preserves exactly the unique Q/C maximum-chain families.
Outer core without b is(0,8), with b(2,8); regional cap increases4->5,
and (3,4,6,7,8) extends to maximum(2,3,4,6,7,8). Naive middle cap6
overflows5; putting a2 with q0 in bottom repairs ordinary BDL. All715
one-change quads, every root mixed triple and explicit maps validate.
Durable core-conservation-regrowth-certificate.json. Diagnostic support
for the uniform negative state claim, not a Lean receipt/BDL result.
No larger confirmation or fitted maximum-family variant follows.

## 75. Natural-band admissibility is neither a matroid nor a submodular rank

A generic matroid partition or rank-exchange theorem cannot supply the
missing compatible recoloring. This fails inside the actual natural
bottom band of a three-band BDL instance, not merely for unrelated bounds.

Fix h>=2. Put a whole h-cup I in one spatial gap of a whole(h+1)-cap J,
with at least one J point on each side, and take Y=I<<J. Then
c(Y)=h+2 (I and both J endpoints), d(Y)=h+1, and sigma(Y)=2h+1.
The mixed strong join I union J attains the last value. Put a new lower
singleton w before every point and form X={w}<<Y. We have
c(X)=d(X)=h+2 and sigma(X)=2h+1=s: w extends J to an(h+2)-cap,
but its mixed cups have at most two points and its strong root join
has only h+2 points. Thus c(X)+d(X)-s=3 and the natural bottom index
is j=s-d(X)=h-1. Its admissible subsets have cup<=h and cap<=h+2.

Both I and J are admissible, with |I|=h<|J|=h+1. Every z in J is
outside I's span, so I union {z} is a whole(h+1)-cup and is inadmissible.
This violates matroid augmentation for these exact natural-band bounds.
The same construction works for every h>=2; no parameter sweep is needed.

The maximum size of an admissible subset is also not a submodular rank.
At h=2 order the old points 0<1<2<3<4, with I={2,3}, J={0,1,4},
and w before0. The only cap triples among the old five points are
012,013,014; all other triples are cups. Put P={0,2,3}, Q={1,2,3}.
Both are whole three-cups, hence r(P)=r(Q)=2. Their intersection I
has rank2. Their union {0,1,2,3} has rank3 because {0,1,2} is a cap,
while the whole four-set contains a three-cup and is inadmissible.
Consequently r(P)+r(Q)=4<5=r(P union Q)+r(P intersection Q).
The host X has c4/d4/sigma5 and natural bands1,2,3, so this remains
an obstruction for the natural bottom band cup<=2/cap<=4.

Dedup search "cup cap bounded independent sets matroid exchange rank
submodular" returned no hits. These are direct uniform paper counterproofs,
not a new computation or Lean theorem. They exclude generic matroid/rank
exchange, but do not refute a decomposition-specific coupled exchange,
BDL, or the strict contracting ROOT obligation.

## 76. Exact regional merge profiles and the singleton tower's scope

For nonempty lower A and upper B, the DS mixed-chain normal forms give
the following exact identities. Empty regional chain maxima are zero,
and span means the open interval between a set's extreme points:

  c(A union B) = max(c(A),c(B),
    1+c(A below max B), 1+c(A above min B),
    2+c(A intersect span(B)));
  d(A union B) = max(d(A),d(B),
    1+d(B below max A), 1+d(B above min A),
    2+d(B intersect span(A))).

Pure chains give the first two terms. One opposite-child endpoint gives
the prefix/suffix terms. Two opposite-child endpoints give the open-span
term. Every positive regional maximum attains its displayed extension
by the extreme opposite-child points. If a region is empty, the artificial
term1 or2 is dominated by an actual point/pair in the nonempty union.
Thus the identities also handle singleton children without fictitious
long chains. Empty children are handled separately by the other child.

For a band's cup limit u>=2 and cap limit v>=2 these identities translate
merge validity into pure-child limits and six regional inequalities:
two lower-child cup prefix/suffix bounds u-1, its cup span bound u-2,
two upper-child cap prefix/suffix bounds v-1, its cap span bound v-2.
If either limit is1, a band meeting both children is already impossible
because its two-point subset is both a cup and a cap. Applied in every
band this is an exact description of compatible assignments, not an
existence theorem: the same child assignment must satisfy every region
and every neighboring-band requirement simultaneously.

For a lower singleton z this simplifies completely. Adding z to a cell C
creates only mixed cup triples bracketing z and caps consisting of z
plus a cap wholly before or after it. Hence keeping z in bottom lo is
unrestricted on cups when lo>=2, requires C one-sided at z when lo=1,
and requires C empty when lo=0. Bottom caps fit the retained global bound.
Lifting z to lo+1 requires no(beta-1)-cap of that cell wholly before z
or wholly after z. This is sufficient on cups only when lo>=1; at lo0
the lifted cell must also be one-sided at z. This positive-floor condition
is automatic in the retained-cap hard root, since 1+beta<=s forceslo>=1.

The newly read shared Q17 PROOF-DRAFT.md section4.5 states the singleton
lift criterion without an explicit retained-cap/positive-floor hypothesis
in its setting, and uses 3<=lo+2. This needs the above qualification.
A direct four-point example shows why: C={0,1,3} is a whole three-cup,
z=2 is lower, Y={z}<<C, and s3. Y's triples012 is cap;013,023,123 are
cups. Thus c(Y)=d(Y)=sigma(Y)=3 andlo0. The valid child assignment
C0=1,C1=2,C3=1 has second cell{0,3}. Its two-cap neither ends beforez
nor starts afterz, but liftingz makes the forbidden three-cup{0,2,3}
in band1, whose cup limit is2. This only corrects the unqualified setting;
it does not refute BDL or the positive-floor retained-cap lemma.

For lo>=1, the core explanation in shared section4.5 is sound when it
uses the PARENT core: z<R*(Y) rules out a maximum beta-cap ending atz,
and z>L*(Y) rules out one starting atz. It cannot use the child's core
in those assertions. When R*(Y)<=z<=L*(Y), both endpoint towers can
be needed. Several lifted sibling points additionally create two-endpoint
caps across an interval; independent marginal endpoint towers alone do
not encode that term. Shared section4.6 explicitly leaves those lifts
under exact semantic closure checks.

Shared draft sections6-7 report determined-rule failures, a one-sided
language failure on four n25 labels, and successful two-sided backtracking
on its diagnostic corpus. These are shared reports, not newly executed
or independently replayed R25 results; our pinned six-label selected-rule
audit remains exactly its finite scope. The general intrinsic family of
contexts with option admission and ambient terminal truth is still absent.
Snapshot Q17-PROOF-DRAFT.snapshot-0039.md was copied at00:38 UTC,
SHA25634d9b5a9b298809ab31d2db688f479c61950e2ceb385bdfb50400374019de732.
Read ctx2.py lines1-155 readonly; did not execute or adopt that new source.
Dedup search "deep below union cup cap exact prefix suffix span chain
maxima" returned no hits. These are direct DS paper identities/scope
checks, not a new Lean statement, diagnostic job or BDL construction.

The reviewed audit_regional_merges.py tests these identities on every
induced cell of every full root in the declared decomposable class, using
promoted all-triple metrics. It also checks the fixed four-point scope
example. Pilot204959-c1c422 passed0.003140763s/7MiB. Full205050-aa468a
passed0.772579555s/8MiB after memory admission: all792 n<=6 colorings,
1214roots72344inducedcells40010mixed agree. Fixed scope/range quad
validates. Durable regional-merges-n4.json/regional-merges-n6.json.
No partition solve, fitted hypothesis, BDL result or Lean credit.

## 77. The cardinality obstruction is an open-core Pascal deficit

CORED-PASCAL-DEFICIT.md gives the detailed conditional equivalence with
Theorem8's cardinality upper bound. For cored B with c=alpha,d=beta,
sigma<=s,p=s-beta>=1,demandalpha-p>=3, the open obligation is

  |B| <= sum(j=p..alpha-1)choose(s-1,j)-choose(s-2,p-1).

The subtracted term is the size of an extremal classical decomposable
cup<=p/cap<=beta set. Insert that entire set into one empty gap of B's
open maximum-cap core: the DS retained-cap window and p+2<alpha keep
both maxima unchanged, and the strong root join is exactlys. Thus the
general cardinality theorem implies this deficit. Conversely a cardinal
size induction consumes disjoint child capacity windows at strict roots,
and the deficit pays for the whole classical sibling at retained roots;
the cap3 boundary is exactly R20's2s-2. This proves a conditional
cardinality equivalence, not the deficit itself or a BDL partition.

The restriction to demand>=3 is essential. The same four-point coloring
with only012cap has c3/d3/sigma3 and open cap core(0,2). At s5 its
one-band F6 minus proposed slab3 is3, less than its actual size4.
The lower set would raise the cup maximum, so the necessity proof cannot
extend to that range. An inductive deficit invariant again needs a
different treatment of low-demand descendants; none is proved here.

This describes the general quantity to understand, not an easier narrowed
result. No recursive deficit trial, small-parameter confirmation or Lean
statement is commissioned. BDL's exact remaining obligation is still
strict contracting ROOT, where a compatible global partition is required.

## 78. Uniform Pascal tails embed every active state into the diagonal

DIAGONAL-PADDING.md gives the complete symbolic construction. Append
classical blocks K(j+1,s-j) spatially RIGHT/UPPER to an old LOWER carrier,
for j0,...,t-1. This E_s(t) has sizeL_s(t)=sum(j<t)choose(s-1,j)
and cup=t,cap=s,strong=s for t>=2 (t1 is a singleton, t0 omitted).
Every root joins j+(s-j)=s. Its classic blocks explicitly realize the
individual band capacities; each lies in its own bandj.

For B cupalpha,capbeta,strong<=s,alpha+beta>=s+1, putp=s-beta,q=s-alpha.
Append LOWER E_s(p) on B's RIGHT, retaining cupalpha and raising cap tos.
Then append UPPER dualE_s(q) on the RIGHT, raising cup tos and keeping
cap/strongs. The original coloring is exactly preserved on its first
|B| points. The resulting diagonal set Z has

  |Z| = |B|+2^(s-1)-sum(j=p..alpha-1)choose(s-1,j).

Thus diagonal cardinality implies all active state cardinalities; the
inactive states are classical. This is a conditional equivalence with
the full cardinality theorem, not a proof of the diagonal upper bound.
Numerical excess is unchanged and size/strong budget do not descend, so
it cannot be inserted as a circular induction step. Restricting a diagonal
BDL map leaves indices0..s-1, without the necessary natural-range
normalization for B. Canonical dummy-tail maps glue with BDLB, but no
converse arbitrary-map transfer is established. Contracting ROOT remains.

The reviewed audit_diagonal_padding.py and byte-identical pinned classical
source use complete-triple/quad metrics, direct mixed-root checks and
original-color preservation. Pilot211235-f49a25 passed0.000383694s/12MiB.
Fixed211338-422631 passed2.672292322s/13MiB: four declared <=16point
tail/dual/actual-root cases, exact diagonal profiles and every old triple
validate. Evidence diagonal-padding-pilot.json/diagonal-padding-fixed.json.
This replays a construction, not an upper bound; no larger confirmation.
No new Lean statement, compiling theorem or proof receipt.

## 79. Full Pascal saturation does not force canonical padding bands

Paper78 embeds the literal ROOT14 at s5 into Z16 by adding lower dummy14
and upper dummy15. All old points retain their labels under prefix01;
the dummies have labels00 and1. This Z has c=d=sigma=5 and cardinality16,
the full diagonal Pascal capacity. Nevertheless the following diagonal
map is valid and fills EVERY cell to its classical capacity:

| band j | points | cup,cap | size=choose(4,j) |
| --- | --- | --- | --- |
| 0 | 6 | 1,1 | 1 |
| 1 | 0,7,13,14 | 2,4 | 4 |
| 2 | 2,3,4,5,11,12 | 3,3 | 6 |
| 3 | 1,8,9,10 | 4,2 | 4 |
| 4 | 15 | 1,1 | 1 |

Keep the old thirteen-point frozen child map. Its bottom is the three-cap
(0,7,13), extended by lower dummy14 to a four-cap; its middle/top remain
valid. Put the original lower point6 alone in band0 and dummy15 alone in
band4. This proves every displayed limit directly. The original ROOT14
natural bands are1,2,3, so restriction of this valid diagonal map leaves
original point6 outside the natural range. The lower dummy is not in its
canonical band0. Classical saturation alone therefore does NOT force the
tail assignments needed for the converse padding argument.

This only refutes automatic restriction/canonical allocation. It does NOT
refute existence of a different normalized diagonal map, global recoloring,
ordinary ROOT or BDL. Indeed ROOT14 already has an explicit natural repair,
which glues with the canonical singleton tails. Normalization must encode
partition compatibility, not just capacity equality.

Dedup search `diagonal saturated band partition canonical padding natural
range` found no theorem. Reviewed one-map complete-triple certificate
211955-bd7fb4 passed0.003640664s/10MiB; saturated-padding-map-certificate.json.
No SAT, fresh coloring or larger sweep. No new Lean statement/receipt.

## 80. The cored deficit has a uniform sharp family and a classical boundary

CORED-PASCAL-SHARPNESS.md proves a symbolic construction for EVERY
p>=1,beta>=3,2<=m<=beta,s=p+beta,alpha=p+m. Start with
U=K(p+1,beta-1), then append upper/right K(j+1,s-j) for
j=p+1,...,alpha-1. Strong joins are exactlys and cup grows toalpha.
The first appended root's beta-caps are exactly one U endpoint plus a
(beta-1)-cap of its upper block; later blocks create no new beta-cap.
Thus the core is open with L=maxU and R strictly to its right. Size is
F_s(alpha,beta)-choose(s-2,p-1), since bottom U is what remains after
deleting lower K(p,beta) from first classic band K(p+1,beta). Every
higher natural band is full. This explains the proposed slab and proves
the numerical target sharp; it supplies no general CD upper bound.

CD at demand m2 is already CLASSICAL. Insert extremal lower K(p,beta)
in an empty cap-core gap; mixed cups have at mostp+2=alpha (strictness
was unnecessary) and cap staysbeta. Classical union cardinality is at
mostchoose(s,p+1)=the two-band F window. Subtract the inserted M.
The general theorem-implies-CD necessity argument works for m>=2.
Only m>=3 CD remains open. Demand1's four-point counter still prevents
unqualified propagation to all cored descendants; numerical m2 closure
does not prove a preserved contextual recurrence or BDL construction.

Reviewed direct212610-152877 passed0.688677356s/12MiB. Casep1/beta4/m3
n13=F14-M1 has profile(4,4,5),core(2,5) and30 entire max4-caps unchanged
across stages. Casep2/beta4/m2 n16=F20-M4 has profile(4,4,6),core(5,8),
276 max4-caps. All triples/quads, roots, natural cells, counts and exact
Cartesian cap families validate; cored-pascal-sharpness.json. No upper
search, SAT, larger sweep, new Lean statement or theorem receipt.

Paper80 research35 corollary: restoring its missing K(p,beta) face in the
empty U/V gap produces a full-capacity parent with an explicit natural
partition. A union U is a full bottom cell; every higher block stays full.
Its max-cap core becomes EXACTLY(maxA,minA), because a U(beta-1)-cap
ends at minA and a V(beta-1)-cap starts at maxA. Thus the core closes or
empties when the face is filled. This explains the construction's deficit
and the two nearmaximum sides it consumes. It is not a universal missing-
face theorem or proof of CD/ROOT; no new instance/search or Lean credit.

## 81. Pure-only new maximum caps close by peeling the classic lower child

At a hard retained-cap root X=A<<B put p=s-beta>=1,m>=3 and assume a
valid supplied B map on p,...,alpha-1. Suppose NO maximum beta-cap of X
meets BOTH A and B. Pure beta-caps of A may still strictly contract the
old B core, so this case was not included in paper68's conservation.

If d(A)<beta set F empty. Otherwise let F be the first points of all
maximum beta-caps of A. Then c(F)<=p-1 and d(A minus F)<=beta-1.
For the endpoint theorem, p>=2: if p1 then A is a singleton and cannot
have beta>=4. Both endpoint chains have at least2 points when needed.
Replace only the first TWO supplied cells by

  new_p     = B_p union F,
  new_(p+1) = B_(p+1) union(A minus F).

Bottom cups have at mostmax(p+1,p-1+2)=p+1 points, by DS; its capbeta
bound follows from containment in X. Second cups have at mostp+2 points,
since c(A minus F)<=p and c(B_(p+1))<=p+2. Neither pure part has a
beta-cap. A mixed beta-cap would contradict the GLOBAL no-mixed-maximum
assumption. Thus the second cap is at mostbeta-1. Every other supplied
cell stays valid, and all points are assigned once. This closes EVERY
no-mixed-max root, even if the supplied map was arbitrary or the core
strictly contracts. The conservation case is its Fempty subcase. ∎

The exact remaining ROOT may therefore require a MIXED maximum beta-cap.
Every such cap has an A endpoint strictly inside the old B core, so it
automatically strictly contracts the core. Pure-only contraction is closed.
In the existing geometric formulation, mixed existence is EXACTLY one
of the following regional threshold equalities (empty rank0):

  d(B_<maxA)=beta-1, OR d(B_>minA)=beta-1, OR
  |A|>=2 and d(B intersect span(A))=beta-2.

A mixed cap has one or two A endpoints, giving these conditions. Each
threshold supplies the corresponding endpoint extension cap; retention
bounds these regional ranks from above, so inequality becomes equality.
There is no compatible partition construction for this genuinely mixed
case. Requiring it is justified by the explicit closed construction above,
not a speculative narrowing. The frozen p1 ROOT14 remains mixed (cap
2,3,5,6) and all earlier arbitrary-map repair obstructions survive.

One direct witness for the newly closed pure-only case: p2,beta5,s7,
alpha5,m3. Put a whole5-cap Q entirely before a whole5-cup C, with Q<<C;
then insert a lower whole5-cap A after Q's first two points. B has c5/d5/
sigma5 and its supplied bands are Q/empty/C at2/3/4. X has c5/d5/sigma7.
Its ONLY max5-caps are pure Q and pure A: B ranks before/after the gap
are2/3, both below4, and its span between A extrema is empty. Core moves
from(0,9) to(2,6), still open. All A in bottom makes a4cup; all A in
second retains cap5 against limit4. Peeling A's first point gives the
valid Q+firstA / restA / C. This tests the actual new mechanism, not a
BDL counterexample. Guarded complete-triple/quad replay
20261003-215341-49dcb5 passed0.207469503s/7MiB: all455 triples/1365
quadruples, parent/child profiles, exact two pure maximum caps, zero mixed
maximum caps, cores, both naive failures and all resulting bands validate.
The output is pure-maximum-closure-certificate.json. This fixed replay
supports the uniform proof above; it is not general or Lean certification.

The replay checks chain/strong maxima by complete triples and defining
strong quadruples. Decomposability comes from the recursive binary-prefix
construction; root membership alone would not certify the children.
No separate runtime OneChange assertion or compiler receipt is claimed.

Dedup search `classic lower cap endpoint peel mixed maximum root band`
found no theorem. This is a paper closing case, no new Lean receipt.

## 82. Full-core BRL+ is false; ordinary recoloring survives this witness

The open question was whether the stronger full-core positioning premise
actually holds in the exact hard-child range. BRL+ asks: for decomposable
B with sigma<=s, actual alpha,beta, beta>=4,p=s-beta>=1,
alpha=p+m with3<=m<=beta, a valid supplied partition on[p,alpha-1],
and open maximum-beta-cap core(L*,R*), does another valid partition exist
whose bottom lies wholly<=L* OR wholly>=R*? Both inequalities are inclusive.
A positive answer would give a sufficient ordinary root repair. A negative
answer would eliminate that general premise while leaving arbitrary global
recoloring open. Only the already reported exact witness was commissioned.

The shared witness is tag g657n25d1-32, mirror0, from
claude-tower-20261003/i_wide4.pkl. Select all25 original labels exceptpoint7,
and relabel the selected24 points consecutively in their original x-order.
The immutable snapshot BRL24-input.snapshot.pkl has SHA
4365fb72752c27cf137631d1105aeefd3ffc365a30b459b4e2a48c99ecec4a80.
brl24-resource-pilot.json records every source label and selected original
index in readable JSON. The labels are distinct equal-length binary words,
hence prefix-free; the promoted decoder validates that contract. Recursive
prefix splitting defines a decomposable coloring, with a mixed triple Cup
exactly when its middle point has bit0 at the first varying coordinate.
Arbitrary deletion preserves that construction. This is diagnostic input
certification, not a compiling Lean certificate.

Independent source brl24_recheck.py is a byte-identical copy of the shared
recheck.py, SHA6d23f4d20bf69a8033d0176affc4bc6508488d6f17107598ec9d32660865a7f9;
dec_audit.py is SHA4031e8f3fdaefe4316a6c259f82c0061694b56977b6ff86743ed130bcfabfb52.
Both were read completely. The coloring/chain DP, direct all-subset strong
DP and complete band backtracking are independent of the coordinator SAT
checker. Backtracking assigns points increasingly, tries every permitted
band, updates longest consecutive cup/cap ending-pair ranks, and restores
those entries on rollback. On a decomposable one-change coloring this is
equivalent to monochromatic-chain admissibility. Found partitions are
verified independently by recomputing per-band chain maxima. The lazy SAT
helper in dec_audit.py is not called by our replay.

Guarded resource-only pilot20261003-223237-f65078 measured the strong DP
on a pure cap at n16:0.049777339s, harness0.1s/13MiB. The subset ratio256
and conservative point-factor384 suggested19.115s and an upper memory
extrapolation3328MiB; the witness used a4G guarded cap and review2min.
The replay queued under the shared pool, then completed normally; no
other agent's reservations were altered and no self-chosen deadline used.

Exact guarded job20261003-223307-714ff0 finished rc0,10.6s/1613MiB,
no OOM or missing output. Its complete verdict is:

    n24, alpha4, beta5, strong6, k7, core(6,15),
    BRL+L=False, BRL+R=False, zlock[7]=(True,2,True).

Thus s6,p1,m3 meet every stated BRL+ parameter. Neither constrained child
partition exists on bands1,2,3 (cup limits2,3,4; cap limits5,4,3), even
allowing ALL child points to recolor. The ordinary parent obtained by a
lower singleton z at localgap7 has a verified valid map with z inband2.
Restricting that map gives a valid B map, so the supplied-map premise is
nonvacuous. DS gives the parent's strong number6, and the replay directly
checks retained cup4/cap5. Output brl24-backtracking-recheck.txt has SHA
723c2121c08c176673209dc52e64d6dd148649f7a87b7f0578ae70f2a3c02be3.

**Consequence:** full-core BRL+ is diagnostically refuted, and its earlier
conditional implication to BDL cannot be a universal proof route. Ordinary
BDL and MIXED ROOT are still unproved/unrefuted. A found band2 solution
does NOT rule out another parent map with z inband1; this run did not ask
that separate question, or replay other gaps. Full-core one-sidedness is
stronger than sibling-specific span avoidance. Preserve that scope rather
than silently treating this witness as a counterexample to ordinary ROOT.
No larger coloring sweep or new theorem was admitted from this result.
