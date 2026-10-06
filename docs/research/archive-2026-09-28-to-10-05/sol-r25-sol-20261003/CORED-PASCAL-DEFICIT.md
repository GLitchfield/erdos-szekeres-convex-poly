# The cardinality analogue of the tight nested split

Paper reduction only. **The open-core deficit below is unproved.** It is
equivalent to the general decomposable cardinality upper bound, conditional
on the accepted DS and classical cup--cap inputs. It is necessary for BDL,
but its sufficiency for BDL is not known. It therefore does not replace the
mixed-maximum ROOT obligation in BDL-CORE-REDUCTION.md.

Write c,d,sigma for actual maximum cup, cap and strong-set sizes. Fix s,
and let all colorings be finite and decomposable. The accepted inputs are
the DS root law, hereditary decomposability/one-change, the classical bound

  |Y| <= choose(c(Y)+d(Y)-2,c(Y)-1),

and its standard recursive extremal construction. Degenerate singleton
cases are handled directly. R23's compiled classical one-change input is
preserved on its own branch; no Lean theorem or import is added here.

## Exact open obligation

Let B have sigma(B)<=s, c(B)=alpha, d(B)=beta, and an OPEN maximum-cap
core (L*,R*), where L* is the largest first point and R* the smallest last
point of its maximum beta-caps. Put p=s-beta. Assume

  p>=1, beta>=4, alpha>=p+3.

Cup and cap sets are strong, hence alpha,beta<=s and alpha-p<=beta.
Define

  F_s(alpha,beta) = sum over j=p,...,alpha-1 of choose(s-1,j),
  M_s(beta) = choose(s-2,p-1).

The **missing cardinality statement** is

  |B| <= F_s(alpha,beta) - M_s(beta).                 (CD)

The subtraction is a full classical cup--cap capacity, not a fitted count.
An open core supplies an empty gap in which an extremal lower set of that
size could be inserted while preserving the global exclusions.

## Why the general cardinality theorem implies CD

Construct a classical decomposable A with cup<=p, cap<=beta and
|A|=choose(p+beta-2,p-1)=M_s(beta). For p=1 use a singleton. Otherwise
the standard Pascal construction K(p,beta) places K(p-1,beta) entirely
before and below K(p,beta-1). Its cup is at mostp and cap at mostbeta,
because a mixed chain has only one opposite-child endpoint in this spatial
concatenation. The singleton boundary p=1 or beta=1 and Pascal's identity
give its size. For p,beta>=2 its actual cup and cap maxima attainp,beta.
Its strong number is at mostp+beta-2=s-2, by DS induction (or the accepted
one-change bound sigma<=cup+cap-2). For the singleton, sigma1<=s-2.
The retained generator is univ.es_labels, reused by the earlier R25
check_block_depth_formula.py; this paragraph gives its symbolic proof.

Insert all A into one empty spatial gap of (L*,R*) and put A<<B. Every A
point lies inside every maximum beta-cap of B, and no B point lies in
span(A). The exact retained-cap criterion therefore gives d(A union B)=beta.
Mixed cups have at mostp+2<alpha points, so c(A union B)=alpha. DS gives
sigma(A union B)=s, since cup(A)+cap(B)=p+beta=s (also when p=1).
The union remains decomposable by its new root.

The general cardinality upper bound applied to this union yields

  |B|+M_s(beta) <= F_s(alpha,beta),

which is CD. Thus BDL, through its per-band classical bounds, also implies
CD. This is a necessity argument, not an independent proof of CD.

## Why CD suffices for the cardinality theorem

Include the already closed beta3 boundary and the cup/cap dual of CD.
Induct on the number of points, with s fixed. For an actual profile(a,b),
the desired bound is classical when a+b<=s+2 and is F_s(a,b) otherwise.
At a+b=s+2 the classical coefficient equals its two-term Pascal window:

  choose(s,a-1) = choose(s-1,a-2)+choose(s-1,a-1).

When a+b<=s+1, the whole child can be assigned a single capacity index j
whenever a-1<=j<=s-b. Its classical size is at mostchoose(s-1,j): pad a
binary word of lengtha+b-2 with j-(a-1) ones and s-j-b zeros. Both padding
counts are nonnegative. This compares capacities without choosing a band
partition of the child's points.

Consider a root X=A<<B with parent alpha+beta>=s+3. Put
pA=c(A),qA=d(A),rB=c(B),tB=d(B), l=s-beta,h=alpha-1.
DS gives pA+tB<=s. If both maxima are strict, beta>tB and alpha>pA,
the child's induction windows [s-qA,pA-1] and [s-tB,rB-1] lie inside
[l,h] and are disjoint. A child with a+b<=s+1 instead consumes only
jA=max(pA-1,l) or jB=min(s-tB,h), respectively. These indices satisfy
their classical capacity bounds. They are disjoint from the other window;
if both children are single-capacity, jA<jB. The same inequalities are
proved in BDL-CORE-REDUCTION.md's strict-max case. Adding disjoint capacity
terms proves the parent's cardinality bound. The two-band children use
their two-term window, as above.

If cap is retained, beta=tB, then pA<=p=s-beta. The nonempty lower part
forcesp>=1, and every maximum beta-cap of B surrounds all A points;
B's cap core is open. Also rB=alpha because mixed cups have at most
pA+2<=p+2<alpha points. A is classical and

  |A| <= choose(p+beta-2,p-1) = M_s(beta),

using cup<=p and cap<=beta (the singleton p=1 case gives1).
CD gives |B|<=F_s(alpha,beta)-M_s(beta). Add the two bounds. The retained
cup case follows by complementing colors and swapping root children.
Both maxima cannot be retained, since that would givealpha+beta<=s.
These cases exhaust the root. No compatible child map is required.

For beta3, the hypotheses forcealpha=s and s>=4. The R20 ordered-two-cup
result gives |B|<=2s-2. Here

  F_s(s,3)-M_s(3)
    = [choose(s-1,2)+(s-1)+1]-choose(s-2,2) = 2s-2.

So this boundary is exactly CD, not just an unrelated small case. Values
beta<=2 cannot have alpha>=p+3 with alpha<=s. Thus CD for beta>=4 and its
dual complete the conditional cardinality induction. This proves the
claimed equivalence with the general cardinality upper bound, under the
stated inputs, without proving CD itself. Monotonicity then passes from
actual maxima to the exclusion parameters of Theorem8.

The repository interface is exact. With a=beta+1,u=alpha+1,k=s+1,
Decomposable.lean's decomposableThreshold is classical precisely when
alpha+beta<=s+2, and otherwise its window[k-a,u-2] in rowk-2 is
[s-beta,alpha-1] in rows-1, namely F_s. For larger exclusion parameters
use the existing decomposableThreshold_mono from2 in
DecomposableContextLemmas.lean. Parameters a1/u1 admit no nonempty
counterexample, by containsCapSet_one/containsCupSet_one; k1 also forces
the carrier empty. These source interfaces were inspected in review36;
no Lean reduction is registered or compiled in this run.

## What is still missing

Demand1 is a genuine failure range, so CD cannot simply be carried as
an invariant to every cored child. The four-point coloring in paper76,
whose only cap triple is012, has c3/d3/sigma3 and open cap core(0,2).
At s5 it has p2 and demand1. The unqualified deficit would give
|B|<=choose(4,2)-choose(3,1)=3, although|B|=4. Inserting a p2-cup can
raise the parent cup to4, so the necessity argument correctly stops at
alpha>=p+2. Equality m2 also preserves the cup, and its deficit is
already classical: insert the extremal A, then use the classical union
bound choose(s,p+1)=F. CORED-PASCAL-SHARPNESS.md gives that proof and a
uniform open-core construction attaining F-M for everyp>=1,beta>=3,
2<=m<=beta. Thus only demand>=3 CD is unresolved. The example is an
exact demand1 range failure, not a target refutation. A
recursive deficit proof would need a separate invariant for demand1
children; the closed m2 numerical bound alone supplies no closure rule.

At alpha=s, Pascal's identity simplifies CD to

  |B| <= 2*sum(i=0,...,beta-2)choose(s-2,i).

For beta3 this is2s-2; for beta4 it is s^2-3s+4. This algebra explains
the loss of the leading capacity term. A gap cut does give cap<=beta-1
on each side, but it does not lower each side's strong budget to s-1.
For example put a single lower z after a whole s-cup P. Then B={z}<<P
has c=s,d3,sigma=s and open cap core (second-last P,z). A gap after P
leaves the whole s-cup on one side. Thus applying an s-1 strong-set bound
independently to both sides is invalid; only a proven joint deficit could
justify the simplified expression. No side-bound confirmation is run.

CD identifies the quantity to explain: why an open maximum-cap core costs
an entire Pascal capacity term. There is no proven injection, counting
invariant or contextual recurrence establishing that loss. This replaces
compatible recoloring only for the cardinality target; it supplies neither
a BDL partition nor a preserved BDL induction hypothesis. It is therefore
an alternate interpretation of the general obstruction, not research
progress by narrowing, and no confirmation sweep is commissioned.

Dedup searches for cored binomial deficiency and classical decomposable
cup--cap extremal constructions returned no theorem hits. The root/metric
library and existing es_labels source were consulted. No Lean statement,
job result, certificate regeneration or theorem credit is claimed.
