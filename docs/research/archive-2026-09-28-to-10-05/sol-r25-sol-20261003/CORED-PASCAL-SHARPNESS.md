# The open-core slab deficit is sharp, and its two-band boundary is closed

Uniform paper constructions using DS and the classical Pascal blocks.
**The general demand>=3 upper bound CD is still unproved.** No Lean
statement or receipt is added. This explains the missing term in
CORED-PASCAL-DEFICIT.md; it does not construct arbitrary BDL partitions.

Let p>=1,beta>=3,s=p+beta and2<=m<=beta,alpha=p+m. Classical K(a,b)
has size choose(a+b-2,a-1), actual cup a/cap b when a,b>=2, and is a
singleton when either bound is1. Its strong number is at mosta+b-2,
apart from the singleton1 boundary. All blocks below are spatially
separated; the old carrier is LOWER/LEFT and the new block UPPER/RIGHT.

Start with U=K(p+1,beta-1). For j=p+1,...,alpha-1 append

  H_j = H_(j-1) << K(j+1,s-j), with H_p=U.

For j=p+1 the old cup is p+1 and the new cap beta-1, so DS gives
strong number exactlys. The new block attains cup p+2. A mixed cap
uses one U endpoint and a new(beta-1)-cap, attaining beta, while all
pure caps have at mostbeta-1 points. At every later step the old cup
is j, the new cap is s-j, and their sum is s. Its new block attains
cup j+1 unless s-j=1; in that final singleton case an old maximum
j-cup gains the new upper endpoint. Thus final H has

  c(H)=alpha, d(H)=beta, sigma(H)=s.

After the first appended block, every mixed new cap has size at most
(s-j)+1<=beta-1. Later blocks consequently create NO new beta-cap.
At the first appended root every beta-cap consists of ONE U point
followed by a(beta-1)-cap of V=K(p+2,beta-1). Conversely every U
point and every such V cap form a beta-cap. Hence

  L_H = max(U),
  R_H = min last(D) over maximum(beta-1)-caps D of V > max(U).

The maximum-beta-cap core is open, and this core/family persists through
all later blocks. The particular empty gap between U and V is contained
in that core.

The cardinality is

  |H| = choose(s-2,p) + sum(j=p+1,...,alpha-1)choose(s-1,j)
      = F_s(alpha,beta) - choose(s-2,p-1).

Indeed U is the upper K(p+1,beta-1) half of K(p+1,beta), whose lower
half K(p,beta) has exactly the removed slab capacity. Assign U to bandp
and each later block to its indexj. This is an explicit natural BDL map;
every cell above bottom is full, and bottom lacks exactly the proposed
slab. Thus the deficit subtraction is sharp for EVERY stated parameter,
not merely a small fitted family. At beta3,m3 it is the R20 quantity
2s-2. This construction supplies no upper bound for other colorings.

The two-band boundary m2 of CD already follows from the classical theorem.
Take any decomposable B with sigma<=s, cup alpha=p+2, cap beta and an open beta-cap
core. Insert A=K(p,beta) in one empty core gap, lower than B. Its size is
M=choose(s-2,p-1); for p1 use a singleton. Exact retained-cap geometry
gives cap(A union B)=beta. Mixed cups have at mostp+2=alpha, so cup stays
alpha. DS gives strong number s, although it is not needed for the next
classical inequality. Therefore

  |B|+M <= choose(alpha+beta-2,alpha-1)
          = choose(s,p+1)
          = choose(s-1,p)+choose(s-1,p+1) = F_s(alpha,beta).

This proves CD at m2. The general-theorem-implies-CD argument actually
works for m>=2; its earlier strict inequality p+2<alpha was unnecessary.
The m1 four-point counterexample still refutes unrestricted low-demand
propagation. Only the demand>=3 deficit is unresolved; closing m2 does
not solve its recursion, tower admission or mixed-maximum ROOT.

## Restoring the missing face closes the core

In this explicit H, insert A=K(p,beta) into the empty gap between U and V,
lower than all H. The gap lies in every maximum-beta-cap interval; no H
point lies in span(A). Retained-cap geometry gives cap(X)=beta, mixed
cups have at mostp+2<=alpha, and the strong join is p+beta=s. Hence
c(X)=alpha,d(X)=beta,sigma(X)=s and|X|=F_s(alpha,beta).

Put A union U in bottom bandp and leave each higher classic block at its
index. U is wholly LEFT of A, so cups meeting A have at mostp+1 points.
The bottom cap is at mostbeta (and attained by a U(beta-1)-cap plus one
A point). The bottom size is M+choose(s-2,p)=choose(s-1,p). Thus EVERY
natural band is full and this parent has an explicit valid BDL map.

The parent's maximum-cap core is exactly

  L_X=max(A), R_X=min(A).

For the first equality, append a maximum(beta-1)-cap of V to max(A);
this beta-cap starts at max(A). No new maximum cap can start later, since
it contains an A point; every old maximum cap starts in U, earlier still.
For the second, append min(A) to a maximum(beta-1)-cap of U, obtaining
a beta-cap ending at min(A). No new cap can end earlier because it
contains an A point, while every old maximum cap ends in V. This covers
p1's singleton and p>=2's larger classical block without needing A itself
to attain capbeta in the singleton case. Therefore restoring the face
degenerates the core when A is a singleton and makes L_X>R_X otherwise.
No further nonempty lower sibling can retain capbeta at this profile.

This is a structural explanation in the explicit sharp family: the missing
face can be filled, but filling it uses both near-maximum cap sides and
destroys the open core. It does NOT show that an arbitrary cored coloring
admits a missing-face representation, universal normalization or CD upper
bound. That would be the unresolved global invariant, not a consequence
of these constructed examples. The result is a direct DS corollary of the
already audited family, not a new search, Lean statement or receipt.

Dedup search `open cap core two band binomial deficit sharp construction`
returned no theorem hits. The pinned classical generator and promoted
all-triple metrics were reused for guarded direct replay212610-152877,
passed0.688677356s/12MiB. The p1/beta4/m3 case has n13=F14-M1,
profile(4,4,5), core(2,5) and30 maximum4-caps unchanged across stages.
The p2/beta4/m2 case has n16=F20-M4,profile(4,4,6),core(5,8) and276
maximum4-caps. Every root, cell and entire Cartesian cap family validates;
cored-pascal-sharpness.json. Diagnostic support, not a compiling theorem.
