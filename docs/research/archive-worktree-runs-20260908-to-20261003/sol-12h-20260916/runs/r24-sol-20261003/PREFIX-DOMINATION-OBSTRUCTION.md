# General cap-block mechanism refuting prefix/suffix domination

2026-10-03 17:16 UTC. The p5 arithmetic below uses the unchanged shared C evaluator. The parameterized argument is hand mathematics and has no compiling Lean receipt.

## Exact diagnostic refutation of the locked statement

For(a,u,k)=(6,5,6), take sigma=S1L3L2LSSS,maxima111. Its child positions are[0,4,5,6]. It is well formed:2<=a,u<=k; the three levels are positive and within the declared depth, each has only lower tags, and every sibling maximum is1 in1..k-2.

Set keep=[0,4,6],d=2. The lower child has word S2L4L3LS1LS,maxima2111,B7. Its upper complement has word1U2L4L3L1US1U,maxima3111,B2. Their sum is9. Every List.take/List.drop cut with j=1,2,3 and every d'=1,2,3,4 has sum at most8. This directly falsifies the **first conjunct** of `ctx_bound_prefix_suffix_domination`, whose locked type hash is dab0805effb44b48. Its source statement does not exclude interval/complement cuts, and the selected complement of a middle singleton meets every hypothesis.

Job20261003-131255-6f4082 completed in0.04486s algorithm. `cap-block-domination-p5.json` stores the24 prefix/suffix terms, both child signatures, all singleton cuts and source hashes. ParentB=9. These are diagnostic integer evaluations, not kernel proof credit. A counterexample to this node is distinct from a literal cardinality counterexample: this word has only4 child positions.

## Parameterized split

For every p>=5, take a=k=p+1,u=5 and the same word/maxima. Its endpoint profile has Cp constantp and Cu diagonal2,cross4. Let the first,second,third,fourth S slots be0,1,2,3 in ordinal order. Retain0,1,3 as the lower child with opposite cap maximum p-3; the middle singleton2 is upper with opposite cup maximum3.

The lower child's Cp is constantp and its Cu is

    [[2,3,3],[0,1,2],[0,0,1]].

Its three runs have capacities p,1,1, so B<=p+2 by the hand B-attainment/interface theorem and the elementary zone upper. The inner split with zone0 lower and the other two runs upper attains p+2: the first leaf is a p-cap; each endpoint run has one point, and the pair is a2-cap. Their root coupling is2+2<=p. Exact finite child transforms leave every required diagonal positive and the first leaf's cup limit2. Therefore B_lower=p+2.

The middle upper singleton has cap limit p-3 and cup limit2. Its one-run arithmetic base is p-3. The candidate contribution is consequently

    (p+2)+(p-3)=2p-1.

Geometrically the lower child combines a p-cap in zone0 with a2-cap of zone1 endpoints. An upper(p-3)-cap lies between those two endpoints. The outer root coupling is3+(p-3)=p; all caps have size at mostp and cups at most4. This is why the interior split contributes more than an end split.

The forced-root argument in `TWO-CAP-BLOCK-OBSTRUCTION.md` excludes B=2p, so the parent finite bound is exactly2p-1 under these hand interfaces. This uses only one slot in zone0 and three in zone1: increasing literal slot multiplicity cannot repair the remaining gap to N=2p.

## End-cut upper: finite-state case distinction

Write d for the lower child's opposite cap maximum,1<=d<=p-1. Cup limit2 makes a whole zone a cap. Cup diagonal1 permits at most one point; a spanning cup limit2 makes the entire two-zone union a cap. Use the exact transforms in `FINITE-PROFILE-STATE.md`, retaining zero children.

- At the boundary after the first slot, either lower side is a whole run. The lower leaf is p when d<=p-2 and1 when d=p-1; the upper leaf is d. The sum is at most2p-2, attained at d=p-2.
- For a lower prefix ending inside the last run, its zone0 has cap limitp/cup2, and its right run has cup diagonal1. Its spanning cup limit is min(3,p-d). Thus its B is at most p+1 for d<=p-3,at mostp for d=p-2,and at most1 for d=p-1. The upper suffix is the one-run value d. Every sum is at most2p-2. Adjacent right slots in the lower prefix remain one run with capacity1; extra resolution does not change this upper.
- For a lower suffix of two right slots, its cup diagonal is1,so its leaf value is1. The upper prefix has one slot in each of two zones,cap matrix constantd,cup diagonal2/cross4. Its finite two-slot bound is at most2d-1: a split gives the growing upper cap at mostd-1 and the lower cap at mostd. This includes d1,where the upper value is0. Hence the sum is at most2p-2.
- For a lower last singleton, its value is1. The upper prefix has one slot in zone0 and two adjacent slots in zone1,cap matrix constantd,cup diagonal2/cross4. If d<=p-2,its two-zone upper2d gives total at most2p-3. At d=p-1,put q=d and strong bound q+1. Its finite three-slot B is at most2q-1 by the auxiliary argument below. Total at most2p-2.

For the auxiliary three-slot bound with caps q,cups2/4 and strong q+1, inspect each proper interval/complement root. A whole-zone leaf split loses at least one cap endpoint, giving at most q+(q-1). If a right singleton is upper,its cap is at most min(m,q-1); the lower two-zone part has a right cup diagonal1 and global cup bound q+1-m (its spanning inherited bound is4,and drops to3 only when the singleton is outside the chain endpoints). Its upper is q+1 for m<=q-2,q for m=q-1,and1 for m=q. Again the sum is at most2q-1. If a right singleton is lower,its cup diagonal is1,so its value is1; each remaining upper run has cap diagonal at mostq-1,so their total is at most2(q-1). These cases cover every interval/complement on three ordered slots. All inequalities permit zero children and bound them by the same hand B-attainment/interface.

Therefore the best prefix/suffix contribution is exactly2p-2,while the retained interior split gives2p-1. The universal end-domination mechanism fails for this entire parameter family. A future formal proof should certify the exact matrix transform and these small symbolic recurrence bounds, rather than add another isolated numerical instance.

## General implication and open certification

The missing end-cut normal form is not an unusual large tree. A single interior opposite slot is enough to require two separate flanks. The true maximum N=2p needs the four zone endpoints as one root child; the finite interval maximum2p-1 uses a nested interval root; end cuts achieve only2p-2. These are three different structural restrictions.

The unchanged-C p5 receipt is complete. The general proof depends on the hand B-attainment and exact-profile-state interfaces; neither is compiled. No Lean instance was added, in accordance with the R24 instruction to reserve Lean work for general structural lemmas. The10-slot literal query remains a separate authorized computation.
