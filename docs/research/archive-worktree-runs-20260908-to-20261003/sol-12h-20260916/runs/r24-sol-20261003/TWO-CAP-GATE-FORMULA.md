# Two-cap spanning-cup gate formula

2026-10-03 18:06 UTC. Proposed general hand result. The upper ingredients are
in `TWO-CAP-CUP3-PENALTY.md`; no new Lean receipt certifies this formula.
Constructor pilot `20261003-140416-e76f31` passed in0.3s/23MiB. Full lower
audit `20261003-141241-25d8f4` passed620/620 constructions throughs8 in
0.9s/37MiB (0.622s algorithm, at most16 points, no SAT calls). The shared
memory refusal and queued recovery are recorded. These are lower-only
checks; no diagnostic or Lean upper receipt is supplied by that job.

Fix strong limit s>=4, global cap limit 2<=R<=s, and ordered zone cap limits
1<=Q<=P<=R. Each zone has cup limit2 and is therefore a cap. Let N_c be the
optional maximum with spanning cup limit c, for c=3 or4. The hand formula is

    N_4 = P+Q,
    N_3 = min(P+Q, 2R-1, 2s-2).

The same maxima are attained with both zones nonempty. This does not force
them to occupy their full diagonal capacities. Requiring P and Q points may
be infeasible for the cup-three profile. Reversing the sweep gives the mirror
formula when the larger diagonal is in the other zone.

## Upper mechanism

The diagonal cap bounds give cardinality at mostP+Q. The classical lemma
that two consecutive full R-caps under global capR force a four-cup excludes
2R; hence N_3<=2R-1. If R<s, this bound is already below2s-2, so the strong
bound adds no loss to the optimum.

When R=s, the critical-root proof in `TWO-CAP-CUP3-PENALTY.md` excludes both
2s and2s-1 under strongs: the former would have two fulls-cap zones, and the
latter one fulls-cap plus an(s-1)-cap. Root endpoint contributions and the
cup-plus-cap coupling exclude every case. Thus N_3<=2s-2. These two upper
arguments remain uncompiled; diagnostic SAT boundaries cannot replace them.

## Lower mechanism

For N_4, restrict the explicit X_R construction toP points of zone0 andQ of
zone1. Restriction preserves decomposability, chain bounds and strong bounds.
X_R has capR/cup4 and strong<=max(R,4)<=s, including theR2/3 bases. It attains
P+Q without introducing new root hypotheses.

For N_3, place a lower P-cap wholly in zone0 and an upper q-cap wholly in
zone1, where q=min(Q,R-1,s-2). Mixed caps extend the upper chain by at most
one lower endpoint, so their size is at mostq+1<=R. Mixed cups use at most
two lower points and one right upper endpoint, so their size is at most3.
The strong root coupling is2+q<=s (or1+q if P=1). This givesP+q points.

This attains the displayed minimum unless R=s and P=Q=s-1. The exceptional
case cannot be attained by that whole-zone root; it requires a nested root.
Take an inner lower s-cap consisting of(s-1) points in zone0 and the first
point in zone1. Add an inner upper singleton as the last point in zone1.
This lower child A has s+1 points, caps, cup3 and strongs. Put an outer upper
(s-3)-cap B between the first and last points of zone1. The full coloring has
(s-1) points in each zone and2s-2 total.

Every three-cup of A ends at its last singleton, so B is inside that cup's
span and cannot extend it to a four-cup. A two-cup can gain at most one B
endpoint: all B points occupy the same gap after the inner lower s-cap.
Thus the full cup rank is at most3. Its cap rank is at most
max(s,(s-3)+2)=s, and its strong root coupling is3+(s-3)=s. Zone1 is a cap
because its two lower endpoints surround all its upper points. This is the
endpoint reason the whole-zone scalar clipping formula loses an extra point.

## Exact profile loss and its limits

For this family, the cross-cup gate loss is

    N_4-N_3 = max(0, P+Q-min(2R-1,2s-2)).

When R<s it is1 only when both zones are fullR. When R=s it is0,1 or2
according as their combined diagonal capacity is at most2s-2,2s-1 or2s.
One loss is the classical endpoint obstruction; the second can come from
critical strong coupling. This is an exact proposed profile capacity law,
not a penalty function for an arbitrary unspecified sibling split.

The pure constructor `two_cap_gate_lower.py` reuses existing cap chains,
X_R, independent endpoint chain tables, literal DS split validation and
strong maximum checks. The pilot checks s=R4,P=Q3, where the nested root is
essential. Failure changes the construction or formula; success supports
the mechanism and provided the timing estimate for the completed general lower audit.
No upper solver, assumed T theorem, new execution framework, or finite
Lean instance is being introduced.
