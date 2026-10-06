# A closed sibling loss for the persistent two-cap root pattern

2026-10-03 21:00 UTC. Hand mathematical consequence of the accepted local DS
interfaces and existing general two-cap construction. No new Lean receipt,
no computation/census. This illustrates one pattern; the general closed loss
invariant remains open.

Fixp>=4, two original ordered zones, cap matrix constantp, cup diagonal2 and
crossing4, strong limitp. Fix root lower cup coupling alpha2 and upper cap
coupling beta=p-2. Its occupied order pattern in EACH original zone is

    a nonempty lower left flank | an upper interior | a nonempty lower right flank.

Precisely, choose the ABBA row from DS-COMPOSITION-PROOF.md in each zone:
the upper interior has at least2 points, and the two lower flanks are
nonempty. The row also permits an optional lower central region between
the upper's first/last points. Retain this optional region in BOTH baseline
and refined states; refinement will prohibit it. Optional gaps in the four
lower flanks may contain additional lower points before gain constraints.
This is not a fixed four-point ambient support.

## Same coupled baseline, before endpoint gains

The lower's cup coupling<=2 makes it globally cap-colored. Its global cap
limitp bounds its total byp. A p-cap distributed over the four required
flanks attains this, with at least one point in each; henceN(D_L)=p. It is
nonempty/decomposable and avoids strongp+1 by total cardinality.

The upper retains two cap-colored zones and global cap coupling<=p-2. Their
sum upper is2p-4. The existing two-cap construction with parameterq=p-2
attains that cardinality, cup<=4 and strong<=max(4,q)<=p. Its baseq2/q3
ingredients are exactly those in two_cap_blocks.py. ThusN(D_U)=2p-4,
includingp4/p5. Required first/last distinction is satisfied sinceq>=2.

## After opposite endpoints

Every lower flank sees an upper point in the SAME original zone strictly
outside every chain contained in that flank. A lower two-cup would gain that
upper endpoint and make a forbidden three-cup within the original zone.
Therefore each flank has cup rank<=1 and contains at most one point.
In either optional lower central region, a chain can gain both opposite
endpoints inside the same original zone, so its cup bound becomes2-2=0.
These central regions are empty. The retained four positive flank
occupancies force exactly four lower points.
Those four can be a cap; cap limitp>=4 and coupling cup<=2 allow it.
SoN(P_L)=4.

For the upper, inherited cap limitp can be reduced by at most two lower
endpoints to p-2. Its already-retained coupling beta=p-2 dominates every
one/two endpoint gain in either zone or across them. Upper cup limits are
inherited unchanged. ThusN(P_U)=N(D_U)=2p-4. The four lower singleton flanks
and the constructed upper glue by the DS middle-child rule, attaining2p.
Their parent cups have rank<=2+2=4 and strong coupling2+(p-2)=p.

The endpoint penalty relative to THIS SAME coupled/occupied baseline is

    Pi = [p-4] + [(2p-4)-(2p-4)] = p-4,
    root contribution = p+(2p-4)-Pi = 2p.

This is not the one-point interval-bound error B<=2p-1. B misses an admissible
root pattern; the loss above compares that pattern's own children before and
after endpoint gains. It also excludes the additional coupling losses needed
for an uncoupled baseline. No claim about arbitrary profiles' scalar maxima
or a closed general N formula follows.

## Formal status and next question

The local strong iff, finite endpoint iff and independent-color gluing are
accepted. Universal two-cap attainment is fully accepted9dd71f32,
type13c4148cbefaef7f; TWO-CAP-FAMILY-ACCEPTED.md pins isolated/full checks,
audits and exact review. Its universal actual-history extension is accepted
0930d3c7, type1c941c8bec8aa44a. The profile maxima/equalities here are hand statements,
not new kernel theorem credit. The general problem remains: identify a
profile invariant that expresses these forced singleton flanks and the other
endpoint-induced losses without recursively solving both child maxima.
