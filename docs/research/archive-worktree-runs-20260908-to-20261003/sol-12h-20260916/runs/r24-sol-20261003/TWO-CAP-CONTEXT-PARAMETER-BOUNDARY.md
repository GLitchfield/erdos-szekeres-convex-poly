# Why the literal two-cap context starts at p=5

2026-10-04 00:58 UTC. Direct hand calculation from the retained Context
definitions, not a new kernel theorem or a numerical case. Search receipt:
`two-cap-context-boundary-search.json`. Definitions are in
`ErdosSzekeres/DecomposableContext.lean`, lines 90–138.

Let p≥4, a=k=p+1, u=5, maxima=(1,1,1), and word
S^r 1L 3L 2L S^t with r,t≥1. The two runs may have any finite positive
resolution. Each declared level is present and has lower side. Write the
external positions as x1<x3<x2.

In the accepted actual history, a=p, b=p+1, c=p+2. Construction adds
a,c,b from the core outward; following the tree inward removes b,c,a.
Each inward context part introduces its nearest ancestor as level 1.
Thus at the core a has level 1, c level 2 and b level 3, agreeing with
the literal word above. Addition order and final level order differ.

For endpoints in the left run, a rightward path can use levels (1,2)
or (1,3), but not all three: after x2 the level-3 point is inward. The
pure extension count is therefore 2. Before level 3, levels (1,2) give
two extensions; joining its unit sibling gives join count 3.

For endpoints in the right run, the leftward path (2,3) uses x2 then x3,
so the pure count is also 2. Before level 3 only levels (1,2) are available;
they cannot both move left because x2>x1. Their best count is 1, so its
join candidate is 2. Including the pure candidate, the join count is 2.

For endpoints spanning both runs, every external point lies between the
endpoints. Both outward counts are zero, and each unit-sibling join
candidate is 1. Upper-side extension and join counts are zero throughout,
because all three levels have lower side.

Consequently the exact profile obtained by these definitions is

    Cp = [[p,p],[0,p]],
    Cu = [[min(2,p−3), min(4,p−1)], [0,min(2,p−2)]],
    strong limit = p.

Natural subtraction is used. At p≥5 this is exactly the persistent two-cap
profile: cup diagonal 2 and crossing 4. At p=4 the left diagonal is 1 and
the crossing limit is 3; the profile is different. Thus the geometric
p≥4 constructor does not supply the desired literal context at p=4.
The accepted universal actual-history theorem's p≥5 hypothesis matches
this definition boundary. No p=4 context B equality, literal history or
additional maximum calculation is asserted.

The accepted strong-composition criterion explains the same threshold
geometrically. At the first actual root of this history, the core is below
a singleton sibling. A core four-cup and that sibling's one-cap have sum 5.
They therefore cannot coexist at a root of strong rank at most 4. This
explains why the specified singleton history cannot preserve the desired
p=4 four-cup core, while p≥5 permits that coupling. It is a hand consequence
of the accepted general iff, not a new kernel receipt, and says nothing
about other possible histories. Search: `history-p-five-coupling-final-search.json`.

This explains the general hypothesis and preserves the distinction between
intrinsic abstract profiles, literal context words and occupancy requirements.
It does not prove B attainment, the numerical matrix backend's Lean
equivalence, or the upper threshold.
