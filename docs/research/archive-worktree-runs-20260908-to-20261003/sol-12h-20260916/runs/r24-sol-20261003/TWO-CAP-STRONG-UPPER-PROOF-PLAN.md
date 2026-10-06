# General two-cap critical strong upper

## Superseded as next target — source check 19:09 UTC

The CLOSED uniform four-diagonal singleton gate
`singletonLowerPascalTailGate_four_diagonal_of_five_le` contains the stronger
one-change two-cup2k-4 argument locally. Its color dual supplies the same
mathematics below. Exporting that already accepted local proof would be a
reuse/public-interface task, not new mathematical understanding. No target
has been registered; R24 now prioritizes the missing general endpoint-profile
gluing interface. The separately proposed triangular consequence is already
a named CLOSED C theorem. Both plans remain historical, with no R24 credit.

2026-10-03 19:02 UTC. Exact target, not yet registered or claimed. Wait for
the strong-avoidance node's finalization/commit before switching branches.

For s>=4, two ordered cap sets P,Q whose union is decomposable, contains
no four-cup and no strong(s+1)-polygon satisfy |P|+|Q|<=2s-2. No separate
cap bound is needed: a cap is strong. Empty zones are permitted. This is the
critical strong upper in TWO-CAP-GATE-FORMULA.md, and directly explains the
extra loss beyond the accepted classical 2s-1 bound. Acceptance of this
unchanged general theorem is the Done criterion; a root classification alone
is not completion.

Search receipts: critical-two-cap-search.json and classical-two-cap-search.json
returned no duplicate. Reuse CLOSED
twoCupBlocks_card_and_extensions_of_oneChange_no_capFour_no_cup
(dac186281844e9ad), color-dualized. Decomposable.dual.turnSequenceAllowed
supplies one-change. Its cardinal and boundary-extension conclusions avoid
the historical recursive classical induction entirely.

Assume contrary cardinal >2s-2. The classical bound and cap<=s force total
2s-1 and zone sizes s,s-1 in either order. Expose a nonempty deep root L/U.

1. If |L|=1, strong gluing gives upper cap rank<=s-1. Apply the classical
   two-cap bound to U: |U|<=2s-3, contradicting total2s-1. Thus |L|>=2.
2. A vacuous two-cup in L now gives upper cap rank<=s-2. Both zones meet L,
   since each has at leasts-1 points.
3. Rule out a whole zone T lying in L. The other V meets U and contributes
   at most two L points by mixed-cap geometry. If |T|=s-1, |V|=s forces
   |V intersect U|>=s-2. If |T|=s, the existing classical full-block
   boundary extension supplies a cap insert p V with p in T. This cap
   meets U and has at most two L points, so |V intersect L|<=1 and again
   |V intersect U|>=s-2. In either case |L|>=s+1; cap avoidance yields a
   lower three-cup, which glues with that upper (s-2)-cap to violate strongs.
4. Both zones are mixed, hence each contributes at most two L points. If
   |L|=4, both contribute two endpoints. Their upper interiors and inner
   lower endpoints form U-L-L-U, a four-cup. Reuse the general endpoint
   argument from TwoFullCapBlocksRootNoninterval as local proof facts;
   no full-zone cardinal or strong hypothesis is used in this step.
5. Thus |L|<=3. The upper cap rank bound<=s-2 and the classical two-cap
   theorem give |U|<=2s-5. Hence total<=2s-2, the required contradiction.

The proof uses exact endpoint placement and local coupling. It introduces
no one-zone T upper premise, solver certificate, tree normal-form assumption
or narrowing of the original critical gate. The explicit general lower is
already a hand construction; a Lean attaining-family constructor remains
separate. Multiple-zone allocation and a universal closed loss invariant
remain open after this two-zone upper.
