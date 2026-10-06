# Classical two-full-cap induction

## Superseding source finding — 2026-10-03 18:59 UTC

This obligation already follows from the stronger CLOSED theorem
`twoCupBlocks_card_and_extensions_of_oneChange_no_capFour_no_cup`,
type `dac186281844e9ad`, standard axioms only. For any two ordered caps
with no four-cup and no (r+1)-cap, apply it to the color dual at u=r+1.
The cardinal conclusion is |Z0|+|Z1|<=2r-1, contradicting two full r-caps.
For a decomposable coloring, `hdec.dual.turnSequenceAllowed` supplies the
required one-change law definitionally. No additional induction theorem
or node should be created. Its boundary-extension conclusions are also
available for the critical-strong gate. The historical hand induction
below remains useful geometric intuition, but is superseded as a proof route.

2026-10-03 18:29 UTC. Hand proof plan; no new Lean acceptance. This supplies
the missing classical upper in TWO-CAP-GATE-FORMULA.md without a strong-set
hypothesis. The statement is: for r>=1, two disjoint ordered full r-caps
covering a decomposable set that has no (r+1)-cap force a four-cup. For r1
the assumptions are contradictory. For r2, no triple is a cap, so all four
points form a cup.

At r>=3 argue contrapositively assuming no four-cup, and expose a nonempty
deep-below root L/U. Both cap blocks meet L: if
one were entirely U, any L point in the other block is an outside sweep
endpoint and extends that r-cap to r+1.

First prove that both blocks also meet U; this cannot be inferred directly
from the intersection bound, which itself requires U nonemptiness. If block0
lies wholly L, the other block is mixed and its L points are endpoints.
If its first endpoint is L, the full lower r-cap plus that endpoint cannot
be an (r+1)-cap, hence contains a three-cup ending there. Any U point in
block1 lies to its right and extends it to four. Otherwise only the last
block1 endpoint is L, and its upper (r-1)-cap is bracketed by that last point
and any L point from block0, yielding an (r+1)-cap. The mirror handles block1
wholly L. This preliminary phase is necessary; omitting it would be circular.

Now existing cap-intersection geometry bounds each L intersection by two
and says its points are block endpoints. Each block has root state F (first
only), E (last only), or D (both). Both U intersections are nonempty.

| lower states | contradiction or reduction |
|---|---|
| E,F; E,D; D,F; D,D | Upper point in block0, last lower point in block0, first lower point in block1, upper point in block1 form a four-cup. |
| F,E; F,D; D,E | Two outer lower endpoints bracket an upper (r-1)-cap from a block with singleton lower intersection, giving an (r+1)-cap. |
| F,F | First lower point in block0 lies before all U. Any r-cap in U extends to r+1. U consists of two ordered (r-1)-caps; apply induction. |
| E,E | Last lower point in block1 lies after all U; the symmetric induction applies. |

The four-cup uses only the crossing rule: every mixed ordered triple has
middle point in L. The cap extension reuses the already CLOSED general
`deepSplit_two_endpoint_extensions` theorem, rather than adding a duplicate
helper. The two recursive cases use decomposability of U and hereditary cap
avoidance strengthened by the outside lower endpoint. Induction decreases r,
so there is no search or unproved tree-normal-form assumption.

The compiled R24 root-structure theorem uses critical strong avoidance to
force D,D outright. This classical induction addresses the larger class
without that bound. Its acceptance would justify the 2R-1 upper for cup3;
the additional critical-strong loss and arbitrary multiple-zone allocation
remain separate obligations.
