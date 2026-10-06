# The finite cut bound constructs optional-profile trees

2026-10-03 16:26 UTC. Hand proof under the audited DS identities and the exact
context extension definitions. Not a new compiled Lean theorem. This is a
lower-construction interpretation; it does not prove the literal context upper
or that the finite cut rule exhausts all decompositions.

Fix legal globals2<=a,u<=k, k>=3 and s=k-1. Assume sigma.WellFormed
with at least one S slot: external IDs are positive and consistent, and
declared maxima are in1..k-2. Retain unused levels interpreted as lower,
exactly as the retained evaluator does. No raw external-level0 extension of
this hand construction is asserted.
Let P(sigma) be its endpoint profile with optional zone occupancy. The proposed
general conclusion, now with the extension argument made explicit, is

    B(sigma) <= N_s(P(sigma)).

The stronger constructive statement assigns every output point to an original
S slot, keeps those slots in sweep order, and attains cardinality B. Empty
slots are permitted. This is why it does not assert required-run or literal
slot occupancy.

## Extension paths lift through a virtual cut

Choose a proper nonempty subset K of the S slots and a kept-child side. The
shared `part` operation leaves K as S, converts the other S slots to external
markers at new level1 with that kept-child side, shifts all older levels by1,
and prepends an opposite-sibling chain maximum m. It preserves the word order.
Each new child run lies in exactly one old parent zone; call this map f.

For an inherited chain, every old extension path is still available after the
shift. If the new level is of the opposite growth type, skip it. If it is of
the same growth type, the extension DP also permits skipping its markers.
The old level maxima and their order are unchanged. Thus the child cap and
cup limits imply the inherited parent limits under f. This includes unused
levels: their default side and declared maximum survive the shift unchanged.

For a lower child, consider a cup of length v with child run endpoints i,j.
Choose any converted S slot x before its first point, and/or y after its last
point. Their parent-zone images are the endpoints of the mixed parent cup.
In the child's extension DP select these one or two level1 markers first.
Then lift any old extension path of the mixed parent chain through the shifted
levels. Relative order is preserved, so this is a valid child extension path.
Writing e=0,1 or2 for the number of selected endpoints gives

    extension_child >= e + extension_parent(mixed endpoints).

For every older strong-join level the e selected markers have already been
counted, hence its child join candidate is at least e plus the corresponding
parent join candidate. The final extension-count alternative has the same
inequality. Therefore the child cup bound implies

    v+e <= Cu_parent[mixed first zone, mixed last zone].

The truncated natural subtraction causes no exception: if the bound is zero
there is no nonempty child chain; otherwise v>=1 forces the relevant parent
limit to exceed the number e subtracted. Taking a maximum over extension paths
only strengthens the implication. For an upper child, exchange cap and cup.

Actual opposite points may occupy any subset of the converted slots and may
expand a slot to many points. A mixed cup/cap uses at most one opposite point
at each endpoint by DS. Its chosen slot is among those the new extension DP
allowed, so the implication remains valid. Empty virtual slots can impose
additional constraints but cannot invalidate a constructed tree.

Finally the new level's join candidate is at least m, even when its markers
are not used as endpoints. Thus the dominant chain maximum of a nonempty
lower child is at most s-m; the upper dual bounds its cap maximum by s-m.

## Induction constructs an attaining tree

Induct on the number of S slots, following an attaining term of the finite
interval/complement recurrence. The maximum is over a finite set. Both proper
parts have fewer S slots, even when one later has bound zero.

At a one-run leaf, the two diagonal limits p,q determine exactly the evaluator's
base. A zero diagonal gives the empty tree; min(p,q)=1 gives a singleton;
otherwise the oracle-free classical/Pascal-band construction in
`BOUND-INTERPRETATION.md` and `q4_bands.py` has size T(p+1,q+1,k), cap<=p,
cup<=q and strong<=s. Assign all leaf points, in their internal order, to the
first retained S slot of that run. The remaining adjacent slots are empty.

At a positive-positive root, let the kept lower part's prepended maximum be
dp, and the upper part's maximum be c=s-dp, as in the retained C recurrence.
The preceding join implication bounds cup(lower)<=c and cap(upper)<=dp.
Root-attach the two recursively constructed trees, then order all points by
their original S slots, retaining each child's internal order. The two parts
use disjoint slot sets, so this placement is well-defined. DS gives

    strong(parent) = max(strong(lower),strong(upper),
                         cup(lower)+cap(upper)) <= s.

Every inherited chain satisfies its parent limit. Every mixed chain satisfies
the one-/two-endpoint implication above. The parent therefore obeys P(sigma)
and has the sum of the two child cardinalities, which is the selected B term.

If a child has B0, discard it. The other child's inherited constraints still
imply the old parent profile, and its strong maximum already obeys s. No
empty DS root is asserted. Both zero gives the admissible optional empty
candidate. This completes the hand construction argument.

## Evidence and remaining formal work

`virtual_cut.py` directly checks the profile implication, conservatively
treating every converted S slot as occupied, for each cut orientation and
coupling share. It reconstructs an attaining B cut using the shared compiled
evaluator and `part`, expands oracle-free leaves, and independently checks
the resulting literal DS coloring, raw endpoint matrices, chain tables and
strong maximum. It makes no SAT calls.

The400-context representative deep sample, job `20261003-122415-4340f4`, passed
39440 child-cut matrix checks and296 positive/104 empty constructions. Its359
selected internal cuts include161 positive-positive glues and198 zero-child
cases. Evidence `virtual-cut-deep400.json`. The first adapter failed because
the existing verifier assumes a nonempty input; v1 and its partial artifact
are preserved, and the repaired empty case checks its exact optional semantics.

Job `20261003-122532-3e1ff9` additionally checked the max-B representatives of
all313 solved shallow k6 profiles across every legal global pair. All17168
child-cut implications and313 constructions passed in4.554s. Their419 selected
internal cuts include325 positive-positive glues and94 zero-child cases;
positive capacities range1..16. Evidence `virtual-cut-k6-profiles.json`.

The kernel already provides the local singleton endpoint, opposite-color
rank-three and strong-transition identities in `RootedChainFootprint.lean`;
adding duplicate singleton corollaries would not advance this obligation.
General extension-path lifting and its positive-limit/coupling consumer are
now fully accepted fa6dacd1; see PART-ENDPOINT-PATH-LIFTING-ACCEPTED.md.
The legal universal threshold lower construction is fully accepted at
aebb6505 after full195602-12b3d3 and independent audits202515-9033b5.
Assigned-limit fixed-root v4 is fully accepted, unchanged
typea89e497ebd1cfbea, commit e0e31525; full203849-0c96ab and audits passed. Stable placement and
fuel induction remain open. At the original probe
date, read-only git metadata prevented a branch switch and no node was added;
subsequent guarded host branch jobs resolved that infrastructure limitation.
The diagnostic checks still do not certify B attainment or matrix equivalence.

The proof explains why a finite B undercount represents missing allowed cut
resolution rather than a union deficiency. It leaves both the sufficiency of
the interval/complement normal form and the general one-zone upper N<=T open.
