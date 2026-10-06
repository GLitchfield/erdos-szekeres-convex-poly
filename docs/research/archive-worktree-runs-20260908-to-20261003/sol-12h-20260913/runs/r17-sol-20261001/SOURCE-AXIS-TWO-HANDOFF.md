# Existing common-rank helper and the axis-two boundary

23:43UTC accepted update: the closed same-cut singleton-value theorem
ctx_pair_contraction_singleton_value_mono_of_opposite_global_two,
typeef8f2f46dd387851/commita7e7b6b71bc3dbce0b16e459c4103c91b66ccc3a,
covers SOURCE-cut opposite axis<=2 (Lower:a/Upper:u) in arbitrary WF
contexts with>=2runs. It kills the source complement and uses closed
outside-leaf equality or inside two-run leaf monotonicity. It requires those
two leaf inputs; no target-complement monotonicity is claimed. Original
184653-5922f6 and complete-parent184449-42278a passed with standard axioms.
Refined Xff30 uses this case and leaves source-opposite>=3 residuals open.
The forcedflip(a2u4,sourceUpper) examples below have source-opposite u4 and
are OUTSIDE this helper's domain. The prospective common-rank specialization
and general source<=1 claims below remain unregistered/unproved and confer
no additional theorem credit. Distinguish these two axes and boundaries.

Read-only check: `ctx_bound_le_one_of_common_singleton_rank`, module
`ESBlueprint.B.CtxBoundLeOneOfCommonSingletonRank`, is closed, lock-matching,
type `bc11e8e891f68d0b`, standard axioms only. Receipt is retained in
`NODE.common-singleton-rank.readonly.json`. This belongs to the approved base,
not a new R17 theorem or an R16 claim.

Its hypothesis concerns only active children. If the selected global axis
is at most two, a positive point capacity on that axis forces the global
parameter to equal two and both pure extension counts to be zero:

`capLimit p p = min (a-1-leftExt Upper 0 p-rightExt Upper 0 p) (...)`;
the corresponding cup formula uses `u` and `Lower`. A positive minimum and
`a<=2` (or `u<=2`) imply global=2 and leftExt=rightExt=0. Hence every active
child has the same available singleton rank `r=1`, satisfying both rank
equations of the closed helper. With global zero or one the active premise
is impossible, so the rank implication is vacuous.

This suggests an immediate specialization: for positive external labels and
either global axis at most two, every fuel bound and full bound are at most
one. The helper also annihilates a part on that small axis whenever it omits
an originally active child. This specialization has not been registered or
checked as a new Lean declaration; it receives no additional theorem credit.

For X, positive labels follow from its one-level letter premise. The closed
singleton threshold identity and `ctx_bound_cut_le` would then bound every
legal source singleton sum by one (using the singleton block and two runs).
The remaining exchange on the positive-axis/opposite-two boundary becomes:
if the source sum is one, some legal target cut at the specified mapped child
has value at least one. A zero source needs only a legal target cut.

The fixed mapped child remains essential. A bound on the entire shorter root
or an attaining cut at some other child does not establish this exchange.
No target nonzero implication or universal selector is claimed here.

At 2026-10-01 21:43 UTC, the running all-axis extension supplies a finite
obstruction to preserving the source orientation on this boundary. For
`a=2,u=4,k=6,m=1`, word `S,S,S,1L,S,1L`, contraction at `y=0`, and source
child `p=1` mapping to `q=0`, the Upper source cuts with `c=2,3,4` each have
value 1. Every Upper target coupling `d=1,2,3,4` has value 0; every Lower
target coupling has value 1. The mirror word `1L,S,1L,S,S,S`, `y=4,p=q=4`,
has the same values. Thus merely choosing another coupling on the source
side cannot prove the remaining positive-target implication, even when the
source is bounded by one. Allowing a side change rescues these witnesses.

The first six records are preserved in
`extended-five-child.axis2-forced-orientation.first6.jsonl`, together with
`extended-five-child.axis2-forced-orientation.checkpoint-2143.json`.
These are independent explicit target-value audits by guarded job
`20261001-164852-b388fe`; they are not a new Lean certificate or a
counterexample to X. The full sweep remains running. Completed-axis common
cells are nonempty; current-axis intersections are only final at axis end.

The closed proper-part large-maximum helper is distinct: it allows the
omitted child to be inactive and kills parts on either side, with arbitrary
new maximum, under an indexed old maximum at least k-2 and opposite global
at most two. Its extracted R16 argument has no multi-run premise. It is now
closed commit `1edc5c9ff9ef7856bc45cc9d575c41eb31b62804`, type5818b07d53e26989,
Std/noholes/lockmatching, originaltargeted175912-d53273 passed51.5s/2345MiB/20G,
with releasedclosed claim. Source is `proper-part.closed-source.txt`.
This does not certify a general positive-target implication at lower maxima.
