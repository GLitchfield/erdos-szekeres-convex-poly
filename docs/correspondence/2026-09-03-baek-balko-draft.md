# Draft: question to Jineon Baek and Martin Balko on Theorem 8 (decomposable sets)

Status: NOT TO BE SENT (decision of 4 September 2026: no external help on
this theorem; see `docs/plans/workstream-b-self-reliant-plan.md`).  Kept as
the most precise record of what is known to break.  Facts below are checked
against the repository at `c74c737` (see the file references).

---

Subject: Theorem 8 of "The Erdős–Szekeres Conjecture Revisited" — how the induction handles children below the binomial window

Dear Jineon and Martin,

I am working on a Lean 4 formalization of the exact Erdős–Szekeres problem
(repository: https://github.com/GLitchfield/erdos-szekeres-convex-poly), and a
central piece is your Theorem 8: every decomposable set of more than
S(a,u,k) = Σ_{i=k−a+2}^{u} C(k−2, i−2) points contains an a-cap, a u-cup, or
k points in convex position. I would be grateful for your help with one step
of the proof, because our transcription of the induction does not close and I
want to know whether the gap is in our reading or in the argument.

**What we formalized.** We use an abstract version of your definition: a
coloring of ordered triples is decomposable if it is a singleton or splits
as A ⊔ B (parts may interleave in sweep order) with A, B decomposable and every
crossing triple colored by the side of its middle vertex (left turn iff the
middle vertex is in A, the "deep below" part). Every such abstract coloring is
realizable by a planar point set (`IsDecomposable.isSweepRealizable`), so the
abstract theorem implies the planar one.

**Where the transcription fails.** Reading the proof as a scalar induction on
(a, u, k) that bounds |P| by the sum of two child contributions, we hit a
boundary case at (a, u, k) = (4, 5, 5) with auxiliary parameters u' = 1,
a' = 3. There a' + u' ≤ k − 1 holds, but the two advertised contributions sum
to 8 while S(4,5,5) = 7 (kernel-checked in Lean as
`published_induction_boundary_regression`). Concretely: P = A ⊔ B with A a
single point deep below a 7-point decomposable set B that has no 4-cap, no
5-cup and no convex pentagon. Any recursion that only knows the children's
parameters bounds |P| by 1 + 7 = 8, but the truth is |P| ≤ 7: the single
point below B extends every 3-cap of B lying on one side of it, and a direct
argument about the 3+4 cup blocks of B closes the case
(`cupBlocks34Force455`). The same arithmetic pattern recurs: an exact census
of the induction's index tuples for 5 ≤ k ≤ 12 finds 1,128 tuples with
positive slack, 660 of them with complementary maximal-index child
cardinalities, of which 652 are not closed by any scalar argument we could
identify; the first is (k, a, u, a', u') = (6, 5, 5, 1, 4) with outer threshold
14 and raw total 15.

**What we know is true.** The theorem itself holds at these boundaries:
kernel-checked proofs of the (a,u,k) statements at (4,5,5), (4,6,6), (5,6,6)
and (4,8,8), and hence of the exact bound for decomposable sets at k = 5 and
k = 6, compile (the 12- and 16-vertex certificates are stated for arbitrary
rank-three signotopes, so they are stronger than the decomposable statement).
So this is a question about the proof, not the theorem.

**One more observation.** Theorem 8 is not a corollary of the split-polygon
theorem: the six points (1,6), (2,44), (3,59), (4,53), (5,50), (6,50) form a
decomposable set with the 4-cap {p1,p2,p3,p6} and the 3-cup {p4,p5,p6}
sharing their right endpoint (a split 5-gon), but with no 5 points in convex
position. So the decomposable theorem needs its own induction, which is why
the boundary matters.

**The question.** In the proof of Theorem 8, when a child of the decomposition
has fewer points than the smallest threshold of the window (for instance a
single point, as above), what invariant is carried across the split? Is the
intended argument a two-parameter recursion on the children with an
additional boundary lemma, or does the induction carry per-vertex information
(such as the longest cap and cup attachable from outside the child)? A pointer
to the relevant lemma in the JCTA version, or to a draft with the full proof,
would resolve this immediately.

If useful, I am happy to share the Lean statements and the census script, and
to credit any correction appropriately in the formalization write-up.

With thanks and best regards,
Gavin Litchfield

---

References inside the repository:

- `ErdosSzekeres/Decomposable.lean`: `published_induction_boundary_regression`
  (arithmetic of the (4,5,5,1,3) boundary), `IsDecomposableOn`,
  `HasDeepBelowSplit`.
- `ErdosSzekeres/PublishedInductionSemantics.lean`: the child-index choice of
  the published proof.
- `ErdosSzekeres/DecomposableRealization.lean`:
  `IsDecomposable.isSweepRealizable`.
- `data/derived/e3-published-offwindow-k20.json` and ticket 0082
  (`docs/wayfinder/tickets/0082-freeze-post0081-rolling-wave.md`, census of
  off-window tuples; 1,128 / 660 / 652 counts for 5 ≤ k ≤ 12).
- Six-point split-pentagon example: verified on 3 Sep 2026 with the repository's
  definitions (decomposable in the x-sweep, no strong 5-set, no convex
  pentagon, 4-cap (0,1,2,5) and 3-cup (3,4,5)).
- Kernel-checked instances: `decomposableExactUpperAt_five`, `_six`;
  `DecomposableStateUpper` at (4,5,5), (4,6,6), (5,6,6), (4,8,8).
