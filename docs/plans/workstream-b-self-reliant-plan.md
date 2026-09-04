# Workstream B without the authors: a self-reliant plan for the decomposable-set theorem

Decision of 4 September 2026 (Gavin): do not write to Baek and Balko; there
is no reason for them to share intermediate results with a group that might
scoop a proof they are working on.  The email draft in
`docs/correspondence/` stays unsent.  This plan replaces step B.1 of
`research-plan-2026-09-03.md` and sharpens B.2–B.4.

## What we are trying to prove

Theorem 8 of Baek–Balko: every decomposable set of more than
`S(a,u,k) = Σ_{i=k−a+2}^{u} C(k−2, i−2)` points contains an `a`-cap, a
`u`-cup, or `k` points in convex position.  In the repository this is
`∀ a u k, DecomposableStateUpper a u k` over the abstract decomposable class
(`IsDecomposable`, `HasDeepBelowSplit` in `Decomposable.lean`), which is at
least as strong as the planar statement because
`IsDecomposable.isSweepRealizable` realizes every abstract member.

## What we already know, and will not redo

- The literal scalar `(a,u,k)` recursion does not close.  First failure
  `(a,u,k,u',a') = (4,5,5,1,3)`: the two child contributions sum to 8 against
  the threshold 7 (`published_induction_boundary_regression`).  The
  off-window census through `k = 12` lists 1,128 index tuples with positive
  slack, 652 not closed by any scalar argument
  (`data/derived/e3-published-offwindow-k20.json`, ticket 0082).
- The theorem is true where the recursion fails: kernel-checked at
  `(4,5,5)`, `(4,6,6)`, `(5,6,6)`, `(4,8,8)`, and the exact bounds
  `decomposableExactUpperAt_five` and `_six`.  The first `k = 7` obligation
  (state 567) is reduced to two 22-point packing statements that are UNSAT
  computationally but not in Lean.
- The theorem is not a corollary of the split-polygon theorem (six-point
  split-pentagon example), so it needs its own induction.
- August's state-by-state charging work (tickets 0063–0073, 0106) conserved
  token mass but never paid a strictly smaller Pascal resource.  Nothing in
  this plan funds another state.
- Most extremal `k`-gon-free sets are not decomposable (experiments 0107,
  0108), so this theorem is a parameterized target in its own right, not a
  route to the conjecture.  That bounds how much it is worth: a uniform
  proof or a written obstruction, inside eight weeks, and nothing beyond.

## The working hypothesis

The boundary failure is an external-endpoint effect: a vertex deep below a
subtree extends every cap of the subtree lying on one side of it, and such
vertices stack across tree levels.  A correct induction hypothesis must
therefore carry, per child, more than `(a', u')`.  The candidate state is
per-vertex: the longest cap and the longest cup that can be attached to the
vertex from outside its subtree, on each side.  Call a candidate hypothesis a
*profile bound*: a function `B(a, u, k, π)` of the parameters and the profile
`π` that (i) equals `S(a,u,k)` for the trivial profile, (ii) is additive
across a deep-below split up to the external extension, and (iii) holds on
every small decomposable coloring.

## Steps, cheapest first, each with a falsifier

1. **Exhaustive small worlds (Week 2).**  Generate every decomposable
   coloring on `n ≤ 9` vertices by the tree grammar (children plus an
   interleaving, crossing triples colored by the deep-below side), up to the
   symmetries of the class, and for each vertex record the external cap and
   cup attachable on each side.  Deliverable: a table of profiles against
   the presence of `a`-caps, `u`-cups, and strong `k`-sets for all small
   `(a,u,k)`.  Falsifier: if profiles do not separate the `(4,5,5,1,3)` boundary
   cases from the rest, the hypothesis is wrong and step 2 changes.
2. **Invariant search (Weeks 2–3).**  Over a small grammar of candidate
   profile bounds (window sums shifted by the external cap and cup lengths,
   per side), test the three properties above mechanically on the step-1
   data and on the existing all-root census (186,888 eight-vertex colorings
   at `k = 6`, the `k = 7` roots).  A candidate that is additive across every
   observed split and never violated is the induction hypothesis to try; the
   exact additivity failures of the losers are the negative record.
3. **Paper proof of the boundary family (Weeks 3–5).**  Prove the surviving
   profile bound by hand for the family of tuples with positive slack,
   starting with `(4,5,5,1,3)` where the direct argument
   (`cupBlocks34Force455`) is known.  A weekly one-page state of the
   argument, same format as Workstream C.  Stop signal: a small decomposable
   coloring that satisfies the bound's hypotheses and violates its
   conclusion; step 1 makes such a search a one-line query.
4. **Lean, one theorem (Weeks 5–8).**  Formalize the profile bound as a
   single parameterized theorem in the abstract class, with
   `DecomposableStateUpper` and `decomposableExactUpperAt_k` as its named
   consumers and the step-1 checker as its falsifier.  State 567 and
   `(5,7,8)` are instances of it, not separate targets.
5. **If it fails (Week 8).**  Write the note: the theorem is kernel-checked
   through `k = 6`, the literal induction does not close, here is the exact
   boundary, here is the realization lemma.  Keep it internal until Gavin
   decides whether and when to circulate it; it reveals a gap that others
   could also try to close.

## Computation budget and rules

- Steps 1 and 2 are exhaustive enumeration and table checks: single-core
  Python under `systemd-run` caps, no solver time, no Lean.
- No SAT certificate is funded for B unless step 4 needs exactly one base
  case that step 3 cannot close by hand.
- Every negative result is a paragraph in the weekly note.
- No external correspondence on this workstream.

## What success looks like

A compiling `theorem decomposableStateUpper (a u k) : DecomposableStateUpper a u k`
with a profile-carrying induction, or, failing that, a precise written
statement of why the induction cannot be repaired within the class, with the
exhaustive small-world tables as evidence.  Either is publishable on our own
terms and on our own schedule.
