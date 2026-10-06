# Local strong-set composition obligation

2026-10-03 18:38 UTC. General Lean body is drafted but no statement has yet
been registered; wait for current endpoint finalization and commit before
creating its separate node branch. Search for strong avoidance at a deep split
returned no indexed result. Reuse the existing mixed-strong iff and cardinal
cup-plus-cap gluing theorems; do not duplicate their internal geometry.

For every natural s and arbitrary deep-below split L/U, prove the equivalence:

    no strong(s+1) in L union U
      iff no strong(s+1) in L, no strong(s+1) in U,
          and every cup C subset L and cap D subset U has |C|+|D|<=s.

Forward direction is hereditary avoidance plus existing strong gluing.
For the backward direction, a violating strong set wholly within one child
contradicts that child's avoidance. Otherwise its intersections are a lower
cup and an upper cap by the existing iff; disjoint partition gives cardinal
s+1, contradicting the displayed sum bound. Empty chains and empty children
are covered by the same argument. There is no order-separation, one-change,
sweep-realizability or nonemptiness assumption beyond the deep split.

This is the exact root strong-coupling component of DS-COMPOSITION-PROOF.md.
It is reusable in the profile gluing proof and construction induction, but
does not close that entire profile law or compute its loss invariant. Its
Done criterion is acceptance of the unchanged general iff, with original
source/full extraction/axiom/layer receipts, not merely registering a node.
