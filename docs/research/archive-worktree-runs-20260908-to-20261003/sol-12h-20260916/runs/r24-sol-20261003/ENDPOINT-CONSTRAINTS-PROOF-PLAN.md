# Exact endpoint constraints at a deep split

2026-10-03 19:11 UTC. General target, not yet registered. Search receipts
endpoint-constraints-search.json/root-chain-characterization-search.json
and source search across every workstream found no matching theorem. Reuse
the existing opposite-child sweep-endpoint necessities and color duality.

Let cupAllowed and capAllowed be arbitrary predicates on finite vertex sets,
and let L/U be an arbitrary deep-below split, including empty children.
Then every parent cup/cap satisfies its predicate iff:

* every cup wholly in U satisfies cupAllowed;
* every cap wholly in L satisfies capAllowed;
* every cup C in L with any subset E of U consisting of sweep endpoints of
  C union E satisfies cupAllowed(C union E);
* every cap C in U with any subset E of L consisting of sweep endpoints of
  C union E satisfies capAllowed(C union E).

There are no nonemptiness, one-change, realizability or threshold hypotheses.
Empty C/E are retained. Endpoints are of the entire union; allowing endpoints
only of C would incorrectly admit two inserted points on the same side.
The predicate form applies to arbitrary endpoint matrices without defining
a new N implementation or choosing an unproved leaf threshold.

Forward: a lower cup plus upper union endpoints is a cup. In each ordered
triple the middle point cannot be in E, since it would have points on both
sides. Wholly-C triples use the cup hypothesis; other triples use the deep
crossing rule with middle lower. Color duality supplies the cap statement.
Apply the parent predicate. Wholly-upper cups/wholly-lower caps are hereditary.

Backward: a parent cup missing L lies in U. Otherwise split it into its
intersections with L/U: the first is a cup and every point in the second
is a sweep endpoint by the accepted necessity lemma. The intersections
partition the set, so the displayed mixed constraint applies. The cap
argument is the color dual, using its existing lower-endpoint necessity.

Together with deepSplit_strong_avoidance_iff this certifies the cup/cap/strong
constraint components of exact DS profile gluing. Joint sub-zone placement,
occupancy allocations, finite maxima and a closed loss invariant are still
separate. Done means unchanged general equivalence accepted by original
source/full extraction/audits/review and committed, not registration.
