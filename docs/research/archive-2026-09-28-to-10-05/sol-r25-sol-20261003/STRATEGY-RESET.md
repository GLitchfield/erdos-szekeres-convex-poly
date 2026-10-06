# R25 structural reset, 2026-10-03 15:54 UTC

The proof idea for BDL is still the exact size induction of BDL-OBSTRUCTION.md.
Its only sufficient missing step is BRL on an already partitioned, core-bearing
child with at least three bands. There is no complete proof of BRL.

The cap core is an endpoint-visibility interval. It lets a positioned bottom
band absorb a tight lower child with only one cup endpoint. It is not a small
chain-bearing set: the uniform nested-upper-pair family in section14 can carry
large cups throughout that interval. The bottom band is also not a transversal
of maximum caps: the section13 eleven-point paper counterexample has an open
core and needs a nonempty bottom, yet every cup<=2 cap transversal fails.
Maximum caps may instead cross several higher bands.

The current partitions should be understood as globally coupled choices.
Keeping an arbitrary child partition fixed fails on six points; keeping all
its upper-band points fixed fails on an independently reduced eighteen-point
example. Even on four points, capacity can force a simultaneous swap rather
than any legal one-point move. These explain three distinct failure modes of
the naive exchange idea, without refuting the existence assertion BRL.

Stop commissioning narrower union bounds or endpoint-peeling variants on
this route. The next genuine proof attempt needs either a global simultaneous
exchange with a structural invariant, or an independent construction of the
whole partition. Its test must execute that construction, or expose the exact
conflict graph it claims to resolve. More existence confirmations are useful
only on previously untested hostile inputs; BRL already survives both CH2
counterexamples and the open-core peeling counterexample independently.

Evidence: BDL-OBSTRUCTION.md sections9-15; prefix-obstruction-independent.json;
fixed-extension-independent.json; core-peel-failure-certificate.json;
brl-hard-input-replay.json; frozen-realignment-reduced.json. All finite checks
are diagnostic. No new compiling Lean theorem, proof receipt or commit exists.

## 16:14 update: direct endpoint-source induction

Sections16,18-20 now close several positional root transitions uniformly on
paper. They use which child can supply the first/last point of a maximum cap,
instead of chain counts of a band's union. Interior lower points cannot supply
such endpoints, so the next band's cap limit is safe; cap gain2 gives two free
separated indices. These actual operations passed n7 and are being audited n8.
They leave split exterior anchors and side compatibility unresolved. Tight dual
absorption requests simultaneous core-side choices on a >=3-band child (Q),
an unproved context-compatible hypothesis. This is the current direct proof
direction; the earlier locality counterexamples still apply to a reconfiguration
proof from arbitrary supplied partitions.
