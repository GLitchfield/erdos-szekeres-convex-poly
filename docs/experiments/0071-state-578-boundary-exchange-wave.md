# Experiment 0071: state-578 boundary-exchange wave

Date: 2026-08-09

Status: Outcome 2 — compiling structural advance; terminal exchange still open

## Question

Can the four-owner private-cup star and six disjoint four-caps construct the
`PrivateCupBoundaryExchange578` required to replace `4r` protected transversal
vertices by at most `3r` boundary vertices?

The exact terminal consequence was already compiled: such an exchange would
give a four-cup transversal of cardinality at most nine, contradicting the
`32/23` density lower bound of ten.  This experiment isolates and advances the
missing collective tree/orientation step.

## Bounded matrix census

An ignored deterministic producer enumerated all `3^10 = 59049` normalized
row/column direction assignments for a `4 × 6` prefix-chain address matrix.
Among the `30100` assignments using both strict directions, the minimum number
of cells at the common minimum was eight.  An independent checker enumerated
90 count profiles and rechecked all 16 extremizers.  These scripts and their
JSON result are under `runs/state578-exchange-matrix/`; they are advisory
computation, not proof evidence.

The part promoted to Lean is more structural and does not trust the census:

- every row/column prefix-chain matrix has a globally minimal cell;
- opposite strict directions force both cross-corners back to that minimum;
- the whole matrix is therefore left-only, right-only, or contains such a
  collapsed cross rectangle;
- a strict step after the common minimum localizes the complete cup--cap union
  in the corresponding child.

The numerical eight-cell bound remains computational evidence only because no
downstream theorem currently consumes that stronger count.

## Boundary exchange and carriers

Lean now treats all full selected cups, not merely one chosen spine.  If `r`
selected cups are wholly contained in the owner transversal, their union has
exactly `4r` vertices and the transversal has at most `9+r` vertices.  The
remaining four-cups are represented by an exact residual family.

For every full spine, the spine plus one private cup is a seven-vertex carrier.
In the absence of a five-cup, every family of four-cups local to such a carrier
has a transversal of at most three vertices.  Choosing one local boundary per
full spine and taking their union costs at most `3r` vertices.

Density proves that this union cannot hit the entire residual family.  The
missed residual cup:

- meets the protected union;
- is disjoint from the total local boundary;
- escapes every old seven-vertex spine/private-cup carrier;
- meets some full spine while containing a vertex outside that spine's old
  carrier.

This is packaged as `ExpandingFullSpineCarrier578`.  It is the first compiling
exchange-wave invariant which works uniformly for one, two, or three full
spines.

In the tight one-spine branch, four owner-indexed partial exchanges also
produce a new residual-cup ledger.  Lean proves those four cups cannot all
collapse to one witness.  Their pairings with the same six disjoint caps form
a second `4 × 6` address matrix with prefix-chain rows and columns, a global
minimum, the one-sided/cross-corner trichotomy, and strict-child localization.

## Autoprove result

The exact local-boundary escape statement was probed with goal extraction,
hammer premise search, state search, `aesop`, `simp_all`, `omega`, and `grind`.
No automated attempt closed it: premise search was irrelevant, broad `aesop`
hit its heartbeat limit, and `grind` stopped before the density construction.
An explicit project-local proof using the nine-vertex candidate, the compiled
density theorem, and residual-family membership now compiles.  The ignored
probe imports and checks that final theorem.

## Outcome and next obstruction

This is Outcome 2.  The exchange route is not closed or refuted.  It advanced
from one static private-cup star to an iterative phenomenon: every complete
collection of local three-boundaries forces a new residual cup outside every
old carrier.  The exact gate now exposes both that expanding carrier and a
second residual-cup/six-cap address matrix.

The next theorem must couple carrier expansion to the six-cap address matrix.
The promising alternatives are:

1. prove that repeated expansion forces enough distinct vertices or cups to
   exceed the 32-vertex reservoir; or
2. use the one-sided/mixed address trichotomy and six-cap child capacity to
   force a forbidden strong eight-set or complete the global `3r` boundary.

Independent pair classifications, common addresses without direction, and
incidence-only counting remain expired.

## Formal evidence

- `ErdosSzekeres/StructuralChargingNextState578BoundaryExchange.lean`
- `lake build ErdosSzekeres.StructuralChargingNextState578BoundaryExchange`
- theorem and source axiom scans recorded in the integration run
