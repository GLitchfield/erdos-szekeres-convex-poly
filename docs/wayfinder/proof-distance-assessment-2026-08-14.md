---
title: Sober proof-distance assessment
artifact: strategic-assessment
status: snapshot
as_of: 2026-08-14
---

# Sober proof-distance assessment — 2026-08-14

This document is the durable synthesis of the project's initial deep review of
what has actually been proved, what remains open, and where the research
program has been spending effort poorly.  It is a dated assessment, not a
second strategic tracker.  The current authoritative state remains the
[Wayfinder map](map.md) and
[frontier portfolio](frontier-portfolio.md).

## Executive judgment

The project has built a substantial and unusually well-audited formal research
base.  It has a direct planar statement, an exact sweep/orientation model, a
compiling model bridge, the all-parameter sharpness construction, exact small
cases through five, the decomposable upper theorem at five and six, and a large
collection of reusable structural and certificate-checking components.

It has **not** yet closed any load-bearing edge of the unrestricted all-parameter
upper bound.  In particular, it has not proved a uniform predecessor-half
producer, a uniform decomposable induction, or a normalization theorem from
arbitrary realizable configurations to the decomposable class.  Consequently,
it would be inaccurate to describe the project as close to the final
conjecture in ordinary proof-distance terms.

The work has nevertheless changed the search problem.  It has ruled out many
natural local invariants, isolated the first exact decomposable obstructions,
and made the remaining logical alternatives explicit.  That is valuable search
information.  It is not the same thing as a shortened proof.

## What is genuinely complete

### 1. Formal destination and geometric model

The public statement separates the forcing upper bound from the sharpness
witness and combines them in `ErdosSzekeresFormulaAt`.  Swept presentations,
orientation colorings, restrictions, and the equivalence between strong
ordered polygons and convex subsets provide the formal bridge between planar
point sets and the finite coloring language.

This closes the model-selection ambiguity that often invalidates computational
approaches to Erdős--Szekeres.  It does not make arbitrary signotopes or
triple-colorings planar; realizability remains an explicit hypothesis where it
is needed.

### 2. The all-parameter lower/sharpness half

`classical_lower_sharpness` constructs, for every `k ≥ 3`, exactly
`2^(k-2)` planar points in general position with no convex `k`-subset.  This is
one full half of the conjectured equality and is a real destination-level
theorem.

No numerically larger lower bound is compatible with the conjecture.  Future
"lower-bound" work is relevant only when it concerns a structural quantity
consumed by an upper-bound proof.

### 3. Exact small and decomposable cases

The unrestricted public formula compiles at `k=3,4,5`.  Separately,
`decomposableExactUpperAt_five` and `decomposableExactUpperAt_six` establish the
exact upper threshold inside the recursively decomposable class.  The latter
uses kernel-checked finite state certificates and audited semantic bridges.

These theorems validate the formal language and prove nontrivial cases of the
published decomposable-set result.  They do not prove unrestricted
`ErdosSzekeresFormulaAt 6`, and finite agreement at five or six does not supply
the missing uniform transition.

### 4. Conditional route infrastructure

The repository contains compiling consumers for both principal upper-bound
architectures:

- a half-sized predecessor-free support feeds the exact doubling recurrence;
- target-reflecting normalization plus the decomposable theorem feeds the
  unrestricted sweep upper bound.

It also contains many exact restriction, packing, profile, mutation, and
finite-set lemmas.  These make proposed producers precise and cheaply
falsifiable.  A conditional consumer is infrastructure, however, not evidence
that its producer exists.

### 5. Reliable finite evidence machinery

Deterministic encoders, independent semantic checkers, LRAT/RUP replay,
checkpointed Lean certificates, corruption controls, immutable task packets,
and guarded resource limits substantially improve the reliability of finite
experiments.  Several otherwise infeasible exact finite theorems now compile
because of this machinery.

This is a research-system accomplishment.  Solver agreement, certificate
compression, or a smaller proof trace does not itself move the mathematical
destination unless it lands a theorem required by a viable proof route.

## Load-bearing gaps

| Dependency | Current status | Exact missing result |
| --- | --- | --- |
| `D-UPPER` | open | `SweepExactUpperAt k` for every `k ≥ 3`. |
| `D-HALF` | open | A uniform producer of a strong-`(k-1)`-free support containing at least half the vertices. |
| `D-DECOMP` | open | A uniform proof of `DecomposableExactUpperAt k`; only `k=5,6` are closed. |
| `D-NORMALIZE` | open | A target-reflecting, realizability-preserving normalization or well-founded descent to the decomposable class. |
| `D-ASSEMBLE` | gated | Routine once `D-UPPER` closes. |

There are therefore two presently explicit logical routes to the upper bound:

1. close `D-HALF`; or
2. close both `D-DECOMP` and `D-NORMALIZE`.

Neither route currently has its central producer.  Most recent activity has
occurred below `D-DECOMP`, especially in the fixed state-567 and state-578
obstructions.  That work can close finite branches, but a route from those
branches to a uniform theorem remains missing.

## Assessment of the current approach

### What the approach gets right

1. **It respects the model boundary.**  Planar realizability is not silently
   replaced by a stronger abstract coloring conjecture.
2. **It makes false ideas fail concretely.**  Exact rational controls and
   auxiliary-blind checkers have rejected numerous plausible but invalid local
   principles before they entered the trusted proof base.
3. **It formalizes consumers early.**  This often reveals circularity or a
   strategically inert premise before a producer consumes months of work.
4. **It preserves negative knowledge.**  Counterexamples and route expiry are
   durable rather than repeatedly rediscovered.
5. **It has produced real theorems.**  The lower construction, small cases,
   decomposable cases, and several structural reductions are not merely
   experiments.

### Principal criticisms

#### 1. Too much effort has remained inside one mechanism family

Many apparently separate state-567/state-578, packing, residual, occupancy,
and certificate threads are descendants of the same decomposable-Pascal
architecture.  Separate files, agents, or SAT instances do not make their
failure modes independent.  This concentration has made the research program
look broader than it is.

#### 2. Negative refinements have sometimes been narrated as forward progress

A counterexample can improve allocation decisions, and an UNSAT result can
increase confidence in a finite statement.  Neither closes a theorem.  Repeated
claims that the problem has been reduced to a narrower terminal are not proof
movement when the new terminal has no producer or is strategically equivalent
to the old target.

#### 3. Finite certificates have attracted work beyond their mathematical
payoff

Certificate engineering is justified when it lands a named Lean theorem or
tests a frozen semantic-extraction hypothesis.  Repeated proof shrinking,
solver seeds, cube refinements, or kernel-memory experiments without such a
consumer primarily improve tooling.  They should not automatically receive the
next mathematical slot.

#### 4. Conditional interfaces can displace rather than reduce difficulty

Several elegant theorems show that a new producer would imply the desired
recurrence or descent.  If the producer is as strong as the original target,
or restores information discarded by the reduction, the theorem has not made
the proof easier.  Every promoted reduction therefore needs an explicit
before/after obligation set and a strict decreasing measure.

#### 5. Finite-to-uniform extrapolation has been too permissive

A fixed state, a first open value, or a finite family of controls can identify
an invariant.  It supports a uniform route only after a parameterized theorem
uses that invariant beyond the tested instance or after it closes a required
base case in an already-defined induction.  The project has often reached the
former diagnostic stage without the latter bridge.

#### 6. The project lacks an intermediate uniform theorem between the
classical binomial bound and the exact conjecture

The repository proves the classical all-parameter cup--cap upper bound, then
jumps directly to the exact target.  Formalizing a known strict quantitative
improvement could supply a genuine uniform milestone and expose geometric
endpoint machinery absent from the current exact routes.  It would not close
the conjecture, but it would be a more informative intermediate theorem than
another isolated finite obstruction.

## Strategic consequences

1. Maintain a concise dependency ledger separate from the inclusive frontier
   registry, and report the exact changed edge after every run.
2. Reserve `advancing` for a route with recent forward proof movement and a
   theorem-producing next gate.
3. Record mechanism family, scope ceiling, missing generalization bridge, and
   last forward result for every portfolio entry.
4. Limit concentration of an execution slate in one mechanism family unless a
   specific closing proof justifies it.
5. Label slots as proof-producing or information-gathering.  An all-information
   slate is exploration.
6. Apply a finite-to-uniform firewall and stop certificate work that lacks a
   named theorem or semantic-extraction hypothesis.
7. Add attainable but honestly scoped intermediary theorems.  Two candidates
   are an unrestricted Lean proof of `ES(6)=17` and a known strict uniform
   improvement over the classical binomial upper bound.  Their closure would
   be real subordinate progress but would leave universal `D-UPPER` open.

These consequences are now reflected in `AGENTS.md`, the Wayfinder dependency
ledger, and frontier schema.  This assessment remains useful as the rationale
for those rules and as a baseline against which future claims of progress can
be tested.

## Bottom line

The project has moved from an informal open conjecture to a mature formal
research environment with one destination half complete, the model bridge
complete, several exact cases complete, and the remaining upper-bound routes
stated sharply.  That is substantial accomplishment.

The central mathematical difficulty has not yet been reduced: no uniform
producer closes `D-HALF`, `D-DECOMP`, or `D-NORMALIZE`.  Until one of those
changes, the honest description is **better-instrumented search with important
subordinate theorems**, not proximity to a proof of the full conjecture.
