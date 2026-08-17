---
title: Review the HMPT H2 route after two non-forward outcomes
type: research
mode: AFK
status: closed
claim: codex-hmpt-h2-route-review-2026-08-17
blocked_by: none
---

# Ticket 0024: review the HMPT H2 route after two non-forward outcomes

## Question

After ticket 0022's kernel-refuted `r = 2` contract and ticket 0023's
inadmissible positive fixture, does a genuinely theorem-first bridge justify
one third `FP-15.C` H2 attempt, or should the mechanism family be suspended?
In particular, do the unchanged inputs imply C2's outer-anchor vertical
profile theorem and C3's distinct-anchor adjacent gluing theorem without a
supplied coloring, maximum, support certificate, convex union, common `x2`
cap, changed carrier, or target-equivalent premise?

This is the mandatory mechanism-family review after two consecutive
negative/information-only outcomes. It does not itself authorize another
fixture repair or the full C1--C4 slate.

## Review method

Three independent read-only lanes audited the exact frozen interfaces and the
authenticated HMPT source:

1. a complete C2 theorem-derivability audit;
2. a complete C3 mixed-four-subset and falsifier audit; and
3. a route-innovation audit comparing H2 completion with possible consumers
   into `D-HALF`, `D-DECOMP`, and `D-NORMALIZE`.

A separate bounded Sol/Fable review then received the H1 interfaces, ticket
0023, the authenticated source passage, and the relevant compiled Suk
geometry, recurrence, and gluing modules. The three task results pass the
repository slate validator. None of these read-only analyses is a Lean proof.

Review artifacts:

- agent slate:
  `runs/agents/20260817-hmpt-h2-route-review/slate-v2.json`, SHA-256
  `a828efe151a763c1621664a85bd91882e47ccde35a0b08a55a97a32d5469ebbe`;
- C2 result SHA-256
  `45dc70b90e61e2a445de1b3d722f64516b764e38bb7a3369b743e0d418359b62`;
- C3 result SHA-256
  `b8bb6922ba5d6c71bd0668c5b5153d47c5b46eb015ff78275e02aec4ff2a5e62`;
- route-innovation result SHA-256
  `471f60f1a8b3bbcfa5c12deebb3873e1fd7896db2d1752acc277122ce26c496c`;
- advisory report:
  `runs/reviews/20260817-hmpt-h2-route-review/provider/REPORT.md`, SHA-256
  `b24015f838f0a48ff13547dc5de48738800d9c54e5a2ed768e06a6fb88548258`.

## Decision criteria

Retain H2 only if the frozen raw interfaces yield a theorem strictly smaller
than C2 or C3, with an immediate consumer and no target-equivalent premise.
Another fixture, finite pass, conditional certificate, or restatement of C3
does not qualify. The review must instead recommend suspension if it finds a
valid counterexample, a missing raw premise, no bounded theorem gate, or no
credible closing mechanism. Any retained gate must state its exact theorem,
falsifier, trust boundary, stop conditions, and load-bearing consequence.

## C2 finding: no mathematical premise gap

The frozen C2 theorem has a noncircular proof graph from the unchanged
`SukRegionGeometry` input.

- Strict HMPT vertical order is reverse strict `SukRegionLT`. This follows
  from the compiled triangle-containment equivalence, base positivity,
  general position, and antisymmetry; it introduces no totality premise.
- In strict HMPT direction, every pair has positive orientation at
  `outerLeft` and negative orientation at `outerRight`. Consequently a
  negative triple extends `outerRight` to a convex quadruple, and a positive
  triple extends `outerLeft`, with converses from general position.
- HMPT-direction four-point transitivity follows by reversing the ordered
  quadruple, applying the compiled Suk transitivity theorem, complementing the
  orientation color, and reversing the two conclusions.
- The H1 consumer supplies actual maximum vertical and horizontal chains.
  The two actual cardinality-maximum outer-anchored subchains can be chosen
  internally from a filtered powerset; they are not inputs.
- Put `T := hmptChainPoints verticalChain` and use forward `SukRegionLT` on
  `T`. The vertical chain makes that order total. In this forward order the
  raw negative/right color means an `outerLeft` cap and the raw positive/left
  color means an `outerRight` cap.
- Invoke the generic lower-level `sukRegionChain_twoColor_cup_or_cap` with
  anchor parameters `(outerLeft, outerLeft, outerRight, outerRight)`,
  `rightSize = leftChain.card + 1`, and
  `leftSize = rightChain.card + 1`. Its threshold is exactly
  `choose (L + R - 2) (L - 1)`. This is a free-anchor use of the generic
  recurrence; it does not construct the impossible repeated-anchor
  `SukRegionGeometry` object.
- The recurrence output transports back to the unchanged maximum vertical
  chain and contradicts one of the two anchored cardinality maxima. Vertical
  cardinalities zero, one, and two close separately; at cardinality at least
  three both maxima have size at least two.

The remaining C2 risk is Lean visibility, subtype/finset transport, and
small-cardinality normalization. It is formalization work, not an identified
missing mathematical premise. C2 remains proposal-level until its exact
declarations compile.

## C3 finding: the distinct anchors are derivable

The common-`x2` public certificate is not applicable: the left profile's
selected chain is capped at `x3`, while the right profile's selected chain is
capped at `x1`. The review instead derives the needed signs directly.

For an HMPT-vertically increasing left pair `a <ᵥ b` and any right-pool point
`q`, the frozen raw adjacent geometry implies

```text
orientation a b x3 < 0  and  orientation a b q < 0.
```

The first sign is the outer-right component of the compiled vertical-order
sign characterization. The second is a signed port of the compiled
Plücker/wedge transport: the right-pool point lies in the same positive wedge
from each left point, and triangle containment transports that wedge sign to
the line through `a,b`. Reflectively, for an increasing right pair and a
remote left point, both orientations at `x1` and at the remote point are
positive. Only five-anchor signs, the two raw support-region memberships,
vertical comparability, and general position are used.

These signed pair transports close every mixed four-subset pattern:

- three left plus one right uses line-arrangement-cell replacement from `x3`;
- three right plus one left uses replacement from `x1`;
- two plus two obtains strict support in both opposite-pair directions; and
- four points from one pool inherit convexity from the profile cap.

The existing four-subset characterization then proves the whole selected
union convex. No valid ordered-field falsifier survives these sign
implications. This too is a proposal until Lean checks the exact theorems.

## Adversarial disposition

Both Sol/Fable reviewers converged after critique on the same bounded
disposition:

1. **Retain for one theorem-first attempt.** Do not rerun or perturb ticket
   0023's fixture and do not launch the full C1--C4 slate.
2. **Use the signed C3 pair transport as the first and decisive gate.** It is
   smaller than C3: three pool points, no profile, maximum, union, or convexity
   conclusion. Its immediate consumers are exactly the C3 `3+1` and `2+2`
   cases.
3. **Suspend automatically** if the gate is falsified, needs a premise absent
   from raw adjacent geometry, compiles only through a supplied certificate or
   common-`x2` cap, or terminates with only fixture/resource information.

The secondary C2 outer-anchor semantics is also well supported, but it is not
the cheapest first gate because a complete profile still carries maximum
selection, recurrence transport, and small-cardinality bookkeeping.

The route-innovation lane recommended immediate quantitative-H2 suspension
and identified one different speculative idea: aggregate the 2413/3142
nonseparable patterns in all chirotope-defined HMPT ranking contexts as a
mutation rank for `D-NORMALIZE`. That idea has a named conditional consumer,
but no rank-zero characterization or radius-three descent theorem. It is
preserved as an unselected proposal, not promoted to the frontier and not used
to claim exact-route progress. It requires a separate bounded review before
any execution.

## Evidence

The C2 and C3 conclusions below are supported by complete proof graphs over
the cited compiled APIs and by the authenticated source passage. The
Sol/Fable report independently challenged order direction, anchor meaning,
pair-side transport, recurrence arithmetic, and proof-distance accounting,
then converged on the same signed-pair gate. These are proposal-level sources;
only a later warning-clean Lean declaration can establish the theorem.

## Exact next theorem gate

One later approved proof packet may freeze the following mathematical
content, with binder order adjusted before packet freeze but no stronger
premise:

```lean
theorem HMPTAdjacentSpikeGeometry.leftPair_orientation_neg
    (h : HMPTAdjacentSpikeGeometry
      x0 x1 x2 x3 x4 leftPool rightPool)
    {a b q : Point 2}
    (ha : a ∈ leftPool) (hb : b ∈ leftPool) (hq : q ∈ rightPool)
    (hv : HMPTSpikeVerticalLT x0 x3 a b) :
    orientation a b x3 < 0 ∧ orientation a b q < 0

theorem HMPTAdjacentSpikeGeometry.rightPair_orientation_pos
    (h : HMPTAdjacentSpikeGeometry
      x0 x1 x2 x3 x4 leftPool rightPool)
    {a b q : Point 2}
    (ha : a ∈ rightPool) (hb : b ∈ rightPool) (hq : q ∈ leftPool)
    (hv : HMPTSpikeVerticalLT x1 x4 a b) :
    0 < orientation a b x1 ∧ 0 < orientation a b q
```

The proof must port only the required private wedge and triangle-transport
lemmas into a new owned module. A frozen admissibility-checked rational
falsifier may run in parallel, but a green finite control is not acceptance.
Acceptance requires both exact declarations to compile warning-clean, a
targeted module build, and declaration-only axiom audits containing only
`propext`, `Classical.choice`, and `Quot.sound`.

Predeclared outcomes:

- `HMPT-H2-PAIR-LAND`: both signed theorems compile and pass the stated trust
  gates;
- `HMPT-H2-PAIR-FALSIFIED`: an admitted exact Euclidean GP fixture contradicts
  either theorem;
- `HMPT-H2-PAIR-GAP`: an unchanged raw field does not imply a required sign;
- `HMPT-H2-PAIR-INERT`: only a supplied certificate, common anchor, or
  target-equivalent shell compiles; or
- `HMPT-H2-PAIR-RESOURCE`: the bounded proof gate stops without a theorem.

Every non-`LAND` terminal suspends active H2 work. `LAND` is a genuinely new
positive theorem and may justify a later decision on full C3, but it does not
by itself change H2's official five-layer count.

## Resolution and proof-distance accounting

Closed with outcome `HMPT-H2-ROUTE-RETAIN-ONE-GATE`.

**Net proof movement:** neutral. **Evidence:** authenticated source, three
independent theorem/route audits, and bounded Sol/Fable advice; no new Lean
declaration. **Difficulty displaced:** no difficulty is moved into a premise.
The review decomposes C2 and C3 to existing compiled machinery plus explicit
local sign theorems, but C1--C4 all remain kernel-open. **Counterfactual:**
knowing these bridges earlier would have prevented the common-`x2` route and
the broad fixture-first slate and would materially lower the estimated C2/C3
implementation risk; it still would not prove H2 or the exact formula.
**Planning consequence:** retain `FP-15.C` as gated for exactly the signed-pair
theorem attempt above, then suspend on any non-`LAND` result. Do not schedule
the full H2 slate from this review alone.

The finite H2 open-layer count remains five. `D-HALF`, `D-DECOMP`, and
`D-NORMALIZE` remain unchanged, and no load-bearing exact-conjecture ledger
edge changes.

## Authorized successor outcome (2026-08-17)

The one theorem-first successor authorized by this ticket closed with
`HMPT-H2-PAIR-LAND`.  The new module
`ErdosSzekeres/HMPTAdjacentPairTransport.lean` proves both frozen declarations
without a profile, maximum, cap/chain certificate, common-`x2` certificate,
convex-union premise, changed carrier, or supplied sign.  A warning-clean
direct check, targeted module build, and declaration-only audits all pass; each
declaration depends only on `propext`, `Classical.choice`, and `Quot.sound`.

The independently frozen exact-rational lane closed with
`HMPT-H2-PAIR-CONTROLS-PASS`: two implementations admitted both positive raw
geometries, rejected all eight frozen corruptions, checked 83,334 fully
admissible bounded queries, and found no falsifier.  That lane is computational
evidence only and is not part of theorem acceptance.

**Net proof movement:** forward on the exact signed-pair gate: the two frozen
raw geometric implications decrease from two open obligations to zero.
**Evidence:** compiling Lean theorems with standard-only trust audits; checked
finite controls are separate neutral search information.  **Difficulty
displaced:** none into a premise.  The remaining C3 work is the distinct
two-anchor arrangement-cell/opposite-support consumer for the `3+1` and `2+2`
mixed four-subsets; C1, C2, and C4 also remain.  **Counterfactual:** these
theorems remove the uncertain wedge/vertical-direction geometry from C3 and
materially reduce that proof to explicit consumers, but do not prove an H2
layer.  **Planning consequence:** retain `FP-15.C` as gated and permit a new
checkpoint plan for the two-anchor C3 consumer; do not launch the full H2 slate.

H2's official finite-layer count remains five.  No load-bearing edge in
`docs/wayfinder/map.md` changes.
