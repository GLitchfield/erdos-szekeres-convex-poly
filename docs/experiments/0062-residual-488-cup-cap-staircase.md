# Experiment 0062: closing the residual `(4,8,8)` window

## Question

After Experiment 0061 proved `upper.card ≤ 12` at every open `(4,8,8)`
critical root, can the remaining exact 23-vertex window be eliminated without
assuming all strict predecessor states or reviving a tree-global payment?

Only the declarations proved in Lean are completed mathematical results.  SAT
models and model reviews below are advisory route-selection evidence.

## False shortcut: smaller cup blocks

The first proposed shortcut replaced the proved ordered `6+7` theorem by one
of four smaller normalized block gates: `5+7`, `6+6`, `4+7`, or `5+6`.
CaDiCaL 1.5.3 and MiniSat 2.2 both returned SAT for every formula at forbidden
outcomes `(cap,cup,strong)=(4,8,8)`.  The independent witness checker verifies
the one-change law, absence of all three target outcomes, and every forced cup
block.  Its new forced-block check has positive and negative unit tests.

The CNF SHA-256 hashes are:

- `5+7`: `3ffd97892ff1b4037c0528c7d4d41768790455f04997874b2caa61d33b721a8f`;
- `6+6`: `4ece5d6296527819368b4f8506779dd84757880069493aa2f2aaa80f75b1fd3a`;
- `4+7`: `a86dc1a755e691b0f878261141687e5816a7a070cd61f53ae155a8fda8d0d8cb`;
- `5+6`: `c8157fa1aac9a53664c5ca5ff3acf7bf513a6f8165dc33b92f722922dd551d8c`.

The checked CaDiCaL assignment hashes are, in the same order,
`e7651a3ae4eb9f01046514f62932890223fe86477d60989412a67bc567e7f097`,
`af92650b9f20f05e8ae9d072f42581ea9ab303a3c04902a98b227ba3dbf614c9`,
`3c18a740f5343d8c01ec5340f8067818b8c5297858d6b47efbfb5e4f34feddc3`,
and `c9485c017d890acee59894e9bef6cdb7029083e2bb7f0842e8d69673546576fa`.
These models refute the abstract one-change gates; they are not Lean
counterexamples and are not asserted to be realizable deep roots.

## Exact residual arithmetic

At an exact critical root,

```text
lower.card + upper.card = 23,
0 < upper.card ≤ 12.
```

Lean also records that the two published child indices sum to eight throughout
this window.  This gives a conditional closure from all strict predecessor
states, but the final proof does not need that assumption.

The useful interpretation of the same staircase is elementary.  The positive
upper cardinalities split into exactly three regimes:

| upper size | lower size | lower witness | upper witness |
| --- | --- | --- | --- |
| `8..12` | `11..15` | five-cup | three-cap |
| `2..7` | `16..21` | six-cup | two-cap |
| `1` | `22` | seven-cup | one-cap |

The lower child is four-cap-free, the upper child is eight-cup-free, and both
children inherit the one-change law from decomposability.  The ordinary
cup--cap recurrence therefore supplies the displayed witnesses.  The one- and
two-vertex cap conditions are vacuous.  In every row the cup and cap sizes sum
to eight, so `HasDeepBelowSplit` glues them to a forbidden strong eight-set.

## Lean result

`StructuralChargingResidualWindow488.lean` proves the fixed cup--cap helpers,
the exact arithmetic normal form, and then:

```lean
theorem criticalRootImpossible_488 :
    DecomposableCriticalRootImpossible 4 8 8

theorem decomposableStateUpper_488 :
    DecomposableStateUpper 4 8 8
```

The second theorem lifts the exact critical-root contradiction through the
already proved root-transition equivalence.  It is unconditional: it does not
use `decomposableStateUpper_488` recursively, assume the strict predecessor
pool, assume sweep realizability, or use color duality.

The narrow module build passes, and `#print axioms` reports only `propext`,
`Classical.choice`, and `Quot.sound` for both declarations.  A frozen,
read-only Formal Proof Reviewer independently reproduced the hashes, build,
axiom audit, and each cardinal branch and returned `ACCEPT`.

## Advisory route review

A bounded Sol/Fable packet at SHA-256
`c460c8b4b3a5728732872469a8ace562bb5d1361532d22fb8ed19f4c48079041`
reviewed the earlier predecessor-conditional closure.  Sol returned
`supported` with high confidence and Fable returned `partially_supported`
with medium confidence, limited by omitted imported theorem bodies.  Both
confirmed the arithmetic and absence of circular use.  That review predates
the stronger unconditional theorem and is not cited as its verification; the
separate frozen formal review covers the final declaration.

## Disposition and next state

The residual `(4,8,8)` root window is closed in the recursively decomposable
model.  This is one off-diagonal state, not the general exact happy-ending
formula and not an unrestricted planar upper bound.

The next consumer named by the higher-cone machinery is `(5,8,8)`, whose
threshold is 42.  Bottom-up dependency analysis exposes `(5,7,8)`, threshold
41, as the smallest new fixed-`k=8` predecessor requiring structural work.
Exact index arithmetic closes lower-child sizes `11..40`, but two oriented
tails remain: lower sizes `1..10` against upper sizes `41..32`, and the extreme
`41+1` split.  Color duality swaps the state to `(7,5,8)` and therefore cannot
merge these obligations.  Restriction reduces the first tail to a
singleton-lower `1+32` gate; the upper-singleton extreme needs a separate
lemma. Experiment 0063 proves the exact two-tail reduction and kernel-checks a
counterexample to the first extracted `5+q+5` shortcut. The full `1+32` route
therefore has to retain its unused side reservoirs before claiming the
`(5,8,8)` consumer.
