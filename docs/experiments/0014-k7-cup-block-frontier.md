# The first `k = 7` saturated frontier

## Question

After closing both orientations of the first `k = 6` saturated boundary, what
is the next published-induction obstruction, and how far does the same
gap-side method extend without a finite E3 certificate?

## Arithmetic frontier

The independently replayed classifier gives eight non-index-one states at
`k = 7`. In enumeration order they are

```text
(4,7,7,3,2)  (4,7,7,3,3)  (5,6,7,4,2)  (5,7,7,4,2)
(6,5,7,2,4)  (7,4,7,2,3)  (7,4,7,3,3)  (7,5,7,2,4).
```

The first state has child pairs `(2,15)` and `(3,14)`. Its color dual has
`(14,3)` and `(15,2)`. The second state has pairs `(4,13)`, `(5,12)`, and
`(6,11)`, together with their reversed dual pairs.

## Compiling Lean results

`StructuralChargingSaturatedResource.lean` now proves the uniform elementary
bound

```text
upper.card < 2 * u
```

for a nonempty lower child when the parent avoids a four-cap and a `u`-cup.
This closes `(4,7,7,3,2)` and its dual without decomposability or a finite
certificate. A sharpened decomposable-child form gives
`upper.card <= 2 * (u-1)`, so the 13-vertex alternative at
`(4,7,7,3,3)` is already impossible.

`StructuralChargingCupBlocks56.lean` freezes and proves the exact local
contract: ordered cup blocks of sizes `5+6` or `6+5` satisfying `OneChangeOn`
force a four-cap, seven-cup, or strong seven-set. The following pieces
compile:

- reversal and order-embedding transport from the normalized eleven-vertex
  statement to both arbitrary block orientations;
- the quantitative consequence `left.card + right.card <= 10`;
- the actual gap-side application, which would close upper sizes 11 and 12;
- a seven-chain theorem saying five equal consecutive turns determine all
  thirty-five triples;
- all five immediate fan branches, each producing an explicit seven-cup;
- the bridge-turn seven-cup `{0,1,2,3,5,9,10}`;
- the overlapping-six-cups strong-seven mechanism: cups
  `{0,1,2,3,4,5}` and `{0,1,2,3,4,6}` together with the all-right fan
  through `5,6` form the strong set `{0,1,2,3,4,5,6}`;
- three explicit cap leaves; and
- a reduction of the complete normalized target to exactly two named residual
  propositions, `CupBlocks56ResidualA` and `CupBlocks56ResidualC`.

Residual A now compiles in full. Its right-`346` half has a three-way explicit
witness proof: a left `4510` gives the seven-cup
`{0,1,2,3,4,5,10}`; otherwise a right `467` gives the four-cap
`{3,4,6,7}`; in the remaining branch, left `467` extends to the six-cup
`{4,6,7,8,9,10}`. The right `4510` turn and the tail cup force the remaining
right fan turns `457`, `458`, and `459`, so that this skip cup and the tail cup
form the strong seven-set `{4,5,6,7,8,9,10}`. Together with the already proved
left-`346` branch, this proves `cupBlocks56ResidualA`.

Residual C now compiles as well. The one-change law forces the bridge turns
`459`, `346`, and `467`. A left `4510` produces the explicit seven-cup
`{0,1,2,3,4,5,10}`. In the right branch, the tail cup
`{5,6,7,8,9,10}` and skip cup `{4,6,7,8,9,10}` force the remaining front
fan and yield the strong seven-set `{4,5,6,7,8,9,10}`. Therefore
`cupBlocks56FinEleven` and `cupBlocks56Force477` compile, and
`StructuralChargingSaturatedResource.lean` closes all three child pairs at
`(4,7,7,3,3)` and their color duals.

## Bounded falsification and review

A deterministic CNF producer forced the two normalized cup blocks and encoded
the rank-three one-change law while forbidding the three target outcomes.
Both orientations have 165 variables and 13,890 clauses. CaDiCaL 1.7.3
reported UNSAT for both in 0.01 seconds below 20 MiB RSS. No proof certificate
has been checked, so this is evidence only.

Sol returned `partially_supported` at high confidence for the contract audit.
Its main objection was to type-check the exact application shell before
freezing the interface; that shell now compiles. A second proof-focused Sol
audit recommended the seven-chain and fan reduction now present in Lean.
Fable again failed at provider quota and returned no review. Work continued
without waiting for it.

A targeted residual SAT test found an important countercontrol: a left
five-cup and an all-right five-turn fan do not alone force a strong seven-set.
This prevented promotion of a false shortcut. The bridge-cup leaf was then
isolated and proved directly in Lean.

The first residual was split on `χ(3,4,6)`. Its left branch uses two
overlapping six-cups, while the right branch is the explicit cup/cap/strong
argument above. During proof search, CaDiCaL emitted a 6.4 KiB LRAT trace for
the refined branch, and backward slicing found 85 relevant original clauses.
That transient trace was used only to identify the turns `4510` and `467`;
the promoted theorem neither imports the trace nor calls an external solver.

A later bounded blind review of the next state used evidence-packet SHA-256
`39ac2acb7aae73c84889f20e0006569b42e630166a1253665ec2d9a2509fa9bc`.
Sol (high confidence) and Fable (medium confidence) both returned
`partially_supported`: the application shell is sufficient, but the
arbitrary-`OneChangeOn` local theorem needed a direct 22-point falsification
test. Fable's suggested count
`choose(k-3,a-3) + choose(a+u-5,a-3)` predicts the sharp value 21 at
`(5,6,7)`, but this formula is advisory conjecture, not evidence.

`scripts/check_two_cap_free_sides.py` implements that deterministic test. It
uses true variables for left turns, checks the one-change law, forbids a
four-cap on either side of every fixed cut, and forbids ambient five-caps,
six-cups, and strong seven-sets. Strong patterns are separated lazily and SAT
models are independently rechecked against every predicate. The results were:

| vertices | cut(s) | result | evidence level |
|---:|---:|---|---|
| 21 | 6 | SAT | independently validated model; the bound is sharp |
| 22 | 1--6 | UNSAT without strong-7 clauses | bounded solver evidence |
| 22 | 7 | UNSAT, 34,450 blockers | bounded solver evidence |
| 22 | 8 | UNSAT, 85,237 blockers | bounded solver evidence |
| 22 | 9 | UNSAT, 114,736 blockers | bounded solver evidence |
| 22 | 10 | limit, 923,072 blockers | inconclusive at 600 seconds |
| 22 | 11 | limit, 912,320 blockers | inconclusive at 600 seconds |

The incremental runs used the Ubuntu CryptoMiniSat 5.11.15 Python binding
from a user-local package extraction. Generated CNFs, models, and manifests
remain under ignored `runs/sat/`. No UNSAT result is promoted as a completed
mathematical result.

## Claim ceiling and next target

The active Lean dependency is `TwoCapFreeSidesBound567`. Its compiled
application bounds the large child by 21 and conditionally eliminates child
pairs `(2,24)`, `(3,23)`, and `(4,22)`, together with the color-dual pairs.
`StructuralChargingCapFreeSides.lean` proves the first noncomputational layer:
each side has cardinality at most 15 by the ordinary `(4,6)` cup--cap
recurrence, with `OneChangeOn` promoting the resulting consecutive chains.
Thus `TwoCapFreeSidesCore567` restricts the open proof to side sizes `[7,15]`.
The `(4,4)` and `(4,5)` recurrences then produce four-cups on both sides and a
five-cup on at least one. The compiled `4+5/5+4` gate consequently yields an
actual four-cap meeting both sides or a strong six-set. The unresolved step is
to charge failure to extend these witnesses to a five-cap or strong seven-set.
The local proposition itself remains open. The next target is a conceptual
rank/charging coupling inside that window. If a later exact search finds an
arbitrary-signotope counterexample at cuts 10 or 11, the fallback is the
reviewed decomposable-only or root-relative cross-gap contract. Nothing here
proves the uniform all-parameter transition.
