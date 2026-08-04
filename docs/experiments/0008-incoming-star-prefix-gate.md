# Incoming-star prefix-control gate

## Status

Exact bounded computation through eight vertices, independently replayed from
increasing chains. Supporting causal, nonvacuity, negative-control, and
crossing-transition theorems compile in Lean. This gate does not prove or
select the uniform incoming-star route. A kernel-checked nine-vertex collision
now rejects the proposed uniform conditional transition and stops the
deterministic incoming-star quotient route.

## State and necessary query

For a coloring `χ`, finite ordered child `s`, terminal vertex `v`, and depth
`d`, let

```text
I_d(χ,s,v) = { L_d(χ,s;u,v) | u ∈ s and u < v }
Ξ_d(χ,s)   = { I_d(χ,s,v) | v ∈ s }.
```

`Ξ_d` forgets vertex identities only after grouping pair languages by their
common terminal endpoint.  For a sweep cut `x`, define

```text
Π_d(χ,s,x) = { I_d(χ,s,v) | v ∈ s and v < x }.
```

At a fixed root `(lower,upper)`, the necessary root query consists of
`Π_d(χ,lower,x)` for every `x ∈ upper` and `Π_d(χ,upper,x)` for every
`x ∈ lower`.  A crossing pair ending at `x` consumes precisely predecessor
languages from the opposite child before that cut.  Equality of global child
spectra must therefore determine these queries before `Ξ_d` can be considered
a contextually compositional state.

The Lean definition is `prefixIncomingStarSpectrum`; the proposition
`RootRelevantPrefixEq` states the two query families.  Lean also proves:

- a chain ending below `x` is unaffected by deleting vertices at or above
  `x`;
- `pairTurnLanguage` and `incomingStar` satisfy the corresponding causality
  theorem; and
- filtering depth-`d` languages down to depth `e ≤ d` recovers the depth-`e`
  language and incoming star.

These are structural theorems for arbitrary triple colorings, not finite
census claims.

## Exact bounded result

The committed producer uses the executable predecessor recurrence.  The
independent checker imports no producer code, regenerates the recursive
colorings locally, and recomputes every pair language directly from increasing
chains.  Both agree on the following `(k,d)=(6,4)` census:

| `n` | open root observations | fixed-root inputs | repeated observations |
|---:|---:|---:|---:|
| 2 | 2 | 2 | 0 |
| 3 | 6 | 6 | 0 |
| 4 | 22 | 22 | 0 |
| 5 | 120 | 120 | 0 |
| 6 | 1,002 | 978 | 24 |
| 7 | 11,242 | 10,038 | 1,204 |
| 8 | 141,254 | 110,990 | 30,264 |
| **total** | **153,648** | **122,156** | **31,492** |

There are zero collisions in each separately checked output:

- root-relevant prefix queries;
- complete ordered child-star sequences, which is stronger than the query;
  and
- parent incoming-star spectra.

The largest input fiber has nine observations, so the result is not an
injectivity artifact.  Without restricting to open colorings, global `Ξ_4`
also determines the complete ordered star sequence for every decomposable
coloring through eight vertices.  At eight vertices this compresses 186,888
colorings to 132,280 global spectra.

The compact positive regression in `IncomingStarPositive.lean` gives two
different, decomposable, strong-six-open colorings on six vertices with equal
child spectra, equal child prefix queries at every cut, and equal parent
spectra.  This kernel-checked theorem confirms that the state can identify
genuinely different colorings while retaining the covered transition data.

`IncomingStarTransition.lean` proves the first uniform transition layer. For
an arbitrary constant predecessor turn, a depth-`d+1` pair language is exactly
the empty word together with that turn appended to every word in the
depth-`d` incoming star at its first endpoint. The two deep-below corollaries
derive the constant left or right turn for crossing pairs, and congruence
corollaries show that equal parent incoming stars give equal crossing pair
languages. This proves the crossing-pair part of the conditional transition;
it does not yet control same-child pairs whose ambient chains visit both
children.

`IncomingStarTransitionCollision.lean` proves that the remaining case is a
genuine obstruction, not just a difficult proof step. At the fixed root
`lower={5}`, two nine-vertex colorings have equal child spectra and every
root-relevant prefix, but unequal parent spectra. The complete upper-child
pair-language matrices are equal in the smallest algebraic witness; the word
`left,right,right` at parent pair `(7,8)` distinguishes the parents.

A second kernel-checked witness makes both parents recursively decomposable
while retaining equal child spectra, all prefix queries, and unequal parent
spectra. Both contain a strong six-set. Thus neither the root split law nor
decomposability/signotope structure repairs the conditional transition; only
a property-relative openness hypothesis remains logically capable of
excluding the obstruction.

The exact manifest is
`data/derived/e3-incoming-star-prefix-k6-n8.json`.  Its producer and checker
hashes are recorded and verified internally.  Running

```console
python3 scripts/check_incoming_star_prefixes.py \
  data/derived/e3-incoming-star-prefix-k6-n8.json
```

replays every count, hash, collision field, and positive decomposition tree.

## Negative controls and limitations

The analogous stronger prefix claim is not true without parameter care.
`IncomingStarPrefixCollision.lean` kernel-checks two open decomposable
colorings at `(k,d,n)=(5,3,8)` with equal global incoming-star spectra and
unequal prefixes at gap seven.  Their depth-four global spectra are already
unequal, so this is a negative control rather than a refutation of the live
`(k,d)=(6,4)` gate.  In particular, a successful recovery argument must use
the depth and openness parameters essentially; anonymous spectrum algebra
alone cannot prove it.

An exploratory singleton-extension census at `(k,d,n)=(6,4,9)` tested every
singleton position and both root orientations.  It found no case where equal
parent `Ξ_4` hid unequal parent prefix spectra.  Those counts come from one
implementation and are not claimed as exact evidence here.

Even the independently replayed gate proves only a finite statement.  It does
not establish:

- prefix control for arbitrary size;
- sufficiency of prefix control for every modified internal pair;
- a uniform parent transition theorem; or
- any compression or charging bound approaching `2^(k-2)`.

## Decision and stop rules

The first Sol audit returned `partially_supported` at high confidence and
correctly required the smaller conditional parent transition before
property-relative prefix recovery:

```text
equal child Ξ_d states + RootRelevantPrefixEq + fixed root behavior
  -> equal parent Ξ_d states.
```

The nine-vertex Lean collisions refute this implication under both the root
split law alone and recursive decomposability. Adding strong-six-openness at
this stage would collapse the planned separation between state sufficiency
and property-relative prefix recovery. The recurrence diagnosis is exact:
same-child pair updates require the incidence between a predecessor identity,
its enlarged parent language, and its internal continuation turn. The
anonymous spectrum and prefix supports retain only marginals, not this joint
data.

The deterministic quotient route is therefore stopped under its declared
rules. In particular, the project will not repair it with ordered endpoints,
multiplicities, interval-indexed state, deeper words, or another incidence
refinement. The previously proposed property-relative implication

```text
equal child Ξ_d states + fixed open decomposable root
  -> RootRelevantPrefixEq.
```

is no longer the next theorem. It remains logically open but cannot repair the
failed state interface by itself.

A clean blind review at revision `b90dd3f` used packet SHA-256
`97f73c43b09f0c591ad43e6a7bed3f034b906c3196b6a7cc375cbf9a1a51c47a`.
Claude Fable 5 returned `supported` at medium confidence and Codex Sol returned
`supported` at high confidence. Both apply the declared stop and select
structural charging over minimal-counterexample descent. Their exact next
theorem is a certificate-free seven-vertex upper-child gap trichotomy with an
external singleton anchor. The review is advisory; the collision theorems,
not reviewer agreement, reject the route. The stop conditions that now apply
are:

- prefix-indexed state in place of global `Ξ_d`;
- an ordered per-vertex star word or vertex identities;
- multiplicities, increased word depth, or another refinement round; or
- a transition theorem with no plausible compression or charging mechanism
  toward `2^(k-2)`.

The default resource limit remains 30 minutes, 8 CPU cores, 16 GiB RAM, and
5 GiB under ignored `runs/`.
