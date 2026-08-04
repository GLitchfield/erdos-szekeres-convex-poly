# Singleton-gap structural charging

## Status

Selected by the clean Sol/Fable review after the incoming-star transition
collision. The reduction, normalized ordered `3+4` core, arbitrary-set
transport, and mirrored `4+3` case all compile in Lean. Consequently the
reviewed seven-vertex gap trichotomy and certificate-free singleton-root
cardinal bound are now proved.

## Route decision

The review packet at revision `b90dd3f` has SHA-256
`97f73c43b09f0c591ad43e6a7bed3f034b906c3196b6a7cc375cbf9a1a51c47a`.
Claude Fable 5 returned `supported` at medium confidence and Codex Sol returned
`supported` at high confidence. Both reviewers apply the declared stop to the
deterministic quotient route and select witness-level structural charging.
This agreement is advisory; the compiling transition collisions are the
mathematical reason for the redirect.

## Lean reduction

`StructuralCharging.lean` states the reviewed target as
`UpperChildGapTrichotomyAtSeven`. For seven decomposable vertices in the upper
child and an external singleton lower anchor `q`, the desired alternatives are

```text
upper four-cap
or upper five-cup
or upper strong five-set
or upper three-cap having q as a sweep endpoint.
```

The endpoint branch extends across the root to a parent four-cap. Lean proves
that the trichotomy implies the full singleton-root `(4,5,5)` alternative and,
by restriction, the cardinal bound seven.

The remaining proof is factored through `CupBlocks34Force455`. If there is no
endpoint three-cap, every upper triple wholly before or wholly after `q` turns
left, so both gap sides are cups. Absence of a five-cup bounds each side by
four. Since their disjoint union has seven vertices, their sizes are `3+4` or
`4+3`. Recursive decomposability is used only to supply the rank-three
one-change law on this union. Thus it suffices to prove:

```text
two consecutive cup blocks of sizes three and four
+ rank-three one-change law
  -> four-cap or five-cup or strong five-set.
```

Lean also proves an asymmetric saturation incompatibility: a lower `r`-cup
and upper `s`-cap cannot both be strictly saturated when the corresponding
`r+1` cup and `s+1` cap extensions are forbidden. This is reusable charging
machinery but does not by itself close the `3+4` core.

`StructuralChargingCore.lean` proves the normalized `Fin 7` statement. Three
small propagation lemmas classify the useful consequences of the one-change
law. Equal outer turns make all four turns equal; the two asymmetric forms
propagate an equality from a witnessed change. The main proof then branches on
only seven named triples. Each branch constructs an explicit four-cap,
five-cup, or strong five-set. Its finite `fin_cases` uses merely check triples
or quadruples inside those fixed witnesses; it is not an enumeration of the
35 turn variables or their colorings.

`StructuralChargingTransport.lean` discharges the deliberately separate
transport obligation. It relabels an arbitrary ordered disjoint union by an
increasing `Fin 7` embedding, identifies the first and last blocks, and maps
the fixed witness back. An explicit reversal of ordered triples proves the
`4+3` version while preserving both the one-change language and the three
possible outcomes. This closes `CupBlocks34Force455` and the existing reduction
then closes `UpperChildGapTrichotomyAtSeven`.

## Completion and stop rules

The certificate-free transported cup-block core and mechanical derivation of
the singleton-root cardinal bound now compile. The proof is symbolic rather
than LRAT or exhaustive coloring enumeration and exposes reusable witness
propagation. The next stop test is whether this mechanism yields a meaningful
charge at the first `k=6` boundary; passing the seven-vertex lemma alone is not
a uniform all-`n` recurrence.
