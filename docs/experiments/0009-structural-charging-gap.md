# Singleton-gap structural charging

## Status

Selected by the clean Sol/Fable review after the incoming-star transition
collision. The reduction to one seven-vertex cup-block lemma compiles in Lean;
that core lemma remains open.

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

## Completion and stop rules

Success requires a certificate-free compiling proof of the cup-block core, a
clean axiom audit, and the already-formalized derivation of the singleton-root
cardinal bound. Stop this target if the normalized seven-vertex statement is
false, if its proof collapses to LRAT or exhaustive coloring enumeration, or
if it does not expose a witness-level mechanism that can be tested at the
first `k=6` boundary.

