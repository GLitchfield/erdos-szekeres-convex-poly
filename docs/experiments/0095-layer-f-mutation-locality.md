# Experiment 0095: Layer-F mutation locality and stratified prime rank

Date: 2026-08-10

Status: Compiling locality infrastructure; geometric descent open

## Question

What part of a decomposition-prime rank can one single-triple mutation change,
and is the raw number of prime cores the right primary descent measure?

## Compiling locality theorem

`DecompositionPrimeMutationLocality.lean` proves that recursive
decomposability, proper deep splits, and decomposition-primality on a support
depend only on the colors of triples wholly contained in that support. Hence a
single mutation at `changed` cannot change prime-core membership for a support
that omits any of the three vertices of `changed`.

Lean now proves the direct consumer

```lean
SingleTripleMutation.exists_primeCore_locality
```

and the family-level containment

```lean
SingleTripleMutation.decompositionPrimeCores_symmDiff_subset
```

which says that the symmetric difference of the old and new prime-core
families is contained in the family of supports carrying all three changed
vertices. The same containment compiles separately in every cardinality
stratum.

## Rank accounting

The exact created-versus-destroyed identity and comparison compile:

```lean
primeCoreCount_add_destroyed_eq_add_created
primeCoreCount_lt_iff_created_lt_destroyed
```

They reduce a raw-rank descent claim to showing that a safe mutation macro
destroys more prime cores than it creates. They do not establish that sign.

The architectural audit recommends a cardinality-stratified replacement for
the raw count: a core of size `m` receives weight `(2^n+1)^m`. The repository
now defines `PrimeCoreCountAtCard` and `StratifiedPrimeCoreRank`, and Lean proves

```lean
StratifiedPrimeCoreRank χ = 0 ↔ IsDecomposable χ
```

for every nonempty ground set. The high base is intended to make a loss in the
largest changed cardinality stratum dominate every possible lower-cardinality
creation; the general comparison theorem is the next arithmetic target.

## Route disposition

`PRIME_CORE_COUNT_MODIFY_TO_STRATIFIED`.

Raw `PrimeCoreCount` remains a useful diagnostic and exact accounting device,
but it ignores core size and may be unstable under spectator extensions. The
primary candidate is the stratified profile, with a decomposition-edit defect
retained as a structurally different backup.

The load-bearing mathematical obstruction is unchanged: construct a macro of
at most three target-free fixed-sweep-realizable mutations whose endpoint
destroys the highest affected prime stratum without creating a higher one.
The locality theorem identifies exactly where such new cores may appear; it
does not select the macro.

## Evidence and model boundary

- `ErdosSzekeres/DecompositionPrimeMutationLocality.lean`
- targeted Lean build: 3,324 jobs
- axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`
- frozen specialist packet:
  `runs/agents/20260810-parallel-portfolio/layerf-task.json`

The compiling locality and rank identities hold for arbitrary triple
colorings. The proposed mutation descent additionally requires
fixed-sweep realizability and target avoidance at every intermediate coloring.
Unrestricted mutation connectivity does not provide that stronger statement.
