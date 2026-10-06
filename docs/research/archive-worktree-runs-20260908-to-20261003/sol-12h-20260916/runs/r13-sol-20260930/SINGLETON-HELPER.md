# Explicit singleton threshold helper

Accepted theorem: `ErdosSzekeres.ctx_singleton_part_bound_eq_threshold`.
For any raw context sigma, child position p, side s and natural sibling
maximum m, the bound of `sigma.part [p] s m` equals
`decomposableThreshold(capLimit p p + 1)(cupLimit p p + 1)sigma.k`.
There is no well-formedness, parameter-range, or positive-limit assumption.

The filtered child list is exactly `[p]`, so the recursion takes its base
branch. Both limits are bounded by k-1. At a zero limit the threshold is
zero; at a unit limit the bounded classical-binomial formula gives one;
otherwise the definitions coincide.

Targeted check: `20260930-165717-642558`, rc=0, type hash
`47f67af285e3e6f`, `sorry=false`, axioms only `propext`, `Classical.choice`,
`Quot.sound`. Evidence: `RECEIPT.singleton-helper-check.json`.
Statement fixture: `fe89f92fb99b2518785065e490af79c7476f0d96688caf4647d212bf7b82d72c`.
Registration: targeted job `20260930-165353-17936b`.

Before writing, `es search "singleton part bound equals decomposable
threshold cap cup limits"` found no matches (artifact
`search-explicit-singleton-node.json`). The registration duplicate search
also found no equal statement. Existing mixed-exchange proofs use a local
baseOf identity; this public theorem exposes the explicit T formula,
including zero/unit limits, for new exchange statements.

Scratch compile `20260930-163834-f2c570` failed at an implicit subset
argument, a let-bound goal, and opaque part.k arithmetic. The threshold
argument did not fail. The repaired scratch passed
`20260930-164345-e12daf`; no mathematical counterexample occurred.

Open research obligation: prove C1r or derive it from a strictly narrower
singleton-base/part exchange. The finite exchange probes pass, but their
sufficiency for all interval cuts remains unproved. This helper alone
does not satisfy either R13 Done criterion.

Review: no workflow algorithm was introduced by this helper. The proof
reuses context child-position, run-count and threshold identities. The
ad hoc probe scripts remain diagnostic run artifacts pending final review;
no unsupported normal-form theorem was imported into this proof.
