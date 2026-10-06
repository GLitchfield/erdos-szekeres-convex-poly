# Full PEEL: kernel refutation

Agent `codex:01a0fc94-0467-7b90-823c-bce1e6fe6128`, R19, 2026-10-02.
Branch `node/CtxBoundSingletonAttainmentCounterexample`, independently based on
`e3c87197b66a65092e1ffe5e9d0d8c7aa1981cf8`. No merge or push.
Pinned commit `119a082b4ee8a668e565027b226f5bc4cacddb66`, guarded commit job
`20261002-102132-5309b1`; claim released CLOSED with this handoff preserved in
the primary checkout.

Accepted theorem `ErdosSzekeres.ctx_bound_singleton_attainment_counterexample`
is the exact universal negation of the registered full PEEL statement:
WellFormed, a,u>=4, at least two runs, bound>=2, arbitrary child, either side,
every coupling 1<=c<=k-2, zero-valued parts retained. The theorem's type hash
`84befa2a0b0ddbc8` is unchanged. The positive conjecture is preserved separately
on `node/CtxBoundAttainedBySingletonCut`, commit
`528caa7e560a86e8e77661d4a21e54d29f3454e4`, with its diagnostic falsifier result.

Original-source check `20261002-101239-d357fa` is DONE/CLOSED, 307.362s/4096MiB.
Receipt `9159d9e9c8b436a7edd362410be34693c221562de3d85dcfca000cbb2c7ee3f5`,
saved and JSON-parsed in `PEEL-REFUTATION.original-check.json`. No sorry,
standard axioms only (`propext`, `Classical.choice`, `Quot.sound`), no nonstandard
or uncovered axioms, no blocked dependencies, lock matches. `es audit --changed`
passes (two declarations audited); `es layers --base e3c87197` passes; status
fresh with no problems. All378 inherited lock entries are structurally unchanged,
with exactly the one new refutation added. No statement was edited by hand.

The witness is (a,u,k)=(4,4,5), word `3U4LSS1L2USS`, maxima1111, children
[2,3,6,7], two runs. The proof establishes its WellFormed clauses by finite
position analysis. The run-block cut [2,3]|[6,7] is worth1+1=2, checked in the
kernel, so the closed `ctx_bound_cut_le` gives bound>=2. Four child positions,
two sides and three couplings give24 cases; kernel decisions show every
singleton sum is1. An alleged singleton attainer contradicts bound>=2.
The proof needs only this lower bound, not a full four-child bound computation.
The numerical equality bound=2 is diagnostic; it is not the exported theorem.

This removes the full PEEL normal-form route under the stated raw hypotheses.
There is no remaining proof idea for that false statement. It does not refute
the happy-ending conjecture or the one-level-root singleton exchange target.
Geometric feasibility is not certified for the witness. The same gap invalidates
the narrower end-cut-of-four-le route mathematically (cut dominance turns its
inequality attainer into equality); that inherited node was only read and no
separate compiled corollary is claimed here. Coordinator reconciliation is due.

Why the failure occurs: the earlier SS1L2USS obstruction at globals3 can be
lifted by an oldest upper unit flank while raising a, then an oldest lower unit
flank while raising u. All three retain diagnostic bound2 versus singleton sums1
in `PEEL.oldest-flank-lift.json`, job `20261002-094943-6dc167`. A single physical
oldest flank of maximumm adds1 to the selected chain and oldPure+m to its join;
its effective global is min(global-1,k-m). Existing boundary normalization
theorems give one-way comparisons. An exact oldest singleton-flank normalization
is a plausible reusable explanation, pending proof. Selected-level markers on
both sides must be excluded, since they can add two extensions.

The k6 middle-child mechanism and failure of raw chain-limit loss minimization
are documented in `PEEL.MECHANISM.md`. Run capacities and new join constraints
matter, and an optimum may have a zero-valued leaf. No further sibling-penalty
narrowing was commissioned. `PEEL.HANDOFF.md` preserves the registered falsifier,
exact witness replay and scientifically superseded scan's incomplete coverage.

Failures recorded before retry: direct registration could not reach the sandbox
user bus, retained an unlocked module and was repeated identically in guarded
job `20261002-100702-280d16`. First proof check `20261002-101030-d69b4f` exhausted
default200000 heartbeats after40.563s/3241MiB. The retry raised only the module's
compiler allowance to4000000; no mathematical premise, statement or proof method
changed. A witness-block probe used an unsupported evaluator context manager and
produced no output; explicit-close repair `20261002-100846-23dcc4` confirmed all
six run-block cuts, recorded diagnostically. These are not hidden proof attempts.

Search before lemma: `es search 'singleton attainment counterexample cut bound'`
returned no duplicate. `es search ctx_bound_cut_le` found the certified interval
cut inequality and the existing end-cut counterexample pattern. Reuse: shared
proof-span assembly, frozen fixture
`393d63a027df2bde2cebae5bf47f7e473f8346d74b5945c42737f383e37b47f4`, kernel
decisions and the existing cut theorem. No custom evaluator or certificate
generator was written; no generated certificate module changed.

The research artifacts are gitignored and must be preserved under
`runs/r19-sol-20261002/` alongside the pinned commit. Routine self-review found
the proof checks exactly the registered domain and conclusion. Formal separate
code/library review and usage reconciliation remain scheduled before R19 ends;
independent coordinator review is pending under the fixed Sol-only contract.
