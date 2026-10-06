# Satisfied contexts have pair limits at least two

Agent `codex:01a0fc94-0467-7b90-823c-bce1e6fe6128`, 2026-10-02.
Node `ErdosSzekeres.ctx_satisfies_pair_limits`, independent branch
`node/CtxSatisfiesPairLimits`, base `e3c87197b66a65092e1ffe5e9d0d8c7aa1981cf8`.
Registered type hash `d7e27cb0f6fc2611`; no statement changes.
Pinned commit `c37f3751de15f776209110fdf31048fa3d8b2319`, commit job
`20261002-105743-c81da5`. Claim release is CLOSED.

The accepted theorem says that if `Ctx.Satisfies χ S σ`, any two child positions
`p < q` have both cup and cap limits at least two. It needs neither WellFormed
nor global parameter assumptions. This is a necessary feasibility condition;
it does not prove PEEL with additional hypotheses or characterize actual
decomposition histories.

Proof: the increasing finite-set enumeration `S.orderEmbOfFin` realizes every
child index. The elements below its index `i` are exactly the image of `Iio i`,
so their cardinality is `i`. Sorted child positions transport `p < q` to the
enumeration indices. Their two ambient vertices form a subset of `S` with
cardinality two; no ordered triple lies in it, hence it is simultaneously a cup
and a cap. The two inequalities follow directly from `Satisfies`.

Original-source check `20261002-105442-376a39` is CLOSED, build 2.921861s /
591 MiB, no sorry, only propext/Classical.choice/Quot.sound, matching type and
lock, empty blocked/nonstandard/uncovered dependencies. Immutable receipt
`7835038cff4025744af5b60c676263d34ca8192bea6b0505951f369c424668d4` is copied to
`PAIR-LIMITS.original-check.json`; receipt reference `PAIR-LIMITS.receipt.json`.
Fresh frozen fixture
`5bca4fc196358a1fe58af1f8170650712fe69d57a1c7a59aafec7ee5eafc0477` is 9000 bytes.
Changed-node audit and layers against the base pass. All 378 inherited lock
entries are structurally unchanged, with exactly this one new entry.

Registration `20261002-103505-a25ab6` succeeded. Searches `satisfies pair limits`
and `cup cap two point vacuous card` found no duplicate; `isCupSet_pair` found
the existing core vacuity lemma in StructuralChargingSpanFrontier. Initial
checks `20261002-103957-913fea` and `20261002-104335-285989` found respectively a
missing `Mathlib.Data.List.GetD` import and its explicit list/default arguments.
Those API failures are logged. Check `20261002-104642-349d6b` compiled the proof
but extraction refused the 28.4 GiB closure of the core pair-lemma import against
the 4 GiB guard. The import was removed; the same no-triple cardinality argument
was proved locally, without exporting a duplicate helper or raising a guard.
Optional dependency metadata was removed; theorem type and lock were unchanged.

Reusable observation: arbitrary raw WellFormed contexts need not satisfy the
constraints of any coloring, even when their recursive bound is positive.
Next verification is the explicit depth-four PEEL witness: its first pair of
children appears to have cup limit one. That computation and the implication
must be certified before reporting the witness as infeasible. Nothing here
refutes the happy-ending conjecture or the one-level root exchange statement.

No new Python research algorithm or tracked workflow helper was introduced.
Inline preservation reuses `es.artifacts.put_json/canonical`; lock comparison
uses parsed JSON and the exact base. Original artifacts and API-failure logs
are preserved. Independent coordinator review remains pending under the fixed
Sol-only contract. Pin the node commit and release the claim CLOSED; preserve
the ignored artifact directory with the branch. No merge or push is authorized.
