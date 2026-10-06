# Inside-pair leaf threshold under two runs — closed and committed

Node `ErdosSzekeres.ctx_inside_pair_leaf_threshold_mono_of_two_runs`.
Branch `node/CtxInsidePairLeafThresholdMonoOfTwoRuns`; approved parent
`5847e155fa613d4d2311eaee86b4b094f630e9a4`; locked type `ca8c8fa7a2e9b812`.

This adapts the earlier inside leaf theorem to X's two-run premise, for
arbitrary well-formed contexts, either child of the pair, and every legal cut.
The earlier explicit-child premise also admits some single-run contexts;
this is not a broader overall domain. The full-sum exchange remains open.

Search artifact `7babe1161db8ae204eb97394b5d1f0b5cfab3ba855b831580e6f93e2b50ca4a2`.
Earlier accepted proof source `dff190112c32d08f2648a74d2aa6b397cde08b9b`.
The new prefix bounds the run-start finset by the first pair position if no
other child survives, contradicting two runs. Then reuse leaf deletion.

Body `cd9cd768dea4dace401527cb8044826d1fd0c9b55a7350122cfc1e5b9b2bf4e8`.
Fixture `9c5f7bd7dc6bf22feb67858467db0dff394cf10f5cea1b97cb55641a9c594048`,
byte span [1500,1510), 134 source and 129 compiled dependency pins.
Isolated job `20261001-163942-45f6a8`: accepted, 6.796s/2,105MiB/4G.
Receipt `49d0fb39d1d962b2be6e5b40bb6716c2f13671f60bdce6605d48397da66ffad9`.
Insertion reuses shared preflight/assembled, validates accepted receipt and
exact body/source bytes; no statement edit or full extraction.
Source SHA `4bbb290e57ca77bd29081c290b6bf6da04c3de9e85d1a6bc0948a8f2c5c33684`.

Original targeted job `20261001-164623-f18764`: passed,
70.0s/2,372MiB/20G, no OOM, missing outputs, or budget exceedance.
Receipt `ce6b5ddc0fd3a8b248008a1ad060e4c5fb07fdd4cbdd86ed0756de0c29cb3b29`.
Closed; locked type matches; no sorry, blockers, tag errors, nonstandard axioms.
Only propext, Classical.choice, Quot.sound.

Earlier old-fixture attempts 145457-a0cd4d and 155904-f1794e were refused
before Lean (missing module and changed source/capture). First original-check
submission used unsupported options and admitted no job; corrected job passed.
First receipt fetch was truncated; complete 65,536-byte fetch supplied audit.
A report replacement patch was rejected atomically for duplicate path actions.
All are workflow failures; none establish a mathematical failure.

Sol self-review only. Independent Astra review deferred by model/no-delegation
scope. Commit463b7f9d5fa23db7733a0fe8c0fa303f5fdbdeb6 verified: approved direct parent, exactly five node files; claim released closed.
