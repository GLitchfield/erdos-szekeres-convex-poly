# R11 Sol progress

Agent: `codex:01a0f2ee-e8b3-78d0-8d67-59fe27405b5b`; configured gpt-6.1-sol, xhigh;
no delegation. Research window: `window-60c40fd28a2d49f9`.
Fixed research deadline: `2026-09-30T23:28:59.179712Z`.

R9p is claimed on `node/CtxBoundAdditiveSingleRunAlternatingOfPartContractionAndDeletion`.
Branch-switch job `20260930-113018-81ceb5` completed with rc=0.
Scratch compile `20260930-113255-b00ef1` passed, rc=0, 19.1s, peak643MiB,
with exactly `propext`, `Classical.choice`, `Quot.sound`.
The copied R9 proof already represents every contracted context as a painted part of a
parent with one contiguous child block. Its existing `hPositions` and `hRunCount` prove
the parent has at most one run, allowing direct use of `hpart`.

R9p is CLOSED and COMMITTED: `254357db32a5e3b3d3364c4e1f6be87df005d546`.
`es node commit` job `20260930-113931-e29ebb` passed rc=0, tree clean.
Targeted check `20260930-113654-9334ed` passed rc=0,113.6s,peak2362MiB:
locked type `1024dcf9ff295899`, `sorry=false`, standard axioms only.
Signature/docstring bytes match the stub; installed body matches scratch.
Original queued check `20260930-113424-cb098c` was withdrawn
before start (rc=130): sandbox-bus refusal in dependency preflight had selected an
unnecessary 20G reservation. No compiler was stopped.
R9p claim is released. Branch-switch job `20260930-114026-bc5dff` passed;
worktree is on `node/CtxBoundAdditiveSingleRunOfPartContractionAndAlternating`.
R6p registration passed (`20260930-114142-a8bf92`, rc=0,160.9s,peak2290MiB),
locked type `bb363755215dc459`. The supplied `R6P-TYPE.txt` is unchanged.
Registration commit: `aabf60cc4e17d50150f3d1eef1ce48017231a7d8`
through `es node commit` job `20260930-114517-7e40bf`, rc=0.
R6p is claimed. Scratch compile `20260930-114612-1d89c5` passed, rc=0,13.0s,
peak600MiB, exactly the three standard axioms;
it copies R6 and replaces its sole true-label contraction by `hpart` on the exact
well-formed single-run source parent. The identical body is installed, preserving the
registered signature/docstring. Targeted check `20260930-114717-d79169` is submitted
under6G, without a kill budget. Registered closure/proof commit remain pending.
Both-node success has NOT yet been reached; the trial continues.
Evidence: `R9p.stub.lean`, `R9p.body.lean`, `R9p.module.lean`, `R9p.lean`,
`FIXTURE.r9p.json`, `RECEIPT.scratch-r9p.json`, `LOG.scratch-r9p.txt`,
`RECEIPT.check-r9p-unstarted.json`, `MATHEMATICAL-HANDOFF.md`;
`CHECK.r9p.json`, `NODE.r9p.closed.json`, `RECEIPT.check-r9p.json`,
`RECEIPT.commit-r9p.json`.
