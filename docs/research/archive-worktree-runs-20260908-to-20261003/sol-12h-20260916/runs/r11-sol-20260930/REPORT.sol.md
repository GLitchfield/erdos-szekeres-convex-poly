# R11 Sol report

Both requested reductions are closed and committed, in order, on their required branches.
Each replaces the old general contraction use with `hpart` on the exact painted part of a
well-formed single-run parent. Statements/docstrings are unchanged; both targets have no
sorry and only `propext`, `Classical.choice`, `Quot.sound`.

| Result | Proof commit | Targeted check | Locked type |
| --- | --- | --- | --- |
| R9p alternating from C1p + deletion | `254357db32a5e3b3d3364c4e1f6be87df005d546` | `20260930-113654-9334ed`, rc=0,113.6s,2362MiB | `1024dcf9ff295899` |
| R6p single-run from C1p + alternating | `e1d3ec8053c5d025c789826f267593c3b4621281` | `20260930-114717-d79169`, rc=0,100.5s,2349MiB | `bb363755215dc459` |

Scratch jobs `20260930-113255-b00ef1` and `20260930-114612-1d89c5` passed.
Proof commits used `es node commit` jobs `20260930-113931-e29ebb` and `20260930-114958-1f699e`.
Per the brief addendum, R6p registration from unchanged `R6P-TYPE.txt` passed in
`20260930-114142-a8bf92`, then committed as `aabf60cc4e17d50150f3d1eef1ce48017231a7d8`
(job `20260930-114517-7e40bf`).

`AUDIT.final.json` verifies branch heads, exact checked/committed sources, unchanged locks,
standard-axiom receipts and clean tracked tree. No compiler jobs or failed mathematical
proofs remain. One oversized queued check was withdrawn before any compiler ran; checkout
output-copy omissions and artifact/receipt inspection errors were logged and repaired.
No merge, push, full extract, other statement edit or delegation occurred. Harness releases
preserve handoff evidence in primary `runs/`; no primary source was edited.

C1p and deletion/alternating assumptions remain explicit. Safest next action: coordinator
review of both commits/receipts, then independent bridge/assumption work. No further trial
is authorized. `PROGRESS.md` carries both-node success for coordinator early finish.
Evidence: `MATHEMATICAL-HANDOFF.md`, `CHECK.r9p.json`, `CHECK.r6p.json`,
`NODE.*.closed.json`, `RECEIPT.*.json`, `SHA256.*.txt`, `AUDIT.final.json`.
The native goal remains subject to its no-completion-before-`2026-09-30T23:28:59.179712Z`
contract; both research results are accepted and host/coordinator finalization remains.
