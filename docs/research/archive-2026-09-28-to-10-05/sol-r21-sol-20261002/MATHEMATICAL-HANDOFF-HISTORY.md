# R21 mathematical handoff (live; 2026-10-02 21:48Z)

Researcher `codex:agent-run-bef3c92bee6b417b`, thread
`01a0fe0f-bbf0-7a53-b71b-d7f6bfd74e21`, host job `20261002-152034-e81b35`.
Research deadline 2026-10-03T07:20:39.240366Z; do not reset it.
Worktree `runs/worktrees/sol-12h-20261002`; branch
`node/DecomposableStateUpperDiagonalFourOfGates`, based on certified diagonal
commit `05ba7924a4ba74089e6ce1f396126cddbaeefca8`, whose ancestor is single-set
commit `adf3b2f1f1e0875dc59057e7abfd46be219d88da`.

## Exact outstanding obligations

1. Register and prove `decomposableStateUpper_four_diagonal_of_gates`, with
   `forall k, 5 <= k -> SingletonLowerPascalTailGate 4 k k` as a hypothesis.
   No R20 result is to be cherry-picked. The upper tail is arithmetically zero.
   Full registration job `20261002-162620-50ff52` succeeded, with unchanged
   type hash `8a8c8eaac2a011d3`; claim is held by this researcher.
   Candidate body `baek-port/DiagonalStateBody.txt` passed isolated check
   `20261002-164739-f7c8e6` with only standard axioms. Its accepted bytes are
   inserted into the original source. Full source check
   `20261002-165002-e99108` succeeded: closed, no sorry, standard axioms only,
   unchanged type hash and fresh index with zero problems. Audits
   `20261002-170811-d4a30d` passed. Separate code/source review
   `window-dc0da6abc7784922` verifies exact byte assembly and records artifact
   `3282828854a31abf87f12abdb7ec9e64388a3c0b9b221484a8b8cee8ddee1982`.
   Claim released closed. Commit `05ba7924a4ba74089e6ce1f396126cddbaeefca8`,
   job `20261002-170947-db7d40`, leaves a clean worktree. Both required
   mathematical obligations are closed; no merge or push occurred.
2. Add the optional cheap color dual `(k,4,k)` after the exact state is closed,
   if practical. Research window `window-fec772473d794228` is active; the
   prepared body uses `decomposableStateUpper_comm`. Branch creation
   `20261002-171028-5412d4` succeeded. Full registration
   `20261002-171102-7dd5ce` succeeded, type hash `9fbc31b5eb51b848`.
   Claim is held. Capture `20261002-172722-0386f3` succeeded with fixture
   `b81e683b25929484caf2d465743cfc23199f97ac13dbbb930bd5fd20c193c8b1`.
   Candidate operation `op-a70d22fb0d42419f`, job `20261002-172749-6b4c46`,
   accepted the candidate with standard axioms only. Accepted bytes are
   inserted through shared assembly/preflight, preserving the statement.
   Source SHA-256 is
   `1575ca2c4b3b9c0f5c8321eae172606e092fdaf15fa8f365b88c41bc0d69699d`.
   Full original-source check `20261002-172932-0a1eb5` succeeded: closed,
   no sorry, standard axioms only, unchanged hash and fresh/zero-problem index.
   Audits `20261002-174759-82d42d` passed. Separate review
   `window-aaf19fdf62ef405c` pins exact source and assembly in artifact
   `e0a9967bbec97ce9df4d5b3bb65e44c85c7f8a2e71e1b52c9131e95a01d71657`.
   Claim release and commit are next. No approved mathematical obligation remains.
   No new obligation replaces the already closed requested state.

## Compiled mathematics and evidence

- Baek `main`, the complete label/lacing/delta induction, compiles on the current
  toolchain and uses only the three standard axioms. Receipt:
  `20261002-153221-05028a`; repaired Mathlib-only diagnostic source
  `baek-port/BaekMathlib.lean`. Original copied source and its hashes are in
  `baek-erdos-tuza-valtr-a5ad53e/` and `baek-port/source-manifest.json`.
- The port is scoped and flattened in
  `ESBlueprint/C/CardLeChooseOfOneChangeNoCapFourNoStrong.lean`, with attributed
  source-section headers. Root List/Finset extensions are prefixed because
  field notation must find them in their actual type namespaces.
- Generic consecutive-to-all-triples promotion under OneChangeOn compiles:
  strong induction on outer index span, using overlapping smaller triples and
  `TurnSequenceAllowed.all_eq_of_outer_eq`. The existing geometric proof in
  `Chains.lean` is the template; no geometry hypothesis is assumed here.
- BaekChain3/CupCap.Consecutive adapters and cup/cap set conversion compile in
  diagnostic `20261002-153535-1c15b4`.
- Private cup-plus-apex strongness compiles in diagnostic
  `20261002-153850-6aa1ed`. A cup with common extrema p,r and cap apex q has
  triple color right exactly for middle q, and left for every cup middle.
  Propagate the endpoint cap through quartets (p,q,y,r) and (p,x,q,y), then
  the outer-apex cases through (p,q,x,y) and (x,y,q,r). Opposite colors on p,q,r
  exclude q from the cup. This is the needed strong-polygon invariant.

The complete target passed isolated proof check `20261002-154155-82ff5c`
and actual-source targeted check `20261002-154314-8d501b`, with hash
`17d2458e770c2e45` and only standard axioms. The former's receipt is
`runs/es-operations/20261002-154155-82ff5c/receipt.json`. The target source
has no remaining sorry. Finalization `op-8fd70671be5c456f` is succeeded:
full-index problems and audit violations are empty. Review artifact source
hash is `94758a5127d9da310118d1d5bf04d0ed2a768edad877b9e23b3f2e43bd5d2a77`.
The single-set node is committed as `adf3b2f1f1e0875dc59057e7abfd46be219d88da`,
job `20261002-162156-adb838`, with no other tracked changes left. It closes
hash `17d2458e770c2e45`; the claim was released closed. No merge/push occurred.

## Current proof idea

Baek's quadratic threshold comes from a structural Pascal induction. Beta is
the longest ending-cup length minus one. Delta chooses the least vertex in
each beta level below n+2, removing at most n+2 vertices. Pascal's identity
leaves the preceding threshold in the complement. If one asymmetric cup join
is absent, label/slope laws extend the inductive interweaved laced cups or
contradict cup-freeness. If both join orientations exist, their joining theorem
already gives interweaved laced cups. The lacing-to-gon theorem closes main.
This explanation is in the compiled source, not a conjectural numeric pattern.

Do not remove OneChangeOn merely because Baek's source theorem allows arbitrary
configurations. Fixed diagnostic `20261002-170418-461953` exhibits Fin5,
right iff the triple index sum is odd, with no all-triple cap4 or strong4
but card5 > bound4. Strongness would force two equal-parity ordered pairs,
whose gaps require span at least five; Fin5 has span at most four. Quartet0123
is RLRL and violates OneChangeOn. A Baek cap014/cup024 gon has non-strong
union0124. This identifies the needed bridge assumption. Artifacts are in
`parity-witness/`; this is ordinary-code evidence, not Lean-certified refutation.

Translate no four-cap to Baek's Config language and invoke `main (k-3)` at
cardinality `choose (k-1) 2 + 2`. In its gon witness the cap list has length at
most three, since otherwise its four-prefix is a forbidden cap. A two-cap
leaves a k-cup, which is strong. A three-cap leaves a (k-1)-cup plus its cap
apex; the compiled middle-color invariant proves strongness. Sorted-list nodup
and apex exclusion give exactly k distinct vertices. The entire candidate
target body is `baek-port/SingleSetBody.txt` and has been accepted and inserted.

For the diagonal state, the single-set theorem applies to the WHOLE set:
decomposability implies OneChangeOn. Evaluate the three-term binomial window
at `(4,k,k)` as `1 + choose (k-1) 2`. A cardinality strictly above this forces
a four-cap or a strong k-set directly. The exact requested gate hypothesis
can be unused. This stronger route avoids predecessor induction, realization,
and all upper/lower child-tail arguments; the original state target is unchanged.

## Failed approaches and practical limits

- Nesting custom List helpers under Baek breaks newer Lean's field notation;
  repaired by prefixed extensions in root List/Finset namespaces. Leaf failure
  `20261002-152546-170eb1`, success `20261002-152757-545631`.
- Full port migration failures were API changes (Sorted/Pairwise, order-dual
  chain simplification, removed lt_or_le, Finset coercions, early simp closure).
  Their exact logs are jobs `20261002-152847-73ba26`, `20261002-153105-7091d8`,
  `20261002-153149-aae592`. Failed compiler recovery printed sorryAx and was
  explicitly excluded from accepted evidence.
- `es build node` in a 20G enclosing job compiled the target, then refused its
  configured 30G final stage: `20261002-153332-ace1ef`. Use guarded direct
  source diagnostics and a sized `es check --targeted` for final receipts.
- Separate untagged ESBlueprint helper modules would fail node extraction;
  keep helper declarations inside this registered node module.
- First finalization's full extract `20261002-154414-813658` failed after
  successful source closure: the fresh worktree lacks `ErdosSzekeres.olean`,
  and the extractor prebuilds only ESBlueprint despite importing both roots.
  Serial restoration `20261002-154541-37c842` succeeded on its covered targets
  but was stopped at the measured ten-minute review: repeated Lake startups
  implied about 130 more minutes. Its cache outputs are preserved. Replacement
  `20261002-155725-92b804` restored the same full ESCore via the guarded
  no-serial path at 30G in 12 seconds, peak 680 MiB, rc0. A pre-build storage
  refusal was repaired by liveness-checked reconciliation
  `20261002-155833-bc8423`; both receipts/logs are under the run directory.
  Explicit `operation retry` preserved accepted stages and launched full
  extraction `20261002-160005-c336e7`, attempt 2, which succeeded. Audits and
  review also succeeded; the recovery is complete.
- No general gon union bridge is needed: the no-four-cap hypothesis reduces
  the problem structurally to one apex. The original target remains unchanged.
- State registration `20261002-162428-b8907e` elaborated the exact statement
  but refused targeted extraction: required gate interface closure 28.4 GiB,
  configured targeted maximum 4 GiB. Full registration
  `20261002-162620-50ff52` recovered successfully without a limit override.
  `node finish` would also enforce the targeted limit in its source stage;
  use capture/check, then only accepted body insertion, full `es check`,
  audits, and node commit. Do not retry the known limited path or override limits.

## Evidence paths and resumption

Read PROGRESS.md and relevant `es journal` history; inspect pending jobs first.
Do not rerun `prepare_baek_port.py` over repaired source: it prepares initial
diagnostics only. The original node module is authoritative. The source script
is one-off migration glue; no recurring library algorithm has been introduced.
No R19/R20 worktree, branch, or node was edited. No merge or push was performed.
Proof fixture is `1ad33659b018baa2cd3026b8c894991f6fb5f0b566dceaedf0fbb27c3c2bc8e4`.
Finalization operation `op-8fd70671be5c456f` and all its jobs are terminal,
accepted and unpublished. Full original-source diagonal check
`20261002-165002-e99108` succeeded, rc0, 1052.6s, peak5704MiB. Its receipt is
`diagonal-finalization/source-check.json`. Research window
`window-1f56fe4fe55046ba` is complete, accepted one original-source result;
review window `window-dc0da6abc7784922` is complete. Audits/review/commit passed.
The optional dual claim is held. Its research window is `window-fec772473d794228`;
candidate check `20261002-172749-6b4c46`, operation `op-a70d22fb0d42419f`, is
accepted. Accepted bytes have been inserted, as recorded in
`dual-finalization/insertion.json`. Full original-source job
`20261002-172932-0a1eb5` succeeded (1023.2s, peak5662MiB); final audits and
separate review passed. Claim release and commit remain. Research window
`window-fec772473d794228` is complete; review window is
`window-aaf19fdf62ef405c`. No compiler or research job is pending.
Fixture
`cde2cefc033c776ec43cd182b35dadc594bc1dd4cf8527e6725c2a5ffa157ea1` and accepted
operation `op-001b20713f8646f6` remain durable. Candidate/source SHA-256 is
`383673715f23c362195b19aaeffbfe4acaaa3064c5f965b1e6f756ec41bd0d09`.
Insertion receipt is `diagonal-finalization/insertion.json`. No shell session
is pending. Inspect audit receipts before review/release/commit.
Separate code/library review is `CODE-LIBRARY-REVIEW.md`, window
`window-7373e4889c364aa7`; configured Sol review, no independent Astra claimed.
