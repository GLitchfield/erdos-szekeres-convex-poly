# Exact one-level limits helper — closed and committed

Node `ErdosSzekeres.ctx_single_level_limits_exact`, statement hash
`27c5ffa48b789810`, branch `node/CtxSingleLevelLimitsExact` from
main41cc0e4b. Registered through targeted `es node add`, job
20260930-190926-53b050. Commit
`95559e090ff7044040348aec1c00ac7094fbd6af`, commit job20260930-194452-0516c6.
The registered theorem is accepted; C1r remains open.

For an arbitrary raw context σ with maxima=[m], a<=k, u<=k and sideAt(1)=s,
the theorem holds for ANY endpoints p,q. Its join extension on s is
max(chain extension,m). On the opposite side, chain and join are zero.
The selected axis limit is min(global-1-chain extension,k-1-m), and the
other axis limit is the other global minus one. No well-formedness, child
membership, uniform physical marker or sibling-maximum-range assumption
is required.

The proof computes the singleton indexed-level list on s and the empty list
on its opposite, then simplifies left/right extensions. Natural-number
arithmetic and a,u<=k remove the redundant limit term. It imports only
ErdosSzekeres.DecomposableContextLemmas from the required main baseline.

Search before writing: search-root-zones.json and search-onelevel-boundary.json
had no hits; the node-add duplicate scan found no exact statement.
Scratch source OneLevelLimits.lean passed
guarded job20260930-190039-f57429 (5.8s,531MiB). Scratch success alone does
not establish acceptance of the registered declaration.

Proof fixture
`3b30692e0ef2e617d34fa03f496fa1dcb3daa9c0d2234a932d3a21d16fec493b`,
body hash `d6be72f2432767d1bc5ed28a06ae573189e1089e23132ab1499f2f9eb7b2337c`.
The verified-unstarted 4G check op-483619df54a444d9 /
20260930-191443-01b66e was cancelled solely to reduce the memory reservation;
it produced no compiler or mathematical result. The identical fixture/body
was accepted at 3G in op-489128753867417b / 20260930-192528-c4309b. Previous
isolated checks measured 2101–2106MiB, supporting the reduced cap.
No coverage was dropped and no kill deadline was chosen.

The isolated receipt reports only propext, Quot.sound and Classical.choice,
12.04s/2101MiB. Its source SHA
`81e034f22cca83090ab7dde2e4c62e0194b826ad670ce2dae56386e736e8266d`
matches the installed module byte-for-byte. INSTALL.onelevel.json verifies
the captured proof span was the only change. The retained source is
runs/es-proof-checks/56f3a5fb282440e58e068fd6f489a8f6/Candidate.lean.
The candidate SHA is a file hash, not an artifact ID; an unsuccessful
artifact lookup is recorded and did not change the accepted source.

Original-source targeted check20260930-194307-536ecb confirms
sorry=false, standard axioms only, unchanged type hash and lock_ok=true.
Build5.13s/649MiB; targeted extraction only. Evidence:
RECEIPT.onelevel-isolated.json, PROOFCHECK.onelevel-accepted-full.json,
CHECK.onelevel-full.json, NODE.onelevel-closed.full.json,
RECEIPT.onelevel-commit.json. The commit contains exactly the new node,
blueprint import and harness index/lock records. No full extraction, merge
or push. Final mathematical review belongs to the coordinator.

The separate reviewed library commit on this branch is
`8fd0a9b8efa3325f492cfb952f810ed9b1b200a4`; it adds the recurring pure
singleton-cut enumerator, catalog/example and checked frozen fixture/tests.
It introduces no additional node and no theorem credit. CODE-REVIEW.md
records validation and the external-review limitation.
