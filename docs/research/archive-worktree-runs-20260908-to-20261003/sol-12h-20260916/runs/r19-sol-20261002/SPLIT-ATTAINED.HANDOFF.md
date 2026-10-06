# Exact splitting witness

Target `ErdosSzekeres.decomposableThreshold_split_attained`, type hash
`24b5d4c235fa6d6f`, on `node/DecomposableThresholdSplitAttained` from `e3c87197`.
For every `3 ≤ a,u ≤ k`, the explicit legal coupling `d=a-2` attains
`T(a,min(u-1,k-d),k)+T(min(a-1,d+1),u,k)=T(a,u,k)`.

Proof: in the classical regime, adjacent coefficients combine by Pascal. In the
active regime, the first term is the coefficient at `k-a`, and the second is the
suffix from `k-a+1` to `u-2`. The proof also establishes locally that the window
formula holds at parameter sums `k+2` and `k+3`, where it is respectively a
singleton and a two-coefficient Pascal identity.

Accepted original-source check: job `20261002-083132-7de94e`, DONE rc0, build
3.450120210647583 seconds / 599 MiB. Receipt
`161f6e6f3b4a97c22b413a26cd4e35801bff88de80ac6d422ab08836262fdf70`,
copied to `SPLIT-ATTAINED.original-check.json`: CLOSED, no sorry, unchanged lock,
only `propext`, `Classical.choice`, `Quot.sound`, no blocked or uncovered axioms.
Incremental extraction rechecked the original module and kept the frontier fresh.
Changed-node axiom audit and layers check pass. All 378 inherited lock records
were compared structurally and are unchanged; the larger textual diff only sorts
existing keys. No inherited node proof or statement was edited.

Registration job `20261002-082818-d68628`: DONE rc0, 2 minutes / 8327 MiB.
Frozen fixture `af6340bde41ead1f8bdbc059562f796015697c86b8ebebcd12c6331230ec5b32`.
The reusable `es.proofs.assembled` inserted only the captured proof span. A first
assembly job `20261002-083051-5be0b9` failed before mutation because the inline
command imported `load` instead of `load_config`; the corrected API succeeded.
This was infrastructure evidence, not a failed mathematical proof.

Review description: splitting adjacent singleton contributions can attain the
parent threshold at an explicit coupling, including the active-window boundary.
Search before proving: the natural-language splitting query returned no existing
identity; `es search decomposableThreshold` found the choose/window lemmas;
`es search 'decomposableThreshold window boundary'` found published boundary
allocations. Existing `CtxBaseUnitTransfer` was inspected for its boundary method.
No PR, merge, or push is authorized for this run; this is the reviewable description.

Open: the companion universal upper bound and resulting maximum identity are not
yet registered here. This witness alone does not prove PEEL or FLANK-SWAP.
